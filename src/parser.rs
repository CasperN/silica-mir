use crate::ast::*;
use tree_sitter::{Parser as TSParser, Node};

extern "C" {
    fn tree_sitter_silica_mir() -> *const std::ffi::c_void;
}

pub fn language() -> tree_sitter::Language {
    unsafe { tree_sitter::Language::from_raw(tree_sitter_silica_mir() as *const _) }
}

pub struct Parser {
    source: String,
}

impl Parser {
    pub fn new(source: String) -> Self {
        Self { source }
    }

    pub fn parse(&self) -> Result<Program, String> {
        let mut parser = TSParser::new();
        parser.set_language(&language()).map_err(|e| e.to_string())?;

        let tree = parser.parse(&self.source, None).ok_or("Failed to parse source code")?;
        let root = tree.root_node();

        if root.has_error() {
            return Err("Syntax error in source code".to_string());
        }

        self.map_program(root)
    }

    fn get_text(&self, node: Node) -> &str {
        &self.source[node.byte_range()]
    }

    fn map_program(&self, node: Node) -> Result<Program, String> {
        let mut declarations = Vec::new();
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "declaration" {
                declarations.push(self.map_declaration(child)?);
            }
        }
        Ok(Program { declarations })
    }

    fn map_declaration(&self, node: Node) -> Result<Declaration, String> {
        let child = node.child(0).ok_or("Empty declaration")?;
        match child.kind() {
            "struct_decl" => Ok(Declaration::Struct(self.map_struct_decl(child)?)),
            "enum_decl" => Ok(Declaration::Enum(self.map_enum_decl(child)?)),
            "function_decl" => Ok(Declaration::Fn(self.map_function_decl(child)?)),
            "extern_fn" => Ok(Declaration::ExternFn(self.map_extern_fn(child)?)),
            _ => Err(format!("Unknown declaration kind: {}", child.kind())),
        }
    }

    fn map_type(&self, node: Node) -> Result<Type, String> {
        match node.kind() {
            "number" => Ok(Type::Number),
            "boolean" => Ok(Type::Boolean),
            "identifier" => Ok(Type::Struct(self.get_text(node).to_string())),
            "type" => {
                let first_child = node.child(0).ok_or("Type node has no children")?;
                let kind = first_child.kind();
                if kind == "number" || kind == "boolean" || kind == "identifier" {
                    return self.map_type(first_child);
                }

                let text = self.get_text(first_child);
                match text {
                    "&" => {
                        let inner = node.child(1).ok_or("Missing inner type for &")?;
                        Ok(Type::Ref(RefKind::Shared, Box::new(self.map_type(inner)?)))
                    }
                    "&mut" => {
                        let inner = node.child(1).ok_or("Missing inner type for &mut")?;
                        Ok(Type::Ref(RefKind::Mut, Box::new(self.map_type(inner)?)))
                    }
                    "&out" => {
                        let inner = node.child(1).ok_or("Missing inner type for &out")?;
                        Ok(Type::Ref(RefKind::Out, Box::new(self.map_type(inner)?)))
                    }
                    "&drop" => {
                        let inner = node.child(1).ok_or("Missing inner type for &drop")?;
                        Ok(Type::Ref(RefKind::Drop, Box::new(self.map_type(inner)?)))
                    }
                    "&uninit" => {
                        let inner = node.child(1).ok_or("Missing inner type for &uninit")?;
                        Ok(Type::Ref(RefKind::Uninit, Box::new(self.map_type(inner)?)))
                    }
                    "fn" => {
                        let mut params = Vec::new();
                        let mut cursor = node.walk();
                        for child in node.children(&mut cursor) {
                            if child.kind() == "type" {
                                params.push(self.map_type(child)?);
                            }
                        }
                        Ok(Type::Fn(params))
                    }
                    _ => Err(format!("Unexpected token in type: {}", text)),
                }
            }
            _ => Err(format!("Unexpected node kind in type: {}", node.kind())),
        }
    }

    fn map_place(&self, node: Node) -> Result<Place, String> {
        match node.kind() {
            "identifier" => Ok(Place::Var(self.get_text(node).to_string())),
            "place" => {
                let first_child = node.child(0).ok_or("Place node has no children")?;
                if first_child.kind() == "identifier" && node.child_count() == 1 {
                    return Ok(Place::Var(self.get_text(first_child).to_string()));
                }

                let text = self.get_text(first_child);
                if text == "*" {
                    let inner = node.child(1).ok_or("Deref missing inner place")?;
                    Ok(Place::Deref(Box::new(self.map_place(inner)?)))
                } else if text == "(" {
                    let inner_place_node = node.child(1).ok_or("Downcast missing inner place")?;
                    let inner_place = self.map_place(inner_place_node)?;
                    let variant_node = node.child_by_field_name("variant").ok_or("Downcast missing variant")?;
                    let variant = self.get_text(variant_node).to_string();
                    Ok(Place::Downcast(Box::new(inner_place), variant))
                } else {
                    let inner_place = self.map_place(first_child)?;
                    let field_node = node.child_by_field_name("field").ok_or("Field projection missing field name")?;
                    let field_name = self.get_text(field_node).to_string();
                    Ok(Place::Field(Box::new(inner_place), field_name))
                }
            }
            _ => Err(format!("Unexpected node kind in place: {}", node.kind())),
        }
    }

    fn map_operand(&self, node: Node) -> Result<Operand, String> {
        if node.kind() == "operand" {
            let first_child = node.child(0).ok_or("Operand missing children")?;
            let text = self.get_text(first_child);
            match text {
                "copy" => {
                    let place_node = node.child(1).ok_or("Copy missing place")?;
                    Ok(Operand::Copy(self.map_place(place_node)?))
                }
                "move" => {
                    let place_node = node.child(1).ok_or("Move missing place")?;
                    Ok(Operand::Move(self.map_place(place_node)?))
                }
                _ => {
                    Ok(Operand::Const(self.map_const(first_child)?))
                }
            }
        } else {
            Err(format!("Expected operand, found: {}", node.kind()))
        }
    }

    fn map_const(&self, node: Node) -> Result<ConstVal, String> {
        match node.kind() {
            "number" => {
                let val = self.get_text(node).parse::<u64>().map_err(|e| e.to_string())?;
                Ok(ConstVal::Number(val))
            }
            "const" => {
                let child = node.child(0).ok_or("Const node is empty")?;
                self.map_const(child)
            }
            _ => {
                let text = self.get_text(node);
                match text {
                    "true" => Ok(ConstVal::Boolean(true)),
                    "false" => Ok(ConstVal::Boolean(false)),
                    _ => Ok(ConstVal::FnName(text.to_string())),
                }
            }
        }
    }

    fn map_rvalue(&self, node: Node) -> Result<RValue, String> {
        let child = node.child(0).ok_or("RValue node is empty")?;
        match child.kind() {
            "operand" => Ok(RValue::Use(self.map_operand(child)?)),
            _ => {
                let text = self.get_text(child);
                match text {
                    "&" => {
                        let place_node = node.child(1).ok_or("Ref missing place")?;
                        Ok(RValue::Ref(RefKind::Shared, self.map_place(place_node)?))
                    }
                    "&mut" => {
                        let place_node = node.child(1).ok_or("Ref missing place")?;
                        Ok(RValue::Ref(RefKind::Mut, self.map_place(place_node)?))
                    }
                    "&out" => {
                        let place_node = node.child(1).ok_or("Ref missing place")?;
                        Ok(RValue::Ref(RefKind::Out, self.map_place(place_node)?))
                    }
                    "&drop" => {
                        let place_node = node.child(1).ok_or("Ref missing place")?;
                        Ok(RValue::Ref(RefKind::Drop, self.map_place(place_node)?))
                    }
                    "&uninit" => {
                        let place_node = node.child(1).ok_or("Ref missing place")?;
                        Ok(RValue::Ref(RefKind::Uninit, self.map_place(place_node)?))
                    }
                    _ => {
                        let enum_name_node = node.child_by_field_name("enum_name").ok_or("Enum construction missing enum name")?;
                        let enum_name = self.get_text(enum_name_node).to_string();
                        let variant_name_node = node.child_by_field_name("variant_name").ok_or("Enum construction missing variant name")?;
                        let variant_name = self.get_text(variant_name_node).to_string();
                        let mut cursor = node.walk();
                        let operand_node = node.children(&mut cursor).find(|c| c.kind() == "operand").ok_or("Enum construction missing operand")?;
                        let operand = self.map_operand(operand_node)?;
                        Ok(RValue::EnumConstr(enum_name, variant_name, operand))
                    }
                }
            }
        }
    }

    fn map_statement(&self, node: Node) -> Result<Statement, String> {
        let child = node.child(0).ok_or("Statement empty")?;
        match child.kind() {
            "assignment" => {
                let lhs_node = child.child_by_field_name("lhs").ok_or("Assignment missing LHS")?;
                let lhs = self.map_place(lhs_node)?;
                let rhs_node = child.child_by_field_name("rhs").ok_or("Assignment missing RHS")?;
                let rhs = self.map_rvalue(rhs_node)?;
                Ok(Statement::Assign(lhs, rhs))
            }
            "call" => {
                let func_node = child.child_by_field_name("function").ok_or("Call missing function")?;
                let func = self.map_operand(func_node)?;

                let mut args = Vec::new();
                let mut cursor = child.walk();
                for item in child.children(&mut cursor) {
                    if item.kind() == "operand" && item != func_node {
                        args.push(self.map_operand(item)?);
                    }
                }
                Ok(Statement::Call(func, args))
            }
            _ => Err(format!("Unknown statement kind: {}", child.kind())),
        }
    }

    fn map_terminator(&self, node: Node) -> Result<Terminator, String> {
        let child = node.child(0).ok_or("Terminator empty")?;
        match child.kind() {
            "goto" => {
                let label_node = child.child_by_field_name("label").ok_or("Goto missing label")?;
                Ok(Terminator::Goto(self.get_text(label_node).to_string()))
            }
            "return" => Ok(Terminator::Return),
            "branch" => {
                let cond_node = child.child_by_field_name("condition").ok_or("Branch missing condition")?;
                let cond = self.map_operand(cond_node)?;
                let true_node = child.child_by_field_name("true_label").ok_or("Branch missing true_label")?;
                let true_label = self.get_text(true_node).to_string();
                let false_node = child.child_by_field_name("false_label").ok_or("Branch missing false_label")?;
                let false_label = self.get_text(false_node).to_string();
                Ok(Terminator::Branch { cond, true_label, false_label })
            }
            "switchEnum" => {
                let place_node = child.child_by_field_name("place").ok_or("SwitchEnum missing place")?;
                let place = self.map_place(place_node)?;

                let mut cases = Vec::new();
                let mut cursor = child.walk();
                for item in child.children(&mut cursor) {
                    if item.kind() == "switch_case" {
                        let variant_node = item.child_by_field_name("variant").ok_or("Switch case missing variant")?;
                        let variant = self.get_text(variant_node).to_string();
                        let label_node = item.child_by_field_name("label").ok_or("Switch case missing label")?;
                        let label = self.get_text(label_node).to_string();
                        cases.push((variant, label));
                    }
                }
                Ok(Terminator::SwitchEnum { place, cases })
            }
            "abort" => Ok(Terminator::Abort),
            "unreachable" => Ok(Terminator::Unreachable),
            _ => Err(format!("Unknown terminator kind: {}", child.kind())),
        }
    }

    fn map_basic_block(&self, node: Node) -> Result<BasicBlock, String> {
        let label_node = node.child_by_field_name("label").ok_or("Basic block missing label")?;
        let label = self.get_text(label_node).to_string();

        let mut statements = Vec::new();
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "statement" {
                statements.push(self.map_statement(child)?);
            }
        }

        let term_node = node.children(&mut cursor).find(|c| c.kind() == "terminator").ok_or("Basic block missing terminator")?;
        let terminator = self.map_terminator(term_node)?;

        Ok(BasicBlock { label, statements, terminator })
    }

    fn map_struct_decl(&self, node: Node) -> Result<StructDecl, String> {
        let name_node = node.child_by_field_name("name").ok_or("Struct decl missing name")?;
        let name = self.get_text(name_node).to_string();

        let mut copy = false;
        let mut drop = false;
        let mut cursor = node.walk();
        if let Some(markers_node) = node.children(&mut cursor).find(|c| c.kind() == "markers") {
            let text = self.get_text(markers_node);
            copy = text.contains("Copy");
            drop = text.contains("Drop");
        }
        let markers = Markers { copy, drop };

        let mut fields = Vec::new();
        for child in node.children(&mut cursor) {
            if child.kind() == "struct_field" {
                let f_name_node = child.child_by_field_name("name").ok_or("Struct field missing name")?;
                let f_name = self.get_text(f_name_node).to_string();
                let f_type_node = child.child_by_field_name("type").ok_or("Struct field missing type")?;
                let f_type = self.map_type(f_type_node)?;
                fields.push((f_name, f_type));
            }
        }

        Ok(StructDecl { name, markers, fields })
    }

    fn map_enum_decl(&self, node: Node) -> Result<EnumDecl, String> {
        let name_node = node.child_by_field_name("name").ok_or("Enum decl missing name")?;
        let name = self.get_text(name_node).to_string();

        let mut copy = false;
        let mut drop = false;
        let mut cursor = node.walk();
        if let Some(markers_node) = node.children(&mut cursor).find(|c| c.kind() == "markers") {
            let text = self.get_text(markers_node);
            copy = text.contains("Copy");
            drop = text.contains("Drop");
        }
        let markers = Markers { copy, drop };

        let mut variants = Vec::new();
        for child in node.children(&mut cursor) {
            if child.kind() == "enum_variant" {
                let v_name_node = child.child_by_field_name("name").ok_or("Enum variant missing name")?;
                let v_name = self.get_text(v_name_node).to_string();
                let v_type_node = child.child_by_field_name("type").ok_or("Enum variant missing type")?;
                let v_type = self.map_type(v_type_node)?;
                variants.push((v_name, v_type));
            }
        }

        Ok(EnumDecl { name, markers, variants })
    }

    fn map_extern_fn(&self, node: Node) -> Result<ExternFn, String> {
        let name_node = node.child_by_field_name("name").ok_or("Extern fn missing name")?;
        let name = self.get_text(name_node).to_string();

        let mut params = Vec::new();
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "param_decl" {
                let p_name_node = child.child_by_field_name("name").ok_or("Param missing name")?;
                let p_name = self.get_text(p_name_node).to_string();
                let p_type_node = child.child_by_field_name("type").ok_or("Param missing type")?;
                let p_type = self.map_type(p_type_node)?;
                params.push((p_name, p_type));
            }
        }

        Ok(ExternFn { name, params })
    }

    fn map_function_decl(&self, node: Node) -> Result<Function, String> {
        let name_node = node.child_by_field_name("name").ok_or("Function missing name")?;
        let name = self.get_text(name_node).to_string();

        let mut params = Vec::new();
        let mut locals = Vec::new();
        let mut blocks = Vec::new();

        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            match child.kind() {
                "param_decl" => {
                    let p_name_node = child.child_by_field_name("name").ok_or("Param missing name")?;
                    let p_name = self.get_text(p_name_node).to_string();
                    let p_type_node = child.child_by_field_name("type").ok_or("Param missing type")?;
                    let p_type = self.map_type(p_type_node)?;
                    params.push((p_name, p_type));
                }
                "local_decl" => {
                    let l_name_node = child.child_by_field_name("name").ok_or("Local missing name")?;
                    let l_name = self.get_text(l_name_node).to_string();
                    let l_type_node = child.child_by_field_name("type").ok_or("Local missing type")?;
                    let l_type = self.map_type(l_type_node)?;
                    locals.push((l_name, l_type));
                }
                "basic_block" => {
                    blocks.push(self.map_basic_block(child)?);
                }
                _ => {}
            }
        }

        Ok(Function { name, params, locals, blocks })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_struct_decl() {
        let source = "
            struct Copy Drop Point {
                x: number
                y: number
            }
        ";
        let parser = Parser::new(source.to_string());
        let program = parser.parse().unwrap();
        assert_eq!(program.declarations.len(), 1);
        if let Declaration::Struct(s) = &program.declarations[0] {
            assert_eq!(s.name, "Point");
            assert!(s.markers.copy);
            assert!(s.markers.drop);
            assert_eq!(s.fields.len(), 2);
            assert_eq!(s.fields[0].0, "x");
            assert_eq!(s.fields[0].1, Type::Number);
            assert_eq!(s.fields[1].0, "y");
            assert_eq!(s.fields[1].1, Type::Number);
        } else {
            panic!("Expected struct declaration");
        }
    }

    #[test]
    fn test_parse_enum_decl() {
        let source = "
            enum Option {
                None: Option
                Some: number
            }
        ";
        let parser = Parser::new(source.to_string());
        let program = parser.parse().unwrap();
        assert_eq!(program.declarations.len(), 1);
        if let Declaration::Enum(e) = &program.declarations[0] {
            assert_eq!(e.name, "Option");
            assert!(!e.markers.copy);
            assert!(!e.markers.drop);
            assert_eq!(e.variants.len(), 2);
            assert_eq!(e.variants[0].0, "None");
            assert_eq!(e.variants[0].1, Type::Struct("Option".to_string()));
            assert_eq!(e.variants[1].0, "Some");
            assert_eq!(e.variants[1].1, Type::Number);
        } else {
            panic!("Expected enum declaration");
        }
    }

    #[test]
    fn test_parse_function_decl() {
        let source = "
            fn add(a: number, b: number) {
                ret: &out number;
                entry:
                    r1 = copy a;
                    r2 = copy b;
                    call add_impl(move r1, move r2);
                    return
            }
        ";
        let parser = Parser::new(source.to_string());
        let program = parser.parse().unwrap();
        assert_eq!(program.declarations.len(), 1);
        if let Declaration::Fn(f) = &program.declarations[0] {
            assert_eq!(f.name, "add");
            assert_eq!(f.params.len(), 2);
            assert_eq!(f.params[0].0, "a");
            assert_eq!(f.params[0].1, Type::Number);
            assert_eq!(f.locals.len(), 1);
            assert_eq!(f.locals[0].0, "ret");
            assert_eq!(f.blocks.len(), 1);
            let block = &f.blocks[0];
            assert_eq!(block.label, "entry");
            assert_eq!(block.statements.len(), 3);
            assert_eq!(block.terminator, Terminator::Return);
        } else {
            panic!("Expected function declaration");
        }
    }
}
