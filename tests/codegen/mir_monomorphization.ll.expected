; Generated from Silica-MIR
declare void @abort()

%"Box<i32>" = type { i32 }
%"Box<Box<i32>>" = type { %"Box<i32>" }
%"Pair<i32, f64>" = type { i32, double }
%"Opt<i32>" = type { i16, [2 x i8], [1 x i32] }
%"Node<i32>" = type { i32, ptr }

define void @make_box(i32 %arg.x, ptr %arg.$return) {
.init:
  %local.$return = alloca ptr, align 8
  store ptr %arg.$return, ptr %local.$return
  %local.x = alloca i32, align 4
  store i32 %arg.x, ptr %local.x
  br label %entry
entry:
  %t.0 = load i32, ptr %local.x
  %t.1 = load ptr, ptr %local.$return
  %t.2 = getelementptr %"Box<i32>", ptr %t.1, i32 0, i32 0
  store i32 %t.0, ptr %t.2
  ret void
}

define void @nested(i32 %arg.x, ptr %arg.$return) {
.init:
  %local.$return = alloca ptr, align 8
  store ptr %arg.$return, ptr %local.$return
  %local.x = alloca i32, align 4
  store i32 %arg.x, ptr %local.x
  %local.inner = alloca %"Box<i32>", align 4
  br label %entry
entry:
  %t.0 = load i32, ptr %local.x
  %t.1 = getelementptr %"Box<i32>", ptr %local.inner, i32 0, i32 0
  store i32 %t.0, ptr %t.1
  %t.2 = load %"Box<i32>", ptr %local.inner
  %t.3 = load ptr, ptr %local.$return
  %t.4 = getelementptr %"Box<Box<i32>>", ptr %t.3, i32 0, i32 0
  store %"Box<i32>" %t.2, ptr %t.4
  ret void
}

define void @make_pair(i32 %arg.a, double %arg.b, ptr %arg.$return) {
.init:
  %local.$return = alloca ptr, align 8
  store ptr %arg.$return, ptr %local.$return
  %local.a = alloca i32, align 4
  store i32 %arg.a, ptr %local.a
  %local.b = alloca double, align 8
  store double %arg.b, ptr %local.b
  br label %entry
entry:
  %t.0 = load i32, ptr %local.a
  %t.1 = load ptr, ptr %local.$return
  %t.2 = getelementptr %"Pair<i32, f64>", ptr %t.1, i32 0, i32 0
  store i32 %t.0, ptr %t.2
  %t.3 = load double, ptr %local.b
  %t.4 = load ptr, ptr %local.$return
  %t.5 = getelementptr %"Pair<i32, f64>", ptr %t.4, i32 0, i32 1
  store double %t.3, ptr %t.5
  ret void
}

define void @make_opt(i32 %arg.x, ptr %arg.$return) {
.init:
  %local.$return = alloca ptr, align 8
  store ptr %arg.$return, ptr %local.$return
  %local.x = alloca i32, align 4
  store i32 %arg.x, ptr %local.x
  br label %entry
entry:
  %t.0 = load i32, ptr %local.x
  %t.1 = load ptr, ptr %local.$return
  %t.2 = getelementptr %"Opt<i32>", ptr %t.1, i32 0, i32 0
  store i16 1, ptr %t.2
  %t.3 = getelementptr %"Opt<i32>", ptr %t.1, i32 0, i32 2
  store i32 %t.0, ptr %t.3
  ret void
}

define void @make_node(i32 %arg.v, ptr %arg.tail, ptr %arg.$return) {
.init:
  %local.$return = alloca ptr, align 8
  store ptr %arg.$return, ptr %local.$return
  %local.v = alloca i32, align 4
  store i32 %arg.v, ptr %local.v
  %local.tail = alloca ptr, align 8
  store ptr %arg.tail, ptr %local.tail
  br label %entry
entry:
  %t.0 = load i32, ptr %local.v
  %t.1 = load ptr, ptr %local.$return
  %t.2 = getelementptr %"Node<i32>", ptr %t.1, i32 0, i32 0
  store i32 %t.0, ptr %t.2
  %t.3 = load ptr, ptr %local.tail
  %t.4 = load ptr, ptr %local.$return
  %t.5 = getelementptr %"Node<i32>", ptr %t.4, i32 0, i32 1
  store ptr %t.3, ptr %t.5
  ret void
}

define void @silica.main(ptr %arg.exit) {
.init:
  %local.exit = alloca ptr, align 8
  store ptr %arg.exit, ptr %local.exit
  %local.b = alloca %"Box<i32>", align 4
  %local.bb = alloca %"Box<Box<i32>>", align 4
  %local.o = alloca %"Opt<i32>", align 4
  %local.p = alloca %"Pair<i32, f64>", align 8
  %local.n = alloca %"Node<i32>", align 8
  %local.null_ptr = alloca ptr, align 8
  %local.id_out = alloca ptr, align 8
  %local.b_out = alloca ptr, align 8
  %local.bb_out = alloca ptr, align 8
  %local.o_out = alloca ptr, align 8
  %local.p_out = alloca ptr, align 8
  %local.n_out = alloca ptr, align 8
  br label %entry
entry:
  store ptr %local.b, ptr %local.b_out
  %t.0 = load ptr, ptr %local.b_out
  call void @make_box(i32 3, ptr %t.0)
  store ptr %local.bb, ptr %local.bb_out
  %t.1 = load ptr, ptr %local.bb_out
  call void @nested(i32 7, ptr %t.1)
  store ptr %local.o, ptr %local.o_out
  %t.2 = load ptr, ptr %local.o_out
  call void @make_opt(i32 11, ptr %t.2)
  store ptr %local.p, ptr %local.p_out
  %t.3 = load ptr, ptr %local.p_out
  call void @make_pair(i32 13, double 0x40091EB851EB851F, ptr %t.3)
  store ptr %local.n, ptr %local.null_ptr
  store ptr %local.n, ptr %local.n_out
  %t.4 = load ptr, ptr %local.null_ptr
  %t.5 = load ptr, ptr %local.n_out
  call void @make_node(i32 17, ptr %t.4, ptr %t.5)
  %t.6 = load ptr, ptr %local.exit
  store ptr %t.6, ptr %local.id_out
  %t.7 = getelementptr %"Box<i32>", ptr %local.b, i32 0, i32 0
  %t.8 = load i32, ptr %t.7
  %t.9 = load ptr, ptr %local.id_out
  call void @"identity<i32>"(i32 %t.8, ptr %t.9)
  ret void
}

define void @"identity<i32>"(i32 %arg.x, ptr %arg.$return) {
.init:
  %local.$return = alloca ptr, align 8
  store ptr %arg.$return, ptr %local.$return
  %local.x = alloca i32, align 4
  store i32 %arg.x, ptr %local.x
  br label %entry
entry:
  %t.0 = load i32, ptr %local.x
  %t.1 = load ptr, ptr %local.$return
  store i32 %t.0, ptr %t.1
  ret void
}

define i32 @main() {
  %exit = alloca i32, align 4
  store i32 0, ptr %exit
  call void @silica.main(ptr %exit)
  %code = load i32, ptr %exit
  ret i32 %code
}

