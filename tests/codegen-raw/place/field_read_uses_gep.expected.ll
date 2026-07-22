; Generated from Silica-MIR
declare void @abort()

%P = type { i64, i64 }

define void @f(%P %arg.p) {
.init:
  %local.p = alloca %P, align 8
  store %P %arg.p, ptr %local.p
  %local.n = alloca i64, align 8
  br label %entry
entry:
  %t.0 = getelementptr %P, ptr %local.p, i32 0, i32 1
  %t.1 = load i64, ptr %t.0
  store i64 %t.1, ptr %local.n
  ret void
}

