; Generated from Silica-MIR
declare void @abort()

define void @f(i64 %arg.x) {
.init:
  %local.x = alloca i64, align 8
  store i64 %arg.x, ptr %local.x
  %local.y = alloca i64, align 8
  br label %entry
entry:
  %t.0 = load i64, ptr %local.x
  store i64 %t.0, ptr %local.y
  ret void
}

