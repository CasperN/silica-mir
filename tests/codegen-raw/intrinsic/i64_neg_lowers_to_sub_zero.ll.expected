; Generated from Silica-MIR
declare void @abort()

define void @f(i64 %arg.a) {
.init:
  %local.a = alloca i64, align 8
  store i64 %arg.a, ptr %local.a
  %local.r = alloca i64, align 8
  %local.out = alloca ptr, align 8
  br label %entry
entry:
  store ptr %local.r, ptr %local.out
  %t.0 = load i64, ptr %local.a
  %t.1 = sub i64 0, %t.0
  %t.2 = load ptr, ptr %local.out
  store i64 %t.1, ptr %t.2
  ret void
}

