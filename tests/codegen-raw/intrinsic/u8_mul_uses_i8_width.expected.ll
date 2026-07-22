; Generated from Silica-MIR
declare void @abort()

define void @f(i8 %arg.a, i8 %arg.b) {
.init:
  %local.a = alloca i8, align 1
  store i8 %arg.a, ptr %local.a
  %local.b = alloca i8, align 1
  store i8 %arg.b, ptr %local.b
  %local.r = alloca i8, align 1
  %local.out = alloca ptr, align 8
  br label %entry
entry:
  store ptr %local.r, ptr %local.out
  %t.0 = load i8, ptr %local.a
  %t.1 = load i8, ptr %local.b
  %t.2 = mul i8 %t.0, %t.1
  %t.3 = load ptr, ptr %local.out
  store i8 %t.2, ptr %t.3
  ret void
}

