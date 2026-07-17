; Generated from Silica-MIR
declare void @abort()

define void @f(i32 %arg.a, i32 %arg.b) {
.init:
  %local.a = alloca i32, align 4
  store i32 %arg.a, ptr %local.a
  %local.b = alloca i32, align 4
  store i32 %arg.b, ptr %local.b
  %local.r = alloca i32, align 4
  %local.out = alloca ptr, align 8
  br label %entry
entry:
  store ptr %local.r, ptr %local.out
  %t.0 = load i32, ptr %local.a
  %t.1 = load i32, ptr %local.b
  %t.2 = add i32 %t.0, %t.1
  %t.3 = load ptr, ptr %local.out
  store i32 %t.2, ptr %t.3
  ret void
}

