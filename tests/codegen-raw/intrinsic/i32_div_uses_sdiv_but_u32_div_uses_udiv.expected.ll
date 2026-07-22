; Generated from Silica-MIR
declare void @abort()

define void @f(i32 %arg.a, i32 %arg.b, i32 %arg.c, i32 %arg.d) {
.init:
  %local.a = alloca i32, align 4
  store i32 %arg.a, ptr %local.a
  %local.b = alloca i32, align 4
  store i32 %arg.b, ptr %local.b
  %local.c = alloca i32, align 4
  store i32 %arg.c, ptr %local.c
  %local.d = alloca i32, align 4
  store i32 %arg.d, ptr %local.d
  %local.r_signed = alloca i32, align 4
  %local.out_signed = alloca ptr, align 8
  %local.r_unsigned = alloca i32, align 4
  %local.out_unsigned = alloca ptr, align 8
  br label %entry
entry:
  store ptr %local.r_signed, ptr %local.out_signed
  %t.0 = load i32, ptr %local.a
  %t.1 = load i32, ptr %local.b
  %t.2 = sdiv i32 %t.0, %t.1
  %t.3 = load ptr, ptr %local.out_signed
  store i32 %t.2, ptr %t.3
  store ptr %local.r_unsigned, ptr %local.out_unsigned
  %t.4 = load i32, ptr %local.c
  %t.5 = load i32, ptr %local.d
  %t.6 = udiv i32 %t.4, %t.5
  %t.7 = load ptr, ptr %local.out_unsigned
  store i32 %t.6, ptr %t.7
  ret void
}

