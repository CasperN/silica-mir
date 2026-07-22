; Generated from Silica-MIR
declare void @abort()

define void @compute(i64 %arg.a, i64 %arg.b, ptr %arg.out) {
.init:
  %local.a = alloca i64, align 8
  store i64 %arg.a, ptr %local.a
  %local.b = alloca i64, align 8
  store i64 %arg.b, ptr %local.b
  %local.out = alloca ptr, align 8
  store ptr %arg.out, ptr %local.out
  %local.t1 = alloca i64, align 8
  %local.t2 = alloca i64, align 8
  %local.t1_out = alloca ptr, align 8
  %local.t2_out = alloca ptr, align 8
  br label %entry
entry:
  store ptr %local.t1, ptr %local.t1_out
  %t.0 = load i64, ptr %local.a
  %t.1 = load i64, ptr %local.b
  %t.2 = add i64 %t.0, %t.1
  %t.3 = load ptr, ptr %local.t1_out
  store i64 %t.2, ptr %t.3
  store ptr %local.t2, ptr %local.t2_out
  %t.4 = load i64, ptr %local.t1
  %t.5 = load i64, ptr %local.a
  %t.6 = mul i64 %t.4, %t.5
  %t.7 = load ptr, ptr %local.t2_out
  store i64 %t.6, ptr %t.7
  %t.8 = load i64, ptr %local.t2
  %t.9 = load ptr, ptr %local.out
  store i64 %t.8, ptr %t.9
  ret void
}

