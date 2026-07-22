; Generated from Silica-MIR
declare void @abort()

define void @f(i64 %arg.x) {
.init:
  %local.x = alloca i64, align 8
  store i64 %arg.x, ptr %local.x
  %local.y = alloca double, align 8
  %local.out = alloca ptr, align 8
  br label %entry
entry:
  store ptr %local.y, ptr %local.out
  %t.0 = load i64, ptr %local.x
  %t.1 = sitofp i64 %t.0 to double
  %t.2 = load ptr, ptr %local.out
  store double %t.1, ptr %t.2
  ret void
}

