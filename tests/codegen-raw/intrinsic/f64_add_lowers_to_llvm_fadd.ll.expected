; Generated from Silica-MIR
declare void @abort()

define void @f(double %arg.a, double %arg.b) {
.init:
  %local.a = alloca double, align 8
  store double %arg.a, ptr %local.a
  %local.b = alloca double, align 8
  store double %arg.b, ptr %local.b
  %local.r = alloca double, align 8
  %local.out = alloca ptr, align 8
  br label %entry
entry:
  store ptr %local.r, ptr %local.out
  %t.0 = load double, ptr %local.a
  %t.1 = load double, ptr %local.b
  %t.2 = fadd double %t.0, %t.1
  %t.3 = load ptr, ptr %local.out
  store double %t.2, ptr %t.3
  ret void
}

