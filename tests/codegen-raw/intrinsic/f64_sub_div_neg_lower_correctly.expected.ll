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
  %t.2 = fsub double %t.0, %t.1
  %t.3 = load ptr, ptr %local.out
  store double %t.2, ptr %t.3
  %t.4 = load double, ptr %local.a
  %t.5 = load double, ptr %local.b
  %t.6 = fdiv double %t.4, %t.5
  %t.7 = load ptr, ptr %local.out
  store double %t.6, ptr %t.7
  %t.8 = load double, ptr %local.a
  %t.9 = fneg double %t.8
  %t.10 = load ptr, ptr %local.out
  store double %t.9, ptr %t.10
  ret void
}

