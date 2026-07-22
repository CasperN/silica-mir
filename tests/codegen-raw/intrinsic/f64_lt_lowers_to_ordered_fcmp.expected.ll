; Generated from Silica-MIR
declare void @abort()

define void @f(double %arg.x, double %arg.y) {
.init:
  %local.x = alloca double, align 8
  store double %arg.x, ptr %local.x
  %local.y = alloca double, align 8
  store double %arg.y, ptr %local.y
  %local.b = alloca i1, align 1
  %local.out = alloca ptr, align 8
  br label %entry
entry:
  store ptr %local.b, ptr %local.out
  %t.0 = load double, ptr %local.x
  %t.1 = load double, ptr %local.y
  %t.2 = fcmp olt double %t.0, %t.1
  %t.3 = load ptr, ptr %local.out
  store i1 %t.2, ptr %t.3
  ret void
}

