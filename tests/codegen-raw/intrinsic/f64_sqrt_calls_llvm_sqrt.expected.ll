; Generated from Silica-MIR
declare void @abort()
declare double @llvm.sqrt.double(double)

define void @f(double %arg.x) {
.init:
  %local.x = alloca double, align 8
  store double %arg.x, ptr %local.x
  %local.y = alloca double, align 8
  %local.out = alloca ptr, align 8
  br label %entry
entry:
  store ptr %local.y, ptr %local.out
  %t.0 = load double, ptr %local.x
  %t.1 = call double @llvm.sqrt.double(double %t.0)
  %t.2 = load ptr, ptr %local.out
  store double %t.1, ptr %t.2
  ret void
}

