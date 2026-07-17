; Generated from Silica-MIR
declare void @abort()

define void @f(float %arg.x) {
.init:
  %local.x = alloca float, align 4
  store float %arg.x, ptr %local.x
  %local.y = alloca double, align 8
  %local.out = alloca ptr, align 8
  br label %entry
entry:
  store ptr %local.y, ptr %local.out
  %t.0 = load float, ptr %local.x
  %t.1 = fpext float %t.0 to double
  %t.2 = load ptr, ptr %local.out
  store double %t.1, ptr %t.2
  ret void
}

