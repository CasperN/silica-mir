; Generated from Silica-MIR
declare void @abort()

define void @f(float %arg.a, float %arg.b) {
.init:
  %local.a = alloca float, align 4
  store float %arg.a, ptr %local.a
  %local.b = alloca float, align 4
  store float %arg.b, ptr %local.b
  %local.r = alloca float, align 4
  %local.out = alloca ptr, align 8
  br label %entry
entry:
  store ptr %local.r, ptr %local.out
  %t.0 = load float, ptr %local.a
  %t.1 = load float, ptr %local.b
  %t.2 = fadd float %t.0, %t.1
  %t.3 = load ptr, ptr %local.out
  store float %t.2, ptr %t.3
  %t.4 = load float, ptr %local.a
  %t.5 = load float, ptr %local.b
  %t.6 = fmul float %t.4, %t.5
  %t.7 = load ptr, ptr %local.out
  store float %t.6, ptr %t.7
  ret void
}

