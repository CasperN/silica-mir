; Generated from Silica-MIR
declare void @abort()

declare void @callee(i64)

define void @f() {
.init:
  %local.g = alloca ptr, align 8
  br label %entry
entry:
  store ptr @callee, ptr %local.g
  %t.0 = load ptr, ptr %local.g
  call void %t.0(i64 1)
  ret void
}

