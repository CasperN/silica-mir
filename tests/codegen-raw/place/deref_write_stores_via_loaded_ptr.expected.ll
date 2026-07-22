; Generated from Silica-MIR
declare void @abort()

define void @f(ptr %arg.r) {
.init:
  %local.r = alloca ptr, align 8
  store ptr %arg.r, ptr %local.r
  br label %entry
entry:
  %t.0 = load ptr, ptr %local.r
  store i64 99, ptr %t.0
  ret void
}

