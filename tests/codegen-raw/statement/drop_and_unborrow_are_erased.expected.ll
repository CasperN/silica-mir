; Generated from Silica-MIR
declare void @abort()

define void @f(ptr %arg.r) {
.init:
  %local.r = alloca ptr, align 8
  store ptr %arg.r, ptr %local.r
  %local.x = alloca i64, align 8
  br label %entry
entry:
  store i64 0, ptr %local.x
  ret void
}

