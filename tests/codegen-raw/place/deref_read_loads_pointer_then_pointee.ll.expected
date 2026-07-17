; Generated from Silica-MIR
declare void @abort()

define void @f(ptr %arg.r) {
.init:
  %local.r = alloca ptr, align 8
  store ptr %arg.r, ptr %local.r
  %local.x = alloca i64, align 8
  br label %entry
entry:
  %t.0 = load ptr, ptr %local.r
  %t.1 = load i64, ptr %t.0
  store i64 %t.1, ptr %local.x
  ret void
}

