; Generated from Silica-MIR
declare void @abort()

declare void @ext(i64, ptr)

define void @caller(ptr %arg.out) {
.init:
  %local.out = alloca ptr, align 8
  store ptr %arg.out, ptr %local.out
  br label %entry
entry:
  %t.0 = load ptr, ptr %local.out
  call void @ext(i64 42, ptr %t.0)
  ret void
}

