; Generated from Silica-MIR
declare void @abort()

define void @f() {
.init:
  %local.x = alloca i64, align 8
  %local.a = alloca ptr, align 8
  %local.b = alloca ptr, align 8
  %local.c = alloca ptr, align 8
  %local.d = alloca ptr, align 8
  %local.e = alloca ptr, align 8
  br label %entry
entry:
  store i64 0, ptr %local.x
  store ptr %local.x, ptr %local.a
  store ptr %local.x, ptr %local.b
  ret void
}

