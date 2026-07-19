; Generated from Silica-MIR
declare void @abort()

define void @callee(ptr %arg.$return) {
.init:
  %local.$return = alloca ptr, align 8
  store ptr %arg.$return, ptr %local.$return
  br label %entry
entry:
  %t.0 = load ptr, ptr %local.$return
  store i64 42, ptr %t.0
  ret void
}

define void @caller(ptr %arg.out) {
.init:
  %local.out = alloca ptr, align 8
  store ptr %arg.out, ptr %local.out
  br label %entry
entry:
  %t.0 = load ptr, ptr %local.out
  call void @callee(ptr %t.0)
  ret void
}

