; Generated from Silica-MIR
declare void @abort()

define void @f(i64 %arg.x, ptr %arg.$return) {
.init:
  %local.$return = alloca ptr, align 8
  store ptr %arg.$return, ptr %local.$return
  %local.x = alloca i64, align 8
  store i64 %arg.x, ptr %local.x
  br label %entry
entry:
  %t.0 = load i64, ptr %local.x
  %t.1 = load ptr, ptr %local.$return
  store i64 %t.0, ptr %t.1
  ret void
}

