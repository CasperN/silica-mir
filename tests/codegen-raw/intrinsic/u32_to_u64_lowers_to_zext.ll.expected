; Generated from Silica-MIR
declare void @abort()

define void @f(i32 %arg.x) {
.init:
  %local.x = alloca i32, align 4
  store i32 %arg.x, ptr %local.x
  %local.y = alloca i64, align 8
  %local.out = alloca ptr, align 8
  br label %entry
entry:
  store ptr %local.y, ptr %local.out
  %t.0 = load i32, ptr %local.x
  %t.1 = zext i32 %t.0 to i64
  %t.2 = load ptr, ptr %local.out
  store i64 %t.1, ptr %t.2
  ret void
}

