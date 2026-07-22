; Generated from Silica-MIR
declare void @abort()

define void @f(i1 %arg.b) {
.init:
  %local.b = alloca i1, align 1
  store i1 %arg.b, ptr %local.b
  %local.y = alloca i32, align 4
  %local.out = alloca ptr, align 8
  br label %entry
entry:
  store ptr %local.y, ptr %local.out
  %t.0 = load i1, ptr %local.b
  %t.1 = zext i1 %t.0 to i32
  %t.2 = load ptr, ptr %local.out
  store i32 %t.1, ptr %t.2
  ret void
}

