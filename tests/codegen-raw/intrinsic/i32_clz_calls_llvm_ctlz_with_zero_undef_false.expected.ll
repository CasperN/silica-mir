; Generated from Silica-MIR
declare void @abort()
declare i32 @llvm.ctlz.i32(i32, i1)

define void @f(i32 %arg.x) {
.init:
  %local.x = alloca i32, align 4
  store i32 %arg.x, ptr %local.x
  %local.y = alloca i32, align 4
  %local.out = alloca ptr, align 8
  br label %entry
entry:
  store ptr %local.y, ptr %local.out
  %t.0 = load i32, ptr %local.x
  %t.1 = call i32 @llvm.ctlz.i32(i32 %t.0, i1 false)
  %t.2 = load ptr, ptr %local.out
  store i32 %t.1, ptr %t.2
  ret void
}

