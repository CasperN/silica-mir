; Generated from Silica-MIR
declare void @abort()

define void @silica.main(ptr %arg.exit) {
.init:
  %local.exit = alloca ptr, align 8
  store ptr %arg.exit, ptr %local.exit
  br label %entry
entry:
  %t.0 = load ptr, ptr %local.exit
  store i32 42, ptr %t.0
  ret void
}

define i32 @main() {
  %exit = alloca i32, align 4
  store i32 0, ptr %exit
  call void @silica.main(ptr %exit)
  %code = load i32, ptr %exit
  ret i32 %code
}

