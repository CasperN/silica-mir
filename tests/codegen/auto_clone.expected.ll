; Generated from Silica-MIR
declare void @abort()

%Cloneable = type { i64 }

declare void @consume(%Cloneable)

define void @silica.main(ptr %arg.exit) {
.init:
  %local.exit = alloca ptr, align 8
  store ptr %arg.exit, ptr %local.exit
  %local.value = alloca %Cloneable, align 8
  %local.$clone_0 = alloca %Cloneable, align 8
  %local.$clone_1 = alloca ptr, align 8
  %local.$clone_2 = alloca ptr, align 8
  br label %entry
entry:
  %t.0 = getelementptr %Cloneable, ptr %local.value, i32 0, i32 0
  store i64 7, ptr %t.0
  store ptr %local.value, ptr %local.$clone_1
  store ptr %local.$clone_0, ptr %local.$clone_2
  %t.1 = load ptr, ptr %local.$clone_1
  %t.2 = load ptr, ptr %local.$clone_2
  call void @"<Cloneable as AutoClone>::clone"(ptr %t.1, ptr %t.2)
  %t.3 = load %Cloneable, ptr %local.$clone_0
  call void @consume(%Cloneable %t.3)
  %t.4 = load %Cloneable, ptr %local.value
  call void @consume(%Cloneable %t.4)
  %t.5 = load ptr, ptr %local.exit
  store i32 0, ptr %t.5
  ret void
}

define void @"<Cloneable as AutoClone>::clone"(ptr %arg.recv, ptr %arg.$return) {
.init:
  %local.$return = alloca ptr, align 8
  store ptr %arg.$return, ptr %local.$return
  %local.recv = alloca ptr, align 8
  store ptr %arg.recv, ptr %local.recv
  br label %entry
entry:
  %t.0 = load ptr, ptr %local.recv
  %t.1 = getelementptr %Cloneable, ptr %t.0, i32 0, i32 0
  %t.2 = load i64, ptr %t.1
  %t.3 = load ptr, ptr %local.$return
  %t.4 = getelementptr %Cloneable, ptr %t.3, i32 0, i32 0
  store i64 %t.2, ptr %t.4
  ret void
}

define i32 @main() {
  %exit = alloca i32, align 4
  store i32 0, ptr %exit
  call void @silica.main(ptr %exit)
  %code = load i32, ptr %exit
  ret i32 %code
}

