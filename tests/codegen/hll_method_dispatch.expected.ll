; Generated from Silica-MIR
declare void @abort()

%Counter = type { i32 }

define void @free_value(ptr %arg.recv, ptr %arg.$return) {
.init:
  %local.$return = alloca ptr, align 8
  store ptr %arg.$return, ptr %local.$return
  %local.recv = alloca ptr, align 8
  store ptr %arg.recv, ptr %local.recv
  br label %entry
entry:
  %t.0 = load ptr, ptr %local.recv
  %t.1 = getelementptr %Counter, ptr %t.0, i32 0, i32 0
  %t.2 = load i32, ptr %t.1
  %t.3 = load ptr, ptr %local.$return
  store i32 %t.2, ptr %t.3
  ret void
}

define void @silica.main(ptr %arg.$return) {
.init:
  %local.$return = alloca ptr, align 8
  store ptr %arg.$return, ptr %local.$return
  %local.counter = alloca %Counter, align 4
  %local.$tmp_0 = alloca i32, align 4
  %local.$tmp_1 = alloca i32, align 4
  %local.$tmp_2 = alloca ptr, align 8
  %local.$tmp_3 = alloca ptr, align 8
  %local.$tmp_4 = alloca i32, align 4
  %local.$tmp_5 = alloca ptr, align 8
  %local.$tmp_6 = alloca ptr, align 8
  %local.$tmp_7 = alloca ptr, align 8
  %local.$tmp_8 = alloca i32, align 4
  %local.$tmp_9 = alloca ptr, align 8
  %local.$tmp_10 = alloca ptr, align 8
  %local.$tmp_11 = alloca ptr, align 8
  br label %entry
entry:
  %t.0 = getelementptr %Counter, ptr %local.counter, i32 0, i32 0
  store i32 14, ptr %t.0
  store ptr %local.counter, ptr %local.$tmp_2
  store ptr %local.$tmp_1, ptr %local.$tmp_3
  %t.1 = load ptr, ptr %local.$tmp_2
  %t.2 = load ptr, ptr %local.$tmp_3
  call void @"<Counter>::inherent_value"(ptr %t.1, ptr %t.2)
  store ptr %local.counter, ptr %local.$tmp_5
  store ptr %local.$tmp_4, ptr %local.$tmp_6
  %t.3 = load ptr, ptr %local.$tmp_5
  %t.4 = load ptr, ptr %local.$tmp_6
  call void @"<Counter as CounterValue>::trait_value"(ptr %t.3, ptr %t.4)
  store ptr %local.$tmp_0, ptr %local.$tmp_7
  %t.5 = load i32, ptr %local.$tmp_1
  %t.6 = load i32, ptr %local.$tmp_4
  %t.7 = add i32 %t.5, %t.6
  %t.8 = load ptr, ptr %local.$tmp_7
  store i32 %t.7, ptr %t.8
  store ptr %local.counter, ptr %local.$tmp_9
  store ptr %local.$tmp_8, ptr %local.$tmp_10
  %t.9 = load ptr, ptr %local.$tmp_9
  %t.10 = load ptr, ptr %local.$tmp_10
  call void @free_value(ptr %t.9, ptr %t.10)
  %t.11 = load ptr, ptr %local.$return
  store ptr %t.11, ptr %local.$tmp_11
  %t.12 = load i32, ptr %local.$tmp_0
  %t.13 = load i32, ptr %local.$tmp_8
  %t.14 = add i32 %t.12, %t.13
  %t.15 = load ptr, ptr %local.$tmp_11
  store i32 %t.14, ptr %t.15
  ret void
}

define void @"<Counter>::inherent_value"(ptr %arg.recv, ptr %arg.$return) {
.init:
  %local.$return = alloca ptr, align 8
  store ptr %arg.$return, ptr %local.$return
  %local.recv = alloca ptr, align 8
  store ptr %arg.recv, ptr %local.recv
  br label %entry
entry:
  %t.0 = load ptr, ptr %local.recv
  %t.1 = getelementptr %Counter, ptr %t.0, i32 0, i32 0
  %t.2 = load i32, ptr %t.1
  %t.3 = load ptr, ptr %local.$return
  store i32 %t.2, ptr %t.3
  ret void
}

define void @"<Counter as CounterValue>::trait_value"(ptr %arg.recv, ptr %arg.$return) {
.init:
  %local.$return = alloca ptr, align 8
  store ptr %arg.$return, ptr %local.$return
  %local.recv = alloca ptr, align 8
  store ptr %arg.recv, ptr %local.recv
  br label %entry
entry:
  %t.0 = load ptr, ptr %local.recv
  %t.1 = getelementptr %Counter, ptr %t.0, i32 0, i32 0
  %t.2 = load i32, ptr %t.1
  %t.3 = load ptr, ptr %local.$return
  store i32 %t.2, ptr %t.3
  ret void
}

define i32 @main() {
  %exit = alloca i32, align 4
  call void @silica.main(ptr %exit)
  %code = load i32, ptr %exit
  ret i32 %code
}

