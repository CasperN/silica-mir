; Generated from Silica-MIR
declare void @abort()

%Counter = type { i64 }
%BorrowedCounter = type { ptr }
%"Box<i64>" = type { i64 }

define void @lifetime_dispatch(ptr %arg.left, ptr %arg.right) {
.init:
  %local.left = alloca ptr, align 8
  store ptr %arg.left, ptr %local.left
  %local.right = alloca ptr, align 8
  store ptr %arg.right, ptr %local.right
  br label %entry
entry:
  %t.0 = load ptr, ptr %local.left
  call void @"<BorrowedCounter as LifetimeRead>::lifetime_read"(ptr %t.0)
  %t.1 = load ptr, ptr %local.right
  call void @"<BorrowedCounter as LifetimeRead>::lifetime_read"(ptr %t.1)
  ret void
}

define void @silica.main(ptr %arg.exit) {
.init:
  %local.exit = alloca ptr, align 8
  store ptr %arg.exit, ptr %local.exit
  %local.counter = alloca %Counter, align 8
  %local.boxed = alloca %"Box<i64>", align 8
  %local.twice_result = alloca i64, align 8
  %local.identity_result = alloca i64, align 8
  %local.identity_bool_result = alloca i1, align 1
  %local.get_result = alloca i64, align 8
  %local.tagged_i64_result = alloca i64, align 8
  %local.tagged_bool_result = alloca i1, align 1
  %local.inherent_result = alloca i64, align 8
  %local.generic_inherent_result = alloca i64, align 8
  %local.twice_recv = alloca ptr, align 8
  %local.twice_out = alloca ptr, align 8
  %local.identity_recv = alloca ptr, align 8
  %local.identity_out = alloca ptr, align 8
  %local.identity_bool_out = alloca ptr, align 8
  %local.get_recv = alloca ptr, align 8
  %local.get_out = alloca ptr, align 8
  %local.tagged_recv = alloca ptr, align 8
  %local.tagged_i64_out = alloca ptr, align 8
  %local.tagged_bool_out = alloca ptr, align 8
  %local.inherent_recv = alloca ptr, align 8
  %local.inherent_out = alloca ptr, align 8
  %local.generic_inherent_out = alloca ptr, align 8
  br label %entry
entry:
  %t.0 = getelementptr %Counter, ptr %local.counter, i32 0, i32 0
  store i64 5, ptr %t.0
  %t.1 = getelementptr %"Box<i64>", ptr %local.boxed, i32 0, i32 0
  store i64 9, ptr %t.1
  store ptr %local.counter, ptr %local.twice_recv
  store ptr %local.twice_result, ptr %local.twice_out
  %t.2 = load ptr, ptr %local.twice_recv
  %t.3 = load ptr, ptr %local.twice_out
  call void @"<Counter as Twice>::twice"(ptr %t.2, ptr %t.3)
  store ptr %local.counter, ptr %local.identity_recv
  store ptr %local.identity_result, ptr %local.identity_out
  %t.4 = load ptr, ptr %local.identity_recv
  %t.5 = load ptr, ptr %local.identity_out
  call void @"<Counter as Identity>::id<i64>"(ptr %t.4, i64 7, ptr %t.5)
  store ptr %local.counter, ptr %local.identity_recv
  store ptr %local.identity_bool_result, ptr %local.identity_bool_out
  %t.6 = load ptr, ptr %local.identity_recv
  %t.7 = load ptr, ptr %local.identity_bool_out
  call void @"<Counter as Identity>::id<bool>"(ptr %t.6, i1 true, ptr %t.7)
  store ptr %local.boxed, ptr %local.get_recv
  store ptr %local.get_result, ptr %local.get_out
  %t.8 = load ptr, ptr %local.get_recv
  %t.9 = load ptr, ptr %local.get_out
  call void @"<Box<i64> as Get<i64>>::get"(ptr %t.8, ptr %t.9)
  store ptr %local.counter, ptr %local.tagged_recv
  store ptr %local.tagged_i64_result, ptr %local.tagged_i64_out
  %t.10 = load ptr, ptr %local.tagged_recv
  %t.11 = load ptr, ptr %local.tagged_i64_out
  call void @"<Counter as Tagged<i64>>::tagged"(ptr %t.10, ptr %t.11)
  store ptr %local.counter, ptr %local.tagged_recv
  store ptr %local.tagged_bool_result, ptr %local.tagged_bool_out
  %t.12 = load ptr, ptr %local.tagged_recv
  %t.13 = load ptr, ptr %local.tagged_bool_out
  call void @"<Counter as Tagged<bool>>::tagged"(ptr %t.12, ptr %t.13)
  store ptr %local.counter, ptr %local.inherent_recv
  store ptr %local.inherent_result, ptr %local.inherent_out
  %t.14 = load ptr, ptr %local.inherent_recv
  %t.15 = load ptr, ptr %local.inherent_out
  call void @"<Counter>::inherent_read"(ptr %t.14, ptr %t.15)
  store ptr %local.boxed, ptr %local.get_recv
  store ptr %local.generic_inherent_result, ptr %local.generic_inherent_out
  %t.16 = load ptr, ptr %local.get_recv
  %t.17 = load ptr, ptr %local.generic_inherent_out
  call void @"inherent_dispatch<i64>"(ptr %t.16, ptr %t.17)
  %t.18 = load ptr, ptr %local.exit
  store i32 0, ptr %t.18
  ret void
}

define void @"<BorrowedCounter as LifetimeRead>::lifetime_read"(ptr %arg.recv) {
.init:
  %local.recv = alloca ptr, align 8
  store ptr %arg.recv, ptr %local.recv
  br label %entry
entry:
  ret void
}

define void @"<Counter as Twice>::twice"(ptr %arg.recv, ptr %arg.$return) {
.init:
  %local.$return = alloca ptr, align 8
  store ptr %arg.$return, ptr %local.$return
  %local.recv = alloca ptr, align 8
  store ptr %arg.recv, ptr %local.recv
  %local.inner = alloca i64, align 8
  %local.inner_out = alloca ptr, align 8
  br label %entry
entry:
  store ptr %local.inner, ptr %local.inner_out
  %t.0 = load ptr, ptr %local.recv
  %t.1 = load ptr, ptr %local.inner_out
  call void @"<Counter as Read>::read"(ptr %t.0, ptr %t.1)
  %t.2 = load i64, ptr %local.inner
  %t.3 = load ptr, ptr %local.$return
  store i64 %t.2, ptr %t.3
  ret void
}

define void @"<Counter as Identity>::id<i64>"(ptr %arg.recv, i64 %arg.value, ptr %arg.$return) {
.init:
  %local.$return = alloca ptr, align 8
  store ptr %arg.$return, ptr %local.$return
  %local.recv = alloca ptr, align 8
  store ptr %arg.recv, ptr %local.recv
  %local.value = alloca i64, align 8
  store i64 %arg.value, ptr %local.value
  br label %entry
entry:
  %t.0 = load i64, ptr %local.value
  %t.1 = load ptr, ptr %local.$return
  store i64 %t.0, ptr %t.1
  ret void
}

define void @"<Counter as Identity>::id<bool>"(ptr %arg.recv, i1 %arg.value, ptr %arg.$return) {
.init:
  %local.$return = alloca ptr, align 8
  store ptr %arg.$return, ptr %local.$return
  %local.recv = alloca ptr, align 8
  store ptr %arg.recv, ptr %local.recv
  %local.value = alloca i1, align 1
  store i1 %arg.value, ptr %local.value
  br label %entry
entry:
  %t.0 = load i1, ptr %local.value
  %t.1 = load ptr, ptr %local.$return
  store i1 %t.0, ptr %t.1
  ret void
}

define void @"<Box<i64> as Get<i64>>::get"(ptr %arg.recv, ptr %arg.$return) {
.init:
  %local.$return = alloca ptr, align 8
  store ptr %arg.$return, ptr %local.$return
  %local.recv = alloca ptr, align 8
  store ptr %arg.recv, ptr %local.recv
  br label %entry
entry:
  %t.0 = load ptr, ptr %local.recv
  %t.1 = getelementptr %"Box<i64>", ptr %t.0, i32 0, i32 0
  %t.2 = load i64, ptr %t.1
  %t.3 = load ptr, ptr %local.$return
  store i64 %t.2, ptr %t.3
  ret void
}

define void @"<Counter as Tagged<i64>>::tagged"(ptr %arg.recv, ptr %arg.$return) {
.init:
  %local.$return = alloca ptr, align 8
  store ptr %arg.$return, ptr %local.$return
  %local.recv = alloca ptr, align 8
  store ptr %arg.recv, ptr %local.recv
  br label %entry
entry:
  %t.0 = load ptr, ptr %local.recv
  %t.1 = getelementptr %Counter, ptr %t.0, i32 0, i32 0
  %t.2 = load i64, ptr %t.1
  %t.3 = load ptr, ptr %local.$return
  store i64 %t.2, ptr %t.3
  ret void
}

define void @"<Counter as Tagged<bool>>::tagged"(ptr %arg.recv, ptr %arg.$return) {
.init:
  %local.$return = alloca ptr, align 8
  store ptr %arg.$return, ptr %local.$return
  %local.recv = alloca ptr, align 8
  store ptr %arg.recv, ptr %local.recv
  br label %entry
entry:
  %t.0 = load ptr, ptr %local.$return
  store i1 true, ptr %t.0
  ret void
}

define void @"<Counter>::inherent_read"(ptr %arg.recv, ptr %arg.$return) {
.init:
  %local.$return = alloca ptr, align 8
  store ptr %arg.$return, ptr %local.$return
  %local.recv = alloca ptr, align 8
  store ptr %arg.recv, ptr %local.recv
  br label %entry
entry:
  %t.0 = load ptr, ptr %local.recv
  %t.1 = getelementptr %Counter, ptr %t.0, i32 0, i32 0
  %t.2 = load i64, ptr %t.1
  %t.3 = load ptr, ptr %local.$return
  store i64 %t.2, ptr %t.3
  ret void
}

define void @"inherent_dispatch<i64>"(ptr %arg.recv, ptr %arg.$return) {
.init:
  %local.$return = alloca ptr, align 8
  store ptr %arg.$return, ptr %local.$return
  %local.recv = alloca ptr, align 8
  store ptr %arg.recv, ptr %local.recv
  br label %entry
entry:
  %t.0 = load ptr, ptr %local.recv
  %t.1 = load ptr, ptr %local.$return
  call void @"<Box<i64>>::inherent_get"(ptr %t.0, ptr %t.1)
  ret void
}

define void @"<Counter as Read>::read"(ptr %arg.recv, ptr %arg.$return) {
.init:
  %local.$return = alloca ptr, align 8
  store ptr %arg.$return, ptr %local.$return
  %local.recv = alloca ptr, align 8
  store ptr %arg.recv, ptr %local.recv
  br label %entry
entry:
  %t.0 = load ptr, ptr %local.recv
  %t.1 = getelementptr %Counter, ptr %t.0, i32 0, i32 0
  %t.2 = load i64, ptr %t.1
  %t.3 = load ptr, ptr %local.$return
  store i64 %t.2, ptr %t.3
  ret void
}

define void @"<Box<i64>>::inherent_get"(ptr %arg.recv, ptr %arg.$return) {
.init:
  %local.$return = alloca ptr, align 8
  store ptr %arg.$return, ptr %local.$return
  %local.recv = alloca ptr, align 8
  store ptr %arg.recv, ptr %local.recv
  br label %entry
entry:
  %t.0 = load ptr, ptr %local.recv
  %t.1 = getelementptr %"Box<i64>", ptr %t.0, i32 0, i32 0
  %t.2 = load i64, ptr %t.1
  %t.3 = load ptr, ptr %local.$return
  store i64 %t.2, ptr %t.3
  ret void
}

define i32 @main() {
  %exit = alloca i32, align 4
  store i32 0, ptr %exit
  call void @silica.main(ptr %exit)
  %code = load i32, ptr %exit
  ret i32 %code
}

