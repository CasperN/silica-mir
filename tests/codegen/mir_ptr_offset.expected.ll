; Generated from Silica-MIR
declare void @abort()

declare void @deref_i64(ptr, ptr)

define void @silica.main(ptr %arg.$return) {
.init:
  %local.$return = alloca ptr, align 8
  store ptr %arg.$return, ptr %local.$return
  %local.arr = alloca [3 x i64], align 8
  %local.base = alloca ptr, align 8
  %local.off = alloca ptr, align 8
  %local.idx = alloca i64, align 8
  %local.val = alloca i64, align 8
  %local._tmp = alloca ptr, align 8
  %local.out_off = alloca ptr, align 8
  %local.out_val = alloca ptr, align 8
  %local.out_cast = alloca ptr, align 8
  br label %entry
entry:
  %t.0 = getelementptr i64, ptr %local.arr, i64 0
  store i64 10, ptr %t.0
  %t.1 = getelementptr i64, ptr %local.arr, i64 1
  store i64 20, ptr %t.1
  %t.2 = getelementptr i64, ptr %local.arr, i64 2
  store i64 30, ptr %t.2
  %t.3 = getelementptr i64, ptr %local.arr, i64 0
  store ptr %t.3, ptr %local._tmp
  %t.4 = load ptr, ptr %local._tmp
  store ptr %t.4, ptr %local.base
  store i64 2, ptr %local.idx
  store ptr %local.off, ptr %local.out_off
  %t.5 = load ptr, ptr %local.base
  %t.6 = load i64, ptr %local.idx
  %t.7 = getelementptr i64, ptr %t.5, i64 %t.6
  %t.8 = load ptr, ptr %local.out_off
  store ptr %t.7, ptr %t.8
  store ptr %local.val, ptr %local.out_val
  %t.9 = load ptr, ptr %local.off
  %t.10 = load ptr, ptr %local.out_val
  call void @deref_i64(ptr %t.9, ptr %t.10)
  %t.11 = load ptr, ptr %local.$return
  store ptr %t.11, ptr %local.out_cast
  %t.12 = load i64, ptr %local.val
  %t.13 = trunc i64 %t.12 to i32
  %t.14 = load ptr, ptr %local.out_cast
  store i32 %t.13, ptr %t.14
  ret void
}

define i32 @main() {
  %exit = alloca i32, align 4
  call void @silica.main(ptr %exit)
  %code = load i32, ptr %exit
  ret i32 %code
}

