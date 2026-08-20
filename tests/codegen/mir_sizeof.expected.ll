; Generated from Silica-MIR
declare void @abort()

%$Tuple0 = type {  }
%Point = type { i64, i64 }

define void @silica.main(ptr %arg.$return) {
.init:
  %local.$return = alloca ptr, align 8
  store ptr %arg.$return, ptr %local.$return
  %local.s_point = alloca i64, align 8
  %local.s_int = alloca i64, align 8
  %local.sum = alloca i64, align 8
  %local.sum_i = alloca i64, align 8
  %local.out_point = alloca ptr, align 8
  %local.out_int = alloca ptr, align 8
  %local.out_sum = alloca ptr, align 8
  %local.out_i = alloca ptr, align 8
  %local.out_cast = alloca ptr, align 8
  br label %entry
entry:
  store ptr %local.s_point, ptr %local.out_point
  %t.0 = load ptr, ptr %local.out_point
  store i64 16, ptr %t.0
  store ptr %local.s_int, ptr %local.out_int
  %t.1 = load ptr, ptr %local.out_int
  store i64 8, ptr %t.1
  store ptr %local.sum, ptr %local.out_sum
  %t.2 = load i64, ptr %local.s_point
  %t.3 = load i64, ptr %local.s_int
  %t.4 = add i64 %t.2, %t.3
  %t.5 = load ptr, ptr %local.out_sum
  store i64 %t.4, ptr %t.5
  store ptr %local.sum_i, ptr %local.out_i
  %t.6 = load i64, ptr %local.sum
  %t.7 = load ptr, ptr %local.out_i
  store i64 %t.6, ptr %t.7
  %t.8 = load ptr, ptr %local.$return
  store ptr %t.8, ptr %local.out_cast
  %t.9 = load i64, ptr %local.sum_i
  %t.10 = trunc i64 %t.9 to i32
  %t.11 = load ptr, ptr %local.out_cast
  store i32 %t.10, ptr %t.11
  ret void
}

define i32 @main() {
  %exit = alloca i32, align 4
  call void @silica.main(ptr %exit)
  %code = load i32, ptr %exit
  ret i32 %code
}

