; Generated from Silica-MIR
declare void @abort()

define void @f(i32 %arg.i) {
.init:
  %local.i = alloca i32, align 4
  store i32 %arg.i, ptr %local.i
  %local.a = alloca [3 x i64], align 8
  %local.x = alloca i64, align 8
  br label %entry
entry:
  %t.0 = getelementptr i64, ptr %local.a, i64 0
  store i64 10, ptr %t.0
  %t.1 = getelementptr i64, ptr %local.a, i64 1
  store i64 20, ptr %t.1
  %t.2 = getelementptr i64, ptr %local.a, i64 2
  store i64 30, ptr %t.2
  %t.3 = load i32, ptr %local.i
  %t.4 = sext i32 %t.3 to i64
  %t.5 = getelementptr i64, ptr %local.a, i64 %t.4
  %t.6 = load i64, ptr %t.5
  store i64 %t.6, ptr %local.x
  ret void
}

