; Generated from Silica-MIR
declare void @abort()

%Row = type { [2 x i64] }

define void @f() {
.init:
  %local.r = alloca %Row, align 8
  %local.x = alloca i64, align 8
  br label %entry
entry:
  %t.0 = getelementptr %Row, ptr %local.r, i32 0, i32 0
  %t.1 = getelementptr i64, ptr %t.0, i64 0
  store i64 7, ptr %t.1
  %t.2 = getelementptr i64, ptr %t.0, i64 1
  store i64 42, ptr %t.2
  %t.3 = getelementptr %Row, ptr %local.r, i32 0, i32 0
  %t.4 = getelementptr i64, ptr %t.3, i64 1
  %t.5 = load i64, ptr %t.4
  store i64 %t.5, ptr %local.x
  ret void
}

