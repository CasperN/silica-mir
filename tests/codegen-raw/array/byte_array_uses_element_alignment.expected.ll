; Generated from Silica-MIR
declare void @abort()

define void @f() {
.init:
  %local.b = alloca [4 x i8], align 1
  br label %entry
entry:
  %t.0 = getelementptr i8, ptr %local.b, i64 0
  store i8 65, ptr %t.0
  %t.1 = getelementptr i8, ptr %local.b, i64 1
  store i8 66, ptr %t.1
  %t.2 = getelementptr i8, ptr %local.b, i64 2
  store i8 67, ptr %t.2
  %t.3 = getelementptr i8, ptr %local.b, i64 3
  store i8 68, ptr %t.3
  ret void
}

