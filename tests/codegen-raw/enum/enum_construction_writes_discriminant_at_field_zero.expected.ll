; Generated from Silica-MIR
declare void @abort()

%E = type { i16, [6 x i8], [1 x i64] }

define void @f() {
.init:
  %local.e = alloca %E, align 8
  br label %entry
entry:
  %t.0 = getelementptr %E, ptr %local.e, i32 0, i32 0
  store i16 0, ptr %t.0
  %t.1 = getelementptr %E, ptr %local.e, i32 0, i32 2
  store i64 42, ptr %t.1
  ret void
}

