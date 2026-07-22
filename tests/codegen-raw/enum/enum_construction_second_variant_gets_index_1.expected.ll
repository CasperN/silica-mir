; Generated from Silica-MIR
declare void @abort()

%E = type { i16, [6 x i8], [1 x i64] }

define void @f() {
.init:
  %local.e = alloca %E, align 8
  br label %entry
entry:
  %t.0 = getelementptr %E, ptr %local.e, i32 0, i32 0
  store i16 1, ptr %t.0
  ret void
}

