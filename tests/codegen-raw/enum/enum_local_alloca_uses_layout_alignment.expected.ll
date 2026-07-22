; Generated from Silica-MIR
declare void @abort()

%E = type { i16, [6 x i8], [1 x i64] }

define void @f() {
.init:
  %local.e = alloca %E, align 8
  br label %entry
entry:
  ret void
}

