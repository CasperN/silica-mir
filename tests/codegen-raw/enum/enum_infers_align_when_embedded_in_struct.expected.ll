; Generated from Silica-MIR
declare void @abort()

%E = type { i16, [6 x i8], [1 x i64] }
%S = type { i1, %E }

define void @f() {
.init:
  br label %entry
entry:
  ret void
}

