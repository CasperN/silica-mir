; Generated from Silica-MIR
declare void @abort()

define void @f() {
.init:
  br label %entry
entry:
  call void @abort()
  unreachable
}

