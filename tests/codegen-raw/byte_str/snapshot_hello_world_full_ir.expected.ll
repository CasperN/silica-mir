; Generated from Silica-MIR
declare void @abort()

define void @f() {
.init:
  %local.s = alloca [5 x i8], align 1
  br label %entry
entry:
  store [5 x i8] c"hello", ptr %local.s
  ret void
}

