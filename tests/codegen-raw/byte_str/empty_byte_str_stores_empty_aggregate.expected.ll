; Generated from Silica-MIR
declare void @abort()

define void @f() {
.init:
  %local.s = alloca [0 x i8], align 1
  br label %entry
entry:
  store [0 x i8] c"", ptr %local.s
  ret void
}

