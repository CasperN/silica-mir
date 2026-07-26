; Generated from Silica-MIR
declare void @abort()

define void @$runtime_hook() {
.init:
  br label %entry
entry:
  ret void
}

define void @invoke_runtime_hook() {
.init:
  br label %entry
entry:
  call void @$runtime_hook()
  ret void
}

