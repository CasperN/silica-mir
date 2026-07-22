; Generated from Silica-MIR
declare void @abort()

%P = type { i64, i64 }

define void @f() {
.init:
  %local.p = alloca %P, align 8
  br label %entry
entry:
  %t.0 = getelementptr %P, ptr %local.p, i32 0, i32 0
  store i64 7, ptr %t.0
  ret void
}

