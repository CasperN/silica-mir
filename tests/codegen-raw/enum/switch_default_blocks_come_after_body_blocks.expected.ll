; Generated from Silica-MIR
declare void @abort()

%E = type { i16, [0 x i8], [0 x i16] }

define void @f(%E %arg.e) {
.init:
  %local.e = alloca %E, align 2
  store %E %arg.e, ptr %local.e
  br label %entry
entry:
  %t.0 = getelementptr %E, ptr %local.e, i32 0, i32 0
  %t.1 = load i16, ptr %t.0
  switch i16 %t.1, label %.switch_default.0 [
    i16 0, label %a_arm
    i16 1, label %b_arm
  ]
a_arm:
  ret void
b_arm:
  ret void
.switch_default.0:
  unreachable
}

