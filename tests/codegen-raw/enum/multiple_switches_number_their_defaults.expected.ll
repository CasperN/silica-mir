; Generated from Silica-MIR
declare void @abort()

%E = type { i16, [0 x i8], [0 x i16] }

define void @f(%E %arg.e, %E %arg.e2) {
.init:
  %local.e = alloca %E, align 2
  store %E %arg.e, ptr %local.e
  %local.e2 = alloca %E, align 2
  store %E %arg.e2, ptr %local.e2
  br label %entry
entry:
  %t.0 = getelementptr %E, ptr %local.e, i32 0, i32 0
  %t.1 = load i16, ptr %t.0
  switch i16 %t.1, label %.switch_default.0 [
    i16 0, label %a1
    i16 1, label %b1
  ]
a1:
  %t.2 = getelementptr %E, ptr %local.e2, i32 0, i32 0
  %t.3 = load i16, ptr %t.2
  switch i16 %t.3, label %.switch_default.1 [
    i16 0, label %a2
    i16 1, label %b2
  ]
b1:
  ret void
a2:
  ret void
b2:
  ret void
.switch_default.0:
  unreachable
.switch_default.1:
  unreachable
}

