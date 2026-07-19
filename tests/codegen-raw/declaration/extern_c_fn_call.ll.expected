; Generated from Silica-MIR
declare void @abort()

declare i64 @get_value()

define void @caller(ptr %arg.$return) {
.init:
  %local.$return = alloca ptr, align 8
  store ptr %arg.$return, ptr %local.$return
  br label %entry
entry:
  %t.0 = load ptr, ptr %local.$return
  %t.1 = call i64 @get_value()
  store i64 %t.1, ptr %t.0
  ret void
}

