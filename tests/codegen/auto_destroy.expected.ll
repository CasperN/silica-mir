; Generated from Silica-MIR
declare void @abort()

%"Resource<i64>" = type { i64 }

define void @silica.main() {
.init:
  %local.resource = alloca %"Resource<i64>", align 8
  %local.$destroy_0 = alloca ptr, align 8
  br label %entry
entry:
  %t.0 = getelementptr %"Resource<i64>", ptr %local.resource, i32 0, i32 0
  store i64 42, ptr %t.0
  store ptr %local.resource, ptr %local.$destroy_0
  %t.1 = load ptr, ptr %local.$destroy_0
  call void @"<Resource<i64> as AutoDestroy>::destroy"(ptr %t.1)
  ret void
}

define void @"<Resource<i64> as AutoDestroy>::destroy"(ptr %arg.recv) {
.init:
  %local.recv = alloca ptr, align 8
  store ptr %arg.recv, ptr %local.recv
  br label %entry
entry:
  ret void
}

define i32 @main() {
  call void @silica.main()
  ret i32 0
}

