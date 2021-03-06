; NOTE: Assertions have been autogenerated by utils/update_test_checks.py
; RUN: opt < %s -instcombine -S | FileCheck %s

target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:128:128"

declare i32 @abs(i32)
declare i64 @labs(i64)
declare i64 @llabs(i64)

; Test that the abs library call simplifier works correctly.
; abs(x) -> x <s 0 ? -x : x.

define i32 @test_abs(i32 %x) {
; CHECK-LABEL: @test_abs(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp slt i32 [[X:%.*]], 0
; CHECK-NEXT:    [[NEG:%.*]] = sub nsw i32 0, [[X]]
; CHECK-NEXT:    [[TMP2:%.*]] = select i1 [[TMP1]], i32 [[NEG]], i32 [[X]]
; CHECK-NEXT:    ret i32 [[TMP2]]
;
  %ret = call i32 @abs(i32 %x)
  ret i32 %ret
}

define i64 @test_labs(i64 %x) {
; CHECK-LABEL: @test_labs(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp slt i64 [[X:%.*]], 0
; CHECK-NEXT:    [[NEG:%.*]] = sub nsw i64 0, [[X]]
; CHECK-NEXT:    [[TMP2:%.*]] = select i1 [[TMP1]], i64 [[NEG]], i64 [[X]]
; CHECK-NEXT:    ret i64 [[TMP2]]
;
  %ret = call i64 @labs(i64 %x)
  ret i64 %ret
}

define i64 @test_llabs(i64 %x) {
; CHECK-LABEL: @test_llabs(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp slt i64 [[X:%.*]], 0
; CHECK-NEXT:    [[NEG:%.*]] = sub nsw i64 0, [[X]]
; CHECK-NEXT:    [[TMP2:%.*]] = select i1 [[TMP1]], i64 [[NEG]], i64 [[X]]
; CHECK-NEXT:    ret i64 [[TMP2]]
;
  %ret = call i64 @llabs(i64 %x)
  ret i64 %ret
}

; We have a canonical form of abs to make CSE easier.

define i8 @abs_canonical_1(i8 %x) {
; CHECK-LABEL: @abs_canonical_1(
; CHECK-NEXT:    [[CMP:%.*]] = icmp slt i8 [[X:%.*]], 0
; CHECK-NEXT:    [[NEG:%.*]] = sub i8 0, [[X]]
; CHECK-NEXT:    [[ABS:%.*]] = select i1 [[CMP]], i8 [[NEG]], i8 [[X]]
; CHECK-NEXT:    ret i8 [[ABS]]
;
  %cmp = icmp sgt i8 %x, 0
  %neg = sub i8 0, %x
  %abs = select i1 %cmp, i8 %x, i8 %neg
  ret i8 %abs
}

; Vectors should work too.

define <2 x i8> @abs_canonical_2(<2 x i8> %x) {
; CHECK-LABEL: @abs_canonical_2(
; CHECK-NEXT:    [[CMP:%.*]] = icmp slt <2 x i8> [[X:%.*]], zeroinitializer
; CHECK-NEXT:    [[NEG:%.*]] = sub <2 x i8> zeroinitializer, [[X]]
; CHECK-NEXT:    [[ABS:%.*]] = select <2 x i1> [[CMP]], <2 x i8> [[NEG]], <2 x i8> [[X]]
; CHECK-NEXT:    ret <2 x i8> [[ABS]]
;
  %cmp = icmp sgt <2 x i8> %x, <i8 -1, i8 -1>
  %neg = sub <2 x i8> zeroinitializer, %x
  %abs = select <2 x i1> %cmp, <2 x i8> %x, <2 x i8> %neg
  ret <2 x i8> %abs
}

; NSW should not change.

define i8 @abs_canonical_3(i8 %x) {
; CHECK-LABEL: @abs_canonical_3(
; CHECK-NEXT:    [[CMP:%.*]] = icmp slt i8 [[X:%.*]], 0
; CHECK-NEXT:    [[NEG:%.*]] = sub nsw i8 0, [[X]]
; CHECK-NEXT:    [[ABS:%.*]] = select i1 [[CMP]], i8 [[NEG]], i8 [[X]]
; CHECK-NEXT:    ret i8 [[ABS]]
;
  %cmp = icmp slt i8 %x, 0
  %neg = sub nsw i8 0, %x
  %abs = select i1 %cmp, i8 %neg, i8 %x
  ret i8 %abs
}

define i8 @abs_canonical_4(i8 %x) {
; CHECK-LABEL: @abs_canonical_4(
; CHECK-NEXT:    [[CMP:%.*]] = icmp slt i8 [[X:%.*]], 0
; CHECK-NEXT:    [[NEG:%.*]] = sub i8 0, [[X]]
; CHECK-NEXT:    [[ABS:%.*]] = select i1 [[CMP]], i8 [[NEG]], i8 [[X]]
; CHECK-NEXT:    ret i8 [[ABS]]
;
  %cmp = icmp slt i8 %x, 1
  %neg = sub i8 0, %x
  %abs = select i1 %cmp, i8 %neg, i8 %x
  ret i8 %abs
}

; We have a canonical form of nabs to make CSE easier.

define i8 @nabs_canonical_1(i8 %x) {
; CHECK-LABEL: @nabs_canonical_1(
; CHECK-NEXT:    [[CMP:%.*]] = icmp slt i8 [[X:%.*]], 0
; CHECK-NEXT:    [[NEG:%.*]] = sub i8 0, [[X]]
; CHECK-NEXT:    [[ABS:%.*]] = select i1 [[CMP]], i8 [[X]], i8 [[NEG]]
; CHECK-NEXT:    ret i8 [[ABS]]
;
  %cmp = icmp sgt i8 %x, 0
  %neg = sub i8 0, %x
  %abs = select i1 %cmp, i8 %neg, i8 %x
  ret i8 %abs
}

; Vectors should work too.

define <2 x i8> @nabs_canonical_2(<2 x i8> %x) {
; CHECK-LABEL: @nabs_canonical_2(
; CHECK-NEXT:    [[CMP:%.*]] = icmp slt <2 x i8> [[X:%.*]], zeroinitializer
; CHECK-NEXT:    [[NEG:%.*]] = sub <2 x i8> zeroinitializer, [[X]]
; CHECK-NEXT:    [[ABS:%.*]] = select <2 x i1> [[CMP]], <2 x i8> [[X]], <2 x i8> [[NEG]]
; CHECK-NEXT:    ret <2 x i8> [[ABS]]
;
  %cmp = icmp sgt <2 x i8> %x, <i8 -1, i8 -1>
  %neg = sub <2 x i8> zeroinitializer, %x
  %abs = select <2 x i1> %cmp, <2 x i8> %neg, <2 x i8> %x
  ret <2 x i8> %abs
}

; NSW should not change.

define i8 @nabs_canonical_3(i8 %x) {
; CHECK-LABEL: @nabs_canonical_3(
; CHECK-NEXT:    [[CMP:%.*]] = icmp slt i8 [[X:%.*]], 0
; CHECK-NEXT:    [[NEG:%.*]] = sub nsw i8 0, [[X]]
; CHECK-NEXT:    [[ABS:%.*]] = select i1 [[CMP]], i8 [[X]], i8 [[NEG]]
; CHECK-NEXT:    ret i8 [[ABS]]
;
  %cmp = icmp slt i8 %x, 0
  %neg = sub nsw i8 0, %x
  %abs = select i1 %cmp, i8 %x, i8 %neg
  ret i8 %abs
}

define i8 @nabs_canonical_4(i8 %x) {
; CHECK-LABEL: @nabs_canonical_4(
; CHECK-NEXT:    [[CMP:%.*]] = icmp slt i8 [[X:%.*]], 0
; CHECK-NEXT:    [[NEG:%.*]] = sub i8 0, [[X]]
; CHECK-NEXT:    [[ABS:%.*]] = select i1 [[CMP]], i8 [[X]], i8 [[NEG]]
; CHECK-NEXT:    ret i8 [[ABS]]
;
  %cmp = icmp slt i8 %x, 1
  %neg = sub i8 0, %x
  %abs = select i1 %cmp, i8 %x, i8 %neg
  ret i8 %abs
}

; The following 5 tests use a shift+add+xor to implement abs():
; B = ashr i8 A, 7  -- smear the sign bit.
; xor (add A, B), B -- add -1 and flip bits if negative

define i8 @shifty_abs_commute0(i8 %x) {
; CHECK-LABEL: @shifty_abs_commute0(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp slt i8 [[X:%.*]], 0
; CHECK-NEXT:    [[TMP2:%.*]] = sub i8 0, [[X]]
; CHECK-NEXT:    [[ABS:%.*]] = select i1 [[TMP1]], i8 [[TMP2]], i8 [[X]]
; CHECK-NEXT:    ret i8 [[ABS]]
;
  %signbit = ashr i8 %x, 7
  %add = add i8 %signbit, %x
  %abs = xor i8 %add, %signbit
  ret i8 %abs
}

define i8 @shifty_abs_commute0_nsw(i8 %x) {
; CHECK-LABEL: @shifty_abs_commute0_nsw(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp slt i8 [[X:%.*]], 0
; CHECK-NEXT:    [[TMP2:%.*]] = sub nsw i8 0, [[X]]
; CHECK-NEXT:    [[ABS:%.*]] = select i1 [[TMP1]], i8 [[TMP2]], i8 [[X]]
; CHECK-NEXT:    ret i8 [[ABS]]
;
  %signbit = ashr i8 %x, 7
  %add = add nsw i8 %signbit, %x
  %abs = xor i8 %add, %signbit
  ret i8 %abs
}

; The nuw flag creates a contradiction. If the shift produces all 1s, the only
; way for the add to not wrap is for %x to be 0, but then the shift couldn't
; have produced all 1s. We partially optimize this.
define i8 @shifty_abs_commute0_nuw(i8 %x) {
; CHECK-LABEL: @shifty_abs_commute0_nuw(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp sgt i8 [[X:%.*]], 0
; CHECK-NEXT:    [[ABS:%.*]] = select i1 [[TMP1]], i8 [[X]], i8 0
; CHECK-NEXT:    ret i8 [[ABS]]
;
  %signbit = ashr i8 %x, 7
  %add = add nuw i8 %signbit, %x
  %abs = xor i8 %add, %signbit
  ret i8 %abs
}

define <2 x i8> @shifty_abs_commute1(<2 x i8> %x) {
; CHECK-LABEL: @shifty_abs_commute1(
; CHECK-NEXT:    [[TMP1:%.*]] = icmp slt <2 x i8> [[X:%.*]], zeroinitializer
; CHECK-NEXT:    [[TMP2:%.*]] = sub <2 x i8> zeroinitializer, [[X]]
; CHECK-NEXT:    [[ABS:%.*]] = select <2 x i1> [[TMP1]], <2 x i8> [[TMP2]], <2 x i8> [[X]]
; CHECK-NEXT:    ret <2 x i8> [[ABS]]
;
  %signbit = ashr <2 x i8> %x, <i8 7, i8 7>
  %add = add <2 x i8> %signbit, %x
  %abs = xor <2 x i8> %signbit, %add
  ret <2 x i8> %abs
}

define <2 x i8> @shifty_abs_commute2(<2 x i8> %x) {
; CHECK-LABEL: @shifty_abs_commute2(
; CHECK-NEXT:    [[Y:%.*]] = mul <2 x i8> [[X:%.*]], <i8 3, i8 3>
; CHECK-NEXT:    [[TMP1:%.*]] = icmp slt <2 x i8> [[Y]], zeroinitializer
; CHECK-NEXT:    [[TMP2:%.*]] = sub <2 x i8> zeroinitializer, [[Y]]
; CHECK-NEXT:    [[ABS:%.*]] = select <2 x i1> [[TMP1]], <2 x i8> [[TMP2]], <2 x i8> [[Y]]
; CHECK-NEXT:    ret <2 x i8> [[ABS]]
;
  %y = mul <2 x i8> %x, <i8 3, i8 3>   ; extra op to thwart complexity-based canonicalization
  %signbit = ashr <2 x i8> %y, <i8 7, i8 7>
  %add = add <2 x i8> %y, %signbit
  %abs = xor <2 x i8> %signbit, %add
  ret <2 x i8> %abs
}

define i8 @shifty_abs_commute3(i8 %x) {
; CHECK-LABEL: @shifty_abs_commute3(
; CHECK-NEXT:    [[Y:%.*]] = mul i8 [[X:%.*]], 3
; CHECK-NEXT:    [[TMP1:%.*]] = icmp slt i8 [[Y]], 0
; CHECK-NEXT:    [[TMP2:%.*]] = sub i8 0, [[Y]]
; CHECK-NEXT:    [[ABS:%.*]] = select i1 [[TMP1]], i8 [[TMP2]], i8 [[Y]]
; CHECK-NEXT:    ret i8 [[ABS]]
;
  %y = mul i8 %x, 3                    ; extra op to thwart complexity-based canonicalization
  %signbit = ashr i8 %y, 7
  %add = add i8 %y, %signbit
  %abs = xor i8 %add, %signbit
  ret i8 %abs
}

; Negative test - don't transform if it would increase instruction count.

declare void @extra_use(i8)

define i8 @shifty_abs_too_many_uses(i8 %x) {
; CHECK-LABEL: @shifty_abs_too_many_uses(
; CHECK-NEXT:    [[SIGNBIT:%.*]] = ashr i8 [[X:%.*]], 7
; CHECK-NEXT:    [[ADD:%.*]] = add i8 [[SIGNBIT]], [[X]]
; CHECK-NEXT:    [[ABS:%.*]] = xor i8 [[ADD]], [[SIGNBIT]]
; CHECK-NEXT:    call void @extra_use(i8 [[SIGNBIT]])
; CHECK-NEXT:    ret i8 [[ABS]]
;
  %signbit = ashr i8 %x, 7
  %add = add i8 %x, %signbit
  %abs = xor i8 %add, %signbit
  call void @extra_use(i8 %signbit)
  ret i8 %abs
}

