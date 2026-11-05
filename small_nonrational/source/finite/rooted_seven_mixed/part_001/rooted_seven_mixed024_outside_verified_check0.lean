module
prelude
public import RootedSevenMixed024OutsideVerifiedLookup

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed024.Outside.Verified
open Papers.RationalityTen.FiniteChecks
def fastGenerator0 (i : Nat) := fastCellTest 0 i
theorem fastGenerator0_block_0 : Interval fastGenerator0 0 16 :=
  interval_of_check fastGenerator0 0 16 (by decide +kernel)

theorem fastGenerator0_block_1 : Interval fastGenerator0 16 32 :=
  interval_of_check fastGenerator0 16 16 (by decide +kernel)

theorem fastGenerator0_block_2 : Interval fastGenerator0 32 48 :=
  interval_of_check fastGenerator0 32 16 (by decide +kernel)

theorem fastGenerator0_block_3 : Interval fastGenerator0 48 64 :=
  interval_of_check fastGenerator0 48 16 (by decide +kernel)

theorem fastGenerator0_block_4 : Interval fastGenerator0 64 80 :=
  interval_of_check fastGenerator0 64 16 (by decide +kernel)

theorem fastGenerator0_block_5 : Interval fastGenerator0 80 96 :=
  interval_of_check fastGenerator0 80 16 (by decide +kernel)

theorem fastGenerator0_block_6 : Interval fastGenerator0 96 112 :=
  interval_of_check fastGenerator0 96 16 (by decide +kernel)

theorem fastGenerator0_block_7 : Interval fastGenerator0 112 128 :=
  interval_of_check fastGenerator0 112 16 (by decide +kernel)

theorem fastGenerator0_block_8 : Interval fastGenerator0 128 144 :=
  interval_of_check fastGenerator0 128 16 (by decide +kernel)

theorem fastGenerator0_block_9 : Interval fastGenerator0 144 160 :=
  interval_of_check fastGenerator0 144 16 (by decide +kernel)

theorem fastGenerator0_block_10 : Interval fastGenerator0 160 176 :=
  interval_of_check fastGenerator0 160 16 (by decide +kernel)

theorem fastGenerator0_block_11 : Interval fastGenerator0 176 192 :=
  interval_of_check fastGenerator0 176 16 (by decide +kernel)

theorem fastGenerator0_block_12 : Interval fastGenerator0 192 208 :=
  interval_of_check fastGenerator0 192 16 (by decide +kernel)

theorem fastGenerator0_block_13 : Interval fastGenerator0 208 224 :=
  interval_of_check fastGenerator0 208 16 (by decide +kernel)

theorem fastGenerator0_block_14 : Interval fastGenerator0 224 240 :=
  interval_of_check fastGenerator0 224 16 (by decide +kernel)

theorem fastGenerator0_block_15 : Interval fastGenerator0 240 256 :=
  interval_of_check fastGenerator0 240 16 (by decide +kernel)

theorem fastGenerator0_block_16 : Interval fastGenerator0 256 272 :=
  interval_of_check fastGenerator0 256 16 (by decide +kernel)

theorem fastGenerator0_block_17 : Interval fastGenerator0 272 288 :=
  interval_of_check fastGenerator0 272 16 (by decide +kernel)

theorem fastGenerator0_block_18 : Interval fastGenerator0 288 304 :=
  interval_of_check fastGenerator0 288 16 (by decide +kernel)

theorem fastGenerator0_block_19 : Interval fastGenerator0 304 320 :=
  interval_of_check fastGenerator0 304 16 (by decide +kernel)

theorem fastGenerator0_block_20 : Interval fastGenerator0 320 336 :=
  interval_of_check fastGenerator0 320 16 (by decide +kernel)

theorem fastGenerator0_block_21 : Interval fastGenerator0 336 352 :=
  interval_of_check fastGenerator0 336 16 (by decide +kernel)

theorem fastGenerator0_block_22 : Interval fastGenerator0 352 368 :=
  interval_of_check fastGenerator0 352 16 (by decide +kernel)

theorem fastGenerator0_block_23 : Interval fastGenerator0 368 384 :=
  interval_of_check fastGenerator0 368 16 (by decide +kernel)

theorem fastGenerator0_block_24 : Interval fastGenerator0 384 400 :=
  interval_of_check fastGenerator0 384 16 (by decide +kernel)

theorem fastGenerator0_block_25 : Interval fastGenerator0 400 416 :=
  interval_of_check fastGenerator0 400 16 (by decide +kernel)

theorem fastGenerator0_block_26 : Interval fastGenerator0 416 432 :=
  interval_of_check fastGenerator0 416 16 (by decide +kernel)

theorem fastGenerator0_block_27 : Interval fastGenerator0 432 448 :=
  interval_of_check fastGenerator0 432 16 (by decide +kernel)

theorem fastGenerator0_block_28 : Interval fastGenerator0 448 464 :=
  interval_of_check fastGenerator0 448 16 (by decide +kernel)

theorem fastGenerator0_block_29 : Interval fastGenerator0 464 466 :=
  interval_of_check fastGenerator0 464 2 (by decide +kernel)

theorem fastGenerator0_complete : Interval fastGenerator0 0 466 :=
  (interval_append fastGenerator0 0 240 466
  (interval_append fastGenerator0 0 112 240
  (interval_append fastGenerator0 0 48 112
  (interval_append fastGenerator0 0 16 48
  fastGenerator0_block_0
  (interval_append fastGenerator0 16 32 48
  fastGenerator0_block_1
  fastGenerator0_block_2))
  (interval_append fastGenerator0 48 80 112
  (interval_append fastGenerator0 48 64 80
  fastGenerator0_block_3
  fastGenerator0_block_4)
  (interval_append fastGenerator0 80 96 112
  fastGenerator0_block_5
  fastGenerator0_block_6)))
  (interval_append fastGenerator0 112 176 240
  (interval_append fastGenerator0 112 144 176
  (interval_append fastGenerator0 112 128 144
  fastGenerator0_block_7
  fastGenerator0_block_8)
  (interval_append fastGenerator0 144 160 176
  fastGenerator0_block_9
  fastGenerator0_block_10))
  (interval_append fastGenerator0 176 208 240
  (interval_append fastGenerator0 176 192 208
  fastGenerator0_block_11
  fastGenerator0_block_12)
  (interval_append fastGenerator0 208 224 240
  fastGenerator0_block_13
  fastGenerator0_block_14))))
  (interval_append fastGenerator0 240 352 466
  (interval_append fastGenerator0 240 288 352
  (interval_append fastGenerator0 240 256 288
  fastGenerator0_block_15
  (interval_append fastGenerator0 256 272 288
  fastGenerator0_block_16
  fastGenerator0_block_17))
  (interval_append fastGenerator0 288 320 352
  (interval_append fastGenerator0 288 304 320
  fastGenerator0_block_18
  fastGenerator0_block_19)
  (interval_append fastGenerator0 320 336 352
  fastGenerator0_block_20
  fastGenerator0_block_21)))
  (interval_append fastGenerator0 352 416 466
  (interval_append fastGenerator0 352 384 416
  (interval_append fastGenerator0 352 368 384
  fastGenerator0_block_22
  fastGenerator0_block_23)
  (interval_append fastGenerator0 384 400 416
  fastGenerator0_block_24
  fastGenerator0_block_25))
  (interval_append fastGenerator0 416 448 466
  (interval_append fastGenerator0 416 432 448
  fastGenerator0_block_26
  fastGenerator0_block_27)
  (interval_append fastGenerator0 448 464 466
  fastGenerator0_block_28
  fastGenerator0_block_29)))))
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed024.Outside.Verified
