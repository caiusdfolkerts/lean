module
prelude
public import RootedSevenMixed030OutsideVerifiedLookup

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed030.Outside.Verified
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

theorem fastGenerator0_block_29 : Interval fastGenerator0 464 480 :=
  interval_of_check fastGenerator0 464 16 (by decide +kernel)

theorem fastGenerator0_block_30 : Interval fastGenerator0 480 496 :=
  interval_of_check fastGenerator0 480 16 (by decide +kernel)

theorem fastGenerator0_block_31 : Interval fastGenerator0 496 512 :=
  interval_of_check fastGenerator0 496 16 (by decide +kernel)

theorem fastGenerator0_block_32 : Interval fastGenerator0 512 528 :=
  interval_of_check fastGenerator0 512 16 (by decide +kernel)

theorem fastGenerator0_block_33 : Interval fastGenerator0 528 544 :=
  interval_of_check fastGenerator0 528 16 (by decide +kernel)

theorem fastGenerator0_block_34 : Interval fastGenerator0 544 560 :=
  interval_of_check fastGenerator0 544 16 (by decide +kernel)

theorem fastGenerator0_block_35 : Interval fastGenerator0 560 576 :=
  interval_of_check fastGenerator0 560 16 (by decide +kernel)

theorem fastGenerator0_block_36 : Interval fastGenerator0 576 592 :=
  interval_of_check fastGenerator0 576 16 (by decide +kernel)

theorem fastGenerator0_block_37 : Interval fastGenerator0 592 608 :=
  interval_of_check fastGenerator0 592 16 (by decide +kernel)

theorem fastGenerator0_block_38 : Interval fastGenerator0 608 624 :=
  interval_of_check fastGenerator0 608 16 (by decide +kernel)

theorem fastGenerator0_block_39 : Interval fastGenerator0 624 640 :=
  interval_of_check fastGenerator0 624 16 (by decide +kernel)

theorem fastGenerator0_block_40 : Interval fastGenerator0 640 655 :=
  interval_of_check fastGenerator0 640 15 (by decide +kernel)

theorem fastGenerator0_complete : Interval fastGenerator0 0 655 :=
  (interval_append fastGenerator0 0 320 655
  (interval_append fastGenerator0 0 160 320
  (interval_append fastGenerator0 0 80 160
  (interval_append fastGenerator0 0 32 80
  (interval_append fastGenerator0 0 16 32
  fastGenerator0_block_0
  fastGenerator0_block_1)
  (interval_append fastGenerator0 32 48 80
  fastGenerator0_block_2
  (interval_append fastGenerator0 48 64 80
  fastGenerator0_block_3
  fastGenerator0_block_4)))
  (interval_append fastGenerator0 80 112 160
  (interval_append fastGenerator0 80 96 112
  fastGenerator0_block_5
  fastGenerator0_block_6)
  (interval_append fastGenerator0 112 128 160
  fastGenerator0_block_7
  (interval_append fastGenerator0 128 144 160
  fastGenerator0_block_8
  fastGenerator0_block_9))))
  (interval_append fastGenerator0 160 240 320
  (interval_append fastGenerator0 160 192 240
  (interval_append fastGenerator0 160 176 192
  fastGenerator0_block_10
  fastGenerator0_block_11)
  (interval_append fastGenerator0 192 208 240
  fastGenerator0_block_12
  (interval_append fastGenerator0 208 224 240
  fastGenerator0_block_13
  fastGenerator0_block_14)))
  (interval_append fastGenerator0 240 272 320
  (interval_append fastGenerator0 240 256 272
  fastGenerator0_block_15
  fastGenerator0_block_16)
  (interval_append fastGenerator0 272 288 320
  fastGenerator0_block_17
  (interval_append fastGenerator0 288 304 320
  fastGenerator0_block_18
  fastGenerator0_block_19)))))
  (interval_append fastGenerator0 320 480 655
  (interval_append fastGenerator0 320 400 480
  (interval_append fastGenerator0 320 352 400
  (interval_append fastGenerator0 320 336 352
  fastGenerator0_block_20
  fastGenerator0_block_21)
  (interval_append fastGenerator0 352 368 400
  fastGenerator0_block_22
  (interval_append fastGenerator0 368 384 400
  fastGenerator0_block_23
  fastGenerator0_block_24)))
  (interval_append fastGenerator0 400 432 480
  (interval_append fastGenerator0 400 416 432
  fastGenerator0_block_25
  fastGenerator0_block_26)
  (interval_append fastGenerator0 432 448 480
  fastGenerator0_block_27
  (interval_append fastGenerator0 448 464 480
  fastGenerator0_block_28
  fastGenerator0_block_29))))
  (interval_append fastGenerator0 480 560 655
  (interval_append fastGenerator0 480 512 560
  (interval_append fastGenerator0 480 496 512
  fastGenerator0_block_30
  fastGenerator0_block_31)
  (interval_append fastGenerator0 512 528 560
  fastGenerator0_block_32
  (interval_append fastGenerator0 528 544 560
  fastGenerator0_block_33
  fastGenerator0_block_34)))
  (interval_append fastGenerator0 560 608 655
  (interval_append fastGenerator0 560 576 608
  fastGenerator0_block_35
  (interval_append fastGenerator0 576 592 608
  fastGenerator0_block_36
  fastGenerator0_block_37))
  (interval_append fastGenerator0 608 624 655
  fastGenerator0_block_38
  (interval_append fastGenerator0 624 640 655
  fastGenerator0_block_39
  fastGenerator0_block_40))))))
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed030.Outside.Verified
