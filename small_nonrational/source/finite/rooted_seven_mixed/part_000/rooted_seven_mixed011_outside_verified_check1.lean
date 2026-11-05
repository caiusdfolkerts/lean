module
prelude
public import RootedSevenMixed011OutsideVerifiedLookup

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed011.Outside.Verified
open Papers.RationalityTen.FiniteChecks
def fastGenerator1 (i : Nat) := fastCellTest 1 i
theorem fastGenerator1_block_0 : Interval fastGenerator1 0 16 :=
  interval_of_check fastGenerator1 0 16 (by decide +kernel)

theorem fastGenerator1_block_1 : Interval fastGenerator1 16 32 :=
  interval_of_check fastGenerator1 16 16 (by decide +kernel)

theorem fastGenerator1_block_2 : Interval fastGenerator1 32 48 :=
  interval_of_check fastGenerator1 32 16 (by decide +kernel)

theorem fastGenerator1_block_3 : Interval fastGenerator1 48 64 :=
  interval_of_check fastGenerator1 48 16 (by decide +kernel)

theorem fastGenerator1_block_4 : Interval fastGenerator1 64 80 :=
  interval_of_check fastGenerator1 64 16 (by decide +kernel)

theorem fastGenerator1_block_5 : Interval fastGenerator1 80 96 :=
  interval_of_check fastGenerator1 80 16 (by decide +kernel)

theorem fastGenerator1_block_6 : Interval fastGenerator1 96 112 :=
  interval_of_check fastGenerator1 96 16 (by decide +kernel)

theorem fastGenerator1_block_7 : Interval fastGenerator1 112 128 :=
  interval_of_check fastGenerator1 112 16 (by decide +kernel)

theorem fastGenerator1_block_8 : Interval fastGenerator1 128 144 :=
  interval_of_check fastGenerator1 128 16 (by decide +kernel)

theorem fastGenerator1_block_9 : Interval fastGenerator1 144 160 :=
  interval_of_check fastGenerator1 144 16 (by decide +kernel)

theorem fastGenerator1_block_10 : Interval fastGenerator1 160 176 :=
  interval_of_check fastGenerator1 160 16 (by decide +kernel)

theorem fastGenerator1_block_11 : Interval fastGenerator1 176 192 :=
  interval_of_check fastGenerator1 176 16 (by decide +kernel)

theorem fastGenerator1_block_12 : Interval fastGenerator1 192 208 :=
  interval_of_check fastGenerator1 192 16 (by decide +kernel)

theorem fastGenerator1_block_13 : Interval fastGenerator1 208 224 :=
  interval_of_check fastGenerator1 208 16 (by decide +kernel)

theorem fastGenerator1_block_14 : Interval fastGenerator1 224 240 :=
  interval_of_check fastGenerator1 224 16 (by decide +kernel)

theorem fastGenerator1_block_15 : Interval fastGenerator1 240 256 :=
  interval_of_check fastGenerator1 240 16 (by decide +kernel)

theorem fastGenerator1_block_16 : Interval fastGenerator1 256 272 :=
  interval_of_check fastGenerator1 256 16 (by decide +kernel)

theorem fastGenerator1_block_17 : Interval fastGenerator1 272 288 :=
  interval_of_check fastGenerator1 272 16 (by decide +kernel)

theorem fastGenerator1_block_18 : Interval fastGenerator1 288 304 :=
  interval_of_check fastGenerator1 288 16 (by decide +kernel)

theorem fastGenerator1_block_19 : Interval fastGenerator1 304 320 :=
  interval_of_check fastGenerator1 304 16 (by decide +kernel)

theorem fastGenerator1_block_20 : Interval fastGenerator1 320 336 :=
  interval_of_check fastGenerator1 320 16 (by decide +kernel)

theorem fastGenerator1_block_21 : Interval fastGenerator1 336 352 :=
  interval_of_check fastGenerator1 336 16 (by decide +kernel)

theorem fastGenerator1_block_22 : Interval fastGenerator1 352 368 :=
  interval_of_check fastGenerator1 352 16 (by decide +kernel)

theorem fastGenerator1_block_23 : Interval fastGenerator1 368 384 :=
  interval_of_check fastGenerator1 368 16 (by decide +kernel)

theorem fastGenerator1_block_24 : Interval fastGenerator1 384 400 :=
  interval_of_check fastGenerator1 384 16 (by decide +kernel)

theorem fastGenerator1_block_25 : Interval fastGenerator1 400 416 :=
  interval_of_check fastGenerator1 400 16 (by decide +kernel)

theorem fastGenerator1_block_26 : Interval fastGenerator1 416 432 :=
  interval_of_check fastGenerator1 416 16 (by decide +kernel)

theorem fastGenerator1_block_27 : Interval fastGenerator1 432 448 :=
  interval_of_check fastGenerator1 432 16 (by decide +kernel)

theorem fastGenerator1_block_28 : Interval fastGenerator1 448 464 :=
  interval_of_check fastGenerator1 448 16 (by decide +kernel)

theorem fastGenerator1_block_29 : Interval fastGenerator1 464 480 :=
  interval_of_check fastGenerator1 464 16 (by decide +kernel)

theorem fastGenerator1_block_30 : Interval fastGenerator1 480 496 :=
  interval_of_check fastGenerator1 480 16 (by decide +kernel)

theorem fastGenerator1_block_31 : Interval fastGenerator1 496 512 :=
  interval_of_check fastGenerator1 496 16 (by decide +kernel)

theorem fastGenerator1_block_32 : Interval fastGenerator1 512 528 :=
  interval_of_check fastGenerator1 512 16 (by decide +kernel)

theorem fastGenerator1_block_33 : Interval fastGenerator1 528 544 :=
  interval_of_check fastGenerator1 528 16 (by decide +kernel)

theorem fastGenerator1_block_34 : Interval fastGenerator1 544 560 :=
  interval_of_check fastGenerator1 544 16 (by decide +kernel)

theorem fastGenerator1_block_35 : Interval fastGenerator1 560 576 :=
  interval_of_check fastGenerator1 560 16 (by decide +kernel)

theorem fastGenerator1_block_36 : Interval fastGenerator1 576 592 :=
  interval_of_check fastGenerator1 576 16 (by decide +kernel)

theorem fastGenerator1_block_37 : Interval fastGenerator1 592 608 :=
  interval_of_check fastGenerator1 592 16 (by decide +kernel)

theorem fastGenerator1_block_38 : Interval fastGenerator1 608 624 :=
  interval_of_check fastGenerator1 608 16 (by decide +kernel)

theorem fastGenerator1_block_39 : Interval fastGenerator1 624 640 :=
  interval_of_check fastGenerator1 624 16 (by decide +kernel)

theorem fastGenerator1_block_40 : Interval fastGenerator1 640 656 :=
  interval_of_check fastGenerator1 640 16 (by decide +kernel)

theorem fastGenerator1_block_41 : Interval fastGenerator1 656 658 :=
  interval_of_check fastGenerator1 656 2 (by decide +kernel)

theorem fastGenerator1_complete : Interval fastGenerator1 0 658 :=
  (interval_append fastGenerator1 0 336 658
  (interval_append fastGenerator1 0 160 336
  (interval_append fastGenerator1 0 80 160
  (interval_append fastGenerator1 0 32 80
  (interval_append fastGenerator1 0 16 32
  fastGenerator1_block_0
  fastGenerator1_block_1)
  (interval_append fastGenerator1 32 48 80
  fastGenerator1_block_2
  (interval_append fastGenerator1 48 64 80
  fastGenerator1_block_3
  fastGenerator1_block_4)))
  (interval_append fastGenerator1 80 112 160
  (interval_append fastGenerator1 80 96 112
  fastGenerator1_block_5
  fastGenerator1_block_6)
  (interval_append fastGenerator1 112 128 160
  fastGenerator1_block_7
  (interval_append fastGenerator1 128 144 160
  fastGenerator1_block_8
  fastGenerator1_block_9))))
  (interval_append fastGenerator1 160 240 336
  (interval_append fastGenerator1 160 192 240
  (interval_append fastGenerator1 160 176 192
  fastGenerator1_block_10
  fastGenerator1_block_11)
  (interval_append fastGenerator1 192 208 240
  fastGenerator1_block_12
  (interval_append fastGenerator1 208 224 240
  fastGenerator1_block_13
  fastGenerator1_block_14)))
  (interval_append fastGenerator1 240 288 336
  (interval_append fastGenerator1 240 256 288
  fastGenerator1_block_15
  (interval_append fastGenerator1 256 272 288
  fastGenerator1_block_16
  fastGenerator1_block_17))
  (interval_append fastGenerator1 288 304 336
  fastGenerator1_block_18
  (interval_append fastGenerator1 304 320 336
  fastGenerator1_block_19
  fastGenerator1_block_20)))))
  (interval_append fastGenerator1 336 496 658
  (interval_append fastGenerator1 336 416 496
  (interval_append fastGenerator1 336 368 416
  (interval_append fastGenerator1 336 352 368
  fastGenerator1_block_21
  fastGenerator1_block_22)
  (interval_append fastGenerator1 368 384 416
  fastGenerator1_block_23
  (interval_append fastGenerator1 384 400 416
  fastGenerator1_block_24
  fastGenerator1_block_25)))
  (interval_append fastGenerator1 416 448 496
  (interval_append fastGenerator1 416 432 448
  fastGenerator1_block_26
  fastGenerator1_block_27)
  (interval_append fastGenerator1 448 464 496
  fastGenerator1_block_28
  (interval_append fastGenerator1 464 480 496
  fastGenerator1_block_29
  fastGenerator1_block_30))))
  (interval_append fastGenerator1 496 576 658
  (interval_append fastGenerator1 496 528 576
  (interval_append fastGenerator1 496 512 528
  fastGenerator1_block_31
  fastGenerator1_block_32)
  (interval_append fastGenerator1 528 544 576
  fastGenerator1_block_33
  (interval_append fastGenerator1 544 560 576
  fastGenerator1_block_34
  fastGenerator1_block_35)))
  (interval_append fastGenerator1 576 624 658
  (interval_append fastGenerator1 576 592 624
  fastGenerator1_block_36
  (interval_append fastGenerator1 592 608 624
  fastGenerator1_block_37
  fastGenerator1_block_38))
  (interval_append fastGenerator1 624 640 658
  fastGenerator1_block_39
  (interval_append fastGenerator1 640 656 658
  fastGenerator1_block_40
  fastGenerator1_block_41))))))
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed011.Outside.Verified
