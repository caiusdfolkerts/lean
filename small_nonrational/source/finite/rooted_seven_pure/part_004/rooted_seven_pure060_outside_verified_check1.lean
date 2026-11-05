module
prelude
public import RootedSevenPure060OutsideVerifiedLookup

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSevenPure060.Outside.Verified
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

theorem fastGenerator1_block_25 : Interval fastGenerator1 400 406 :=
  interval_of_check fastGenerator1 400 6 (by decide +kernel)

theorem fastGenerator1_complete : Interval fastGenerator1 0 406 :=
  (interval_append fastGenerator1 0 208 406
  (interval_append fastGenerator1 0 96 208
  (interval_append fastGenerator1 0 48 96
  (interval_append fastGenerator1 0 16 48
  fastGenerator1_block_0
  (interval_append fastGenerator1 16 32 48
  fastGenerator1_block_1
  fastGenerator1_block_2))
  (interval_append fastGenerator1 48 64 96
  fastGenerator1_block_3
  (interval_append fastGenerator1 64 80 96
  fastGenerator1_block_4
  fastGenerator1_block_5)))
  (interval_append fastGenerator1 96 144 208
  (interval_append fastGenerator1 96 112 144
  fastGenerator1_block_6
  (interval_append fastGenerator1 112 128 144
  fastGenerator1_block_7
  fastGenerator1_block_8))
  (interval_append fastGenerator1 144 176 208
  (interval_append fastGenerator1 144 160 176
  fastGenerator1_block_9
  fastGenerator1_block_10)
  (interval_append fastGenerator1 176 192 208
  fastGenerator1_block_11
  fastGenerator1_block_12))))
  (interval_append fastGenerator1 208 304 406
  (interval_append fastGenerator1 208 256 304
  (interval_append fastGenerator1 208 224 256
  fastGenerator1_block_13
  (interval_append fastGenerator1 224 240 256
  fastGenerator1_block_14
  fastGenerator1_block_15))
  (interval_append fastGenerator1 256 272 304
  fastGenerator1_block_16
  (interval_append fastGenerator1 272 288 304
  fastGenerator1_block_17
  fastGenerator1_block_18)))
  (interval_append fastGenerator1 304 352 406
  (interval_append fastGenerator1 304 320 352
  fastGenerator1_block_19
  (interval_append fastGenerator1 320 336 352
  fastGenerator1_block_20
  fastGenerator1_block_21))
  (interval_append fastGenerator1 352 384 406
  (interval_append fastGenerator1 352 368 384
  fastGenerator1_block_22
  fastGenerator1_block_23)
  (interval_append fastGenerator1 384 400 406
  fastGenerator1_block_24
  fastGenerator1_block_25)))))
end Papers.RationalityTen.FacetUniverses.RootedSevenPure060.Outside.Verified
