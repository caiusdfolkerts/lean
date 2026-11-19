module
prelude
public meta import LowerSchemas.FiniteRootedSevenMixed
public import RootedSevenMixed029OutsideVerifiedLookup

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed029.Outside.Verified
open Papers.RationalityTen.FiniteChecks
cert_fastGenerator 1
cert_fastGenerator_block 1 0 0 16 16
cert_fastGenerator_block 1 1 16 32 16
cert_fastGenerator_block 1 2 32 48 16
cert_fastGenerator_block 1 3 48 64 16
cert_fastGenerator_block 1 4 64 80 16
cert_fastGenerator_block 1 5 80 96 16
cert_fastGenerator_block 1 6 96 112 16
cert_fastGenerator_block 1 7 112 128 16
cert_fastGenerator_block 1 8 128 144 16
cert_fastGenerator_block 1 9 144 160 16
cert_fastGenerator_block 1 10 160 176 16
cert_fastGenerator_block 1 11 176 192 16
cert_fastGenerator_block 1 12 192 208 16
cert_fastGenerator_block 1 13 208 224 16
cert_fastGenerator_block 1 14 224 240 16
cert_fastGenerator_block 1 15 240 256 16
cert_fastGenerator_block 1 16 256 272 16
cert_fastGenerator_block 1 17 272 288 16
cert_fastGenerator_block 1 18 288 304 16
cert_fastGenerator_block 1 19 304 320 16
cert_fastGenerator_block 1 20 320 336 16
cert_fastGenerator_block 1 21 336 352 16
cert_fastGenerator_block 1 22 352 368 16
cert_fastGenerator_block 1 23 368 376 8
theorem fastGenerator1_complete : Interval fastGenerator1 0 376 :=
  (interval_append fastGenerator1 0 192 376
  (interval_append fastGenerator1 0 96 192
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
  (interval_append fastGenerator1 96 144 192
  (interval_append fastGenerator1 96 112 144
  fastGenerator1_block_6
  (interval_append fastGenerator1 112 128 144
  fastGenerator1_block_7
  fastGenerator1_block_8))
  (interval_append fastGenerator1 144 160 192
  fastGenerator1_block_9
  (interval_append fastGenerator1 160 176 192
  fastGenerator1_block_10
  fastGenerator1_block_11))))
  (interval_append fastGenerator1 192 288 376
  (interval_append fastGenerator1 192 240 288
  (interval_append fastGenerator1 192 208 240
  fastGenerator1_block_12
  (interval_append fastGenerator1 208 224 240
  fastGenerator1_block_13
  fastGenerator1_block_14))
  (interval_append fastGenerator1 240 256 288
  fastGenerator1_block_15
  (interval_append fastGenerator1 256 272 288
  fastGenerator1_block_16
  fastGenerator1_block_17)))
  (interval_append fastGenerator1 288 336 376
  (interval_append fastGenerator1 288 304 336
  fastGenerator1_block_18
  (interval_append fastGenerator1 304 320 336
  fastGenerator1_block_19
  fastGenerator1_block_20))
  (interval_append fastGenerator1 336 352 376
  fastGenerator1_block_21
  (interval_append fastGenerator1 352 368 376
  fastGenerator1_block_22
  fastGenerator1_block_23)))))
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed029.Outside.Verified
