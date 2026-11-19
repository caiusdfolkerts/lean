module
prelude
public meta import LowerSchemas.FiniteRootedSevenPure
public import RootedSevenPure067OutsideVerifiedLookup

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSevenPure067.Outside.Verified
open Papers.RationalityTen.FiniteChecks
cert_fastGenerator_2 1
cert_fastGenerator_block_2 1 0 0 16 16
cert_fastGenerator_block_2 1 1 16 32 16
cert_fastGenerator_block_2 1 2 32 48 16
cert_fastGenerator_block_2 1 3 48 64 16
cert_fastGenerator_block_2 1 4 64 80 16
cert_fastGenerator_block_2 1 5 80 96 16
cert_fastGenerator_block_2 1 6 96 112 16
cert_fastGenerator_block_2 1 7 112 128 16
cert_fastGenerator_block_2 1 8 128 144 16
cert_fastGenerator_block_2 1 9 144 160 16
cert_fastGenerator_block_2 1 10 160 176 16
cert_fastGenerator_block_2 1 11 176 192 16
cert_fastGenerator_block_2 1 12 192 208 16
cert_fastGenerator_block_2 1 13 208 224 16
cert_fastGenerator_block_2 1 14 224 240 16
cert_fastGenerator_block_2 1 15 240 256 16
cert_fastGenerator_block_2 1 16 256 272 16
cert_fastGenerator_block_2 1 17 272 288 16
cert_fastGenerator_block_2 1 18 288 304 16
cert_fastGenerator_block_2 1 19 304 320 16
cert_fastGenerator_block_2 1 20 320 336 16
cert_fastGenerator_block_2 1 21 336 352 16
cert_fastGenerator_block_2 1 22 352 368 16
cert_fastGenerator_block_2 1 23 368 384 16
cert_fastGenerator_block_2 1 24 384 400 16
cert_fastGenerator_block_2 1 25 400 406 6
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
end Papers.RationalityTen.FacetUniverses.RootedSevenPure067.Outside.Verified
