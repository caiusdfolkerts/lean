module
prelude
public meta import LowerSchemas.FinitePackedSevenMixed
public import PackedSevenMixed009Nodes
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed009
open Papers.RationalityTen Papers.RationalityTen.FiniteChecks
cert_maskTest_block 0 0 32 32
cert_maskTest_block 1 32 64 32
cert_maskTest_block 2 64 96 32
cert_maskTest_block 3 96 128 32
cert_maskTest_block 4 128 160 32
cert_maskTest_block 5 160 192 32
cert_maskTest_block 6 192 224 32
cert_maskTest_block 7 224 256 32
cert_maskTest_block 8 256 288 32
cert_maskTest_block 9 288 320 32
cert_maskTest_block 10 320 352 32
cert_maskTest_block 11 352 384 32
cert_maskTest_block 12 384 416 32
cert_maskTest_block 13 416 448 32
cert_maskTest_block 14 448 480 32
cert_maskTest_block 15 480 508 28
theorem maskTest_complete : Interval maskTest 0 508 :=
  (interval_append maskTest 0 256 508
  (interval_append maskTest 0 128 256
  (interval_append maskTest 0 64 128
  (interval_append maskTest 0 32 64
  maskTest_block_0
  maskTest_block_1)
  (interval_append maskTest 64 96 128
  maskTest_block_2
  maskTest_block_3))
  (interval_append maskTest 128 192 256
  (interval_append maskTest 128 160 192
  maskTest_block_4
  maskTest_block_5)
  (interval_append maskTest 192 224 256
  maskTest_block_6
  maskTest_block_7)))
  (interval_append maskTest 256 384 508
  (interval_append maskTest 256 320 384
  (interval_append maskTest 256 288 320
  maskTest_block_8
  maskTest_block_9)
  (interval_append maskTest 320 352 384
  maskTest_block_10
  maskTest_block_11))
  (interval_append maskTest 384 448 508
  (interval_append maskTest 384 416 448
  maskTest_block_12
  maskTest_block_13)
  (interval_append maskTest 448 480 508
  maskTest_block_14
  maskTest_block_15))))

cert_selectedMasks_exact 508
cert_fastTest_sound 910 1 508
end Papers.RationalityTen.PackedReplay.PackedSevenMixed009
