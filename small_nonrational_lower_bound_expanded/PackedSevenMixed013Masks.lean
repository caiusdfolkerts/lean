module
prelude
public meta import LowerSchemas.FinitePackedSevenMixed
public import PackedSevenMixed013Nodes
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed013
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
cert_maskTest_block 12 384 394 10
theorem maskTest_complete : Interval maskTest 0 394 :=
  (interval_append maskTest 0 192 394
  (interval_append maskTest 0 96 192
  (interval_append maskTest 0 32 96
  maskTest_block_0
  (interval_append maskTest 32 64 96
  maskTest_block_1
  maskTest_block_2))
  (interval_append maskTest 96 128 192
  maskTest_block_3
  (interval_append maskTest 128 160 192
  maskTest_block_4
  maskTest_block_5)))
  (interval_append maskTest 192 288 394
  (interval_append maskTest 192 224 288
  maskTest_block_6
  (interval_append maskTest 224 256 288
  maskTest_block_7
  maskTest_block_8))
  (interval_append maskTest 288 352 394
  (interval_append maskTest 288 320 352
  maskTest_block_9
  maskTest_block_10)
  (interval_append maskTest 352 384 394
  maskTest_block_11
  maskTest_block_12))))

cert_selectedMasks_exact 394
cert_fastTest_sound 466 1 394
end Papers.RationalityTen.PackedReplay.PackedSevenMixed013
