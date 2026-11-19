module
prelude
public meta import LowerSchemas.FinitePackedSevenMixed
public import PackedSevenMixed019Nodes
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed019
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
cert_maskTest_block 15 480 512 32
cert_maskTest_block 16 512 544 32
cert_maskTest_block 17 544 553 9
theorem maskTest_complete : Interval maskTest 0 553 :=
  (interval_append maskTest 0 288 553
  (interval_append maskTest 0 128 288
  (interval_append maskTest 0 64 128
  (interval_append maskTest 0 32 64
  maskTest_block_0
  maskTest_block_1)
  (interval_append maskTest 64 96 128
  maskTest_block_2
  maskTest_block_3))
  (interval_append maskTest 128 192 288
  (interval_append maskTest 128 160 192
  maskTest_block_4
  maskTest_block_5)
  (interval_append maskTest 192 224 288
  maskTest_block_6
  (interval_append maskTest 224 256 288
  maskTest_block_7
  maskTest_block_8))))
  (interval_append maskTest 288 416 553
  (interval_append maskTest 288 352 416
  (interval_append maskTest 288 320 352
  maskTest_block_9
  maskTest_block_10)
  (interval_append maskTest 352 384 416
  maskTest_block_11
  maskTest_block_12))
  (interval_append maskTest 416 480 553
  (interval_append maskTest 416 448 480
  maskTest_block_13
  maskTest_block_14)
  (interval_append maskTest 480 512 553
  maskTest_block_15
  (interval_append maskTest 512 544 553
  maskTest_block_16
  maskTest_block_17)))))

cert_selectedMasks_exact 553
cert_fastTest_sound 556 1 553
end Papers.RationalityTen.PackedReplay.PackedSevenMixed019
