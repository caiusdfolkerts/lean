module
prelude
public meta import LowerSchemas.FinitePackedSevenMixed
public import PackedSevenMixed021Nodes
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed021
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
cert_maskTest_block 13 416 445 29
theorem maskTest_complete : Interval maskTest 0 445 :=
  (interval_append maskTest 0 224 445
  (interval_append maskTest 0 96 224
  (interval_append maskTest 0 32 96
  maskTest_block_0
  (interval_append maskTest 32 64 96
  maskTest_block_1
  maskTest_block_2))
  (interval_append maskTest 96 160 224
  (interval_append maskTest 96 128 160
  maskTest_block_3
  maskTest_block_4)
  (interval_append maskTest 160 192 224
  maskTest_block_5
  maskTest_block_6)))
  (interval_append maskTest 224 320 445
  (interval_append maskTest 224 256 320
  maskTest_block_7
  (interval_append maskTest 256 288 320
  maskTest_block_8
  maskTest_block_9))
  (interval_append maskTest 320 384 445
  (interval_append maskTest 320 352 384
  maskTest_block_10
  maskTest_block_11)
  (interval_append maskTest 384 416 445
  maskTest_block_12
  maskTest_block_13))))

cert_selectedMasks_exact 445
cert_fastTest_sound 556 1 445
end Papers.RationalityTen.PackedReplay.PackedSevenMixed021
