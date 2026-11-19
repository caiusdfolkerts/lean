module
prelude
public meta import LowerSchemas.FinitePackedSevenMixed
public import PackedSevenMixed018Nodes
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed018
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
cert_maskTest_block 10 320 337 17
theorem maskTest_complete : Interval maskTest 0 337 :=
  (interval_append maskTest 0 160 337
  (interval_append maskTest 0 64 160
  (interval_append maskTest 0 32 64
  maskTest_block_0
  maskTest_block_1)
  (interval_append maskTest 64 96 160
  maskTest_block_2
  (interval_append maskTest 96 128 160
  maskTest_block_3
  maskTest_block_4)))
  (interval_append maskTest 160 256 337
  (interval_append maskTest 160 192 256
  maskTest_block_5
  (interval_append maskTest 192 224 256
  maskTest_block_6
  maskTest_block_7))
  (interval_append maskTest 256 288 337
  maskTest_block_8
  (interval_append maskTest 288 320 337
  maskTest_block_9
  maskTest_block_10))))

cert_selectedMasks_exact 337
cert_fastTest_sound 556 1 337
end Papers.RationalityTen.PackedReplay.PackedSevenMixed018
