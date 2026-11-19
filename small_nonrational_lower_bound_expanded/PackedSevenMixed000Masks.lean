module
prelude
public meta import LowerSchemas.FinitePackedSevenMixed
public import PackedSevenMixed000Nodes
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed000
open Papers.RationalityTen Papers.RationalityTen.FiniteChecks
cert_maskTest_block 0 0 32 32
cert_maskTest_block 1 32 64 32
cert_maskTest_block 2 64 96 32
cert_maskTest_block 3 96 128 32
cert_maskTest_block 4 128 160 32
cert_maskTest_block 5 160 192 32
cert_maskTest_block 6 192 224 32
cert_maskTest_block 7 224 256 32
cert_maskTest_block 8 256 262 6
theorem maskTest_complete : Interval maskTest 0 262 :=
  (interval_append maskTest 0 128 262
  (interval_append maskTest 0 64 128
  (interval_append maskTest 0 32 64
  maskTest_block_0
  maskTest_block_1)
  (interval_append maskTest 64 96 128
  maskTest_block_2
  maskTest_block_3))
  (interval_append maskTest 128 192 262
  (interval_append maskTest 128 160 192
  maskTest_block_4
  maskTest_block_5)
  (interval_append maskTest 192 224 262
  maskTest_block_6
  (interval_append maskTest 224 256 262
  maskTest_block_7
  maskTest_block_8))))

cert_selectedMasks_exact 262
cert_fastTest_sound 646 1 262
end Papers.RationalityTen.PackedReplay.PackedSevenMixed000
