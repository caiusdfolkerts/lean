module
prelude
public meta import LowerSchemas.FinitePackedSevenMixed
public import PackedSevenMixed011Nodes
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed011
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
cert_maskTest_block 9 288 310 22
theorem maskTest_complete : Interval maskTest 0 310 :=
  (interval_append maskTest 0 160 310
  (interval_append maskTest 0 64 160
  (interval_append maskTest 0 32 64
  maskTest_block_0
  maskTest_block_1)
  (interval_append maskTest 64 96 160
  maskTest_block_2
  (interval_append maskTest 96 128 160
  maskTest_block_3
  maskTest_block_4)))
  (interval_append maskTest 160 224 310
  (interval_append maskTest 160 192 224
  maskTest_block_5
  maskTest_block_6)
  (interval_append maskTest 224 256 310
  maskTest_block_7
  (interval_append maskTest 256 288 310
  maskTest_block_8
  maskTest_block_9))))

cert_selectedMasks_exact 310
cert_fastTest_sound 658 1 310
#print axioms fastTest_sound
end Papers.RationalityTen.PackedReplay.PackedSevenMixed011
