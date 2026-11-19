module
prelude
public meta import LowerSchemas.FinitePackedSevenMixed
public import PackedSevenMixed008Nodes
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed008
open Papers.RationalityTen Papers.RationalityTen.FiniteChecks
cert_maskTest_block 0 0 32 32
cert_maskTest_block 1 32 64 32
cert_maskTest_block 2 64 96 32
cert_maskTest_block 3 96 128 32
cert_maskTest_block 4 128 160 32
cert_maskTest_block 5 160 192 32
cert_maskTest_block 6 192 196 4
theorem maskTest_complete : Interval maskTest 0 196 :=
  (interval_append maskTest 0 96 196
  (interval_append maskTest 0 32 96
  maskTest_block_0
  (interval_append maskTest 32 64 96
  maskTest_block_1
  maskTest_block_2))
  (interval_append maskTest 96 160 196
  (interval_append maskTest 96 128 160
  maskTest_block_3
  maskTest_block_4)
  (interval_append maskTest 160 192 196
  maskTest_block_5
  maskTest_block_6)))

cert_selectedMasks_exact 196
cert_fastTest_sound 694 1 196
#print axioms fastTest_sound
end Papers.RationalityTen.PackedReplay.PackedSevenMixed008
