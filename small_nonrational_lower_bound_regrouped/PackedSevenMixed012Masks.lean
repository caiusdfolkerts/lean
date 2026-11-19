module
prelude
public meta import LowerSchemas.FinitePackedSevenMixed
public import PackedSevenMixed012Nodes
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed012
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
cert_maskTest_block 17 544 576 32
cert_maskTest_block 18 576 608 32
cert_maskTest_block 19 608 640 32
cert_maskTest_block 20 640 672 32
cert_maskTest_block 21 672 704 32
cert_maskTest_block 22 704 736 32
cert_maskTest_block 23 736 768 32
cert_maskTest_block 24 768 800 32
cert_maskTest_block 25 800 832 32
cert_maskTest_block 26 832 864 32
cert_maskTest_block 27 864 868 4
theorem maskTest_complete : Interval maskTest 0 868 :=
  (interval_append maskTest 0 448 868
  (interval_append maskTest 0 224 448
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
  (interval_append maskTest 224 320 448
  (interval_append maskTest 224 256 320
  maskTest_block_7
  (interval_append maskTest 256 288 320
  maskTest_block_8
  maskTest_block_9))
  (interval_append maskTest 320 384 448
  (interval_append maskTest 320 352 384
  maskTest_block_10
  maskTest_block_11)
  (interval_append maskTest 384 416 448
  maskTest_block_12
  maskTest_block_13))))
  (interval_append maskTest 448 672 868
  (interval_append maskTest 448 544 672
  (interval_append maskTest 448 480 544
  maskTest_block_14
  (interval_append maskTest 480 512 544
  maskTest_block_15
  maskTest_block_16))
  (interval_append maskTest 544 608 672
  (interval_append maskTest 544 576 608
  maskTest_block_17
  maskTest_block_18)
  (interval_append maskTest 608 640 672
  maskTest_block_19
  maskTest_block_20)))
  (interval_append maskTest 672 768 868
  (interval_append maskTest 672 704 768
  maskTest_block_21
  (interval_append maskTest 704 736 768
  maskTest_block_22
  maskTest_block_23))
  (interval_append maskTest 768 832 868
  (interval_append maskTest 768 800 832
  maskTest_block_24
  maskTest_block_25)
  (interval_append maskTest 832 864 868
  maskTest_block_26
  maskTest_block_27)))))

cert_selectedMasks_exact 868
cert_fastTest_sound 838 1 868
#print axioms fastTest_sound
end Papers.RationalityTen.PackedReplay.PackedSevenMixed012
