module
prelude
public meta import LowerSchemas.FinitePackedSevenMixed
public import PackedSevenMixed015Nodes
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed015
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
cert_maskTest_block 27 864 896 32
cert_maskTest_block 28 896 928 32
cert_maskTest_block 29 928 960 32
cert_maskTest_block 30 960 992 32
cert_maskTest_block 31 992 1024 32
cert_maskTest_block 32 1024 1056 32
cert_maskTest_block 33 1056 1088 32
cert_maskTest_block 34 1088 1120 32
cert_maskTest_block 35 1120 1152 32
cert_maskTest_block 36 1152 1184 32
cert_maskTest_block 37 1184 1216 32
cert_maskTest_block 38 1216 1248 32
cert_maskTest_block 39 1248 1280 32
cert_maskTest_block 40 1280 1312 32
cert_maskTest_block 41 1312 1344 32
cert_maskTest_block 42 1344 1376 32
cert_maskTest_block 43 1376 1408 32
cert_maskTest_block 44 1408 1440 32
cert_maskTest_block 45 1440 1472 32
cert_maskTest_block 46 1472 1504 32
cert_maskTest_block 47 1504 1536 32
cert_maskTest_block 48 1536 1568 32
cert_maskTest_block 49 1568 1575 7
theorem maskTest_complete : Interval maskTest 0 1575 :=
  (interval_append maskTest 0 800 1575
  (interval_append maskTest 0 384 800
  (interval_append maskTest 0 192 384
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
  (interval_append maskTest 192 288 384
  (interval_append maskTest 192 224 288
  maskTest_block_6
  (interval_append maskTest 224 256 288
  maskTest_block_7
  maskTest_block_8))
  (interval_append maskTest 288 320 384
  maskTest_block_9
  (interval_append maskTest 320 352 384
  maskTest_block_10
  maskTest_block_11))))
  (interval_append maskTest 384 576 800
  (interval_append maskTest 384 480 576
  (interval_append maskTest 384 416 480
  maskTest_block_12
  (interval_append maskTest 416 448 480
  maskTest_block_13
  maskTest_block_14))
  (interval_append maskTest 480 512 576
  maskTest_block_15
  (interval_append maskTest 512 544 576
  maskTest_block_16
  maskTest_block_17)))
  (interval_append maskTest 576 672 800
  (interval_append maskTest 576 608 672
  maskTest_block_18
  (interval_append maskTest 608 640 672
  maskTest_block_19
  maskTest_block_20))
  (interval_append maskTest 672 736 800
  (interval_append maskTest 672 704 736
  maskTest_block_21
  maskTest_block_22)
  (interval_append maskTest 736 768 800
  maskTest_block_23
  maskTest_block_24)))))
  (interval_append maskTest 800 1184 1575
  (interval_append maskTest 800 992 1184
  (interval_append maskTest 800 896 992
  (interval_append maskTest 800 832 896
  maskTest_block_25
  (interval_append maskTest 832 864 896
  maskTest_block_26
  maskTest_block_27))
  (interval_append maskTest 896 928 992
  maskTest_block_28
  (interval_append maskTest 928 960 992
  maskTest_block_29
  maskTest_block_30)))
  (interval_append maskTest 992 1088 1184
  (interval_append maskTest 992 1024 1088
  maskTest_block_31
  (interval_append maskTest 1024 1056 1088
  maskTest_block_32
  maskTest_block_33))
  (interval_append maskTest 1088 1120 1184
  maskTest_block_34
  (interval_append maskTest 1120 1152 1184
  maskTest_block_35
  maskTest_block_36))))
  (interval_append maskTest 1184 1376 1575
  (interval_append maskTest 1184 1280 1376
  (interval_append maskTest 1184 1216 1280
  maskTest_block_37
  (interval_append maskTest 1216 1248 1280
  maskTest_block_38
  maskTest_block_39))
  (interval_append maskTest 1280 1312 1376
  maskTest_block_40
  (interval_append maskTest 1312 1344 1376
  maskTest_block_41
  maskTest_block_42)))
  (interval_append maskTest 1376 1472 1575
  (interval_append maskTest 1376 1408 1472
  maskTest_block_43
  (interval_append maskTest 1408 1440 1472
  maskTest_block_44
  maskTest_block_45))
  (interval_append maskTest 1472 1536 1575
  (interval_append maskTest 1472 1504 1536
  maskTest_block_46
  maskTest_block_47)
  (interval_append maskTest 1536 1568 1575
  maskTest_block_48
  maskTest_block_49))))))

cert_selectedMasks_exact 1575
cert_fastTest_sound 521 18 1575
#print axioms fastTest_sound
end Papers.RationalityTen.PackedReplay.PackedSevenMixed015
