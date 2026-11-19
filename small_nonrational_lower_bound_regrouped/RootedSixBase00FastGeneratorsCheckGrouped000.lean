module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase00FastGeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_7 0 128 128
cert_checked_7 128 256 128
cert_checked_7 256 384 128
cert_checked_7 384 512 128
cert_checked_7 512 640 128
cert_checked_7 640 768 128
cert_checked_7 768 896 128
cert_checked_7 896 1024 128
cert_checked_7 1024 1152 128
cert_checked_7 1152 1280 128
cert_checked_7 1280 1408 128
cert_checked_7 1408 1536 128
cert_checked_7 1536 1664 128
cert_checked_7 1664 1792 128
cert_checked_7 1792 1920 128
cert_checked_7 1920 2048 128
cert_checked_7 2048 2176 128
cert_checked_7 2176 2304 128
cert_checked_7 2304 2432 128
cert_checked_7 2432 2560 128
cert_checked_7 2560 2688 128
cert_checked_7 2688 2816 128
cert_checked_7 2816 2944 128
cert_checked_7 2944 3072 128
cert_checked_7 3072 3200 128
cert_checked_7 3200 3328 128
cert_checked_7 3328 3456 128
cert_checked_7 3456 3584 128
cert_checked_7 3584 3712 128
cert_checked_7 3712 3840 128
cert_checked_7 3840 3968 128
cert_checked_7 3968 4096 128
theorem interval_0 : FiniteChecks.Interval test 0 4096 :=
  (FiniteChecks.interval_append test 0 2048 4096
  (FiniteChecks.interval_append test 0 1024 2048
  (FiniteChecks.interval_append test 0 512 1024
  (FiniteChecks.interval_append test 0 256 512
  (FiniteChecks.interval_append test 0 128 256
  checked_0
  checked_128)
  (FiniteChecks.interval_append test 256 384 512
  checked_256
  checked_384))
  (FiniteChecks.interval_append test 512 768 1024
  (FiniteChecks.interval_append test 512 640 768
  checked_512
  checked_640)
  (FiniteChecks.interval_append test 768 896 1024
  checked_768
  checked_896)))
  (FiniteChecks.interval_append test 1024 1536 2048
  (FiniteChecks.interval_append test 1024 1280 1536
  (FiniteChecks.interval_append test 1024 1152 1280
  checked_1024
  checked_1152)
  (FiniteChecks.interval_append test 1280 1408 1536
  checked_1280
  checked_1408))
  (FiniteChecks.interval_append test 1536 1792 2048
  (FiniteChecks.interval_append test 1536 1664 1792
  checked_1536
  checked_1664)
  (FiniteChecks.interval_append test 1792 1920 2048
  checked_1792
  checked_1920))))
  (FiniteChecks.interval_append test 2048 3072 4096
  (FiniteChecks.interval_append test 2048 2560 3072
  (FiniteChecks.interval_append test 2048 2304 2560
  (FiniteChecks.interval_append test 2048 2176 2304
  checked_2048
  checked_2176)
  (FiniteChecks.interval_append test 2304 2432 2560
  checked_2304
  checked_2432))
  (FiniteChecks.interval_append test 2560 2816 3072
  (FiniteChecks.interval_append test 2560 2688 2816
  checked_2560
  checked_2688)
  (FiniteChecks.interval_append test 2816 2944 3072
  checked_2816
  checked_2944)))
  (FiniteChecks.interval_append test 3072 3584 4096
  (FiniteChecks.interval_append test 3072 3328 3584
  (FiniteChecks.interval_append test 3072 3200 3328
  checked_3072
  checked_3200)
  (FiniteChecks.interval_append test 3328 3456 3584
  checked_3328
  checked_3456))
  (FiniteChecks.interval_append test 3584 3840 4096
  (FiniteChecks.interval_append test 3584 3712 3840
  checked_3584
  checked_3712)
  (FiniteChecks.interval_append test 3840 3968 4096
  checked_3840
  checked_3968)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_7 4096 4224 128
cert_checked_7 4224 4352 128
cert_checked_7 4352 4480 128
cert_checked_7 4480 4608 128
cert_checked_7 4608 4736 128
cert_checked_7 4736 4864 128
cert_checked_7 4864 4992 128
cert_checked_7 4992 5120 128
cert_checked_7 5120 5248 128
cert_checked_7 5248 5376 128
cert_checked_7 5376 5504 128
cert_checked_7 5504 5632 128
cert_checked_7 5632 5760 128
cert_checked_7 5760 5888 128
cert_checked_7 5888 6016 128
cert_checked_7 6016 6144 128
cert_checked_7 6144 6272 128
cert_checked_7 6272 6400 128
cert_checked_7 6400 6528 128
cert_checked_7 6528 6656 128
cert_checked_7 6656 6784 128
cert_checked_7 6784 6912 128
cert_checked_7 6912 7040 128
cert_checked_7 7040 7168 128
cert_checked_7 7168 7296 128
cert_checked_7 7296 7424 128
cert_checked_7 7424 7552 128
cert_checked_7 7552 7680 128
cert_checked_7 7680 7808 128
cert_checked_7 7808 7936 128
cert_checked_7 7936 8064 128
cert_checked_7 8064 8192 128
theorem interval_4096 : FiniteChecks.Interval test 4096 8192 :=
  (FiniteChecks.interval_append test 4096 6144 8192
  (FiniteChecks.interval_append test 4096 5120 6144
  (FiniteChecks.interval_append test 4096 4608 5120
  (FiniteChecks.interval_append test 4096 4352 4608
  (FiniteChecks.interval_append test 4096 4224 4352
  checked_4096
  checked_4224)
  (FiniteChecks.interval_append test 4352 4480 4608
  checked_4352
  checked_4480))
  (FiniteChecks.interval_append test 4608 4864 5120
  (FiniteChecks.interval_append test 4608 4736 4864
  checked_4608
  checked_4736)
  (FiniteChecks.interval_append test 4864 4992 5120
  checked_4864
  checked_4992)))
  (FiniteChecks.interval_append test 5120 5632 6144
  (FiniteChecks.interval_append test 5120 5376 5632
  (FiniteChecks.interval_append test 5120 5248 5376
  checked_5120
  checked_5248)
  (FiniteChecks.interval_append test 5376 5504 5632
  checked_5376
  checked_5504))
  (FiniteChecks.interval_append test 5632 5888 6144
  (FiniteChecks.interval_append test 5632 5760 5888
  checked_5632
  checked_5760)
  (FiniteChecks.interval_append test 5888 6016 6144
  checked_5888
  checked_6016))))
  (FiniteChecks.interval_append test 6144 7168 8192
  (FiniteChecks.interval_append test 6144 6656 7168
  (FiniteChecks.interval_append test 6144 6400 6656
  (FiniteChecks.interval_append test 6144 6272 6400
  checked_6144
  checked_6272)
  (FiniteChecks.interval_append test 6400 6528 6656
  checked_6400
  checked_6528))
  (FiniteChecks.interval_append test 6656 6912 7168
  (FiniteChecks.interval_append test 6656 6784 6912
  checked_6656
  checked_6784)
  (FiniteChecks.interval_append test 6912 7040 7168
  checked_6912
  checked_7040)))
  (FiniteChecks.interval_append test 7168 7680 8192
  (FiniteChecks.interval_append test 7168 7424 7680
  (FiniteChecks.interval_append test 7168 7296 7424
  checked_7168
  checked_7296)
  (FiniteChecks.interval_append test 7424 7552 7680
  checked_7424
  checked_7552))
  (FiniteChecks.interval_append test 7680 7936 8192
  (FiniteChecks.interval_append test 7680 7808 7936
  checked_7680
  checked_7808)
  (FiniteChecks.interval_append test 7936 8064 8192
  checked_7936
  checked_8064)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_7 8192 8320 128
cert_checked_7 8320 8448 128
cert_checked_7 8448 8576 128
cert_checked_7 8576 8704 128
cert_checked_7 8704 8832 128
cert_checked_7 8832 8960 128
cert_checked_7 8960 9088 128
cert_checked_7 9088 9216 128
cert_checked_7 9216 9344 128
cert_checked_7 9344 9472 128
cert_checked_7 9472 9600 128
cert_checked_7 9600 9728 128
cert_checked_7 9728 9856 128
cert_checked_7 9856 9984 128
cert_checked_7 9984 10112 128
cert_checked_7 10112 10240 128
cert_checked_7 10240 10368 128
cert_checked_7 10368 10496 128
cert_checked_7 10496 10624 128
cert_checked_7 10624 10752 128
cert_checked_7 10752 10880 128
cert_checked_7 10880 11008 128
cert_checked_7 11008 11136 128
cert_checked_7 11136 11264 128
cert_checked_7 11264 11392 128
cert_checked_7 11392 11520 128
cert_checked_7 11520 11648 128
cert_checked_7 11648 11776 128
cert_checked_7 11776 11904 128
cert_checked_7 11904 12032 128
cert_checked_7 12032 12160 128
cert_checked_7 12160 12288 128
theorem interval_8192 : FiniteChecks.Interval test 8192 12288 :=
  (FiniteChecks.interval_append test 8192 10240 12288
  (FiniteChecks.interval_append test 8192 9216 10240
  (FiniteChecks.interval_append test 8192 8704 9216
  (FiniteChecks.interval_append test 8192 8448 8704
  (FiniteChecks.interval_append test 8192 8320 8448
  checked_8192
  checked_8320)
  (FiniteChecks.interval_append test 8448 8576 8704
  checked_8448
  checked_8576))
  (FiniteChecks.interval_append test 8704 8960 9216
  (FiniteChecks.interval_append test 8704 8832 8960
  checked_8704
  checked_8832)
  (FiniteChecks.interval_append test 8960 9088 9216
  checked_8960
  checked_9088)))
  (FiniteChecks.interval_append test 9216 9728 10240
  (FiniteChecks.interval_append test 9216 9472 9728
  (FiniteChecks.interval_append test 9216 9344 9472
  checked_9216
  checked_9344)
  (FiniteChecks.interval_append test 9472 9600 9728
  checked_9472
  checked_9600))
  (FiniteChecks.interval_append test 9728 9984 10240
  (FiniteChecks.interval_append test 9728 9856 9984
  checked_9728
  checked_9856)
  (FiniteChecks.interval_append test 9984 10112 10240
  checked_9984
  checked_10112))))
  (FiniteChecks.interval_append test 10240 11264 12288
  (FiniteChecks.interval_append test 10240 10752 11264
  (FiniteChecks.interval_append test 10240 10496 10752
  (FiniteChecks.interval_append test 10240 10368 10496
  checked_10240
  checked_10368)
  (FiniteChecks.interval_append test 10496 10624 10752
  checked_10496
  checked_10624))
  (FiniteChecks.interval_append test 10752 11008 11264
  (FiniteChecks.interval_append test 10752 10880 11008
  checked_10752
  checked_10880)
  (FiniteChecks.interval_append test 11008 11136 11264
  checked_11008
  checked_11136)))
  (FiniteChecks.interval_append test 11264 11776 12288
  (FiniteChecks.interval_append test 11264 11520 11776
  (FiniteChecks.interval_append test 11264 11392 11520
  checked_11264
  checked_11392)
  (FiniteChecks.interval_append test 11520 11648 11776
  checked_11520
  checked_11648))
  (FiniteChecks.interval_append test 11776 12032 12288
  (FiniteChecks.interval_append test 11776 11904 12032
  checked_11776
  checked_11904)
  (FiniteChecks.interval_append test 12032 12160 12288
  checked_12032
  checked_12160)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_7 12288 12416 128
cert_checked_7 12416 12544 128
cert_checked_7 12544 12672 128
cert_checked_7 12672 12800 128
cert_checked_7 12800 12928 128
cert_checked_7 12928 13056 128
cert_checked_7 13056 13184 128
cert_checked_7 13184 13312 128
cert_checked_7 13312 13440 128
cert_checked_7 13440 13568 128
cert_checked_7 13568 13696 128
cert_checked_7 13696 13824 128
cert_checked_7 13824 13952 128
cert_checked_7 13952 14080 128
cert_checked_7 14080 14208 128
cert_checked_7 14208 14336 128
cert_checked_7 14336 14464 128
cert_checked_7 14464 14592 128
cert_checked_7 14592 14720 128
cert_checked_7 14720 14848 128
cert_checked_7 14848 14976 128
cert_checked_7 14976 15104 128
cert_checked_7 15104 15232 128
cert_checked_7 15232 15360 128
cert_checked_7 15360 15488 128
cert_checked_7 15488 15616 128
cert_checked_7 15616 15744 128
cert_checked_7 15744 15872 128
cert_checked_7 15872 16000 128
cert_checked_7 16000 16128 128
cert_checked_7 16128 16256 128
cert_checked_7 16256 16384 128
theorem interval_12288 : FiniteChecks.Interval test 12288 16384 :=
  (FiniteChecks.interval_append test 12288 14336 16384
  (FiniteChecks.interval_append test 12288 13312 14336
  (FiniteChecks.interval_append test 12288 12800 13312
  (FiniteChecks.interval_append test 12288 12544 12800
  (FiniteChecks.interval_append test 12288 12416 12544
  checked_12288
  checked_12416)
  (FiniteChecks.interval_append test 12544 12672 12800
  checked_12544
  checked_12672))
  (FiniteChecks.interval_append test 12800 13056 13312
  (FiniteChecks.interval_append test 12800 12928 13056
  checked_12800
  checked_12928)
  (FiniteChecks.interval_append test 13056 13184 13312
  checked_13056
  checked_13184)))
  (FiniteChecks.interval_append test 13312 13824 14336
  (FiniteChecks.interval_append test 13312 13568 13824
  (FiniteChecks.interval_append test 13312 13440 13568
  checked_13312
  checked_13440)
  (FiniteChecks.interval_append test 13568 13696 13824
  checked_13568
  checked_13696))
  (FiniteChecks.interval_append test 13824 14080 14336
  (FiniteChecks.interval_append test 13824 13952 14080
  checked_13824
  checked_13952)
  (FiniteChecks.interval_append test 14080 14208 14336
  checked_14080
  checked_14208))))
  (FiniteChecks.interval_append test 14336 15360 16384
  (FiniteChecks.interval_append test 14336 14848 15360
  (FiniteChecks.interval_append test 14336 14592 14848
  (FiniteChecks.interval_append test 14336 14464 14592
  checked_14336
  checked_14464)
  (FiniteChecks.interval_append test 14592 14720 14848
  checked_14592
  checked_14720))
  (FiniteChecks.interval_append test 14848 15104 15360
  (FiniteChecks.interval_append test 14848 14976 15104
  checked_14848
  checked_14976)
  (FiniteChecks.interval_append test 15104 15232 15360
  checked_15104
  checked_15232)))
  (FiniteChecks.interval_append test 15360 15872 16384
  (FiniteChecks.interval_append test 15360 15616 15872
  (FiniteChecks.interval_append test 15360 15488 15616
  checked_15360
  checked_15488)
  (FiniteChecks.interval_append test 15616 15744 15872
  checked_15616
  checked_15744))
  (FiniteChecks.interval_append test 15872 16128 16384
  (FiniteChecks.interval_append test 15872 16000 16128
  checked_15872
  checked_16000)
  (FiniteChecks.interval_append test 16128 16256 16384
  checked_16128
  checked_16256)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_7 16384 16512 128
cert_checked_7 16512 16640 128
cert_checked_7 16640 16768 128
cert_checked_7 16768 16896 128
cert_checked_7 16896 17024 128
cert_checked_7 17024 17152 128
cert_checked_7 17152 17280 128
cert_checked_7 17280 17408 128
cert_checked_7 17408 17536 128
cert_checked_7 17536 17664 128
cert_checked_7 17664 17792 128
cert_checked_7 17792 17920 128
cert_checked_7 17920 18048 128
cert_checked_7 18048 18176 128
cert_checked_7 18176 18304 128
cert_checked_7 18304 18432 128
cert_checked_7 18432 18560 128
cert_checked_7 18560 18688 128
cert_checked_7 18688 18816 128
cert_checked_7 18816 18944 128
cert_checked_7 18944 19072 128
cert_checked_7 19072 19200 128
cert_checked_7 19200 19328 128
cert_checked_7 19328 19456 128
cert_checked_7 19456 19584 128
cert_checked_7 19584 19712 128
cert_checked_7 19712 19840 128
cert_checked_7 19840 19968 128
cert_checked_7 19968 20096 128
cert_checked_7 20096 20224 128
cert_checked_7 20224 20352 128
cert_checked_7 20352 20480 128
theorem interval_16384 : FiniteChecks.Interval test 16384 20480 :=
  (FiniteChecks.interval_append test 16384 18432 20480
  (FiniteChecks.interval_append test 16384 17408 18432
  (FiniteChecks.interval_append test 16384 16896 17408
  (FiniteChecks.interval_append test 16384 16640 16896
  (FiniteChecks.interval_append test 16384 16512 16640
  checked_16384
  checked_16512)
  (FiniteChecks.interval_append test 16640 16768 16896
  checked_16640
  checked_16768))
  (FiniteChecks.interval_append test 16896 17152 17408
  (FiniteChecks.interval_append test 16896 17024 17152
  checked_16896
  checked_17024)
  (FiniteChecks.interval_append test 17152 17280 17408
  checked_17152
  checked_17280)))
  (FiniteChecks.interval_append test 17408 17920 18432
  (FiniteChecks.interval_append test 17408 17664 17920
  (FiniteChecks.interval_append test 17408 17536 17664
  checked_17408
  checked_17536)
  (FiniteChecks.interval_append test 17664 17792 17920
  checked_17664
  checked_17792))
  (FiniteChecks.interval_append test 17920 18176 18432
  (FiniteChecks.interval_append test 17920 18048 18176
  checked_17920
  checked_18048)
  (FiniteChecks.interval_append test 18176 18304 18432
  checked_18176
  checked_18304))))
  (FiniteChecks.interval_append test 18432 19456 20480
  (FiniteChecks.interval_append test 18432 18944 19456
  (FiniteChecks.interval_append test 18432 18688 18944
  (FiniteChecks.interval_append test 18432 18560 18688
  checked_18432
  checked_18560)
  (FiniteChecks.interval_append test 18688 18816 18944
  checked_18688
  checked_18816))
  (FiniteChecks.interval_append test 18944 19200 19456
  (FiniteChecks.interval_append test 18944 19072 19200
  checked_18944
  checked_19072)
  (FiniteChecks.interval_append test 19200 19328 19456
  checked_19200
  checked_19328)))
  (FiniteChecks.interval_append test 19456 19968 20480
  (FiniteChecks.interval_append test 19456 19712 19968
  (FiniteChecks.interval_append test 19456 19584 19712
  checked_19456
  checked_19584)
  (FiniteChecks.interval_append test 19712 19840 19968
  checked_19712
  checked_19840))
  (FiniteChecks.interval_append test 19968 20224 20480
  (FiniteChecks.interval_append test 19968 20096 20224
  checked_19968
  checked_20096)
  (FiniteChecks.interval_append test 20224 20352 20480
  checked_20224
  checked_20352)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_7 20480 20608 128
cert_checked_7 20608 20736 128
cert_checked_7 20736 20864 128
cert_checked_7 20864 20992 128
cert_checked_7 20992 21120 128
cert_checked_7 21120 21248 128
cert_checked_7 21248 21376 128
cert_checked_7 21376 21504 128
cert_checked_7 21504 21632 128
cert_checked_7 21632 21760 128
cert_checked_7 21760 21888 128
cert_checked_7 21888 22016 128
cert_checked_7 22016 22144 128
cert_checked_7 22144 22272 128
cert_checked_7 22272 22400 128
cert_checked_7 22400 22528 128
cert_checked_7 22528 22656 128
cert_checked_7 22656 22784 128
cert_checked_7 22784 22912 128
cert_checked_7 22912 23040 128
cert_checked_7 23040 23168 128
cert_checked_7 23168 23296 128
cert_checked_7 23296 23424 128
cert_checked_7 23424 23552 128
cert_checked_7 23552 23680 128
cert_checked_7 23680 23808 128
cert_checked_7 23808 23936 128
cert_checked_7 23936 24064 128
cert_checked_7 24064 24192 128
cert_checked_7 24192 24320 128
cert_checked_7 24320 24448 128
cert_checked_7 24448 24576 128
theorem interval_20480 : FiniteChecks.Interval test 20480 24576 :=
  (FiniteChecks.interval_append test 20480 22528 24576
  (FiniteChecks.interval_append test 20480 21504 22528
  (FiniteChecks.interval_append test 20480 20992 21504
  (FiniteChecks.interval_append test 20480 20736 20992
  (FiniteChecks.interval_append test 20480 20608 20736
  checked_20480
  checked_20608)
  (FiniteChecks.interval_append test 20736 20864 20992
  checked_20736
  checked_20864))
  (FiniteChecks.interval_append test 20992 21248 21504
  (FiniteChecks.interval_append test 20992 21120 21248
  checked_20992
  checked_21120)
  (FiniteChecks.interval_append test 21248 21376 21504
  checked_21248
  checked_21376)))
  (FiniteChecks.interval_append test 21504 22016 22528
  (FiniteChecks.interval_append test 21504 21760 22016
  (FiniteChecks.interval_append test 21504 21632 21760
  checked_21504
  checked_21632)
  (FiniteChecks.interval_append test 21760 21888 22016
  checked_21760
  checked_21888))
  (FiniteChecks.interval_append test 22016 22272 22528
  (FiniteChecks.interval_append test 22016 22144 22272
  checked_22016
  checked_22144)
  (FiniteChecks.interval_append test 22272 22400 22528
  checked_22272
  checked_22400))))
  (FiniteChecks.interval_append test 22528 23552 24576
  (FiniteChecks.interval_append test 22528 23040 23552
  (FiniteChecks.interval_append test 22528 22784 23040
  (FiniteChecks.interval_append test 22528 22656 22784
  checked_22528
  checked_22656)
  (FiniteChecks.interval_append test 22784 22912 23040
  checked_22784
  checked_22912))
  (FiniteChecks.interval_append test 23040 23296 23552
  (FiniteChecks.interval_append test 23040 23168 23296
  checked_23040
  checked_23168)
  (FiniteChecks.interval_append test 23296 23424 23552
  checked_23296
  checked_23424)))
  (FiniteChecks.interval_append test 23552 24064 24576
  (FiniteChecks.interval_append test 23552 23808 24064
  (FiniteChecks.interval_append test 23552 23680 23808
  checked_23552
  checked_23680)
  (FiniteChecks.interval_append test 23808 23936 24064
  checked_23808
  checked_23936))
  (FiniteChecks.interval_append test 24064 24320 24576
  (FiniteChecks.interval_append test 24064 24192 24320
  checked_24064
  checked_24192)
  (FiniteChecks.interval_append test 24320 24448 24576
  checked_24320
  checked_24448)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_7 24576 24704 128
cert_checked_7 24704 24832 128
cert_checked_7 24832 24960 128
cert_checked_7 24960 25088 128
cert_checked_7 25088 25216 128
cert_checked_7 25216 25344 128
cert_checked_7 25344 25472 128
cert_checked_7 25472 25600 128
cert_checked_7 25600 25728 128
cert_checked_7 25728 25856 128
cert_checked_7 25856 25984 128
cert_checked_7 25984 26112 128
cert_checked_7 26112 26240 128
cert_checked_7 26240 26368 128
cert_checked_7 26368 26496 128
cert_checked_7 26496 26624 128
cert_checked_7 26624 26752 128
cert_checked_7 26752 26880 128
cert_checked_7 26880 27008 128
cert_checked_7 27008 27136 128
cert_checked_7 27136 27264 128
cert_checked_7 27264 27392 128
cert_checked_7 27392 27520 128
cert_checked_7 27520 27648 128
cert_checked_7 27648 27776 128
cert_checked_7 27776 27904 128
cert_checked_7 27904 28032 128
cert_checked_7 28032 28160 128
cert_checked_7 28160 28288 128
cert_checked_7 28288 28416 128
cert_checked_7 28416 28544 128
cert_checked_7 28544 28672 128
theorem interval_24576 : FiniteChecks.Interval test 24576 28672 :=
  (FiniteChecks.interval_append test 24576 26624 28672
  (FiniteChecks.interval_append test 24576 25600 26624
  (FiniteChecks.interval_append test 24576 25088 25600
  (FiniteChecks.interval_append test 24576 24832 25088
  (FiniteChecks.interval_append test 24576 24704 24832
  checked_24576
  checked_24704)
  (FiniteChecks.interval_append test 24832 24960 25088
  checked_24832
  checked_24960))
  (FiniteChecks.interval_append test 25088 25344 25600
  (FiniteChecks.interval_append test 25088 25216 25344
  checked_25088
  checked_25216)
  (FiniteChecks.interval_append test 25344 25472 25600
  checked_25344
  checked_25472)))
  (FiniteChecks.interval_append test 25600 26112 26624
  (FiniteChecks.interval_append test 25600 25856 26112
  (FiniteChecks.interval_append test 25600 25728 25856
  checked_25600
  checked_25728)
  (FiniteChecks.interval_append test 25856 25984 26112
  checked_25856
  checked_25984))
  (FiniteChecks.interval_append test 26112 26368 26624
  (FiniteChecks.interval_append test 26112 26240 26368
  checked_26112
  checked_26240)
  (FiniteChecks.interval_append test 26368 26496 26624
  checked_26368
  checked_26496))))
  (FiniteChecks.interval_append test 26624 27648 28672
  (FiniteChecks.interval_append test 26624 27136 27648
  (FiniteChecks.interval_append test 26624 26880 27136
  (FiniteChecks.interval_append test 26624 26752 26880
  checked_26624
  checked_26752)
  (FiniteChecks.interval_append test 26880 27008 27136
  checked_26880
  checked_27008))
  (FiniteChecks.interval_append test 27136 27392 27648
  (FiniteChecks.interval_append test 27136 27264 27392
  checked_27136
  checked_27264)
  (FiniteChecks.interval_append test 27392 27520 27648
  checked_27392
  checked_27520)))
  (FiniteChecks.interval_append test 27648 28160 28672
  (FiniteChecks.interval_append test 27648 27904 28160
  (FiniteChecks.interval_append test 27648 27776 27904
  checked_27648
  checked_27776)
  (FiniteChecks.interval_append test 27904 28032 28160
  checked_27904
  checked_28032))
  (FiniteChecks.interval_append test 28160 28416 28672
  (FiniteChecks.interval_append test 28160 28288 28416
  checked_28160
  checked_28288)
  (FiniteChecks.interval_append test 28416 28544 28672
  checked_28416
  checked_28544)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_7 28672 28800 128
cert_checked_7 28800 28928 128
cert_checked_7 28928 29056 128
cert_checked_7 29056 29184 128
cert_checked_7 29184 29312 128
cert_checked_7 29312 29440 128
cert_checked_7 29440 29568 128
cert_checked_7 29568 29696 128
cert_checked_7 29696 29824 128
cert_checked_7 29824 29952 128
cert_checked_7 29952 30080 128
cert_checked_7 30080 30208 128
cert_checked_7 30208 30336 128
cert_checked_7 30336 30464 128
cert_checked_7 30464 30592 128
cert_checked_7 30592 30720 128
cert_checked_7 30720 30848 128
cert_checked_7 30848 30976 128
cert_checked_7 30976 31104 128
cert_checked_7 31104 31232 128
cert_checked_7 31232 31360 128
cert_checked_7 31360 31488 128
cert_checked_7 31488 31616 128
cert_checked_7 31616 31744 128
cert_checked_7 31744 31872 128
cert_checked_7 31872 32000 128
cert_checked_7 32000 32128 128
cert_checked_7 32128 32256 128
cert_checked_7 32256 32384 128
cert_checked_7 32384 32512 128
cert_checked_7 32512 32640 128
cert_checked_7 32640 32768 128
theorem interval_28672 : FiniteChecks.Interval test 28672 32768 :=
  (FiniteChecks.interval_append test 28672 30720 32768
  (FiniteChecks.interval_append test 28672 29696 30720
  (FiniteChecks.interval_append test 28672 29184 29696
  (FiniteChecks.interval_append test 28672 28928 29184
  (FiniteChecks.interval_append test 28672 28800 28928
  checked_28672
  checked_28800)
  (FiniteChecks.interval_append test 28928 29056 29184
  checked_28928
  checked_29056))
  (FiniteChecks.interval_append test 29184 29440 29696
  (FiniteChecks.interval_append test 29184 29312 29440
  checked_29184
  checked_29312)
  (FiniteChecks.interval_append test 29440 29568 29696
  checked_29440
  checked_29568)))
  (FiniteChecks.interval_append test 29696 30208 30720
  (FiniteChecks.interval_append test 29696 29952 30208
  (FiniteChecks.interval_append test 29696 29824 29952
  checked_29696
  checked_29824)
  (FiniteChecks.interval_append test 29952 30080 30208
  checked_29952
  checked_30080))
  (FiniteChecks.interval_append test 30208 30464 30720
  (FiniteChecks.interval_append test 30208 30336 30464
  checked_30208
  checked_30336)
  (FiniteChecks.interval_append test 30464 30592 30720
  checked_30464
  checked_30592))))
  (FiniteChecks.interval_append test 30720 31744 32768
  (FiniteChecks.interval_append test 30720 31232 31744
  (FiniteChecks.interval_append test 30720 30976 31232
  (FiniteChecks.interval_append test 30720 30848 30976
  checked_30720
  checked_30848)
  (FiniteChecks.interval_append test 30976 31104 31232
  checked_30976
  checked_31104))
  (FiniteChecks.interval_append test 31232 31488 31744
  (FiniteChecks.interval_append test 31232 31360 31488
  checked_31232
  checked_31360)
  (FiniteChecks.interval_append test 31488 31616 31744
  checked_31488
  checked_31616)))
  (FiniteChecks.interval_append test 31744 32256 32768
  (FiniteChecks.interval_append test 31744 32000 32256
  (FiniteChecks.interval_append test 31744 31872 32000
  checked_31744
  checked_31872)
  (FiniteChecks.interval_append test 32000 32128 32256
  checked_32000
  checked_32128))
  (FiniteChecks.interval_append test 32256 32512 32768
  (FiniteChecks.interval_append test 32256 32384 32512
  checked_32256
  checked_32384)
  (FiniteChecks.interval_append test 32512 32640 32768
  checked_32512
  checked_32640)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_7 32768 32896 128
cert_checked_7 32896 33024 128
cert_checked_7 33024 33152 128
cert_checked_7 33152 33280 128
cert_checked_7 33280 33408 128
cert_checked_7 33408 33536 128
cert_checked_7 33536 33664 128
cert_checked_7 33664 33792 128
cert_checked_7 33792 33920 128
cert_checked_7 33920 34048 128
cert_checked_7 34048 34176 128
cert_checked_7 34176 34304 128
cert_checked_7 34304 34432 128
cert_checked_7 34432 34560 128
cert_checked_7 34560 34688 128
cert_checked_7 34688 34816 128
cert_checked_7 34816 34944 128
cert_checked_7 34944 35072 128
cert_checked_7 35072 35200 128
cert_checked_7 35200 35328 128
cert_checked_7 35328 35456 128
cert_checked_7 35456 35584 128
cert_checked_7 35584 35712 128
cert_checked_7 35712 35840 128
cert_checked_7 35840 35968 128
cert_checked_7 35968 36096 128
cert_checked_7 36096 36224 128
cert_checked_7 36224 36352 128
cert_checked_7 36352 36480 128
cert_checked_7 36480 36608 128
cert_checked_7 36608 36736 128
cert_checked_7 36736 36864 128
theorem interval_32768 : FiniteChecks.Interval test 32768 36864 :=
  (FiniteChecks.interval_append test 32768 34816 36864
  (FiniteChecks.interval_append test 32768 33792 34816
  (FiniteChecks.interval_append test 32768 33280 33792
  (FiniteChecks.interval_append test 32768 33024 33280
  (FiniteChecks.interval_append test 32768 32896 33024
  checked_32768
  checked_32896)
  (FiniteChecks.interval_append test 33024 33152 33280
  checked_33024
  checked_33152))
  (FiniteChecks.interval_append test 33280 33536 33792
  (FiniteChecks.interval_append test 33280 33408 33536
  checked_33280
  checked_33408)
  (FiniteChecks.interval_append test 33536 33664 33792
  checked_33536
  checked_33664)))
  (FiniteChecks.interval_append test 33792 34304 34816
  (FiniteChecks.interval_append test 33792 34048 34304
  (FiniteChecks.interval_append test 33792 33920 34048
  checked_33792
  checked_33920)
  (FiniteChecks.interval_append test 34048 34176 34304
  checked_34048
  checked_34176))
  (FiniteChecks.interval_append test 34304 34560 34816
  (FiniteChecks.interval_append test 34304 34432 34560
  checked_34304
  checked_34432)
  (FiniteChecks.interval_append test 34560 34688 34816
  checked_34560
  checked_34688))))
  (FiniteChecks.interval_append test 34816 35840 36864
  (FiniteChecks.interval_append test 34816 35328 35840
  (FiniteChecks.interval_append test 34816 35072 35328
  (FiniteChecks.interval_append test 34816 34944 35072
  checked_34816
  checked_34944)
  (FiniteChecks.interval_append test 35072 35200 35328
  checked_35072
  checked_35200))
  (FiniteChecks.interval_append test 35328 35584 35840
  (FiniteChecks.interval_append test 35328 35456 35584
  checked_35328
  checked_35456)
  (FiniteChecks.interval_append test 35584 35712 35840
  checked_35584
  checked_35712)))
  (FiniteChecks.interval_append test 35840 36352 36864
  (FiniteChecks.interval_append test 35840 36096 36352
  (FiniteChecks.interval_append test 35840 35968 36096
  checked_35840
  checked_35968)
  (FiniteChecks.interval_append test 36096 36224 36352
  checked_36096
  checked_36224))
  (FiniteChecks.interval_append test 36352 36608 36864
  (FiniteChecks.interval_append test 36352 36480 36608
  checked_36352
  checked_36480)
  (FiniteChecks.interval_append test 36608 36736 36864
  checked_36608
  checked_36736)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_7 36864 36992 128
cert_checked_7 36992 37120 128
cert_checked_7 37120 37248 128
cert_checked_7 37248 37376 128
cert_checked_7 37376 37504 128
cert_checked_7 37504 37632 128
cert_checked_7 37632 37760 128
cert_checked_7 37760 37888 128
cert_checked_7 37888 38016 128
cert_checked_7 38016 38144 128
cert_checked_7 38144 38272 128
cert_checked_7 38272 38400 128
cert_checked_7 38400 38528 128
cert_checked_7 38528 38656 128
cert_checked_7 38656 38784 128
cert_checked_7 38784 38912 128
cert_checked_7 38912 39040 128
cert_checked_7 39040 39168 128
cert_checked_7 39168 39296 128
cert_checked_7 39296 39424 128
cert_checked_7 39424 39552 128
cert_checked_7 39552 39680 128
cert_checked_7 39680 39808 128
cert_checked_7 39808 39936 128
cert_checked_7 39936 40064 128
cert_checked_7 40064 40192 128
cert_checked_7 40192 40320 128
cert_checked_7 40320 40448 128
cert_checked_7 40448 40576 128
cert_checked_7 40576 40704 128
cert_checked_7 40704 40832 128
cert_checked_7 40832 40960 128
theorem interval_36864 : FiniteChecks.Interval test 36864 40960 :=
  (FiniteChecks.interval_append test 36864 38912 40960
  (FiniteChecks.interval_append test 36864 37888 38912
  (FiniteChecks.interval_append test 36864 37376 37888
  (FiniteChecks.interval_append test 36864 37120 37376
  (FiniteChecks.interval_append test 36864 36992 37120
  checked_36864
  checked_36992)
  (FiniteChecks.interval_append test 37120 37248 37376
  checked_37120
  checked_37248))
  (FiniteChecks.interval_append test 37376 37632 37888
  (FiniteChecks.interval_append test 37376 37504 37632
  checked_37376
  checked_37504)
  (FiniteChecks.interval_append test 37632 37760 37888
  checked_37632
  checked_37760)))
  (FiniteChecks.interval_append test 37888 38400 38912
  (FiniteChecks.interval_append test 37888 38144 38400
  (FiniteChecks.interval_append test 37888 38016 38144
  checked_37888
  checked_38016)
  (FiniteChecks.interval_append test 38144 38272 38400
  checked_38144
  checked_38272))
  (FiniteChecks.interval_append test 38400 38656 38912
  (FiniteChecks.interval_append test 38400 38528 38656
  checked_38400
  checked_38528)
  (FiniteChecks.interval_append test 38656 38784 38912
  checked_38656
  checked_38784))))
  (FiniteChecks.interval_append test 38912 39936 40960
  (FiniteChecks.interval_append test 38912 39424 39936
  (FiniteChecks.interval_append test 38912 39168 39424
  (FiniteChecks.interval_append test 38912 39040 39168
  checked_38912
  checked_39040)
  (FiniteChecks.interval_append test 39168 39296 39424
  checked_39168
  checked_39296))
  (FiniteChecks.interval_append test 39424 39680 39936
  (FiniteChecks.interval_append test 39424 39552 39680
  checked_39424
  checked_39552)
  (FiniteChecks.interval_append test 39680 39808 39936
  checked_39680
  checked_39808)))
  (FiniteChecks.interval_append test 39936 40448 40960
  (FiniteChecks.interval_append test 39936 40192 40448
  (FiniteChecks.interval_append test 39936 40064 40192
  checked_39936
  checked_40064)
  (FiniteChecks.interval_append test 40192 40320 40448
  checked_40192
  checked_40320))
  (FiniteChecks.interval_append test 40448 40704 40960
  (FiniteChecks.interval_append test 40448 40576 40704
  checked_40448
  checked_40576)
  (FiniteChecks.interval_append test 40704 40832 40960
  checked_40704
  checked_40832)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_7 40960 41088 128
cert_checked_7 41088 41216 128
cert_checked_7 41216 41344 128
cert_checked_7 41344 41472 128
cert_checked_7 41472 41600 128
cert_checked_7 41600 41728 128
cert_checked_7 41728 41856 128
cert_checked_7 41856 41984 128
cert_checked_7 41984 42112 128
cert_checked_7 42112 42240 128
cert_checked_7 42240 42368 128
cert_checked_7 42368 42496 128
cert_checked_7 42496 42624 128
cert_checked_7 42624 42752 128
cert_checked_7 42752 42880 128
cert_checked_7 42880 43008 128
cert_checked_7 43008 43136 128
cert_checked_7 43136 43264 128
cert_checked_7 43264 43392 128
cert_checked_7 43392 43520 128
cert_checked_7 43520 43648 128
cert_checked_7 43648 43776 128
cert_checked_7 43776 43904 128
cert_checked_7 43904 44032 128
cert_checked_7 44032 44160 128
cert_checked_7 44160 44288 128
cert_checked_7 44288 44416 128
cert_checked_7 44416 44544 128
cert_checked_7 44544 44672 128
cert_checked_7 44672 44800 128
cert_checked_7 44800 44928 128
cert_checked_7 44928 45056 128
theorem interval_40960 : FiniteChecks.Interval test 40960 45056 :=
  (FiniteChecks.interval_append test 40960 43008 45056
  (FiniteChecks.interval_append test 40960 41984 43008
  (FiniteChecks.interval_append test 40960 41472 41984
  (FiniteChecks.interval_append test 40960 41216 41472
  (FiniteChecks.interval_append test 40960 41088 41216
  checked_40960
  checked_41088)
  (FiniteChecks.interval_append test 41216 41344 41472
  checked_41216
  checked_41344))
  (FiniteChecks.interval_append test 41472 41728 41984
  (FiniteChecks.interval_append test 41472 41600 41728
  checked_41472
  checked_41600)
  (FiniteChecks.interval_append test 41728 41856 41984
  checked_41728
  checked_41856)))
  (FiniteChecks.interval_append test 41984 42496 43008
  (FiniteChecks.interval_append test 41984 42240 42496
  (FiniteChecks.interval_append test 41984 42112 42240
  checked_41984
  checked_42112)
  (FiniteChecks.interval_append test 42240 42368 42496
  checked_42240
  checked_42368))
  (FiniteChecks.interval_append test 42496 42752 43008
  (FiniteChecks.interval_append test 42496 42624 42752
  checked_42496
  checked_42624)
  (FiniteChecks.interval_append test 42752 42880 43008
  checked_42752
  checked_42880))))
  (FiniteChecks.interval_append test 43008 44032 45056
  (FiniteChecks.interval_append test 43008 43520 44032
  (FiniteChecks.interval_append test 43008 43264 43520
  (FiniteChecks.interval_append test 43008 43136 43264
  checked_43008
  checked_43136)
  (FiniteChecks.interval_append test 43264 43392 43520
  checked_43264
  checked_43392))
  (FiniteChecks.interval_append test 43520 43776 44032
  (FiniteChecks.interval_append test 43520 43648 43776
  checked_43520
  checked_43648)
  (FiniteChecks.interval_append test 43776 43904 44032
  checked_43776
  checked_43904)))
  (FiniteChecks.interval_append test 44032 44544 45056
  (FiniteChecks.interval_append test 44032 44288 44544
  (FiniteChecks.interval_append test 44032 44160 44288
  checked_44032
  checked_44160)
  (FiniteChecks.interval_append test 44288 44416 44544
  checked_44288
  checked_44416))
  (FiniteChecks.interval_append test 44544 44800 45056
  (FiniteChecks.interval_append test 44544 44672 44800
  checked_44544
  checked_44672)
  (FiniteChecks.interval_append test 44800 44928 45056
  checked_44800
  checked_44928)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_7 45056 45184 128
cert_checked_7 45184 45312 128
cert_checked_7 45312 45440 128
cert_checked_7 45440 45568 128
cert_checked_7 45568 45696 128
cert_checked_7 45696 45824 128
cert_checked_7 45824 45952 128
cert_checked_7 45952 46080 128
cert_checked_7 46080 46208 128
cert_checked_7 46208 46336 128
cert_checked_7 46336 46464 128
cert_checked_7 46464 46592 128
cert_checked_7 46592 46720 128
cert_checked_7 46720 46848 128
cert_checked_7 46848 46976 128
cert_checked_7 46976 47104 128
cert_checked_7 47104 47232 128
cert_checked_7 47232 47360 128
cert_checked_7 47360 47488 128
cert_checked_7 47488 47616 128
cert_checked_7 47616 47744 128
cert_checked_7 47744 47872 128
cert_checked_7 47872 48000 128
cert_checked_7 48000 48128 128
cert_checked_7 48128 48256 128
cert_checked_7 48256 48384 128
cert_checked_7 48384 48512 128
cert_checked_7 48512 48640 128
cert_checked_7 48640 48768 128
cert_checked_7 48768 48896 128
cert_checked_7 48896 49024 128
cert_checked_7 49024 49152 128
theorem interval_45056 : FiniteChecks.Interval test 45056 49152 :=
  (FiniteChecks.interval_append test 45056 47104 49152
  (FiniteChecks.interval_append test 45056 46080 47104
  (FiniteChecks.interval_append test 45056 45568 46080
  (FiniteChecks.interval_append test 45056 45312 45568
  (FiniteChecks.interval_append test 45056 45184 45312
  checked_45056
  checked_45184)
  (FiniteChecks.interval_append test 45312 45440 45568
  checked_45312
  checked_45440))
  (FiniteChecks.interval_append test 45568 45824 46080
  (FiniteChecks.interval_append test 45568 45696 45824
  checked_45568
  checked_45696)
  (FiniteChecks.interval_append test 45824 45952 46080
  checked_45824
  checked_45952)))
  (FiniteChecks.interval_append test 46080 46592 47104
  (FiniteChecks.interval_append test 46080 46336 46592
  (FiniteChecks.interval_append test 46080 46208 46336
  checked_46080
  checked_46208)
  (FiniteChecks.interval_append test 46336 46464 46592
  checked_46336
  checked_46464))
  (FiniteChecks.interval_append test 46592 46848 47104
  (FiniteChecks.interval_append test 46592 46720 46848
  checked_46592
  checked_46720)
  (FiniteChecks.interval_append test 46848 46976 47104
  checked_46848
  checked_46976))))
  (FiniteChecks.interval_append test 47104 48128 49152
  (FiniteChecks.interval_append test 47104 47616 48128
  (FiniteChecks.interval_append test 47104 47360 47616
  (FiniteChecks.interval_append test 47104 47232 47360
  checked_47104
  checked_47232)
  (FiniteChecks.interval_append test 47360 47488 47616
  checked_47360
  checked_47488))
  (FiniteChecks.interval_append test 47616 47872 48128
  (FiniteChecks.interval_append test 47616 47744 47872
  checked_47616
  checked_47744)
  (FiniteChecks.interval_append test 47872 48000 48128
  checked_47872
  checked_48000)))
  (FiniteChecks.interval_append test 48128 48640 49152
  (FiniteChecks.interval_append test 48128 48384 48640
  (FiniteChecks.interval_append test 48128 48256 48384
  checked_48128
  checked_48256)
  (FiniteChecks.interval_append test 48384 48512 48640
  checked_48384
  checked_48512))
  (FiniteChecks.interval_append test 48640 48896 49152
  (FiniteChecks.interval_append test 48640 48768 48896
  checked_48640
  checked_48768)
  (FiniteChecks.interval_append test 48896 49024 49152
  checked_48896
  checked_49024)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_7 49152 49280 128
cert_checked_7 49280 49408 128
cert_checked_7 49408 49536 128
cert_checked_7 49536 49664 128
cert_checked_7 49664 49792 128
cert_checked_7 49792 49920 128
cert_checked_7 49920 50048 128
cert_checked_7 50048 50176 128
cert_checked_7 50176 50304 128
cert_checked_7 50304 50432 128
cert_checked_7 50432 50560 128
cert_checked_7 50560 50688 128
cert_checked_7 50688 50816 128
cert_checked_7 50816 50944 128
cert_checked_7 50944 51072 128
cert_checked_7 51072 51200 128
cert_checked_7 51200 51328 128
cert_checked_7 51328 51456 128
cert_checked_7 51456 51584 128
cert_checked_7 51584 51712 128
cert_checked_7 51712 51840 128
cert_checked_7 51840 51968 128
cert_checked_7 51968 52096 128
cert_checked_7 52096 52224 128
cert_checked_7 52224 52352 128
cert_checked_7 52352 52480 128
cert_checked_7 52480 52608 128
cert_checked_7 52608 52736 128
cert_checked_7 52736 52864 128
cert_checked_7 52864 52992 128
cert_checked_7 52992 53120 128
cert_checked_7 53120 53248 128
theorem interval_49152 : FiniteChecks.Interval test 49152 53248 :=
  (FiniteChecks.interval_append test 49152 51200 53248
  (FiniteChecks.interval_append test 49152 50176 51200
  (FiniteChecks.interval_append test 49152 49664 50176
  (FiniteChecks.interval_append test 49152 49408 49664
  (FiniteChecks.interval_append test 49152 49280 49408
  checked_49152
  checked_49280)
  (FiniteChecks.interval_append test 49408 49536 49664
  checked_49408
  checked_49536))
  (FiniteChecks.interval_append test 49664 49920 50176
  (FiniteChecks.interval_append test 49664 49792 49920
  checked_49664
  checked_49792)
  (FiniteChecks.interval_append test 49920 50048 50176
  checked_49920
  checked_50048)))
  (FiniteChecks.interval_append test 50176 50688 51200
  (FiniteChecks.interval_append test 50176 50432 50688
  (FiniteChecks.interval_append test 50176 50304 50432
  checked_50176
  checked_50304)
  (FiniteChecks.interval_append test 50432 50560 50688
  checked_50432
  checked_50560))
  (FiniteChecks.interval_append test 50688 50944 51200
  (FiniteChecks.interval_append test 50688 50816 50944
  checked_50688
  checked_50816)
  (FiniteChecks.interval_append test 50944 51072 51200
  checked_50944
  checked_51072))))
  (FiniteChecks.interval_append test 51200 52224 53248
  (FiniteChecks.interval_append test 51200 51712 52224
  (FiniteChecks.interval_append test 51200 51456 51712
  (FiniteChecks.interval_append test 51200 51328 51456
  checked_51200
  checked_51328)
  (FiniteChecks.interval_append test 51456 51584 51712
  checked_51456
  checked_51584))
  (FiniteChecks.interval_append test 51712 51968 52224
  (FiniteChecks.interval_append test 51712 51840 51968
  checked_51712
  checked_51840)
  (FiniteChecks.interval_append test 51968 52096 52224
  checked_51968
  checked_52096)))
  (FiniteChecks.interval_append test 52224 52736 53248
  (FiniteChecks.interval_append test 52224 52480 52736
  (FiniteChecks.interval_append test 52224 52352 52480
  checked_52224
  checked_52352)
  (FiniteChecks.interval_append test 52480 52608 52736
  checked_52480
  checked_52608))
  (FiniteChecks.interval_append test 52736 52992 53248
  (FiniteChecks.interval_append test 52736 52864 52992
  checked_52736
  checked_52864)
  (FiniteChecks.interval_append test 52992 53120 53248
  checked_52992
  checked_53120)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_7 53248 53376 128
cert_checked_7 53376 53504 128
cert_checked_7 53504 53632 128
cert_checked_7 53632 53760 128
cert_checked_7 53760 53888 128
cert_checked_7 53888 54016 128
cert_checked_7 54016 54144 128
cert_checked_7 54144 54272 128
cert_checked_7 54272 54400 128
cert_checked_7 54400 54528 128
cert_checked_7 54528 54656 128
cert_checked_7 54656 54784 128
cert_checked_7 54784 54912 128
cert_checked_7 54912 55040 128
cert_checked_7 55040 55168 128
cert_checked_7 55168 55296 128
cert_checked_7 55296 55424 128
cert_checked_7 55424 55552 128
cert_checked_7 55552 55680 128
cert_checked_7 55680 55808 128
cert_checked_7 55808 55936 128
cert_checked_7 55936 56064 128
cert_checked_7 56064 56192 128
cert_checked_7 56192 56320 128
cert_checked_7 56320 56448 128
cert_checked_7 56448 56576 128
cert_checked_7 56576 56704 128
cert_checked_7 56704 56832 128
cert_checked_7 56832 56960 128
cert_checked_7 56960 57088 128
cert_checked_7 57088 57216 128
cert_checked_7 57216 57344 128
theorem interval_53248 : FiniteChecks.Interval test 53248 57344 :=
  (FiniteChecks.interval_append test 53248 55296 57344
  (FiniteChecks.interval_append test 53248 54272 55296
  (FiniteChecks.interval_append test 53248 53760 54272
  (FiniteChecks.interval_append test 53248 53504 53760
  (FiniteChecks.interval_append test 53248 53376 53504
  checked_53248
  checked_53376)
  (FiniteChecks.interval_append test 53504 53632 53760
  checked_53504
  checked_53632))
  (FiniteChecks.interval_append test 53760 54016 54272
  (FiniteChecks.interval_append test 53760 53888 54016
  checked_53760
  checked_53888)
  (FiniteChecks.interval_append test 54016 54144 54272
  checked_54016
  checked_54144)))
  (FiniteChecks.interval_append test 54272 54784 55296
  (FiniteChecks.interval_append test 54272 54528 54784
  (FiniteChecks.interval_append test 54272 54400 54528
  checked_54272
  checked_54400)
  (FiniteChecks.interval_append test 54528 54656 54784
  checked_54528
  checked_54656))
  (FiniteChecks.interval_append test 54784 55040 55296
  (FiniteChecks.interval_append test 54784 54912 55040
  checked_54784
  checked_54912)
  (FiniteChecks.interval_append test 55040 55168 55296
  checked_55040
  checked_55168))))
  (FiniteChecks.interval_append test 55296 56320 57344
  (FiniteChecks.interval_append test 55296 55808 56320
  (FiniteChecks.interval_append test 55296 55552 55808
  (FiniteChecks.interval_append test 55296 55424 55552
  checked_55296
  checked_55424)
  (FiniteChecks.interval_append test 55552 55680 55808
  checked_55552
  checked_55680))
  (FiniteChecks.interval_append test 55808 56064 56320
  (FiniteChecks.interval_append test 55808 55936 56064
  checked_55808
  checked_55936)
  (FiniteChecks.interval_append test 56064 56192 56320
  checked_56064
  checked_56192)))
  (FiniteChecks.interval_append test 56320 56832 57344
  (FiniteChecks.interval_append test 56320 56576 56832
  (FiniteChecks.interval_append test 56320 56448 56576
  checked_56320
  checked_56448)
  (FiniteChecks.interval_append test 56576 56704 56832
  checked_56576
  checked_56704))
  (FiniteChecks.interval_append test 56832 57088 57344
  (FiniteChecks.interval_append test 56832 56960 57088
  checked_56832
  checked_56960)
  (FiniteChecks.interval_append test 57088 57216 57344
  checked_57088
  checked_57216)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_7 57344 57472 128
cert_checked_7 57472 57600 128
cert_checked_7 57600 57728 128
cert_checked_7 57728 57856 128
cert_checked_7 57856 57984 128
cert_checked_7 57984 58112 128
cert_checked_7 58112 58240 128
cert_checked_7 58240 58368 128
cert_checked_7 58368 58496 128
cert_checked_7 58496 58624 128
cert_checked_7 58624 58752 128
cert_checked_7 58752 58880 128
cert_checked_7 58880 59008 128
cert_checked_7 59008 59136 128
cert_checked_7 59136 59264 128
cert_checked_7 59264 59392 128
cert_checked_7 59392 59520 128
cert_checked_7 59520 59648 128
cert_checked_7 59648 59776 128
cert_checked_7 59776 59904 128
cert_checked_7 59904 60032 128
cert_checked_7 60032 60160 128
cert_checked_7 60160 60288 128
cert_checked_7 60288 60416 128
cert_checked_7 60416 60544 128
cert_checked_7 60544 60672 128
cert_checked_7 60672 60800 128
cert_checked_7 60800 60928 128
cert_checked_7 60928 61056 128
cert_checked_7 61056 61184 128
cert_checked_7 61184 61312 128
cert_checked_7 61312 61440 128
theorem interval_57344 : FiniteChecks.Interval test 57344 61440 :=
  (FiniteChecks.interval_append test 57344 59392 61440
  (FiniteChecks.interval_append test 57344 58368 59392
  (FiniteChecks.interval_append test 57344 57856 58368
  (FiniteChecks.interval_append test 57344 57600 57856
  (FiniteChecks.interval_append test 57344 57472 57600
  checked_57344
  checked_57472)
  (FiniteChecks.interval_append test 57600 57728 57856
  checked_57600
  checked_57728))
  (FiniteChecks.interval_append test 57856 58112 58368
  (FiniteChecks.interval_append test 57856 57984 58112
  checked_57856
  checked_57984)
  (FiniteChecks.interval_append test 58112 58240 58368
  checked_58112
  checked_58240)))
  (FiniteChecks.interval_append test 58368 58880 59392
  (FiniteChecks.interval_append test 58368 58624 58880
  (FiniteChecks.interval_append test 58368 58496 58624
  checked_58368
  checked_58496)
  (FiniteChecks.interval_append test 58624 58752 58880
  checked_58624
  checked_58752))
  (FiniteChecks.interval_append test 58880 59136 59392
  (FiniteChecks.interval_append test 58880 59008 59136
  checked_58880
  checked_59008)
  (FiniteChecks.interval_append test 59136 59264 59392
  checked_59136
  checked_59264))))
  (FiniteChecks.interval_append test 59392 60416 61440
  (FiniteChecks.interval_append test 59392 59904 60416
  (FiniteChecks.interval_append test 59392 59648 59904
  (FiniteChecks.interval_append test 59392 59520 59648
  checked_59392
  checked_59520)
  (FiniteChecks.interval_append test 59648 59776 59904
  checked_59648
  checked_59776))
  (FiniteChecks.interval_append test 59904 60160 60416
  (FiniteChecks.interval_append test 59904 60032 60160
  checked_59904
  checked_60032)
  (FiniteChecks.interval_append test 60160 60288 60416
  checked_60160
  checked_60288)))
  (FiniteChecks.interval_append test 60416 60928 61440
  (FiniteChecks.interval_append test 60416 60672 60928
  (FiniteChecks.interval_append test 60416 60544 60672
  checked_60416
  checked_60544)
  (FiniteChecks.interval_append test 60672 60800 60928
  checked_60672
  checked_60800))
  (FiniteChecks.interval_append test 60928 61184 61440
  (FiniteChecks.interval_append test 60928 61056 61184
  checked_60928
  checked_61056)
  (FiniteChecks.interval_append test 61184 61312 61440
  checked_61184
  checked_61312)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_7 61440 61568 128
cert_checked_7 61568 61696 128
cert_checked_7 61696 61824 128
cert_checked_7 61824 61952 128
cert_checked_7 61952 62080 128
cert_checked_7 62080 62208 128
cert_checked_7 62208 62336 128
cert_checked_7 62336 62464 128
cert_checked_7 62464 62592 128
cert_checked_7 62592 62720 128
cert_checked_7 62720 62848 128
cert_checked_7 62848 62976 128
cert_checked_7 62976 63104 128
cert_checked_7 63104 63232 128
cert_checked_7 63232 63360 128
cert_checked_7 63360 63488 128
cert_checked_7 63488 63616 128
cert_checked_7 63616 63744 128
cert_checked_7 63744 63872 128
cert_checked_7 63872 64000 128
cert_checked_7 64000 64128 128
cert_checked_7 64128 64256 128
cert_checked_7 64256 64384 128
cert_checked_7 64384 64512 128
cert_checked_7 64512 64640 128
cert_checked_7 64640 64768 128
cert_checked_7 64768 64896 128
cert_checked_7 64896 65024 128
cert_checked_7 65024 65152 128
cert_checked_7 65152 65280 128
cert_checked_7 65280 65408 128
cert_checked_7 65408 65536 128
theorem interval_61440 : FiniteChecks.Interval test 61440 65536 :=
  (FiniteChecks.interval_append test 61440 63488 65536
  (FiniteChecks.interval_append test 61440 62464 63488
  (FiniteChecks.interval_append test 61440 61952 62464
  (FiniteChecks.interval_append test 61440 61696 61952
  (FiniteChecks.interval_append test 61440 61568 61696
  checked_61440
  checked_61568)
  (FiniteChecks.interval_append test 61696 61824 61952
  checked_61696
  checked_61824))
  (FiniteChecks.interval_append test 61952 62208 62464
  (FiniteChecks.interval_append test 61952 62080 62208
  checked_61952
  checked_62080)
  (FiniteChecks.interval_append test 62208 62336 62464
  checked_62208
  checked_62336)))
  (FiniteChecks.interval_append test 62464 62976 63488
  (FiniteChecks.interval_append test 62464 62720 62976
  (FiniteChecks.interval_append test 62464 62592 62720
  checked_62464
  checked_62592)
  (FiniteChecks.interval_append test 62720 62848 62976
  checked_62720
  checked_62848))
  (FiniteChecks.interval_append test 62976 63232 63488
  (FiniteChecks.interval_append test 62976 63104 63232
  checked_62976
  checked_63104)
  (FiniteChecks.interval_append test 63232 63360 63488
  checked_63232
  checked_63360))))
  (FiniteChecks.interval_append test 63488 64512 65536
  (FiniteChecks.interval_append test 63488 64000 64512
  (FiniteChecks.interval_append test 63488 63744 64000
  (FiniteChecks.interval_append test 63488 63616 63744
  checked_63488
  checked_63616)
  (FiniteChecks.interval_append test 63744 63872 64000
  checked_63744
  checked_63872))
  (FiniteChecks.interval_append test 64000 64256 64512
  (FiniteChecks.interval_append test 64000 64128 64256
  checked_64000
  checked_64128)
  (FiniteChecks.interval_append test 64256 64384 64512
  checked_64256
  checked_64384)))
  (FiniteChecks.interval_append test 64512 65024 65536
  (FiniteChecks.interval_append test 64512 64768 65024
  (FiniteChecks.interval_append test 64512 64640 64768
  checked_64512
  checked_64640)
  (FiniteChecks.interval_append test 64768 64896 65024
  checked_64768
  checked_64896))
  (FiniteChecks.interval_append test 65024 65280 65536
  (FiniteChecks.interval_append test 65024 65152 65280
  checked_65024
  checked_65152)
  (FiniteChecks.interval_append test 65280 65408 65536
  checked_65280
  checked_65408)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
end
end
