module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase02FastGeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.Fast
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
end Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.Fast
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.Fast
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
end Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.Fast
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.Fast
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
end Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.Fast
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.Fast
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
end Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.Fast
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.Fast
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
end Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.Fast
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.Fast
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
end Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.Fast
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.Fast
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
end Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.Fast
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.Fast
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
cert_checked_7 32256 32336 80
theorem interval_28672 : FiniteChecks.Interval test 28672 32336 :=
  (FiniteChecks.interval_append test 28672 30464 32336
  (FiniteChecks.interval_append test 28672 29568 30464
  (FiniteChecks.interval_append test 28672 29056 29568
  (FiniteChecks.interval_append test 28672 28800 29056
  checked_28672
  (FiniteChecks.interval_append test 28800 28928 29056
  checked_28800
  checked_28928))
  (FiniteChecks.interval_append test 29056 29312 29568
  (FiniteChecks.interval_append test 29056 29184 29312
  checked_29056
  checked_29184)
  (FiniteChecks.interval_append test 29312 29440 29568
  checked_29312
  checked_29440)))
  (FiniteChecks.interval_append test 29568 29952 30464
  (FiniteChecks.interval_append test 29568 29696 29952
  checked_29568
  (FiniteChecks.interval_append test 29696 29824 29952
  checked_29696
  checked_29824))
  (FiniteChecks.interval_append test 29952 30208 30464
  (FiniteChecks.interval_append test 29952 30080 30208
  checked_29952
  checked_30080)
  (FiniteChecks.interval_append test 30208 30336 30464
  checked_30208
  checked_30336))))
  (FiniteChecks.interval_append test 30464 31360 32336
  (FiniteChecks.interval_append test 30464 30848 31360
  (FiniteChecks.interval_append test 30464 30592 30848
  checked_30464
  (FiniteChecks.interval_append test 30592 30720 30848
  checked_30592
  checked_30720))
  (FiniteChecks.interval_append test 30848 31104 31360
  (FiniteChecks.interval_append test 30848 30976 31104
  checked_30848
  checked_30976)
  (FiniteChecks.interval_append test 31104 31232 31360
  checked_31104
  checked_31232)))
  (FiniteChecks.interval_append test 31360 31872 32336
  (FiniteChecks.interval_append test 31360 31616 31872
  (FiniteChecks.interval_append test 31360 31488 31616
  checked_31360
  checked_31488)
  (FiniteChecks.interval_append test 31616 31744 31872
  checked_31616
  checked_31744))
  (FiniteChecks.interval_append test 31872 32128 32336
  (FiniteChecks.interval_append test 31872 32000 32128
  checked_31872
  checked_32000)
  (FiniteChecks.interval_append test 32128 32256 32336
  checked_32128
  checked_32256)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.Fast
end
end
