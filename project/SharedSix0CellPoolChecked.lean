module
prelude
public import SharedSix0CellPoolReplay00
public import SharedSix0CellPoolReplay01
public import SharedSix0CellPoolReplay02
public import SharedSix0CellPoolReplay03
public import SharedSix0CellPoolReplay04
public import SharedSix0CellPoolReplay05
public import SharedSix0CellPoolReplay06
public import SharedSix0CellPoolReplay07
public import SharedSix0CellPoolReplay08
public import SharedSix0CellPoolReplay09
public import SharedSix0CellPoolReplay10
public import SharedSix0CellPoolReplay11
public import SharedSix0CellPoolReplay12
public import SharedSix0CellPoolReplay13
public import SharedSix0CellPoolReplay14
public import SharedSix0CellPoolReplay15
public import SharedSix0CellPoolReplay16
public import SharedSix0CellPoolReplay17

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem checked : Interval test 0 count :=
  (FiniteChecks.interval_append test 0 22144 44310
  (FiniteChecks.interval_append test 0 11008 22144
  (FiniteChecks.interval_append test 0 5504 11008
  (FiniteChecks.interval_append test 0 2688 5504
  (FiniteChecks.interval_append test 0 1280 2688
  (FiniteChecks.interval_append test 0 640 1280
  (FiniteChecks.interval_append test 0 256 640
  (FiniteChecks.interval_append test 0 128 256
  Check000.checked
  Check001.checked)
  (FiniteChecks.interval_append test 256 384 640
  Check002.checked
  (FiniteChecks.interval_append test 384 512 640
  Check003.checked
  Check004.checked)))
  (FiniteChecks.interval_append test 640 896 1280
  (FiniteChecks.interval_append test 640 768 896
  Check005.checked
  Check006.checked)
  (FiniteChecks.interval_append test 896 1024 1280
  Check007.checked
  (FiniteChecks.interval_append test 1024 1152 1280
  Check008.checked
  Check009.checked))))
  (FiniteChecks.interval_append test 1280 1920 2688
  (FiniteChecks.interval_append test 1280 1536 1920
  (FiniteChecks.interval_append test 1280 1408 1536
  Check010.checked
  Check011.checked)
  (FiniteChecks.interval_append test 1536 1664 1920
  Check012.checked
  (FiniteChecks.interval_append test 1664 1792 1920
  Check013.checked
  Check014.checked)))
  (FiniteChecks.interval_append test 1920 2304 2688
  (FiniteChecks.interval_append test 1920 2048 2304
  Check015.checked
  (FiniteChecks.interval_append test 2048 2176 2304
  Check016.checked
  Check017.checked))
  (FiniteChecks.interval_append test 2304 2432 2688
  Check018.checked
  (FiniteChecks.interval_append test 2432 2560 2688
  Check019.checked
  Check020.checked)))))
  (FiniteChecks.interval_append test 2688 4096 5504
  (FiniteChecks.interval_append test 2688 3328 4096
  (FiniteChecks.interval_append test 2688 2944 3328
  (FiniteChecks.interval_append test 2688 2816 2944
  Check021.checked
  Check022.checked)
  (FiniteChecks.interval_append test 2944 3072 3328
  Check023.checked
  (FiniteChecks.interval_append test 3072 3200 3328
  Check024.checked
  Check025.checked)))
  (FiniteChecks.interval_append test 3328 3712 4096
  (FiniteChecks.interval_append test 3328 3456 3712
  Check026.checked
  (FiniteChecks.interval_append test 3456 3584 3712
  Check027.checked
  Check028.checked))
  (FiniteChecks.interval_append test 3712 3840 4096
  Check029.checked
  (FiniteChecks.interval_append test 3840 3968 4096
  Check030.checked
  Check031.checked))))
  (FiniteChecks.interval_append test 4096 4736 5504
  (FiniteChecks.interval_append test 4096 4352 4736
  (FiniteChecks.interval_append test 4096 4224 4352
  Check032.checked
  Check033.checked)
  (FiniteChecks.interval_append test 4352 4480 4736
  Check034.checked
  (FiniteChecks.interval_append test 4480 4608 4736
  Check035.checked
  Check036.checked)))
  (FiniteChecks.interval_append test 4736 5120 5504
  (FiniteChecks.interval_append test 4736 4864 5120
  Check037.checked
  (FiniteChecks.interval_append test 4864 4992 5120
  Check038.checked
  Check039.checked))
  (FiniteChecks.interval_append test 5120 5248 5504
  Check040.checked
  (FiniteChecks.interval_append test 5248 5376 5504
  Check041.checked
  Check042.checked))))))
  (FiniteChecks.interval_append test 5504 8192 11008
  (FiniteChecks.interval_append test 5504 6784 8192
  (FiniteChecks.interval_append test 5504 6144 6784
  (FiniteChecks.interval_append test 5504 5760 6144
  (FiniteChecks.interval_append test 5504 5632 5760
  Check043.checked
  Check044.checked)
  (FiniteChecks.interval_append test 5760 5888 6144
  Check045.checked
  (FiniteChecks.interval_append test 5888 6016 6144
  Check046.checked
  Check047.checked)))
  (FiniteChecks.interval_append test 6144 6400 6784
  (FiniteChecks.interval_append test 6144 6272 6400
  Check048.checked
  Check049.checked)
  (FiniteChecks.interval_append test 6400 6528 6784
  Check050.checked
  (FiniteChecks.interval_append test 6528 6656 6784
  Check051.checked
  Check052.checked))))
  (FiniteChecks.interval_append test 6784 7424 8192
  (FiniteChecks.interval_append test 6784 7040 7424
  (FiniteChecks.interval_append test 6784 6912 7040
  Check053.checked
  Check054.checked)
  (FiniteChecks.interval_append test 7040 7168 7424
  Check055.checked
  (FiniteChecks.interval_append test 7168 7296 7424
  Check056.checked
  Check057.checked)))
  (FiniteChecks.interval_append test 7424 7808 8192
  (FiniteChecks.interval_append test 7424 7552 7808
  Check058.checked
  (FiniteChecks.interval_append test 7552 7680 7808
  Check059.checked
  Check060.checked))
  (FiniteChecks.interval_append test 7808 7936 8192
  Check061.checked
  (FiniteChecks.interval_append test 7936 8064 8192
  Check062.checked
  Check063.checked)))))
  (FiniteChecks.interval_append test 8192 9600 11008
  (FiniteChecks.interval_append test 8192 8832 9600
  (FiniteChecks.interval_append test 8192 8448 8832
  (FiniteChecks.interval_append test 8192 8320 8448
  Check064.checked
  Check065.checked)
  (FiniteChecks.interval_append test 8448 8576 8832
  Check066.checked
  (FiniteChecks.interval_append test 8576 8704 8832
  Check067.checked
  Check068.checked)))
  (FiniteChecks.interval_append test 8832 9216 9600
  (FiniteChecks.interval_append test 8832 8960 9216
  Check069.checked
  (FiniteChecks.interval_append test 8960 9088 9216
  Check070.checked
  Check071.checked))
  (FiniteChecks.interval_append test 9216 9344 9600
  Check072.checked
  (FiniteChecks.interval_append test 9344 9472 9600
  Check073.checked
  Check074.checked))))
  (FiniteChecks.interval_append test 9600 10240 11008
  (FiniteChecks.interval_append test 9600 9856 10240
  (FiniteChecks.interval_append test 9600 9728 9856
  Check075.checked
  Check076.checked)
  (FiniteChecks.interval_append test 9856 9984 10240
  Check077.checked
  (FiniteChecks.interval_append test 9984 10112 10240
  Check078.checked
  Check079.checked)))
  (FiniteChecks.interval_append test 10240 10624 11008
  (FiniteChecks.interval_append test 10240 10368 10624
  Check080.checked
  (FiniteChecks.interval_append test 10368 10496 10624
  Check081.checked
  Check082.checked))
  (FiniteChecks.interval_append test 10624 10752 11008
  Check083.checked
  (FiniteChecks.interval_append test 10752 10880 11008
  Check084.checked
  Check085.checked)))))))
  (FiniteChecks.interval_append test 11008 16512 22144
  (FiniteChecks.interval_append test 11008 13696 16512
  (FiniteChecks.interval_append test 11008 12288 13696
  (FiniteChecks.interval_append test 11008 11648 12288
  (FiniteChecks.interval_append test 11008 11264 11648
  (FiniteChecks.interval_append test 11008 11136 11264
  Check086.checked
  Check087.checked)
  (FiniteChecks.interval_append test 11264 11392 11648
  Check088.checked
  (FiniteChecks.interval_append test 11392 11520 11648
  Check089.checked
  Check090.checked)))
  (FiniteChecks.interval_append test 11648 11904 12288
  (FiniteChecks.interval_append test 11648 11776 11904
  Check091.checked
  Check092.checked)
  (FiniteChecks.interval_append test 11904 12032 12288
  Check093.checked
  (FiniteChecks.interval_append test 12032 12160 12288
  Check094.checked
  Check095.checked))))
  (FiniteChecks.interval_append test 12288 12928 13696
  (FiniteChecks.interval_append test 12288 12544 12928
  (FiniteChecks.interval_append test 12288 12416 12544
  Check096.checked
  Check097.checked)
  (FiniteChecks.interval_append test 12544 12672 12928
  Check098.checked
  (FiniteChecks.interval_append test 12672 12800 12928
  Check099.checked
  Check100.checked)))
  (FiniteChecks.interval_append test 12928 13312 13696
  (FiniteChecks.interval_append test 12928 13056 13312
  Check101.checked
  (FiniteChecks.interval_append test 13056 13184 13312
  Check102.checked
  Check103.checked))
  (FiniteChecks.interval_append test 13312 13440 13696
  Check104.checked
  (FiniteChecks.interval_append test 13440 13568 13696
  Check105.checked
  Check106.checked)))))
  (FiniteChecks.interval_append test 13696 15104 16512
  (FiniteChecks.interval_append test 13696 14336 15104
  (FiniteChecks.interval_append test 13696 13952 14336
  (FiniteChecks.interval_append test 13696 13824 13952
  Check107.checked
  Check108.checked)
  (FiniteChecks.interval_append test 13952 14080 14336
  Check109.checked
  (FiniteChecks.interval_append test 14080 14208 14336
  Check110.checked
  Check111.checked)))
  (FiniteChecks.interval_append test 14336 14720 15104
  (FiniteChecks.interval_append test 14336 14464 14720
  Check112.checked
  (FiniteChecks.interval_append test 14464 14592 14720
  Check113.checked
  Check114.checked))
  (FiniteChecks.interval_append test 14720 14848 15104
  Check115.checked
  (FiniteChecks.interval_append test 14848 14976 15104
  Check116.checked
  Check117.checked))))
  (FiniteChecks.interval_append test 15104 15744 16512
  (FiniteChecks.interval_append test 15104 15360 15744
  (FiniteChecks.interval_append test 15104 15232 15360
  Check118.checked
  Check119.checked)
  (FiniteChecks.interval_append test 15360 15488 15744
  Check120.checked
  (FiniteChecks.interval_append test 15488 15616 15744
  Check121.checked
  Check122.checked)))
  (FiniteChecks.interval_append test 15744 16128 16512
  (FiniteChecks.interval_append test 15744 15872 16128
  Check123.checked
  (FiniteChecks.interval_append test 15872 16000 16128
  Check124.checked
  Check125.checked))
  (FiniteChecks.interval_append test 16128 16256 16512
  Check126.checked
  (FiniteChecks.interval_append test 16256 16384 16512
  Check127.checked
  Check128.checked))))))
  (FiniteChecks.interval_append test 16512 19328 22144
  (FiniteChecks.interval_append test 16512 17920 19328
  (FiniteChecks.interval_append test 16512 17152 17920
  (FiniteChecks.interval_append test 16512 16768 17152
  (FiniteChecks.interval_append test 16512 16640 16768
  Check129.checked
  Check130.checked)
  (FiniteChecks.interval_append test 16768 16896 17152
  Check131.checked
  (FiniteChecks.interval_append test 16896 17024 17152
  Check132.checked
  Check133.checked)))
  (FiniteChecks.interval_append test 17152 17536 17920
  (FiniteChecks.interval_append test 17152 17280 17536
  Check134.checked
  (FiniteChecks.interval_append test 17280 17408 17536
  Check135.checked
  Check136.checked))
  (FiniteChecks.interval_append test 17536 17664 17920
  Check137.checked
  (FiniteChecks.interval_append test 17664 17792 17920
  Check138.checked
  Check139.checked))))
  (FiniteChecks.interval_append test 17920 18560 19328
  (FiniteChecks.interval_append test 17920 18176 18560
  (FiniteChecks.interval_append test 17920 18048 18176
  Check140.checked
  Check141.checked)
  (FiniteChecks.interval_append test 18176 18304 18560
  Check142.checked
  (FiniteChecks.interval_append test 18304 18432 18560
  Check143.checked
  Check144.checked)))
  (FiniteChecks.interval_append test 18560 18944 19328
  (FiniteChecks.interval_append test 18560 18688 18944
  Check145.checked
  (FiniteChecks.interval_append test 18688 18816 18944
  Check146.checked
  Check147.checked))
  (FiniteChecks.interval_append test 18944 19072 19328
  Check148.checked
  (FiniteChecks.interval_append test 19072 19200 19328
  Check149.checked
  Check150.checked)))))
  (FiniteChecks.interval_append test 19328 20736 22144
  (FiniteChecks.interval_append test 19328 19968 20736
  (FiniteChecks.interval_append test 19328 19584 19968
  (FiniteChecks.interval_append test 19328 19456 19584
  Check151.checked
  Check152.checked)
  (FiniteChecks.interval_append test 19584 19712 19968
  Check153.checked
  (FiniteChecks.interval_append test 19712 19840 19968
  Check154.checked
  Check155.checked)))
  (FiniteChecks.interval_append test 19968 20352 20736
  (FiniteChecks.interval_append test 19968 20096 20352
  Check156.checked
  (FiniteChecks.interval_append test 20096 20224 20352
  Check157.checked
  Check158.checked))
  (FiniteChecks.interval_append test 20352 20480 20736
  Check159.checked
  (FiniteChecks.interval_append test 20480 20608 20736
  Check160.checked
  Check161.checked))))
  (FiniteChecks.interval_append test 20736 21376 22144
  (FiniteChecks.interval_append test 20736 20992 21376
  (FiniteChecks.interval_append test 20736 20864 20992
  Check162.checked
  Check163.checked)
  (FiniteChecks.interval_append test 20992 21120 21376
  Check164.checked
  (FiniteChecks.interval_append test 21120 21248 21376
  Check165.checked
  Check166.checked)))
  (FiniteChecks.interval_append test 21376 21760 22144
  (FiniteChecks.interval_append test 21376 21504 21760
  Check167.checked
  (FiniteChecks.interval_append test 21504 21632 21760
  Check168.checked
  Check169.checked))
  (FiniteChecks.interval_append test 21760 21888 22144
  Check170.checked
  (FiniteChecks.interval_append test 21888 22016 22144
  Check171.checked
  Check172.checked))))))))
  (FiniteChecks.interval_append test 22144 33280 44310
  (FiniteChecks.interval_append test 22144 27648 33280
  (FiniteChecks.interval_append test 22144 24832 27648
  (FiniteChecks.interval_append test 22144 23424 24832
  (FiniteChecks.interval_append test 22144 22784 23424
  (FiniteChecks.interval_append test 22144 22400 22784
  (FiniteChecks.interval_append test 22144 22272 22400
  Check173.checked
  Check174.checked)
  (FiniteChecks.interval_append test 22400 22528 22784
  Check175.checked
  (FiniteChecks.interval_append test 22528 22656 22784
  Check176.checked
  Check177.checked)))
  (FiniteChecks.interval_append test 22784 23040 23424
  (FiniteChecks.interval_append test 22784 22912 23040
  Check178.checked
  Check179.checked)
  (FiniteChecks.interval_append test 23040 23168 23424
  Check180.checked
  (FiniteChecks.interval_append test 23168 23296 23424
  Check181.checked
  Check182.checked))))
  (FiniteChecks.interval_append test 23424 24064 24832
  (FiniteChecks.interval_append test 23424 23680 24064
  (FiniteChecks.interval_append test 23424 23552 23680
  Check183.checked
  Check184.checked)
  (FiniteChecks.interval_append test 23680 23808 24064
  Check185.checked
  (FiniteChecks.interval_append test 23808 23936 24064
  Check186.checked
  Check187.checked)))
  (FiniteChecks.interval_append test 24064 24448 24832
  (FiniteChecks.interval_append test 24064 24192 24448
  Check188.checked
  (FiniteChecks.interval_append test 24192 24320 24448
  Check189.checked
  Check190.checked))
  (FiniteChecks.interval_append test 24448 24576 24832
  Check191.checked
  (FiniteChecks.interval_append test 24576 24704 24832
  Check192.checked
  Check193.checked)))))
  (FiniteChecks.interval_append test 24832 26240 27648
  (FiniteChecks.interval_append test 24832 25472 26240
  (FiniteChecks.interval_append test 24832 25088 25472
  (FiniteChecks.interval_append test 24832 24960 25088
  Check194.checked
  Check195.checked)
  (FiniteChecks.interval_append test 25088 25216 25472
  Check196.checked
  (FiniteChecks.interval_append test 25216 25344 25472
  Check197.checked
  Check198.checked)))
  (FiniteChecks.interval_append test 25472 25856 26240
  (FiniteChecks.interval_append test 25472 25600 25856
  Check199.checked
  (FiniteChecks.interval_append test 25600 25728 25856
  Check200.checked
  Check201.checked))
  (FiniteChecks.interval_append test 25856 25984 26240
  Check202.checked
  (FiniteChecks.interval_append test 25984 26112 26240
  Check203.checked
  Check204.checked))))
  (FiniteChecks.interval_append test 26240 26880 27648
  (FiniteChecks.interval_append test 26240 26496 26880
  (FiniteChecks.interval_append test 26240 26368 26496
  Check205.checked
  Check206.checked)
  (FiniteChecks.interval_append test 26496 26624 26880
  Check207.checked
  (FiniteChecks.interval_append test 26624 26752 26880
  Check208.checked
  Check209.checked)))
  (FiniteChecks.interval_append test 26880 27264 27648
  (FiniteChecks.interval_append test 26880 27008 27264
  Check210.checked
  (FiniteChecks.interval_append test 27008 27136 27264
  Check211.checked
  Check212.checked))
  (FiniteChecks.interval_append test 27264 27392 27648
  Check213.checked
  (FiniteChecks.interval_append test 27392 27520 27648
  Check214.checked
  Check215.checked))))))
  (FiniteChecks.interval_append test 27648 30464 33280
  (FiniteChecks.interval_append test 27648 29056 30464
  (FiniteChecks.interval_append test 27648 28288 29056
  (FiniteChecks.interval_append test 27648 27904 28288
  (FiniteChecks.interval_append test 27648 27776 27904
  Check216.checked
  Check217.checked)
  (FiniteChecks.interval_append test 27904 28032 28288
  Check218.checked
  (FiniteChecks.interval_append test 28032 28160 28288
  Check219.checked
  Check220.checked)))
  (FiniteChecks.interval_append test 28288 28672 29056
  (FiniteChecks.interval_append test 28288 28416 28672
  Check221.checked
  (FiniteChecks.interval_append test 28416 28544 28672
  Check222.checked
  Check223.checked))
  (FiniteChecks.interval_append test 28672 28800 29056
  Check224.checked
  (FiniteChecks.interval_append test 28800 28928 29056
  Check225.checked
  Check226.checked))))
  (FiniteChecks.interval_append test 29056 29696 30464
  (FiniteChecks.interval_append test 29056 29312 29696
  (FiniteChecks.interval_append test 29056 29184 29312
  Check227.checked
  Check228.checked)
  (FiniteChecks.interval_append test 29312 29440 29696
  Check229.checked
  (FiniteChecks.interval_append test 29440 29568 29696
  Check230.checked
  Check231.checked)))
  (FiniteChecks.interval_append test 29696 30080 30464
  (FiniteChecks.interval_append test 29696 29824 30080
  Check232.checked
  (FiniteChecks.interval_append test 29824 29952 30080
  Check233.checked
  Check234.checked))
  (FiniteChecks.interval_append test 30080 30208 30464
  Check235.checked
  (FiniteChecks.interval_append test 30208 30336 30464
  Check236.checked
  Check237.checked)))))
  (FiniteChecks.interval_append test 30464 31872 33280
  (FiniteChecks.interval_append test 30464 31104 31872
  (FiniteChecks.interval_append test 30464 30720 31104
  (FiniteChecks.interval_append test 30464 30592 30720
  Check238.checked
  Check239.checked)
  (FiniteChecks.interval_append test 30720 30848 31104
  Check240.checked
  (FiniteChecks.interval_append test 30848 30976 31104
  Check241.checked
  Check242.checked)))
  (FiniteChecks.interval_append test 31104 31488 31872
  (FiniteChecks.interval_append test 31104 31232 31488
  Check243.checked
  (FiniteChecks.interval_append test 31232 31360 31488
  Check244.checked
  Check245.checked))
  (FiniteChecks.interval_append test 31488 31616 31872
  Check246.checked
  (FiniteChecks.interval_append test 31616 31744 31872
  Check247.checked
  Check248.checked))))
  (FiniteChecks.interval_append test 31872 32512 33280
  (FiniteChecks.interval_append test 31872 32128 32512
  (FiniteChecks.interval_append test 31872 32000 32128
  Check249.checked
  Check250.checked)
  (FiniteChecks.interval_append test 32128 32256 32512
  Check251.checked
  (FiniteChecks.interval_append test 32256 32384 32512
  Check252.checked
  Check253.checked)))
  (FiniteChecks.interval_append test 32512 32896 33280
  (FiniteChecks.interval_append test 32512 32640 32896
  Check254.checked
  (FiniteChecks.interval_append test 32640 32768 32896
  Check255.checked
  Check256.checked))
  (FiniteChecks.interval_append test 32896 33024 33280
  Check257.checked
  (FiniteChecks.interval_append test 33024 33152 33280
  Check258.checked
  Check259.checked)))))))
  (FiniteChecks.interval_append test 33280 38784 44310
  (FiniteChecks.interval_append test 33280 35968 38784
  (FiniteChecks.interval_append test 33280 34560 35968
  (FiniteChecks.interval_append test 33280 33920 34560
  (FiniteChecks.interval_append test 33280 33536 33920
  (FiniteChecks.interval_append test 33280 33408 33536
  Check260.checked
  Check261.checked)
  (FiniteChecks.interval_append test 33536 33664 33920
  Check262.checked
  (FiniteChecks.interval_append test 33664 33792 33920
  Check263.checked
  Check264.checked)))
  (FiniteChecks.interval_append test 33920 34176 34560
  (FiniteChecks.interval_append test 33920 34048 34176
  Check265.checked
  Check266.checked)
  (FiniteChecks.interval_append test 34176 34304 34560
  Check267.checked
  (FiniteChecks.interval_append test 34304 34432 34560
  Check268.checked
  Check269.checked))))
  (FiniteChecks.interval_append test 34560 35200 35968
  (FiniteChecks.interval_append test 34560 34816 35200
  (FiniteChecks.interval_append test 34560 34688 34816
  Check270.checked
  Check271.checked)
  (FiniteChecks.interval_append test 34816 34944 35200
  Check272.checked
  (FiniteChecks.interval_append test 34944 35072 35200
  Check273.checked
  Check274.checked)))
  (FiniteChecks.interval_append test 35200 35584 35968
  (FiniteChecks.interval_append test 35200 35328 35584
  Check275.checked
  (FiniteChecks.interval_append test 35328 35456 35584
  Check276.checked
  Check277.checked))
  (FiniteChecks.interval_append test 35584 35712 35968
  Check278.checked
  (FiniteChecks.interval_append test 35712 35840 35968
  Check279.checked
  Check280.checked)))))
  (FiniteChecks.interval_append test 35968 37376 38784
  (FiniteChecks.interval_append test 35968 36608 37376
  (FiniteChecks.interval_append test 35968 36224 36608
  (FiniteChecks.interval_append test 35968 36096 36224
  Check281.checked
  Check282.checked)
  (FiniteChecks.interval_append test 36224 36352 36608
  Check283.checked
  (FiniteChecks.interval_append test 36352 36480 36608
  Check284.checked
  Check285.checked)))
  (FiniteChecks.interval_append test 36608 36992 37376
  (FiniteChecks.interval_append test 36608 36736 36992
  Check286.checked
  (FiniteChecks.interval_append test 36736 36864 36992
  Check287.checked
  Check288.checked))
  (FiniteChecks.interval_append test 36992 37120 37376
  Check289.checked
  (FiniteChecks.interval_append test 37120 37248 37376
  Check290.checked
  Check291.checked))))
  (FiniteChecks.interval_append test 37376 38016 38784
  (FiniteChecks.interval_append test 37376 37632 38016
  (FiniteChecks.interval_append test 37376 37504 37632
  Check292.checked
  Check293.checked)
  (FiniteChecks.interval_append test 37632 37760 38016
  Check294.checked
  (FiniteChecks.interval_append test 37760 37888 38016
  Check295.checked
  Check296.checked)))
  (FiniteChecks.interval_append test 38016 38400 38784
  (FiniteChecks.interval_append test 38016 38144 38400
  Check297.checked
  (FiniteChecks.interval_append test 38144 38272 38400
  Check298.checked
  Check299.checked))
  (FiniteChecks.interval_append test 38400 38528 38784
  Check300.checked
  (FiniteChecks.interval_append test 38528 38656 38784
  Check301.checked
  Check302.checked))))))
  (FiniteChecks.interval_append test 38784 41600 44310
  (FiniteChecks.interval_append test 38784 40192 41600
  (FiniteChecks.interval_append test 38784 39424 40192
  (FiniteChecks.interval_append test 38784 39040 39424
  (FiniteChecks.interval_append test 38784 38912 39040
  Check303.checked
  Check304.checked)
  (FiniteChecks.interval_append test 39040 39168 39424
  Check305.checked
  (FiniteChecks.interval_append test 39168 39296 39424
  Check306.checked
  Check307.checked)))
  (FiniteChecks.interval_append test 39424 39808 40192
  (FiniteChecks.interval_append test 39424 39552 39808
  Check308.checked
  (FiniteChecks.interval_append test 39552 39680 39808
  Check309.checked
  Check310.checked))
  (FiniteChecks.interval_append test 39808 39936 40192
  Check311.checked
  (FiniteChecks.interval_append test 39936 40064 40192
  Check312.checked
  Check313.checked))))
  (FiniteChecks.interval_append test 40192 40832 41600
  (FiniteChecks.interval_append test 40192 40448 40832
  (FiniteChecks.interval_append test 40192 40320 40448
  Check314.checked
  Check315.checked)
  (FiniteChecks.interval_append test 40448 40576 40832
  Check316.checked
  (FiniteChecks.interval_append test 40576 40704 40832
  Check317.checked
  Check318.checked)))
  (FiniteChecks.interval_append test 40832 41216 41600
  (FiniteChecks.interval_append test 40832 40960 41216
  Check319.checked
  (FiniteChecks.interval_append test 40960 41088 41216
  Check320.checked
  Check321.checked))
  (FiniteChecks.interval_append test 41216 41344 41600
  Check322.checked
  (FiniteChecks.interval_append test 41344 41472 41600
  Check323.checked
  Check324.checked)))))
  (FiniteChecks.interval_append test 41600 43008 44310
  (FiniteChecks.interval_append test 41600 42240 43008
  (FiniteChecks.interval_append test 41600 41856 42240
  (FiniteChecks.interval_append test 41600 41728 41856
  Check325.checked
  Check326.checked)
  (FiniteChecks.interval_append test 41856 41984 42240
  Check327.checked
  (FiniteChecks.interval_append test 41984 42112 42240
  Check328.checked
  Check329.checked)))
  (FiniteChecks.interval_append test 42240 42624 43008
  (FiniteChecks.interval_append test 42240 42368 42624
  Check330.checked
  (FiniteChecks.interval_append test 42368 42496 42624
  Check331.checked
  Check332.checked))
  (FiniteChecks.interval_append test 42624 42752 43008
  Check333.checked
  (FiniteChecks.interval_append test 42752 42880 43008
  Check334.checked
  Check335.checked))))
  (FiniteChecks.interval_append test 43008 43648 44310
  (FiniteChecks.interval_append test 43008 43264 43648
  (FiniteChecks.interval_append test 43008 43136 43264
  Check336.checked
  Check337.checked)
  (FiniteChecks.interval_append test 43264 43392 43648
  Check338.checked
  (FiniteChecks.interval_append test 43392 43520 43648
  Check339.checked
  Check340.checked)))
  (FiniteChecks.interval_append test 43648 44032 44310
  (FiniteChecks.interval_append test 43648 43776 44032
  Check341.checked
  (FiniteChecks.interval_append test 43776 43904 44032
  Check342.checked
  Check343.checked))
  (FiniteChecks.interval_append test 44032 44160 44310
  Check344.checked
  (FiniteChecks.interval_append test 44160 44288 44310
  Check345.checked
  Check346.checked)))))))))
theorem facts (c : Fin count) :
    (entry c).Facts (FacetUniverses.FullSix0.cells c) SharedSmallGraph.withinMask := by
  apply Entry.facts_of_check
  exact fin_of_interval (fun c : Fin count =>
    (entry c).check (FacetUniverses.FullSix0.cells c) SharedSmallGraph.withinMask) checked c
#print axioms facts
end Papers.RationalityTen.SharedSix0CellPool
