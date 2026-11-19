module
prelude
public import SharedSix0IncidenceReplay00
public import SharedSix0IncidenceReplay01
public import SharedSix0IncidenceReplay02
public import SharedSix0IncidenceReplay03
public import SharedSix0IncidenceReplay04
public import SharedSix0IncidenceReplay05
public import SharedSix0IncidenceReplay06
public import SharedSix0IncidenceReplay07
public import SharedSix0IncidenceReplay08

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem checked : Interval test 0 44310 :=
  (FiniteChecks.interval_append test 0 22272 44310
  (FiniteChecks.interval_append test 0 11008 22272
  (FiniteChecks.interval_append test 0 5376 11008
  (FiniteChecks.interval_append test 0 2560 5376
  (FiniteChecks.interval_append test 0 1280 2560
  (FiniteChecks.interval_append test 0 512 1280
  (FiniteChecks.interval_append test 0 256 512
  Check000.checked
  Check001.checked)
  (FiniteChecks.interval_append test 512 768 1280
  Check002.checked
  (FiniteChecks.interval_append test 768 1024 1280
  Check003.checked
  Check004.checked)))
  (FiniteChecks.interval_append test 1280 1792 2560
  (FiniteChecks.interval_append test 1280 1536 1792
  Check005.checked
  Check006.checked)
  (FiniteChecks.interval_append test 1792 2048 2560
  Check007.checked
  (FiniteChecks.interval_append test 2048 2304 2560
  Check008.checked
  Check009.checked))))
  (FiniteChecks.interval_append test 2560 3840 5376
  (FiniteChecks.interval_append test 2560 3072 3840
  (FiniteChecks.interval_append test 2560 2816 3072
  Check010.checked
  Check011.checked)
  (FiniteChecks.interval_append test 3072 3328 3840
  Check012.checked
  (FiniteChecks.interval_append test 3328 3584 3840
  Check013.checked
  Check014.checked)))
  (FiniteChecks.interval_append test 3840 4608 5376
  (FiniteChecks.interval_append test 3840 4096 4608
  Check015.checked
  (FiniteChecks.interval_append test 4096 4352 4608
  Check016.checked
  Check017.checked))
  (FiniteChecks.interval_append test 4608 4864 5376
  Check018.checked
  (FiniteChecks.interval_append test 4864 5120 5376
  Check019.checked
  Check020.checked)))))
  (FiniteChecks.interval_append test 5376 8192 11008
  (FiniteChecks.interval_append test 5376 6656 8192
  (FiniteChecks.interval_append test 5376 5888 6656
  (FiniteChecks.interval_append test 5376 5632 5888
  Check021.checked
  Check022.checked)
  (FiniteChecks.interval_append test 5888 6144 6656
  Check023.checked
  (FiniteChecks.interval_append test 6144 6400 6656
  Check024.checked
  Check025.checked)))
  (FiniteChecks.interval_append test 6656 7424 8192
  (FiniteChecks.interval_append test 6656 6912 7424
  Check026.checked
  (FiniteChecks.interval_append test 6912 7168 7424
  Check027.checked
  Check028.checked))
  (FiniteChecks.interval_append test 7424 7680 8192
  Check029.checked
  (FiniteChecks.interval_append test 7680 7936 8192
  Check030.checked
  Check031.checked))))
  (FiniteChecks.interval_append test 8192 9472 11008
  (FiniteChecks.interval_append test 8192 8704 9472
  (FiniteChecks.interval_append test 8192 8448 8704
  Check032.checked
  Check033.checked)
  (FiniteChecks.interval_append test 8704 8960 9472
  Check034.checked
  (FiniteChecks.interval_append test 8960 9216 9472
  Check035.checked
  Check036.checked)))
  (FiniteChecks.interval_append test 9472 10240 11008
  (FiniteChecks.interval_append test 9472 9728 10240
  Check037.checked
  (FiniteChecks.interval_append test 9728 9984 10240
  Check038.checked
  Check039.checked))
  (FiniteChecks.interval_append test 10240 10496 11008
  Check040.checked
  (FiniteChecks.interval_append test 10496 10752 11008
  Check041.checked
  Check042.checked))))))
  (FiniteChecks.interval_append test 11008 16640 22272
  (FiniteChecks.interval_append test 11008 13824 16640
  (FiniteChecks.interval_append test 11008 12288 13824
  (FiniteChecks.interval_append test 11008 11520 12288
  (FiniteChecks.interval_append test 11008 11264 11520
  Check043.checked
  Check044.checked)
  (FiniteChecks.interval_append test 11520 11776 12288
  Check045.checked
  (FiniteChecks.interval_append test 11776 12032 12288
  Check046.checked
  Check047.checked)))
  (FiniteChecks.interval_append test 12288 13056 13824
  (FiniteChecks.interval_append test 12288 12544 13056
  Check048.checked
  (FiniteChecks.interval_append test 12544 12800 13056
  Check049.checked
  Check050.checked))
  (FiniteChecks.interval_append test 13056 13312 13824
  Check051.checked
  (FiniteChecks.interval_append test 13312 13568 13824
  Check052.checked
  Check053.checked))))
  (FiniteChecks.interval_append test 13824 15104 16640
  (FiniteChecks.interval_append test 13824 14336 15104
  (FiniteChecks.interval_append test 13824 14080 14336
  Check054.checked
  Check055.checked)
  (FiniteChecks.interval_append test 14336 14592 15104
  Check056.checked
  (FiniteChecks.interval_append test 14592 14848 15104
  Check057.checked
  Check058.checked)))
  (FiniteChecks.interval_append test 15104 15872 16640
  (FiniteChecks.interval_append test 15104 15360 15872
  Check059.checked
  (FiniteChecks.interval_append test 15360 15616 15872
  Check060.checked
  Check061.checked))
  (FiniteChecks.interval_append test 15872 16128 16640
  Check062.checked
  (FiniteChecks.interval_append test 16128 16384 16640
  Check063.checked
  Check064.checked)))))
  (FiniteChecks.interval_append test 16640 19456 22272
  (FiniteChecks.interval_append test 16640 17920 19456
  (FiniteChecks.interval_append test 16640 17152 17920
  (FiniteChecks.interval_append test 16640 16896 17152
  Check065.checked
  Check066.checked)
  (FiniteChecks.interval_append test 17152 17408 17920
  Check067.checked
  (FiniteChecks.interval_append test 17408 17664 17920
  Check068.checked
  Check069.checked)))
  (FiniteChecks.interval_append test 17920 18688 19456
  (FiniteChecks.interval_append test 17920 18176 18688
  Check070.checked
  (FiniteChecks.interval_append test 18176 18432 18688
  Check071.checked
  Check072.checked))
  (FiniteChecks.interval_append test 18688 18944 19456
  Check073.checked
  (FiniteChecks.interval_append test 18944 19200 19456
  Check074.checked
  Check075.checked))))
  (FiniteChecks.interval_append test 19456 20736 22272
  (FiniteChecks.interval_append test 19456 19968 20736
  (FiniteChecks.interval_append test 19456 19712 19968
  Check076.checked
  Check077.checked)
  (FiniteChecks.interval_append test 19968 20224 20736
  Check078.checked
  (FiniteChecks.interval_append test 20224 20480 20736
  Check079.checked
  Check080.checked)))
  (FiniteChecks.interval_append test 20736 21504 22272
  (FiniteChecks.interval_append test 20736 20992 21504
  Check081.checked
  (FiniteChecks.interval_append test 20992 21248 21504
  Check082.checked
  Check083.checked))
  (FiniteChecks.interval_append test 21504 21760 22272
  Check084.checked
  (FiniteChecks.interval_append test 21760 22016 22272
  Check085.checked
  Check086.checked)))))))
  (FiniteChecks.interval_append test 22272 33280 44310
  (FiniteChecks.interval_append test 22272 27648 33280
  (FiniteChecks.interval_append test 22272 24832 27648
  (FiniteChecks.interval_append test 22272 23552 24832
  (FiniteChecks.interval_append test 22272 22784 23552
  (FiniteChecks.interval_append test 22272 22528 22784
  Check087.checked
  Check088.checked)
  (FiniteChecks.interval_append test 22784 23040 23552
  Check089.checked
  (FiniteChecks.interval_append test 23040 23296 23552
  Check090.checked
  Check091.checked)))
  (FiniteChecks.interval_append test 23552 24064 24832
  (FiniteChecks.interval_append test 23552 23808 24064
  Check092.checked
  Check093.checked)
  (FiniteChecks.interval_append test 24064 24320 24832
  Check094.checked
  (FiniteChecks.interval_append test 24320 24576 24832
  Check095.checked
  Check096.checked))))
  (FiniteChecks.interval_append test 24832 26112 27648
  (FiniteChecks.interval_append test 24832 25344 26112
  (FiniteChecks.interval_append test 24832 25088 25344
  Check097.checked
  Check098.checked)
  (FiniteChecks.interval_append test 25344 25600 26112
  Check099.checked
  (FiniteChecks.interval_append test 25600 25856 26112
  Check100.checked
  Check101.checked)))
  (FiniteChecks.interval_append test 26112 26880 27648
  (FiniteChecks.interval_append test 26112 26368 26880
  Check102.checked
  (FiniteChecks.interval_append test 26368 26624 26880
  Check103.checked
  Check104.checked))
  (FiniteChecks.interval_append test 26880 27136 27648
  Check105.checked
  (FiniteChecks.interval_append test 27136 27392 27648
  Check106.checked
  Check107.checked)))))
  (FiniteChecks.interval_append test 27648 30464 33280
  (FiniteChecks.interval_append test 27648 28928 30464
  (FiniteChecks.interval_append test 27648 28160 28928
  (FiniteChecks.interval_append test 27648 27904 28160
  Check108.checked
  Check109.checked)
  (FiniteChecks.interval_append test 28160 28416 28928
  Check110.checked
  (FiniteChecks.interval_append test 28416 28672 28928
  Check111.checked
  Check112.checked)))
  (FiniteChecks.interval_append test 28928 29696 30464
  (FiniteChecks.interval_append test 28928 29184 29696
  Check113.checked
  (FiniteChecks.interval_append test 29184 29440 29696
  Check114.checked
  Check115.checked))
  (FiniteChecks.interval_append test 29696 29952 30464
  Check116.checked
  (FiniteChecks.interval_append test 29952 30208 30464
  Check117.checked
  Check118.checked))))
  (FiniteChecks.interval_append test 30464 31744 33280
  (FiniteChecks.interval_append test 30464 30976 31744
  (FiniteChecks.interval_append test 30464 30720 30976
  Check119.checked
  Check120.checked)
  (FiniteChecks.interval_append test 30976 31232 31744
  Check121.checked
  (FiniteChecks.interval_append test 31232 31488 31744
  Check122.checked
  Check123.checked)))
  (FiniteChecks.interval_append test 31744 32512 33280
  (FiniteChecks.interval_append test 31744 32000 32512
  Check124.checked
  (FiniteChecks.interval_append test 32000 32256 32512
  Check125.checked
  Check126.checked))
  (FiniteChecks.interval_append test 32512 32768 33280
  Check127.checked
  (FiniteChecks.interval_append test 32768 33024 33280
  Check128.checked
  Check129.checked))))))
  (FiniteChecks.interval_append test 33280 38912 44310
  (FiniteChecks.interval_append test 33280 36096 38912
  (FiniteChecks.interval_append test 33280 34560 36096
  (FiniteChecks.interval_append test 33280 33792 34560
  (FiniteChecks.interval_append test 33280 33536 33792
  Check130.checked
  Check131.checked)
  (FiniteChecks.interval_append test 33792 34048 34560
  Check132.checked
  (FiniteChecks.interval_append test 34048 34304 34560
  Check133.checked
  Check134.checked)))
  (FiniteChecks.interval_append test 34560 35328 36096
  (FiniteChecks.interval_append test 34560 34816 35328
  Check135.checked
  (FiniteChecks.interval_append test 34816 35072 35328
  Check136.checked
  Check137.checked))
  (FiniteChecks.interval_append test 35328 35584 36096
  Check138.checked
  (FiniteChecks.interval_append test 35584 35840 36096
  Check139.checked
  Check140.checked))))
  (FiniteChecks.interval_append test 36096 37376 38912
  (FiniteChecks.interval_append test 36096 36608 37376
  (FiniteChecks.interval_append test 36096 36352 36608
  Check141.checked
  Check142.checked)
  (FiniteChecks.interval_append test 36608 36864 37376
  Check143.checked
  (FiniteChecks.interval_append test 36864 37120 37376
  Check144.checked
  Check145.checked)))
  (FiniteChecks.interval_append test 37376 38144 38912
  (FiniteChecks.interval_append test 37376 37632 38144
  Check146.checked
  (FiniteChecks.interval_append test 37632 37888 38144
  Check147.checked
  Check148.checked))
  (FiniteChecks.interval_append test 38144 38400 38912
  Check149.checked
  (FiniteChecks.interval_append test 38400 38656 38912
  Check150.checked
  Check151.checked)))))
  (FiniteChecks.interval_append test 38912 41728 44310
  (FiniteChecks.interval_append test 38912 40192 41728
  (FiniteChecks.interval_append test 38912 39424 40192
  (FiniteChecks.interval_append test 38912 39168 39424
  Check152.checked
  Check153.checked)
  (FiniteChecks.interval_append test 39424 39680 40192
  Check154.checked
  (FiniteChecks.interval_append test 39680 39936 40192
  Check155.checked
  Check156.checked)))
  (FiniteChecks.interval_append test 40192 40960 41728
  (FiniteChecks.interval_append test 40192 40448 40960
  Check157.checked
  (FiniteChecks.interval_append test 40448 40704 40960
  Check158.checked
  Check159.checked))
  (FiniteChecks.interval_append test 40960 41216 41728
  Check160.checked
  (FiniteChecks.interval_append test 41216 41472 41728
  Check161.checked
  Check162.checked))))
  (FiniteChecks.interval_append test 41728 43008 44310
  (FiniteChecks.interval_append test 41728 42240 43008
  (FiniteChecks.interval_append test 41728 41984 42240
  Check163.checked
  Check164.checked)
  (FiniteChecks.interval_append test 42240 42496 43008
  Check165.checked
  (FiniteChecks.interval_append test 42496 42752 43008
  Check166.checked
  Check167.checked)))
  (FiniteChecks.interval_append test 43008 43776 44310
  (FiniteChecks.interval_append test 43008 43264 43776
  Check168.checked
  (FiniteChecks.interval_append test 43264 43520 43776
  Check169.checked
  Check170.checked))
  (FiniteChecks.interval_append test 43776 44032 44310
  Check171.checked
  (FiniteChecks.interval_append test 44032 44288 44310
  Check172.checked
  Check173.checked))))))))
theorem facts : RowFacts SharedSix0CellPool.entry rows :=
  rows_of_interval SharedSix0CellPool.entry rows checked
def graphRows : GraphCandidateCoverage.IncidenceRows 44310 10 45 :=
  SharedPoolIncidence.graphRows SharedSix0CellPool.entry rows facts
#print axioms facts
end Papers.RationalityTen.SharedSix0Incidence
