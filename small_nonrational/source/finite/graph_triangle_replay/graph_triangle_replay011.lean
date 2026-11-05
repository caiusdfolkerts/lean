module
prelude
public import SharedTriangleCountsData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open Papers.RationalityTen FiniteChecks

namespace Papers.RationalityTen.SharedTriangleCounts
theorem Check088.part11264 : Interval test 11264 11272 :=
  interval_of_check _ 11264 8 (by decide +kernel)
theorem Check088.part11272 : Interval test 11272 11280 :=
  interval_of_check _ 11272 8 (by decide +kernel)
theorem Check088.part11280 : Interval test 11280 11288 :=
  interval_of_check _ 11280 8 (by decide +kernel)
theorem Check088.part11288 : Interval test 11288 11296 :=
  interval_of_check _ 11288 8 (by decide +kernel)
theorem Check088.part11296 : Interval test 11296 11304 :=
  interval_of_check _ 11296 8 (by decide +kernel)
theorem Check088.part11304 : Interval test 11304 11312 :=
  interval_of_check _ 11304 8 (by decide +kernel)
theorem Check088.part11312 : Interval test 11312 11320 :=
  interval_of_check _ 11312 8 (by decide +kernel)
theorem Check088.part11320 : Interval test 11320 11328 :=
  interval_of_check _ 11320 8 (by decide +kernel)
theorem Check088.part11328 : Interval test 11328 11336 :=
  interval_of_check _ 11328 8 (by decide +kernel)
theorem Check088.part11336 : Interval test 11336 11344 :=
  interval_of_check _ 11336 8 (by decide +kernel)
theorem Check088.part11344 : Interval test 11344 11352 :=
  interval_of_check _ 11344 8 (by decide +kernel)
theorem Check088.part11352 : Interval test 11352 11360 :=
  interval_of_check _ 11352 8 (by decide +kernel)
theorem Check088.part11360 : Interval test 11360 11368 :=
  interval_of_check _ 11360 8 (by decide +kernel)
theorem Check088.part11368 : Interval test 11368 11376 :=
  interval_of_check _ 11368 8 (by decide +kernel)
theorem Check088.part11376 : Interval test 11376 11384 :=
  interval_of_check _ 11376 8 (by decide +kernel)
theorem Check088.part11384 : Interval test 11384 11392 :=
  interval_of_check _ 11384 8 (by decide +kernel)
theorem Check088.checked : Interval test 11264 11392 :=
  (FiniteChecks.interval_append test 11264 11328 11392
  (FiniteChecks.interval_append test 11264 11296 11328
  (FiniteChecks.interval_append test 11264 11280 11296
  (FiniteChecks.interval_append test 11264 11272 11280
  Check088.part11264
  Check088.part11272)
  (FiniteChecks.interval_append test 11280 11288 11296
  Check088.part11280
  Check088.part11288))
  (FiniteChecks.interval_append test 11296 11312 11328
  (FiniteChecks.interval_append test 11296 11304 11312
  Check088.part11296
  Check088.part11304)
  (FiniteChecks.interval_append test 11312 11320 11328
  Check088.part11312
  Check088.part11320)))
  (FiniteChecks.interval_append test 11328 11360 11392
  (FiniteChecks.interval_append test 11328 11344 11360
  (FiniteChecks.interval_append test 11328 11336 11344
  Check088.part11328
  Check088.part11336)
  (FiniteChecks.interval_append test 11344 11352 11360
  Check088.part11344
  Check088.part11352))
  (FiniteChecks.interval_append test 11360 11376 11392
  (FiniteChecks.interval_append test 11360 11368 11376
  Check088.part11360
  Check088.part11368)
  (FiniteChecks.interval_append test 11376 11384 11392
  Check088.part11376
  Check088.part11384))))
theorem Check089.part11392 : Interval test 11392 11400 :=
  interval_of_check _ 11392 8 (by decide +kernel)
theorem Check089.part11400 : Interval test 11400 11408 :=
  interval_of_check _ 11400 8 (by decide +kernel)
theorem Check089.part11408 : Interval test 11408 11416 :=
  interval_of_check _ 11408 8 (by decide +kernel)
theorem Check089.part11416 : Interval test 11416 11424 :=
  interval_of_check _ 11416 8 (by decide +kernel)
theorem Check089.part11424 : Interval test 11424 11432 :=
  interval_of_check _ 11424 8 (by decide +kernel)
theorem Check089.part11432 : Interval test 11432 11440 :=
  interval_of_check _ 11432 8 (by decide +kernel)
theorem Check089.part11440 : Interval test 11440 11448 :=
  interval_of_check _ 11440 8 (by decide +kernel)
theorem Check089.part11448 : Interval test 11448 11456 :=
  interval_of_check _ 11448 8 (by decide +kernel)
theorem Check089.part11456 : Interval test 11456 11464 :=
  interval_of_check _ 11456 8 (by decide +kernel)
theorem Check089.part11464 : Interval test 11464 11472 :=
  interval_of_check _ 11464 8 (by decide +kernel)
theorem Check089.part11472 : Interval test 11472 11480 :=
  interval_of_check _ 11472 8 (by decide +kernel)
theorem Check089.part11480 : Interval test 11480 11488 :=
  interval_of_check _ 11480 8 (by decide +kernel)
theorem Check089.part11488 : Interval test 11488 11496 :=
  interval_of_check _ 11488 8 (by decide +kernel)
theorem Check089.part11496 : Interval test 11496 11504 :=
  interval_of_check _ 11496 8 (by decide +kernel)
theorem Check089.part11504 : Interval test 11504 11512 :=
  interval_of_check _ 11504 8 (by decide +kernel)
theorem Check089.part11512 : Interval test 11512 11520 :=
  interval_of_check _ 11512 8 (by decide +kernel)
theorem Check089.checked : Interval test 11392 11520 :=
  (FiniteChecks.interval_append test 11392 11456 11520
  (FiniteChecks.interval_append test 11392 11424 11456
  (FiniteChecks.interval_append test 11392 11408 11424
  (FiniteChecks.interval_append test 11392 11400 11408
  Check089.part11392
  Check089.part11400)
  (FiniteChecks.interval_append test 11408 11416 11424
  Check089.part11408
  Check089.part11416))
  (FiniteChecks.interval_append test 11424 11440 11456
  (FiniteChecks.interval_append test 11424 11432 11440
  Check089.part11424
  Check089.part11432)
  (FiniteChecks.interval_append test 11440 11448 11456
  Check089.part11440
  Check089.part11448)))
  (FiniteChecks.interval_append test 11456 11488 11520
  (FiniteChecks.interval_append test 11456 11472 11488
  (FiniteChecks.interval_append test 11456 11464 11472
  Check089.part11456
  Check089.part11464)
  (FiniteChecks.interval_append test 11472 11480 11488
  Check089.part11472
  Check089.part11480))
  (FiniteChecks.interval_append test 11488 11504 11520
  (FiniteChecks.interval_append test 11488 11496 11504
  Check089.part11488
  Check089.part11496)
  (FiniteChecks.interval_append test 11504 11512 11520
  Check089.part11504
  Check089.part11512))))
theorem Check090.part11520 : Interval test 11520 11528 :=
  interval_of_check _ 11520 8 (by decide +kernel)
theorem Check090.part11528 : Interval test 11528 11536 :=
  interval_of_check _ 11528 8 (by decide +kernel)
theorem Check090.part11536 : Interval test 11536 11544 :=
  interval_of_check _ 11536 8 (by decide +kernel)
theorem Check090.part11544 : Interval test 11544 11552 :=
  interval_of_check _ 11544 8 (by decide +kernel)
theorem Check090.part11552 : Interval test 11552 11560 :=
  interval_of_check _ 11552 8 (by decide +kernel)
theorem Check090.part11560 : Interval test 11560 11568 :=
  interval_of_check _ 11560 8 (by decide +kernel)
theorem Check090.part11568 : Interval test 11568 11576 :=
  interval_of_check _ 11568 8 (by decide +kernel)
theorem Check090.part11576 : Interval test 11576 11584 :=
  interval_of_check _ 11576 8 (by decide +kernel)
theorem Check090.part11584 : Interval test 11584 11592 :=
  interval_of_check _ 11584 8 (by decide +kernel)
theorem Check090.part11592 : Interval test 11592 11600 :=
  interval_of_check _ 11592 8 (by decide +kernel)
theorem Check090.part11600 : Interval test 11600 11608 :=
  interval_of_check _ 11600 8 (by decide +kernel)
theorem Check090.part11608 : Interval test 11608 11616 :=
  interval_of_check _ 11608 8 (by decide +kernel)
theorem Check090.part11616 : Interval test 11616 11624 :=
  interval_of_check _ 11616 8 (by decide +kernel)
theorem Check090.part11624 : Interval test 11624 11632 :=
  interval_of_check _ 11624 8 (by decide +kernel)
theorem Check090.part11632 : Interval test 11632 11640 :=
  interval_of_check _ 11632 8 (by decide +kernel)
theorem Check090.part11640 : Interval test 11640 11648 :=
  interval_of_check _ 11640 8 (by decide +kernel)
theorem Check090.checked : Interval test 11520 11648 :=
  (FiniteChecks.interval_append test 11520 11584 11648
  (FiniteChecks.interval_append test 11520 11552 11584
  (FiniteChecks.interval_append test 11520 11536 11552
  (FiniteChecks.interval_append test 11520 11528 11536
  Check090.part11520
  Check090.part11528)
  (FiniteChecks.interval_append test 11536 11544 11552
  Check090.part11536
  Check090.part11544))
  (FiniteChecks.interval_append test 11552 11568 11584
  (FiniteChecks.interval_append test 11552 11560 11568
  Check090.part11552
  Check090.part11560)
  (FiniteChecks.interval_append test 11568 11576 11584
  Check090.part11568
  Check090.part11576)))
  (FiniteChecks.interval_append test 11584 11616 11648
  (FiniteChecks.interval_append test 11584 11600 11616
  (FiniteChecks.interval_append test 11584 11592 11600
  Check090.part11584
  Check090.part11592)
  (FiniteChecks.interval_append test 11600 11608 11616
  Check090.part11600
  Check090.part11608))
  (FiniteChecks.interval_append test 11616 11632 11648
  (FiniteChecks.interval_append test 11616 11624 11632
  Check090.part11616
  Check090.part11624)
  (FiniteChecks.interval_append test 11632 11640 11648
  Check090.part11632
  Check090.part11640))))
theorem Check091.part11648 : Interval test 11648 11656 :=
  interval_of_check _ 11648 8 (by decide +kernel)
theorem Check091.part11656 : Interval test 11656 11664 :=
  interval_of_check _ 11656 8 (by decide +kernel)
theorem Check091.part11664 : Interval test 11664 11672 :=
  interval_of_check _ 11664 8 (by decide +kernel)
theorem Check091.part11672 : Interval test 11672 11680 :=
  interval_of_check _ 11672 8 (by decide +kernel)
theorem Check091.part11680 : Interval test 11680 11688 :=
  interval_of_check _ 11680 8 (by decide +kernel)
theorem Check091.part11688 : Interval test 11688 11696 :=
  interval_of_check _ 11688 8 (by decide +kernel)
theorem Check091.part11696 : Interval test 11696 11704 :=
  interval_of_check _ 11696 8 (by decide +kernel)
theorem Check091.part11704 : Interval test 11704 11712 :=
  interval_of_check _ 11704 8 (by decide +kernel)
theorem Check091.part11712 : Interval test 11712 11720 :=
  interval_of_check _ 11712 8 (by decide +kernel)
theorem Check091.part11720 : Interval test 11720 11728 :=
  interval_of_check _ 11720 8 (by decide +kernel)
theorem Check091.part11728 : Interval test 11728 11736 :=
  interval_of_check _ 11728 8 (by decide +kernel)
theorem Check091.part11736 : Interval test 11736 11744 :=
  interval_of_check _ 11736 8 (by decide +kernel)
theorem Check091.part11744 : Interval test 11744 11752 :=
  interval_of_check _ 11744 8 (by decide +kernel)
theorem Check091.part11752 : Interval test 11752 11760 :=
  interval_of_check _ 11752 8 (by decide +kernel)
theorem Check091.part11760 : Interval test 11760 11768 :=
  interval_of_check _ 11760 8 (by decide +kernel)
theorem Check091.part11768 : Interval test 11768 11776 :=
  interval_of_check _ 11768 8 (by decide +kernel)
theorem Check091.checked : Interval test 11648 11776 :=
  (FiniteChecks.interval_append test 11648 11712 11776
  (FiniteChecks.interval_append test 11648 11680 11712
  (FiniteChecks.interval_append test 11648 11664 11680
  (FiniteChecks.interval_append test 11648 11656 11664
  Check091.part11648
  Check091.part11656)
  (FiniteChecks.interval_append test 11664 11672 11680
  Check091.part11664
  Check091.part11672))
  (FiniteChecks.interval_append test 11680 11696 11712
  (FiniteChecks.interval_append test 11680 11688 11696
  Check091.part11680
  Check091.part11688)
  (FiniteChecks.interval_append test 11696 11704 11712
  Check091.part11696
  Check091.part11704)))
  (FiniteChecks.interval_append test 11712 11744 11776
  (FiniteChecks.interval_append test 11712 11728 11744
  (FiniteChecks.interval_append test 11712 11720 11728
  Check091.part11712
  Check091.part11720)
  (FiniteChecks.interval_append test 11728 11736 11744
  Check091.part11728
  Check091.part11736))
  (FiniteChecks.interval_append test 11744 11760 11776
  (FiniteChecks.interval_append test 11744 11752 11760
  Check091.part11744
  Check091.part11752)
  (FiniteChecks.interval_append test 11760 11768 11776
  Check091.part11760
  Check091.part11768))))
theorem Check092.part11776 : Interval test 11776 11784 :=
  interval_of_check _ 11776 8 (by decide +kernel)
theorem Check092.part11784 : Interval test 11784 11792 :=
  interval_of_check _ 11784 8 (by decide +kernel)
theorem Check092.part11792 : Interval test 11792 11800 :=
  interval_of_check _ 11792 8 (by decide +kernel)
theorem Check092.part11800 : Interval test 11800 11808 :=
  interval_of_check _ 11800 8 (by decide +kernel)
theorem Check092.part11808 : Interval test 11808 11816 :=
  interval_of_check _ 11808 8 (by decide +kernel)
theorem Check092.part11816 : Interval test 11816 11824 :=
  interval_of_check _ 11816 8 (by decide +kernel)
theorem Check092.part11824 : Interval test 11824 11832 :=
  interval_of_check _ 11824 8 (by decide +kernel)
theorem Check092.part11832 : Interval test 11832 11840 :=
  interval_of_check _ 11832 8 (by decide +kernel)
theorem Check092.part11840 : Interval test 11840 11848 :=
  interval_of_check _ 11840 8 (by decide +kernel)
theorem Check092.part11848 : Interval test 11848 11856 :=
  interval_of_check _ 11848 8 (by decide +kernel)
theorem Check092.part11856 : Interval test 11856 11864 :=
  interval_of_check _ 11856 8 (by decide +kernel)
theorem Check092.part11864 : Interval test 11864 11872 :=
  interval_of_check _ 11864 8 (by decide +kernel)
theorem Check092.part11872 : Interval test 11872 11880 :=
  interval_of_check _ 11872 8 (by decide +kernel)
theorem Check092.part11880 : Interval test 11880 11888 :=
  interval_of_check _ 11880 8 (by decide +kernel)
theorem Check092.part11888 : Interval test 11888 11896 :=
  interval_of_check _ 11888 8 (by decide +kernel)
theorem Check092.part11896 : Interval test 11896 11904 :=
  interval_of_check _ 11896 8 (by decide +kernel)
theorem Check092.checked : Interval test 11776 11904 :=
  (FiniteChecks.interval_append test 11776 11840 11904
  (FiniteChecks.interval_append test 11776 11808 11840
  (FiniteChecks.interval_append test 11776 11792 11808
  (FiniteChecks.interval_append test 11776 11784 11792
  Check092.part11776
  Check092.part11784)
  (FiniteChecks.interval_append test 11792 11800 11808
  Check092.part11792
  Check092.part11800))
  (FiniteChecks.interval_append test 11808 11824 11840
  (FiniteChecks.interval_append test 11808 11816 11824
  Check092.part11808
  Check092.part11816)
  (FiniteChecks.interval_append test 11824 11832 11840
  Check092.part11824
  Check092.part11832)))
  (FiniteChecks.interval_append test 11840 11872 11904
  (FiniteChecks.interval_append test 11840 11856 11872
  (FiniteChecks.interval_append test 11840 11848 11856
  Check092.part11840
  Check092.part11848)
  (FiniteChecks.interval_append test 11856 11864 11872
  Check092.part11856
  Check092.part11864))
  (FiniteChecks.interval_append test 11872 11888 11904
  (FiniteChecks.interval_append test 11872 11880 11888
  Check092.part11872
  Check092.part11880)
  (FiniteChecks.interval_append test 11888 11896 11904
  Check092.part11888
  Check092.part11896))))
theorem Check093.part11904 : Interval test 11904 11912 :=
  interval_of_check _ 11904 8 (by decide +kernel)
theorem Check093.part11912 : Interval test 11912 11920 :=
  interval_of_check _ 11912 8 (by decide +kernel)
theorem Check093.part11920 : Interval test 11920 11928 :=
  interval_of_check _ 11920 8 (by decide +kernel)
theorem Check093.part11928 : Interval test 11928 11936 :=
  interval_of_check _ 11928 8 (by decide +kernel)
theorem Check093.part11936 : Interval test 11936 11944 :=
  interval_of_check _ 11936 8 (by decide +kernel)
theorem Check093.part11944 : Interval test 11944 11952 :=
  interval_of_check _ 11944 8 (by decide +kernel)
theorem Check093.part11952 : Interval test 11952 11960 :=
  interval_of_check _ 11952 8 (by decide +kernel)
theorem Check093.part11960 : Interval test 11960 11968 :=
  interval_of_check _ 11960 8 (by decide +kernel)
theorem Check093.part11968 : Interval test 11968 11976 :=
  interval_of_check _ 11968 8 (by decide +kernel)
theorem Check093.part11976 : Interval test 11976 11984 :=
  interval_of_check _ 11976 8 (by decide +kernel)
theorem Check093.part11984 : Interval test 11984 11992 :=
  interval_of_check _ 11984 8 (by decide +kernel)
theorem Check093.part11992 : Interval test 11992 12000 :=
  interval_of_check _ 11992 8 (by decide +kernel)
theorem Check093.part12000 : Interval test 12000 12008 :=
  interval_of_check _ 12000 8 (by decide +kernel)
theorem Check093.part12008 : Interval test 12008 12016 :=
  interval_of_check _ 12008 8 (by decide +kernel)
theorem Check093.part12016 : Interval test 12016 12024 :=
  interval_of_check _ 12016 8 (by decide +kernel)
theorem Check093.part12024 : Interval test 12024 12032 :=
  interval_of_check _ 12024 8 (by decide +kernel)
theorem Check093.checked : Interval test 11904 12032 :=
  (FiniteChecks.interval_append test 11904 11968 12032
  (FiniteChecks.interval_append test 11904 11936 11968
  (FiniteChecks.interval_append test 11904 11920 11936
  (FiniteChecks.interval_append test 11904 11912 11920
  Check093.part11904
  Check093.part11912)
  (FiniteChecks.interval_append test 11920 11928 11936
  Check093.part11920
  Check093.part11928))
  (FiniteChecks.interval_append test 11936 11952 11968
  (FiniteChecks.interval_append test 11936 11944 11952
  Check093.part11936
  Check093.part11944)
  (FiniteChecks.interval_append test 11952 11960 11968
  Check093.part11952
  Check093.part11960)))
  (FiniteChecks.interval_append test 11968 12000 12032
  (FiniteChecks.interval_append test 11968 11984 12000
  (FiniteChecks.interval_append test 11968 11976 11984
  Check093.part11968
  Check093.part11976)
  (FiniteChecks.interval_append test 11984 11992 12000
  Check093.part11984
  Check093.part11992))
  (FiniteChecks.interval_append test 12000 12016 12032
  (FiniteChecks.interval_append test 12000 12008 12016
  Check093.part12000
  Check093.part12008)
  (FiniteChecks.interval_append test 12016 12024 12032
  Check093.part12016
  Check093.part12024))))
theorem Check094.part12032 : Interval test 12032 12040 :=
  interval_of_check _ 12032 8 (by decide +kernel)
theorem Check094.part12040 : Interval test 12040 12048 :=
  interval_of_check _ 12040 8 (by decide +kernel)
theorem Check094.part12048 : Interval test 12048 12056 :=
  interval_of_check _ 12048 8 (by decide +kernel)
theorem Check094.part12056 : Interval test 12056 12064 :=
  interval_of_check _ 12056 8 (by decide +kernel)
theorem Check094.part12064 : Interval test 12064 12072 :=
  interval_of_check _ 12064 8 (by decide +kernel)
theorem Check094.part12072 : Interval test 12072 12080 :=
  interval_of_check _ 12072 8 (by decide +kernel)
theorem Check094.part12080 : Interval test 12080 12088 :=
  interval_of_check _ 12080 8 (by decide +kernel)
theorem Check094.part12088 : Interval test 12088 12096 :=
  interval_of_check _ 12088 8 (by decide +kernel)
theorem Check094.part12096 : Interval test 12096 12104 :=
  interval_of_check _ 12096 8 (by decide +kernel)
theorem Check094.part12104 : Interval test 12104 12112 :=
  interval_of_check _ 12104 8 (by decide +kernel)
theorem Check094.part12112 : Interval test 12112 12120 :=
  interval_of_check _ 12112 8 (by decide +kernel)
theorem Check094.part12120 : Interval test 12120 12128 :=
  interval_of_check _ 12120 8 (by decide +kernel)
theorem Check094.part12128 : Interval test 12128 12136 :=
  interval_of_check _ 12128 8 (by decide +kernel)
theorem Check094.part12136 : Interval test 12136 12144 :=
  interval_of_check _ 12136 8 (by decide +kernel)
theorem Check094.part12144 : Interval test 12144 12152 :=
  interval_of_check _ 12144 8 (by decide +kernel)
theorem Check094.part12152 : Interval test 12152 12160 :=
  interval_of_check _ 12152 8 (by decide +kernel)
theorem Check094.checked : Interval test 12032 12160 :=
  (FiniteChecks.interval_append test 12032 12096 12160
  (FiniteChecks.interval_append test 12032 12064 12096
  (FiniteChecks.interval_append test 12032 12048 12064
  (FiniteChecks.interval_append test 12032 12040 12048
  Check094.part12032
  Check094.part12040)
  (FiniteChecks.interval_append test 12048 12056 12064
  Check094.part12048
  Check094.part12056))
  (FiniteChecks.interval_append test 12064 12080 12096
  (FiniteChecks.interval_append test 12064 12072 12080
  Check094.part12064
  Check094.part12072)
  (FiniteChecks.interval_append test 12080 12088 12096
  Check094.part12080
  Check094.part12088)))
  (FiniteChecks.interval_append test 12096 12128 12160
  (FiniteChecks.interval_append test 12096 12112 12128
  (FiniteChecks.interval_append test 12096 12104 12112
  Check094.part12096
  Check094.part12104)
  (FiniteChecks.interval_append test 12112 12120 12128
  Check094.part12112
  Check094.part12120))
  (FiniteChecks.interval_append test 12128 12144 12160
  (FiniteChecks.interval_append test 12128 12136 12144
  Check094.part12128
  Check094.part12136)
  (FiniteChecks.interval_append test 12144 12152 12160
  Check094.part12144
  Check094.part12152))))
theorem Check095.part12160 : Interval test 12160 12168 :=
  interval_of_check _ 12160 8 (by decide +kernel)
theorem Check095.part12168 : Interval test 12168 12176 :=
  interval_of_check _ 12168 8 (by decide +kernel)
theorem Check095.part12176 : Interval test 12176 12184 :=
  interval_of_check _ 12176 8 (by decide +kernel)
theorem Check095.part12184 : Interval test 12184 12192 :=
  interval_of_check _ 12184 8 (by decide +kernel)
theorem Check095.part12192 : Interval test 12192 12200 :=
  interval_of_check _ 12192 8 (by decide +kernel)
theorem Check095.part12200 : Interval test 12200 12208 :=
  interval_of_check _ 12200 8 (by decide +kernel)
theorem Check095.part12208 : Interval test 12208 12216 :=
  interval_of_check _ 12208 8 (by decide +kernel)
theorem Check095.part12216 : Interval test 12216 12224 :=
  interval_of_check _ 12216 8 (by decide +kernel)
theorem Check095.part12224 : Interval test 12224 12232 :=
  interval_of_check _ 12224 8 (by decide +kernel)
theorem Check095.part12232 : Interval test 12232 12240 :=
  interval_of_check _ 12232 8 (by decide +kernel)
theorem Check095.part12240 : Interval test 12240 12248 :=
  interval_of_check _ 12240 8 (by decide +kernel)
theorem Check095.part12248 : Interval test 12248 12256 :=
  interval_of_check _ 12248 8 (by decide +kernel)
theorem Check095.part12256 : Interval test 12256 12264 :=
  interval_of_check _ 12256 8 (by decide +kernel)
theorem Check095.part12264 : Interval test 12264 12272 :=
  interval_of_check _ 12264 8 (by decide +kernel)
theorem Check095.part12272 : Interval test 12272 12280 :=
  interval_of_check _ 12272 8 (by decide +kernel)
theorem Check095.part12280 : Interval test 12280 12288 :=
  interval_of_check _ 12280 8 (by decide +kernel)
theorem Check095.checked : Interval test 12160 12288 :=
  (FiniteChecks.interval_append test 12160 12224 12288
  (FiniteChecks.interval_append test 12160 12192 12224
  (FiniteChecks.interval_append test 12160 12176 12192
  (FiniteChecks.interval_append test 12160 12168 12176
  Check095.part12160
  Check095.part12168)
  (FiniteChecks.interval_append test 12176 12184 12192
  Check095.part12176
  Check095.part12184))
  (FiniteChecks.interval_append test 12192 12208 12224
  (FiniteChecks.interval_append test 12192 12200 12208
  Check095.part12192
  Check095.part12200)
  (FiniteChecks.interval_append test 12208 12216 12224
  Check095.part12208
  Check095.part12216)))
  (FiniteChecks.interval_append test 12224 12256 12288
  (FiniteChecks.interval_append test 12224 12240 12256
  (FiniteChecks.interval_append test 12224 12232 12240
  Check095.part12224
  Check095.part12232)
  (FiniteChecks.interval_append test 12240 12248 12256
  Check095.part12240
  Check095.part12248))
  (FiniteChecks.interval_append test 12256 12272 12288
  (FiniteChecks.interval_append test 12256 12264 12272
  Check095.part12256
  Check095.part12264)
  (FiniteChecks.interval_append test 12272 12280 12288
  Check095.part12272
  Check095.part12280))))
end Papers.RationalityTen.SharedTriangleCounts
