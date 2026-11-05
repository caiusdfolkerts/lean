module
prelude
public import SharedTriangleCountsData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open Papers.RationalityTen FiniteChecks

namespace Papers.RationalityTen.SharedTriangleCounts
theorem Check048.part6144 : Interval test 6144 6152 :=
  interval_of_check _ 6144 8 (by decide +kernel)
theorem Check048.part6152 : Interval test 6152 6160 :=
  interval_of_check _ 6152 8 (by decide +kernel)
theorem Check048.part6160 : Interval test 6160 6168 :=
  interval_of_check _ 6160 8 (by decide +kernel)
theorem Check048.part6168 : Interval test 6168 6176 :=
  interval_of_check _ 6168 8 (by decide +kernel)
theorem Check048.part6176 : Interval test 6176 6184 :=
  interval_of_check _ 6176 8 (by decide +kernel)
theorem Check048.part6184 : Interval test 6184 6192 :=
  interval_of_check _ 6184 8 (by decide +kernel)
theorem Check048.part6192 : Interval test 6192 6200 :=
  interval_of_check _ 6192 8 (by decide +kernel)
theorem Check048.part6200 : Interval test 6200 6208 :=
  interval_of_check _ 6200 8 (by decide +kernel)
theorem Check048.part6208 : Interval test 6208 6216 :=
  interval_of_check _ 6208 8 (by decide +kernel)
theorem Check048.part6216 : Interval test 6216 6224 :=
  interval_of_check _ 6216 8 (by decide +kernel)
theorem Check048.part6224 : Interval test 6224 6232 :=
  interval_of_check _ 6224 8 (by decide +kernel)
theorem Check048.part6232 : Interval test 6232 6240 :=
  interval_of_check _ 6232 8 (by decide +kernel)
theorem Check048.part6240 : Interval test 6240 6248 :=
  interval_of_check _ 6240 8 (by decide +kernel)
theorem Check048.part6248 : Interval test 6248 6256 :=
  interval_of_check _ 6248 8 (by decide +kernel)
theorem Check048.part6256 : Interval test 6256 6264 :=
  interval_of_check _ 6256 8 (by decide +kernel)
theorem Check048.part6264 : Interval test 6264 6272 :=
  interval_of_check _ 6264 8 (by decide +kernel)
theorem Check048.checked : Interval test 6144 6272 :=
  (FiniteChecks.interval_append test 6144 6208 6272
  (FiniteChecks.interval_append test 6144 6176 6208
  (FiniteChecks.interval_append test 6144 6160 6176
  (FiniteChecks.interval_append test 6144 6152 6160
  Check048.part6144
  Check048.part6152)
  (FiniteChecks.interval_append test 6160 6168 6176
  Check048.part6160
  Check048.part6168))
  (FiniteChecks.interval_append test 6176 6192 6208
  (FiniteChecks.interval_append test 6176 6184 6192
  Check048.part6176
  Check048.part6184)
  (FiniteChecks.interval_append test 6192 6200 6208
  Check048.part6192
  Check048.part6200)))
  (FiniteChecks.interval_append test 6208 6240 6272
  (FiniteChecks.interval_append test 6208 6224 6240
  (FiniteChecks.interval_append test 6208 6216 6224
  Check048.part6208
  Check048.part6216)
  (FiniteChecks.interval_append test 6224 6232 6240
  Check048.part6224
  Check048.part6232))
  (FiniteChecks.interval_append test 6240 6256 6272
  (FiniteChecks.interval_append test 6240 6248 6256
  Check048.part6240
  Check048.part6248)
  (FiniteChecks.interval_append test 6256 6264 6272
  Check048.part6256
  Check048.part6264))))
theorem Check049.part6272 : Interval test 6272 6280 :=
  interval_of_check _ 6272 8 (by decide +kernel)
theorem Check049.part6280 : Interval test 6280 6288 :=
  interval_of_check _ 6280 8 (by decide +kernel)
theorem Check049.part6288 : Interval test 6288 6296 :=
  interval_of_check _ 6288 8 (by decide +kernel)
theorem Check049.part6296 : Interval test 6296 6304 :=
  interval_of_check _ 6296 8 (by decide +kernel)
theorem Check049.part6304 : Interval test 6304 6312 :=
  interval_of_check _ 6304 8 (by decide +kernel)
theorem Check049.part6312 : Interval test 6312 6320 :=
  interval_of_check _ 6312 8 (by decide +kernel)
theorem Check049.part6320 : Interval test 6320 6328 :=
  interval_of_check _ 6320 8 (by decide +kernel)
theorem Check049.part6328 : Interval test 6328 6336 :=
  interval_of_check _ 6328 8 (by decide +kernel)
theorem Check049.part6336 : Interval test 6336 6344 :=
  interval_of_check _ 6336 8 (by decide +kernel)
theorem Check049.part6344 : Interval test 6344 6352 :=
  interval_of_check _ 6344 8 (by decide +kernel)
theorem Check049.part6352 : Interval test 6352 6360 :=
  interval_of_check _ 6352 8 (by decide +kernel)
theorem Check049.part6360 : Interval test 6360 6368 :=
  interval_of_check _ 6360 8 (by decide +kernel)
theorem Check049.part6368 : Interval test 6368 6376 :=
  interval_of_check _ 6368 8 (by decide +kernel)
theorem Check049.part6376 : Interval test 6376 6384 :=
  interval_of_check _ 6376 8 (by decide +kernel)
theorem Check049.part6384 : Interval test 6384 6392 :=
  interval_of_check _ 6384 8 (by decide +kernel)
theorem Check049.part6392 : Interval test 6392 6400 :=
  interval_of_check _ 6392 8 (by decide +kernel)
theorem Check049.checked : Interval test 6272 6400 :=
  (FiniteChecks.interval_append test 6272 6336 6400
  (FiniteChecks.interval_append test 6272 6304 6336
  (FiniteChecks.interval_append test 6272 6288 6304
  (FiniteChecks.interval_append test 6272 6280 6288
  Check049.part6272
  Check049.part6280)
  (FiniteChecks.interval_append test 6288 6296 6304
  Check049.part6288
  Check049.part6296))
  (FiniteChecks.interval_append test 6304 6320 6336
  (FiniteChecks.interval_append test 6304 6312 6320
  Check049.part6304
  Check049.part6312)
  (FiniteChecks.interval_append test 6320 6328 6336
  Check049.part6320
  Check049.part6328)))
  (FiniteChecks.interval_append test 6336 6368 6400
  (FiniteChecks.interval_append test 6336 6352 6368
  (FiniteChecks.interval_append test 6336 6344 6352
  Check049.part6336
  Check049.part6344)
  (FiniteChecks.interval_append test 6352 6360 6368
  Check049.part6352
  Check049.part6360))
  (FiniteChecks.interval_append test 6368 6384 6400
  (FiniteChecks.interval_append test 6368 6376 6384
  Check049.part6368
  Check049.part6376)
  (FiniteChecks.interval_append test 6384 6392 6400
  Check049.part6384
  Check049.part6392))))
theorem Check050.part6400 : Interval test 6400 6408 :=
  interval_of_check _ 6400 8 (by decide +kernel)
theorem Check050.part6408 : Interval test 6408 6416 :=
  interval_of_check _ 6408 8 (by decide +kernel)
theorem Check050.part6416 : Interval test 6416 6424 :=
  interval_of_check _ 6416 8 (by decide +kernel)
theorem Check050.part6424 : Interval test 6424 6432 :=
  interval_of_check _ 6424 8 (by decide +kernel)
theorem Check050.part6432 : Interval test 6432 6440 :=
  interval_of_check _ 6432 8 (by decide +kernel)
theorem Check050.part6440 : Interval test 6440 6448 :=
  interval_of_check _ 6440 8 (by decide +kernel)
theorem Check050.part6448 : Interval test 6448 6456 :=
  interval_of_check _ 6448 8 (by decide +kernel)
theorem Check050.part6456 : Interval test 6456 6464 :=
  interval_of_check _ 6456 8 (by decide +kernel)
theorem Check050.part6464 : Interval test 6464 6472 :=
  interval_of_check _ 6464 8 (by decide +kernel)
theorem Check050.part6472 : Interval test 6472 6480 :=
  interval_of_check _ 6472 8 (by decide +kernel)
theorem Check050.part6480 : Interval test 6480 6488 :=
  interval_of_check _ 6480 8 (by decide +kernel)
theorem Check050.part6488 : Interval test 6488 6496 :=
  interval_of_check _ 6488 8 (by decide +kernel)
theorem Check050.part6496 : Interval test 6496 6504 :=
  interval_of_check _ 6496 8 (by decide +kernel)
theorem Check050.part6504 : Interval test 6504 6512 :=
  interval_of_check _ 6504 8 (by decide +kernel)
theorem Check050.part6512 : Interval test 6512 6520 :=
  interval_of_check _ 6512 8 (by decide +kernel)
theorem Check050.part6520 : Interval test 6520 6528 :=
  interval_of_check _ 6520 8 (by decide +kernel)
theorem Check050.checked : Interval test 6400 6528 :=
  (FiniteChecks.interval_append test 6400 6464 6528
  (FiniteChecks.interval_append test 6400 6432 6464
  (FiniteChecks.interval_append test 6400 6416 6432
  (FiniteChecks.interval_append test 6400 6408 6416
  Check050.part6400
  Check050.part6408)
  (FiniteChecks.interval_append test 6416 6424 6432
  Check050.part6416
  Check050.part6424))
  (FiniteChecks.interval_append test 6432 6448 6464
  (FiniteChecks.interval_append test 6432 6440 6448
  Check050.part6432
  Check050.part6440)
  (FiniteChecks.interval_append test 6448 6456 6464
  Check050.part6448
  Check050.part6456)))
  (FiniteChecks.interval_append test 6464 6496 6528
  (FiniteChecks.interval_append test 6464 6480 6496
  (FiniteChecks.interval_append test 6464 6472 6480
  Check050.part6464
  Check050.part6472)
  (FiniteChecks.interval_append test 6480 6488 6496
  Check050.part6480
  Check050.part6488))
  (FiniteChecks.interval_append test 6496 6512 6528
  (FiniteChecks.interval_append test 6496 6504 6512
  Check050.part6496
  Check050.part6504)
  (FiniteChecks.interval_append test 6512 6520 6528
  Check050.part6512
  Check050.part6520))))
theorem Check051.part6528 : Interval test 6528 6536 :=
  interval_of_check _ 6528 8 (by decide +kernel)
theorem Check051.part6536 : Interval test 6536 6544 :=
  interval_of_check _ 6536 8 (by decide +kernel)
theorem Check051.part6544 : Interval test 6544 6552 :=
  interval_of_check _ 6544 8 (by decide +kernel)
theorem Check051.part6552 : Interval test 6552 6560 :=
  interval_of_check _ 6552 8 (by decide +kernel)
theorem Check051.part6560 : Interval test 6560 6568 :=
  interval_of_check _ 6560 8 (by decide +kernel)
theorem Check051.part6568 : Interval test 6568 6576 :=
  interval_of_check _ 6568 8 (by decide +kernel)
theorem Check051.part6576 : Interval test 6576 6584 :=
  interval_of_check _ 6576 8 (by decide +kernel)
theorem Check051.part6584 : Interval test 6584 6592 :=
  interval_of_check _ 6584 8 (by decide +kernel)
theorem Check051.part6592 : Interval test 6592 6600 :=
  interval_of_check _ 6592 8 (by decide +kernel)
theorem Check051.part6600 : Interval test 6600 6608 :=
  interval_of_check _ 6600 8 (by decide +kernel)
theorem Check051.part6608 : Interval test 6608 6616 :=
  interval_of_check _ 6608 8 (by decide +kernel)
theorem Check051.part6616 : Interval test 6616 6624 :=
  interval_of_check _ 6616 8 (by decide +kernel)
theorem Check051.part6624 : Interval test 6624 6632 :=
  interval_of_check _ 6624 8 (by decide +kernel)
theorem Check051.part6632 : Interval test 6632 6640 :=
  interval_of_check _ 6632 8 (by decide +kernel)
theorem Check051.part6640 : Interval test 6640 6648 :=
  interval_of_check _ 6640 8 (by decide +kernel)
theorem Check051.part6648 : Interval test 6648 6656 :=
  interval_of_check _ 6648 8 (by decide +kernel)
theorem Check051.checked : Interval test 6528 6656 :=
  (FiniteChecks.interval_append test 6528 6592 6656
  (FiniteChecks.interval_append test 6528 6560 6592
  (FiniteChecks.interval_append test 6528 6544 6560
  (FiniteChecks.interval_append test 6528 6536 6544
  Check051.part6528
  Check051.part6536)
  (FiniteChecks.interval_append test 6544 6552 6560
  Check051.part6544
  Check051.part6552))
  (FiniteChecks.interval_append test 6560 6576 6592
  (FiniteChecks.interval_append test 6560 6568 6576
  Check051.part6560
  Check051.part6568)
  (FiniteChecks.interval_append test 6576 6584 6592
  Check051.part6576
  Check051.part6584)))
  (FiniteChecks.interval_append test 6592 6624 6656
  (FiniteChecks.interval_append test 6592 6608 6624
  (FiniteChecks.interval_append test 6592 6600 6608
  Check051.part6592
  Check051.part6600)
  (FiniteChecks.interval_append test 6608 6616 6624
  Check051.part6608
  Check051.part6616))
  (FiniteChecks.interval_append test 6624 6640 6656
  (FiniteChecks.interval_append test 6624 6632 6640
  Check051.part6624
  Check051.part6632)
  (FiniteChecks.interval_append test 6640 6648 6656
  Check051.part6640
  Check051.part6648))))
theorem Check052.part6656 : Interval test 6656 6664 :=
  interval_of_check _ 6656 8 (by decide +kernel)
theorem Check052.part6664 : Interval test 6664 6672 :=
  interval_of_check _ 6664 8 (by decide +kernel)
theorem Check052.part6672 : Interval test 6672 6680 :=
  interval_of_check _ 6672 8 (by decide +kernel)
theorem Check052.part6680 : Interval test 6680 6688 :=
  interval_of_check _ 6680 8 (by decide +kernel)
theorem Check052.part6688 : Interval test 6688 6696 :=
  interval_of_check _ 6688 8 (by decide +kernel)
theorem Check052.part6696 : Interval test 6696 6704 :=
  interval_of_check _ 6696 8 (by decide +kernel)
theorem Check052.part6704 : Interval test 6704 6712 :=
  interval_of_check _ 6704 8 (by decide +kernel)
theorem Check052.part6712 : Interval test 6712 6720 :=
  interval_of_check _ 6712 8 (by decide +kernel)
theorem Check052.part6720 : Interval test 6720 6728 :=
  interval_of_check _ 6720 8 (by decide +kernel)
theorem Check052.part6728 : Interval test 6728 6736 :=
  interval_of_check _ 6728 8 (by decide +kernel)
theorem Check052.part6736 : Interval test 6736 6744 :=
  interval_of_check _ 6736 8 (by decide +kernel)
theorem Check052.part6744 : Interval test 6744 6752 :=
  interval_of_check _ 6744 8 (by decide +kernel)
theorem Check052.part6752 : Interval test 6752 6760 :=
  interval_of_check _ 6752 8 (by decide +kernel)
theorem Check052.part6760 : Interval test 6760 6768 :=
  interval_of_check _ 6760 8 (by decide +kernel)
theorem Check052.part6768 : Interval test 6768 6776 :=
  interval_of_check _ 6768 8 (by decide +kernel)
theorem Check052.part6776 : Interval test 6776 6784 :=
  interval_of_check _ 6776 8 (by decide +kernel)
theorem Check052.checked : Interval test 6656 6784 :=
  (FiniteChecks.interval_append test 6656 6720 6784
  (FiniteChecks.interval_append test 6656 6688 6720
  (FiniteChecks.interval_append test 6656 6672 6688
  (FiniteChecks.interval_append test 6656 6664 6672
  Check052.part6656
  Check052.part6664)
  (FiniteChecks.interval_append test 6672 6680 6688
  Check052.part6672
  Check052.part6680))
  (FiniteChecks.interval_append test 6688 6704 6720
  (FiniteChecks.interval_append test 6688 6696 6704
  Check052.part6688
  Check052.part6696)
  (FiniteChecks.interval_append test 6704 6712 6720
  Check052.part6704
  Check052.part6712)))
  (FiniteChecks.interval_append test 6720 6752 6784
  (FiniteChecks.interval_append test 6720 6736 6752
  (FiniteChecks.interval_append test 6720 6728 6736
  Check052.part6720
  Check052.part6728)
  (FiniteChecks.interval_append test 6736 6744 6752
  Check052.part6736
  Check052.part6744))
  (FiniteChecks.interval_append test 6752 6768 6784
  (FiniteChecks.interval_append test 6752 6760 6768
  Check052.part6752
  Check052.part6760)
  (FiniteChecks.interval_append test 6768 6776 6784
  Check052.part6768
  Check052.part6776))))
theorem Check053.part6784 : Interval test 6784 6792 :=
  interval_of_check _ 6784 8 (by decide +kernel)
theorem Check053.part6792 : Interval test 6792 6800 :=
  interval_of_check _ 6792 8 (by decide +kernel)
theorem Check053.part6800 : Interval test 6800 6808 :=
  interval_of_check _ 6800 8 (by decide +kernel)
theorem Check053.part6808 : Interval test 6808 6816 :=
  interval_of_check _ 6808 8 (by decide +kernel)
theorem Check053.part6816 : Interval test 6816 6824 :=
  interval_of_check _ 6816 8 (by decide +kernel)
theorem Check053.part6824 : Interval test 6824 6832 :=
  interval_of_check _ 6824 8 (by decide +kernel)
theorem Check053.part6832 : Interval test 6832 6840 :=
  interval_of_check _ 6832 8 (by decide +kernel)
theorem Check053.part6840 : Interval test 6840 6848 :=
  interval_of_check _ 6840 8 (by decide +kernel)
theorem Check053.part6848 : Interval test 6848 6856 :=
  interval_of_check _ 6848 8 (by decide +kernel)
theorem Check053.part6856 : Interval test 6856 6864 :=
  interval_of_check _ 6856 8 (by decide +kernel)
theorem Check053.part6864 : Interval test 6864 6872 :=
  interval_of_check _ 6864 8 (by decide +kernel)
theorem Check053.part6872 : Interval test 6872 6880 :=
  interval_of_check _ 6872 8 (by decide +kernel)
theorem Check053.part6880 : Interval test 6880 6888 :=
  interval_of_check _ 6880 8 (by decide +kernel)
theorem Check053.part6888 : Interval test 6888 6896 :=
  interval_of_check _ 6888 8 (by decide +kernel)
theorem Check053.part6896 : Interval test 6896 6904 :=
  interval_of_check _ 6896 8 (by decide +kernel)
theorem Check053.part6904 : Interval test 6904 6912 :=
  interval_of_check _ 6904 8 (by decide +kernel)
theorem Check053.checked : Interval test 6784 6912 :=
  (FiniteChecks.interval_append test 6784 6848 6912
  (FiniteChecks.interval_append test 6784 6816 6848
  (FiniteChecks.interval_append test 6784 6800 6816
  (FiniteChecks.interval_append test 6784 6792 6800
  Check053.part6784
  Check053.part6792)
  (FiniteChecks.interval_append test 6800 6808 6816
  Check053.part6800
  Check053.part6808))
  (FiniteChecks.interval_append test 6816 6832 6848
  (FiniteChecks.interval_append test 6816 6824 6832
  Check053.part6816
  Check053.part6824)
  (FiniteChecks.interval_append test 6832 6840 6848
  Check053.part6832
  Check053.part6840)))
  (FiniteChecks.interval_append test 6848 6880 6912
  (FiniteChecks.interval_append test 6848 6864 6880
  (FiniteChecks.interval_append test 6848 6856 6864
  Check053.part6848
  Check053.part6856)
  (FiniteChecks.interval_append test 6864 6872 6880
  Check053.part6864
  Check053.part6872))
  (FiniteChecks.interval_append test 6880 6896 6912
  (FiniteChecks.interval_append test 6880 6888 6896
  Check053.part6880
  Check053.part6888)
  (FiniteChecks.interval_append test 6896 6904 6912
  Check053.part6896
  Check053.part6904))))
theorem Check054.part6912 : Interval test 6912 6920 :=
  interval_of_check _ 6912 8 (by decide +kernel)
theorem Check054.part6920 : Interval test 6920 6928 :=
  interval_of_check _ 6920 8 (by decide +kernel)
theorem Check054.part6928 : Interval test 6928 6936 :=
  interval_of_check _ 6928 8 (by decide +kernel)
theorem Check054.part6936 : Interval test 6936 6944 :=
  interval_of_check _ 6936 8 (by decide +kernel)
theorem Check054.part6944 : Interval test 6944 6952 :=
  interval_of_check _ 6944 8 (by decide +kernel)
theorem Check054.part6952 : Interval test 6952 6960 :=
  interval_of_check _ 6952 8 (by decide +kernel)
theorem Check054.part6960 : Interval test 6960 6968 :=
  interval_of_check _ 6960 8 (by decide +kernel)
theorem Check054.part6968 : Interval test 6968 6976 :=
  interval_of_check _ 6968 8 (by decide +kernel)
theorem Check054.part6976 : Interval test 6976 6984 :=
  interval_of_check _ 6976 8 (by decide +kernel)
theorem Check054.part6984 : Interval test 6984 6992 :=
  interval_of_check _ 6984 8 (by decide +kernel)
theorem Check054.part6992 : Interval test 6992 7000 :=
  interval_of_check _ 6992 8 (by decide +kernel)
theorem Check054.part7000 : Interval test 7000 7008 :=
  interval_of_check _ 7000 8 (by decide +kernel)
theorem Check054.part7008 : Interval test 7008 7016 :=
  interval_of_check _ 7008 8 (by decide +kernel)
theorem Check054.part7016 : Interval test 7016 7024 :=
  interval_of_check _ 7016 8 (by decide +kernel)
theorem Check054.part7024 : Interval test 7024 7032 :=
  interval_of_check _ 7024 8 (by decide +kernel)
theorem Check054.part7032 : Interval test 7032 7040 :=
  interval_of_check _ 7032 8 (by decide +kernel)
theorem Check054.checked : Interval test 6912 7040 :=
  (FiniteChecks.interval_append test 6912 6976 7040
  (FiniteChecks.interval_append test 6912 6944 6976
  (FiniteChecks.interval_append test 6912 6928 6944
  (FiniteChecks.interval_append test 6912 6920 6928
  Check054.part6912
  Check054.part6920)
  (FiniteChecks.interval_append test 6928 6936 6944
  Check054.part6928
  Check054.part6936))
  (FiniteChecks.interval_append test 6944 6960 6976
  (FiniteChecks.interval_append test 6944 6952 6960
  Check054.part6944
  Check054.part6952)
  (FiniteChecks.interval_append test 6960 6968 6976
  Check054.part6960
  Check054.part6968)))
  (FiniteChecks.interval_append test 6976 7008 7040
  (FiniteChecks.interval_append test 6976 6992 7008
  (FiniteChecks.interval_append test 6976 6984 6992
  Check054.part6976
  Check054.part6984)
  (FiniteChecks.interval_append test 6992 7000 7008
  Check054.part6992
  Check054.part7000))
  (FiniteChecks.interval_append test 7008 7024 7040
  (FiniteChecks.interval_append test 7008 7016 7024
  Check054.part7008
  Check054.part7016)
  (FiniteChecks.interval_append test 7024 7032 7040
  Check054.part7024
  Check054.part7032))))
theorem Check055.part7040 : Interval test 7040 7048 :=
  interval_of_check _ 7040 8 (by decide +kernel)
theorem Check055.part7048 : Interval test 7048 7056 :=
  interval_of_check _ 7048 8 (by decide +kernel)
theorem Check055.part7056 : Interval test 7056 7064 :=
  interval_of_check _ 7056 8 (by decide +kernel)
theorem Check055.part7064 : Interval test 7064 7072 :=
  interval_of_check _ 7064 8 (by decide +kernel)
theorem Check055.part7072 : Interval test 7072 7080 :=
  interval_of_check _ 7072 8 (by decide +kernel)
theorem Check055.part7080 : Interval test 7080 7088 :=
  interval_of_check _ 7080 8 (by decide +kernel)
theorem Check055.part7088 : Interval test 7088 7096 :=
  interval_of_check _ 7088 8 (by decide +kernel)
theorem Check055.part7096 : Interval test 7096 7104 :=
  interval_of_check _ 7096 8 (by decide +kernel)
theorem Check055.part7104 : Interval test 7104 7112 :=
  interval_of_check _ 7104 8 (by decide +kernel)
theorem Check055.part7112 : Interval test 7112 7120 :=
  interval_of_check _ 7112 8 (by decide +kernel)
theorem Check055.part7120 : Interval test 7120 7128 :=
  interval_of_check _ 7120 8 (by decide +kernel)
theorem Check055.part7128 : Interval test 7128 7136 :=
  interval_of_check _ 7128 8 (by decide +kernel)
theorem Check055.part7136 : Interval test 7136 7144 :=
  interval_of_check _ 7136 8 (by decide +kernel)
theorem Check055.part7144 : Interval test 7144 7152 :=
  interval_of_check _ 7144 8 (by decide +kernel)
theorem Check055.part7152 : Interval test 7152 7160 :=
  interval_of_check _ 7152 8 (by decide +kernel)
theorem Check055.part7160 : Interval test 7160 7168 :=
  interval_of_check _ 7160 8 (by decide +kernel)
theorem Check055.checked : Interval test 7040 7168 :=
  (FiniteChecks.interval_append test 7040 7104 7168
  (FiniteChecks.interval_append test 7040 7072 7104
  (FiniteChecks.interval_append test 7040 7056 7072
  (FiniteChecks.interval_append test 7040 7048 7056
  Check055.part7040
  Check055.part7048)
  (FiniteChecks.interval_append test 7056 7064 7072
  Check055.part7056
  Check055.part7064))
  (FiniteChecks.interval_append test 7072 7088 7104
  (FiniteChecks.interval_append test 7072 7080 7088
  Check055.part7072
  Check055.part7080)
  (FiniteChecks.interval_append test 7088 7096 7104
  Check055.part7088
  Check055.part7096)))
  (FiniteChecks.interval_append test 7104 7136 7168
  (FiniteChecks.interval_append test 7104 7120 7136
  (FiniteChecks.interval_append test 7104 7112 7120
  Check055.part7104
  Check055.part7112)
  (FiniteChecks.interval_append test 7120 7128 7136
  Check055.part7120
  Check055.part7128))
  (FiniteChecks.interval_append test 7136 7152 7168
  (FiniteChecks.interval_append test 7136 7144 7152
  Check055.part7136
  Check055.part7144)
  (FiniteChecks.interval_append test 7152 7160 7168
  Check055.part7152
  Check055.part7160))))
end Papers.RationalityTen.SharedTriangleCounts
