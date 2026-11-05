module
prelude
public import SharedTriangleCountsData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open Papers.RationalityTen FiniteChecks

namespace Papers.RationalityTen.SharedTriangleCounts
theorem Check096.part12288 : Interval test 12288 12296 :=
  interval_of_check _ 12288 8 (by decide +kernel)
theorem Check096.part12296 : Interval test 12296 12304 :=
  interval_of_check _ 12296 8 (by decide +kernel)
theorem Check096.part12304 : Interval test 12304 12312 :=
  interval_of_check _ 12304 8 (by decide +kernel)
theorem Check096.part12312 : Interval test 12312 12320 :=
  interval_of_check _ 12312 8 (by decide +kernel)
theorem Check096.part12320 : Interval test 12320 12328 :=
  interval_of_check _ 12320 8 (by decide +kernel)
theorem Check096.part12328 : Interval test 12328 12336 :=
  interval_of_check _ 12328 8 (by decide +kernel)
theorem Check096.part12336 : Interval test 12336 12344 :=
  interval_of_check _ 12336 8 (by decide +kernel)
theorem Check096.part12344 : Interval test 12344 12352 :=
  interval_of_check _ 12344 8 (by decide +kernel)
theorem Check096.part12352 : Interval test 12352 12360 :=
  interval_of_check _ 12352 8 (by decide +kernel)
theorem Check096.part12360 : Interval test 12360 12368 :=
  interval_of_check _ 12360 8 (by decide +kernel)
theorem Check096.part12368 : Interval test 12368 12376 :=
  interval_of_check _ 12368 8 (by decide +kernel)
theorem Check096.part12376 : Interval test 12376 12384 :=
  interval_of_check _ 12376 8 (by decide +kernel)
theorem Check096.part12384 : Interval test 12384 12392 :=
  interval_of_check _ 12384 8 (by decide +kernel)
theorem Check096.part12392 : Interval test 12392 12400 :=
  interval_of_check _ 12392 8 (by decide +kernel)
theorem Check096.part12400 : Interval test 12400 12408 :=
  interval_of_check _ 12400 8 (by decide +kernel)
theorem Check096.part12408 : Interval test 12408 12416 :=
  interval_of_check _ 12408 8 (by decide +kernel)
theorem Check096.checked : Interval test 12288 12416 :=
  (FiniteChecks.interval_append test 12288 12352 12416
  (FiniteChecks.interval_append test 12288 12320 12352
  (FiniteChecks.interval_append test 12288 12304 12320
  (FiniteChecks.interval_append test 12288 12296 12304
  Check096.part12288
  Check096.part12296)
  (FiniteChecks.interval_append test 12304 12312 12320
  Check096.part12304
  Check096.part12312))
  (FiniteChecks.interval_append test 12320 12336 12352
  (FiniteChecks.interval_append test 12320 12328 12336
  Check096.part12320
  Check096.part12328)
  (FiniteChecks.interval_append test 12336 12344 12352
  Check096.part12336
  Check096.part12344)))
  (FiniteChecks.interval_append test 12352 12384 12416
  (FiniteChecks.interval_append test 12352 12368 12384
  (FiniteChecks.interval_append test 12352 12360 12368
  Check096.part12352
  Check096.part12360)
  (FiniteChecks.interval_append test 12368 12376 12384
  Check096.part12368
  Check096.part12376))
  (FiniteChecks.interval_append test 12384 12400 12416
  (FiniteChecks.interval_append test 12384 12392 12400
  Check096.part12384
  Check096.part12392)
  (FiniteChecks.interval_append test 12400 12408 12416
  Check096.part12400
  Check096.part12408))))
theorem Check097.part12416 : Interval test 12416 12424 :=
  interval_of_check _ 12416 8 (by decide +kernel)
theorem Check097.part12424 : Interval test 12424 12432 :=
  interval_of_check _ 12424 8 (by decide +kernel)
theorem Check097.part12432 : Interval test 12432 12440 :=
  interval_of_check _ 12432 8 (by decide +kernel)
theorem Check097.part12440 : Interval test 12440 12448 :=
  interval_of_check _ 12440 8 (by decide +kernel)
theorem Check097.part12448 : Interval test 12448 12456 :=
  interval_of_check _ 12448 8 (by decide +kernel)
theorem Check097.part12456 : Interval test 12456 12464 :=
  interval_of_check _ 12456 8 (by decide +kernel)
theorem Check097.part12464 : Interval test 12464 12472 :=
  interval_of_check _ 12464 8 (by decide +kernel)
theorem Check097.part12472 : Interval test 12472 12480 :=
  interval_of_check _ 12472 8 (by decide +kernel)
theorem Check097.part12480 : Interval test 12480 12488 :=
  interval_of_check _ 12480 8 (by decide +kernel)
theorem Check097.part12488 : Interval test 12488 12496 :=
  interval_of_check _ 12488 8 (by decide +kernel)
theorem Check097.part12496 : Interval test 12496 12504 :=
  interval_of_check _ 12496 8 (by decide +kernel)
theorem Check097.part12504 : Interval test 12504 12512 :=
  interval_of_check _ 12504 8 (by decide +kernel)
theorem Check097.part12512 : Interval test 12512 12520 :=
  interval_of_check _ 12512 8 (by decide +kernel)
theorem Check097.part12520 : Interval test 12520 12528 :=
  interval_of_check _ 12520 8 (by decide +kernel)
theorem Check097.part12528 : Interval test 12528 12536 :=
  interval_of_check _ 12528 8 (by decide +kernel)
theorem Check097.part12536 : Interval test 12536 12544 :=
  interval_of_check _ 12536 8 (by decide +kernel)
theorem Check097.checked : Interval test 12416 12544 :=
  (FiniteChecks.interval_append test 12416 12480 12544
  (FiniteChecks.interval_append test 12416 12448 12480
  (FiniteChecks.interval_append test 12416 12432 12448
  (FiniteChecks.interval_append test 12416 12424 12432
  Check097.part12416
  Check097.part12424)
  (FiniteChecks.interval_append test 12432 12440 12448
  Check097.part12432
  Check097.part12440))
  (FiniteChecks.interval_append test 12448 12464 12480
  (FiniteChecks.interval_append test 12448 12456 12464
  Check097.part12448
  Check097.part12456)
  (FiniteChecks.interval_append test 12464 12472 12480
  Check097.part12464
  Check097.part12472)))
  (FiniteChecks.interval_append test 12480 12512 12544
  (FiniteChecks.interval_append test 12480 12496 12512
  (FiniteChecks.interval_append test 12480 12488 12496
  Check097.part12480
  Check097.part12488)
  (FiniteChecks.interval_append test 12496 12504 12512
  Check097.part12496
  Check097.part12504))
  (FiniteChecks.interval_append test 12512 12528 12544
  (FiniteChecks.interval_append test 12512 12520 12528
  Check097.part12512
  Check097.part12520)
  (FiniteChecks.interval_append test 12528 12536 12544
  Check097.part12528
  Check097.part12536))))
theorem Check098.part12544 : Interval test 12544 12552 :=
  interval_of_check _ 12544 8 (by decide +kernel)
theorem Check098.part12552 : Interval test 12552 12560 :=
  interval_of_check _ 12552 8 (by decide +kernel)
theorem Check098.part12560 : Interval test 12560 12568 :=
  interval_of_check _ 12560 8 (by decide +kernel)
theorem Check098.part12568 : Interval test 12568 12576 :=
  interval_of_check _ 12568 8 (by decide +kernel)
theorem Check098.part12576 : Interval test 12576 12584 :=
  interval_of_check _ 12576 8 (by decide +kernel)
theorem Check098.part12584 : Interval test 12584 12592 :=
  interval_of_check _ 12584 8 (by decide +kernel)
theorem Check098.part12592 : Interval test 12592 12600 :=
  interval_of_check _ 12592 8 (by decide +kernel)
theorem Check098.part12600 : Interval test 12600 12608 :=
  interval_of_check _ 12600 8 (by decide +kernel)
theorem Check098.part12608 : Interval test 12608 12616 :=
  interval_of_check _ 12608 8 (by decide +kernel)
theorem Check098.part12616 : Interval test 12616 12624 :=
  interval_of_check _ 12616 8 (by decide +kernel)
theorem Check098.part12624 : Interval test 12624 12632 :=
  interval_of_check _ 12624 8 (by decide +kernel)
theorem Check098.part12632 : Interval test 12632 12640 :=
  interval_of_check _ 12632 8 (by decide +kernel)
theorem Check098.part12640 : Interval test 12640 12648 :=
  interval_of_check _ 12640 8 (by decide +kernel)
theorem Check098.part12648 : Interval test 12648 12656 :=
  interval_of_check _ 12648 8 (by decide +kernel)
theorem Check098.part12656 : Interval test 12656 12664 :=
  interval_of_check _ 12656 8 (by decide +kernel)
theorem Check098.part12664 : Interval test 12664 12672 :=
  interval_of_check _ 12664 8 (by decide +kernel)
theorem Check098.checked : Interval test 12544 12672 :=
  (FiniteChecks.interval_append test 12544 12608 12672
  (FiniteChecks.interval_append test 12544 12576 12608
  (FiniteChecks.interval_append test 12544 12560 12576
  (FiniteChecks.interval_append test 12544 12552 12560
  Check098.part12544
  Check098.part12552)
  (FiniteChecks.interval_append test 12560 12568 12576
  Check098.part12560
  Check098.part12568))
  (FiniteChecks.interval_append test 12576 12592 12608
  (FiniteChecks.interval_append test 12576 12584 12592
  Check098.part12576
  Check098.part12584)
  (FiniteChecks.interval_append test 12592 12600 12608
  Check098.part12592
  Check098.part12600)))
  (FiniteChecks.interval_append test 12608 12640 12672
  (FiniteChecks.interval_append test 12608 12624 12640
  (FiniteChecks.interval_append test 12608 12616 12624
  Check098.part12608
  Check098.part12616)
  (FiniteChecks.interval_append test 12624 12632 12640
  Check098.part12624
  Check098.part12632))
  (FiniteChecks.interval_append test 12640 12656 12672
  (FiniteChecks.interval_append test 12640 12648 12656
  Check098.part12640
  Check098.part12648)
  (FiniteChecks.interval_append test 12656 12664 12672
  Check098.part12656
  Check098.part12664))))
theorem Check099.part12672 : Interval test 12672 12680 :=
  interval_of_check _ 12672 8 (by decide +kernel)
theorem Check099.part12680 : Interval test 12680 12688 :=
  interval_of_check _ 12680 8 (by decide +kernel)
theorem Check099.part12688 : Interval test 12688 12696 :=
  interval_of_check _ 12688 8 (by decide +kernel)
theorem Check099.part12696 : Interval test 12696 12704 :=
  interval_of_check _ 12696 8 (by decide +kernel)
theorem Check099.part12704 : Interval test 12704 12712 :=
  interval_of_check _ 12704 8 (by decide +kernel)
theorem Check099.part12712 : Interval test 12712 12720 :=
  interval_of_check _ 12712 8 (by decide +kernel)
theorem Check099.part12720 : Interval test 12720 12728 :=
  interval_of_check _ 12720 8 (by decide +kernel)
theorem Check099.part12728 : Interval test 12728 12736 :=
  interval_of_check _ 12728 8 (by decide +kernel)
theorem Check099.part12736 : Interval test 12736 12744 :=
  interval_of_check _ 12736 8 (by decide +kernel)
theorem Check099.part12744 : Interval test 12744 12752 :=
  interval_of_check _ 12744 8 (by decide +kernel)
theorem Check099.part12752 : Interval test 12752 12760 :=
  interval_of_check _ 12752 8 (by decide +kernel)
theorem Check099.part12760 : Interval test 12760 12768 :=
  interval_of_check _ 12760 8 (by decide +kernel)
theorem Check099.part12768 : Interval test 12768 12776 :=
  interval_of_check _ 12768 8 (by decide +kernel)
theorem Check099.part12776 : Interval test 12776 12784 :=
  interval_of_check _ 12776 8 (by decide +kernel)
theorem Check099.part12784 : Interval test 12784 12792 :=
  interval_of_check _ 12784 8 (by decide +kernel)
theorem Check099.part12792 : Interval test 12792 12800 :=
  interval_of_check _ 12792 8 (by decide +kernel)
theorem Check099.checked : Interval test 12672 12800 :=
  (FiniteChecks.interval_append test 12672 12736 12800
  (FiniteChecks.interval_append test 12672 12704 12736
  (FiniteChecks.interval_append test 12672 12688 12704
  (FiniteChecks.interval_append test 12672 12680 12688
  Check099.part12672
  Check099.part12680)
  (FiniteChecks.interval_append test 12688 12696 12704
  Check099.part12688
  Check099.part12696))
  (FiniteChecks.interval_append test 12704 12720 12736
  (FiniteChecks.interval_append test 12704 12712 12720
  Check099.part12704
  Check099.part12712)
  (FiniteChecks.interval_append test 12720 12728 12736
  Check099.part12720
  Check099.part12728)))
  (FiniteChecks.interval_append test 12736 12768 12800
  (FiniteChecks.interval_append test 12736 12752 12768
  (FiniteChecks.interval_append test 12736 12744 12752
  Check099.part12736
  Check099.part12744)
  (FiniteChecks.interval_append test 12752 12760 12768
  Check099.part12752
  Check099.part12760))
  (FiniteChecks.interval_append test 12768 12784 12800
  (FiniteChecks.interval_append test 12768 12776 12784
  Check099.part12768
  Check099.part12776)
  (FiniteChecks.interval_append test 12784 12792 12800
  Check099.part12784
  Check099.part12792))))
theorem Check100.part12800 : Interval test 12800 12808 :=
  interval_of_check _ 12800 8 (by decide +kernel)
theorem Check100.part12808 : Interval test 12808 12816 :=
  interval_of_check _ 12808 8 (by decide +kernel)
theorem Check100.part12816 : Interval test 12816 12824 :=
  interval_of_check _ 12816 8 (by decide +kernel)
theorem Check100.part12824 : Interval test 12824 12832 :=
  interval_of_check _ 12824 8 (by decide +kernel)
theorem Check100.part12832 : Interval test 12832 12840 :=
  interval_of_check _ 12832 8 (by decide +kernel)
theorem Check100.part12840 : Interval test 12840 12848 :=
  interval_of_check _ 12840 8 (by decide +kernel)
theorem Check100.part12848 : Interval test 12848 12856 :=
  interval_of_check _ 12848 8 (by decide +kernel)
theorem Check100.part12856 : Interval test 12856 12864 :=
  interval_of_check _ 12856 8 (by decide +kernel)
theorem Check100.part12864 : Interval test 12864 12872 :=
  interval_of_check _ 12864 8 (by decide +kernel)
theorem Check100.part12872 : Interval test 12872 12880 :=
  interval_of_check _ 12872 8 (by decide +kernel)
theorem Check100.part12880 : Interval test 12880 12888 :=
  interval_of_check _ 12880 8 (by decide +kernel)
theorem Check100.part12888 : Interval test 12888 12896 :=
  interval_of_check _ 12888 8 (by decide +kernel)
theorem Check100.part12896 : Interval test 12896 12904 :=
  interval_of_check _ 12896 8 (by decide +kernel)
theorem Check100.part12904 : Interval test 12904 12912 :=
  interval_of_check _ 12904 8 (by decide +kernel)
theorem Check100.part12912 : Interval test 12912 12920 :=
  interval_of_check _ 12912 8 (by decide +kernel)
theorem Check100.part12920 : Interval test 12920 12928 :=
  interval_of_check _ 12920 8 (by decide +kernel)
theorem Check100.checked : Interval test 12800 12928 :=
  (FiniteChecks.interval_append test 12800 12864 12928
  (FiniteChecks.interval_append test 12800 12832 12864
  (FiniteChecks.interval_append test 12800 12816 12832
  (FiniteChecks.interval_append test 12800 12808 12816
  Check100.part12800
  Check100.part12808)
  (FiniteChecks.interval_append test 12816 12824 12832
  Check100.part12816
  Check100.part12824))
  (FiniteChecks.interval_append test 12832 12848 12864
  (FiniteChecks.interval_append test 12832 12840 12848
  Check100.part12832
  Check100.part12840)
  (FiniteChecks.interval_append test 12848 12856 12864
  Check100.part12848
  Check100.part12856)))
  (FiniteChecks.interval_append test 12864 12896 12928
  (FiniteChecks.interval_append test 12864 12880 12896
  (FiniteChecks.interval_append test 12864 12872 12880
  Check100.part12864
  Check100.part12872)
  (FiniteChecks.interval_append test 12880 12888 12896
  Check100.part12880
  Check100.part12888))
  (FiniteChecks.interval_append test 12896 12912 12928
  (FiniteChecks.interval_append test 12896 12904 12912
  Check100.part12896
  Check100.part12904)
  (FiniteChecks.interval_append test 12912 12920 12928
  Check100.part12912
  Check100.part12920))))
theorem Check101.part12928 : Interval test 12928 12936 :=
  interval_of_check _ 12928 8 (by decide +kernel)
theorem Check101.part12936 : Interval test 12936 12944 :=
  interval_of_check _ 12936 8 (by decide +kernel)
theorem Check101.part12944 : Interval test 12944 12952 :=
  interval_of_check _ 12944 8 (by decide +kernel)
theorem Check101.part12952 : Interval test 12952 12960 :=
  interval_of_check _ 12952 8 (by decide +kernel)
theorem Check101.part12960 : Interval test 12960 12968 :=
  interval_of_check _ 12960 8 (by decide +kernel)
theorem Check101.part12968 : Interval test 12968 12976 :=
  interval_of_check _ 12968 8 (by decide +kernel)
theorem Check101.part12976 : Interval test 12976 12984 :=
  interval_of_check _ 12976 8 (by decide +kernel)
theorem Check101.part12984 : Interval test 12984 12992 :=
  interval_of_check _ 12984 8 (by decide +kernel)
theorem Check101.part12992 : Interval test 12992 13000 :=
  interval_of_check _ 12992 8 (by decide +kernel)
theorem Check101.part13000 : Interval test 13000 13008 :=
  interval_of_check _ 13000 8 (by decide +kernel)
theorem Check101.part13008 : Interval test 13008 13016 :=
  interval_of_check _ 13008 8 (by decide +kernel)
theorem Check101.part13016 : Interval test 13016 13024 :=
  interval_of_check _ 13016 8 (by decide +kernel)
theorem Check101.part13024 : Interval test 13024 13032 :=
  interval_of_check _ 13024 8 (by decide +kernel)
theorem Check101.part13032 : Interval test 13032 13040 :=
  interval_of_check _ 13032 8 (by decide +kernel)
theorem Check101.part13040 : Interval test 13040 13048 :=
  interval_of_check _ 13040 8 (by decide +kernel)
theorem Check101.part13048 : Interval test 13048 13056 :=
  interval_of_check _ 13048 8 (by decide +kernel)
theorem Check101.checked : Interval test 12928 13056 :=
  (FiniteChecks.interval_append test 12928 12992 13056
  (FiniteChecks.interval_append test 12928 12960 12992
  (FiniteChecks.interval_append test 12928 12944 12960
  (FiniteChecks.interval_append test 12928 12936 12944
  Check101.part12928
  Check101.part12936)
  (FiniteChecks.interval_append test 12944 12952 12960
  Check101.part12944
  Check101.part12952))
  (FiniteChecks.interval_append test 12960 12976 12992
  (FiniteChecks.interval_append test 12960 12968 12976
  Check101.part12960
  Check101.part12968)
  (FiniteChecks.interval_append test 12976 12984 12992
  Check101.part12976
  Check101.part12984)))
  (FiniteChecks.interval_append test 12992 13024 13056
  (FiniteChecks.interval_append test 12992 13008 13024
  (FiniteChecks.interval_append test 12992 13000 13008
  Check101.part12992
  Check101.part13000)
  (FiniteChecks.interval_append test 13008 13016 13024
  Check101.part13008
  Check101.part13016))
  (FiniteChecks.interval_append test 13024 13040 13056
  (FiniteChecks.interval_append test 13024 13032 13040
  Check101.part13024
  Check101.part13032)
  (FiniteChecks.interval_append test 13040 13048 13056
  Check101.part13040
  Check101.part13048))))
theorem Check102.part13056 : Interval test 13056 13064 :=
  interval_of_check _ 13056 8 (by decide +kernel)
theorem Check102.part13064 : Interval test 13064 13072 :=
  interval_of_check _ 13064 8 (by decide +kernel)
theorem Check102.part13072 : Interval test 13072 13080 :=
  interval_of_check _ 13072 8 (by decide +kernel)
theorem Check102.part13080 : Interval test 13080 13088 :=
  interval_of_check _ 13080 8 (by decide +kernel)
theorem Check102.part13088 : Interval test 13088 13096 :=
  interval_of_check _ 13088 8 (by decide +kernel)
theorem Check102.part13096 : Interval test 13096 13104 :=
  interval_of_check _ 13096 8 (by decide +kernel)
theorem Check102.part13104 : Interval test 13104 13112 :=
  interval_of_check _ 13104 8 (by decide +kernel)
theorem Check102.part13112 : Interval test 13112 13120 :=
  interval_of_check _ 13112 8 (by decide +kernel)
theorem Check102.part13120 : Interval test 13120 13128 :=
  interval_of_check _ 13120 8 (by decide +kernel)
theorem Check102.part13128 : Interval test 13128 13136 :=
  interval_of_check _ 13128 8 (by decide +kernel)
theorem Check102.part13136 : Interval test 13136 13144 :=
  interval_of_check _ 13136 8 (by decide +kernel)
theorem Check102.part13144 : Interval test 13144 13152 :=
  interval_of_check _ 13144 8 (by decide +kernel)
theorem Check102.part13152 : Interval test 13152 13160 :=
  interval_of_check _ 13152 8 (by decide +kernel)
theorem Check102.part13160 : Interval test 13160 13168 :=
  interval_of_check _ 13160 8 (by decide +kernel)
theorem Check102.part13168 : Interval test 13168 13176 :=
  interval_of_check _ 13168 8 (by decide +kernel)
theorem Check102.part13176 : Interval test 13176 13184 :=
  interval_of_check _ 13176 8 (by decide +kernel)
theorem Check102.checked : Interval test 13056 13184 :=
  (FiniteChecks.interval_append test 13056 13120 13184
  (FiniteChecks.interval_append test 13056 13088 13120
  (FiniteChecks.interval_append test 13056 13072 13088
  (FiniteChecks.interval_append test 13056 13064 13072
  Check102.part13056
  Check102.part13064)
  (FiniteChecks.interval_append test 13072 13080 13088
  Check102.part13072
  Check102.part13080))
  (FiniteChecks.interval_append test 13088 13104 13120
  (FiniteChecks.interval_append test 13088 13096 13104
  Check102.part13088
  Check102.part13096)
  (FiniteChecks.interval_append test 13104 13112 13120
  Check102.part13104
  Check102.part13112)))
  (FiniteChecks.interval_append test 13120 13152 13184
  (FiniteChecks.interval_append test 13120 13136 13152
  (FiniteChecks.interval_append test 13120 13128 13136
  Check102.part13120
  Check102.part13128)
  (FiniteChecks.interval_append test 13136 13144 13152
  Check102.part13136
  Check102.part13144))
  (FiniteChecks.interval_append test 13152 13168 13184
  (FiniteChecks.interval_append test 13152 13160 13168
  Check102.part13152
  Check102.part13160)
  (FiniteChecks.interval_append test 13168 13176 13184
  Check102.part13168
  Check102.part13176))))
theorem Check103.part13184 : Interval test 13184 13192 :=
  interval_of_check _ 13184 8 (by decide +kernel)
theorem Check103.part13192 : Interval test 13192 13200 :=
  interval_of_check _ 13192 8 (by decide +kernel)
theorem Check103.part13200 : Interval test 13200 13208 :=
  interval_of_check _ 13200 8 (by decide +kernel)
theorem Check103.part13208 : Interval test 13208 13216 :=
  interval_of_check _ 13208 8 (by decide +kernel)
theorem Check103.part13216 : Interval test 13216 13224 :=
  interval_of_check _ 13216 8 (by decide +kernel)
theorem Check103.part13224 : Interval test 13224 13232 :=
  interval_of_check _ 13224 8 (by decide +kernel)
theorem Check103.part13232 : Interval test 13232 13240 :=
  interval_of_check _ 13232 8 (by decide +kernel)
theorem Check103.part13240 : Interval test 13240 13248 :=
  interval_of_check _ 13240 8 (by decide +kernel)
theorem Check103.part13248 : Interval test 13248 13256 :=
  interval_of_check _ 13248 8 (by decide +kernel)
theorem Check103.part13256 : Interval test 13256 13264 :=
  interval_of_check _ 13256 8 (by decide +kernel)
theorem Check103.part13264 : Interval test 13264 13272 :=
  interval_of_check _ 13264 8 (by decide +kernel)
theorem Check103.part13272 : Interval test 13272 13280 :=
  interval_of_check _ 13272 8 (by decide +kernel)
theorem Check103.part13280 : Interval test 13280 13288 :=
  interval_of_check _ 13280 8 (by decide +kernel)
theorem Check103.part13288 : Interval test 13288 13296 :=
  interval_of_check _ 13288 8 (by decide +kernel)
theorem Check103.part13296 : Interval test 13296 13304 :=
  interval_of_check _ 13296 8 (by decide +kernel)
theorem Check103.part13304 : Interval test 13304 13309 :=
  interval_of_check _ 13304 5 (by decide +kernel)
theorem Check103.checked : Interval test 13184 13309 :=
  (FiniteChecks.interval_append test 13184 13248 13309
  (FiniteChecks.interval_append test 13184 13216 13248
  (FiniteChecks.interval_append test 13184 13200 13216
  (FiniteChecks.interval_append test 13184 13192 13200
  Check103.part13184
  Check103.part13192)
  (FiniteChecks.interval_append test 13200 13208 13216
  Check103.part13200
  Check103.part13208))
  (FiniteChecks.interval_append test 13216 13232 13248
  (FiniteChecks.interval_append test 13216 13224 13232
  Check103.part13216
  Check103.part13224)
  (FiniteChecks.interval_append test 13232 13240 13248
  Check103.part13232
  Check103.part13240)))
  (FiniteChecks.interval_append test 13248 13280 13309
  (FiniteChecks.interval_append test 13248 13264 13280
  (FiniteChecks.interval_append test 13248 13256 13264
  Check103.part13248
  Check103.part13256)
  (FiniteChecks.interval_append test 13264 13272 13280
  Check103.part13264
  Check103.part13272))
  (FiniteChecks.interval_append test 13280 13296 13309
  (FiniteChecks.interval_append test 13280 13288 13296
  Check103.part13280
  Check103.part13288)
  (FiniteChecks.interval_append test 13296 13304 13309
  Check103.part13296
  Check103.part13304))))
end Papers.RationalityTen.SharedTriangleCounts
