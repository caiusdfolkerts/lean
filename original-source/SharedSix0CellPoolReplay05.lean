module
prelude
public import SharedSix0CellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check100.part12800 : Interval test 12800 12816 :=
  interval_of_check _ 12800 16 (by decide +kernel)
theorem Check100.part12816 : Interval test 12816 12832 :=
  interval_of_check _ 12816 16 (by decide +kernel)
theorem Check100.part12832 : Interval test 12832 12848 :=
  interval_of_check _ 12832 16 (by decide +kernel)
theorem Check100.part12848 : Interval test 12848 12864 :=
  interval_of_check _ 12848 16 (by decide +kernel)
theorem Check100.part12864 : Interval test 12864 12880 :=
  interval_of_check _ 12864 16 (by decide +kernel)
theorem Check100.part12880 : Interval test 12880 12896 :=
  interval_of_check _ 12880 16 (by decide +kernel)
theorem Check100.part12896 : Interval test 12896 12912 :=
  interval_of_check _ 12896 16 (by decide +kernel)
theorem Check100.part12912 : Interval test 12912 12928 :=
  interval_of_check _ 12912 16 (by decide +kernel)
theorem Check100.checked : Interval test 12800 12928 :=
  (FiniteChecks.interval_append test 12800 12864 12928
  (FiniteChecks.interval_append test 12800 12832 12864
  (FiniteChecks.interval_append test 12800 12816 12832
  Check100.part12800
  Check100.part12816)
  (FiniteChecks.interval_append test 12832 12848 12864
  Check100.part12832
  Check100.part12848))
  (FiniteChecks.interval_append test 12864 12896 12928
  (FiniteChecks.interval_append test 12864 12880 12896
  Check100.part12864
  Check100.part12880)
  (FiniteChecks.interval_append test 12896 12912 12928
  Check100.part12896
  Check100.part12912)))
#print axioms Check100.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check101.part12928 : Interval test 12928 12944 :=
  interval_of_check _ 12928 16 (by decide +kernel)
theorem Check101.part12944 : Interval test 12944 12960 :=
  interval_of_check _ 12944 16 (by decide +kernel)
theorem Check101.part12960 : Interval test 12960 12976 :=
  interval_of_check _ 12960 16 (by decide +kernel)
theorem Check101.part12976 : Interval test 12976 12992 :=
  interval_of_check _ 12976 16 (by decide +kernel)
theorem Check101.part12992 : Interval test 12992 13008 :=
  interval_of_check _ 12992 16 (by decide +kernel)
theorem Check101.part13008 : Interval test 13008 13024 :=
  interval_of_check _ 13008 16 (by decide +kernel)
theorem Check101.part13024 : Interval test 13024 13040 :=
  interval_of_check _ 13024 16 (by decide +kernel)
theorem Check101.part13040 : Interval test 13040 13056 :=
  interval_of_check _ 13040 16 (by decide +kernel)
theorem Check101.checked : Interval test 12928 13056 :=
  (FiniteChecks.interval_append test 12928 12992 13056
  (FiniteChecks.interval_append test 12928 12960 12992
  (FiniteChecks.interval_append test 12928 12944 12960
  Check101.part12928
  Check101.part12944)
  (FiniteChecks.interval_append test 12960 12976 12992
  Check101.part12960
  Check101.part12976))
  (FiniteChecks.interval_append test 12992 13024 13056
  (FiniteChecks.interval_append test 12992 13008 13024
  Check101.part12992
  Check101.part13008)
  (FiniteChecks.interval_append test 13024 13040 13056
  Check101.part13024
  Check101.part13040)))
#print axioms Check101.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check102.part13056 : Interval test 13056 13072 :=
  interval_of_check _ 13056 16 (by decide +kernel)
theorem Check102.part13072 : Interval test 13072 13088 :=
  interval_of_check _ 13072 16 (by decide +kernel)
theorem Check102.part13088 : Interval test 13088 13104 :=
  interval_of_check _ 13088 16 (by decide +kernel)
theorem Check102.part13104 : Interval test 13104 13120 :=
  interval_of_check _ 13104 16 (by decide +kernel)
theorem Check102.part13120 : Interval test 13120 13136 :=
  interval_of_check _ 13120 16 (by decide +kernel)
theorem Check102.part13136 : Interval test 13136 13152 :=
  interval_of_check _ 13136 16 (by decide +kernel)
theorem Check102.part13152 : Interval test 13152 13168 :=
  interval_of_check _ 13152 16 (by decide +kernel)
theorem Check102.part13168 : Interval test 13168 13184 :=
  interval_of_check _ 13168 16 (by decide +kernel)
theorem Check102.checked : Interval test 13056 13184 :=
  (FiniteChecks.interval_append test 13056 13120 13184
  (FiniteChecks.interval_append test 13056 13088 13120
  (FiniteChecks.interval_append test 13056 13072 13088
  Check102.part13056
  Check102.part13072)
  (FiniteChecks.interval_append test 13088 13104 13120
  Check102.part13088
  Check102.part13104))
  (FiniteChecks.interval_append test 13120 13152 13184
  (FiniteChecks.interval_append test 13120 13136 13152
  Check102.part13120
  Check102.part13136)
  (FiniteChecks.interval_append test 13152 13168 13184
  Check102.part13152
  Check102.part13168)))
#print axioms Check102.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check103.part13184 : Interval test 13184 13200 :=
  interval_of_check _ 13184 16 (by decide +kernel)
theorem Check103.part13200 : Interval test 13200 13216 :=
  interval_of_check _ 13200 16 (by decide +kernel)
theorem Check103.part13216 : Interval test 13216 13232 :=
  interval_of_check _ 13216 16 (by decide +kernel)
theorem Check103.part13232 : Interval test 13232 13248 :=
  interval_of_check _ 13232 16 (by decide +kernel)
theorem Check103.part13248 : Interval test 13248 13264 :=
  interval_of_check _ 13248 16 (by decide +kernel)
theorem Check103.part13264 : Interval test 13264 13280 :=
  interval_of_check _ 13264 16 (by decide +kernel)
theorem Check103.part13280 : Interval test 13280 13296 :=
  interval_of_check _ 13280 16 (by decide +kernel)
theorem Check103.part13296 : Interval test 13296 13312 :=
  interval_of_check _ 13296 16 (by decide +kernel)
theorem Check103.checked : Interval test 13184 13312 :=
  (FiniteChecks.interval_append test 13184 13248 13312
  (FiniteChecks.interval_append test 13184 13216 13248
  (FiniteChecks.interval_append test 13184 13200 13216
  Check103.part13184
  Check103.part13200)
  (FiniteChecks.interval_append test 13216 13232 13248
  Check103.part13216
  Check103.part13232))
  (FiniteChecks.interval_append test 13248 13280 13312
  (FiniteChecks.interval_append test 13248 13264 13280
  Check103.part13248
  Check103.part13264)
  (FiniteChecks.interval_append test 13280 13296 13312
  Check103.part13280
  Check103.part13296)))
#print axioms Check103.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check104.part13312 : Interval test 13312 13328 :=
  interval_of_check _ 13312 16 (by decide +kernel)
theorem Check104.part13328 : Interval test 13328 13344 :=
  interval_of_check _ 13328 16 (by decide +kernel)
theorem Check104.part13344 : Interval test 13344 13360 :=
  interval_of_check _ 13344 16 (by decide +kernel)
theorem Check104.part13360 : Interval test 13360 13376 :=
  interval_of_check _ 13360 16 (by decide +kernel)
theorem Check104.part13376 : Interval test 13376 13392 :=
  interval_of_check _ 13376 16 (by decide +kernel)
theorem Check104.part13392 : Interval test 13392 13408 :=
  interval_of_check _ 13392 16 (by decide +kernel)
theorem Check104.part13408 : Interval test 13408 13424 :=
  interval_of_check _ 13408 16 (by decide +kernel)
theorem Check104.part13424 : Interval test 13424 13440 :=
  interval_of_check _ 13424 16 (by decide +kernel)
theorem Check104.checked : Interval test 13312 13440 :=
  (FiniteChecks.interval_append test 13312 13376 13440
  (FiniteChecks.interval_append test 13312 13344 13376
  (FiniteChecks.interval_append test 13312 13328 13344
  Check104.part13312
  Check104.part13328)
  (FiniteChecks.interval_append test 13344 13360 13376
  Check104.part13344
  Check104.part13360))
  (FiniteChecks.interval_append test 13376 13408 13440
  (FiniteChecks.interval_append test 13376 13392 13408
  Check104.part13376
  Check104.part13392)
  (FiniteChecks.interval_append test 13408 13424 13440
  Check104.part13408
  Check104.part13424)))
#print axioms Check104.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check105.part13440 : Interval test 13440 13456 :=
  interval_of_check _ 13440 16 (by decide +kernel)
theorem Check105.part13456 : Interval test 13456 13472 :=
  interval_of_check _ 13456 16 (by decide +kernel)
theorem Check105.part13472 : Interval test 13472 13488 :=
  interval_of_check _ 13472 16 (by decide +kernel)
theorem Check105.part13488 : Interval test 13488 13504 :=
  interval_of_check _ 13488 16 (by decide +kernel)
theorem Check105.part13504 : Interval test 13504 13520 :=
  interval_of_check _ 13504 16 (by decide +kernel)
theorem Check105.part13520 : Interval test 13520 13536 :=
  interval_of_check _ 13520 16 (by decide +kernel)
theorem Check105.part13536 : Interval test 13536 13552 :=
  interval_of_check _ 13536 16 (by decide +kernel)
theorem Check105.part13552 : Interval test 13552 13568 :=
  interval_of_check _ 13552 16 (by decide +kernel)
theorem Check105.checked : Interval test 13440 13568 :=
  (FiniteChecks.interval_append test 13440 13504 13568
  (FiniteChecks.interval_append test 13440 13472 13504
  (FiniteChecks.interval_append test 13440 13456 13472
  Check105.part13440
  Check105.part13456)
  (FiniteChecks.interval_append test 13472 13488 13504
  Check105.part13472
  Check105.part13488))
  (FiniteChecks.interval_append test 13504 13536 13568
  (FiniteChecks.interval_append test 13504 13520 13536
  Check105.part13504
  Check105.part13520)
  (FiniteChecks.interval_append test 13536 13552 13568
  Check105.part13536
  Check105.part13552)))
#print axioms Check105.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check106.part13568 : Interval test 13568 13584 :=
  interval_of_check _ 13568 16 (by decide +kernel)
theorem Check106.part13584 : Interval test 13584 13600 :=
  interval_of_check _ 13584 16 (by decide +kernel)
theorem Check106.part13600 : Interval test 13600 13616 :=
  interval_of_check _ 13600 16 (by decide +kernel)
theorem Check106.part13616 : Interval test 13616 13632 :=
  interval_of_check _ 13616 16 (by decide +kernel)
theorem Check106.part13632 : Interval test 13632 13648 :=
  interval_of_check _ 13632 16 (by decide +kernel)
theorem Check106.part13648 : Interval test 13648 13664 :=
  interval_of_check _ 13648 16 (by decide +kernel)
theorem Check106.part13664 : Interval test 13664 13680 :=
  interval_of_check _ 13664 16 (by decide +kernel)
theorem Check106.part13680 : Interval test 13680 13696 :=
  interval_of_check _ 13680 16 (by decide +kernel)
theorem Check106.checked : Interval test 13568 13696 :=
  (FiniteChecks.interval_append test 13568 13632 13696
  (FiniteChecks.interval_append test 13568 13600 13632
  (FiniteChecks.interval_append test 13568 13584 13600
  Check106.part13568
  Check106.part13584)
  (FiniteChecks.interval_append test 13600 13616 13632
  Check106.part13600
  Check106.part13616))
  (FiniteChecks.interval_append test 13632 13664 13696
  (FiniteChecks.interval_append test 13632 13648 13664
  Check106.part13632
  Check106.part13648)
  (FiniteChecks.interval_append test 13664 13680 13696
  Check106.part13664
  Check106.part13680)))
#print axioms Check106.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check107.part13696 : Interval test 13696 13712 :=
  interval_of_check _ 13696 16 (by decide +kernel)
theorem Check107.part13712 : Interval test 13712 13728 :=
  interval_of_check _ 13712 16 (by decide +kernel)
theorem Check107.part13728 : Interval test 13728 13744 :=
  interval_of_check _ 13728 16 (by decide +kernel)
theorem Check107.part13744 : Interval test 13744 13760 :=
  interval_of_check _ 13744 16 (by decide +kernel)
theorem Check107.part13760 : Interval test 13760 13776 :=
  interval_of_check _ 13760 16 (by decide +kernel)
theorem Check107.part13776 : Interval test 13776 13792 :=
  interval_of_check _ 13776 16 (by decide +kernel)
theorem Check107.part13792 : Interval test 13792 13808 :=
  interval_of_check _ 13792 16 (by decide +kernel)
theorem Check107.part13808 : Interval test 13808 13824 :=
  interval_of_check _ 13808 16 (by decide +kernel)
theorem Check107.checked : Interval test 13696 13824 :=
  (FiniteChecks.interval_append test 13696 13760 13824
  (FiniteChecks.interval_append test 13696 13728 13760
  (FiniteChecks.interval_append test 13696 13712 13728
  Check107.part13696
  Check107.part13712)
  (FiniteChecks.interval_append test 13728 13744 13760
  Check107.part13728
  Check107.part13744))
  (FiniteChecks.interval_append test 13760 13792 13824
  (FiniteChecks.interval_append test 13760 13776 13792
  Check107.part13760
  Check107.part13776)
  (FiniteChecks.interval_append test 13792 13808 13824
  Check107.part13792
  Check107.part13808)))
#print axioms Check107.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check108.part13824 : Interval test 13824 13840 :=
  interval_of_check _ 13824 16 (by decide +kernel)
theorem Check108.part13840 : Interval test 13840 13856 :=
  interval_of_check _ 13840 16 (by decide +kernel)
theorem Check108.part13856 : Interval test 13856 13872 :=
  interval_of_check _ 13856 16 (by decide +kernel)
theorem Check108.part13872 : Interval test 13872 13888 :=
  interval_of_check _ 13872 16 (by decide +kernel)
theorem Check108.part13888 : Interval test 13888 13904 :=
  interval_of_check _ 13888 16 (by decide +kernel)
theorem Check108.part13904 : Interval test 13904 13920 :=
  interval_of_check _ 13904 16 (by decide +kernel)
theorem Check108.part13920 : Interval test 13920 13936 :=
  interval_of_check _ 13920 16 (by decide +kernel)
theorem Check108.part13936 : Interval test 13936 13952 :=
  interval_of_check _ 13936 16 (by decide +kernel)
theorem Check108.checked : Interval test 13824 13952 :=
  (FiniteChecks.interval_append test 13824 13888 13952
  (FiniteChecks.interval_append test 13824 13856 13888
  (FiniteChecks.interval_append test 13824 13840 13856
  Check108.part13824
  Check108.part13840)
  (FiniteChecks.interval_append test 13856 13872 13888
  Check108.part13856
  Check108.part13872))
  (FiniteChecks.interval_append test 13888 13920 13952
  (FiniteChecks.interval_append test 13888 13904 13920
  Check108.part13888
  Check108.part13904)
  (FiniteChecks.interval_append test 13920 13936 13952
  Check108.part13920
  Check108.part13936)))
#print axioms Check108.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check109.part13952 : Interval test 13952 13968 :=
  interval_of_check _ 13952 16 (by decide +kernel)
theorem Check109.part13968 : Interval test 13968 13984 :=
  interval_of_check _ 13968 16 (by decide +kernel)
theorem Check109.part13984 : Interval test 13984 14000 :=
  interval_of_check _ 13984 16 (by decide +kernel)
theorem Check109.part14000 : Interval test 14000 14016 :=
  interval_of_check _ 14000 16 (by decide +kernel)
theorem Check109.part14016 : Interval test 14016 14032 :=
  interval_of_check _ 14016 16 (by decide +kernel)
theorem Check109.part14032 : Interval test 14032 14048 :=
  interval_of_check _ 14032 16 (by decide +kernel)
theorem Check109.part14048 : Interval test 14048 14064 :=
  interval_of_check _ 14048 16 (by decide +kernel)
theorem Check109.part14064 : Interval test 14064 14080 :=
  interval_of_check _ 14064 16 (by decide +kernel)
theorem Check109.checked : Interval test 13952 14080 :=
  (FiniteChecks.interval_append test 13952 14016 14080
  (FiniteChecks.interval_append test 13952 13984 14016
  (FiniteChecks.interval_append test 13952 13968 13984
  Check109.part13952
  Check109.part13968)
  (FiniteChecks.interval_append test 13984 14000 14016
  Check109.part13984
  Check109.part14000))
  (FiniteChecks.interval_append test 14016 14048 14080
  (FiniteChecks.interval_append test 14016 14032 14048
  Check109.part14016
  Check109.part14032)
  (FiniteChecks.interval_append test 14048 14064 14080
  Check109.part14048
  Check109.part14064)))
#print axioms Check109.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check110.part14080 : Interval test 14080 14096 :=
  interval_of_check _ 14080 16 (by decide +kernel)
theorem Check110.part14096 : Interval test 14096 14112 :=
  interval_of_check _ 14096 16 (by decide +kernel)
theorem Check110.part14112 : Interval test 14112 14128 :=
  interval_of_check _ 14112 16 (by decide +kernel)
theorem Check110.part14128 : Interval test 14128 14144 :=
  interval_of_check _ 14128 16 (by decide +kernel)
theorem Check110.part14144 : Interval test 14144 14160 :=
  interval_of_check _ 14144 16 (by decide +kernel)
theorem Check110.part14160 : Interval test 14160 14176 :=
  interval_of_check _ 14160 16 (by decide +kernel)
theorem Check110.part14176 : Interval test 14176 14192 :=
  interval_of_check _ 14176 16 (by decide +kernel)
theorem Check110.part14192 : Interval test 14192 14208 :=
  interval_of_check _ 14192 16 (by decide +kernel)
theorem Check110.checked : Interval test 14080 14208 :=
  (FiniteChecks.interval_append test 14080 14144 14208
  (FiniteChecks.interval_append test 14080 14112 14144
  (FiniteChecks.interval_append test 14080 14096 14112
  Check110.part14080
  Check110.part14096)
  (FiniteChecks.interval_append test 14112 14128 14144
  Check110.part14112
  Check110.part14128))
  (FiniteChecks.interval_append test 14144 14176 14208
  (FiniteChecks.interval_append test 14144 14160 14176
  Check110.part14144
  Check110.part14160)
  (FiniteChecks.interval_append test 14176 14192 14208
  Check110.part14176
  Check110.part14192)))
#print axioms Check110.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check111.part14208 : Interval test 14208 14224 :=
  interval_of_check _ 14208 16 (by decide +kernel)
theorem Check111.part14224 : Interval test 14224 14240 :=
  interval_of_check _ 14224 16 (by decide +kernel)
theorem Check111.part14240 : Interval test 14240 14256 :=
  interval_of_check _ 14240 16 (by decide +kernel)
theorem Check111.part14256 : Interval test 14256 14272 :=
  interval_of_check _ 14256 16 (by decide +kernel)
theorem Check111.part14272 : Interval test 14272 14288 :=
  interval_of_check _ 14272 16 (by decide +kernel)
theorem Check111.part14288 : Interval test 14288 14304 :=
  interval_of_check _ 14288 16 (by decide +kernel)
theorem Check111.part14304 : Interval test 14304 14320 :=
  interval_of_check _ 14304 16 (by decide +kernel)
theorem Check111.part14320 : Interval test 14320 14336 :=
  interval_of_check _ 14320 16 (by decide +kernel)
theorem Check111.checked : Interval test 14208 14336 :=
  (FiniteChecks.interval_append test 14208 14272 14336
  (FiniteChecks.interval_append test 14208 14240 14272
  (FiniteChecks.interval_append test 14208 14224 14240
  Check111.part14208
  Check111.part14224)
  (FiniteChecks.interval_append test 14240 14256 14272
  Check111.part14240
  Check111.part14256))
  (FiniteChecks.interval_append test 14272 14304 14336
  (FiniteChecks.interval_append test 14272 14288 14304
  Check111.part14272
  Check111.part14288)
  (FiniteChecks.interval_append test 14304 14320 14336
  Check111.part14304
  Check111.part14320)))
#print axioms Check111.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check112.part14336 : Interval test 14336 14352 :=
  interval_of_check _ 14336 16 (by decide +kernel)
theorem Check112.part14352 : Interval test 14352 14368 :=
  interval_of_check _ 14352 16 (by decide +kernel)
theorem Check112.part14368 : Interval test 14368 14384 :=
  interval_of_check _ 14368 16 (by decide +kernel)
theorem Check112.part14384 : Interval test 14384 14400 :=
  interval_of_check _ 14384 16 (by decide +kernel)
theorem Check112.part14400 : Interval test 14400 14416 :=
  interval_of_check _ 14400 16 (by decide +kernel)
theorem Check112.part14416 : Interval test 14416 14432 :=
  interval_of_check _ 14416 16 (by decide +kernel)
theorem Check112.part14432 : Interval test 14432 14448 :=
  interval_of_check _ 14432 16 (by decide +kernel)
theorem Check112.part14448 : Interval test 14448 14464 :=
  interval_of_check _ 14448 16 (by decide +kernel)
theorem Check112.checked : Interval test 14336 14464 :=
  (FiniteChecks.interval_append test 14336 14400 14464
  (FiniteChecks.interval_append test 14336 14368 14400
  (FiniteChecks.interval_append test 14336 14352 14368
  Check112.part14336
  Check112.part14352)
  (FiniteChecks.interval_append test 14368 14384 14400
  Check112.part14368
  Check112.part14384))
  (FiniteChecks.interval_append test 14400 14432 14464
  (FiniteChecks.interval_append test 14400 14416 14432
  Check112.part14400
  Check112.part14416)
  (FiniteChecks.interval_append test 14432 14448 14464
  Check112.part14432
  Check112.part14448)))
#print axioms Check112.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check113.part14464 : Interval test 14464 14480 :=
  interval_of_check _ 14464 16 (by decide +kernel)
theorem Check113.part14480 : Interval test 14480 14496 :=
  interval_of_check _ 14480 16 (by decide +kernel)
theorem Check113.part14496 : Interval test 14496 14512 :=
  interval_of_check _ 14496 16 (by decide +kernel)
theorem Check113.part14512 : Interval test 14512 14528 :=
  interval_of_check _ 14512 16 (by decide +kernel)
theorem Check113.part14528 : Interval test 14528 14544 :=
  interval_of_check _ 14528 16 (by decide +kernel)
theorem Check113.part14544 : Interval test 14544 14560 :=
  interval_of_check _ 14544 16 (by decide +kernel)
theorem Check113.part14560 : Interval test 14560 14576 :=
  interval_of_check _ 14560 16 (by decide +kernel)
theorem Check113.part14576 : Interval test 14576 14592 :=
  interval_of_check _ 14576 16 (by decide +kernel)
theorem Check113.checked : Interval test 14464 14592 :=
  (FiniteChecks.interval_append test 14464 14528 14592
  (FiniteChecks.interval_append test 14464 14496 14528
  (FiniteChecks.interval_append test 14464 14480 14496
  Check113.part14464
  Check113.part14480)
  (FiniteChecks.interval_append test 14496 14512 14528
  Check113.part14496
  Check113.part14512))
  (FiniteChecks.interval_append test 14528 14560 14592
  (FiniteChecks.interval_append test 14528 14544 14560
  Check113.part14528
  Check113.part14544)
  (FiniteChecks.interval_append test 14560 14576 14592
  Check113.part14560
  Check113.part14576)))
#print axioms Check113.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check114.part14592 : Interval test 14592 14608 :=
  interval_of_check _ 14592 16 (by decide +kernel)
theorem Check114.part14608 : Interval test 14608 14624 :=
  interval_of_check _ 14608 16 (by decide +kernel)
theorem Check114.part14624 : Interval test 14624 14640 :=
  interval_of_check _ 14624 16 (by decide +kernel)
theorem Check114.part14640 : Interval test 14640 14656 :=
  interval_of_check _ 14640 16 (by decide +kernel)
theorem Check114.part14656 : Interval test 14656 14672 :=
  interval_of_check _ 14656 16 (by decide +kernel)
theorem Check114.part14672 : Interval test 14672 14688 :=
  interval_of_check _ 14672 16 (by decide +kernel)
theorem Check114.part14688 : Interval test 14688 14704 :=
  interval_of_check _ 14688 16 (by decide +kernel)
theorem Check114.part14704 : Interval test 14704 14720 :=
  interval_of_check _ 14704 16 (by decide +kernel)
theorem Check114.checked : Interval test 14592 14720 :=
  (FiniteChecks.interval_append test 14592 14656 14720
  (FiniteChecks.interval_append test 14592 14624 14656
  (FiniteChecks.interval_append test 14592 14608 14624
  Check114.part14592
  Check114.part14608)
  (FiniteChecks.interval_append test 14624 14640 14656
  Check114.part14624
  Check114.part14640))
  (FiniteChecks.interval_append test 14656 14688 14720
  (FiniteChecks.interval_append test 14656 14672 14688
  Check114.part14656
  Check114.part14672)
  (FiniteChecks.interval_append test 14688 14704 14720
  Check114.part14688
  Check114.part14704)))
#print axioms Check114.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check115.part14720 : Interval test 14720 14736 :=
  interval_of_check _ 14720 16 (by decide +kernel)
theorem Check115.part14736 : Interval test 14736 14752 :=
  interval_of_check _ 14736 16 (by decide +kernel)
theorem Check115.part14752 : Interval test 14752 14768 :=
  interval_of_check _ 14752 16 (by decide +kernel)
theorem Check115.part14768 : Interval test 14768 14784 :=
  interval_of_check _ 14768 16 (by decide +kernel)
theorem Check115.part14784 : Interval test 14784 14800 :=
  interval_of_check _ 14784 16 (by decide +kernel)
theorem Check115.part14800 : Interval test 14800 14816 :=
  interval_of_check _ 14800 16 (by decide +kernel)
theorem Check115.part14816 : Interval test 14816 14832 :=
  interval_of_check _ 14816 16 (by decide +kernel)
theorem Check115.part14832 : Interval test 14832 14848 :=
  interval_of_check _ 14832 16 (by decide +kernel)
theorem Check115.checked : Interval test 14720 14848 :=
  (FiniteChecks.interval_append test 14720 14784 14848
  (FiniteChecks.interval_append test 14720 14752 14784
  (FiniteChecks.interval_append test 14720 14736 14752
  Check115.part14720
  Check115.part14736)
  (FiniteChecks.interval_append test 14752 14768 14784
  Check115.part14752
  Check115.part14768))
  (FiniteChecks.interval_append test 14784 14816 14848
  (FiniteChecks.interval_append test 14784 14800 14816
  Check115.part14784
  Check115.part14800)
  (FiniteChecks.interval_append test 14816 14832 14848
  Check115.part14816
  Check115.part14832)))
#print axioms Check115.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check116.part14848 : Interval test 14848 14864 :=
  interval_of_check _ 14848 16 (by decide +kernel)
theorem Check116.part14864 : Interval test 14864 14880 :=
  interval_of_check _ 14864 16 (by decide +kernel)
theorem Check116.part14880 : Interval test 14880 14896 :=
  interval_of_check _ 14880 16 (by decide +kernel)
theorem Check116.part14896 : Interval test 14896 14912 :=
  interval_of_check _ 14896 16 (by decide +kernel)
theorem Check116.part14912 : Interval test 14912 14928 :=
  interval_of_check _ 14912 16 (by decide +kernel)
theorem Check116.part14928 : Interval test 14928 14944 :=
  interval_of_check _ 14928 16 (by decide +kernel)
theorem Check116.part14944 : Interval test 14944 14960 :=
  interval_of_check _ 14944 16 (by decide +kernel)
theorem Check116.part14960 : Interval test 14960 14976 :=
  interval_of_check _ 14960 16 (by decide +kernel)
theorem Check116.checked : Interval test 14848 14976 :=
  (FiniteChecks.interval_append test 14848 14912 14976
  (FiniteChecks.interval_append test 14848 14880 14912
  (FiniteChecks.interval_append test 14848 14864 14880
  Check116.part14848
  Check116.part14864)
  (FiniteChecks.interval_append test 14880 14896 14912
  Check116.part14880
  Check116.part14896))
  (FiniteChecks.interval_append test 14912 14944 14976
  (FiniteChecks.interval_append test 14912 14928 14944
  Check116.part14912
  Check116.part14928)
  (FiniteChecks.interval_append test 14944 14960 14976
  Check116.part14944
  Check116.part14960)))
#print axioms Check116.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check117.part14976 : Interval test 14976 14992 :=
  interval_of_check _ 14976 16 (by decide +kernel)
theorem Check117.part14992 : Interval test 14992 15008 :=
  interval_of_check _ 14992 16 (by decide +kernel)
theorem Check117.part15008 : Interval test 15008 15024 :=
  interval_of_check _ 15008 16 (by decide +kernel)
theorem Check117.part15024 : Interval test 15024 15040 :=
  interval_of_check _ 15024 16 (by decide +kernel)
theorem Check117.part15040 : Interval test 15040 15056 :=
  interval_of_check _ 15040 16 (by decide +kernel)
theorem Check117.part15056 : Interval test 15056 15072 :=
  interval_of_check _ 15056 16 (by decide +kernel)
theorem Check117.part15072 : Interval test 15072 15088 :=
  interval_of_check _ 15072 16 (by decide +kernel)
theorem Check117.part15088 : Interval test 15088 15104 :=
  interval_of_check _ 15088 16 (by decide +kernel)
theorem Check117.checked : Interval test 14976 15104 :=
  (FiniteChecks.interval_append test 14976 15040 15104
  (FiniteChecks.interval_append test 14976 15008 15040
  (FiniteChecks.interval_append test 14976 14992 15008
  Check117.part14976
  Check117.part14992)
  (FiniteChecks.interval_append test 15008 15024 15040
  Check117.part15008
  Check117.part15024))
  (FiniteChecks.interval_append test 15040 15072 15104
  (FiniteChecks.interval_append test 15040 15056 15072
  Check117.part15040
  Check117.part15056)
  (FiniteChecks.interval_append test 15072 15088 15104
  Check117.part15072
  Check117.part15088)))
#print axioms Check117.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check118.part15104 : Interval test 15104 15120 :=
  interval_of_check _ 15104 16 (by decide +kernel)
theorem Check118.part15120 : Interval test 15120 15136 :=
  interval_of_check _ 15120 16 (by decide +kernel)
theorem Check118.part15136 : Interval test 15136 15152 :=
  interval_of_check _ 15136 16 (by decide +kernel)
theorem Check118.part15152 : Interval test 15152 15168 :=
  interval_of_check _ 15152 16 (by decide +kernel)
theorem Check118.part15168 : Interval test 15168 15184 :=
  interval_of_check _ 15168 16 (by decide +kernel)
theorem Check118.part15184 : Interval test 15184 15200 :=
  interval_of_check _ 15184 16 (by decide +kernel)
theorem Check118.part15200 : Interval test 15200 15216 :=
  interval_of_check _ 15200 16 (by decide +kernel)
theorem Check118.part15216 : Interval test 15216 15232 :=
  interval_of_check _ 15216 16 (by decide +kernel)
theorem Check118.checked : Interval test 15104 15232 :=
  (FiniteChecks.interval_append test 15104 15168 15232
  (FiniteChecks.interval_append test 15104 15136 15168
  (FiniteChecks.interval_append test 15104 15120 15136
  Check118.part15104
  Check118.part15120)
  (FiniteChecks.interval_append test 15136 15152 15168
  Check118.part15136
  Check118.part15152))
  (FiniteChecks.interval_append test 15168 15200 15232
  (FiniteChecks.interval_append test 15168 15184 15200
  Check118.part15168
  Check118.part15184)
  (FiniteChecks.interval_append test 15200 15216 15232
  Check118.part15200
  Check118.part15216)))
#print axioms Check118.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check119.part15232 : Interval test 15232 15248 :=
  interval_of_check _ 15232 16 (by decide +kernel)
theorem Check119.part15248 : Interval test 15248 15264 :=
  interval_of_check _ 15248 16 (by decide +kernel)
theorem Check119.part15264 : Interval test 15264 15280 :=
  interval_of_check _ 15264 16 (by decide +kernel)
theorem Check119.part15280 : Interval test 15280 15296 :=
  interval_of_check _ 15280 16 (by decide +kernel)
theorem Check119.part15296 : Interval test 15296 15312 :=
  interval_of_check _ 15296 16 (by decide +kernel)
theorem Check119.part15312 : Interval test 15312 15328 :=
  interval_of_check _ 15312 16 (by decide +kernel)
theorem Check119.part15328 : Interval test 15328 15344 :=
  interval_of_check _ 15328 16 (by decide +kernel)
theorem Check119.part15344 : Interval test 15344 15360 :=
  interval_of_check _ 15344 16 (by decide +kernel)
theorem Check119.checked : Interval test 15232 15360 :=
  (FiniteChecks.interval_append test 15232 15296 15360
  (FiniteChecks.interval_append test 15232 15264 15296
  (FiniteChecks.interval_append test 15232 15248 15264
  Check119.part15232
  Check119.part15248)
  (FiniteChecks.interval_append test 15264 15280 15296
  Check119.part15264
  Check119.part15280))
  (FiniteChecks.interval_append test 15296 15328 15360
  (FiniteChecks.interval_append test 15296 15312 15328
  Check119.part15296
  Check119.part15312)
  (FiniteChecks.interval_append test 15328 15344 15360
  Check119.part15328
  Check119.part15344)))
#print axioms Check119.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
