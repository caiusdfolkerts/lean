module
prelude
public import SharedSix0CellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check120.part15360 : Interval test 15360 15376 :=
  interval_of_check _ 15360 16 (by decide +kernel)
theorem Check120.part15376 : Interval test 15376 15392 :=
  interval_of_check _ 15376 16 (by decide +kernel)
theorem Check120.part15392 : Interval test 15392 15408 :=
  interval_of_check _ 15392 16 (by decide +kernel)
theorem Check120.part15408 : Interval test 15408 15424 :=
  interval_of_check _ 15408 16 (by decide +kernel)
theorem Check120.part15424 : Interval test 15424 15440 :=
  interval_of_check _ 15424 16 (by decide +kernel)
theorem Check120.part15440 : Interval test 15440 15456 :=
  interval_of_check _ 15440 16 (by decide +kernel)
theorem Check120.part15456 : Interval test 15456 15472 :=
  interval_of_check _ 15456 16 (by decide +kernel)
theorem Check120.part15472 : Interval test 15472 15488 :=
  interval_of_check _ 15472 16 (by decide +kernel)
theorem Check120.checked : Interval test 15360 15488 :=
  (FiniteChecks.interval_append test 15360 15424 15488
  (FiniteChecks.interval_append test 15360 15392 15424
  (FiniteChecks.interval_append test 15360 15376 15392
  Check120.part15360
  Check120.part15376)
  (FiniteChecks.interval_append test 15392 15408 15424
  Check120.part15392
  Check120.part15408))
  (FiniteChecks.interval_append test 15424 15456 15488
  (FiniteChecks.interval_append test 15424 15440 15456
  Check120.part15424
  Check120.part15440)
  (FiniteChecks.interval_append test 15456 15472 15488
  Check120.part15456
  Check120.part15472)))
#print axioms Check120.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check121.part15488 : Interval test 15488 15504 :=
  interval_of_check _ 15488 16 (by decide +kernel)
theorem Check121.part15504 : Interval test 15504 15520 :=
  interval_of_check _ 15504 16 (by decide +kernel)
theorem Check121.part15520 : Interval test 15520 15536 :=
  interval_of_check _ 15520 16 (by decide +kernel)
theorem Check121.part15536 : Interval test 15536 15552 :=
  interval_of_check _ 15536 16 (by decide +kernel)
theorem Check121.part15552 : Interval test 15552 15568 :=
  interval_of_check _ 15552 16 (by decide +kernel)
theorem Check121.part15568 : Interval test 15568 15584 :=
  interval_of_check _ 15568 16 (by decide +kernel)
theorem Check121.part15584 : Interval test 15584 15600 :=
  interval_of_check _ 15584 16 (by decide +kernel)
theorem Check121.part15600 : Interval test 15600 15616 :=
  interval_of_check _ 15600 16 (by decide +kernel)
theorem Check121.checked : Interval test 15488 15616 :=
  (FiniteChecks.interval_append test 15488 15552 15616
  (FiniteChecks.interval_append test 15488 15520 15552
  (FiniteChecks.interval_append test 15488 15504 15520
  Check121.part15488
  Check121.part15504)
  (FiniteChecks.interval_append test 15520 15536 15552
  Check121.part15520
  Check121.part15536))
  (FiniteChecks.interval_append test 15552 15584 15616
  (FiniteChecks.interval_append test 15552 15568 15584
  Check121.part15552
  Check121.part15568)
  (FiniteChecks.interval_append test 15584 15600 15616
  Check121.part15584
  Check121.part15600)))
#print axioms Check121.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check122.part15616 : Interval test 15616 15632 :=
  interval_of_check _ 15616 16 (by decide +kernel)
theorem Check122.part15632 : Interval test 15632 15648 :=
  interval_of_check _ 15632 16 (by decide +kernel)
theorem Check122.part15648 : Interval test 15648 15664 :=
  interval_of_check _ 15648 16 (by decide +kernel)
theorem Check122.part15664 : Interval test 15664 15680 :=
  interval_of_check _ 15664 16 (by decide +kernel)
theorem Check122.part15680 : Interval test 15680 15696 :=
  interval_of_check _ 15680 16 (by decide +kernel)
theorem Check122.part15696 : Interval test 15696 15712 :=
  interval_of_check _ 15696 16 (by decide +kernel)
theorem Check122.part15712 : Interval test 15712 15728 :=
  interval_of_check _ 15712 16 (by decide +kernel)
theorem Check122.part15728 : Interval test 15728 15744 :=
  interval_of_check _ 15728 16 (by decide +kernel)
theorem Check122.checked : Interval test 15616 15744 :=
  (FiniteChecks.interval_append test 15616 15680 15744
  (FiniteChecks.interval_append test 15616 15648 15680
  (FiniteChecks.interval_append test 15616 15632 15648
  Check122.part15616
  Check122.part15632)
  (FiniteChecks.interval_append test 15648 15664 15680
  Check122.part15648
  Check122.part15664))
  (FiniteChecks.interval_append test 15680 15712 15744
  (FiniteChecks.interval_append test 15680 15696 15712
  Check122.part15680
  Check122.part15696)
  (FiniteChecks.interval_append test 15712 15728 15744
  Check122.part15712
  Check122.part15728)))
#print axioms Check122.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check123.part15744 : Interval test 15744 15760 :=
  interval_of_check _ 15744 16 (by decide +kernel)
theorem Check123.part15760 : Interval test 15760 15776 :=
  interval_of_check _ 15760 16 (by decide +kernel)
theorem Check123.part15776 : Interval test 15776 15792 :=
  interval_of_check _ 15776 16 (by decide +kernel)
theorem Check123.part15792 : Interval test 15792 15808 :=
  interval_of_check _ 15792 16 (by decide +kernel)
theorem Check123.part15808 : Interval test 15808 15824 :=
  interval_of_check _ 15808 16 (by decide +kernel)
theorem Check123.part15824 : Interval test 15824 15840 :=
  interval_of_check _ 15824 16 (by decide +kernel)
theorem Check123.part15840 : Interval test 15840 15856 :=
  interval_of_check _ 15840 16 (by decide +kernel)
theorem Check123.part15856 : Interval test 15856 15872 :=
  interval_of_check _ 15856 16 (by decide +kernel)
theorem Check123.checked : Interval test 15744 15872 :=
  (FiniteChecks.interval_append test 15744 15808 15872
  (FiniteChecks.interval_append test 15744 15776 15808
  (FiniteChecks.interval_append test 15744 15760 15776
  Check123.part15744
  Check123.part15760)
  (FiniteChecks.interval_append test 15776 15792 15808
  Check123.part15776
  Check123.part15792))
  (FiniteChecks.interval_append test 15808 15840 15872
  (FiniteChecks.interval_append test 15808 15824 15840
  Check123.part15808
  Check123.part15824)
  (FiniteChecks.interval_append test 15840 15856 15872
  Check123.part15840
  Check123.part15856)))
#print axioms Check123.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check124.part15872 : Interval test 15872 15888 :=
  interval_of_check _ 15872 16 (by decide +kernel)
theorem Check124.part15888 : Interval test 15888 15904 :=
  interval_of_check _ 15888 16 (by decide +kernel)
theorem Check124.part15904 : Interval test 15904 15920 :=
  interval_of_check _ 15904 16 (by decide +kernel)
theorem Check124.part15920 : Interval test 15920 15936 :=
  interval_of_check _ 15920 16 (by decide +kernel)
theorem Check124.part15936 : Interval test 15936 15952 :=
  interval_of_check _ 15936 16 (by decide +kernel)
theorem Check124.part15952 : Interval test 15952 15968 :=
  interval_of_check _ 15952 16 (by decide +kernel)
theorem Check124.part15968 : Interval test 15968 15984 :=
  interval_of_check _ 15968 16 (by decide +kernel)
theorem Check124.part15984 : Interval test 15984 16000 :=
  interval_of_check _ 15984 16 (by decide +kernel)
theorem Check124.checked : Interval test 15872 16000 :=
  (FiniteChecks.interval_append test 15872 15936 16000
  (FiniteChecks.interval_append test 15872 15904 15936
  (FiniteChecks.interval_append test 15872 15888 15904
  Check124.part15872
  Check124.part15888)
  (FiniteChecks.interval_append test 15904 15920 15936
  Check124.part15904
  Check124.part15920))
  (FiniteChecks.interval_append test 15936 15968 16000
  (FiniteChecks.interval_append test 15936 15952 15968
  Check124.part15936
  Check124.part15952)
  (FiniteChecks.interval_append test 15968 15984 16000
  Check124.part15968
  Check124.part15984)))
#print axioms Check124.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check125.part16000 : Interval test 16000 16016 :=
  interval_of_check _ 16000 16 (by decide +kernel)
theorem Check125.part16016 : Interval test 16016 16032 :=
  interval_of_check _ 16016 16 (by decide +kernel)
theorem Check125.part16032 : Interval test 16032 16048 :=
  interval_of_check _ 16032 16 (by decide +kernel)
theorem Check125.part16048 : Interval test 16048 16064 :=
  interval_of_check _ 16048 16 (by decide +kernel)
theorem Check125.part16064 : Interval test 16064 16080 :=
  interval_of_check _ 16064 16 (by decide +kernel)
theorem Check125.part16080 : Interval test 16080 16096 :=
  interval_of_check _ 16080 16 (by decide +kernel)
theorem Check125.part16096 : Interval test 16096 16112 :=
  interval_of_check _ 16096 16 (by decide +kernel)
theorem Check125.part16112 : Interval test 16112 16128 :=
  interval_of_check _ 16112 16 (by decide +kernel)
theorem Check125.checked : Interval test 16000 16128 :=
  (FiniteChecks.interval_append test 16000 16064 16128
  (FiniteChecks.interval_append test 16000 16032 16064
  (FiniteChecks.interval_append test 16000 16016 16032
  Check125.part16000
  Check125.part16016)
  (FiniteChecks.interval_append test 16032 16048 16064
  Check125.part16032
  Check125.part16048))
  (FiniteChecks.interval_append test 16064 16096 16128
  (FiniteChecks.interval_append test 16064 16080 16096
  Check125.part16064
  Check125.part16080)
  (FiniteChecks.interval_append test 16096 16112 16128
  Check125.part16096
  Check125.part16112)))
#print axioms Check125.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check126.part16128 : Interval test 16128 16144 :=
  interval_of_check _ 16128 16 (by decide +kernel)
theorem Check126.part16144 : Interval test 16144 16160 :=
  interval_of_check _ 16144 16 (by decide +kernel)
theorem Check126.part16160 : Interval test 16160 16176 :=
  interval_of_check _ 16160 16 (by decide +kernel)
theorem Check126.part16176 : Interval test 16176 16192 :=
  interval_of_check _ 16176 16 (by decide +kernel)
theorem Check126.part16192 : Interval test 16192 16208 :=
  interval_of_check _ 16192 16 (by decide +kernel)
theorem Check126.part16208 : Interval test 16208 16224 :=
  interval_of_check _ 16208 16 (by decide +kernel)
theorem Check126.part16224 : Interval test 16224 16240 :=
  interval_of_check _ 16224 16 (by decide +kernel)
theorem Check126.part16240 : Interval test 16240 16256 :=
  interval_of_check _ 16240 16 (by decide +kernel)
theorem Check126.checked : Interval test 16128 16256 :=
  (FiniteChecks.interval_append test 16128 16192 16256
  (FiniteChecks.interval_append test 16128 16160 16192
  (FiniteChecks.interval_append test 16128 16144 16160
  Check126.part16128
  Check126.part16144)
  (FiniteChecks.interval_append test 16160 16176 16192
  Check126.part16160
  Check126.part16176))
  (FiniteChecks.interval_append test 16192 16224 16256
  (FiniteChecks.interval_append test 16192 16208 16224
  Check126.part16192
  Check126.part16208)
  (FiniteChecks.interval_append test 16224 16240 16256
  Check126.part16224
  Check126.part16240)))
#print axioms Check126.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check127.part16256 : Interval test 16256 16272 :=
  interval_of_check _ 16256 16 (by decide +kernel)
theorem Check127.part16272 : Interval test 16272 16288 :=
  interval_of_check _ 16272 16 (by decide +kernel)
theorem Check127.part16288 : Interval test 16288 16304 :=
  interval_of_check _ 16288 16 (by decide +kernel)
theorem Check127.part16304 : Interval test 16304 16320 :=
  interval_of_check _ 16304 16 (by decide +kernel)
theorem Check127.part16320 : Interval test 16320 16336 :=
  interval_of_check _ 16320 16 (by decide +kernel)
theorem Check127.part16336 : Interval test 16336 16352 :=
  interval_of_check _ 16336 16 (by decide +kernel)
theorem Check127.part16352 : Interval test 16352 16368 :=
  interval_of_check _ 16352 16 (by decide +kernel)
theorem Check127.part16368 : Interval test 16368 16384 :=
  interval_of_check _ 16368 16 (by decide +kernel)
theorem Check127.checked : Interval test 16256 16384 :=
  (FiniteChecks.interval_append test 16256 16320 16384
  (FiniteChecks.interval_append test 16256 16288 16320
  (FiniteChecks.interval_append test 16256 16272 16288
  Check127.part16256
  Check127.part16272)
  (FiniteChecks.interval_append test 16288 16304 16320
  Check127.part16288
  Check127.part16304))
  (FiniteChecks.interval_append test 16320 16352 16384
  (FiniteChecks.interval_append test 16320 16336 16352
  Check127.part16320
  Check127.part16336)
  (FiniteChecks.interval_append test 16352 16368 16384
  Check127.part16352
  Check127.part16368)))
#print axioms Check127.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check128.part16384 : Interval test 16384 16400 :=
  interval_of_check _ 16384 16 (by decide +kernel)
theorem Check128.part16400 : Interval test 16400 16416 :=
  interval_of_check _ 16400 16 (by decide +kernel)
theorem Check128.part16416 : Interval test 16416 16432 :=
  interval_of_check _ 16416 16 (by decide +kernel)
theorem Check128.part16432 : Interval test 16432 16448 :=
  interval_of_check _ 16432 16 (by decide +kernel)
theorem Check128.part16448 : Interval test 16448 16464 :=
  interval_of_check _ 16448 16 (by decide +kernel)
theorem Check128.part16464 : Interval test 16464 16480 :=
  interval_of_check _ 16464 16 (by decide +kernel)
theorem Check128.part16480 : Interval test 16480 16496 :=
  interval_of_check _ 16480 16 (by decide +kernel)
theorem Check128.part16496 : Interval test 16496 16512 :=
  interval_of_check _ 16496 16 (by decide +kernel)
theorem Check128.checked : Interval test 16384 16512 :=
  (FiniteChecks.interval_append test 16384 16448 16512
  (FiniteChecks.interval_append test 16384 16416 16448
  (FiniteChecks.interval_append test 16384 16400 16416
  Check128.part16384
  Check128.part16400)
  (FiniteChecks.interval_append test 16416 16432 16448
  Check128.part16416
  Check128.part16432))
  (FiniteChecks.interval_append test 16448 16480 16512
  (FiniteChecks.interval_append test 16448 16464 16480
  Check128.part16448
  Check128.part16464)
  (FiniteChecks.interval_append test 16480 16496 16512
  Check128.part16480
  Check128.part16496)))
#print axioms Check128.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check129.part16512 : Interval test 16512 16528 :=
  interval_of_check _ 16512 16 (by decide +kernel)
theorem Check129.part16528 : Interval test 16528 16544 :=
  interval_of_check _ 16528 16 (by decide +kernel)
theorem Check129.part16544 : Interval test 16544 16560 :=
  interval_of_check _ 16544 16 (by decide +kernel)
theorem Check129.part16560 : Interval test 16560 16576 :=
  interval_of_check _ 16560 16 (by decide +kernel)
theorem Check129.part16576 : Interval test 16576 16592 :=
  interval_of_check _ 16576 16 (by decide +kernel)
theorem Check129.part16592 : Interval test 16592 16608 :=
  interval_of_check _ 16592 16 (by decide +kernel)
theorem Check129.part16608 : Interval test 16608 16624 :=
  interval_of_check _ 16608 16 (by decide +kernel)
theorem Check129.part16624 : Interval test 16624 16640 :=
  interval_of_check _ 16624 16 (by decide +kernel)
theorem Check129.checked : Interval test 16512 16640 :=
  (FiniteChecks.interval_append test 16512 16576 16640
  (FiniteChecks.interval_append test 16512 16544 16576
  (FiniteChecks.interval_append test 16512 16528 16544
  Check129.part16512
  Check129.part16528)
  (FiniteChecks.interval_append test 16544 16560 16576
  Check129.part16544
  Check129.part16560))
  (FiniteChecks.interval_append test 16576 16608 16640
  (FiniteChecks.interval_append test 16576 16592 16608
  Check129.part16576
  Check129.part16592)
  (FiniteChecks.interval_append test 16608 16624 16640
  Check129.part16608
  Check129.part16624)))
#print axioms Check129.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check130.part16640 : Interval test 16640 16656 :=
  interval_of_check _ 16640 16 (by decide +kernel)
theorem Check130.part16656 : Interval test 16656 16672 :=
  interval_of_check _ 16656 16 (by decide +kernel)
theorem Check130.part16672 : Interval test 16672 16688 :=
  interval_of_check _ 16672 16 (by decide +kernel)
theorem Check130.part16688 : Interval test 16688 16704 :=
  interval_of_check _ 16688 16 (by decide +kernel)
theorem Check130.part16704 : Interval test 16704 16720 :=
  interval_of_check _ 16704 16 (by decide +kernel)
theorem Check130.part16720 : Interval test 16720 16736 :=
  interval_of_check _ 16720 16 (by decide +kernel)
theorem Check130.part16736 : Interval test 16736 16752 :=
  interval_of_check _ 16736 16 (by decide +kernel)
theorem Check130.part16752 : Interval test 16752 16768 :=
  interval_of_check _ 16752 16 (by decide +kernel)
theorem Check130.checked : Interval test 16640 16768 :=
  (FiniteChecks.interval_append test 16640 16704 16768
  (FiniteChecks.interval_append test 16640 16672 16704
  (FiniteChecks.interval_append test 16640 16656 16672
  Check130.part16640
  Check130.part16656)
  (FiniteChecks.interval_append test 16672 16688 16704
  Check130.part16672
  Check130.part16688))
  (FiniteChecks.interval_append test 16704 16736 16768
  (FiniteChecks.interval_append test 16704 16720 16736
  Check130.part16704
  Check130.part16720)
  (FiniteChecks.interval_append test 16736 16752 16768
  Check130.part16736
  Check130.part16752)))
#print axioms Check130.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check131.part16768 : Interval test 16768 16784 :=
  interval_of_check _ 16768 16 (by decide +kernel)
theorem Check131.part16784 : Interval test 16784 16800 :=
  interval_of_check _ 16784 16 (by decide +kernel)
theorem Check131.part16800 : Interval test 16800 16816 :=
  interval_of_check _ 16800 16 (by decide +kernel)
theorem Check131.part16816 : Interval test 16816 16832 :=
  interval_of_check _ 16816 16 (by decide +kernel)
theorem Check131.part16832 : Interval test 16832 16848 :=
  interval_of_check _ 16832 16 (by decide +kernel)
theorem Check131.part16848 : Interval test 16848 16864 :=
  interval_of_check _ 16848 16 (by decide +kernel)
theorem Check131.part16864 : Interval test 16864 16880 :=
  interval_of_check _ 16864 16 (by decide +kernel)
theorem Check131.part16880 : Interval test 16880 16896 :=
  interval_of_check _ 16880 16 (by decide +kernel)
theorem Check131.checked : Interval test 16768 16896 :=
  (FiniteChecks.interval_append test 16768 16832 16896
  (FiniteChecks.interval_append test 16768 16800 16832
  (FiniteChecks.interval_append test 16768 16784 16800
  Check131.part16768
  Check131.part16784)
  (FiniteChecks.interval_append test 16800 16816 16832
  Check131.part16800
  Check131.part16816))
  (FiniteChecks.interval_append test 16832 16864 16896
  (FiniteChecks.interval_append test 16832 16848 16864
  Check131.part16832
  Check131.part16848)
  (FiniteChecks.interval_append test 16864 16880 16896
  Check131.part16864
  Check131.part16880)))
#print axioms Check131.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check132.part16896 : Interval test 16896 16912 :=
  interval_of_check _ 16896 16 (by decide +kernel)
theorem Check132.part16912 : Interval test 16912 16928 :=
  interval_of_check _ 16912 16 (by decide +kernel)
theorem Check132.part16928 : Interval test 16928 16944 :=
  interval_of_check _ 16928 16 (by decide +kernel)
theorem Check132.part16944 : Interval test 16944 16960 :=
  interval_of_check _ 16944 16 (by decide +kernel)
theorem Check132.part16960 : Interval test 16960 16976 :=
  interval_of_check _ 16960 16 (by decide +kernel)
theorem Check132.part16976 : Interval test 16976 16992 :=
  interval_of_check _ 16976 16 (by decide +kernel)
theorem Check132.part16992 : Interval test 16992 17008 :=
  interval_of_check _ 16992 16 (by decide +kernel)
theorem Check132.part17008 : Interval test 17008 17024 :=
  interval_of_check _ 17008 16 (by decide +kernel)
theorem Check132.checked : Interval test 16896 17024 :=
  (FiniteChecks.interval_append test 16896 16960 17024
  (FiniteChecks.interval_append test 16896 16928 16960
  (FiniteChecks.interval_append test 16896 16912 16928
  Check132.part16896
  Check132.part16912)
  (FiniteChecks.interval_append test 16928 16944 16960
  Check132.part16928
  Check132.part16944))
  (FiniteChecks.interval_append test 16960 16992 17024
  (FiniteChecks.interval_append test 16960 16976 16992
  Check132.part16960
  Check132.part16976)
  (FiniteChecks.interval_append test 16992 17008 17024
  Check132.part16992
  Check132.part17008)))
#print axioms Check132.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check133.part17024 : Interval test 17024 17040 :=
  interval_of_check _ 17024 16 (by decide +kernel)
theorem Check133.part17040 : Interval test 17040 17056 :=
  interval_of_check _ 17040 16 (by decide +kernel)
theorem Check133.part17056 : Interval test 17056 17072 :=
  interval_of_check _ 17056 16 (by decide +kernel)
theorem Check133.part17072 : Interval test 17072 17088 :=
  interval_of_check _ 17072 16 (by decide +kernel)
theorem Check133.part17088 : Interval test 17088 17104 :=
  interval_of_check _ 17088 16 (by decide +kernel)
theorem Check133.part17104 : Interval test 17104 17120 :=
  interval_of_check _ 17104 16 (by decide +kernel)
theorem Check133.part17120 : Interval test 17120 17136 :=
  interval_of_check _ 17120 16 (by decide +kernel)
theorem Check133.part17136 : Interval test 17136 17152 :=
  interval_of_check _ 17136 16 (by decide +kernel)
theorem Check133.checked : Interval test 17024 17152 :=
  (FiniteChecks.interval_append test 17024 17088 17152
  (FiniteChecks.interval_append test 17024 17056 17088
  (FiniteChecks.interval_append test 17024 17040 17056
  Check133.part17024
  Check133.part17040)
  (FiniteChecks.interval_append test 17056 17072 17088
  Check133.part17056
  Check133.part17072))
  (FiniteChecks.interval_append test 17088 17120 17152
  (FiniteChecks.interval_append test 17088 17104 17120
  Check133.part17088
  Check133.part17104)
  (FiniteChecks.interval_append test 17120 17136 17152
  Check133.part17120
  Check133.part17136)))
#print axioms Check133.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check134.part17152 : Interval test 17152 17168 :=
  interval_of_check _ 17152 16 (by decide +kernel)
theorem Check134.part17168 : Interval test 17168 17184 :=
  interval_of_check _ 17168 16 (by decide +kernel)
theorem Check134.part17184 : Interval test 17184 17200 :=
  interval_of_check _ 17184 16 (by decide +kernel)
theorem Check134.part17200 : Interval test 17200 17216 :=
  interval_of_check _ 17200 16 (by decide +kernel)
theorem Check134.part17216 : Interval test 17216 17232 :=
  interval_of_check _ 17216 16 (by decide +kernel)
theorem Check134.part17232 : Interval test 17232 17248 :=
  interval_of_check _ 17232 16 (by decide +kernel)
theorem Check134.part17248 : Interval test 17248 17264 :=
  interval_of_check _ 17248 16 (by decide +kernel)
theorem Check134.part17264 : Interval test 17264 17280 :=
  interval_of_check _ 17264 16 (by decide +kernel)
theorem Check134.checked : Interval test 17152 17280 :=
  (FiniteChecks.interval_append test 17152 17216 17280
  (FiniteChecks.interval_append test 17152 17184 17216
  (FiniteChecks.interval_append test 17152 17168 17184
  Check134.part17152
  Check134.part17168)
  (FiniteChecks.interval_append test 17184 17200 17216
  Check134.part17184
  Check134.part17200))
  (FiniteChecks.interval_append test 17216 17248 17280
  (FiniteChecks.interval_append test 17216 17232 17248
  Check134.part17216
  Check134.part17232)
  (FiniteChecks.interval_append test 17248 17264 17280
  Check134.part17248
  Check134.part17264)))
#print axioms Check134.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check135.part17280 : Interval test 17280 17296 :=
  interval_of_check _ 17280 16 (by decide +kernel)
theorem Check135.part17296 : Interval test 17296 17312 :=
  interval_of_check _ 17296 16 (by decide +kernel)
theorem Check135.part17312 : Interval test 17312 17328 :=
  interval_of_check _ 17312 16 (by decide +kernel)
theorem Check135.part17328 : Interval test 17328 17344 :=
  interval_of_check _ 17328 16 (by decide +kernel)
theorem Check135.part17344 : Interval test 17344 17360 :=
  interval_of_check _ 17344 16 (by decide +kernel)
theorem Check135.part17360 : Interval test 17360 17376 :=
  interval_of_check _ 17360 16 (by decide +kernel)
theorem Check135.part17376 : Interval test 17376 17392 :=
  interval_of_check _ 17376 16 (by decide +kernel)
theorem Check135.part17392 : Interval test 17392 17408 :=
  interval_of_check _ 17392 16 (by decide +kernel)
theorem Check135.checked : Interval test 17280 17408 :=
  (FiniteChecks.interval_append test 17280 17344 17408
  (FiniteChecks.interval_append test 17280 17312 17344
  (FiniteChecks.interval_append test 17280 17296 17312
  Check135.part17280
  Check135.part17296)
  (FiniteChecks.interval_append test 17312 17328 17344
  Check135.part17312
  Check135.part17328))
  (FiniteChecks.interval_append test 17344 17376 17408
  (FiniteChecks.interval_append test 17344 17360 17376
  Check135.part17344
  Check135.part17360)
  (FiniteChecks.interval_append test 17376 17392 17408
  Check135.part17376
  Check135.part17392)))
#print axioms Check135.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check136.part17408 : Interval test 17408 17424 :=
  interval_of_check _ 17408 16 (by decide +kernel)
theorem Check136.part17424 : Interval test 17424 17440 :=
  interval_of_check _ 17424 16 (by decide +kernel)
theorem Check136.part17440 : Interval test 17440 17456 :=
  interval_of_check _ 17440 16 (by decide +kernel)
theorem Check136.part17456 : Interval test 17456 17472 :=
  interval_of_check _ 17456 16 (by decide +kernel)
theorem Check136.part17472 : Interval test 17472 17488 :=
  interval_of_check _ 17472 16 (by decide +kernel)
theorem Check136.part17488 : Interval test 17488 17504 :=
  interval_of_check _ 17488 16 (by decide +kernel)
theorem Check136.part17504 : Interval test 17504 17520 :=
  interval_of_check _ 17504 16 (by decide +kernel)
theorem Check136.part17520 : Interval test 17520 17536 :=
  interval_of_check _ 17520 16 (by decide +kernel)
theorem Check136.checked : Interval test 17408 17536 :=
  (FiniteChecks.interval_append test 17408 17472 17536
  (FiniteChecks.interval_append test 17408 17440 17472
  (FiniteChecks.interval_append test 17408 17424 17440
  Check136.part17408
  Check136.part17424)
  (FiniteChecks.interval_append test 17440 17456 17472
  Check136.part17440
  Check136.part17456))
  (FiniteChecks.interval_append test 17472 17504 17536
  (FiniteChecks.interval_append test 17472 17488 17504
  Check136.part17472
  Check136.part17488)
  (FiniteChecks.interval_append test 17504 17520 17536
  Check136.part17504
  Check136.part17520)))
#print axioms Check136.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check137.part17536 : Interval test 17536 17552 :=
  interval_of_check _ 17536 16 (by decide +kernel)
theorem Check137.part17552 : Interval test 17552 17568 :=
  interval_of_check _ 17552 16 (by decide +kernel)
theorem Check137.part17568 : Interval test 17568 17584 :=
  interval_of_check _ 17568 16 (by decide +kernel)
theorem Check137.part17584 : Interval test 17584 17600 :=
  interval_of_check _ 17584 16 (by decide +kernel)
theorem Check137.part17600 : Interval test 17600 17616 :=
  interval_of_check _ 17600 16 (by decide +kernel)
theorem Check137.part17616 : Interval test 17616 17632 :=
  interval_of_check _ 17616 16 (by decide +kernel)
theorem Check137.part17632 : Interval test 17632 17648 :=
  interval_of_check _ 17632 16 (by decide +kernel)
theorem Check137.part17648 : Interval test 17648 17664 :=
  interval_of_check _ 17648 16 (by decide +kernel)
theorem Check137.checked : Interval test 17536 17664 :=
  (FiniteChecks.interval_append test 17536 17600 17664
  (FiniteChecks.interval_append test 17536 17568 17600
  (FiniteChecks.interval_append test 17536 17552 17568
  Check137.part17536
  Check137.part17552)
  (FiniteChecks.interval_append test 17568 17584 17600
  Check137.part17568
  Check137.part17584))
  (FiniteChecks.interval_append test 17600 17632 17664
  (FiniteChecks.interval_append test 17600 17616 17632
  Check137.part17600
  Check137.part17616)
  (FiniteChecks.interval_append test 17632 17648 17664
  Check137.part17632
  Check137.part17648)))
#print axioms Check137.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check138.part17664 : Interval test 17664 17680 :=
  interval_of_check _ 17664 16 (by decide +kernel)
theorem Check138.part17680 : Interval test 17680 17696 :=
  interval_of_check _ 17680 16 (by decide +kernel)
theorem Check138.part17696 : Interval test 17696 17712 :=
  interval_of_check _ 17696 16 (by decide +kernel)
theorem Check138.part17712 : Interval test 17712 17728 :=
  interval_of_check _ 17712 16 (by decide +kernel)
theorem Check138.part17728 : Interval test 17728 17744 :=
  interval_of_check _ 17728 16 (by decide +kernel)
theorem Check138.part17744 : Interval test 17744 17760 :=
  interval_of_check _ 17744 16 (by decide +kernel)
theorem Check138.part17760 : Interval test 17760 17776 :=
  interval_of_check _ 17760 16 (by decide +kernel)
theorem Check138.part17776 : Interval test 17776 17792 :=
  interval_of_check _ 17776 16 (by decide +kernel)
theorem Check138.checked : Interval test 17664 17792 :=
  (FiniteChecks.interval_append test 17664 17728 17792
  (FiniteChecks.interval_append test 17664 17696 17728
  (FiniteChecks.interval_append test 17664 17680 17696
  Check138.part17664
  Check138.part17680)
  (FiniteChecks.interval_append test 17696 17712 17728
  Check138.part17696
  Check138.part17712))
  (FiniteChecks.interval_append test 17728 17760 17792
  (FiniteChecks.interval_append test 17728 17744 17760
  Check138.part17728
  Check138.part17744)
  (FiniteChecks.interval_append test 17760 17776 17792
  Check138.part17760
  Check138.part17776)))
#print axioms Check138.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check139.part17792 : Interval test 17792 17808 :=
  interval_of_check _ 17792 16 (by decide +kernel)
theorem Check139.part17808 : Interval test 17808 17824 :=
  interval_of_check _ 17808 16 (by decide +kernel)
theorem Check139.part17824 : Interval test 17824 17840 :=
  interval_of_check _ 17824 16 (by decide +kernel)
theorem Check139.part17840 : Interval test 17840 17856 :=
  interval_of_check _ 17840 16 (by decide +kernel)
theorem Check139.part17856 : Interval test 17856 17872 :=
  interval_of_check _ 17856 16 (by decide +kernel)
theorem Check139.part17872 : Interval test 17872 17888 :=
  interval_of_check _ 17872 16 (by decide +kernel)
theorem Check139.part17888 : Interval test 17888 17904 :=
  interval_of_check _ 17888 16 (by decide +kernel)
theorem Check139.part17904 : Interval test 17904 17920 :=
  interval_of_check _ 17904 16 (by decide +kernel)
theorem Check139.checked : Interval test 17792 17920 :=
  (FiniteChecks.interval_append test 17792 17856 17920
  (FiniteChecks.interval_append test 17792 17824 17856
  (FiniteChecks.interval_append test 17792 17808 17824
  Check139.part17792
  Check139.part17808)
  (FiniteChecks.interval_append test 17824 17840 17856
  Check139.part17824
  Check139.part17840))
  (FiniteChecks.interval_append test 17856 17888 17920
  (FiniteChecks.interval_append test 17856 17872 17888
  Check139.part17856
  Check139.part17872)
  (FiniteChecks.interval_append test 17888 17904 17920
  Check139.part17888
  Check139.part17904)))
#print axioms Check139.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
