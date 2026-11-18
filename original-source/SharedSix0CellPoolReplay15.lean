module
prelude
public import SharedSix0CellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check300.part38400 : Interval test 38400 38416 :=
  interval_of_check _ 38400 16 (by decide +kernel)
theorem Check300.part38416 : Interval test 38416 38432 :=
  interval_of_check _ 38416 16 (by decide +kernel)
theorem Check300.part38432 : Interval test 38432 38448 :=
  interval_of_check _ 38432 16 (by decide +kernel)
theorem Check300.part38448 : Interval test 38448 38464 :=
  interval_of_check _ 38448 16 (by decide +kernel)
theorem Check300.part38464 : Interval test 38464 38480 :=
  interval_of_check _ 38464 16 (by decide +kernel)
theorem Check300.part38480 : Interval test 38480 38496 :=
  interval_of_check _ 38480 16 (by decide +kernel)
theorem Check300.part38496 : Interval test 38496 38512 :=
  interval_of_check _ 38496 16 (by decide +kernel)
theorem Check300.part38512 : Interval test 38512 38528 :=
  interval_of_check _ 38512 16 (by decide +kernel)
theorem Check300.checked : Interval test 38400 38528 :=
  (FiniteChecks.interval_append test 38400 38464 38528
  (FiniteChecks.interval_append test 38400 38432 38464
  (FiniteChecks.interval_append test 38400 38416 38432
  Check300.part38400
  Check300.part38416)
  (FiniteChecks.interval_append test 38432 38448 38464
  Check300.part38432
  Check300.part38448))
  (FiniteChecks.interval_append test 38464 38496 38528
  (FiniteChecks.interval_append test 38464 38480 38496
  Check300.part38464
  Check300.part38480)
  (FiniteChecks.interval_append test 38496 38512 38528
  Check300.part38496
  Check300.part38512)))
#print axioms Check300.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check301.part38528 : Interval test 38528 38544 :=
  interval_of_check _ 38528 16 (by decide +kernel)
theorem Check301.part38544 : Interval test 38544 38560 :=
  interval_of_check _ 38544 16 (by decide +kernel)
theorem Check301.part38560 : Interval test 38560 38576 :=
  interval_of_check _ 38560 16 (by decide +kernel)
theorem Check301.part38576 : Interval test 38576 38592 :=
  interval_of_check _ 38576 16 (by decide +kernel)
theorem Check301.part38592 : Interval test 38592 38608 :=
  interval_of_check _ 38592 16 (by decide +kernel)
theorem Check301.part38608 : Interval test 38608 38624 :=
  interval_of_check _ 38608 16 (by decide +kernel)
theorem Check301.part38624 : Interval test 38624 38640 :=
  interval_of_check _ 38624 16 (by decide +kernel)
theorem Check301.part38640 : Interval test 38640 38656 :=
  interval_of_check _ 38640 16 (by decide +kernel)
theorem Check301.checked : Interval test 38528 38656 :=
  (FiniteChecks.interval_append test 38528 38592 38656
  (FiniteChecks.interval_append test 38528 38560 38592
  (FiniteChecks.interval_append test 38528 38544 38560
  Check301.part38528
  Check301.part38544)
  (FiniteChecks.interval_append test 38560 38576 38592
  Check301.part38560
  Check301.part38576))
  (FiniteChecks.interval_append test 38592 38624 38656
  (FiniteChecks.interval_append test 38592 38608 38624
  Check301.part38592
  Check301.part38608)
  (FiniteChecks.interval_append test 38624 38640 38656
  Check301.part38624
  Check301.part38640)))
#print axioms Check301.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check302.part38656 : Interval test 38656 38672 :=
  interval_of_check _ 38656 16 (by decide +kernel)
theorem Check302.part38672 : Interval test 38672 38688 :=
  interval_of_check _ 38672 16 (by decide +kernel)
theorem Check302.part38688 : Interval test 38688 38704 :=
  interval_of_check _ 38688 16 (by decide +kernel)
theorem Check302.part38704 : Interval test 38704 38720 :=
  interval_of_check _ 38704 16 (by decide +kernel)
theorem Check302.part38720 : Interval test 38720 38736 :=
  interval_of_check _ 38720 16 (by decide +kernel)
theorem Check302.part38736 : Interval test 38736 38752 :=
  interval_of_check _ 38736 16 (by decide +kernel)
theorem Check302.part38752 : Interval test 38752 38768 :=
  interval_of_check _ 38752 16 (by decide +kernel)
theorem Check302.part38768 : Interval test 38768 38784 :=
  interval_of_check _ 38768 16 (by decide +kernel)
theorem Check302.checked : Interval test 38656 38784 :=
  (FiniteChecks.interval_append test 38656 38720 38784
  (FiniteChecks.interval_append test 38656 38688 38720
  (FiniteChecks.interval_append test 38656 38672 38688
  Check302.part38656
  Check302.part38672)
  (FiniteChecks.interval_append test 38688 38704 38720
  Check302.part38688
  Check302.part38704))
  (FiniteChecks.interval_append test 38720 38752 38784
  (FiniteChecks.interval_append test 38720 38736 38752
  Check302.part38720
  Check302.part38736)
  (FiniteChecks.interval_append test 38752 38768 38784
  Check302.part38752
  Check302.part38768)))
#print axioms Check302.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check303.part38784 : Interval test 38784 38800 :=
  interval_of_check _ 38784 16 (by decide +kernel)
theorem Check303.part38800 : Interval test 38800 38816 :=
  interval_of_check _ 38800 16 (by decide +kernel)
theorem Check303.part38816 : Interval test 38816 38832 :=
  interval_of_check _ 38816 16 (by decide +kernel)
theorem Check303.part38832 : Interval test 38832 38848 :=
  interval_of_check _ 38832 16 (by decide +kernel)
theorem Check303.part38848 : Interval test 38848 38864 :=
  interval_of_check _ 38848 16 (by decide +kernel)
theorem Check303.part38864 : Interval test 38864 38880 :=
  interval_of_check _ 38864 16 (by decide +kernel)
theorem Check303.part38880 : Interval test 38880 38896 :=
  interval_of_check _ 38880 16 (by decide +kernel)
theorem Check303.part38896 : Interval test 38896 38912 :=
  interval_of_check _ 38896 16 (by decide +kernel)
theorem Check303.checked : Interval test 38784 38912 :=
  (FiniteChecks.interval_append test 38784 38848 38912
  (FiniteChecks.interval_append test 38784 38816 38848
  (FiniteChecks.interval_append test 38784 38800 38816
  Check303.part38784
  Check303.part38800)
  (FiniteChecks.interval_append test 38816 38832 38848
  Check303.part38816
  Check303.part38832))
  (FiniteChecks.interval_append test 38848 38880 38912
  (FiniteChecks.interval_append test 38848 38864 38880
  Check303.part38848
  Check303.part38864)
  (FiniteChecks.interval_append test 38880 38896 38912
  Check303.part38880
  Check303.part38896)))
#print axioms Check303.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check304.part38912 : Interval test 38912 38928 :=
  interval_of_check _ 38912 16 (by decide +kernel)
theorem Check304.part38928 : Interval test 38928 38944 :=
  interval_of_check _ 38928 16 (by decide +kernel)
theorem Check304.part38944 : Interval test 38944 38960 :=
  interval_of_check _ 38944 16 (by decide +kernel)
theorem Check304.part38960 : Interval test 38960 38976 :=
  interval_of_check _ 38960 16 (by decide +kernel)
theorem Check304.part38976 : Interval test 38976 38992 :=
  interval_of_check _ 38976 16 (by decide +kernel)
theorem Check304.part38992 : Interval test 38992 39008 :=
  interval_of_check _ 38992 16 (by decide +kernel)
theorem Check304.part39008 : Interval test 39008 39024 :=
  interval_of_check _ 39008 16 (by decide +kernel)
theorem Check304.part39024 : Interval test 39024 39040 :=
  interval_of_check _ 39024 16 (by decide +kernel)
theorem Check304.checked : Interval test 38912 39040 :=
  (FiniteChecks.interval_append test 38912 38976 39040
  (FiniteChecks.interval_append test 38912 38944 38976
  (FiniteChecks.interval_append test 38912 38928 38944
  Check304.part38912
  Check304.part38928)
  (FiniteChecks.interval_append test 38944 38960 38976
  Check304.part38944
  Check304.part38960))
  (FiniteChecks.interval_append test 38976 39008 39040
  (FiniteChecks.interval_append test 38976 38992 39008
  Check304.part38976
  Check304.part38992)
  (FiniteChecks.interval_append test 39008 39024 39040
  Check304.part39008
  Check304.part39024)))
#print axioms Check304.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check305.part39040 : Interval test 39040 39056 :=
  interval_of_check _ 39040 16 (by decide +kernel)
theorem Check305.part39056 : Interval test 39056 39072 :=
  interval_of_check _ 39056 16 (by decide +kernel)
theorem Check305.part39072 : Interval test 39072 39088 :=
  interval_of_check _ 39072 16 (by decide +kernel)
theorem Check305.part39088 : Interval test 39088 39104 :=
  interval_of_check _ 39088 16 (by decide +kernel)
theorem Check305.part39104 : Interval test 39104 39120 :=
  interval_of_check _ 39104 16 (by decide +kernel)
theorem Check305.part39120 : Interval test 39120 39136 :=
  interval_of_check _ 39120 16 (by decide +kernel)
theorem Check305.part39136 : Interval test 39136 39152 :=
  interval_of_check _ 39136 16 (by decide +kernel)
theorem Check305.part39152 : Interval test 39152 39168 :=
  interval_of_check _ 39152 16 (by decide +kernel)
theorem Check305.checked : Interval test 39040 39168 :=
  (FiniteChecks.interval_append test 39040 39104 39168
  (FiniteChecks.interval_append test 39040 39072 39104
  (FiniteChecks.interval_append test 39040 39056 39072
  Check305.part39040
  Check305.part39056)
  (FiniteChecks.interval_append test 39072 39088 39104
  Check305.part39072
  Check305.part39088))
  (FiniteChecks.interval_append test 39104 39136 39168
  (FiniteChecks.interval_append test 39104 39120 39136
  Check305.part39104
  Check305.part39120)
  (FiniteChecks.interval_append test 39136 39152 39168
  Check305.part39136
  Check305.part39152)))
#print axioms Check305.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check306.part39168 : Interval test 39168 39184 :=
  interval_of_check _ 39168 16 (by decide +kernel)
theorem Check306.part39184 : Interval test 39184 39200 :=
  interval_of_check _ 39184 16 (by decide +kernel)
theorem Check306.part39200 : Interval test 39200 39216 :=
  interval_of_check _ 39200 16 (by decide +kernel)
theorem Check306.part39216 : Interval test 39216 39232 :=
  interval_of_check _ 39216 16 (by decide +kernel)
theorem Check306.part39232 : Interval test 39232 39248 :=
  interval_of_check _ 39232 16 (by decide +kernel)
theorem Check306.part39248 : Interval test 39248 39264 :=
  interval_of_check _ 39248 16 (by decide +kernel)
theorem Check306.part39264 : Interval test 39264 39280 :=
  interval_of_check _ 39264 16 (by decide +kernel)
theorem Check306.part39280 : Interval test 39280 39296 :=
  interval_of_check _ 39280 16 (by decide +kernel)
theorem Check306.checked : Interval test 39168 39296 :=
  (FiniteChecks.interval_append test 39168 39232 39296
  (FiniteChecks.interval_append test 39168 39200 39232
  (FiniteChecks.interval_append test 39168 39184 39200
  Check306.part39168
  Check306.part39184)
  (FiniteChecks.interval_append test 39200 39216 39232
  Check306.part39200
  Check306.part39216))
  (FiniteChecks.interval_append test 39232 39264 39296
  (FiniteChecks.interval_append test 39232 39248 39264
  Check306.part39232
  Check306.part39248)
  (FiniteChecks.interval_append test 39264 39280 39296
  Check306.part39264
  Check306.part39280)))
#print axioms Check306.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check307.part39296 : Interval test 39296 39312 :=
  interval_of_check _ 39296 16 (by decide +kernel)
theorem Check307.part39312 : Interval test 39312 39328 :=
  interval_of_check _ 39312 16 (by decide +kernel)
theorem Check307.part39328 : Interval test 39328 39344 :=
  interval_of_check _ 39328 16 (by decide +kernel)
theorem Check307.part39344 : Interval test 39344 39360 :=
  interval_of_check _ 39344 16 (by decide +kernel)
theorem Check307.part39360 : Interval test 39360 39376 :=
  interval_of_check _ 39360 16 (by decide +kernel)
theorem Check307.part39376 : Interval test 39376 39392 :=
  interval_of_check _ 39376 16 (by decide +kernel)
theorem Check307.part39392 : Interval test 39392 39408 :=
  interval_of_check _ 39392 16 (by decide +kernel)
theorem Check307.part39408 : Interval test 39408 39424 :=
  interval_of_check _ 39408 16 (by decide +kernel)
theorem Check307.checked : Interval test 39296 39424 :=
  (FiniteChecks.interval_append test 39296 39360 39424
  (FiniteChecks.interval_append test 39296 39328 39360
  (FiniteChecks.interval_append test 39296 39312 39328
  Check307.part39296
  Check307.part39312)
  (FiniteChecks.interval_append test 39328 39344 39360
  Check307.part39328
  Check307.part39344))
  (FiniteChecks.interval_append test 39360 39392 39424
  (FiniteChecks.interval_append test 39360 39376 39392
  Check307.part39360
  Check307.part39376)
  (FiniteChecks.interval_append test 39392 39408 39424
  Check307.part39392
  Check307.part39408)))
#print axioms Check307.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check308.part39424 : Interval test 39424 39440 :=
  interval_of_check _ 39424 16 (by decide +kernel)
theorem Check308.part39440 : Interval test 39440 39456 :=
  interval_of_check _ 39440 16 (by decide +kernel)
theorem Check308.part39456 : Interval test 39456 39472 :=
  interval_of_check _ 39456 16 (by decide +kernel)
theorem Check308.part39472 : Interval test 39472 39488 :=
  interval_of_check _ 39472 16 (by decide +kernel)
theorem Check308.part39488 : Interval test 39488 39504 :=
  interval_of_check _ 39488 16 (by decide +kernel)
theorem Check308.part39504 : Interval test 39504 39520 :=
  interval_of_check _ 39504 16 (by decide +kernel)
theorem Check308.part39520 : Interval test 39520 39536 :=
  interval_of_check _ 39520 16 (by decide +kernel)
theorem Check308.part39536 : Interval test 39536 39552 :=
  interval_of_check _ 39536 16 (by decide +kernel)
theorem Check308.checked : Interval test 39424 39552 :=
  (FiniteChecks.interval_append test 39424 39488 39552
  (FiniteChecks.interval_append test 39424 39456 39488
  (FiniteChecks.interval_append test 39424 39440 39456
  Check308.part39424
  Check308.part39440)
  (FiniteChecks.interval_append test 39456 39472 39488
  Check308.part39456
  Check308.part39472))
  (FiniteChecks.interval_append test 39488 39520 39552
  (FiniteChecks.interval_append test 39488 39504 39520
  Check308.part39488
  Check308.part39504)
  (FiniteChecks.interval_append test 39520 39536 39552
  Check308.part39520
  Check308.part39536)))
#print axioms Check308.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check309.part39552 : Interval test 39552 39568 :=
  interval_of_check _ 39552 16 (by decide +kernel)
theorem Check309.part39568 : Interval test 39568 39584 :=
  interval_of_check _ 39568 16 (by decide +kernel)
theorem Check309.part39584 : Interval test 39584 39600 :=
  interval_of_check _ 39584 16 (by decide +kernel)
theorem Check309.part39600 : Interval test 39600 39616 :=
  interval_of_check _ 39600 16 (by decide +kernel)
theorem Check309.part39616 : Interval test 39616 39632 :=
  interval_of_check _ 39616 16 (by decide +kernel)
theorem Check309.part39632 : Interval test 39632 39648 :=
  interval_of_check _ 39632 16 (by decide +kernel)
theorem Check309.part39648 : Interval test 39648 39664 :=
  interval_of_check _ 39648 16 (by decide +kernel)
theorem Check309.part39664 : Interval test 39664 39680 :=
  interval_of_check _ 39664 16 (by decide +kernel)
theorem Check309.checked : Interval test 39552 39680 :=
  (FiniteChecks.interval_append test 39552 39616 39680
  (FiniteChecks.interval_append test 39552 39584 39616
  (FiniteChecks.interval_append test 39552 39568 39584
  Check309.part39552
  Check309.part39568)
  (FiniteChecks.interval_append test 39584 39600 39616
  Check309.part39584
  Check309.part39600))
  (FiniteChecks.interval_append test 39616 39648 39680
  (FiniteChecks.interval_append test 39616 39632 39648
  Check309.part39616
  Check309.part39632)
  (FiniteChecks.interval_append test 39648 39664 39680
  Check309.part39648
  Check309.part39664)))
#print axioms Check309.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check310.part39680 : Interval test 39680 39696 :=
  interval_of_check _ 39680 16 (by decide +kernel)
theorem Check310.part39696 : Interval test 39696 39712 :=
  interval_of_check _ 39696 16 (by decide +kernel)
theorem Check310.part39712 : Interval test 39712 39728 :=
  interval_of_check _ 39712 16 (by decide +kernel)
theorem Check310.part39728 : Interval test 39728 39744 :=
  interval_of_check _ 39728 16 (by decide +kernel)
theorem Check310.part39744 : Interval test 39744 39760 :=
  interval_of_check _ 39744 16 (by decide +kernel)
theorem Check310.part39760 : Interval test 39760 39776 :=
  interval_of_check _ 39760 16 (by decide +kernel)
theorem Check310.part39776 : Interval test 39776 39792 :=
  interval_of_check _ 39776 16 (by decide +kernel)
theorem Check310.part39792 : Interval test 39792 39808 :=
  interval_of_check _ 39792 16 (by decide +kernel)
theorem Check310.checked : Interval test 39680 39808 :=
  (FiniteChecks.interval_append test 39680 39744 39808
  (FiniteChecks.interval_append test 39680 39712 39744
  (FiniteChecks.interval_append test 39680 39696 39712
  Check310.part39680
  Check310.part39696)
  (FiniteChecks.interval_append test 39712 39728 39744
  Check310.part39712
  Check310.part39728))
  (FiniteChecks.interval_append test 39744 39776 39808
  (FiniteChecks.interval_append test 39744 39760 39776
  Check310.part39744
  Check310.part39760)
  (FiniteChecks.interval_append test 39776 39792 39808
  Check310.part39776
  Check310.part39792)))
#print axioms Check310.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check311.part39808 : Interval test 39808 39824 :=
  interval_of_check _ 39808 16 (by decide +kernel)
theorem Check311.part39824 : Interval test 39824 39840 :=
  interval_of_check _ 39824 16 (by decide +kernel)
theorem Check311.part39840 : Interval test 39840 39856 :=
  interval_of_check _ 39840 16 (by decide +kernel)
theorem Check311.part39856 : Interval test 39856 39872 :=
  interval_of_check _ 39856 16 (by decide +kernel)
theorem Check311.part39872 : Interval test 39872 39888 :=
  interval_of_check _ 39872 16 (by decide +kernel)
theorem Check311.part39888 : Interval test 39888 39904 :=
  interval_of_check _ 39888 16 (by decide +kernel)
theorem Check311.part39904 : Interval test 39904 39920 :=
  interval_of_check _ 39904 16 (by decide +kernel)
theorem Check311.part39920 : Interval test 39920 39936 :=
  interval_of_check _ 39920 16 (by decide +kernel)
theorem Check311.checked : Interval test 39808 39936 :=
  (FiniteChecks.interval_append test 39808 39872 39936
  (FiniteChecks.interval_append test 39808 39840 39872
  (FiniteChecks.interval_append test 39808 39824 39840
  Check311.part39808
  Check311.part39824)
  (FiniteChecks.interval_append test 39840 39856 39872
  Check311.part39840
  Check311.part39856))
  (FiniteChecks.interval_append test 39872 39904 39936
  (FiniteChecks.interval_append test 39872 39888 39904
  Check311.part39872
  Check311.part39888)
  (FiniteChecks.interval_append test 39904 39920 39936
  Check311.part39904
  Check311.part39920)))
#print axioms Check311.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check312.part39936 : Interval test 39936 39952 :=
  interval_of_check _ 39936 16 (by decide +kernel)
theorem Check312.part39952 : Interval test 39952 39968 :=
  interval_of_check _ 39952 16 (by decide +kernel)
theorem Check312.part39968 : Interval test 39968 39984 :=
  interval_of_check _ 39968 16 (by decide +kernel)
theorem Check312.part39984 : Interval test 39984 40000 :=
  interval_of_check _ 39984 16 (by decide +kernel)
theorem Check312.part40000 : Interval test 40000 40016 :=
  interval_of_check _ 40000 16 (by decide +kernel)
theorem Check312.part40016 : Interval test 40016 40032 :=
  interval_of_check _ 40016 16 (by decide +kernel)
theorem Check312.part40032 : Interval test 40032 40048 :=
  interval_of_check _ 40032 16 (by decide +kernel)
theorem Check312.part40048 : Interval test 40048 40064 :=
  interval_of_check _ 40048 16 (by decide +kernel)
theorem Check312.checked : Interval test 39936 40064 :=
  (FiniteChecks.interval_append test 39936 40000 40064
  (FiniteChecks.interval_append test 39936 39968 40000
  (FiniteChecks.interval_append test 39936 39952 39968
  Check312.part39936
  Check312.part39952)
  (FiniteChecks.interval_append test 39968 39984 40000
  Check312.part39968
  Check312.part39984))
  (FiniteChecks.interval_append test 40000 40032 40064
  (FiniteChecks.interval_append test 40000 40016 40032
  Check312.part40000
  Check312.part40016)
  (FiniteChecks.interval_append test 40032 40048 40064
  Check312.part40032
  Check312.part40048)))
#print axioms Check312.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check313.part40064 : Interval test 40064 40080 :=
  interval_of_check _ 40064 16 (by decide +kernel)
theorem Check313.part40080 : Interval test 40080 40096 :=
  interval_of_check _ 40080 16 (by decide +kernel)
theorem Check313.part40096 : Interval test 40096 40112 :=
  interval_of_check _ 40096 16 (by decide +kernel)
theorem Check313.part40112 : Interval test 40112 40128 :=
  interval_of_check _ 40112 16 (by decide +kernel)
theorem Check313.part40128 : Interval test 40128 40144 :=
  interval_of_check _ 40128 16 (by decide +kernel)
theorem Check313.part40144 : Interval test 40144 40160 :=
  interval_of_check _ 40144 16 (by decide +kernel)
theorem Check313.part40160 : Interval test 40160 40176 :=
  interval_of_check _ 40160 16 (by decide +kernel)
theorem Check313.part40176 : Interval test 40176 40192 :=
  interval_of_check _ 40176 16 (by decide +kernel)
theorem Check313.checked : Interval test 40064 40192 :=
  (FiniteChecks.interval_append test 40064 40128 40192
  (FiniteChecks.interval_append test 40064 40096 40128
  (FiniteChecks.interval_append test 40064 40080 40096
  Check313.part40064
  Check313.part40080)
  (FiniteChecks.interval_append test 40096 40112 40128
  Check313.part40096
  Check313.part40112))
  (FiniteChecks.interval_append test 40128 40160 40192
  (FiniteChecks.interval_append test 40128 40144 40160
  Check313.part40128
  Check313.part40144)
  (FiniteChecks.interval_append test 40160 40176 40192
  Check313.part40160
  Check313.part40176)))
#print axioms Check313.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check314.part40192 : Interval test 40192 40208 :=
  interval_of_check _ 40192 16 (by decide +kernel)
theorem Check314.part40208 : Interval test 40208 40224 :=
  interval_of_check _ 40208 16 (by decide +kernel)
theorem Check314.part40224 : Interval test 40224 40240 :=
  interval_of_check _ 40224 16 (by decide +kernel)
theorem Check314.part40240 : Interval test 40240 40256 :=
  interval_of_check _ 40240 16 (by decide +kernel)
theorem Check314.part40256 : Interval test 40256 40272 :=
  interval_of_check _ 40256 16 (by decide +kernel)
theorem Check314.part40272 : Interval test 40272 40288 :=
  interval_of_check _ 40272 16 (by decide +kernel)
theorem Check314.part40288 : Interval test 40288 40304 :=
  interval_of_check _ 40288 16 (by decide +kernel)
theorem Check314.part40304 : Interval test 40304 40320 :=
  interval_of_check _ 40304 16 (by decide +kernel)
theorem Check314.checked : Interval test 40192 40320 :=
  (FiniteChecks.interval_append test 40192 40256 40320
  (FiniteChecks.interval_append test 40192 40224 40256
  (FiniteChecks.interval_append test 40192 40208 40224
  Check314.part40192
  Check314.part40208)
  (FiniteChecks.interval_append test 40224 40240 40256
  Check314.part40224
  Check314.part40240))
  (FiniteChecks.interval_append test 40256 40288 40320
  (FiniteChecks.interval_append test 40256 40272 40288
  Check314.part40256
  Check314.part40272)
  (FiniteChecks.interval_append test 40288 40304 40320
  Check314.part40288
  Check314.part40304)))
#print axioms Check314.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check315.part40320 : Interval test 40320 40336 :=
  interval_of_check _ 40320 16 (by decide +kernel)
theorem Check315.part40336 : Interval test 40336 40352 :=
  interval_of_check _ 40336 16 (by decide +kernel)
theorem Check315.part40352 : Interval test 40352 40368 :=
  interval_of_check _ 40352 16 (by decide +kernel)
theorem Check315.part40368 : Interval test 40368 40384 :=
  interval_of_check _ 40368 16 (by decide +kernel)
theorem Check315.part40384 : Interval test 40384 40400 :=
  interval_of_check _ 40384 16 (by decide +kernel)
theorem Check315.part40400 : Interval test 40400 40416 :=
  interval_of_check _ 40400 16 (by decide +kernel)
theorem Check315.part40416 : Interval test 40416 40432 :=
  interval_of_check _ 40416 16 (by decide +kernel)
theorem Check315.part40432 : Interval test 40432 40448 :=
  interval_of_check _ 40432 16 (by decide +kernel)
theorem Check315.checked : Interval test 40320 40448 :=
  (FiniteChecks.interval_append test 40320 40384 40448
  (FiniteChecks.interval_append test 40320 40352 40384
  (FiniteChecks.interval_append test 40320 40336 40352
  Check315.part40320
  Check315.part40336)
  (FiniteChecks.interval_append test 40352 40368 40384
  Check315.part40352
  Check315.part40368))
  (FiniteChecks.interval_append test 40384 40416 40448
  (FiniteChecks.interval_append test 40384 40400 40416
  Check315.part40384
  Check315.part40400)
  (FiniteChecks.interval_append test 40416 40432 40448
  Check315.part40416
  Check315.part40432)))
#print axioms Check315.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check316.part40448 : Interval test 40448 40464 :=
  interval_of_check _ 40448 16 (by decide +kernel)
theorem Check316.part40464 : Interval test 40464 40480 :=
  interval_of_check _ 40464 16 (by decide +kernel)
theorem Check316.part40480 : Interval test 40480 40496 :=
  interval_of_check _ 40480 16 (by decide +kernel)
theorem Check316.part40496 : Interval test 40496 40512 :=
  interval_of_check _ 40496 16 (by decide +kernel)
theorem Check316.part40512 : Interval test 40512 40528 :=
  interval_of_check _ 40512 16 (by decide +kernel)
theorem Check316.part40528 : Interval test 40528 40544 :=
  interval_of_check _ 40528 16 (by decide +kernel)
theorem Check316.part40544 : Interval test 40544 40560 :=
  interval_of_check _ 40544 16 (by decide +kernel)
theorem Check316.part40560 : Interval test 40560 40576 :=
  interval_of_check _ 40560 16 (by decide +kernel)
theorem Check316.checked : Interval test 40448 40576 :=
  (FiniteChecks.interval_append test 40448 40512 40576
  (FiniteChecks.interval_append test 40448 40480 40512
  (FiniteChecks.interval_append test 40448 40464 40480
  Check316.part40448
  Check316.part40464)
  (FiniteChecks.interval_append test 40480 40496 40512
  Check316.part40480
  Check316.part40496))
  (FiniteChecks.interval_append test 40512 40544 40576
  (FiniteChecks.interval_append test 40512 40528 40544
  Check316.part40512
  Check316.part40528)
  (FiniteChecks.interval_append test 40544 40560 40576
  Check316.part40544
  Check316.part40560)))
#print axioms Check316.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check317.part40576 : Interval test 40576 40592 :=
  interval_of_check _ 40576 16 (by decide +kernel)
theorem Check317.part40592 : Interval test 40592 40608 :=
  interval_of_check _ 40592 16 (by decide +kernel)
theorem Check317.part40608 : Interval test 40608 40624 :=
  interval_of_check _ 40608 16 (by decide +kernel)
theorem Check317.part40624 : Interval test 40624 40640 :=
  interval_of_check _ 40624 16 (by decide +kernel)
theorem Check317.part40640 : Interval test 40640 40656 :=
  interval_of_check _ 40640 16 (by decide +kernel)
theorem Check317.part40656 : Interval test 40656 40672 :=
  interval_of_check _ 40656 16 (by decide +kernel)
theorem Check317.part40672 : Interval test 40672 40688 :=
  interval_of_check _ 40672 16 (by decide +kernel)
theorem Check317.part40688 : Interval test 40688 40704 :=
  interval_of_check _ 40688 16 (by decide +kernel)
theorem Check317.checked : Interval test 40576 40704 :=
  (FiniteChecks.interval_append test 40576 40640 40704
  (FiniteChecks.interval_append test 40576 40608 40640
  (FiniteChecks.interval_append test 40576 40592 40608
  Check317.part40576
  Check317.part40592)
  (FiniteChecks.interval_append test 40608 40624 40640
  Check317.part40608
  Check317.part40624))
  (FiniteChecks.interval_append test 40640 40672 40704
  (FiniteChecks.interval_append test 40640 40656 40672
  Check317.part40640
  Check317.part40656)
  (FiniteChecks.interval_append test 40672 40688 40704
  Check317.part40672
  Check317.part40688)))
#print axioms Check317.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check318.part40704 : Interval test 40704 40720 :=
  interval_of_check _ 40704 16 (by decide +kernel)
theorem Check318.part40720 : Interval test 40720 40736 :=
  interval_of_check _ 40720 16 (by decide +kernel)
theorem Check318.part40736 : Interval test 40736 40752 :=
  interval_of_check _ 40736 16 (by decide +kernel)
theorem Check318.part40752 : Interval test 40752 40768 :=
  interval_of_check _ 40752 16 (by decide +kernel)
theorem Check318.part40768 : Interval test 40768 40784 :=
  interval_of_check _ 40768 16 (by decide +kernel)
theorem Check318.part40784 : Interval test 40784 40800 :=
  interval_of_check _ 40784 16 (by decide +kernel)
theorem Check318.part40800 : Interval test 40800 40816 :=
  interval_of_check _ 40800 16 (by decide +kernel)
theorem Check318.part40816 : Interval test 40816 40832 :=
  interval_of_check _ 40816 16 (by decide +kernel)
theorem Check318.checked : Interval test 40704 40832 :=
  (FiniteChecks.interval_append test 40704 40768 40832
  (FiniteChecks.interval_append test 40704 40736 40768
  (FiniteChecks.interval_append test 40704 40720 40736
  Check318.part40704
  Check318.part40720)
  (FiniteChecks.interval_append test 40736 40752 40768
  Check318.part40736
  Check318.part40752))
  (FiniteChecks.interval_append test 40768 40800 40832
  (FiniteChecks.interval_append test 40768 40784 40800
  Check318.part40768
  Check318.part40784)
  (FiniteChecks.interval_append test 40800 40816 40832
  Check318.part40800
  Check318.part40816)))
#print axioms Check318.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check319.part40832 : Interval test 40832 40848 :=
  interval_of_check _ 40832 16 (by decide +kernel)
theorem Check319.part40848 : Interval test 40848 40864 :=
  interval_of_check _ 40848 16 (by decide +kernel)
theorem Check319.part40864 : Interval test 40864 40880 :=
  interval_of_check _ 40864 16 (by decide +kernel)
theorem Check319.part40880 : Interval test 40880 40896 :=
  interval_of_check _ 40880 16 (by decide +kernel)
theorem Check319.part40896 : Interval test 40896 40912 :=
  interval_of_check _ 40896 16 (by decide +kernel)
theorem Check319.part40912 : Interval test 40912 40928 :=
  interval_of_check _ 40912 16 (by decide +kernel)
theorem Check319.part40928 : Interval test 40928 40944 :=
  interval_of_check _ 40928 16 (by decide +kernel)
theorem Check319.part40944 : Interval test 40944 40960 :=
  interval_of_check _ 40944 16 (by decide +kernel)
theorem Check319.checked : Interval test 40832 40960 :=
  (FiniteChecks.interval_append test 40832 40896 40960
  (FiniteChecks.interval_append test 40832 40864 40896
  (FiniteChecks.interval_append test 40832 40848 40864
  Check319.part40832
  Check319.part40848)
  (FiniteChecks.interval_append test 40864 40880 40896
  Check319.part40864
  Check319.part40880))
  (FiniteChecks.interval_append test 40896 40928 40960
  (FiniteChecks.interval_append test 40896 40912 40928
  Check319.part40896
  Check319.part40912)
  (FiniteChecks.interval_append test 40928 40944 40960
  Check319.part40928
  Check319.part40944)))
#print axioms Check319.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
