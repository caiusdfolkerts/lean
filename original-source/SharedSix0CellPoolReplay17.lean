module
prelude
public import SharedSix0CellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check340.part43520 : Interval test 43520 43536 :=
  interval_of_check _ 43520 16 (by decide +kernel)
theorem Check340.part43536 : Interval test 43536 43552 :=
  interval_of_check _ 43536 16 (by decide +kernel)
theorem Check340.part43552 : Interval test 43552 43568 :=
  interval_of_check _ 43552 16 (by decide +kernel)
theorem Check340.part43568 : Interval test 43568 43584 :=
  interval_of_check _ 43568 16 (by decide +kernel)
theorem Check340.part43584 : Interval test 43584 43600 :=
  interval_of_check _ 43584 16 (by decide +kernel)
theorem Check340.part43600 : Interval test 43600 43616 :=
  interval_of_check _ 43600 16 (by decide +kernel)
theorem Check340.part43616 : Interval test 43616 43632 :=
  interval_of_check _ 43616 16 (by decide +kernel)
theorem Check340.part43632 : Interval test 43632 43648 :=
  interval_of_check _ 43632 16 (by decide +kernel)
theorem Check340.checked : Interval test 43520 43648 :=
  (FiniteChecks.interval_append test 43520 43584 43648
  (FiniteChecks.interval_append test 43520 43552 43584
  (FiniteChecks.interval_append test 43520 43536 43552
  Check340.part43520
  Check340.part43536)
  (FiniteChecks.interval_append test 43552 43568 43584
  Check340.part43552
  Check340.part43568))
  (FiniteChecks.interval_append test 43584 43616 43648
  (FiniteChecks.interval_append test 43584 43600 43616
  Check340.part43584
  Check340.part43600)
  (FiniteChecks.interval_append test 43616 43632 43648
  Check340.part43616
  Check340.part43632)))
#print axioms Check340.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check341.part43648 : Interval test 43648 43664 :=
  interval_of_check _ 43648 16 (by decide +kernel)
theorem Check341.part43664 : Interval test 43664 43680 :=
  interval_of_check _ 43664 16 (by decide +kernel)
theorem Check341.part43680 : Interval test 43680 43696 :=
  interval_of_check _ 43680 16 (by decide +kernel)
theorem Check341.part43696 : Interval test 43696 43712 :=
  interval_of_check _ 43696 16 (by decide +kernel)
theorem Check341.part43712 : Interval test 43712 43728 :=
  interval_of_check _ 43712 16 (by decide +kernel)
theorem Check341.part43728 : Interval test 43728 43744 :=
  interval_of_check _ 43728 16 (by decide +kernel)
theorem Check341.part43744 : Interval test 43744 43760 :=
  interval_of_check _ 43744 16 (by decide +kernel)
theorem Check341.part43760 : Interval test 43760 43776 :=
  interval_of_check _ 43760 16 (by decide +kernel)
theorem Check341.checked : Interval test 43648 43776 :=
  (FiniteChecks.interval_append test 43648 43712 43776
  (FiniteChecks.interval_append test 43648 43680 43712
  (FiniteChecks.interval_append test 43648 43664 43680
  Check341.part43648
  Check341.part43664)
  (FiniteChecks.interval_append test 43680 43696 43712
  Check341.part43680
  Check341.part43696))
  (FiniteChecks.interval_append test 43712 43744 43776
  (FiniteChecks.interval_append test 43712 43728 43744
  Check341.part43712
  Check341.part43728)
  (FiniteChecks.interval_append test 43744 43760 43776
  Check341.part43744
  Check341.part43760)))
#print axioms Check341.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check342.part43776 : Interval test 43776 43792 :=
  interval_of_check _ 43776 16 (by decide +kernel)
theorem Check342.part43792 : Interval test 43792 43808 :=
  interval_of_check _ 43792 16 (by decide +kernel)
theorem Check342.part43808 : Interval test 43808 43824 :=
  interval_of_check _ 43808 16 (by decide +kernel)
theorem Check342.part43824 : Interval test 43824 43840 :=
  interval_of_check _ 43824 16 (by decide +kernel)
theorem Check342.part43840 : Interval test 43840 43856 :=
  interval_of_check _ 43840 16 (by decide +kernel)
theorem Check342.part43856 : Interval test 43856 43872 :=
  interval_of_check _ 43856 16 (by decide +kernel)
theorem Check342.part43872 : Interval test 43872 43888 :=
  interval_of_check _ 43872 16 (by decide +kernel)
theorem Check342.part43888 : Interval test 43888 43904 :=
  interval_of_check _ 43888 16 (by decide +kernel)
theorem Check342.checked : Interval test 43776 43904 :=
  (FiniteChecks.interval_append test 43776 43840 43904
  (FiniteChecks.interval_append test 43776 43808 43840
  (FiniteChecks.interval_append test 43776 43792 43808
  Check342.part43776
  Check342.part43792)
  (FiniteChecks.interval_append test 43808 43824 43840
  Check342.part43808
  Check342.part43824))
  (FiniteChecks.interval_append test 43840 43872 43904
  (FiniteChecks.interval_append test 43840 43856 43872
  Check342.part43840
  Check342.part43856)
  (FiniteChecks.interval_append test 43872 43888 43904
  Check342.part43872
  Check342.part43888)))
#print axioms Check342.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check343.part43904 : Interval test 43904 43920 :=
  interval_of_check _ 43904 16 (by decide +kernel)
theorem Check343.part43920 : Interval test 43920 43936 :=
  interval_of_check _ 43920 16 (by decide +kernel)
theorem Check343.part43936 : Interval test 43936 43952 :=
  interval_of_check _ 43936 16 (by decide +kernel)
theorem Check343.part43952 : Interval test 43952 43968 :=
  interval_of_check _ 43952 16 (by decide +kernel)
theorem Check343.part43968 : Interval test 43968 43984 :=
  interval_of_check _ 43968 16 (by decide +kernel)
theorem Check343.part43984 : Interval test 43984 44000 :=
  interval_of_check _ 43984 16 (by decide +kernel)
theorem Check343.part44000 : Interval test 44000 44016 :=
  interval_of_check _ 44000 16 (by decide +kernel)
theorem Check343.part44016 : Interval test 44016 44032 :=
  interval_of_check _ 44016 16 (by decide +kernel)
theorem Check343.checked : Interval test 43904 44032 :=
  (FiniteChecks.interval_append test 43904 43968 44032
  (FiniteChecks.interval_append test 43904 43936 43968
  (FiniteChecks.interval_append test 43904 43920 43936
  Check343.part43904
  Check343.part43920)
  (FiniteChecks.interval_append test 43936 43952 43968
  Check343.part43936
  Check343.part43952))
  (FiniteChecks.interval_append test 43968 44000 44032
  (FiniteChecks.interval_append test 43968 43984 44000
  Check343.part43968
  Check343.part43984)
  (FiniteChecks.interval_append test 44000 44016 44032
  Check343.part44000
  Check343.part44016)))
#print axioms Check343.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check344.part44032 : Interval test 44032 44048 :=
  interval_of_check _ 44032 16 (by decide +kernel)
theorem Check344.part44048 : Interval test 44048 44064 :=
  interval_of_check _ 44048 16 (by decide +kernel)
theorem Check344.part44064 : Interval test 44064 44080 :=
  interval_of_check _ 44064 16 (by decide +kernel)
theorem Check344.part44080 : Interval test 44080 44096 :=
  interval_of_check _ 44080 16 (by decide +kernel)
theorem Check344.part44096 : Interval test 44096 44112 :=
  interval_of_check _ 44096 16 (by decide +kernel)
theorem Check344.part44112 : Interval test 44112 44128 :=
  interval_of_check _ 44112 16 (by decide +kernel)
theorem Check344.part44128 : Interval test 44128 44144 :=
  interval_of_check _ 44128 16 (by decide +kernel)
theorem Check344.part44144 : Interval test 44144 44160 :=
  interval_of_check _ 44144 16 (by decide +kernel)
theorem Check344.checked : Interval test 44032 44160 :=
  (FiniteChecks.interval_append test 44032 44096 44160
  (FiniteChecks.interval_append test 44032 44064 44096
  (FiniteChecks.interval_append test 44032 44048 44064
  Check344.part44032
  Check344.part44048)
  (FiniteChecks.interval_append test 44064 44080 44096
  Check344.part44064
  Check344.part44080))
  (FiniteChecks.interval_append test 44096 44128 44160
  (FiniteChecks.interval_append test 44096 44112 44128
  Check344.part44096
  Check344.part44112)
  (FiniteChecks.interval_append test 44128 44144 44160
  Check344.part44128
  Check344.part44144)))
#print axioms Check344.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check345.part44160 : Interval test 44160 44176 :=
  interval_of_check _ 44160 16 (by decide +kernel)
theorem Check345.part44176 : Interval test 44176 44192 :=
  interval_of_check _ 44176 16 (by decide +kernel)
theorem Check345.part44192 : Interval test 44192 44208 :=
  interval_of_check _ 44192 16 (by decide +kernel)
theorem Check345.part44208 : Interval test 44208 44224 :=
  interval_of_check _ 44208 16 (by decide +kernel)
theorem Check345.part44224 : Interval test 44224 44240 :=
  interval_of_check _ 44224 16 (by decide +kernel)
theorem Check345.part44240 : Interval test 44240 44256 :=
  interval_of_check _ 44240 16 (by decide +kernel)
theorem Check345.part44256 : Interval test 44256 44272 :=
  interval_of_check _ 44256 16 (by decide +kernel)
theorem Check345.part44272 : Interval test 44272 44288 :=
  interval_of_check _ 44272 16 (by decide +kernel)
theorem Check345.checked : Interval test 44160 44288 :=
  (FiniteChecks.interval_append test 44160 44224 44288
  (FiniteChecks.interval_append test 44160 44192 44224
  (FiniteChecks.interval_append test 44160 44176 44192
  Check345.part44160
  Check345.part44176)
  (FiniteChecks.interval_append test 44192 44208 44224
  Check345.part44192
  Check345.part44208))
  (FiniteChecks.interval_append test 44224 44256 44288
  (FiniteChecks.interval_append test 44224 44240 44256
  Check345.part44224
  Check345.part44240)
  (FiniteChecks.interval_append test 44256 44272 44288
  Check345.part44256
  Check345.part44272)))
#print axioms Check345.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check346.part44288 : Interval test 44288 44304 :=
  interval_of_check _ 44288 16 (by decide +kernel)
theorem Check346.part44304 : Interval test 44304 44310 :=
  interval_of_check _ 44304 6 (by decide +kernel)
theorem Check346.checked : Interval test 44288 44310 :=
  (FiniteChecks.interval_append test 44288 44304 44310
  Check346.part44288
  Check346.part44304)
#print axioms Check346.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
