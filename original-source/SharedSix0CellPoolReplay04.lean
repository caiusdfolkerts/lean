module
prelude
public import SharedSix0CellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check080.part10240 : Interval test 10240 10256 :=
  interval_of_check _ 10240 16 (by decide +kernel)
theorem Check080.part10256 : Interval test 10256 10272 :=
  interval_of_check _ 10256 16 (by decide +kernel)
theorem Check080.part10272 : Interval test 10272 10288 :=
  interval_of_check _ 10272 16 (by decide +kernel)
theorem Check080.part10288 : Interval test 10288 10304 :=
  interval_of_check _ 10288 16 (by decide +kernel)
theorem Check080.part10304 : Interval test 10304 10320 :=
  interval_of_check _ 10304 16 (by decide +kernel)
theorem Check080.part10320 : Interval test 10320 10336 :=
  interval_of_check _ 10320 16 (by decide +kernel)
theorem Check080.part10336 : Interval test 10336 10352 :=
  interval_of_check _ 10336 16 (by decide +kernel)
theorem Check080.part10352 : Interval test 10352 10368 :=
  interval_of_check _ 10352 16 (by decide +kernel)
theorem Check080.checked : Interval test 10240 10368 :=
  (FiniteChecks.interval_append test 10240 10304 10368
  (FiniteChecks.interval_append test 10240 10272 10304
  (FiniteChecks.interval_append test 10240 10256 10272
  Check080.part10240
  Check080.part10256)
  (FiniteChecks.interval_append test 10272 10288 10304
  Check080.part10272
  Check080.part10288))
  (FiniteChecks.interval_append test 10304 10336 10368
  (FiniteChecks.interval_append test 10304 10320 10336
  Check080.part10304
  Check080.part10320)
  (FiniteChecks.interval_append test 10336 10352 10368
  Check080.part10336
  Check080.part10352)))
#print axioms Check080.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check081.part10368 : Interval test 10368 10384 :=
  interval_of_check _ 10368 16 (by decide +kernel)
theorem Check081.part10384 : Interval test 10384 10400 :=
  interval_of_check _ 10384 16 (by decide +kernel)
theorem Check081.part10400 : Interval test 10400 10416 :=
  interval_of_check _ 10400 16 (by decide +kernel)
theorem Check081.part10416 : Interval test 10416 10432 :=
  interval_of_check _ 10416 16 (by decide +kernel)
theorem Check081.part10432 : Interval test 10432 10448 :=
  interval_of_check _ 10432 16 (by decide +kernel)
theorem Check081.part10448 : Interval test 10448 10464 :=
  interval_of_check _ 10448 16 (by decide +kernel)
theorem Check081.part10464 : Interval test 10464 10480 :=
  interval_of_check _ 10464 16 (by decide +kernel)
theorem Check081.part10480 : Interval test 10480 10496 :=
  interval_of_check _ 10480 16 (by decide +kernel)
theorem Check081.checked : Interval test 10368 10496 :=
  (FiniteChecks.interval_append test 10368 10432 10496
  (FiniteChecks.interval_append test 10368 10400 10432
  (FiniteChecks.interval_append test 10368 10384 10400
  Check081.part10368
  Check081.part10384)
  (FiniteChecks.interval_append test 10400 10416 10432
  Check081.part10400
  Check081.part10416))
  (FiniteChecks.interval_append test 10432 10464 10496
  (FiniteChecks.interval_append test 10432 10448 10464
  Check081.part10432
  Check081.part10448)
  (FiniteChecks.interval_append test 10464 10480 10496
  Check081.part10464
  Check081.part10480)))
#print axioms Check081.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check082.part10496 : Interval test 10496 10512 :=
  interval_of_check _ 10496 16 (by decide +kernel)
theorem Check082.part10512 : Interval test 10512 10528 :=
  interval_of_check _ 10512 16 (by decide +kernel)
theorem Check082.part10528 : Interval test 10528 10544 :=
  interval_of_check _ 10528 16 (by decide +kernel)
theorem Check082.part10544 : Interval test 10544 10560 :=
  interval_of_check _ 10544 16 (by decide +kernel)
theorem Check082.part10560 : Interval test 10560 10576 :=
  interval_of_check _ 10560 16 (by decide +kernel)
theorem Check082.part10576 : Interval test 10576 10592 :=
  interval_of_check _ 10576 16 (by decide +kernel)
theorem Check082.part10592 : Interval test 10592 10608 :=
  interval_of_check _ 10592 16 (by decide +kernel)
theorem Check082.part10608 : Interval test 10608 10624 :=
  interval_of_check _ 10608 16 (by decide +kernel)
theorem Check082.checked : Interval test 10496 10624 :=
  (FiniteChecks.interval_append test 10496 10560 10624
  (FiniteChecks.interval_append test 10496 10528 10560
  (FiniteChecks.interval_append test 10496 10512 10528
  Check082.part10496
  Check082.part10512)
  (FiniteChecks.interval_append test 10528 10544 10560
  Check082.part10528
  Check082.part10544))
  (FiniteChecks.interval_append test 10560 10592 10624
  (FiniteChecks.interval_append test 10560 10576 10592
  Check082.part10560
  Check082.part10576)
  (FiniteChecks.interval_append test 10592 10608 10624
  Check082.part10592
  Check082.part10608)))
#print axioms Check082.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check083.part10624 : Interval test 10624 10640 :=
  interval_of_check _ 10624 16 (by decide +kernel)
theorem Check083.part10640 : Interval test 10640 10656 :=
  interval_of_check _ 10640 16 (by decide +kernel)
theorem Check083.part10656 : Interval test 10656 10672 :=
  interval_of_check _ 10656 16 (by decide +kernel)
theorem Check083.part10672 : Interval test 10672 10688 :=
  interval_of_check _ 10672 16 (by decide +kernel)
theorem Check083.part10688 : Interval test 10688 10704 :=
  interval_of_check _ 10688 16 (by decide +kernel)
theorem Check083.part10704 : Interval test 10704 10720 :=
  interval_of_check _ 10704 16 (by decide +kernel)
theorem Check083.part10720 : Interval test 10720 10736 :=
  interval_of_check _ 10720 16 (by decide +kernel)
theorem Check083.part10736 : Interval test 10736 10752 :=
  interval_of_check _ 10736 16 (by decide +kernel)
theorem Check083.checked : Interval test 10624 10752 :=
  (FiniteChecks.interval_append test 10624 10688 10752
  (FiniteChecks.interval_append test 10624 10656 10688
  (FiniteChecks.interval_append test 10624 10640 10656
  Check083.part10624
  Check083.part10640)
  (FiniteChecks.interval_append test 10656 10672 10688
  Check083.part10656
  Check083.part10672))
  (FiniteChecks.interval_append test 10688 10720 10752
  (FiniteChecks.interval_append test 10688 10704 10720
  Check083.part10688
  Check083.part10704)
  (FiniteChecks.interval_append test 10720 10736 10752
  Check083.part10720
  Check083.part10736)))
#print axioms Check083.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check084.part10752 : Interval test 10752 10768 :=
  interval_of_check _ 10752 16 (by decide +kernel)
theorem Check084.part10768 : Interval test 10768 10784 :=
  interval_of_check _ 10768 16 (by decide +kernel)
theorem Check084.part10784 : Interval test 10784 10800 :=
  interval_of_check _ 10784 16 (by decide +kernel)
theorem Check084.part10800 : Interval test 10800 10816 :=
  interval_of_check _ 10800 16 (by decide +kernel)
theorem Check084.part10816 : Interval test 10816 10832 :=
  interval_of_check _ 10816 16 (by decide +kernel)
theorem Check084.part10832 : Interval test 10832 10848 :=
  interval_of_check _ 10832 16 (by decide +kernel)
theorem Check084.part10848 : Interval test 10848 10864 :=
  interval_of_check _ 10848 16 (by decide +kernel)
theorem Check084.part10864 : Interval test 10864 10880 :=
  interval_of_check _ 10864 16 (by decide +kernel)
theorem Check084.checked : Interval test 10752 10880 :=
  (FiniteChecks.interval_append test 10752 10816 10880
  (FiniteChecks.interval_append test 10752 10784 10816
  (FiniteChecks.interval_append test 10752 10768 10784
  Check084.part10752
  Check084.part10768)
  (FiniteChecks.interval_append test 10784 10800 10816
  Check084.part10784
  Check084.part10800))
  (FiniteChecks.interval_append test 10816 10848 10880
  (FiniteChecks.interval_append test 10816 10832 10848
  Check084.part10816
  Check084.part10832)
  (FiniteChecks.interval_append test 10848 10864 10880
  Check084.part10848
  Check084.part10864)))
#print axioms Check084.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check085.part10880 : Interval test 10880 10896 :=
  interval_of_check _ 10880 16 (by decide +kernel)
theorem Check085.part10896 : Interval test 10896 10912 :=
  interval_of_check _ 10896 16 (by decide +kernel)
theorem Check085.part10912 : Interval test 10912 10928 :=
  interval_of_check _ 10912 16 (by decide +kernel)
theorem Check085.part10928 : Interval test 10928 10944 :=
  interval_of_check _ 10928 16 (by decide +kernel)
theorem Check085.part10944 : Interval test 10944 10960 :=
  interval_of_check _ 10944 16 (by decide +kernel)
theorem Check085.part10960 : Interval test 10960 10976 :=
  interval_of_check _ 10960 16 (by decide +kernel)
theorem Check085.part10976 : Interval test 10976 10992 :=
  interval_of_check _ 10976 16 (by decide +kernel)
theorem Check085.part10992 : Interval test 10992 11008 :=
  interval_of_check _ 10992 16 (by decide +kernel)
theorem Check085.checked : Interval test 10880 11008 :=
  (FiniteChecks.interval_append test 10880 10944 11008
  (FiniteChecks.interval_append test 10880 10912 10944
  (FiniteChecks.interval_append test 10880 10896 10912
  Check085.part10880
  Check085.part10896)
  (FiniteChecks.interval_append test 10912 10928 10944
  Check085.part10912
  Check085.part10928))
  (FiniteChecks.interval_append test 10944 10976 11008
  (FiniteChecks.interval_append test 10944 10960 10976
  Check085.part10944
  Check085.part10960)
  (FiniteChecks.interval_append test 10976 10992 11008
  Check085.part10976
  Check085.part10992)))
#print axioms Check085.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check086.part11008 : Interval test 11008 11024 :=
  interval_of_check _ 11008 16 (by decide +kernel)
theorem Check086.part11024 : Interval test 11024 11040 :=
  interval_of_check _ 11024 16 (by decide +kernel)
theorem Check086.part11040 : Interval test 11040 11056 :=
  interval_of_check _ 11040 16 (by decide +kernel)
theorem Check086.part11056 : Interval test 11056 11072 :=
  interval_of_check _ 11056 16 (by decide +kernel)
theorem Check086.part11072 : Interval test 11072 11088 :=
  interval_of_check _ 11072 16 (by decide +kernel)
theorem Check086.part11088 : Interval test 11088 11104 :=
  interval_of_check _ 11088 16 (by decide +kernel)
theorem Check086.part11104 : Interval test 11104 11120 :=
  interval_of_check _ 11104 16 (by decide +kernel)
theorem Check086.part11120 : Interval test 11120 11136 :=
  interval_of_check _ 11120 16 (by decide +kernel)
theorem Check086.checked : Interval test 11008 11136 :=
  (FiniteChecks.interval_append test 11008 11072 11136
  (FiniteChecks.interval_append test 11008 11040 11072
  (FiniteChecks.interval_append test 11008 11024 11040
  Check086.part11008
  Check086.part11024)
  (FiniteChecks.interval_append test 11040 11056 11072
  Check086.part11040
  Check086.part11056))
  (FiniteChecks.interval_append test 11072 11104 11136
  (FiniteChecks.interval_append test 11072 11088 11104
  Check086.part11072
  Check086.part11088)
  (FiniteChecks.interval_append test 11104 11120 11136
  Check086.part11104
  Check086.part11120)))
#print axioms Check086.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check087.part11136 : Interval test 11136 11152 :=
  interval_of_check _ 11136 16 (by decide +kernel)
theorem Check087.part11152 : Interval test 11152 11168 :=
  interval_of_check _ 11152 16 (by decide +kernel)
theorem Check087.part11168 : Interval test 11168 11184 :=
  interval_of_check _ 11168 16 (by decide +kernel)
theorem Check087.part11184 : Interval test 11184 11200 :=
  interval_of_check _ 11184 16 (by decide +kernel)
theorem Check087.part11200 : Interval test 11200 11216 :=
  interval_of_check _ 11200 16 (by decide +kernel)
theorem Check087.part11216 : Interval test 11216 11232 :=
  interval_of_check _ 11216 16 (by decide +kernel)
theorem Check087.part11232 : Interval test 11232 11248 :=
  interval_of_check _ 11232 16 (by decide +kernel)
theorem Check087.part11248 : Interval test 11248 11264 :=
  interval_of_check _ 11248 16 (by decide +kernel)
theorem Check087.checked : Interval test 11136 11264 :=
  (FiniteChecks.interval_append test 11136 11200 11264
  (FiniteChecks.interval_append test 11136 11168 11200
  (FiniteChecks.interval_append test 11136 11152 11168
  Check087.part11136
  Check087.part11152)
  (FiniteChecks.interval_append test 11168 11184 11200
  Check087.part11168
  Check087.part11184))
  (FiniteChecks.interval_append test 11200 11232 11264
  (FiniteChecks.interval_append test 11200 11216 11232
  Check087.part11200
  Check087.part11216)
  (FiniteChecks.interval_append test 11232 11248 11264
  Check087.part11232
  Check087.part11248)))
#print axioms Check087.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check088.part11264 : Interval test 11264 11280 :=
  interval_of_check _ 11264 16 (by decide +kernel)
theorem Check088.part11280 : Interval test 11280 11296 :=
  interval_of_check _ 11280 16 (by decide +kernel)
theorem Check088.part11296 : Interval test 11296 11312 :=
  interval_of_check _ 11296 16 (by decide +kernel)
theorem Check088.part11312 : Interval test 11312 11328 :=
  interval_of_check _ 11312 16 (by decide +kernel)
theorem Check088.part11328 : Interval test 11328 11344 :=
  interval_of_check _ 11328 16 (by decide +kernel)
theorem Check088.part11344 : Interval test 11344 11360 :=
  interval_of_check _ 11344 16 (by decide +kernel)
theorem Check088.part11360 : Interval test 11360 11376 :=
  interval_of_check _ 11360 16 (by decide +kernel)
theorem Check088.part11376 : Interval test 11376 11392 :=
  interval_of_check _ 11376 16 (by decide +kernel)
theorem Check088.checked : Interval test 11264 11392 :=
  (FiniteChecks.interval_append test 11264 11328 11392
  (FiniteChecks.interval_append test 11264 11296 11328
  (FiniteChecks.interval_append test 11264 11280 11296
  Check088.part11264
  Check088.part11280)
  (FiniteChecks.interval_append test 11296 11312 11328
  Check088.part11296
  Check088.part11312))
  (FiniteChecks.interval_append test 11328 11360 11392
  (FiniteChecks.interval_append test 11328 11344 11360
  Check088.part11328
  Check088.part11344)
  (FiniteChecks.interval_append test 11360 11376 11392
  Check088.part11360
  Check088.part11376)))
#print axioms Check088.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check089.part11392 : Interval test 11392 11408 :=
  interval_of_check _ 11392 16 (by decide +kernel)
theorem Check089.part11408 : Interval test 11408 11424 :=
  interval_of_check _ 11408 16 (by decide +kernel)
theorem Check089.part11424 : Interval test 11424 11440 :=
  interval_of_check _ 11424 16 (by decide +kernel)
theorem Check089.part11440 : Interval test 11440 11456 :=
  interval_of_check _ 11440 16 (by decide +kernel)
theorem Check089.part11456 : Interval test 11456 11472 :=
  interval_of_check _ 11456 16 (by decide +kernel)
theorem Check089.part11472 : Interval test 11472 11488 :=
  interval_of_check _ 11472 16 (by decide +kernel)
theorem Check089.part11488 : Interval test 11488 11504 :=
  interval_of_check _ 11488 16 (by decide +kernel)
theorem Check089.part11504 : Interval test 11504 11520 :=
  interval_of_check _ 11504 16 (by decide +kernel)
theorem Check089.checked : Interval test 11392 11520 :=
  (FiniteChecks.interval_append test 11392 11456 11520
  (FiniteChecks.interval_append test 11392 11424 11456
  (FiniteChecks.interval_append test 11392 11408 11424
  Check089.part11392
  Check089.part11408)
  (FiniteChecks.interval_append test 11424 11440 11456
  Check089.part11424
  Check089.part11440))
  (FiniteChecks.interval_append test 11456 11488 11520
  (FiniteChecks.interval_append test 11456 11472 11488
  Check089.part11456
  Check089.part11472)
  (FiniteChecks.interval_append test 11488 11504 11520
  Check089.part11488
  Check089.part11504)))
#print axioms Check089.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check090.part11520 : Interval test 11520 11536 :=
  interval_of_check _ 11520 16 (by decide +kernel)
theorem Check090.part11536 : Interval test 11536 11552 :=
  interval_of_check _ 11536 16 (by decide +kernel)
theorem Check090.part11552 : Interval test 11552 11568 :=
  interval_of_check _ 11552 16 (by decide +kernel)
theorem Check090.part11568 : Interval test 11568 11584 :=
  interval_of_check _ 11568 16 (by decide +kernel)
theorem Check090.part11584 : Interval test 11584 11600 :=
  interval_of_check _ 11584 16 (by decide +kernel)
theorem Check090.part11600 : Interval test 11600 11616 :=
  interval_of_check _ 11600 16 (by decide +kernel)
theorem Check090.part11616 : Interval test 11616 11632 :=
  interval_of_check _ 11616 16 (by decide +kernel)
theorem Check090.part11632 : Interval test 11632 11648 :=
  interval_of_check _ 11632 16 (by decide +kernel)
theorem Check090.checked : Interval test 11520 11648 :=
  (FiniteChecks.interval_append test 11520 11584 11648
  (FiniteChecks.interval_append test 11520 11552 11584
  (FiniteChecks.interval_append test 11520 11536 11552
  Check090.part11520
  Check090.part11536)
  (FiniteChecks.interval_append test 11552 11568 11584
  Check090.part11552
  Check090.part11568))
  (FiniteChecks.interval_append test 11584 11616 11648
  (FiniteChecks.interval_append test 11584 11600 11616
  Check090.part11584
  Check090.part11600)
  (FiniteChecks.interval_append test 11616 11632 11648
  Check090.part11616
  Check090.part11632)))
#print axioms Check090.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check091.part11648 : Interval test 11648 11664 :=
  interval_of_check _ 11648 16 (by decide +kernel)
theorem Check091.part11664 : Interval test 11664 11680 :=
  interval_of_check _ 11664 16 (by decide +kernel)
theorem Check091.part11680 : Interval test 11680 11696 :=
  interval_of_check _ 11680 16 (by decide +kernel)
theorem Check091.part11696 : Interval test 11696 11712 :=
  interval_of_check _ 11696 16 (by decide +kernel)
theorem Check091.part11712 : Interval test 11712 11728 :=
  interval_of_check _ 11712 16 (by decide +kernel)
theorem Check091.part11728 : Interval test 11728 11744 :=
  interval_of_check _ 11728 16 (by decide +kernel)
theorem Check091.part11744 : Interval test 11744 11760 :=
  interval_of_check _ 11744 16 (by decide +kernel)
theorem Check091.part11760 : Interval test 11760 11776 :=
  interval_of_check _ 11760 16 (by decide +kernel)
theorem Check091.checked : Interval test 11648 11776 :=
  (FiniteChecks.interval_append test 11648 11712 11776
  (FiniteChecks.interval_append test 11648 11680 11712
  (FiniteChecks.interval_append test 11648 11664 11680
  Check091.part11648
  Check091.part11664)
  (FiniteChecks.interval_append test 11680 11696 11712
  Check091.part11680
  Check091.part11696))
  (FiniteChecks.interval_append test 11712 11744 11776
  (FiniteChecks.interval_append test 11712 11728 11744
  Check091.part11712
  Check091.part11728)
  (FiniteChecks.interval_append test 11744 11760 11776
  Check091.part11744
  Check091.part11760)))
#print axioms Check091.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check092.part11776 : Interval test 11776 11792 :=
  interval_of_check _ 11776 16 (by decide +kernel)
theorem Check092.part11792 : Interval test 11792 11808 :=
  interval_of_check _ 11792 16 (by decide +kernel)
theorem Check092.part11808 : Interval test 11808 11824 :=
  interval_of_check _ 11808 16 (by decide +kernel)
theorem Check092.part11824 : Interval test 11824 11840 :=
  interval_of_check _ 11824 16 (by decide +kernel)
theorem Check092.part11840 : Interval test 11840 11856 :=
  interval_of_check _ 11840 16 (by decide +kernel)
theorem Check092.part11856 : Interval test 11856 11872 :=
  interval_of_check _ 11856 16 (by decide +kernel)
theorem Check092.part11872 : Interval test 11872 11888 :=
  interval_of_check _ 11872 16 (by decide +kernel)
theorem Check092.part11888 : Interval test 11888 11904 :=
  interval_of_check _ 11888 16 (by decide +kernel)
theorem Check092.checked : Interval test 11776 11904 :=
  (FiniteChecks.interval_append test 11776 11840 11904
  (FiniteChecks.interval_append test 11776 11808 11840
  (FiniteChecks.interval_append test 11776 11792 11808
  Check092.part11776
  Check092.part11792)
  (FiniteChecks.interval_append test 11808 11824 11840
  Check092.part11808
  Check092.part11824))
  (FiniteChecks.interval_append test 11840 11872 11904
  (FiniteChecks.interval_append test 11840 11856 11872
  Check092.part11840
  Check092.part11856)
  (FiniteChecks.interval_append test 11872 11888 11904
  Check092.part11872
  Check092.part11888)))
#print axioms Check092.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check093.part11904 : Interval test 11904 11920 :=
  interval_of_check _ 11904 16 (by decide +kernel)
theorem Check093.part11920 : Interval test 11920 11936 :=
  interval_of_check _ 11920 16 (by decide +kernel)
theorem Check093.part11936 : Interval test 11936 11952 :=
  interval_of_check _ 11936 16 (by decide +kernel)
theorem Check093.part11952 : Interval test 11952 11968 :=
  interval_of_check _ 11952 16 (by decide +kernel)
theorem Check093.part11968 : Interval test 11968 11984 :=
  interval_of_check _ 11968 16 (by decide +kernel)
theorem Check093.part11984 : Interval test 11984 12000 :=
  interval_of_check _ 11984 16 (by decide +kernel)
theorem Check093.part12000 : Interval test 12000 12016 :=
  interval_of_check _ 12000 16 (by decide +kernel)
theorem Check093.part12016 : Interval test 12016 12032 :=
  interval_of_check _ 12016 16 (by decide +kernel)
theorem Check093.checked : Interval test 11904 12032 :=
  (FiniteChecks.interval_append test 11904 11968 12032
  (FiniteChecks.interval_append test 11904 11936 11968
  (FiniteChecks.interval_append test 11904 11920 11936
  Check093.part11904
  Check093.part11920)
  (FiniteChecks.interval_append test 11936 11952 11968
  Check093.part11936
  Check093.part11952))
  (FiniteChecks.interval_append test 11968 12000 12032
  (FiniteChecks.interval_append test 11968 11984 12000
  Check093.part11968
  Check093.part11984)
  (FiniteChecks.interval_append test 12000 12016 12032
  Check093.part12000
  Check093.part12016)))
#print axioms Check093.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check094.part12032 : Interval test 12032 12048 :=
  interval_of_check _ 12032 16 (by decide +kernel)
theorem Check094.part12048 : Interval test 12048 12064 :=
  interval_of_check _ 12048 16 (by decide +kernel)
theorem Check094.part12064 : Interval test 12064 12080 :=
  interval_of_check _ 12064 16 (by decide +kernel)
theorem Check094.part12080 : Interval test 12080 12096 :=
  interval_of_check _ 12080 16 (by decide +kernel)
theorem Check094.part12096 : Interval test 12096 12112 :=
  interval_of_check _ 12096 16 (by decide +kernel)
theorem Check094.part12112 : Interval test 12112 12128 :=
  interval_of_check _ 12112 16 (by decide +kernel)
theorem Check094.part12128 : Interval test 12128 12144 :=
  interval_of_check _ 12128 16 (by decide +kernel)
theorem Check094.part12144 : Interval test 12144 12160 :=
  interval_of_check _ 12144 16 (by decide +kernel)
theorem Check094.checked : Interval test 12032 12160 :=
  (FiniteChecks.interval_append test 12032 12096 12160
  (FiniteChecks.interval_append test 12032 12064 12096
  (FiniteChecks.interval_append test 12032 12048 12064
  Check094.part12032
  Check094.part12048)
  (FiniteChecks.interval_append test 12064 12080 12096
  Check094.part12064
  Check094.part12080))
  (FiniteChecks.interval_append test 12096 12128 12160
  (FiniteChecks.interval_append test 12096 12112 12128
  Check094.part12096
  Check094.part12112)
  (FiniteChecks.interval_append test 12128 12144 12160
  Check094.part12128
  Check094.part12144)))
#print axioms Check094.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check095.part12160 : Interval test 12160 12176 :=
  interval_of_check _ 12160 16 (by decide +kernel)
theorem Check095.part12176 : Interval test 12176 12192 :=
  interval_of_check _ 12176 16 (by decide +kernel)
theorem Check095.part12192 : Interval test 12192 12208 :=
  interval_of_check _ 12192 16 (by decide +kernel)
theorem Check095.part12208 : Interval test 12208 12224 :=
  interval_of_check _ 12208 16 (by decide +kernel)
theorem Check095.part12224 : Interval test 12224 12240 :=
  interval_of_check _ 12224 16 (by decide +kernel)
theorem Check095.part12240 : Interval test 12240 12256 :=
  interval_of_check _ 12240 16 (by decide +kernel)
theorem Check095.part12256 : Interval test 12256 12272 :=
  interval_of_check _ 12256 16 (by decide +kernel)
theorem Check095.part12272 : Interval test 12272 12288 :=
  interval_of_check _ 12272 16 (by decide +kernel)
theorem Check095.checked : Interval test 12160 12288 :=
  (FiniteChecks.interval_append test 12160 12224 12288
  (FiniteChecks.interval_append test 12160 12192 12224
  (FiniteChecks.interval_append test 12160 12176 12192
  Check095.part12160
  Check095.part12176)
  (FiniteChecks.interval_append test 12192 12208 12224
  Check095.part12192
  Check095.part12208))
  (FiniteChecks.interval_append test 12224 12256 12288
  (FiniteChecks.interval_append test 12224 12240 12256
  Check095.part12224
  Check095.part12240)
  (FiniteChecks.interval_append test 12256 12272 12288
  Check095.part12256
  Check095.part12272)))
#print axioms Check095.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check096.part12288 : Interval test 12288 12304 :=
  interval_of_check _ 12288 16 (by decide +kernel)
theorem Check096.part12304 : Interval test 12304 12320 :=
  interval_of_check _ 12304 16 (by decide +kernel)
theorem Check096.part12320 : Interval test 12320 12336 :=
  interval_of_check _ 12320 16 (by decide +kernel)
theorem Check096.part12336 : Interval test 12336 12352 :=
  interval_of_check _ 12336 16 (by decide +kernel)
theorem Check096.part12352 : Interval test 12352 12368 :=
  interval_of_check _ 12352 16 (by decide +kernel)
theorem Check096.part12368 : Interval test 12368 12384 :=
  interval_of_check _ 12368 16 (by decide +kernel)
theorem Check096.part12384 : Interval test 12384 12400 :=
  interval_of_check _ 12384 16 (by decide +kernel)
theorem Check096.part12400 : Interval test 12400 12416 :=
  interval_of_check _ 12400 16 (by decide +kernel)
theorem Check096.checked : Interval test 12288 12416 :=
  (FiniteChecks.interval_append test 12288 12352 12416
  (FiniteChecks.interval_append test 12288 12320 12352
  (FiniteChecks.interval_append test 12288 12304 12320
  Check096.part12288
  Check096.part12304)
  (FiniteChecks.interval_append test 12320 12336 12352
  Check096.part12320
  Check096.part12336))
  (FiniteChecks.interval_append test 12352 12384 12416
  (FiniteChecks.interval_append test 12352 12368 12384
  Check096.part12352
  Check096.part12368)
  (FiniteChecks.interval_append test 12384 12400 12416
  Check096.part12384
  Check096.part12400)))
#print axioms Check096.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check097.part12416 : Interval test 12416 12432 :=
  interval_of_check _ 12416 16 (by decide +kernel)
theorem Check097.part12432 : Interval test 12432 12448 :=
  interval_of_check _ 12432 16 (by decide +kernel)
theorem Check097.part12448 : Interval test 12448 12464 :=
  interval_of_check _ 12448 16 (by decide +kernel)
theorem Check097.part12464 : Interval test 12464 12480 :=
  interval_of_check _ 12464 16 (by decide +kernel)
theorem Check097.part12480 : Interval test 12480 12496 :=
  interval_of_check _ 12480 16 (by decide +kernel)
theorem Check097.part12496 : Interval test 12496 12512 :=
  interval_of_check _ 12496 16 (by decide +kernel)
theorem Check097.part12512 : Interval test 12512 12528 :=
  interval_of_check _ 12512 16 (by decide +kernel)
theorem Check097.part12528 : Interval test 12528 12544 :=
  interval_of_check _ 12528 16 (by decide +kernel)
theorem Check097.checked : Interval test 12416 12544 :=
  (FiniteChecks.interval_append test 12416 12480 12544
  (FiniteChecks.interval_append test 12416 12448 12480
  (FiniteChecks.interval_append test 12416 12432 12448
  Check097.part12416
  Check097.part12432)
  (FiniteChecks.interval_append test 12448 12464 12480
  Check097.part12448
  Check097.part12464))
  (FiniteChecks.interval_append test 12480 12512 12544
  (FiniteChecks.interval_append test 12480 12496 12512
  Check097.part12480
  Check097.part12496)
  (FiniteChecks.interval_append test 12512 12528 12544
  Check097.part12512
  Check097.part12528)))
#print axioms Check097.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check098.part12544 : Interval test 12544 12560 :=
  interval_of_check _ 12544 16 (by decide +kernel)
theorem Check098.part12560 : Interval test 12560 12576 :=
  interval_of_check _ 12560 16 (by decide +kernel)
theorem Check098.part12576 : Interval test 12576 12592 :=
  interval_of_check _ 12576 16 (by decide +kernel)
theorem Check098.part12592 : Interval test 12592 12608 :=
  interval_of_check _ 12592 16 (by decide +kernel)
theorem Check098.part12608 : Interval test 12608 12624 :=
  interval_of_check _ 12608 16 (by decide +kernel)
theorem Check098.part12624 : Interval test 12624 12640 :=
  interval_of_check _ 12624 16 (by decide +kernel)
theorem Check098.part12640 : Interval test 12640 12656 :=
  interval_of_check _ 12640 16 (by decide +kernel)
theorem Check098.part12656 : Interval test 12656 12672 :=
  interval_of_check _ 12656 16 (by decide +kernel)
theorem Check098.checked : Interval test 12544 12672 :=
  (FiniteChecks.interval_append test 12544 12608 12672
  (FiniteChecks.interval_append test 12544 12576 12608
  (FiniteChecks.interval_append test 12544 12560 12576
  Check098.part12544
  Check098.part12560)
  (FiniteChecks.interval_append test 12576 12592 12608
  Check098.part12576
  Check098.part12592))
  (FiniteChecks.interval_append test 12608 12640 12672
  (FiniteChecks.interval_append test 12608 12624 12640
  Check098.part12608
  Check098.part12624)
  (FiniteChecks.interval_append test 12640 12656 12672
  Check098.part12640
  Check098.part12656)))
#print axioms Check098.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check099.part12672 : Interval test 12672 12688 :=
  interval_of_check _ 12672 16 (by decide +kernel)
theorem Check099.part12688 : Interval test 12688 12704 :=
  interval_of_check _ 12688 16 (by decide +kernel)
theorem Check099.part12704 : Interval test 12704 12720 :=
  interval_of_check _ 12704 16 (by decide +kernel)
theorem Check099.part12720 : Interval test 12720 12736 :=
  interval_of_check _ 12720 16 (by decide +kernel)
theorem Check099.part12736 : Interval test 12736 12752 :=
  interval_of_check _ 12736 16 (by decide +kernel)
theorem Check099.part12752 : Interval test 12752 12768 :=
  interval_of_check _ 12752 16 (by decide +kernel)
theorem Check099.part12768 : Interval test 12768 12784 :=
  interval_of_check _ 12768 16 (by decide +kernel)
theorem Check099.part12784 : Interval test 12784 12800 :=
  interval_of_check _ 12784 16 (by decide +kernel)
theorem Check099.checked : Interval test 12672 12800 :=
  (FiniteChecks.interval_append test 12672 12736 12800
  (FiniteChecks.interval_append test 12672 12704 12736
  (FiniteChecks.interval_append test 12672 12688 12704
  Check099.part12672
  Check099.part12688)
  (FiniteChecks.interval_append test 12704 12720 12736
  Check099.part12704
  Check099.part12720))
  (FiniteChecks.interval_append test 12736 12768 12800
  (FiniteChecks.interval_append test 12736 12752 12768
  Check099.part12736
  Check099.part12752)
  (FiniteChecks.interval_append test 12768 12784 12800
  Check099.part12768
  Check099.part12784)))
#print axioms Check099.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
