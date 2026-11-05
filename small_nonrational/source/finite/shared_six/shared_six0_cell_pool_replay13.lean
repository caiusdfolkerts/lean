module
prelude
public import SharedSix0CellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check260.part33280 : Interval test 33280 33296 :=
  interval_of_check _ 33280 16 (by decide +kernel)
theorem Check260.part33296 : Interval test 33296 33312 :=
  interval_of_check _ 33296 16 (by decide +kernel)
theorem Check260.part33312 : Interval test 33312 33328 :=
  interval_of_check _ 33312 16 (by decide +kernel)
theorem Check260.part33328 : Interval test 33328 33344 :=
  interval_of_check _ 33328 16 (by decide +kernel)
theorem Check260.part33344 : Interval test 33344 33360 :=
  interval_of_check _ 33344 16 (by decide +kernel)
theorem Check260.part33360 : Interval test 33360 33376 :=
  interval_of_check _ 33360 16 (by decide +kernel)
theorem Check260.part33376 : Interval test 33376 33392 :=
  interval_of_check _ 33376 16 (by decide +kernel)
theorem Check260.part33392 : Interval test 33392 33408 :=
  interval_of_check _ 33392 16 (by decide +kernel)
theorem Check260.checked : Interval test 33280 33408 :=
  (FiniteChecks.interval_append test 33280 33344 33408
  (FiniteChecks.interval_append test 33280 33312 33344
  (FiniteChecks.interval_append test 33280 33296 33312
  Check260.part33280
  Check260.part33296)
  (FiniteChecks.interval_append test 33312 33328 33344
  Check260.part33312
  Check260.part33328))
  (FiniteChecks.interval_append test 33344 33376 33408
  (FiniteChecks.interval_append test 33344 33360 33376
  Check260.part33344
  Check260.part33360)
  (FiniteChecks.interval_append test 33376 33392 33408
  Check260.part33376
  Check260.part33392)))
#print axioms Check260.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check261.part33408 : Interval test 33408 33424 :=
  interval_of_check _ 33408 16 (by decide +kernel)
theorem Check261.part33424 : Interval test 33424 33440 :=
  interval_of_check _ 33424 16 (by decide +kernel)
theorem Check261.part33440 : Interval test 33440 33456 :=
  interval_of_check _ 33440 16 (by decide +kernel)
theorem Check261.part33456 : Interval test 33456 33472 :=
  interval_of_check _ 33456 16 (by decide +kernel)
theorem Check261.part33472 : Interval test 33472 33488 :=
  interval_of_check _ 33472 16 (by decide +kernel)
theorem Check261.part33488 : Interval test 33488 33504 :=
  interval_of_check _ 33488 16 (by decide +kernel)
theorem Check261.part33504 : Interval test 33504 33520 :=
  interval_of_check _ 33504 16 (by decide +kernel)
theorem Check261.part33520 : Interval test 33520 33536 :=
  interval_of_check _ 33520 16 (by decide +kernel)
theorem Check261.checked : Interval test 33408 33536 :=
  (FiniteChecks.interval_append test 33408 33472 33536
  (FiniteChecks.interval_append test 33408 33440 33472
  (FiniteChecks.interval_append test 33408 33424 33440
  Check261.part33408
  Check261.part33424)
  (FiniteChecks.interval_append test 33440 33456 33472
  Check261.part33440
  Check261.part33456))
  (FiniteChecks.interval_append test 33472 33504 33536
  (FiniteChecks.interval_append test 33472 33488 33504
  Check261.part33472
  Check261.part33488)
  (FiniteChecks.interval_append test 33504 33520 33536
  Check261.part33504
  Check261.part33520)))
#print axioms Check261.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check262.part33536 : Interval test 33536 33552 :=
  interval_of_check _ 33536 16 (by decide +kernel)
theorem Check262.part33552 : Interval test 33552 33568 :=
  interval_of_check _ 33552 16 (by decide +kernel)
theorem Check262.part33568 : Interval test 33568 33584 :=
  interval_of_check _ 33568 16 (by decide +kernel)
theorem Check262.part33584 : Interval test 33584 33600 :=
  interval_of_check _ 33584 16 (by decide +kernel)
theorem Check262.part33600 : Interval test 33600 33616 :=
  interval_of_check _ 33600 16 (by decide +kernel)
theorem Check262.part33616 : Interval test 33616 33632 :=
  interval_of_check _ 33616 16 (by decide +kernel)
theorem Check262.part33632 : Interval test 33632 33648 :=
  interval_of_check _ 33632 16 (by decide +kernel)
theorem Check262.part33648 : Interval test 33648 33664 :=
  interval_of_check _ 33648 16 (by decide +kernel)
theorem Check262.checked : Interval test 33536 33664 :=
  (FiniteChecks.interval_append test 33536 33600 33664
  (FiniteChecks.interval_append test 33536 33568 33600
  (FiniteChecks.interval_append test 33536 33552 33568
  Check262.part33536
  Check262.part33552)
  (FiniteChecks.interval_append test 33568 33584 33600
  Check262.part33568
  Check262.part33584))
  (FiniteChecks.interval_append test 33600 33632 33664
  (FiniteChecks.interval_append test 33600 33616 33632
  Check262.part33600
  Check262.part33616)
  (FiniteChecks.interval_append test 33632 33648 33664
  Check262.part33632
  Check262.part33648)))
#print axioms Check262.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check263.part33664 : Interval test 33664 33680 :=
  interval_of_check _ 33664 16 (by decide +kernel)
theorem Check263.part33680 : Interval test 33680 33696 :=
  interval_of_check _ 33680 16 (by decide +kernel)
theorem Check263.part33696 : Interval test 33696 33712 :=
  interval_of_check _ 33696 16 (by decide +kernel)
theorem Check263.part33712 : Interval test 33712 33728 :=
  interval_of_check _ 33712 16 (by decide +kernel)
theorem Check263.part33728 : Interval test 33728 33744 :=
  interval_of_check _ 33728 16 (by decide +kernel)
theorem Check263.part33744 : Interval test 33744 33760 :=
  interval_of_check _ 33744 16 (by decide +kernel)
theorem Check263.part33760 : Interval test 33760 33776 :=
  interval_of_check _ 33760 16 (by decide +kernel)
theorem Check263.part33776 : Interval test 33776 33792 :=
  interval_of_check _ 33776 16 (by decide +kernel)
theorem Check263.checked : Interval test 33664 33792 :=
  (FiniteChecks.interval_append test 33664 33728 33792
  (FiniteChecks.interval_append test 33664 33696 33728
  (FiniteChecks.interval_append test 33664 33680 33696
  Check263.part33664
  Check263.part33680)
  (FiniteChecks.interval_append test 33696 33712 33728
  Check263.part33696
  Check263.part33712))
  (FiniteChecks.interval_append test 33728 33760 33792
  (FiniteChecks.interval_append test 33728 33744 33760
  Check263.part33728
  Check263.part33744)
  (FiniteChecks.interval_append test 33760 33776 33792
  Check263.part33760
  Check263.part33776)))
#print axioms Check263.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check264.part33792 : Interval test 33792 33808 :=
  interval_of_check _ 33792 16 (by decide +kernel)
theorem Check264.part33808 : Interval test 33808 33824 :=
  interval_of_check _ 33808 16 (by decide +kernel)
theorem Check264.part33824 : Interval test 33824 33840 :=
  interval_of_check _ 33824 16 (by decide +kernel)
theorem Check264.part33840 : Interval test 33840 33856 :=
  interval_of_check _ 33840 16 (by decide +kernel)
theorem Check264.part33856 : Interval test 33856 33872 :=
  interval_of_check _ 33856 16 (by decide +kernel)
theorem Check264.part33872 : Interval test 33872 33888 :=
  interval_of_check _ 33872 16 (by decide +kernel)
theorem Check264.part33888 : Interval test 33888 33904 :=
  interval_of_check _ 33888 16 (by decide +kernel)
theorem Check264.part33904 : Interval test 33904 33920 :=
  interval_of_check _ 33904 16 (by decide +kernel)
theorem Check264.checked : Interval test 33792 33920 :=
  (FiniteChecks.interval_append test 33792 33856 33920
  (FiniteChecks.interval_append test 33792 33824 33856
  (FiniteChecks.interval_append test 33792 33808 33824
  Check264.part33792
  Check264.part33808)
  (FiniteChecks.interval_append test 33824 33840 33856
  Check264.part33824
  Check264.part33840))
  (FiniteChecks.interval_append test 33856 33888 33920
  (FiniteChecks.interval_append test 33856 33872 33888
  Check264.part33856
  Check264.part33872)
  (FiniteChecks.interval_append test 33888 33904 33920
  Check264.part33888
  Check264.part33904)))
#print axioms Check264.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check265.part33920 : Interval test 33920 33936 :=
  interval_of_check _ 33920 16 (by decide +kernel)
theorem Check265.part33936 : Interval test 33936 33952 :=
  interval_of_check _ 33936 16 (by decide +kernel)
theorem Check265.part33952 : Interval test 33952 33968 :=
  interval_of_check _ 33952 16 (by decide +kernel)
theorem Check265.part33968 : Interval test 33968 33984 :=
  interval_of_check _ 33968 16 (by decide +kernel)
theorem Check265.part33984 : Interval test 33984 34000 :=
  interval_of_check _ 33984 16 (by decide +kernel)
theorem Check265.part34000 : Interval test 34000 34016 :=
  interval_of_check _ 34000 16 (by decide +kernel)
theorem Check265.part34016 : Interval test 34016 34032 :=
  interval_of_check _ 34016 16 (by decide +kernel)
theorem Check265.part34032 : Interval test 34032 34048 :=
  interval_of_check _ 34032 16 (by decide +kernel)
theorem Check265.checked : Interval test 33920 34048 :=
  (FiniteChecks.interval_append test 33920 33984 34048
  (FiniteChecks.interval_append test 33920 33952 33984
  (FiniteChecks.interval_append test 33920 33936 33952
  Check265.part33920
  Check265.part33936)
  (FiniteChecks.interval_append test 33952 33968 33984
  Check265.part33952
  Check265.part33968))
  (FiniteChecks.interval_append test 33984 34016 34048
  (FiniteChecks.interval_append test 33984 34000 34016
  Check265.part33984
  Check265.part34000)
  (FiniteChecks.interval_append test 34016 34032 34048
  Check265.part34016
  Check265.part34032)))
#print axioms Check265.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check266.part34048 : Interval test 34048 34064 :=
  interval_of_check _ 34048 16 (by decide +kernel)
theorem Check266.part34064 : Interval test 34064 34080 :=
  interval_of_check _ 34064 16 (by decide +kernel)
theorem Check266.part34080 : Interval test 34080 34096 :=
  interval_of_check _ 34080 16 (by decide +kernel)
theorem Check266.part34096 : Interval test 34096 34112 :=
  interval_of_check _ 34096 16 (by decide +kernel)
theorem Check266.part34112 : Interval test 34112 34128 :=
  interval_of_check _ 34112 16 (by decide +kernel)
theorem Check266.part34128 : Interval test 34128 34144 :=
  interval_of_check _ 34128 16 (by decide +kernel)
theorem Check266.part34144 : Interval test 34144 34160 :=
  interval_of_check _ 34144 16 (by decide +kernel)
theorem Check266.part34160 : Interval test 34160 34176 :=
  interval_of_check _ 34160 16 (by decide +kernel)
theorem Check266.checked : Interval test 34048 34176 :=
  (FiniteChecks.interval_append test 34048 34112 34176
  (FiniteChecks.interval_append test 34048 34080 34112
  (FiniteChecks.interval_append test 34048 34064 34080
  Check266.part34048
  Check266.part34064)
  (FiniteChecks.interval_append test 34080 34096 34112
  Check266.part34080
  Check266.part34096))
  (FiniteChecks.interval_append test 34112 34144 34176
  (FiniteChecks.interval_append test 34112 34128 34144
  Check266.part34112
  Check266.part34128)
  (FiniteChecks.interval_append test 34144 34160 34176
  Check266.part34144
  Check266.part34160)))
#print axioms Check266.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check267.part34176 : Interval test 34176 34192 :=
  interval_of_check _ 34176 16 (by decide +kernel)
theorem Check267.part34192 : Interval test 34192 34208 :=
  interval_of_check _ 34192 16 (by decide +kernel)
theorem Check267.part34208 : Interval test 34208 34224 :=
  interval_of_check _ 34208 16 (by decide +kernel)
theorem Check267.part34224 : Interval test 34224 34240 :=
  interval_of_check _ 34224 16 (by decide +kernel)
theorem Check267.part34240 : Interval test 34240 34256 :=
  interval_of_check _ 34240 16 (by decide +kernel)
theorem Check267.part34256 : Interval test 34256 34272 :=
  interval_of_check _ 34256 16 (by decide +kernel)
theorem Check267.part34272 : Interval test 34272 34288 :=
  interval_of_check _ 34272 16 (by decide +kernel)
theorem Check267.part34288 : Interval test 34288 34304 :=
  interval_of_check _ 34288 16 (by decide +kernel)
theorem Check267.checked : Interval test 34176 34304 :=
  (FiniteChecks.interval_append test 34176 34240 34304
  (FiniteChecks.interval_append test 34176 34208 34240
  (FiniteChecks.interval_append test 34176 34192 34208
  Check267.part34176
  Check267.part34192)
  (FiniteChecks.interval_append test 34208 34224 34240
  Check267.part34208
  Check267.part34224))
  (FiniteChecks.interval_append test 34240 34272 34304
  (FiniteChecks.interval_append test 34240 34256 34272
  Check267.part34240
  Check267.part34256)
  (FiniteChecks.interval_append test 34272 34288 34304
  Check267.part34272
  Check267.part34288)))
#print axioms Check267.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check268.part34304 : Interval test 34304 34320 :=
  interval_of_check _ 34304 16 (by decide +kernel)
theorem Check268.part34320 : Interval test 34320 34336 :=
  interval_of_check _ 34320 16 (by decide +kernel)
theorem Check268.part34336 : Interval test 34336 34352 :=
  interval_of_check _ 34336 16 (by decide +kernel)
theorem Check268.part34352 : Interval test 34352 34368 :=
  interval_of_check _ 34352 16 (by decide +kernel)
theorem Check268.part34368 : Interval test 34368 34384 :=
  interval_of_check _ 34368 16 (by decide +kernel)
theorem Check268.part34384 : Interval test 34384 34400 :=
  interval_of_check _ 34384 16 (by decide +kernel)
theorem Check268.part34400 : Interval test 34400 34416 :=
  interval_of_check _ 34400 16 (by decide +kernel)
theorem Check268.part34416 : Interval test 34416 34432 :=
  interval_of_check _ 34416 16 (by decide +kernel)
theorem Check268.checked : Interval test 34304 34432 :=
  (FiniteChecks.interval_append test 34304 34368 34432
  (FiniteChecks.interval_append test 34304 34336 34368
  (FiniteChecks.interval_append test 34304 34320 34336
  Check268.part34304
  Check268.part34320)
  (FiniteChecks.interval_append test 34336 34352 34368
  Check268.part34336
  Check268.part34352))
  (FiniteChecks.interval_append test 34368 34400 34432
  (FiniteChecks.interval_append test 34368 34384 34400
  Check268.part34368
  Check268.part34384)
  (FiniteChecks.interval_append test 34400 34416 34432
  Check268.part34400
  Check268.part34416)))
#print axioms Check268.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check269.part34432 : Interval test 34432 34448 :=
  interval_of_check _ 34432 16 (by decide +kernel)
theorem Check269.part34448 : Interval test 34448 34464 :=
  interval_of_check _ 34448 16 (by decide +kernel)
theorem Check269.part34464 : Interval test 34464 34480 :=
  interval_of_check _ 34464 16 (by decide +kernel)
theorem Check269.part34480 : Interval test 34480 34496 :=
  interval_of_check _ 34480 16 (by decide +kernel)
theorem Check269.part34496 : Interval test 34496 34512 :=
  interval_of_check _ 34496 16 (by decide +kernel)
theorem Check269.part34512 : Interval test 34512 34528 :=
  interval_of_check _ 34512 16 (by decide +kernel)
theorem Check269.part34528 : Interval test 34528 34544 :=
  interval_of_check _ 34528 16 (by decide +kernel)
theorem Check269.part34544 : Interval test 34544 34560 :=
  interval_of_check _ 34544 16 (by decide +kernel)
theorem Check269.checked : Interval test 34432 34560 :=
  (FiniteChecks.interval_append test 34432 34496 34560
  (FiniteChecks.interval_append test 34432 34464 34496
  (FiniteChecks.interval_append test 34432 34448 34464
  Check269.part34432
  Check269.part34448)
  (FiniteChecks.interval_append test 34464 34480 34496
  Check269.part34464
  Check269.part34480))
  (FiniteChecks.interval_append test 34496 34528 34560
  (FiniteChecks.interval_append test 34496 34512 34528
  Check269.part34496
  Check269.part34512)
  (FiniteChecks.interval_append test 34528 34544 34560
  Check269.part34528
  Check269.part34544)))
#print axioms Check269.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check270.part34560 : Interval test 34560 34576 :=
  interval_of_check _ 34560 16 (by decide +kernel)
theorem Check270.part34576 : Interval test 34576 34592 :=
  interval_of_check _ 34576 16 (by decide +kernel)
theorem Check270.part34592 : Interval test 34592 34608 :=
  interval_of_check _ 34592 16 (by decide +kernel)
theorem Check270.part34608 : Interval test 34608 34624 :=
  interval_of_check _ 34608 16 (by decide +kernel)
theorem Check270.part34624 : Interval test 34624 34640 :=
  interval_of_check _ 34624 16 (by decide +kernel)
theorem Check270.part34640 : Interval test 34640 34656 :=
  interval_of_check _ 34640 16 (by decide +kernel)
theorem Check270.part34656 : Interval test 34656 34672 :=
  interval_of_check _ 34656 16 (by decide +kernel)
theorem Check270.part34672 : Interval test 34672 34688 :=
  interval_of_check _ 34672 16 (by decide +kernel)
theorem Check270.checked : Interval test 34560 34688 :=
  (FiniteChecks.interval_append test 34560 34624 34688
  (FiniteChecks.interval_append test 34560 34592 34624
  (FiniteChecks.interval_append test 34560 34576 34592
  Check270.part34560
  Check270.part34576)
  (FiniteChecks.interval_append test 34592 34608 34624
  Check270.part34592
  Check270.part34608))
  (FiniteChecks.interval_append test 34624 34656 34688
  (FiniteChecks.interval_append test 34624 34640 34656
  Check270.part34624
  Check270.part34640)
  (FiniteChecks.interval_append test 34656 34672 34688
  Check270.part34656
  Check270.part34672)))
#print axioms Check270.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check271.part34688 : Interval test 34688 34704 :=
  interval_of_check _ 34688 16 (by decide +kernel)
theorem Check271.part34704 : Interval test 34704 34720 :=
  interval_of_check _ 34704 16 (by decide +kernel)
theorem Check271.part34720 : Interval test 34720 34736 :=
  interval_of_check _ 34720 16 (by decide +kernel)
theorem Check271.part34736 : Interval test 34736 34752 :=
  interval_of_check _ 34736 16 (by decide +kernel)
theorem Check271.part34752 : Interval test 34752 34768 :=
  interval_of_check _ 34752 16 (by decide +kernel)
theorem Check271.part34768 : Interval test 34768 34784 :=
  interval_of_check _ 34768 16 (by decide +kernel)
theorem Check271.part34784 : Interval test 34784 34800 :=
  interval_of_check _ 34784 16 (by decide +kernel)
theorem Check271.part34800 : Interval test 34800 34816 :=
  interval_of_check _ 34800 16 (by decide +kernel)
theorem Check271.checked : Interval test 34688 34816 :=
  (FiniteChecks.interval_append test 34688 34752 34816
  (FiniteChecks.interval_append test 34688 34720 34752
  (FiniteChecks.interval_append test 34688 34704 34720
  Check271.part34688
  Check271.part34704)
  (FiniteChecks.interval_append test 34720 34736 34752
  Check271.part34720
  Check271.part34736))
  (FiniteChecks.interval_append test 34752 34784 34816
  (FiniteChecks.interval_append test 34752 34768 34784
  Check271.part34752
  Check271.part34768)
  (FiniteChecks.interval_append test 34784 34800 34816
  Check271.part34784
  Check271.part34800)))
#print axioms Check271.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check272.part34816 : Interval test 34816 34832 :=
  interval_of_check _ 34816 16 (by decide +kernel)
theorem Check272.part34832 : Interval test 34832 34848 :=
  interval_of_check _ 34832 16 (by decide +kernel)
theorem Check272.part34848 : Interval test 34848 34864 :=
  interval_of_check _ 34848 16 (by decide +kernel)
theorem Check272.part34864 : Interval test 34864 34880 :=
  interval_of_check _ 34864 16 (by decide +kernel)
theorem Check272.part34880 : Interval test 34880 34896 :=
  interval_of_check _ 34880 16 (by decide +kernel)
theorem Check272.part34896 : Interval test 34896 34912 :=
  interval_of_check _ 34896 16 (by decide +kernel)
theorem Check272.part34912 : Interval test 34912 34928 :=
  interval_of_check _ 34912 16 (by decide +kernel)
theorem Check272.part34928 : Interval test 34928 34944 :=
  interval_of_check _ 34928 16 (by decide +kernel)
theorem Check272.checked : Interval test 34816 34944 :=
  (FiniteChecks.interval_append test 34816 34880 34944
  (FiniteChecks.interval_append test 34816 34848 34880
  (FiniteChecks.interval_append test 34816 34832 34848
  Check272.part34816
  Check272.part34832)
  (FiniteChecks.interval_append test 34848 34864 34880
  Check272.part34848
  Check272.part34864))
  (FiniteChecks.interval_append test 34880 34912 34944
  (FiniteChecks.interval_append test 34880 34896 34912
  Check272.part34880
  Check272.part34896)
  (FiniteChecks.interval_append test 34912 34928 34944
  Check272.part34912
  Check272.part34928)))
#print axioms Check272.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check273.part34944 : Interval test 34944 34960 :=
  interval_of_check _ 34944 16 (by decide +kernel)
theorem Check273.part34960 : Interval test 34960 34976 :=
  interval_of_check _ 34960 16 (by decide +kernel)
theorem Check273.part34976 : Interval test 34976 34992 :=
  interval_of_check _ 34976 16 (by decide +kernel)
theorem Check273.part34992 : Interval test 34992 35008 :=
  interval_of_check _ 34992 16 (by decide +kernel)
theorem Check273.part35008 : Interval test 35008 35024 :=
  interval_of_check _ 35008 16 (by decide +kernel)
theorem Check273.part35024 : Interval test 35024 35040 :=
  interval_of_check _ 35024 16 (by decide +kernel)
theorem Check273.part35040 : Interval test 35040 35056 :=
  interval_of_check _ 35040 16 (by decide +kernel)
theorem Check273.part35056 : Interval test 35056 35072 :=
  interval_of_check _ 35056 16 (by decide +kernel)
theorem Check273.checked : Interval test 34944 35072 :=
  (FiniteChecks.interval_append test 34944 35008 35072
  (FiniteChecks.interval_append test 34944 34976 35008
  (FiniteChecks.interval_append test 34944 34960 34976
  Check273.part34944
  Check273.part34960)
  (FiniteChecks.interval_append test 34976 34992 35008
  Check273.part34976
  Check273.part34992))
  (FiniteChecks.interval_append test 35008 35040 35072
  (FiniteChecks.interval_append test 35008 35024 35040
  Check273.part35008
  Check273.part35024)
  (FiniteChecks.interval_append test 35040 35056 35072
  Check273.part35040
  Check273.part35056)))
#print axioms Check273.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check274.part35072 : Interval test 35072 35088 :=
  interval_of_check _ 35072 16 (by decide +kernel)
theorem Check274.part35088 : Interval test 35088 35104 :=
  interval_of_check _ 35088 16 (by decide +kernel)
theorem Check274.part35104 : Interval test 35104 35120 :=
  interval_of_check _ 35104 16 (by decide +kernel)
theorem Check274.part35120 : Interval test 35120 35136 :=
  interval_of_check _ 35120 16 (by decide +kernel)
theorem Check274.part35136 : Interval test 35136 35152 :=
  interval_of_check _ 35136 16 (by decide +kernel)
theorem Check274.part35152 : Interval test 35152 35168 :=
  interval_of_check _ 35152 16 (by decide +kernel)
theorem Check274.part35168 : Interval test 35168 35184 :=
  interval_of_check _ 35168 16 (by decide +kernel)
theorem Check274.part35184 : Interval test 35184 35200 :=
  interval_of_check _ 35184 16 (by decide +kernel)
theorem Check274.checked : Interval test 35072 35200 :=
  (FiniteChecks.interval_append test 35072 35136 35200
  (FiniteChecks.interval_append test 35072 35104 35136
  (FiniteChecks.interval_append test 35072 35088 35104
  Check274.part35072
  Check274.part35088)
  (FiniteChecks.interval_append test 35104 35120 35136
  Check274.part35104
  Check274.part35120))
  (FiniteChecks.interval_append test 35136 35168 35200
  (FiniteChecks.interval_append test 35136 35152 35168
  Check274.part35136
  Check274.part35152)
  (FiniteChecks.interval_append test 35168 35184 35200
  Check274.part35168
  Check274.part35184)))
#print axioms Check274.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check275.part35200 : Interval test 35200 35216 :=
  interval_of_check _ 35200 16 (by decide +kernel)
theorem Check275.part35216 : Interval test 35216 35232 :=
  interval_of_check _ 35216 16 (by decide +kernel)
theorem Check275.part35232 : Interval test 35232 35248 :=
  interval_of_check _ 35232 16 (by decide +kernel)
theorem Check275.part35248 : Interval test 35248 35264 :=
  interval_of_check _ 35248 16 (by decide +kernel)
theorem Check275.part35264 : Interval test 35264 35280 :=
  interval_of_check _ 35264 16 (by decide +kernel)
theorem Check275.part35280 : Interval test 35280 35296 :=
  interval_of_check _ 35280 16 (by decide +kernel)
theorem Check275.part35296 : Interval test 35296 35312 :=
  interval_of_check _ 35296 16 (by decide +kernel)
theorem Check275.part35312 : Interval test 35312 35328 :=
  interval_of_check _ 35312 16 (by decide +kernel)
theorem Check275.checked : Interval test 35200 35328 :=
  (FiniteChecks.interval_append test 35200 35264 35328
  (FiniteChecks.interval_append test 35200 35232 35264
  (FiniteChecks.interval_append test 35200 35216 35232
  Check275.part35200
  Check275.part35216)
  (FiniteChecks.interval_append test 35232 35248 35264
  Check275.part35232
  Check275.part35248))
  (FiniteChecks.interval_append test 35264 35296 35328
  (FiniteChecks.interval_append test 35264 35280 35296
  Check275.part35264
  Check275.part35280)
  (FiniteChecks.interval_append test 35296 35312 35328
  Check275.part35296
  Check275.part35312)))
#print axioms Check275.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check276.part35328 : Interval test 35328 35344 :=
  interval_of_check _ 35328 16 (by decide +kernel)
theorem Check276.part35344 : Interval test 35344 35360 :=
  interval_of_check _ 35344 16 (by decide +kernel)
theorem Check276.part35360 : Interval test 35360 35376 :=
  interval_of_check _ 35360 16 (by decide +kernel)
theorem Check276.part35376 : Interval test 35376 35392 :=
  interval_of_check _ 35376 16 (by decide +kernel)
theorem Check276.part35392 : Interval test 35392 35408 :=
  interval_of_check _ 35392 16 (by decide +kernel)
theorem Check276.part35408 : Interval test 35408 35424 :=
  interval_of_check _ 35408 16 (by decide +kernel)
theorem Check276.part35424 : Interval test 35424 35440 :=
  interval_of_check _ 35424 16 (by decide +kernel)
theorem Check276.part35440 : Interval test 35440 35456 :=
  interval_of_check _ 35440 16 (by decide +kernel)
theorem Check276.checked : Interval test 35328 35456 :=
  (FiniteChecks.interval_append test 35328 35392 35456
  (FiniteChecks.interval_append test 35328 35360 35392
  (FiniteChecks.interval_append test 35328 35344 35360
  Check276.part35328
  Check276.part35344)
  (FiniteChecks.interval_append test 35360 35376 35392
  Check276.part35360
  Check276.part35376))
  (FiniteChecks.interval_append test 35392 35424 35456
  (FiniteChecks.interval_append test 35392 35408 35424
  Check276.part35392
  Check276.part35408)
  (FiniteChecks.interval_append test 35424 35440 35456
  Check276.part35424
  Check276.part35440)))
#print axioms Check276.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check277.part35456 : Interval test 35456 35472 :=
  interval_of_check _ 35456 16 (by decide +kernel)
theorem Check277.part35472 : Interval test 35472 35488 :=
  interval_of_check _ 35472 16 (by decide +kernel)
theorem Check277.part35488 : Interval test 35488 35504 :=
  interval_of_check _ 35488 16 (by decide +kernel)
theorem Check277.part35504 : Interval test 35504 35520 :=
  interval_of_check _ 35504 16 (by decide +kernel)
theorem Check277.part35520 : Interval test 35520 35536 :=
  interval_of_check _ 35520 16 (by decide +kernel)
theorem Check277.part35536 : Interval test 35536 35552 :=
  interval_of_check _ 35536 16 (by decide +kernel)
theorem Check277.part35552 : Interval test 35552 35568 :=
  interval_of_check _ 35552 16 (by decide +kernel)
theorem Check277.part35568 : Interval test 35568 35584 :=
  interval_of_check _ 35568 16 (by decide +kernel)
theorem Check277.checked : Interval test 35456 35584 :=
  (FiniteChecks.interval_append test 35456 35520 35584
  (FiniteChecks.interval_append test 35456 35488 35520
  (FiniteChecks.interval_append test 35456 35472 35488
  Check277.part35456
  Check277.part35472)
  (FiniteChecks.interval_append test 35488 35504 35520
  Check277.part35488
  Check277.part35504))
  (FiniteChecks.interval_append test 35520 35552 35584
  (FiniteChecks.interval_append test 35520 35536 35552
  Check277.part35520
  Check277.part35536)
  (FiniteChecks.interval_append test 35552 35568 35584
  Check277.part35552
  Check277.part35568)))
#print axioms Check277.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check278.part35584 : Interval test 35584 35600 :=
  interval_of_check _ 35584 16 (by decide +kernel)
theorem Check278.part35600 : Interval test 35600 35616 :=
  interval_of_check _ 35600 16 (by decide +kernel)
theorem Check278.part35616 : Interval test 35616 35632 :=
  interval_of_check _ 35616 16 (by decide +kernel)
theorem Check278.part35632 : Interval test 35632 35648 :=
  interval_of_check _ 35632 16 (by decide +kernel)
theorem Check278.part35648 : Interval test 35648 35664 :=
  interval_of_check _ 35648 16 (by decide +kernel)
theorem Check278.part35664 : Interval test 35664 35680 :=
  interval_of_check _ 35664 16 (by decide +kernel)
theorem Check278.part35680 : Interval test 35680 35696 :=
  interval_of_check _ 35680 16 (by decide +kernel)
theorem Check278.part35696 : Interval test 35696 35712 :=
  interval_of_check _ 35696 16 (by decide +kernel)
theorem Check278.checked : Interval test 35584 35712 :=
  (FiniteChecks.interval_append test 35584 35648 35712
  (FiniteChecks.interval_append test 35584 35616 35648
  (FiniteChecks.interval_append test 35584 35600 35616
  Check278.part35584
  Check278.part35600)
  (FiniteChecks.interval_append test 35616 35632 35648
  Check278.part35616
  Check278.part35632))
  (FiniteChecks.interval_append test 35648 35680 35712
  (FiniteChecks.interval_append test 35648 35664 35680
  Check278.part35648
  Check278.part35664)
  (FiniteChecks.interval_append test 35680 35696 35712
  Check278.part35680
  Check278.part35696)))
#print axioms Check278.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check279.part35712 : Interval test 35712 35728 :=
  interval_of_check _ 35712 16 (by decide +kernel)
theorem Check279.part35728 : Interval test 35728 35744 :=
  interval_of_check _ 35728 16 (by decide +kernel)
theorem Check279.part35744 : Interval test 35744 35760 :=
  interval_of_check _ 35744 16 (by decide +kernel)
theorem Check279.part35760 : Interval test 35760 35776 :=
  interval_of_check _ 35760 16 (by decide +kernel)
theorem Check279.part35776 : Interval test 35776 35792 :=
  interval_of_check _ 35776 16 (by decide +kernel)
theorem Check279.part35792 : Interval test 35792 35808 :=
  interval_of_check _ 35792 16 (by decide +kernel)
theorem Check279.part35808 : Interval test 35808 35824 :=
  interval_of_check _ 35808 16 (by decide +kernel)
theorem Check279.part35824 : Interval test 35824 35840 :=
  interval_of_check _ 35824 16 (by decide +kernel)
theorem Check279.checked : Interval test 35712 35840 :=
  (FiniteChecks.interval_append test 35712 35776 35840
  (FiniteChecks.interval_append test 35712 35744 35776
  (FiniteChecks.interval_append test 35712 35728 35744
  Check279.part35712
  Check279.part35728)
  (FiniteChecks.interval_append test 35744 35760 35776
  Check279.part35744
  Check279.part35760))
  (FiniteChecks.interval_append test 35776 35808 35840
  (FiniteChecks.interval_append test 35776 35792 35808
  Check279.part35776
  Check279.part35792)
  (FiniteChecks.interval_append test 35808 35824 35840
  Check279.part35808
  Check279.part35824)))
#print axioms Check279.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
