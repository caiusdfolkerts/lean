module
prelude
public import SharedSix0CellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check160.part20480 : Interval test 20480 20496 :=
  interval_of_check _ 20480 16 (by decide +kernel)
theorem Check160.part20496 : Interval test 20496 20512 :=
  interval_of_check _ 20496 16 (by decide +kernel)
theorem Check160.part20512 : Interval test 20512 20528 :=
  interval_of_check _ 20512 16 (by decide +kernel)
theorem Check160.part20528 : Interval test 20528 20544 :=
  interval_of_check _ 20528 16 (by decide +kernel)
theorem Check160.part20544 : Interval test 20544 20560 :=
  interval_of_check _ 20544 16 (by decide +kernel)
theorem Check160.part20560 : Interval test 20560 20576 :=
  interval_of_check _ 20560 16 (by decide +kernel)
theorem Check160.part20576 : Interval test 20576 20592 :=
  interval_of_check _ 20576 16 (by decide +kernel)
theorem Check160.part20592 : Interval test 20592 20608 :=
  interval_of_check _ 20592 16 (by decide +kernel)
theorem Check160.checked : Interval test 20480 20608 :=
  (FiniteChecks.interval_append test 20480 20544 20608
  (FiniteChecks.interval_append test 20480 20512 20544
  (FiniteChecks.interval_append test 20480 20496 20512
  Check160.part20480
  Check160.part20496)
  (FiniteChecks.interval_append test 20512 20528 20544
  Check160.part20512
  Check160.part20528))
  (FiniteChecks.interval_append test 20544 20576 20608
  (FiniteChecks.interval_append test 20544 20560 20576
  Check160.part20544
  Check160.part20560)
  (FiniteChecks.interval_append test 20576 20592 20608
  Check160.part20576
  Check160.part20592)))
#print axioms Check160.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check161.part20608 : Interval test 20608 20624 :=
  interval_of_check _ 20608 16 (by decide +kernel)
theorem Check161.part20624 : Interval test 20624 20640 :=
  interval_of_check _ 20624 16 (by decide +kernel)
theorem Check161.part20640 : Interval test 20640 20656 :=
  interval_of_check _ 20640 16 (by decide +kernel)
theorem Check161.part20656 : Interval test 20656 20672 :=
  interval_of_check _ 20656 16 (by decide +kernel)
theorem Check161.part20672 : Interval test 20672 20688 :=
  interval_of_check _ 20672 16 (by decide +kernel)
theorem Check161.part20688 : Interval test 20688 20704 :=
  interval_of_check _ 20688 16 (by decide +kernel)
theorem Check161.part20704 : Interval test 20704 20720 :=
  interval_of_check _ 20704 16 (by decide +kernel)
theorem Check161.part20720 : Interval test 20720 20736 :=
  interval_of_check _ 20720 16 (by decide +kernel)
theorem Check161.checked : Interval test 20608 20736 :=
  (FiniteChecks.interval_append test 20608 20672 20736
  (FiniteChecks.interval_append test 20608 20640 20672
  (FiniteChecks.interval_append test 20608 20624 20640
  Check161.part20608
  Check161.part20624)
  (FiniteChecks.interval_append test 20640 20656 20672
  Check161.part20640
  Check161.part20656))
  (FiniteChecks.interval_append test 20672 20704 20736
  (FiniteChecks.interval_append test 20672 20688 20704
  Check161.part20672
  Check161.part20688)
  (FiniteChecks.interval_append test 20704 20720 20736
  Check161.part20704
  Check161.part20720)))
#print axioms Check161.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check162.part20736 : Interval test 20736 20752 :=
  interval_of_check _ 20736 16 (by decide +kernel)
theorem Check162.part20752 : Interval test 20752 20768 :=
  interval_of_check _ 20752 16 (by decide +kernel)
theorem Check162.part20768 : Interval test 20768 20784 :=
  interval_of_check _ 20768 16 (by decide +kernel)
theorem Check162.part20784 : Interval test 20784 20800 :=
  interval_of_check _ 20784 16 (by decide +kernel)
theorem Check162.part20800 : Interval test 20800 20816 :=
  interval_of_check _ 20800 16 (by decide +kernel)
theorem Check162.part20816 : Interval test 20816 20832 :=
  interval_of_check _ 20816 16 (by decide +kernel)
theorem Check162.part20832 : Interval test 20832 20848 :=
  interval_of_check _ 20832 16 (by decide +kernel)
theorem Check162.part20848 : Interval test 20848 20864 :=
  interval_of_check _ 20848 16 (by decide +kernel)
theorem Check162.checked : Interval test 20736 20864 :=
  (FiniteChecks.interval_append test 20736 20800 20864
  (FiniteChecks.interval_append test 20736 20768 20800
  (FiniteChecks.interval_append test 20736 20752 20768
  Check162.part20736
  Check162.part20752)
  (FiniteChecks.interval_append test 20768 20784 20800
  Check162.part20768
  Check162.part20784))
  (FiniteChecks.interval_append test 20800 20832 20864
  (FiniteChecks.interval_append test 20800 20816 20832
  Check162.part20800
  Check162.part20816)
  (FiniteChecks.interval_append test 20832 20848 20864
  Check162.part20832
  Check162.part20848)))
#print axioms Check162.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check163.part20864 : Interval test 20864 20880 :=
  interval_of_check _ 20864 16 (by decide +kernel)
theorem Check163.part20880 : Interval test 20880 20896 :=
  interval_of_check _ 20880 16 (by decide +kernel)
theorem Check163.part20896 : Interval test 20896 20912 :=
  interval_of_check _ 20896 16 (by decide +kernel)
theorem Check163.part20912 : Interval test 20912 20928 :=
  interval_of_check _ 20912 16 (by decide +kernel)
theorem Check163.part20928 : Interval test 20928 20944 :=
  interval_of_check _ 20928 16 (by decide +kernel)
theorem Check163.part20944 : Interval test 20944 20960 :=
  interval_of_check _ 20944 16 (by decide +kernel)
theorem Check163.part20960 : Interval test 20960 20976 :=
  interval_of_check _ 20960 16 (by decide +kernel)
theorem Check163.part20976 : Interval test 20976 20992 :=
  interval_of_check _ 20976 16 (by decide +kernel)
theorem Check163.checked : Interval test 20864 20992 :=
  (FiniteChecks.interval_append test 20864 20928 20992
  (FiniteChecks.interval_append test 20864 20896 20928
  (FiniteChecks.interval_append test 20864 20880 20896
  Check163.part20864
  Check163.part20880)
  (FiniteChecks.interval_append test 20896 20912 20928
  Check163.part20896
  Check163.part20912))
  (FiniteChecks.interval_append test 20928 20960 20992
  (FiniteChecks.interval_append test 20928 20944 20960
  Check163.part20928
  Check163.part20944)
  (FiniteChecks.interval_append test 20960 20976 20992
  Check163.part20960
  Check163.part20976)))
#print axioms Check163.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check164.part20992 : Interval test 20992 21008 :=
  interval_of_check _ 20992 16 (by decide +kernel)
theorem Check164.part21008 : Interval test 21008 21024 :=
  interval_of_check _ 21008 16 (by decide +kernel)
theorem Check164.part21024 : Interval test 21024 21040 :=
  interval_of_check _ 21024 16 (by decide +kernel)
theorem Check164.part21040 : Interval test 21040 21056 :=
  interval_of_check _ 21040 16 (by decide +kernel)
theorem Check164.part21056 : Interval test 21056 21072 :=
  interval_of_check _ 21056 16 (by decide +kernel)
theorem Check164.part21072 : Interval test 21072 21088 :=
  interval_of_check _ 21072 16 (by decide +kernel)
theorem Check164.part21088 : Interval test 21088 21104 :=
  interval_of_check _ 21088 16 (by decide +kernel)
theorem Check164.part21104 : Interval test 21104 21120 :=
  interval_of_check _ 21104 16 (by decide +kernel)
theorem Check164.checked : Interval test 20992 21120 :=
  (FiniteChecks.interval_append test 20992 21056 21120
  (FiniteChecks.interval_append test 20992 21024 21056
  (FiniteChecks.interval_append test 20992 21008 21024
  Check164.part20992
  Check164.part21008)
  (FiniteChecks.interval_append test 21024 21040 21056
  Check164.part21024
  Check164.part21040))
  (FiniteChecks.interval_append test 21056 21088 21120
  (FiniteChecks.interval_append test 21056 21072 21088
  Check164.part21056
  Check164.part21072)
  (FiniteChecks.interval_append test 21088 21104 21120
  Check164.part21088
  Check164.part21104)))
#print axioms Check164.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check165.part21120 : Interval test 21120 21136 :=
  interval_of_check _ 21120 16 (by decide +kernel)
theorem Check165.part21136 : Interval test 21136 21152 :=
  interval_of_check _ 21136 16 (by decide +kernel)
theorem Check165.part21152 : Interval test 21152 21168 :=
  interval_of_check _ 21152 16 (by decide +kernel)
theorem Check165.part21168 : Interval test 21168 21184 :=
  interval_of_check _ 21168 16 (by decide +kernel)
theorem Check165.part21184 : Interval test 21184 21200 :=
  interval_of_check _ 21184 16 (by decide +kernel)
theorem Check165.part21200 : Interval test 21200 21216 :=
  interval_of_check _ 21200 16 (by decide +kernel)
theorem Check165.part21216 : Interval test 21216 21232 :=
  interval_of_check _ 21216 16 (by decide +kernel)
theorem Check165.part21232 : Interval test 21232 21248 :=
  interval_of_check _ 21232 16 (by decide +kernel)
theorem Check165.checked : Interval test 21120 21248 :=
  (FiniteChecks.interval_append test 21120 21184 21248
  (FiniteChecks.interval_append test 21120 21152 21184
  (FiniteChecks.interval_append test 21120 21136 21152
  Check165.part21120
  Check165.part21136)
  (FiniteChecks.interval_append test 21152 21168 21184
  Check165.part21152
  Check165.part21168))
  (FiniteChecks.interval_append test 21184 21216 21248
  (FiniteChecks.interval_append test 21184 21200 21216
  Check165.part21184
  Check165.part21200)
  (FiniteChecks.interval_append test 21216 21232 21248
  Check165.part21216
  Check165.part21232)))
#print axioms Check165.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check166.part21248 : Interval test 21248 21264 :=
  interval_of_check _ 21248 16 (by decide +kernel)
theorem Check166.part21264 : Interval test 21264 21280 :=
  interval_of_check _ 21264 16 (by decide +kernel)
theorem Check166.part21280 : Interval test 21280 21296 :=
  interval_of_check _ 21280 16 (by decide +kernel)
theorem Check166.part21296 : Interval test 21296 21312 :=
  interval_of_check _ 21296 16 (by decide +kernel)
theorem Check166.part21312 : Interval test 21312 21328 :=
  interval_of_check _ 21312 16 (by decide +kernel)
theorem Check166.part21328 : Interval test 21328 21344 :=
  interval_of_check _ 21328 16 (by decide +kernel)
theorem Check166.part21344 : Interval test 21344 21360 :=
  interval_of_check _ 21344 16 (by decide +kernel)
theorem Check166.part21360 : Interval test 21360 21376 :=
  interval_of_check _ 21360 16 (by decide +kernel)
theorem Check166.checked : Interval test 21248 21376 :=
  (FiniteChecks.interval_append test 21248 21312 21376
  (FiniteChecks.interval_append test 21248 21280 21312
  (FiniteChecks.interval_append test 21248 21264 21280
  Check166.part21248
  Check166.part21264)
  (FiniteChecks.interval_append test 21280 21296 21312
  Check166.part21280
  Check166.part21296))
  (FiniteChecks.interval_append test 21312 21344 21376
  (FiniteChecks.interval_append test 21312 21328 21344
  Check166.part21312
  Check166.part21328)
  (FiniteChecks.interval_append test 21344 21360 21376
  Check166.part21344
  Check166.part21360)))
#print axioms Check166.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check167.part21376 : Interval test 21376 21392 :=
  interval_of_check _ 21376 16 (by decide +kernel)
theorem Check167.part21392 : Interval test 21392 21408 :=
  interval_of_check _ 21392 16 (by decide +kernel)
theorem Check167.part21408 : Interval test 21408 21424 :=
  interval_of_check _ 21408 16 (by decide +kernel)
theorem Check167.part21424 : Interval test 21424 21440 :=
  interval_of_check _ 21424 16 (by decide +kernel)
theorem Check167.part21440 : Interval test 21440 21456 :=
  interval_of_check _ 21440 16 (by decide +kernel)
theorem Check167.part21456 : Interval test 21456 21472 :=
  interval_of_check _ 21456 16 (by decide +kernel)
theorem Check167.part21472 : Interval test 21472 21488 :=
  interval_of_check _ 21472 16 (by decide +kernel)
theorem Check167.part21488 : Interval test 21488 21504 :=
  interval_of_check _ 21488 16 (by decide +kernel)
theorem Check167.checked : Interval test 21376 21504 :=
  (FiniteChecks.interval_append test 21376 21440 21504
  (FiniteChecks.interval_append test 21376 21408 21440
  (FiniteChecks.interval_append test 21376 21392 21408
  Check167.part21376
  Check167.part21392)
  (FiniteChecks.interval_append test 21408 21424 21440
  Check167.part21408
  Check167.part21424))
  (FiniteChecks.interval_append test 21440 21472 21504
  (FiniteChecks.interval_append test 21440 21456 21472
  Check167.part21440
  Check167.part21456)
  (FiniteChecks.interval_append test 21472 21488 21504
  Check167.part21472
  Check167.part21488)))
#print axioms Check167.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check168.part21504 : Interval test 21504 21520 :=
  interval_of_check _ 21504 16 (by decide +kernel)
theorem Check168.part21520 : Interval test 21520 21536 :=
  interval_of_check _ 21520 16 (by decide +kernel)
theorem Check168.part21536 : Interval test 21536 21552 :=
  interval_of_check _ 21536 16 (by decide +kernel)
theorem Check168.part21552 : Interval test 21552 21568 :=
  interval_of_check _ 21552 16 (by decide +kernel)
theorem Check168.part21568 : Interval test 21568 21584 :=
  interval_of_check _ 21568 16 (by decide +kernel)
theorem Check168.part21584 : Interval test 21584 21600 :=
  interval_of_check _ 21584 16 (by decide +kernel)
theorem Check168.part21600 : Interval test 21600 21616 :=
  interval_of_check _ 21600 16 (by decide +kernel)
theorem Check168.part21616 : Interval test 21616 21632 :=
  interval_of_check _ 21616 16 (by decide +kernel)
theorem Check168.checked : Interval test 21504 21632 :=
  (FiniteChecks.interval_append test 21504 21568 21632
  (FiniteChecks.interval_append test 21504 21536 21568
  (FiniteChecks.interval_append test 21504 21520 21536
  Check168.part21504
  Check168.part21520)
  (FiniteChecks.interval_append test 21536 21552 21568
  Check168.part21536
  Check168.part21552))
  (FiniteChecks.interval_append test 21568 21600 21632
  (FiniteChecks.interval_append test 21568 21584 21600
  Check168.part21568
  Check168.part21584)
  (FiniteChecks.interval_append test 21600 21616 21632
  Check168.part21600
  Check168.part21616)))
#print axioms Check168.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check169.part21632 : Interval test 21632 21648 :=
  interval_of_check _ 21632 16 (by decide +kernel)
theorem Check169.part21648 : Interval test 21648 21664 :=
  interval_of_check _ 21648 16 (by decide +kernel)
theorem Check169.part21664 : Interval test 21664 21680 :=
  interval_of_check _ 21664 16 (by decide +kernel)
theorem Check169.part21680 : Interval test 21680 21696 :=
  interval_of_check _ 21680 16 (by decide +kernel)
theorem Check169.part21696 : Interval test 21696 21712 :=
  interval_of_check _ 21696 16 (by decide +kernel)
theorem Check169.part21712 : Interval test 21712 21728 :=
  interval_of_check _ 21712 16 (by decide +kernel)
theorem Check169.part21728 : Interval test 21728 21744 :=
  interval_of_check _ 21728 16 (by decide +kernel)
theorem Check169.part21744 : Interval test 21744 21760 :=
  interval_of_check _ 21744 16 (by decide +kernel)
theorem Check169.checked : Interval test 21632 21760 :=
  (FiniteChecks.interval_append test 21632 21696 21760
  (FiniteChecks.interval_append test 21632 21664 21696
  (FiniteChecks.interval_append test 21632 21648 21664
  Check169.part21632
  Check169.part21648)
  (FiniteChecks.interval_append test 21664 21680 21696
  Check169.part21664
  Check169.part21680))
  (FiniteChecks.interval_append test 21696 21728 21760
  (FiniteChecks.interval_append test 21696 21712 21728
  Check169.part21696
  Check169.part21712)
  (FiniteChecks.interval_append test 21728 21744 21760
  Check169.part21728
  Check169.part21744)))
#print axioms Check169.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check170.part21760 : Interval test 21760 21776 :=
  interval_of_check _ 21760 16 (by decide +kernel)
theorem Check170.part21776 : Interval test 21776 21792 :=
  interval_of_check _ 21776 16 (by decide +kernel)
theorem Check170.part21792 : Interval test 21792 21808 :=
  interval_of_check _ 21792 16 (by decide +kernel)
theorem Check170.part21808 : Interval test 21808 21824 :=
  interval_of_check _ 21808 16 (by decide +kernel)
theorem Check170.part21824 : Interval test 21824 21840 :=
  interval_of_check _ 21824 16 (by decide +kernel)
theorem Check170.part21840 : Interval test 21840 21856 :=
  interval_of_check _ 21840 16 (by decide +kernel)
theorem Check170.part21856 : Interval test 21856 21872 :=
  interval_of_check _ 21856 16 (by decide +kernel)
theorem Check170.part21872 : Interval test 21872 21888 :=
  interval_of_check _ 21872 16 (by decide +kernel)
theorem Check170.checked : Interval test 21760 21888 :=
  (FiniteChecks.interval_append test 21760 21824 21888
  (FiniteChecks.interval_append test 21760 21792 21824
  (FiniteChecks.interval_append test 21760 21776 21792
  Check170.part21760
  Check170.part21776)
  (FiniteChecks.interval_append test 21792 21808 21824
  Check170.part21792
  Check170.part21808))
  (FiniteChecks.interval_append test 21824 21856 21888
  (FiniteChecks.interval_append test 21824 21840 21856
  Check170.part21824
  Check170.part21840)
  (FiniteChecks.interval_append test 21856 21872 21888
  Check170.part21856
  Check170.part21872)))
#print axioms Check170.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check171.part21888 : Interval test 21888 21904 :=
  interval_of_check _ 21888 16 (by decide +kernel)
theorem Check171.part21904 : Interval test 21904 21920 :=
  interval_of_check _ 21904 16 (by decide +kernel)
theorem Check171.part21920 : Interval test 21920 21936 :=
  interval_of_check _ 21920 16 (by decide +kernel)
theorem Check171.part21936 : Interval test 21936 21952 :=
  interval_of_check _ 21936 16 (by decide +kernel)
theorem Check171.part21952 : Interval test 21952 21968 :=
  interval_of_check _ 21952 16 (by decide +kernel)
theorem Check171.part21968 : Interval test 21968 21984 :=
  interval_of_check _ 21968 16 (by decide +kernel)
theorem Check171.part21984 : Interval test 21984 22000 :=
  interval_of_check _ 21984 16 (by decide +kernel)
theorem Check171.part22000 : Interval test 22000 22016 :=
  interval_of_check _ 22000 16 (by decide +kernel)
theorem Check171.checked : Interval test 21888 22016 :=
  (FiniteChecks.interval_append test 21888 21952 22016
  (FiniteChecks.interval_append test 21888 21920 21952
  (FiniteChecks.interval_append test 21888 21904 21920
  Check171.part21888
  Check171.part21904)
  (FiniteChecks.interval_append test 21920 21936 21952
  Check171.part21920
  Check171.part21936))
  (FiniteChecks.interval_append test 21952 21984 22016
  (FiniteChecks.interval_append test 21952 21968 21984
  Check171.part21952
  Check171.part21968)
  (FiniteChecks.interval_append test 21984 22000 22016
  Check171.part21984
  Check171.part22000)))
#print axioms Check171.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check172.part22016 : Interval test 22016 22032 :=
  interval_of_check _ 22016 16 (by decide +kernel)
theorem Check172.part22032 : Interval test 22032 22048 :=
  interval_of_check _ 22032 16 (by decide +kernel)
theorem Check172.part22048 : Interval test 22048 22064 :=
  interval_of_check _ 22048 16 (by decide +kernel)
theorem Check172.part22064 : Interval test 22064 22080 :=
  interval_of_check _ 22064 16 (by decide +kernel)
theorem Check172.part22080 : Interval test 22080 22096 :=
  interval_of_check _ 22080 16 (by decide +kernel)
theorem Check172.part22096 : Interval test 22096 22112 :=
  interval_of_check _ 22096 16 (by decide +kernel)
theorem Check172.part22112 : Interval test 22112 22128 :=
  interval_of_check _ 22112 16 (by decide +kernel)
theorem Check172.part22128 : Interval test 22128 22144 :=
  interval_of_check _ 22128 16 (by decide +kernel)
theorem Check172.checked : Interval test 22016 22144 :=
  (FiniteChecks.interval_append test 22016 22080 22144
  (FiniteChecks.interval_append test 22016 22048 22080
  (FiniteChecks.interval_append test 22016 22032 22048
  Check172.part22016
  Check172.part22032)
  (FiniteChecks.interval_append test 22048 22064 22080
  Check172.part22048
  Check172.part22064))
  (FiniteChecks.interval_append test 22080 22112 22144
  (FiniteChecks.interval_append test 22080 22096 22112
  Check172.part22080
  Check172.part22096)
  (FiniteChecks.interval_append test 22112 22128 22144
  Check172.part22112
  Check172.part22128)))
#print axioms Check172.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check173.part22144 : Interval test 22144 22160 :=
  interval_of_check _ 22144 16 (by decide +kernel)
theorem Check173.part22160 : Interval test 22160 22176 :=
  interval_of_check _ 22160 16 (by decide +kernel)
theorem Check173.part22176 : Interval test 22176 22192 :=
  interval_of_check _ 22176 16 (by decide +kernel)
theorem Check173.part22192 : Interval test 22192 22208 :=
  interval_of_check _ 22192 16 (by decide +kernel)
theorem Check173.part22208 : Interval test 22208 22224 :=
  interval_of_check _ 22208 16 (by decide +kernel)
theorem Check173.part22224 : Interval test 22224 22240 :=
  interval_of_check _ 22224 16 (by decide +kernel)
theorem Check173.part22240 : Interval test 22240 22256 :=
  interval_of_check _ 22240 16 (by decide +kernel)
theorem Check173.part22256 : Interval test 22256 22272 :=
  interval_of_check _ 22256 16 (by decide +kernel)
theorem Check173.checked : Interval test 22144 22272 :=
  (FiniteChecks.interval_append test 22144 22208 22272
  (FiniteChecks.interval_append test 22144 22176 22208
  (FiniteChecks.interval_append test 22144 22160 22176
  Check173.part22144
  Check173.part22160)
  (FiniteChecks.interval_append test 22176 22192 22208
  Check173.part22176
  Check173.part22192))
  (FiniteChecks.interval_append test 22208 22240 22272
  (FiniteChecks.interval_append test 22208 22224 22240
  Check173.part22208
  Check173.part22224)
  (FiniteChecks.interval_append test 22240 22256 22272
  Check173.part22240
  Check173.part22256)))
#print axioms Check173.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check174.part22272 : Interval test 22272 22288 :=
  interval_of_check _ 22272 16 (by decide +kernel)
theorem Check174.part22288 : Interval test 22288 22304 :=
  interval_of_check _ 22288 16 (by decide +kernel)
theorem Check174.part22304 : Interval test 22304 22320 :=
  interval_of_check _ 22304 16 (by decide +kernel)
theorem Check174.part22320 : Interval test 22320 22336 :=
  interval_of_check _ 22320 16 (by decide +kernel)
theorem Check174.part22336 : Interval test 22336 22352 :=
  interval_of_check _ 22336 16 (by decide +kernel)
theorem Check174.part22352 : Interval test 22352 22368 :=
  interval_of_check _ 22352 16 (by decide +kernel)
theorem Check174.part22368 : Interval test 22368 22384 :=
  interval_of_check _ 22368 16 (by decide +kernel)
theorem Check174.part22384 : Interval test 22384 22400 :=
  interval_of_check _ 22384 16 (by decide +kernel)
theorem Check174.checked : Interval test 22272 22400 :=
  (FiniteChecks.interval_append test 22272 22336 22400
  (FiniteChecks.interval_append test 22272 22304 22336
  (FiniteChecks.interval_append test 22272 22288 22304
  Check174.part22272
  Check174.part22288)
  (FiniteChecks.interval_append test 22304 22320 22336
  Check174.part22304
  Check174.part22320))
  (FiniteChecks.interval_append test 22336 22368 22400
  (FiniteChecks.interval_append test 22336 22352 22368
  Check174.part22336
  Check174.part22352)
  (FiniteChecks.interval_append test 22368 22384 22400
  Check174.part22368
  Check174.part22384)))
#print axioms Check174.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check175.part22400 : Interval test 22400 22416 :=
  interval_of_check _ 22400 16 (by decide +kernel)
theorem Check175.part22416 : Interval test 22416 22432 :=
  interval_of_check _ 22416 16 (by decide +kernel)
theorem Check175.part22432 : Interval test 22432 22448 :=
  interval_of_check _ 22432 16 (by decide +kernel)
theorem Check175.part22448 : Interval test 22448 22464 :=
  interval_of_check _ 22448 16 (by decide +kernel)
theorem Check175.part22464 : Interval test 22464 22480 :=
  interval_of_check _ 22464 16 (by decide +kernel)
theorem Check175.part22480 : Interval test 22480 22496 :=
  interval_of_check _ 22480 16 (by decide +kernel)
theorem Check175.part22496 : Interval test 22496 22512 :=
  interval_of_check _ 22496 16 (by decide +kernel)
theorem Check175.part22512 : Interval test 22512 22528 :=
  interval_of_check _ 22512 16 (by decide +kernel)
theorem Check175.checked : Interval test 22400 22528 :=
  (FiniteChecks.interval_append test 22400 22464 22528
  (FiniteChecks.interval_append test 22400 22432 22464
  (FiniteChecks.interval_append test 22400 22416 22432
  Check175.part22400
  Check175.part22416)
  (FiniteChecks.interval_append test 22432 22448 22464
  Check175.part22432
  Check175.part22448))
  (FiniteChecks.interval_append test 22464 22496 22528
  (FiniteChecks.interval_append test 22464 22480 22496
  Check175.part22464
  Check175.part22480)
  (FiniteChecks.interval_append test 22496 22512 22528
  Check175.part22496
  Check175.part22512)))
#print axioms Check175.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check176.part22528 : Interval test 22528 22544 :=
  interval_of_check _ 22528 16 (by decide +kernel)
theorem Check176.part22544 : Interval test 22544 22560 :=
  interval_of_check _ 22544 16 (by decide +kernel)
theorem Check176.part22560 : Interval test 22560 22576 :=
  interval_of_check _ 22560 16 (by decide +kernel)
theorem Check176.part22576 : Interval test 22576 22592 :=
  interval_of_check _ 22576 16 (by decide +kernel)
theorem Check176.part22592 : Interval test 22592 22608 :=
  interval_of_check _ 22592 16 (by decide +kernel)
theorem Check176.part22608 : Interval test 22608 22624 :=
  interval_of_check _ 22608 16 (by decide +kernel)
theorem Check176.part22624 : Interval test 22624 22640 :=
  interval_of_check _ 22624 16 (by decide +kernel)
theorem Check176.part22640 : Interval test 22640 22656 :=
  interval_of_check _ 22640 16 (by decide +kernel)
theorem Check176.checked : Interval test 22528 22656 :=
  (FiniteChecks.interval_append test 22528 22592 22656
  (FiniteChecks.interval_append test 22528 22560 22592
  (FiniteChecks.interval_append test 22528 22544 22560
  Check176.part22528
  Check176.part22544)
  (FiniteChecks.interval_append test 22560 22576 22592
  Check176.part22560
  Check176.part22576))
  (FiniteChecks.interval_append test 22592 22624 22656
  (FiniteChecks.interval_append test 22592 22608 22624
  Check176.part22592
  Check176.part22608)
  (FiniteChecks.interval_append test 22624 22640 22656
  Check176.part22624
  Check176.part22640)))
#print axioms Check176.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check177.part22656 : Interval test 22656 22672 :=
  interval_of_check _ 22656 16 (by decide +kernel)
theorem Check177.part22672 : Interval test 22672 22688 :=
  interval_of_check _ 22672 16 (by decide +kernel)
theorem Check177.part22688 : Interval test 22688 22704 :=
  interval_of_check _ 22688 16 (by decide +kernel)
theorem Check177.part22704 : Interval test 22704 22720 :=
  interval_of_check _ 22704 16 (by decide +kernel)
theorem Check177.part22720 : Interval test 22720 22736 :=
  interval_of_check _ 22720 16 (by decide +kernel)
theorem Check177.part22736 : Interval test 22736 22752 :=
  interval_of_check _ 22736 16 (by decide +kernel)
theorem Check177.part22752 : Interval test 22752 22768 :=
  interval_of_check _ 22752 16 (by decide +kernel)
theorem Check177.part22768 : Interval test 22768 22784 :=
  interval_of_check _ 22768 16 (by decide +kernel)
theorem Check177.checked : Interval test 22656 22784 :=
  (FiniteChecks.interval_append test 22656 22720 22784
  (FiniteChecks.interval_append test 22656 22688 22720
  (FiniteChecks.interval_append test 22656 22672 22688
  Check177.part22656
  Check177.part22672)
  (FiniteChecks.interval_append test 22688 22704 22720
  Check177.part22688
  Check177.part22704))
  (FiniteChecks.interval_append test 22720 22752 22784
  (FiniteChecks.interval_append test 22720 22736 22752
  Check177.part22720
  Check177.part22736)
  (FiniteChecks.interval_append test 22752 22768 22784
  Check177.part22752
  Check177.part22768)))
#print axioms Check177.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check178.part22784 : Interval test 22784 22800 :=
  interval_of_check _ 22784 16 (by decide +kernel)
theorem Check178.part22800 : Interval test 22800 22816 :=
  interval_of_check _ 22800 16 (by decide +kernel)
theorem Check178.part22816 : Interval test 22816 22832 :=
  interval_of_check _ 22816 16 (by decide +kernel)
theorem Check178.part22832 : Interval test 22832 22848 :=
  interval_of_check _ 22832 16 (by decide +kernel)
theorem Check178.part22848 : Interval test 22848 22864 :=
  interval_of_check _ 22848 16 (by decide +kernel)
theorem Check178.part22864 : Interval test 22864 22880 :=
  interval_of_check _ 22864 16 (by decide +kernel)
theorem Check178.part22880 : Interval test 22880 22896 :=
  interval_of_check _ 22880 16 (by decide +kernel)
theorem Check178.part22896 : Interval test 22896 22912 :=
  interval_of_check _ 22896 16 (by decide +kernel)
theorem Check178.checked : Interval test 22784 22912 :=
  (FiniteChecks.interval_append test 22784 22848 22912
  (FiniteChecks.interval_append test 22784 22816 22848
  (FiniteChecks.interval_append test 22784 22800 22816
  Check178.part22784
  Check178.part22800)
  (FiniteChecks.interval_append test 22816 22832 22848
  Check178.part22816
  Check178.part22832))
  (FiniteChecks.interval_append test 22848 22880 22912
  (FiniteChecks.interval_append test 22848 22864 22880
  Check178.part22848
  Check178.part22864)
  (FiniteChecks.interval_append test 22880 22896 22912
  Check178.part22880
  Check178.part22896)))
#print axioms Check178.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check179.part22912 : Interval test 22912 22928 :=
  interval_of_check _ 22912 16 (by decide +kernel)
theorem Check179.part22928 : Interval test 22928 22944 :=
  interval_of_check _ 22928 16 (by decide +kernel)
theorem Check179.part22944 : Interval test 22944 22960 :=
  interval_of_check _ 22944 16 (by decide +kernel)
theorem Check179.part22960 : Interval test 22960 22976 :=
  interval_of_check _ 22960 16 (by decide +kernel)
theorem Check179.part22976 : Interval test 22976 22992 :=
  interval_of_check _ 22976 16 (by decide +kernel)
theorem Check179.part22992 : Interval test 22992 23008 :=
  interval_of_check _ 22992 16 (by decide +kernel)
theorem Check179.part23008 : Interval test 23008 23024 :=
  interval_of_check _ 23008 16 (by decide +kernel)
theorem Check179.part23024 : Interval test 23024 23040 :=
  interval_of_check _ 23024 16 (by decide +kernel)
theorem Check179.checked : Interval test 22912 23040 :=
  (FiniteChecks.interval_append test 22912 22976 23040
  (FiniteChecks.interval_append test 22912 22944 22976
  (FiniteChecks.interval_append test 22912 22928 22944
  Check179.part22912
  Check179.part22928)
  (FiniteChecks.interval_append test 22944 22960 22976
  Check179.part22944
  Check179.part22960))
  (FiniteChecks.interval_append test 22976 23008 23040
  (FiniteChecks.interval_append test 22976 22992 23008
  Check179.part22976
  Check179.part22992)
  (FiniteChecks.interval_append test 23008 23024 23040
  Check179.part23008
  Check179.part23024)))
#print axioms Check179.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
