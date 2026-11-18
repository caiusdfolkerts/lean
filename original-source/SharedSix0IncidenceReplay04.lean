module
prelude
public import SharedSix0IncidenceData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check080.part20480 : Interval test 20480 20496 :=
  interval_of_check _ 20480 16 (by decide +kernel)
theorem Check080.part20496 : Interval test 20496 20512 :=
  interval_of_check _ 20496 16 (by decide +kernel)
theorem Check080.part20512 : Interval test 20512 20528 :=
  interval_of_check _ 20512 16 (by decide +kernel)
theorem Check080.part20528 : Interval test 20528 20544 :=
  interval_of_check _ 20528 16 (by decide +kernel)
theorem Check080.part20544 : Interval test 20544 20560 :=
  interval_of_check _ 20544 16 (by decide +kernel)
theorem Check080.part20560 : Interval test 20560 20576 :=
  interval_of_check _ 20560 16 (by decide +kernel)
theorem Check080.part20576 : Interval test 20576 20592 :=
  interval_of_check _ 20576 16 (by decide +kernel)
theorem Check080.part20592 : Interval test 20592 20608 :=
  interval_of_check _ 20592 16 (by decide +kernel)
theorem Check080.part20608 : Interval test 20608 20624 :=
  interval_of_check _ 20608 16 (by decide +kernel)
theorem Check080.part20624 : Interval test 20624 20640 :=
  interval_of_check _ 20624 16 (by decide +kernel)
theorem Check080.part20640 : Interval test 20640 20656 :=
  interval_of_check _ 20640 16 (by decide +kernel)
theorem Check080.part20656 : Interval test 20656 20672 :=
  interval_of_check _ 20656 16 (by decide +kernel)
theorem Check080.part20672 : Interval test 20672 20688 :=
  interval_of_check _ 20672 16 (by decide +kernel)
theorem Check080.part20688 : Interval test 20688 20704 :=
  interval_of_check _ 20688 16 (by decide +kernel)
theorem Check080.part20704 : Interval test 20704 20720 :=
  interval_of_check _ 20704 16 (by decide +kernel)
theorem Check080.part20720 : Interval test 20720 20736 :=
  interval_of_check _ 20720 16 (by decide +kernel)
theorem Check080.checked : Interval test 20480 20736 :=
  (FiniteChecks.interval_append test 20480 20608 20736
  (FiniteChecks.interval_append test 20480 20544 20608
  (FiniteChecks.interval_append test 20480 20512 20544
  (FiniteChecks.interval_append test 20480 20496 20512
  Check080.part20480
  Check080.part20496)
  (FiniteChecks.interval_append test 20512 20528 20544
  Check080.part20512
  Check080.part20528))
  (FiniteChecks.interval_append test 20544 20576 20608
  (FiniteChecks.interval_append test 20544 20560 20576
  Check080.part20544
  Check080.part20560)
  (FiniteChecks.interval_append test 20576 20592 20608
  Check080.part20576
  Check080.part20592)))
  (FiniteChecks.interval_append test 20608 20672 20736
  (FiniteChecks.interval_append test 20608 20640 20672
  (FiniteChecks.interval_append test 20608 20624 20640
  Check080.part20608
  Check080.part20624)
  (FiniteChecks.interval_append test 20640 20656 20672
  Check080.part20640
  Check080.part20656))
  (FiniteChecks.interval_append test 20672 20704 20736
  (FiniteChecks.interval_append test 20672 20688 20704
  Check080.part20672
  Check080.part20688)
  (FiniteChecks.interval_append test 20704 20720 20736
  Check080.part20704
  Check080.part20720))))
#print axioms Check080.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check081.part20736 : Interval test 20736 20752 :=
  interval_of_check _ 20736 16 (by decide +kernel)
theorem Check081.part20752 : Interval test 20752 20768 :=
  interval_of_check _ 20752 16 (by decide +kernel)
theorem Check081.part20768 : Interval test 20768 20784 :=
  interval_of_check _ 20768 16 (by decide +kernel)
theorem Check081.part20784 : Interval test 20784 20800 :=
  interval_of_check _ 20784 16 (by decide +kernel)
theorem Check081.part20800 : Interval test 20800 20816 :=
  interval_of_check _ 20800 16 (by decide +kernel)
theorem Check081.part20816 : Interval test 20816 20832 :=
  interval_of_check _ 20816 16 (by decide +kernel)
theorem Check081.part20832 : Interval test 20832 20848 :=
  interval_of_check _ 20832 16 (by decide +kernel)
theorem Check081.part20848 : Interval test 20848 20864 :=
  interval_of_check _ 20848 16 (by decide +kernel)
theorem Check081.part20864 : Interval test 20864 20880 :=
  interval_of_check _ 20864 16 (by decide +kernel)
theorem Check081.part20880 : Interval test 20880 20896 :=
  interval_of_check _ 20880 16 (by decide +kernel)
theorem Check081.part20896 : Interval test 20896 20912 :=
  interval_of_check _ 20896 16 (by decide +kernel)
theorem Check081.part20912 : Interval test 20912 20928 :=
  interval_of_check _ 20912 16 (by decide +kernel)
theorem Check081.part20928 : Interval test 20928 20944 :=
  interval_of_check _ 20928 16 (by decide +kernel)
theorem Check081.part20944 : Interval test 20944 20960 :=
  interval_of_check _ 20944 16 (by decide +kernel)
theorem Check081.part20960 : Interval test 20960 20976 :=
  interval_of_check _ 20960 16 (by decide +kernel)
theorem Check081.part20976 : Interval test 20976 20992 :=
  interval_of_check _ 20976 16 (by decide +kernel)
theorem Check081.checked : Interval test 20736 20992 :=
  (FiniteChecks.interval_append test 20736 20864 20992
  (FiniteChecks.interval_append test 20736 20800 20864
  (FiniteChecks.interval_append test 20736 20768 20800
  (FiniteChecks.interval_append test 20736 20752 20768
  Check081.part20736
  Check081.part20752)
  (FiniteChecks.interval_append test 20768 20784 20800
  Check081.part20768
  Check081.part20784))
  (FiniteChecks.interval_append test 20800 20832 20864
  (FiniteChecks.interval_append test 20800 20816 20832
  Check081.part20800
  Check081.part20816)
  (FiniteChecks.interval_append test 20832 20848 20864
  Check081.part20832
  Check081.part20848)))
  (FiniteChecks.interval_append test 20864 20928 20992
  (FiniteChecks.interval_append test 20864 20896 20928
  (FiniteChecks.interval_append test 20864 20880 20896
  Check081.part20864
  Check081.part20880)
  (FiniteChecks.interval_append test 20896 20912 20928
  Check081.part20896
  Check081.part20912))
  (FiniteChecks.interval_append test 20928 20960 20992
  (FiniteChecks.interval_append test 20928 20944 20960
  Check081.part20928
  Check081.part20944)
  (FiniteChecks.interval_append test 20960 20976 20992
  Check081.part20960
  Check081.part20976))))
#print axioms Check081.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check082.part20992 : Interval test 20992 21008 :=
  interval_of_check _ 20992 16 (by decide +kernel)
theorem Check082.part21008 : Interval test 21008 21024 :=
  interval_of_check _ 21008 16 (by decide +kernel)
theorem Check082.part21024 : Interval test 21024 21040 :=
  interval_of_check _ 21024 16 (by decide +kernel)
theorem Check082.part21040 : Interval test 21040 21056 :=
  interval_of_check _ 21040 16 (by decide +kernel)
theorem Check082.part21056 : Interval test 21056 21072 :=
  interval_of_check _ 21056 16 (by decide +kernel)
theorem Check082.part21072 : Interval test 21072 21088 :=
  interval_of_check _ 21072 16 (by decide +kernel)
theorem Check082.part21088 : Interval test 21088 21104 :=
  interval_of_check _ 21088 16 (by decide +kernel)
theorem Check082.part21104 : Interval test 21104 21120 :=
  interval_of_check _ 21104 16 (by decide +kernel)
theorem Check082.part21120 : Interval test 21120 21136 :=
  interval_of_check _ 21120 16 (by decide +kernel)
theorem Check082.part21136 : Interval test 21136 21152 :=
  interval_of_check _ 21136 16 (by decide +kernel)
theorem Check082.part21152 : Interval test 21152 21168 :=
  interval_of_check _ 21152 16 (by decide +kernel)
theorem Check082.part21168 : Interval test 21168 21184 :=
  interval_of_check _ 21168 16 (by decide +kernel)
theorem Check082.part21184 : Interval test 21184 21200 :=
  interval_of_check _ 21184 16 (by decide +kernel)
theorem Check082.part21200 : Interval test 21200 21216 :=
  interval_of_check _ 21200 16 (by decide +kernel)
theorem Check082.part21216 : Interval test 21216 21232 :=
  interval_of_check _ 21216 16 (by decide +kernel)
theorem Check082.part21232 : Interval test 21232 21248 :=
  interval_of_check _ 21232 16 (by decide +kernel)
theorem Check082.checked : Interval test 20992 21248 :=
  (FiniteChecks.interval_append test 20992 21120 21248
  (FiniteChecks.interval_append test 20992 21056 21120
  (FiniteChecks.interval_append test 20992 21024 21056
  (FiniteChecks.interval_append test 20992 21008 21024
  Check082.part20992
  Check082.part21008)
  (FiniteChecks.interval_append test 21024 21040 21056
  Check082.part21024
  Check082.part21040))
  (FiniteChecks.interval_append test 21056 21088 21120
  (FiniteChecks.interval_append test 21056 21072 21088
  Check082.part21056
  Check082.part21072)
  (FiniteChecks.interval_append test 21088 21104 21120
  Check082.part21088
  Check082.part21104)))
  (FiniteChecks.interval_append test 21120 21184 21248
  (FiniteChecks.interval_append test 21120 21152 21184
  (FiniteChecks.interval_append test 21120 21136 21152
  Check082.part21120
  Check082.part21136)
  (FiniteChecks.interval_append test 21152 21168 21184
  Check082.part21152
  Check082.part21168))
  (FiniteChecks.interval_append test 21184 21216 21248
  (FiniteChecks.interval_append test 21184 21200 21216
  Check082.part21184
  Check082.part21200)
  (FiniteChecks.interval_append test 21216 21232 21248
  Check082.part21216
  Check082.part21232))))
#print axioms Check082.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check083.part21248 : Interval test 21248 21264 :=
  interval_of_check _ 21248 16 (by decide +kernel)
theorem Check083.part21264 : Interval test 21264 21280 :=
  interval_of_check _ 21264 16 (by decide +kernel)
theorem Check083.part21280 : Interval test 21280 21296 :=
  interval_of_check _ 21280 16 (by decide +kernel)
theorem Check083.part21296 : Interval test 21296 21312 :=
  interval_of_check _ 21296 16 (by decide +kernel)
theorem Check083.part21312 : Interval test 21312 21328 :=
  interval_of_check _ 21312 16 (by decide +kernel)
theorem Check083.part21328 : Interval test 21328 21344 :=
  interval_of_check _ 21328 16 (by decide +kernel)
theorem Check083.part21344 : Interval test 21344 21360 :=
  interval_of_check _ 21344 16 (by decide +kernel)
theorem Check083.part21360 : Interval test 21360 21376 :=
  interval_of_check _ 21360 16 (by decide +kernel)
theorem Check083.part21376 : Interval test 21376 21392 :=
  interval_of_check _ 21376 16 (by decide +kernel)
theorem Check083.part21392 : Interval test 21392 21408 :=
  interval_of_check _ 21392 16 (by decide +kernel)
theorem Check083.part21408 : Interval test 21408 21424 :=
  interval_of_check _ 21408 16 (by decide +kernel)
theorem Check083.part21424 : Interval test 21424 21440 :=
  interval_of_check _ 21424 16 (by decide +kernel)
theorem Check083.part21440 : Interval test 21440 21456 :=
  interval_of_check _ 21440 16 (by decide +kernel)
theorem Check083.part21456 : Interval test 21456 21472 :=
  interval_of_check _ 21456 16 (by decide +kernel)
theorem Check083.part21472 : Interval test 21472 21488 :=
  interval_of_check _ 21472 16 (by decide +kernel)
theorem Check083.part21488 : Interval test 21488 21504 :=
  interval_of_check _ 21488 16 (by decide +kernel)
theorem Check083.checked : Interval test 21248 21504 :=
  (FiniteChecks.interval_append test 21248 21376 21504
  (FiniteChecks.interval_append test 21248 21312 21376
  (FiniteChecks.interval_append test 21248 21280 21312
  (FiniteChecks.interval_append test 21248 21264 21280
  Check083.part21248
  Check083.part21264)
  (FiniteChecks.interval_append test 21280 21296 21312
  Check083.part21280
  Check083.part21296))
  (FiniteChecks.interval_append test 21312 21344 21376
  (FiniteChecks.interval_append test 21312 21328 21344
  Check083.part21312
  Check083.part21328)
  (FiniteChecks.interval_append test 21344 21360 21376
  Check083.part21344
  Check083.part21360)))
  (FiniteChecks.interval_append test 21376 21440 21504
  (FiniteChecks.interval_append test 21376 21408 21440
  (FiniteChecks.interval_append test 21376 21392 21408
  Check083.part21376
  Check083.part21392)
  (FiniteChecks.interval_append test 21408 21424 21440
  Check083.part21408
  Check083.part21424))
  (FiniteChecks.interval_append test 21440 21472 21504
  (FiniteChecks.interval_append test 21440 21456 21472
  Check083.part21440
  Check083.part21456)
  (FiniteChecks.interval_append test 21472 21488 21504
  Check083.part21472
  Check083.part21488))))
#print axioms Check083.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check084.part21504 : Interval test 21504 21520 :=
  interval_of_check _ 21504 16 (by decide +kernel)
theorem Check084.part21520 : Interval test 21520 21536 :=
  interval_of_check _ 21520 16 (by decide +kernel)
theorem Check084.part21536 : Interval test 21536 21552 :=
  interval_of_check _ 21536 16 (by decide +kernel)
theorem Check084.part21552 : Interval test 21552 21568 :=
  interval_of_check _ 21552 16 (by decide +kernel)
theorem Check084.part21568 : Interval test 21568 21584 :=
  interval_of_check _ 21568 16 (by decide +kernel)
theorem Check084.part21584 : Interval test 21584 21600 :=
  interval_of_check _ 21584 16 (by decide +kernel)
theorem Check084.part21600 : Interval test 21600 21616 :=
  interval_of_check _ 21600 16 (by decide +kernel)
theorem Check084.part21616 : Interval test 21616 21632 :=
  interval_of_check _ 21616 16 (by decide +kernel)
theorem Check084.part21632 : Interval test 21632 21648 :=
  interval_of_check _ 21632 16 (by decide +kernel)
theorem Check084.part21648 : Interval test 21648 21664 :=
  interval_of_check _ 21648 16 (by decide +kernel)
theorem Check084.part21664 : Interval test 21664 21680 :=
  interval_of_check _ 21664 16 (by decide +kernel)
theorem Check084.part21680 : Interval test 21680 21696 :=
  interval_of_check _ 21680 16 (by decide +kernel)
theorem Check084.part21696 : Interval test 21696 21712 :=
  interval_of_check _ 21696 16 (by decide +kernel)
theorem Check084.part21712 : Interval test 21712 21728 :=
  interval_of_check _ 21712 16 (by decide +kernel)
theorem Check084.part21728 : Interval test 21728 21744 :=
  interval_of_check _ 21728 16 (by decide +kernel)
theorem Check084.part21744 : Interval test 21744 21760 :=
  interval_of_check _ 21744 16 (by decide +kernel)
theorem Check084.checked : Interval test 21504 21760 :=
  (FiniteChecks.interval_append test 21504 21632 21760
  (FiniteChecks.interval_append test 21504 21568 21632
  (FiniteChecks.interval_append test 21504 21536 21568
  (FiniteChecks.interval_append test 21504 21520 21536
  Check084.part21504
  Check084.part21520)
  (FiniteChecks.interval_append test 21536 21552 21568
  Check084.part21536
  Check084.part21552))
  (FiniteChecks.interval_append test 21568 21600 21632
  (FiniteChecks.interval_append test 21568 21584 21600
  Check084.part21568
  Check084.part21584)
  (FiniteChecks.interval_append test 21600 21616 21632
  Check084.part21600
  Check084.part21616)))
  (FiniteChecks.interval_append test 21632 21696 21760
  (FiniteChecks.interval_append test 21632 21664 21696
  (FiniteChecks.interval_append test 21632 21648 21664
  Check084.part21632
  Check084.part21648)
  (FiniteChecks.interval_append test 21664 21680 21696
  Check084.part21664
  Check084.part21680))
  (FiniteChecks.interval_append test 21696 21728 21760
  (FiniteChecks.interval_append test 21696 21712 21728
  Check084.part21696
  Check084.part21712)
  (FiniteChecks.interval_append test 21728 21744 21760
  Check084.part21728
  Check084.part21744))))
#print axioms Check084.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check085.part21760 : Interval test 21760 21776 :=
  interval_of_check _ 21760 16 (by decide +kernel)
theorem Check085.part21776 : Interval test 21776 21792 :=
  interval_of_check _ 21776 16 (by decide +kernel)
theorem Check085.part21792 : Interval test 21792 21808 :=
  interval_of_check _ 21792 16 (by decide +kernel)
theorem Check085.part21808 : Interval test 21808 21824 :=
  interval_of_check _ 21808 16 (by decide +kernel)
theorem Check085.part21824 : Interval test 21824 21840 :=
  interval_of_check _ 21824 16 (by decide +kernel)
theorem Check085.part21840 : Interval test 21840 21856 :=
  interval_of_check _ 21840 16 (by decide +kernel)
theorem Check085.part21856 : Interval test 21856 21872 :=
  interval_of_check _ 21856 16 (by decide +kernel)
theorem Check085.part21872 : Interval test 21872 21888 :=
  interval_of_check _ 21872 16 (by decide +kernel)
theorem Check085.part21888 : Interval test 21888 21904 :=
  interval_of_check _ 21888 16 (by decide +kernel)
theorem Check085.part21904 : Interval test 21904 21920 :=
  interval_of_check _ 21904 16 (by decide +kernel)
theorem Check085.part21920 : Interval test 21920 21936 :=
  interval_of_check _ 21920 16 (by decide +kernel)
theorem Check085.part21936 : Interval test 21936 21952 :=
  interval_of_check _ 21936 16 (by decide +kernel)
theorem Check085.part21952 : Interval test 21952 21968 :=
  interval_of_check _ 21952 16 (by decide +kernel)
theorem Check085.part21968 : Interval test 21968 21984 :=
  interval_of_check _ 21968 16 (by decide +kernel)
theorem Check085.part21984 : Interval test 21984 22000 :=
  interval_of_check _ 21984 16 (by decide +kernel)
theorem Check085.part22000 : Interval test 22000 22016 :=
  interval_of_check _ 22000 16 (by decide +kernel)
theorem Check085.checked : Interval test 21760 22016 :=
  (FiniteChecks.interval_append test 21760 21888 22016
  (FiniteChecks.interval_append test 21760 21824 21888
  (FiniteChecks.interval_append test 21760 21792 21824
  (FiniteChecks.interval_append test 21760 21776 21792
  Check085.part21760
  Check085.part21776)
  (FiniteChecks.interval_append test 21792 21808 21824
  Check085.part21792
  Check085.part21808))
  (FiniteChecks.interval_append test 21824 21856 21888
  (FiniteChecks.interval_append test 21824 21840 21856
  Check085.part21824
  Check085.part21840)
  (FiniteChecks.interval_append test 21856 21872 21888
  Check085.part21856
  Check085.part21872)))
  (FiniteChecks.interval_append test 21888 21952 22016
  (FiniteChecks.interval_append test 21888 21920 21952
  (FiniteChecks.interval_append test 21888 21904 21920
  Check085.part21888
  Check085.part21904)
  (FiniteChecks.interval_append test 21920 21936 21952
  Check085.part21920
  Check085.part21936))
  (FiniteChecks.interval_append test 21952 21984 22016
  (FiniteChecks.interval_append test 21952 21968 21984
  Check085.part21952
  Check085.part21968)
  (FiniteChecks.interval_append test 21984 22000 22016
  Check085.part21984
  Check085.part22000))))
#print axioms Check085.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check086.part22016 : Interval test 22016 22032 :=
  interval_of_check _ 22016 16 (by decide +kernel)
theorem Check086.part22032 : Interval test 22032 22048 :=
  interval_of_check _ 22032 16 (by decide +kernel)
theorem Check086.part22048 : Interval test 22048 22064 :=
  interval_of_check _ 22048 16 (by decide +kernel)
theorem Check086.part22064 : Interval test 22064 22080 :=
  interval_of_check _ 22064 16 (by decide +kernel)
theorem Check086.part22080 : Interval test 22080 22096 :=
  interval_of_check _ 22080 16 (by decide +kernel)
theorem Check086.part22096 : Interval test 22096 22112 :=
  interval_of_check _ 22096 16 (by decide +kernel)
theorem Check086.part22112 : Interval test 22112 22128 :=
  interval_of_check _ 22112 16 (by decide +kernel)
theorem Check086.part22128 : Interval test 22128 22144 :=
  interval_of_check _ 22128 16 (by decide +kernel)
theorem Check086.part22144 : Interval test 22144 22160 :=
  interval_of_check _ 22144 16 (by decide +kernel)
theorem Check086.part22160 : Interval test 22160 22176 :=
  interval_of_check _ 22160 16 (by decide +kernel)
theorem Check086.part22176 : Interval test 22176 22192 :=
  interval_of_check _ 22176 16 (by decide +kernel)
theorem Check086.part22192 : Interval test 22192 22208 :=
  interval_of_check _ 22192 16 (by decide +kernel)
theorem Check086.part22208 : Interval test 22208 22224 :=
  interval_of_check _ 22208 16 (by decide +kernel)
theorem Check086.part22224 : Interval test 22224 22240 :=
  interval_of_check _ 22224 16 (by decide +kernel)
theorem Check086.part22240 : Interval test 22240 22256 :=
  interval_of_check _ 22240 16 (by decide +kernel)
theorem Check086.part22256 : Interval test 22256 22272 :=
  interval_of_check _ 22256 16 (by decide +kernel)
theorem Check086.checked : Interval test 22016 22272 :=
  (FiniteChecks.interval_append test 22016 22144 22272
  (FiniteChecks.interval_append test 22016 22080 22144
  (FiniteChecks.interval_append test 22016 22048 22080
  (FiniteChecks.interval_append test 22016 22032 22048
  Check086.part22016
  Check086.part22032)
  (FiniteChecks.interval_append test 22048 22064 22080
  Check086.part22048
  Check086.part22064))
  (FiniteChecks.interval_append test 22080 22112 22144
  (FiniteChecks.interval_append test 22080 22096 22112
  Check086.part22080
  Check086.part22096)
  (FiniteChecks.interval_append test 22112 22128 22144
  Check086.part22112
  Check086.part22128)))
  (FiniteChecks.interval_append test 22144 22208 22272
  (FiniteChecks.interval_append test 22144 22176 22208
  (FiniteChecks.interval_append test 22144 22160 22176
  Check086.part22144
  Check086.part22160)
  (FiniteChecks.interval_append test 22176 22192 22208
  Check086.part22176
  Check086.part22192))
  (FiniteChecks.interval_append test 22208 22240 22272
  (FiniteChecks.interval_append test 22208 22224 22240
  Check086.part22208
  Check086.part22224)
  (FiniteChecks.interval_append test 22240 22256 22272
  Check086.part22240
  Check086.part22256))))
#print axioms Check086.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check087.part22272 : Interval test 22272 22288 :=
  interval_of_check _ 22272 16 (by decide +kernel)
theorem Check087.part22288 : Interval test 22288 22304 :=
  interval_of_check _ 22288 16 (by decide +kernel)
theorem Check087.part22304 : Interval test 22304 22320 :=
  interval_of_check _ 22304 16 (by decide +kernel)
theorem Check087.part22320 : Interval test 22320 22336 :=
  interval_of_check _ 22320 16 (by decide +kernel)
theorem Check087.part22336 : Interval test 22336 22352 :=
  interval_of_check _ 22336 16 (by decide +kernel)
theorem Check087.part22352 : Interval test 22352 22368 :=
  interval_of_check _ 22352 16 (by decide +kernel)
theorem Check087.part22368 : Interval test 22368 22384 :=
  interval_of_check _ 22368 16 (by decide +kernel)
theorem Check087.part22384 : Interval test 22384 22400 :=
  interval_of_check _ 22384 16 (by decide +kernel)
theorem Check087.part22400 : Interval test 22400 22416 :=
  interval_of_check _ 22400 16 (by decide +kernel)
theorem Check087.part22416 : Interval test 22416 22432 :=
  interval_of_check _ 22416 16 (by decide +kernel)
theorem Check087.part22432 : Interval test 22432 22448 :=
  interval_of_check _ 22432 16 (by decide +kernel)
theorem Check087.part22448 : Interval test 22448 22464 :=
  interval_of_check _ 22448 16 (by decide +kernel)
theorem Check087.part22464 : Interval test 22464 22480 :=
  interval_of_check _ 22464 16 (by decide +kernel)
theorem Check087.part22480 : Interval test 22480 22496 :=
  interval_of_check _ 22480 16 (by decide +kernel)
theorem Check087.part22496 : Interval test 22496 22512 :=
  interval_of_check _ 22496 16 (by decide +kernel)
theorem Check087.part22512 : Interval test 22512 22528 :=
  interval_of_check _ 22512 16 (by decide +kernel)
theorem Check087.checked : Interval test 22272 22528 :=
  (FiniteChecks.interval_append test 22272 22400 22528
  (FiniteChecks.interval_append test 22272 22336 22400
  (FiniteChecks.interval_append test 22272 22304 22336
  (FiniteChecks.interval_append test 22272 22288 22304
  Check087.part22272
  Check087.part22288)
  (FiniteChecks.interval_append test 22304 22320 22336
  Check087.part22304
  Check087.part22320))
  (FiniteChecks.interval_append test 22336 22368 22400
  (FiniteChecks.interval_append test 22336 22352 22368
  Check087.part22336
  Check087.part22352)
  (FiniteChecks.interval_append test 22368 22384 22400
  Check087.part22368
  Check087.part22384)))
  (FiniteChecks.interval_append test 22400 22464 22528
  (FiniteChecks.interval_append test 22400 22432 22464
  (FiniteChecks.interval_append test 22400 22416 22432
  Check087.part22400
  Check087.part22416)
  (FiniteChecks.interval_append test 22432 22448 22464
  Check087.part22432
  Check087.part22448))
  (FiniteChecks.interval_append test 22464 22496 22528
  (FiniteChecks.interval_append test 22464 22480 22496
  Check087.part22464
  Check087.part22480)
  (FiniteChecks.interval_append test 22496 22512 22528
  Check087.part22496
  Check087.part22512))))
#print axioms Check087.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check088.part22528 : Interval test 22528 22544 :=
  interval_of_check _ 22528 16 (by decide +kernel)
theorem Check088.part22544 : Interval test 22544 22560 :=
  interval_of_check _ 22544 16 (by decide +kernel)
theorem Check088.part22560 : Interval test 22560 22576 :=
  interval_of_check _ 22560 16 (by decide +kernel)
theorem Check088.part22576 : Interval test 22576 22592 :=
  interval_of_check _ 22576 16 (by decide +kernel)
theorem Check088.part22592 : Interval test 22592 22608 :=
  interval_of_check _ 22592 16 (by decide +kernel)
theorem Check088.part22608 : Interval test 22608 22624 :=
  interval_of_check _ 22608 16 (by decide +kernel)
theorem Check088.part22624 : Interval test 22624 22640 :=
  interval_of_check _ 22624 16 (by decide +kernel)
theorem Check088.part22640 : Interval test 22640 22656 :=
  interval_of_check _ 22640 16 (by decide +kernel)
theorem Check088.part22656 : Interval test 22656 22672 :=
  interval_of_check _ 22656 16 (by decide +kernel)
theorem Check088.part22672 : Interval test 22672 22688 :=
  interval_of_check _ 22672 16 (by decide +kernel)
theorem Check088.part22688 : Interval test 22688 22704 :=
  interval_of_check _ 22688 16 (by decide +kernel)
theorem Check088.part22704 : Interval test 22704 22720 :=
  interval_of_check _ 22704 16 (by decide +kernel)
theorem Check088.part22720 : Interval test 22720 22736 :=
  interval_of_check _ 22720 16 (by decide +kernel)
theorem Check088.part22736 : Interval test 22736 22752 :=
  interval_of_check _ 22736 16 (by decide +kernel)
theorem Check088.part22752 : Interval test 22752 22768 :=
  interval_of_check _ 22752 16 (by decide +kernel)
theorem Check088.part22768 : Interval test 22768 22784 :=
  interval_of_check _ 22768 16 (by decide +kernel)
theorem Check088.checked : Interval test 22528 22784 :=
  (FiniteChecks.interval_append test 22528 22656 22784
  (FiniteChecks.interval_append test 22528 22592 22656
  (FiniteChecks.interval_append test 22528 22560 22592
  (FiniteChecks.interval_append test 22528 22544 22560
  Check088.part22528
  Check088.part22544)
  (FiniteChecks.interval_append test 22560 22576 22592
  Check088.part22560
  Check088.part22576))
  (FiniteChecks.interval_append test 22592 22624 22656
  (FiniteChecks.interval_append test 22592 22608 22624
  Check088.part22592
  Check088.part22608)
  (FiniteChecks.interval_append test 22624 22640 22656
  Check088.part22624
  Check088.part22640)))
  (FiniteChecks.interval_append test 22656 22720 22784
  (FiniteChecks.interval_append test 22656 22688 22720
  (FiniteChecks.interval_append test 22656 22672 22688
  Check088.part22656
  Check088.part22672)
  (FiniteChecks.interval_append test 22688 22704 22720
  Check088.part22688
  Check088.part22704))
  (FiniteChecks.interval_append test 22720 22752 22784
  (FiniteChecks.interval_append test 22720 22736 22752
  Check088.part22720
  Check088.part22736)
  (FiniteChecks.interval_append test 22752 22768 22784
  Check088.part22752
  Check088.part22768))))
#print axioms Check088.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check089.part22784 : Interval test 22784 22800 :=
  interval_of_check _ 22784 16 (by decide +kernel)
theorem Check089.part22800 : Interval test 22800 22816 :=
  interval_of_check _ 22800 16 (by decide +kernel)
theorem Check089.part22816 : Interval test 22816 22832 :=
  interval_of_check _ 22816 16 (by decide +kernel)
theorem Check089.part22832 : Interval test 22832 22848 :=
  interval_of_check _ 22832 16 (by decide +kernel)
theorem Check089.part22848 : Interval test 22848 22864 :=
  interval_of_check _ 22848 16 (by decide +kernel)
theorem Check089.part22864 : Interval test 22864 22880 :=
  interval_of_check _ 22864 16 (by decide +kernel)
theorem Check089.part22880 : Interval test 22880 22896 :=
  interval_of_check _ 22880 16 (by decide +kernel)
theorem Check089.part22896 : Interval test 22896 22912 :=
  interval_of_check _ 22896 16 (by decide +kernel)
theorem Check089.part22912 : Interval test 22912 22928 :=
  interval_of_check _ 22912 16 (by decide +kernel)
theorem Check089.part22928 : Interval test 22928 22944 :=
  interval_of_check _ 22928 16 (by decide +kernel)
theorem Check089.part22944 : Interval test 22944 22960 :=
  interval_of_check _ 22944 16 (by decide +kernel)
theorem Check089.part22960 : Interval test 22960 22976 :=
  interval_of_check _ 22960 16 (by decide +kernel)
theorem Check089.part22976 : Interval test 22976 22992 :=
  interval_of_check _ 22976 16 (by decide +kernel)
theorem Check089.part22992 : Interval test 22992 23008 :=
  interval_of_check _ 22992 16 (by decide +kernel)
theorem Check089.part23008 : Interval test 23008 23024 :=
  interval_of_check _ 23008 16 (by decide +kernel)
theorem Check089.part23024 : Interval test 23024 23040 :=
  interval_of_check _ 23024 16 (by decide +kernel)
theorem Check089.checked : Interval test 22784 23040 :=
  (FiniteChecks.interval_append test 22784 22912 23040
  (FiniteChecks.interval_append test 22784 22848 22912
  (FiniteChecks.interval_append test 22784 22816 22848
  (FiniteChecks.interval_append test 22784 22800 22816
  Check089.part22784
  Check089.part22800)
  (FiniteChecks.interval_append test 22816 22832 22848
  Check089.part22816
  Check089.part22832))
  (FiniteChecks.interval_append test 22848 22880 22912
  (FiniteChecks.interval_append test 22848 22864 22880
  Check089.part22848
  Check089.part22864)
  (FiniteChecks.interval_append test 22880 22896 22912
  Check089.part22880
  Check089.part22896)))
  (FiniteChecks.interval_append test 22912 22976 23040
  (FiniteChecks.interval_append test 22912 22944 22976
  (FiniteChecks.interval_append test 22912 22928 22944
  Check089.part22912
  Check089.part22928)
  (FiniteChecks.interval_append test 22944 22960 22976
  Check089.part22944
  Check089.part22960))
  (FiniteChecks.interval_append test 22976 23008 23040
  (FiniteChecks.interval_append test 22976 22992 23008
  Check089.part22976
  Check089.part22992)
  (FiniteChecks.interval_append test 23008 23024 23040
  Check089.part23008
  Check089.part23024))))
#print axioms Check089.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check090.part23040 : Interval test 23040 23056 :=
  interval_of_check _ 23040 16 (by decide +kernel)
theorem Check090.part23056 : Interval test 23056 23072 :=
  interval_of_check _ 23056 16 (by decide +kernel)
theorem Check090.part23072 : Interval test 23072 23088 :=
  interval_of_check _ 23072 16 (by decide +kernel)
theorem Check090.part23088 : Interval test 23088 23104 :=
  interval_of_check _ 23088 16 (by decide +kernel)
theorem Check090.part23104 : Interval test 23104 23120 :=
  interval_of_check _ 23104 16 (by decide +kernel)
theorem Check090.part23120 : Interval test 23120 23136 :=
  interval_of_check _ 23120 16 (by decide +kernel)
theorem Check090.part23136 : Interval test 23136 23152 :=
  interval_of_check _ 23136 16 (by decide +kernel)
theorem Check090.part23152 : Interval test 23152 23168 :=
  interval_of_check _ 23152 16 (by decide +kernel)
theorem Check090.part23168 : Interval test 23168 23184 :=
  interval_of_check _ 23168 16 (by decide +kernel)
theorem Check090.part23184 : Interval test 23184 23200 :=
  interval_of_check _ 23184 16 (by decide +kernel)
theorem Check090.part23200 : Interval test 23200 23216 :=
  interval_of_check _ 23200 16 (by decide +kernel)
theorem Check090.part23216 : Interval test 23216 23232 :=
  interval_of_check _ 23216 16 (by decide +kernel)
theorem Check090.part23232 : Interval test 23232 23248 :=
  interval_of_check _ 23232 16 (by decide +kernel)
theorem Check090.part23248 : Interval test 23248 23264 :=
  interval_of_check _ 23248 16 (by decide +kernel)
theorem Check090.part23264 : Interval test 23264 23280 :=
  interval_of_check _ 23264 16 (by decide +kernel)
theorem Check090.part23280 : Interval test 23280 23296 :=
  interval_of_check _ 23280 16 (by decide +kernel)
theorem Check090.checked : Interval test 23040 23296 :=
  (FiniteChecks.interval_append test 23040 23168 23296
  (FiniteChecks.interval_append test 23040 23104 23168
  (FiniteChecks.interval_append test 23040 23072 23104
  (FiniteChecks.interval_append test 23040 23056 23072
  Check090.part23040
  Check090.part23056)
  (FiniteChecks.interval_append test 23072 23088 23104
  Check090.part23072
  Check090.part23088))
  (FiniteChecks.interval_append test 23104 23136 23168
  (FiniteChecks.interval_append test 23104 23120 23136
  Check090.part23104
  Check090.part23120)
  (FiniteChecks.interval_append test 23136 23152 23168
  Check090.part23136
  Check090.part23152)))
  (FiniteChecks.interval_append test 23168 23232 23296
  (FiniteChecks.interval_append test 23168 23200 23232
  (FiniteChecks.interval_append test 23168 23184 23200
  Check090.part23168
  Check090.part23184)
  (FiniteChecks.interval_append test 23200 23216 23232
  Check090.part23200
  Check090.part23216))
  (FiniteChecks.interval_append test 23232 23264 23296
  (FiniteChecks.interval_append test 23232 23248 23264
  Check090.part23232
  Check090.part23248)
  (FiniteChecks.interval_append test 23264 23280 23296
  Check090.part23264
  Check090.part23280))))
#print axioms Check090.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check091.part23296 : Interval test 23296 23312 :=
  interval_of_check _ 23296 16 (by decide +kernel)
theorem Check091.part23312 : Interval test 23312 23328 :=
  interval_of_check _ 23312 16 (by decide +kernel)
theorem Check091.part23328 : Interval test 23328 23344 :=
  interval_of_check _ 23328 16 (by decide +kernel)
theorem Check091.part23344 : Interval test 23344 23360 :=
  interval_of_check _ 23344 16 (by decide +kernel)
theorem Check091.part23360 : Interval test 23360 23376 :=
  interval_of_check _ 23360 16 (by decide +kernel)
theorem Check091.part23376 : Interval test 23376 23392 :=
  interval_of_check _ 23376 16 (by decide +kernel)
theorem Check091.part23392 : Interval test 23392 23408 :=
  interval_of_check _ 23392 16 (by decide +kernel)
theorem Check091.part23408 : Interval test 23408 23424 :=
  interval_of_check _ 23408 16 (by decide +kernel)
theorem Check091.part23424 : Interval test 23424 23440 :=
  interval_of_check _ 23424 16 (by decide +kernel)
theorem Check091.part23440 : Interval test 23440 23456 :=
  interval_of_check _ 23440 16 (by decide +kernel)
theorem Check091.part23456 : Interval test 23456 23472 :=
  interval_of_check _ 23456 16 (by decide +kernel)
theorem Check091.part23472 : Interval test 23472 23488 :=
  interval_of_check _ 23472 16 (by decide +kernel)
theorem Check091.part23488 : Interval test 23488 23504 :=
  interval_of_check _ 23488 16 (by decide +kernel)
theorem Check091.part23504 : Interval test 23504 23520 :=
  interval_of_check _ 23504 16 (by decide +kernel)
theorem Check091.part23520 : Interval test 23520 23536 :=
  interval_of_check _ 23520 16 (by decide +kernel)
theorem Check091.part23536 : Interval test 23536 23552 :=
  interval_of_check _ 23536 16 (by decide +kernel)
theorem Check091.checked : Interval test 23296 23552 :=
  (FiniteChecks.interval_append test 23296 23424 23552
  (FiniteChecks.interval_append test 23296 23360 23424
  (FiniteChecks.interval_append test 23296 23328 23360
  (FiniteChecks.interval_append test 23296 23312 23328
  Check091.part23296
  Check091.part23312)
  (FiniteChecks.interval_append test 23328 23344 23360
  Check091.part23328
  Check091.part23344))
  (FiniteChecks.interval_append test 23360 23392 23424
  (FiniteChecks.interval_append test 23360 23376 23392
  Check091.part23360
  Check091.part23376)
  (FiniteChecks.interval_append test 23392 23408 23424
  Check091.part23392
  Check091.part23408)))
  (FiniteChecks.interval_append test 23424 23488 23552
  (FiniteChecks.interval_append test 23424 23456 23488
  (FiniteChecks.interval_append test 23424 23440 23456
  Check091.part23424
  Check091.part23440)
  (FiniteChecks.interval_append test 23456 23472 23488
  Check091.part23456
  Check091.part23472))
  (FiniteChecks.interval_append test 23488 23520 23552
  (FiniteChecks.interval_append test 23488 23504 23520
  Check091.part23488
  Check091.part23504)
  (FiniteChecks.interval_append test 23520 23536 23552
  Check091.part23520
  Check091.part23536))))
#print axioms Check091.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check092.part23552 : Interval test 23552 23568 :=
  interval_of_check _ 23552 16 (by decide +kernel)
theorem Check092.part23568 : Interval test 23568 23584 :=
  interval_of_check _ 23568 16 (by decide +kernel)
theorem Check092.part23584 : Interval test 23584 23600 :=
  interval_of_check _ 23584 16 (by decide +kernel)
theorem Check092.part23600 : Interval test 23600 23616 :=
  interval_of_check _ 23600 16 (by decide +kernel)
theorem Check092.part23616 : Interval test 23616 23632 :=
  interval_of_check _ 23616 16 (by decide +kernel)
theorem Check092.part23632 : Interval test 23632 23648 :=
  interval_of_check _ 23632 16 (by decide +kernel)
theorem Check092.part23648 : Interval test 23648 23664 :=
  interval_of_check _ 23648 16 (by decide +kernel)
theorem Check092.part23664 : Interval test 23664 23680 :=
  interval_of_check _ 23664 16 (by decide +kernel)
theorem Check092.part23680 : Interval test 23680 23696 :=
  interval_of_check _ 23680 16 (by decide +kernel)
theorem Check092.part23696 : Interval test 23696 23712 :=
  interval_of_check _ 23696 16 (by decide +kernel)
theorem Check092.part23712 : Interval test 23712 23728 :=
  interval_of_check _ 23712 16 (by decide +kernel)
theorem Check092.part23728 : Interval test 23728 23744 :=
  interval_of_check _ 23728 16 (by decide +kernel)
theorem Check092.part23744 : Interval test 23744 23760 :=
  interval_of_check _ 23744 16 (by decide +kernel)
theorem Check092.part23760 : Interval test 23760 23776 :=
  interval_of_check _ 23760 16 (by decide +kernel)
theorem Check092.part23776 : Interval test 23776 23792 :=
  interval_of_check _ 23776 16 (by decide +kernel)
theorem Check092.part23792 : Interval test 23792 23808 :=
  interval_of_check _ 23792 16 (by decide +kernel)
theorem Check092.checked : Interval test 23552 23808 :=
  (FiniteChecks.interval_append test 23552 23680 23808
  (FiniteChecks.interval_append test 23552 23616 23680
  (FiniteChecks.interval_append test 23552 23584 23616
  (FiniteChecks.interval_append test 23552 23568 23584
  Check092.part23552
  Check092.part23568)
  (FiniteChecks.interval_append test 23584 23600 23616
  Check092.part23584
  Check092.part23600))
  (FiniteChecks.interval_append test 23616 23648 23680
  (FiniteChecks.interval_append test 23616 23632 23648
  Check092.part23616
  Check092.part23632)
  (FiniteChecks.interval_append test 23648 23664 23680
  Check092.part23648
  Check092.part23664)))
  (FiniteChecks.interval_append test 23680 23744 23808
  (FiniteChecks.interval_append test 23680 23712 23744
  (FiniteChecks.interval_append test 23680 23696 23712
  Check092.part23680
  Check092.part23696)
  (FiniteChecks.interval_append test 23712 23728 23744
  Check092.part23712
  Check092.part23728))
  (FiniteChecks.interval_append test 23744 23776 23808
  (FiniteChecks.interval_append test 23744 23760 23776
  Check092.part23744
  Check092.part23760)
  (FiniteChecks.interval_append test 23776 23792 23808
  Check092.part23776
  Check092.part23792))))
#print axioms Check092.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check093.part23808 : Interval test 23808 23824 :=
  interval_of_check _ 23808 16 (by decide +kernel)
theorem Check093.part23824 : Interval test 23824 23840 :=
  interval_of_check _ 23824 16 (by decide +kernel)
theorem Check093.part23840 : Interval test 23840 23856 :=
  interval_of_check _ 23840 16 (by decide +kernel)
theorem Check093.part23856 : Interval test 23856 23872 :=
  interval_of_check _ 23856 16 (by decide +kernel)
theorem Check093.part23872 : Interval test 23872 23888 :=
  interval_of_check _ 23872 16 (by decide +kernel)
theorem Check093.part23888 : Interval test 23888 23904 :=
  interval_of_check _ 23888 16 (by decide +kernel)
theorem Check093.part23904 : Interval test 23904 23920 :=
  interval_of_check _ 23904 16 (by decide +kernel)
theorem Check093.part23920 : Interval test 23920 23936 :=
  interval_of_check _ 23920 16 (by decide +kernel)
theorem Check093.part23936 : Interval test 23936 23952 :=
  interval_of_check _ 23936 16 (by decide +kernel)
theorem Check093.part23952 : Interval test 23952 23968 :=
  interval_of_check _ 23952 16 (by decide +kernel)
theorem Check093.part23968 : Interval test 23968 23984 :=
  interval_of_check _ 23968 16 (by decide +kernel)
theorem Check093.part23984 : Interval test 23984 24000 :=
  interval_of_check _ 23984 16 (by decide +kernel)
theorem Check093.part24000 : Interval test 24000 24016 :=
  interval_of_check _ 24000 16 (by decide +kernel)
theorem Check093.part24016 : Interval test 24016 24032 :=
  interval_of_check _ 24016 16 (by decide +kernel)
theorem Check093.part24032 : Interval test 24032 24048 :=
  interval_of_check _ 24032 16 (by decide +kernel)
theorem Check093.part24048 : Interval test 24048 24064 :=
  interval_of_check _ 24048 16 (by decide +kernel)
theorem Check093.checked : Interval test 23808 24064 :=
  (FiniteChecks.interval_append test 23808 23936 24064
  (FiniteChecks.interval_append test 23808 23872 23936
  (FiniteChecks.interval_append test 23808 23840 23872
  (FiniteChecks.interval_append test 23808 23824 23840
  Check093.part23808
  Check093.part23824)
  (FiniteChecks.interval_append test 23840 23856 23872
  Check093.part23840
  Check093.part23856))
  (FiniteChecks.interval_append test 23872 23904 23936
  (FiniteChecks.interval_append test 23872 23888 23904
  Check093.part23872
  Check093.part23888)
  (FiniteChecks.interval_append test 23904 23920 23936
  Check093.part23904
  Check093.part23920)))
  (FiniteChecks.interval_append test 23936 24000 24064
  (FiniteChecks.interval_append test 23936 23968 24000
  (FiniteChecks.interval_append test 23936 23952 23968
  Check093.part23936
  Check093.part23952)
  (FiniteChecks.interval_append test 23968 23984 24000
  Check093.part23968
  Check093.part23984))
  (FiniteChecks.interval_append test 24000 24032 24064
  (FiniteChecks.interval_append test 24000 24016 24032
  Check093.part24000
  Check093.part24016)
  (FiniteChecks.interval_append test 24032 24048 24064
  Check093.part24032
  Check093.part24048))))
#print axioms Check093.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check094.part24064 : Interval test 24064 24080 :=
  interval_of_check _ 24064 16 (by decide +kernel)
theorem Check094.part24080 : Interval test 24080 24096 :=
  interval_of_check _ 24080 16 (by decide +kernel)
theorem Check094.part24096 : Interval test 24096 24112 :=
  interval_of_check _ 24096 16 (by decide +kernel)
theorem Check094.part24112 : Interval test 24112 24128 :=
  interval_of_check _ 24112 16 (by decide +kernel)
theorem Check094.part24128 : Interval test 24128 24144 :=
  interval_of_check _ 24128 16 (by decide +kernel)
theorem Check094.part24144 : Interval test 24144 24160 :=
  interval_of_check _ 24144 16 (by decide +kernel)
theorem Check094.part24160 : Interval test 24160 24176 :=
  interval_of_check _ 24160 16 (by decide +kernel)
theorem Check094.part24176 : Interval test 24176 24192 :=
  interval_of_check _ 24176 16 (by decide +kernel)
theorem Check094.part24192 : Interval test 24192 24208 :=
  interval_of_check _ 24192 16 (by decide +kernel)
theorem Check094.part24208 : Interval test 24208 24224 :=
  interval_of_check _ 24208 16 (by decide +kernel)
theorem Check094.part24224 : Interval test 24224 24240 :=
  interval_of_check _ 24224 16 (by decide +kernel)
theorem Check094.part24240 : Interval test 24240 24256 :=
  interval_of_check _ 24240 16 (by decide +kernel)
theorem Check094.part24256 : Interval test 24256 24272 :=
  interval_of_check _ 24256 16 (by decide +kernel)
theorem Check094.part24272 : Interval test 24272 24288 :=
  interval_of_check _ 24272 16 (by decide +kernel)
theorem Check094.part24288 : Interval test 24288 24304 :=
  interval_of_check _ 24288 16 (by decide +kernel)
theorem Check094.part24304 : Interval test 24304 24320 :=
  interval_of_check _ 24304 16 (by decide +kernel)
theorem Check094.checked : Interval test 24064 24320 :=
  (FiniteChecks.interval_append test 24064 24192 24320
  (FiniteChecks.interval_append test 24064 24128 24192
  (FiniteChecks.interval_append test 24064 24096 24128
  (FiniteChecks.interval_append test 24064 24080 24096
  Check094.part24064
  Check094.part24080)
  (FiniteChecks.interval_append test 24096 24112 24128
  Check094.part24096
  Check094.part24112))
  (FiniteChecks.interval_append test 24128 24160 24192
  (FiniteChecks.interval_append test 24128 24144 24160
  Check094.part24128
  Check094.part24144)
  (FiniteChecks.interval_append test 24160 24176 24192
  Check094.part24160
  Check094.part24176)))
  (FiniteChecks.interval_append test 24192 24256 24320
  (FiniteChecks.interval_append test 24192 24224 24256
  (FiniteChecks.interval_append test 24192 24208 24224
  Check094.part24192
  Check094.part24208)
  (FiniteChecks.interval_append test 24224 24240 24256
  Check094.part24224
  Check094.part24240))
  (FiniteChecks.interval_append test 24256 24288 24320
  (FiniteChecks.interval_append test 24256 24272 24288
  Check094.part24256
  Check094.part24272)
  (FiniteChecks.interval_append test 24288 24304 24320
  Check094.part24288
  Check094.part24304))))
#print axioms Check094.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check095.part24320 : Interval test 24320 24336 :=
  interval_of_check _ 24320 16 (by decide +kernel)
theorem Check095.part24336 : Interval test 24336 24352 :=
  interval_of_check _ 24336 16 (by decide +kernel)
theorem Check095.part24352 : Interval test 24352 24368 :=
  interval_of_check _ 24352 16 (by decide +kernel)
theorem Check095.part24368 : Interval test 24368 24384 :=
  interval_of_check _ 24368 16 (by decide +kernel)
theorem Check095.part24384 : Interval test 24384 24400 :=
  interval_of_check _ 24384 16 (by decide +kernel)
theorem Check095.part24400 : Interval test 24400 24416 :=
  interval_of_check _ 24400 16 (by decide +kernel)
theorem Check095.part24416 : Interval test 24416 24432 :=
  interval_of_check _ 24416 16 (by decide +kernel)
theorem Check095.part24432 : Interval test 24432 24448 :=
  interval_of_check _ 24432 16 (by decide +kernel)
theorem Check095.part24448 : Interval test 24448 24464 :=
  interval_of_check _ 24448 16 (by decide +kernel)
theorem Check095.part24464 : Interval test 24464 24480 :=
  interval_of_check _ 24464 16 (by decide +kernel)
theorem Check095.part24480 : Interval test 24480 24496 :=
  interval_of_check _ 24480 16 (by decide +kernel)
theorem Check095.part24496 : Interval test 24496 24512 :=
  interval_of_check _ 24496 16 (by decide +kernel)
theorem Check095.part24512 : Interval test 24512 24528 :=
  interval_of_check _ 24512 16 (by decide +kernel)
theorem Check095.part24528 : Interval test 24528 24544 :=
  interval_of_check _ 24528 16 (by decide +kernel)
theorem Check095.part24544 : Interval test 24544 24560 :=
  interval_of_check _ 24544 16 (by decide +kernel)
theorem Check095.part24560 : Interval test 24560 24576 :=
  interval_of_check _ 24560 16 (by decide +kernel)
theorem Check095.checked : Interval test 24320 24576 :=
  (FiniteChecks.interval_append test 24320 24448 24576
  (FiniteChecks.interval_append test 24320 24384 24448
  (FiniteChecks.interval_append test 24320 24352 24384
  (FiniteChecks.interval_append test 24320 24336 24352
  Check095.part24320
  Check095.part24336)
  (FiniteChecks.interval_append test 24352 24368 24384
  Check095.part24352
  Check095.part24368))
  (FiniteChecks.interval_append test 24384 24416 24448
  (FiniteChecks.interval_append test 24384 24400 24416
  Check095.part24384
  Check095.part24400)
  (FiniteChecks.interval_append test 24416 24432 24448
  Check095.part24416
  Check095.part24432)))
  (FiniteChecks.interval_append test 24448 24512 24576
  (FiniteChecks.interval_append test 24448 24480 24512
  (FiniteChecks.interval_append test 24448 24464 24480
  Check095.part24448
  Check095.part24464)
  (FiniteChecks.interval_append test 24480 24496 24512
  Check095.part24480
  Check095.part24496))
  (FiniteChecks.interval_append test 24512 24544 24576
  (FiniteChecks.interval_append test 24512 24528 24544
  Check095.part24512
  Check095.part24528)
  (FiniteChecks.interval_append test 24544 24560 24576
  Check095.part24544
  Check095.part24560))))
#print axioms Check095.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check096.part24576 : Interval test 24576 24592 :=
  interval_of_check _ 24576 16 (by decide +kernel)
theorem Check096.part24592 : Interval test 24592 24608 :=
  interval_of_check _ 24592 16 (by decide +kernel)
theorem Check096.part24608 : Interval test 24608 24624 :=
  interval_of_check _ 24608 16 (by decide +kernel)
theorem Check096.part24624 : Interval test 24624 24640 :=
  interval_of_check _ 24624 16 (by decide +kernel)
theorem Check096.part24640 : Interval test 24640 24656 :=
  interval_of_check _ 24640 16 (by decide +kernel)
theorem Check096.part24656 : Interval test 24656 24672 :=
  interval_of_check _ 24656 16 (by decide +kernel)
theorem Check096.part24672 : Interval test 24672 24688 :=
  interval_of_check _ 24672 16 (by decide +kernel)
theorem Check096.part24688 : Interval test 24688 24704 :=
  interval_of_check _ 24688 16 (by decide +kernel)
theorem Check096.part24704 : Interval test 24704 24720 :=
  interval_of_check _ 24704 16 (by decide +kernel)
theorem Check096.part24720 : Interval test 24720 24736 :=
  interval_of_check _ 24720 16 (by decide +kernel)
theorem Check096.part24736 : Interval test 24736 24752 :=
  interval_of_check _ 24736 16 (by decide +kernel)
theorem Check096.part24752 : Interval test 24752 24768 :=
  interval_of_check _ 24752 16 (by decide +kernel)
theorem Check096.part24768 : Interval test 24768 24784 :=
  interval_of_check _ 24768 16 (by decide +kernel)
theorem Check096.part24784 : Interval test 24784 24800 :=
  interval_of_check _ 24784 16 (by decide +kernel)
theorem Check096.part24800 : Interval test 24800 24816 :=
  interval_of_check _ 24800 16 (by decide +kernel)
theorem Check096.part24816 : Interval test 24816 24832 :=
  interval_of_check _ 24816 16 (by decide +kernel)
theorem Check096.checked : Interval test 24576 24832 :=
  (FiniteChecks.interval_append test 24576 24704 24832
  (FiniteChecks.interval_append test 24576 24640 24704
  (FiniteChecks.interval_append test 24576 24608 24640
  (FiniteChecks.interval_append test 24576 24592 24608
  Check096.part24576
  Check096.part24592)
  (FiniteChecks.interval_append test 24608 24624 24640
  Check096.part24608
  Check096.part24624))
  (FiniteChecks.interval_append test 24640 24672 24704
  (FiniteChecks.interval_append test 24640 24656 24672
  Check096.part24640
  Check096.part24656)
  (FiniteChecks.interval_append test 24672 24688 24704
  Check096.part24672
  Check096.part24688)))
  (FiniteChecks.interval_append test 24704 24768 24832
  (FiniteChecks.interval_append test 24704 24736 24768
  (FiniteChecks.interval_append test 24704 24720 24736
  Check096.part24704
  Check096.part24720)
  (FiniteChecks.interval_append test 24736 24752 24768
  Check096.part24736
  Check096.part24752))
  (FiniteChecks.interval_append test 24768 24800 24832
  (FiniteChecks.interval_append test 24768 24784 24800
  Check096.part24768
  Check096.part24784)
  (FiniteChecks.interval_append test 24800 24816 24832
  Check096.part24800
  Check096.part24816))))
#print axioms Check096.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check097.part24832 : Interval test 24832 24848 :=
  interval_of_check _ 24832 16 (by decide +kernel)
theorem Check097.part24848 : Interval test 24848 24864 :=
  interval_of_check _ 24848 16 (by decide +kernel)
theorem Check097.part24864 : Interval test 24864 24880 :=
  interval_of_check _ 24864 16 (by decide +kernel)
theorem Check097.part24880 : Interval test 24880 24896 :=
  interval_of_check _ 24880 16 (by decide +kernel)
theorem Check097.part24896 : Interval test 24896 24912 :=
  interval_of_check _ 24896 16 (by decide +kernel)
theorem Check097.part24912 : Interval test 24912 24928 :=
  interval_of_check _ 24912 16 (by decide +kernel)
theorem Check097.part24928 : Interval test 24928 24944 :=
  interval_of_check _ 24928 16 (by decide +kernel)
theorem Check097.part24944 : Interval test 24944 24960 :=
  interval_of_check _ 24944 16 (by decide +kernel)
theorem Check097.part24960 : Interval test 24960 24976 :=
  interval_of_check _ 24960 16 (by decide +kernel)
theorem Check097.part24976 : Interval test 24976 24992 :=
  interval_of_check _ 24976 16 (by decide +kernel)
theorem Check097.part24992 : Interval test 24992 25008 :=
  interval_of_check _ 24992 16 (by decide +kernel)
theorem Check097.part25008 : Interval test 25008 25024 :=
  interval_of_check _ 25008 16 (by decide +kernel)
theorem Check097.part25024 : Interval test 25024 25040 :=
  interval_of_check _ 25024 16 (by decide +kernel)
theorem Check097.part25040 : Interval test 25040 25056 :=
  interval_of_check _ 25040 16 (by decide +kernel)
theorem Check097.part25056 : Interval test 25056 25072 :=
  interval_of_check _ 25056 16 (by decide +kernel)
theorem Check097.part25072 : Interval test 25072 25088 :=
  interval_of_check _ 25072 16 (by decide +kernel)
theorem Check097.checked : Interval test 24832 25088 :=
  (FiniteChecks.interval_append test 24832 24960 25088
  (FiniteChecks.interval_append test 24832 24896 24960
  (FiniteChecks.interval_append test 24832 24864 24896
  (FiniteChecks.interval_append test 24832 24848 24864
  Check097.part24832
  Check097.part24848)
  (FiniteChecks.interval_append test 24864 24880 24896
  Check097.part24864
  Check097.part24880))
  (FiniteChecks.interval_append test 24896 24928 24960
  (FiniteChecks.interval_append test 24896 24912 24928
  Check097.part24896
  Check097.part24912)
  (FiniteChecks.interval_append test 24928 24944 24960
  Check097.part24928
  Check097.part24944)))
  (FiniteChecks.interval_append test 24960 25024 25088
  (FiniteChecks.interval_append test 24960 24992 25024
  (FiniteChecks.interval_append test 24960 24976 24992
  Check097.part24960
  Check097.part24976)
  (FiniteChecks.interval_append test 24992 25008 25024
  Check097.part24992
  Check097.part25008))
  (FiniteChecks.interval_append test 25024 25056 25088
  (FiniteChecks.interval_append test 25024 25040 25056
  Check097.part25024
  Check097.part25040)
  (FiniteChecks.interval_append test 25056 25072 25088
  Check097.part25056
  Check097.part25072))))
#print axioms Check097.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check098.part25088 : Interval test 25088 25104 :=
  interval_of_check _ 25088 16 (by decide +kernel)
theorem Check098.part25104 : Interval test 25104 25120 :=
  interval_of_check _ 25104 16 (by decide +kernel)
theorem Check098.part25120 : Interval test 25120 25136 :=
  interval_of_check _ 25120 16 (by decide +kernel)
theorem Check098.part25136 : Interval test 25136 25152 :=
  interval_of_check _ 25136 16 (by decide +kernel)
theorem Check098.part25152 : Interval test 25152 25168 :=
  interval_of_check _ 25152 16 (by decide +kernel)
theorem Check098.part25168 : Interval test 25168 25184 :=
  interval_of_check _ 25168 16 (by decide +kernel)
theorem Check098.part25184 : Interval test 25184 25200 :=
  interval_of_check _ 25184 16 (by decide +kernel)
theorem Check098.part25200 : Interval test 25200 25216 :=
  interval_of_check _ 25200 16 (by decide +kernel)
theorem Check098.part25216 : Interval test 25216 25232 :=
  interval_of_check _ 25216 16 (by decide +kernel)
theorem Check098.part25232 : Interval test 25232 25248 :=
  interval_of_check _ 25232 16 (by decide +kernel)
theorem Check098.part25248 : Interval test 25248 25264 :=
  interval_of_check _ 25248 16 (by decide +kernel)
theorem Check098.part25264 : Interval test 25264 25280 :=
  interval_of_check _ 25264 16 (by decide +kernel)
theorem Check098.part25280 : Interval test 25280 25296 :=
  interval_of_check _ 25280 16 (by decide +kernel)
theorem Check098.part25296 : Interval test 25296 25312 :=
  interval_of_check _ 25296 16 (by decide +kernel)
theorem Check098.part25312 : Interval test 25312 25328 :=
  interval_of_check _ 25312 16 (by decide +kernel)
theorem Check098.part25328 : Interval test 25328 25344 :=
  interval_of_check _ 25328 16 (by decide +kernel)
theorem Check098.checked : Interval test 25088 25344 :=
  (FiniteChecks.interval_append test 25088 25216 25344
  (FiniteChecks.interval_append test 25088 25152 25216
  (FiniteChecks.interval_append test 25088 25120 25152
  (FiniteChecks.interval_append test 25088 25104 25120
  Check098.part25088
  Check098.part25104)
  (FiniteChecks.interval_append test 25120 25136 25152
  Check098.part25120
  Check098.part25136))
  (FiniteChecks.interval_append test 25152 25184 25216
  (FiniteChecks.interval_append test 25152 25168 25184
  Check098.part25152
  Check098.part25168)
  (FiniteChecks.interval_append test 25184 25200 25216
  Check098.part25184
  Check098.part25200)))
  (FiniteChecks.interval_append test 25216 25280 25344
  (FiniteChecks.interval_append test 25216 25248 25280
  (FiniteChecks.interval_append test 25216 25232 25248
  Check098.part25216
  Check098.part25232)
  (FiniteChecks.interval_append test 25248 25264 25280
  Check098.part25248
  Check098.part25264))
  (FiniteChecks.interval_append test 25280 25312 25344
  (FiniteChecks.interval_append test 25280 25296 25312
  Check098.part25280
  Check098.part25296)
  (FiniteChecks.interval_append test 25312 25328 25344
  Check098.part25312
  Check098.part25328))))
#print axioms Check098.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check099.part25344 : Interval test 25344 25360 :=
  interval_of_check _ 25344 16 (by decide +kernel)
theorem Check099.part25360 : Interval test 25360 25376 :=
  interval_of_check _ 25360 16 (by decide +kernel)
theorem Check099.part25376 : Interval test 25376 25392 :=
  interval_of_check _ 25376 16 (by decide +kernel)
theorem Check099.part25392 : Interval test 25392 25408 :=
  interval_of_check _ 25392 16 (by decide +kernel)
theorem Check099.part25408 : Interval test 25408 25424 :=
  interval_of_check _ 25408 16 (by decide +kernel)
theorem Check099.part25424 : Interval test 25424 25440 :=
  interval_of_check _ 25424 16 (by decide +kernel)
theorem Check099.part25440 : Interval test 25440 25456 :=
  interval_of_check _ 25440 16 (by decide +kernel)
theorem Check099.part25456 : Interval test 25456 25472 :=
  interval_of_check _ 25456 16 (by decide +kernel)
theorem Check099.part25472 : Interval test 25472 25488 :=
  interval_of_check _ 25472 16 (by decide +kernel)
theorem Check099.part25488 : Interval test 25488 25504 :=
  interval_of_check _ 25488 16 (by decide +kernel)
theorem Check099.part25504 : Interval test 25504 25520 :=
  interval_of_check _ 25504 16 (by decide +kernel)
theorem Check099.part25520 : Interval test 25520 25536 :=
  interval_of_check _ 25520 16 (by decide +kernel)
theorem Check099.part25536 : Interval test 25536 25552 :=
  interval_of_check _ 25536 16 (by decide +kernel)
theorem Check099.part25552 : Interval test 25552 25568 :=
  interval_of_check _ 25552 16 (by decide +kernel)
theorem Check099.part25568 : Interval test 25568 25584 :=
  interval_of_check _ 25568 16 (by decide +kernel)
theorem Check099.part25584 : Interval test 25584 25600 :=
  interval_of_check _ 25584 16 (by decide +kernel)
theorem Check099.checked : Interval test 25344 25600 :=
  (FiniteChecks.interval_append test 25344 25472 25600
  (FiniteChecks.interval_append test 25344 25408 25472
  (FiniteChecks.interval_append test 25344 25376 25408
  (FiniteChecks.interval_append test 25344 25360 25376
  Check099.part25344
  Check099.part25360)
  (FiniteChecks.interval_append test 25376 25392 25408
  Check099.part25376
  Check099.part25392))
  (FiniteChecks.interval_append test 25408 25440 25472
  (FiniteChecks.interval_append test 25408 25424 25440
  Check099.part25408
  Check099.part25424)
  (FiniteChecks.interval_append test 25440 25456 25472
  Check099.part25440
  Check099.part25456)))
  (FiniteChecks.interval_append test 25472 25536 25600
  (FiniteChecks.interval_append test 25472 25504 25536
  (FiniteChecks.interval_append test 25472 25488 25504
  Check099.part25472
  Check099.part25488)
  (FiniteChecks.interval_append test 25504 25520 25536
  Check099.part25504
  Check099.part25520))
  (FiniteChecks.interval_append test 25536 25568 25600
  (FiniteChecks.interval_append test 25536 25552 25568
  Check099.part25536
  Check099.part25552)
  (FiniteChecks.interval_append test 25568 25584 25600
  Check099.part25568
  Check099.part25584))))
#print axioms Check099.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
