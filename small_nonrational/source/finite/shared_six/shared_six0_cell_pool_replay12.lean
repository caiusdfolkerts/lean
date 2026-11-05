module
prelude
public import SharedSix0CellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check240.part30720 : Interval test 30720 30736 :=
  interval_of_check _ 30720 16 (by decide +kernel)
theorem Check240.part30736 : Interval test 30736 30752 :=
  interval_of_check _ 30736 16 (by decide +kernel)
theorem Check240.part30752 : Interval test 30752 30768 :=
  interval_of_check _ 30752 16 (by decide +kernel)
theorem Check240.part30768 : Interval test 30768 30784 :=
  interval_of_check _ 30768 16 (by decide +kernel)
theorem Check240.part30784 : Interval test 30784 30800 :=
  interval_of_check _ 30784 16 (by decide +kernel)
theorem Check240.part30800 : Interval test 30800 30816 :=
  interval_of_check _ 30800 16 (by decide +kernel)
theorem Check240.part30816 : Interval test 30816 30832 :=
  interval_of_check _ 30816 16 (by decide +kernel)
theorem Check240.part30832 : Interval test 30832 30848 :=
  interval_of_check _ 30832 16 (by decide +kernel)
theorem Check240.checked : Interval test 30720 30848 :=
  (FiniteChecks.interval_append test 30720 30784 30848
  (FiniteChecks.interval_append test 30720 30752 30784
  (FiniteChecks.interval_append test 30720 30736 30752
  Check240.part30720
  Check240.part30736)
  (FiniteChecks.interval_append test 30752 30768 30784
  Check240.part30752
  Check240.part30768))
  (FiniteChecks.interval_append test 30784 30816 30848
  (FiniteChecks.interval_append test 30784 30800 30816
  Check240.part30784
  Check240.part30800)
  (FiniteChecks.interval_append test 30816 30832 30848
  Check240.part30816
  Check240.part30832)))
#print axioms Check240.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check241.part30848 : Interval test 30848 30864 :=
  interval_of_check _ 30848 16 (by decide +kernel)
theorem Check241.part30864 : Interval test 30864 30880 :=
  interval_of_check _ 30864 16 (by decide +kernel)
theorem Check241.part30880 : Interval test 30880 30896 :=
  interval_of_check _ 30880 16 (by decide +kernel)
theorem Check241.part30896 : Interval test 30896 30912 :=
  interval_of_check _ 30896 16 (by decide +kernel)
theorem Check241.part30912 : Interval test 30912 30928 :=
  interval_of_check _ 30912 16 (by decide +kernel)
theorem Check241.part30928 : Interval test 30928 30944 :=
  interval_of_check _ 30928 16 (by decide +kernel)
theorem Check241.part30944 : Interval test 30944 30960 :=
  interval_of_check _ 30944 16 (by decide +kernel)
theorem Check241.part30960 : Interval test 30960 30976 :=
  interval_of_check _ 30960 16 (by decide +kernel)
theorem Check241.checked : Interval test 30848 30976 :=
  (FiniteChecks.interval_append test 30848 30912 30976
  (FiniteChecks.interval_append test 30848 30880 30912
  (FiniteChecks.interval_append test 30848 30864 30880
  Check241.part30848
  Check241.part30864)
  (FiniteChecks.interval_append test 30880 30896 30912
  Check241.part30880
  Check241.part30896))
  (FiniteChecks.interval_append test 30912 30944 30976
  (FiniteChecks.interval_append test 30912 30928 30944
  Check241.part30912
  Check241.part30928)
  (FiniteChecks.interval_append test 30944 30960 30976
  Check241.part30944
  Check241.part30960)))
#print axioms Check241.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check242.part30976 : Interval test 30976 30992 :=
  interval_of_check _ 30976 16 (by decide +kernel)
theorem Check242.part30992 : Interval test 30992 31008 :=
  interval_of_check _ 30992 16 (by decide +kernel)
theorem Check242.part31008 : Interval test 31008 31024 :=
  interval_of_check _ 31008 16 (by decide +kernel)
theorem Check242.part31024 : Interval test 31024 31040 :=
  interval_of_check _ 31024 16 (by decide +kernel)
theorem Check242.part31040 : Interval test 31040 31056 :=
  interval_of_check _ 31040 16 (by decide +kernel)
theorem Check242.part31056 : Interval test 31056 31072 :=
  interval_of_check _ 31056 16 (by decide +kernel)
theorem Check242.part31072 : Interval test 31072 31088 :=
  interval_of_check _ 31072 16 (by decide +kernel)
theorem Check242.part31088 : Interval test 31088 31104 :=
  interval_of_check _ 31088 16 (by decide +kernel)
theorem Check242.checked : Interval test 30976 31104 :=
  (FiniteChecks.interval_append test 30976 31040 31104
  (FiniteChecks.interval_append test 30976 31008 31040
  (FiniteChecks.interval_append test 30976 30992 31008
  Check242.part30976
  Check242.part30992)
  (FiniteChecks.interval_append test 31008 31024 31040
  Check242.part31008
  Check242.part31024))
  (FiniteChecks.interval_append test 31040 31072 31104
  (FiniteChecks.interval_append test 31040 31056 31072
  Check242.part31040
  Check242.part31056)
  (FiniteChecks.interval_append test 31072 31088 31104
  Check242.part31072
  Check242.part31088)))
#print axioms Check242.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check243.part31104 : Interval test 31104 31120 :=
  interval_of_check _ 31104 16 (by decide +kernel)
theorem Check243.part31120 : Interval test 31120 31136 :=
  interval_of_check _ 31120 16 (by decide +kernel)
theorem Check243.part31136 : Interval test 31136 31152 :=
  interval_of_check _ 31136 16 (by decide +kernel)
theorem Check243.part31152 : Interval test 31152 31168 :=
  interval_of_check _ 31152 16 (by decide +kernel)
theorem Check243.part31168 : Interval test 31168 31184 :=
  interval_of_check _ 31168 16 (by decide +kernel)
theorem Check243.part31184 : Interval test 31184 31200 :=
  interval_of_check _ 31184 16 (by decide +kernel)
theorem Check243.part31200 : Interval test 31200 31216 :=
  interval_of_check _ 31200 16 (by decide +kernel)
theorem Check243.part31216 : Interval test 31216 31232 :=
  interval_of_check _ 31216 16 (by decide +kernel)
theorem Check243.checked : Interval test 31104 31232 :=
  (FiniteChecks.interval_append test 31104 31168 31232
  (FiniteChecks.interval_append test 31104 31136 31168
  (FiniteChecks.interval_append test 31104 31120 31136
  Check243.part31104
  Check243.part31120)
  (FiniteChecks.interval_append test 31136 31152 31168
  Check243.part31136
  Check243.part31152))
  (FiniteChecks.interval_append test 31168 31200 31232
  (FiniteChecks.interval_append test 31168 31184 31200
  Check243.part31168
  Check243.part31184)
  (FiniteChecks.interval_append test 31200 31216 31232
  Check243.part31200
  Check243.part31216)))
#print axioms Check243.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check244.part31232 : Interval test 31232 31248 :=
  interval_of_check _ 31232 16 (by decide +kernel)
theorem Check244.part31248 : Interval test 31248 31264 :=
  interval_of_check _ 31248 16 (by decide +kernel)
theorem Check244.part31264 : Interval test 31264 31280 :=
  interval_of_check _ 31264 16 (by decide +kernel)
theorem Check244.part31280 : Interval test 31280 31296 :=
  interval_of_check _ 31280 16 (by decide +kernel)
theorem Check244.part31296 : Interval test 31296 31312 :=
  interval_of_check _ 31296 16 (by decide +kernel)
theorem Check244.part31312 : Interval test 31312 31328 :=
  interval_of_check _ 31312 16 (by decide +kernel)
theorem Check244.part31328 : Interval test 31328 31344 :=
  interval_of_check _ 31328 16 (by decide +kernel)
theorem Check244.part31344 : Interval test 31344 31360 :=
  interval_of_check _ 31344 16 (by decide +kernel)
theorem Check244.checked : Interval test 31232 31360 :=
  (FiniteChecks.interval_append test 31232 31296 31360
  (FiniteChecks.interval_append test 31232 31264 31296
  (FiniteChecks.interval_append test 31232 31248 31264
  Check244.part31232
  Check244.part31248)
  (FiniteChecks.interval_append test 31264 31280 31296
  Check244.part31264
  Check244.part31280))
  (FiniteChecks.interval_append test 31296 31328 31360
  (FiniteChecks.interval_append test 31296 31312 31328
  Check244.part31296
  Check244.part31312)
  (FiniteChecks.interval_append test 31328 31344 31360
  Check244.part31328
  Check244.part31344)))
#print axioms Check244.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check245.part31360 : Interval test 31360 31376 :=
  interval_of_check _ 31360 16 (by decide +kernel)
theorem Check245.part31376 : Interval test 31376 31392 :=
  interval_of_check _ 31376 16 (by decide +kernel)
theorem Check245.part31392 : Interval test 31392 31408 :=
  interval_of_check _ 31392 16 (by decide +kernel)
theorem Check245.part31408 : Interval test 31408 31424 :=
  interval_of_check _ 31408 16 (by decide +kernel)
theorem Check245.part31424 : Interval test 31424 31440 :=
  interval_of_check _ 31424 16 (by decide +kernel)
theorem Check245.part31440 : Interval test 31440 31456 :=
  interval_of_check _ 31440 16 (by decide +kernel)
theorem Check245.part31456 : Interval test 31456 31472 :=
  interval_of_check _ 31456 16 (by decide +kernel)
theorem Check245.part31472 : Interval test 31472 31488 :=
  interval_of_check _ 31472 16 (by decide +kernel)
theorem Check245.checked : Interval test 31360 31488 :=
  (FiniteChecks.interval_append test 31360 31424 31488
  (FiniteChecks.interval_append test 31360 31392 31424
  (FiniteChecks.interval_append test 31360 31376 31392
  Check245.part31360
  Check245.part31376)
  (FiniteChecks.interval_append test 31392 31408 31424
  Check245.part31392
  Check245.part31408))
  (FiniteChecks.interval_append test 31424 31456 31488
  (FiniteChecks.interval_append test 31424 31440 31456
  Check245.part31424
  Check245.part31440)
  (FiniteChecks.interval_append test 31456 31472 31488
  Check245.part31456
  Check245.part31472)))
#print axioms Check245.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check246.part31488 : Interval test 31488 31504 :=
  interval_of_check _ 31488 16 (by decide +kernel)
theorem Check246.part31504 : Interval test 31504 31520 :=
  interval_of_check _ 31504 16 (by decide +kernel)
theorem Check246.part31520 : Interval test 31520 31536 :=
  interval_of_check _ 31520 16 (by decide +kernel)
theorem Check246.part31536 : Interval test 31536 31552 :=
  interval_of_check _ 31536 16 (by decide +kernel)
theorem Check246.part31552 : Interval test 31552 31568 :=
  interval_of_check _ 31552 16 (by decide +kernel)
theorem Check246.part31568 : Interval test 31568 31584 :=
  interval_of_check _ 31568 16 (by decide +kernel)
theorem Check246.part31584 : Interval test 31584 31600 :=
  interval_of_check _ 31584 16 (by decide +kernel)
theorem Check246.part31600 : Interval test 31600 31616 :=
  interval_of_check _ 31600 16 (by decide +kernel)
theorem Check246.checked : Interval test 31488 31616 :=
  (FiniteChecks.interval_append test 31488 31552 31616
  (FiniteChecks.interval_append test 31488 31520 31552
  (FiniteChecks.interval_append test 31488 31504 31520
  Check246.part31488
  Check246.part31504)
  (FiniteChecks.interval_append test 31520 31536 31552
  Check246.part31520
  Check246.part31536))
  (FiniteChecks.interval_append test 31552 31584 31616
  (FiniteChecks.interval_append test 31552 31568 31584
  Check246.part31552
  Check246.part31568)
  (FiniteChecks.interval_append test 31584 31600 31616
  Check246.part31584
  Check246.part31600)))
#print axioms Check246.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check247.part31616 : Interval test 31616 31632 :=
  interval_of_check _ 31616 16 (by decide +kernel)
theorem Check247.part31632 : Interval test 31632 31648 :=
  interval_of_check _ 31632 16 (by decide +kernel)
theorem Check247.part31648 : Interval test 31648 31664 :=
  interval_of_check _ 31648 16 (by decide +kernel)
theorem Check247.part31664 : Interval test 31664 31680 :=
  interval_of_check _ 31664 16 (by decide +kernel)
theorem Check247.part31680 : Interval test 31680 31696 :=
  interval_of_check _ 31680 16 (by decide +kernel)
theorem Check247.part31696 : Interval test 31696 31712 :=
  interval_of_check _ 31696 16 (by decide +kernel)
theorem Check247.part31712 : Interval test 31712 31728 :=
  interval_of_check _ 31712 16 (by decide +kernel)
theorem Check247.part31728 : Interval test 31728 31744 :=
  interval_of_check _ 31728 16 (by decide +kernel)
theorem Check247.checked : Interval test 31616 31744 :=
  (FiniteChecks.interval_append test 31616 31680 31744
  (FiniteChecks.interval_append test 31616 31648 31680
  (FiniteChecks.interval_append test 31616 31632 31648
  Check247.part31616
  Check247.part31632)
  (FiniteChecks.interval_append test 31648 31664 31680
  Check247.part31648
  Check247.part31664))
  (FiniteChecks.interval_append test 31680 31712 31744
  (FiniteChecks.interval_append test 31680 31696 31712
  Check247.part31680
  Check247.part31696)
  (FiniteChecks.interval_append test 31712 31728 31744
  Check247.part31712
  Check247.part31728)))
#print axioms Check247.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check248.part31744 : Interval test 31744 31760 :=
  interval_of_check _ 31744 16 (by decide +kernel)
theorem Check248.part31760 : Interval test 31760 31776 :=
  interval_of_check _ 31760 16 (by decide +kernel)
theorem Check248.part31776 : Interval test 31776 31792 :=
  interval_of_check _ 31776 16 (by decide +kernel)
theorem Check248.part31792 : Interval test 31792 31808 :=
  interval_of_check _ 31792 16 (by decide +kernel)
theorem Check248.part31808 : Interval test 31808 31824 :=
  interval_of_check _ 31808 16 (by decide +kernel)
theorem Check248.part31824 : Interval test 31824 31840 :=
  interval_of_check _ 31824 16 (by decide +kernel)
theorem Check248.part31840 : Interval test 31840 31856 :=
  interval_of_check _ 31840 16 (by decide +kernel)
theorem Check248.part31856 : Interval test 31856 31872 :=
  interval_of_check _ 31856 16 (by decide +kernel)
theorem Check248.checked : Interval test 31744 31872 :=
  (FiniteChecks.interval_append test 31744 31808 31872
  (FiniteChecks.interval_append test 31744 31776 31808
  (FiniteChecks.interval_append test 31744 31760 31776
  Check248.part31744
  Check248.part31760)
  (FiniteChecks.interval_append test 31776 31792 31808
  Check248.part31776
  Check248.part31792))
  (FiniteChecks.interval_append test 31808 31840 31872
  (FiniteChecks.interval_append test 31808 31824 31840
  Check248.part31808
  Check248.part31824)
  (FiniteChecks.interval_append test 31840 31856 31872
  Check248.part31840
  Check248.part31856)))
#print axioms Check248.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check249.part31872 : Interval test 31872 31888 :=
  interval_of_check _ 31872 16 (by decide +kernel)
theorem Check249.part31888 : Interval test 31888 31904 :=
  interval_of_check _ 31888 16 (by decide +kernel)
theorem Check249.part31904 : Interval test 31904 31920 :=
  interval_of_check _ 31904 16 (by decide +kernel)
theorem Check249.part31920 : Interval test 31920 31936 :=
  interval_of_check _ 31920 16 (by decide +kernel)
theorem Check249.part31936 : Interval test 31936 31952 :=
  interval_of_check _ 31936 16 (by decide +kernel)
theorem Check249.part31952 : Interval test 31952 31968 :=
  interval_of_check _ 31952 16 (by decide +kernel)
theorem Check249.part31968 : Interval test 31968 31984 :=
  interval_of_check _ 31968 16 (by decide +kernel)
theorem Check249.part31984 : Interval test 31984 32000 :=
  interval_of_check _ 31984 16 (by decide +kernel)
theorem Check249.checked : Interval test 31872 32000 :=
  (FiniteChecks.interval_append test 31872 31936 32000
  (FiniteChecks.interval_append test 31872 31904 31936
  (FiniteChecks.interval_append test 31872 31888 31904
  Check249.part31872
  Check249.part31888)
  (FiniteChecks.interval_append test 31904 31920 31936
  Check249.part31904
  Check249.part31920))
  (FiniteChecks.interval_append test 31936 31968 32000
  (FiniteChecks.interval_append test 31936 31952 31968
  Check249.part31936
  Check249.part31952)
  (FiniteChecks.interval_append test 31968 31984 32000
  Check249.part31968
  Check249.part31984)))
#print axioms Check249.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check250.part32000 : Interval test 32000 32016 :=
  interval_of_check _ 32000 16 (by decide +kernel)
theorem Check250.part32016 : Interval test 32016 32032 :=
  interval_of_check _ 32016 16 (by decide +kernel)
theorem Check250.part32032 : Interval test 32032 32048 :=
  interval_of_check _ 32032 16 (by decide +kernel)
theorem Check250.part32048 : Interval test 32048 32064 :=
  interval_of_check _ 32048 16 (by decide +kernel)
theorem Check250.part32064 : Interval test 32064 32080 :=
  interval_of_check _ 32064 16 (by decide +kernel)
theorem Check250.part32080 : Interval test 32080 32096 :=
  interval_of_check _ 32080 16 (by decide +kernel)
theorem Check250.part32096 : Interval test 32096 32112 :=
  interval_of_check _ 32096 16 (by decide +kernel)
theorem Check250.part32112 : Interval test 32112 32128 :=
  interval_of_check _ 32112 16 (by decide +kernel)
theorem Check250.checked : Interval test 32000 32128 :=
  (FiniteChecks.interval_append test 32000 32064 32128
  (FiniteChecks.interval_append test 32000 32032 32064
  (FiniteChecks.interval_append test 32000 32016 32032
  Check250.part32000
  Check250.part32016)
  (FiniteChecks.interval_append test 32032 32048 32064
  Check250.part32032
  Check250.part32048))
  (FiniteChecks.interval_append test 32064 32096 32128
  (FiniteChecks.interval_append test 32064 32080 32096
  Check250.part32064
  Check250.part32080)
  (FiniteChecks.interval_append test 32096 32112 32128
  Check250.part32096
  Check250.part32112)))
#print axioms Check250.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check251.part32128 : Interval test 32128 32144 :=
  interval_of_check _ 32128 16 (by decide +kernel)
theorem Check251.part32144 : Interval test 32144 32160 :=
  interval_of_check _ 32144 16 (by decide +kernel)
theorem Check251.part32160 : Interval test 32160 32176 :=
  interval_of_check _ 32160 16 (by decide +kernel)
theorem Check251.part32176 : Interval test 32176 32192 :=
  interval_of_check _ 32176 16 (by decide +kernel)
theorem Check251.part32192 : Interval test 32192 32208 :=
  interval_of_check _ 32192 16 (by decide +kernel)
theorem Check251.part32208 : Interval test 32208 32224 :=
  interval_of_check _ 32208 16 (by decide +kernel)
theorem Check251.part32224 : Interval test 32224 32240 :=
  interval_of_check _ 32224 16 (by decide +kernel)
theorem Check251.part32240 : Interval test 32240 32256 :=
  interval_of_check _ 32240 16 (by decide +kernel)
theorem Check251.checked : Interval test 32128 32256 :=
  (FiniteChecks.interval_append test 32128 32192 32256
  (FiniteChecks.interval_append test 32128 32160 32192
  (FiniteChecks.interval_append test 32128 32144 32160
  Check251.part32128
  Check251.part32144)
  (FiniteChecks.interval_append test 32160 32176 32192
  Check251.part32160
  Check251.part32176))
  (FiniteChecks.interval_append test 32192 32224 32256
  (FiniteChecks.interval_append test 32192 32208 32224
  Check251.part32192
  Check251.part32208)
  (FiniteChecks.interval_append test 32224 32240 32256
  Check251.part32224
  Check251.part32240)))
#print axioms Check251.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check252.part32256 : Interval test 32256 32272 :=
  interval_of_check _ 32256 16 (by decide +kernel)
theorem Check252.part32272 : Interval test 32272 32288 :=
  interval_of_check _ 32272 16 (by decide +kernel)
theorem Check252.part32288 : Interval test 32288 32304 :=
  interval_of_check _ 32288 16 (by decide +kernel)
theorem Check252.part32304 : Interval test 32304 32320 :=
  interval_of_check _ 32304 16 (by decide +kernel)
theorem Check252.part32320 : Interval test 32320 32336 :=
  interval_of_check _ 32320 16 (by decide +kernel)
theorem Check252.part32336 : Interval test 32336 32352 :=
  interval_of_check _ 32336 16 (by decide +kernel)
theorem Check252.part32352 : Interval test 32352 32368 :=
  interval_of_check _ 32352 16 (by decide +kernel)
theorem Check252.part32368 : Interval test 32368 32384 :=
  interval_of_check _ 32368 16 (by decide +kernel)
theorem Check252.checked : Interval test 32256 32384 :=
  (FiniteChecks.interval_append test 32256 32320 32384
  (FiniteChecks.interval_append test 32256 32288 32320
  (FiniteChecks.interval_append test 32256 32272 32288
  Check252.part32256
  Check252.part32272)
  (FiniteChecks.interval_append test 32288 32304 32320
  Check252.part32288
  Check252.part32304))
  (FiniteChecks.interval_append test 32320 32352 32384
  (FiniteChecks.interval_append test 32320 32336 32352
  Check252.part32320
  Check252.part32336)
  (FiniteChecks.interval_append test 32352 32368 32384
  Check252.part32352
  Check252.part32368)))
#print axioms Check252.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check253.part32384 : Interval test 32384 32400 :=
  interval_of_check _ 32384 16 (by decide +kernel)
theorem Check253.part32400 : Interval test 32400 32416 :=
  interval_of_check _ 32400 16 (by decide +kernel)
theorem Check253.part32416 : Interval test 32416 32432 :=
  interval_of_check _ 32416 16 (by decide +kernel)
theorem Check253.part32432 : Interval test 32432 32448 :=
  interval_of_check _ 32432 16 (by decide +kernel)
theorem Check253.part32448 : Interval test 32448 32464 :=
  interval_of_check _ 32448 16 (by decide +kernel)
theorem Check253.part32464 : Interval test 32464 32480 :=
  interval_of_check _ 32464 16 (by decide +kernel)
theorem Check253.part32480 : Interval test 32480 32496 :=
  interval_of_check _ 32480 16 (by decide +kernel)
theorem Check253.part32496 : Interval test 32496 32512 :=
  interval_of_check _ 32496 16 (by decide +kernel)
theorem Check253.checked : Interval test 32384 32512 :=
  (FiniteChecks.interval_append test 32384 32448 32512
  (FiniteChecks.interval_append test 32384 32416 32448
  (FiniteChecks.interval_append test 32384 32400 32416
  Check253.part32384
  Check253.part32400)
  (FiniteChecks.interval_append test 32416 32432 32448
  Check253.part32416
  Check253.part32432))
  (FiniteChecks.interval_append test 32448 32480 32512
  (FiniteChecks.interval_append test 32448 32464 32480
  Check253.part32448
  Check253.part32464)
  (FiniteChecks.interval_append test 32480 32496 32512
  Check253.part32480
  Check253.part32496)))
#print axioms Check253.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check254.part32512 : Interval test 32512 32528 :=
  interval_of_check _ 32512 16 (by decide +kernel)
theorem Check254.part32528 : Interval test 32528 32544 :=
  interval_of_check _ 32528 16 (by decide +kernel)
theorem Check254.part32544 : Interval test 32544 32560 :=
  interval_of_check _ 32544 16 (by decide +kernel)
theorem Check254.part32560 : Interval test 32560 32576 :=
  interval_of_check _ 32560 16 (by decide +kernel)
theorem Check254.part32576 : Interval test 32576 32592 :=
  interval_of_check _ 32576 16 (by decide +kernel)
theorem Check254.part32592 : Interval test 32592 32608 :=
  interval_of_check _ 32592 16 (by decide +kernel)
theorem Check254.part32608 : Interval test 32608 32624 :=
  interval_of_check _ 32608 16 (by decide +kernel)
theorem Check254.part32624 : Interval test 32624 32640 :=
  interval_of_check _ 32624 16 (by decide +kernel)
theorem Check254.checked : Interval test 32512 32640 :=
  (FiniteChecks.interval_append test 32512 32576 32640
  (FiniteChecks.interval_append test 32512 32544 32576
  (FiniteChecks.interval_append test 32512 32528 32544
  Check254.part32512
  Check254.part32528)
  (FiniteChecks.interval_append test 32544 32560 32576
  Check254.part32544
  Check254.part32560))
  (FiniteChecks.interval_append test 32576 32608 32640
  (FiniteChecks.interval_append test 32576 32592 32608
  Check254.part32576
  Check254.part32592)
  (FiniteChecks.interval_append test 32608 32624 32640
  Check254.part32608
  Check254.part32624)))
#print axioms Check254.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check255.part32640 : Interval test 32640 32656 :=
  interval_of_check _ 32640 16 (by decide +kernel)
theorem Check255.part32656 : Interval test 32656 32672 :=
  interval_of_check _ 32656 16 (by decide +kernel)
theorem Check255.part32672 : Interval test 32672 32688 :=
  interval_of_check _ 32672 16 (by decide +kernel)
theorem Check255.part32688 : Interval test 32688 32704 :=
  interval_of_check _ 32688 16 (by decide +kernel)
theorem Check255.part32704 : Interval test 32704 32720 :=
  interval_of_check _ 32704 16 (by decide +kernel)
theorem Check255.part32720 : Interval test 32720 32736 :=
  interval_of_check _ 32720 16 (by decide +kernel)
theorem Check255.part32736 : Interval test 32736 32752 :=
  interval_of_check _ 32736 16 (by decide +kernel)
theorem Check255.part32752 : Interval test 32752 32768 :=
  interval_of_check _ 32752 16 (by decide +kernel)
theorem Check255.checked : Interval test 32640 32768 :=
  (FiniteChecks.interval_append test 32640 32704 32768
  (FiniteChecks.interval_append test 32640 32672 32704
  (FiniteChecks.interval_append test 32640 32656 32672
  Check255.part32640
  Check255.part32656)
  (FiniteChecks.interval_append test 32672 32688 32704
  Check255.part32672
  Check255.part32688))
  (FiniteChecks.interval_append test 32704 32736 32768
  (FiniteChecks.interval_append test 32704 32720 32736
  Check255.part32704
  Check255.part32720)
  (FiniteChecks.interval_append test 32736 32752 32768
  Check255.part32736
  Check255.part32752)))
#print axioms Check255.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check256.part32768 : Interval test 32768 32784 :=
  interval_of_check _ 32768 16 (by decide +kernel)
theorem Check256.part32784 : Interval test 32784 32800 :=
  interval_of_check _ 32784 16 (by decide +kernel)
theorem Check256.part32800 : Interval test 32800 32816 :=
  interval_of_check _ 32800 16 (by decide +kernel)
theorem Check256.part32816 : Interval test 32816 32832 :=
  interval_of_check _ 32816 16 (by decide +kernel)
theorem Check256.part32832 : Interval test 32832 32848 :=
  interval_of_check _ 32832 16 (by decide +kernel)
theorem Check256.part32848 : Interval test 32848 32864 :=
  interval_of_check _ 32848 16 (by decide +kernel)
theorem Check256.part32864 : Interval test 32864 32880 :=
  interval_of_check _ 32864 16 (by decide +kernel)
theorem Check256.part32880 : Interval test 32880 32896 :=
  interval_of_check _ 32880 16 (by decide +kernel)
theorem Check256.checked : Interval test 32768 32896 :=
  (FiniteChecks.interval_append test 32768 32832 32896
  (FiniteChecks.interval_append test 32768 32800 32832
  (FiniteChecks.interval_append test 32768 32784 32800
  Check256.part32768
  Check256.part32784)
  (FiniteChecks.interval_append test 32800 32816 32832
  Check256.part32800
  Check256.part32816))
  (FiniteChecks.interval_append test 32832 32864 32896
  (FiniteChecks.interval_append test 32832 32848 32864
  Check256.part32832
  Check256.part32848)
  (FiniteChecks.interval_append test 32864 32880 32896
  Check256.part32864
  Check256.part32880)))
#print axioms Check256.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check257.part32896 : Interval test 32896 32912 :=
  interval_of_check _ 32896 16 (by decide +kernel)
theorem Check257.part32912 : Interval test 32912 32928 :=
  interval_of_check _ 32912 16 (by decide +kernel)
theorem Check257.part32928 : Interval test 32928 32944 :=
  interval_of_check _ 32928 16 (by decide +kernel)
theorem Check257.part32944 : Interval test 32944 32960 :=
  interval_of_check _ 32944 16 (by decide +kernel)
theorem Check257.part32960 : Interval test 32960 32976 :=
  interval_of_check _ 32960 16 (by decide +kernel)
theorem Check257.part32976 : Interval test 32976 32992 :=
  interval_of_check _ 32976 16 (by decide +kernel)
theorem Check257.part32992 : Interval test 32992 33008 :=
  interval_of_check _ 32992 16 (by decide +kernel)
theorem Check257.part33008 : Interval test 33008 33024 :=
  interval_of_check _ 33008 16 (by decide +kernel)
theorem Check257.checked : Interval test 32896 33024 :=
  (FiniteChecks.interval_append test 32896 32960 33024
  (FiniteChecks.interval_append test 32896 32928 32960
  (FiniteChecks.interval_append test 32896 32912 32928
  Check257.part32896
  Check257.part32912)
  (FiniteChecks.interval_append test 32928 32944 32960
  Check257.part32928
  Check257.part32944))
  (FiniteChecks.interval_append test 32960 32992 33024
  (FiniteChecks.interval_append test 32960 32976 32992
  Check257.part32960
  Check257.part32976)
  (FiniteChecks.interval_append test 32992 33008 33024
  Check257.part32992
  Check257.part33008)))
#print axioms Check257.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check258.part33024 : Interval test 33024 33040 :=
  interval_of_check _ 33024 16 (by decide +kernel)
theorem Check258.part33040 : Interval test 33040 33056 :=
  interval_of_check _ 33040 16 (by decide +kernel)
theorem Check258.part33056 : Interval test 33056 33072 :=
  interval_of_check _ 33056 16 (by decide +kernel)
theorem Check258.part33072 : Interval test 33072 33088 :=
  interval_of_check _ 33072 16 (by decide +kernel)
theorem Check258.part33088 : Interval test 33088 33104 :=
  interval_of_check _ 33088 16 (by decide +kernel)
theorem Check258.part33104 : Interval test 33104 33120 :=
  interval_of_check _ 33104 16 (by decide +kernel)
theorem Check258.part33120 : Interval test 33120 33136 :=
  interval_of_check _ 33120 16 (by decide +kernel)
theorem Check258.part33136 : Interval test 33136 33152 :=
  interval_of_check _ 33136 16 (by decide +kernel)
theorem Check258.checked : Interval test 33024 33152 :=
  (FiniteChecks.interval_append test 33024 33088 33152
  (FiniteChecks.interval_append test 33024 33056 33088
  (FiniteChecks.interval_append test 33024 33040 33056
  Check258.part33024
  Check258.part33040)
  (FiniteChecks.interval_append test 33056 33072 33088
  Check258.part33056
  Check258.part33072))
  (FiniteChecks.interval_append test 33088 33120 33152
  (FiniteChecks.interval_append test 33088 33104 33120
  Check258.part33088
  Check258.part33104)
  (FiniteChecks.interval_append test 33120 33136 33152
  Check258.part33120
  Check258.part33136)))
#print axioms Check258.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check259.part33152 : Interval test 33152 33168 :=
  interval_of_check _ 33152 16 (by decide +kernel)
theorem Check259.part33168 : Interval test 33168 33184 :=
  interval_of_check _ 33168 16 (by decide +kernel)
theorem Check259.part33184 : Interval test 33184 33200 :=
  interval_of_check _ 33184 16 (by decide +kernel)
theorem Check259.part33200 : Interval test 33200 33216 :=
  interval_of_check _ 33200 16 (by decide +kernel)
theorem Check259.part33216 : Interval test 33216 33232 :=
  interval_of_check _ 33216 16 (by decide +kernel)
theorem Check259.part33232 : Interval test 33232 33248 :=
  interval_of_check _ 33232 16 (by decide +kernel)
theorem Check259.part33248 : Interval test 33248 33264 :=
  interval_of_check _ 33248 16 (by decide +kernel)
theorem Check259.part33264 : Interval test 33264 33280 :=
  interval_of_check _ 33264 16 (by decide +kernel)
theorem Check259.checked : Interval test 33152 33280 :=
  (FiniteChecks.interval_append test 33152 33216 33280
  (FiniteChecks.interval_append test 33152 33184 33216
  (FiniteChecks.interval_append test 33152 33168 33184
  Check259.part33152
  Check259.part33168)
  (FiniteChecks.interval_append test 33184 33200 33216
  Check259.part33184
  Check259.part33200))
  (FiniteChecks.interval_append test 33216 33248 33280
  (FiniteChecks.interval_append test 33216 33232 33248
  Check259.part33216
  Check259.part33232)
  (FiniteChecks.interval_append test 33248 33264 33280
  Check259.part33248
  Check259.part33264)))
#print axioms Check259.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
