module
prelude
public import SharedSix0IncidenceData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check120.part30720 : Interval test 30720 30736 :=
  interval_of_check _ 30720 16 (by decide +kernel)
theorem Check120.part30736 : Interval test 30736 30752 :=
  interval_of_check _ 30736 16 (by decide +kernel)
theorem Check120.part30752 : Interval test 30752 30768 :=
  interval_of_check _ 30752 16 (by decide +kernel)
theorem Check120.part30768 : Interval test 30768 30784 :=
  interval_of_check _ 30768 16 (by decide +kernel)
theorem Check120.part30784 : Interval test 30784 30800 :=
  interval_of_check _ 30784 16 (by decide +kernel)
theorem Check120.part30800 : Interval test 30800 30816 :=
  interval_of_check _ 30800 16 (by decide +kernel)
theorem Check120.part30816 : Interval test 30816 30832 :=
  interval_of_check _ 30816 16 (by decide +kernel)
theorem Check120.part30832 : Interval test 30832 30848 :=
  interval_of_check _ 30832 16 (by decide +kernel)
theorem Check120.part30848 : Interval test 30848 30864 :=
  interval_of_check _ 30848 16 (by decide +kernel)
theorem Check120.part30864 : Interval test 30864 30880 :=
  interval_of_check _ 30864 16 (by decide +kernel)
theorem Check120.part30880 : Interval test 30880 30896 :=
  interval_of_check _ 30880 16 (by decide +kernel)
theorem Check120.part30896 : Interval test 30896 30912 :=
  interval_of_check _ 30896 16 (by decide +kernel)
theorem Check120.part30912 : Interval test 30912 30928 :=
  interval_of_check _ 30912 16 (by decide +kernel)
theorem Check120.part30928 : Interval test 30928 30944 :=
  interval_of_check _ 30928 16 (by decide +kernel)
theorem Check120.part30944 : Interval test 30944 30960 :=
  interval_of_check _ 30944 16 (by decide +kernel)
theorem Check120.part30960 : Interval test 30960 30976 :=
  interval_of_check _ 30960 16 (by decide +kernel)
theorem Check120.checked : Interval test 30720 30976 :=
  (FiniteChecks.interval_append test 30720 30848 30976
  (FiniteChecks.interval_append test 30720 30784 30848
  (FiniteChecks.interval_append test 30720 30752 30784
  (FiniteChecks.interval_append test 30720 30736 30752
  Check120.part30720
  Check120.part30736)
  (FiniteChecks.interval_append test 30752 30768 30784
  Check120.part30752
  Check120.part30768))
  (FiniteChecks.interval_append test 30784 30816 30848
  (FiniteChecks.interval_append test 30784 30800 30816
  Check120.part30784
  Check120.part30800)
  (FiniteChecks.interval_append test 30816 30832 30848
  Check120.part30816
  Check120.part30832)))
  (FiniteChecks.interval_append test 30848 30912 30976
  (FiniteChecks.interval_append test 30848 30880 30912
  (FiniteChecks.interval_append test 30848 30864 30880
  Check120.part30848
  Check120.part30864)
  (FiniteChecks.interval_append test 30880 30896 30912
  Check120.part30880
  Check120.part30896))
  (FiniteChecks.interval_append test 30912 30944 30976
  (FiniteChecks.interval_append test 30912 30928 30944
  Check120.part30912
  Check120.part30928)
  (FiniteChecks.interval_append test 30944 30960 30976
  Check120.part30944
  Check120.part30960))))
#print axioms Check120.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check121.part30976 : Interval test 30976 30992 :=
  interval_of_check _ 30976 16 (by decide +kernel)
theorem Check121.part30992 : Interval test 30992 31008 :=
  interval_of_check _ 30992 16 (by decide +kernel)
theorem Check121.part31008 : Interval test 31008 31024 :=
  interval_of_check _ 31008 16 (by decide +kernel)
theorem Check121.part31024 : Interval test 31024 31040 :=
  interval_of_check _ 31024 16 (by decide +kernel)
theorem Check121.part31040 : Interval test 31040 31056 :=
  interval_of_check _ 31040 16 (by decide +kernel)
theorem Check121.part31056 : Interval test 31056 31072 :=
  interval_of_check _ 31056 16 (by decide +kernel)
theorem Check121.part31072 : Interval test 31072 31088 :=
  interval_of_check _ 31072 16 (by decide +kernel)
theorem Check121.part31088 : Interval test 31088 31104 :=
  interval_of_check _ 31088 16 (by decide +kernel)
theorem Check121.part31104 : Interval test 31104 31120 :=
  interval_of_check _ 31104 16 (by decide +kernel)
theorem Check121.part31120 : Interval test 31120 31136 :=
  interval_of_check _ 31120 16 (by decide +kernel)
theorem Check121.part31136 : Interval test 31136 31152 :=
  interval_of_check _ 31136 16 (by decide +kernel)
theorem Check121.part31152 : Interval test 31152 31168 :=
  interval_of_check _ 31152 16 (by decide +kernel)
theorem Check121.part31168 : Interval test 31168 31184 :=
  interval_of_check _ 31168 16 (by decide +kernel)
theorem Check121.part31184 : Interval test 31184 31200 :=
  interval_of_check _ 31184 16 (by decide +kernel)
theorem Check121.part31200 : Interval test 31200 31216 :=
  interval_of_check _ 31200 16 (by decide +kernel)
theorem Check121.part31216 : Interval test 31216 31232 :=
  interval_of_check _ 31216 16 (by decide +kernel)
theorem Check121.checked : Interval test 30976 31232 :=
  (FiniteChecks.interval_append test 30976 31104 31232
  (FiniteChecks.interval_append test 30976 31040 31104
  (FiniteChecks.interval_append test 30976 31008 31040
  (FiniteChecks.interval_append test 30976 30992 31008
  Check121.part30976
  Check121.part30992)
  (FiniteChecks.interval_append test 31008 31024 31040
  Check121.part31008
  Check121.part31024))
  (FiniteChecks.interval_append test 31040 31072 31104
  (FiniteChecks.interval_append test 31040 31056 31072
  Check121.part31040
  Check121.part31056)
  (FiniteChecks.interval_append test 31072 31088 31104
  Check121.part31072
  Check121.part31088)))
  (FiniteChecks.interval_append test 31104 31168 31232
  (FiniteChecks.interval_append test 31104 31136 31168
  (FiniteChecks.interval_append test 31104 31120 31136
  Check121.part31104
  Check121.part31120)
  (FiniteChecks.interval_append test 31136 31152 31168
  Check121.part31136
  Check121.part31152))
  (FiniteChecks.interval_append test 31168 31200 31232
  (FiniteChecks.interval_append test 31168 31184 31200
  Check121.part31168
  Check121.part31184)
  (FiniteChecks.interval_append test 31200 31216 31232
  Check121.part31200
  Check121.part31216))))
#print axioms Check121.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check122.part31232 : Interval test 31232 31248 :=
  interval_of_check _ 31232 16 (by decide +kernel)
theorem Check122.part31248 : Interval test 31248 31264 :=
  interval_of_check _ 31248 16 (by decide +kernel)
theorem Check122.part31264 : Interval test 31264 31280 :=
  interval_of_check _ 31264 16 (by decide +kernel)
theorem Check122.part31280 : Interval test 31280 31296 :=
  interval_of_check _ 31280 16 (by decide +kernel)
theorem Check122.part31296 : Interval test 31296 31312 :=
  interval_of_check _ 31296 16 (by decide +kernel)
theorem Check122.part31312 : Interval test 31312 31328 :=
  interval_of_check _ 31312 16 (by decide +kernel)
theorem Check122.part31328 : Interval test 31328 31344 :=
  interval_of_check _ 31328 16 (by decide +kernel)
theorem Check122.part31344 : Interval test 31344 31360 :=
  interval_of_check _ 31344 16 (by decide +kernel)
theorem Check122.part31360 : Interval test 31360 31376 :=
  interval_of_check _ 31360 16 (by decide +kernel)
theorem Check122.part31376 : Interval test 31376 31392 :=
  interval_of_check _ 31376 16 (by decide +kernel)
theorem Check122.part31392 : Interval test 31392 31408 :=
  interval_of_check _ 31392 16 (by decide +kernel)
theorem Check122.part31408 : Interval test 31408 31424 :=
  interval_of_check _ 31408 16 (by decide +kernel)
theorem Check122.part31424 : Interval test 31424 31440 :=
  interval_of_check _ 31424 16 (by decide +kernel)
theorem Check122.part31440 : Interval test 31440 31456 :=
  interval_of_check _ 31440 16 (by decide +kernel)
theorem Check122.part31456 : Interval test 31456 31472 :=
  interval_of_check _ 31456 16 (by decide +kernel)
theorem Check122.part31472 : Interval test 31472 31488 :=
  interval_of_check _ 31472 16 (by decide +kernel)
theorem Check122.checked : Interval test 31232 31488 :=
  (FiniteChecks.interval_append test 31232 31360 31488
  (FiniteChecks.interval_append test 31232 31296 31360
  (FiniteChecks.interval_append test 31232 31264 31296
  (FiniteChecks.interval_append test 31232 31248 31264
  Check122.part31232
  Check122.part31248)
  (FiniteChecks.interval_append test 31264 31280 31296
  Check122.part31264
  Check122.part31280))
  (FiniteChecks.interval_append test 31296 31328 31360
  (FiniteChecks.interval_append test 31296 31312 31328
  Check122.part31296
  Check122.part31312)
  (FiniteChecks.interval_append test 31328 31344 31360
  Check122.part31328
  Check122.part31344)))
  (FiniteChecks.interval_append test 31360 31424 31488
  (FiniteChecks.interval_append test 31360 31392 31424
  (FiniteChecks.interval_append test 31360 31376 31392
  Check122.part31360
  Check122.part31376)
  (FiniteChecks.interval_append test 31392 31408 31424
  Check122.part31392
  Check122.part31408))
  (FiniteChecks.interval_append test 31424 31456 31488
  (FiniteChecks.interval_append test 31424 31440 31456
  Check122.part31424
  Check122.part31440)
  (FiniteChecks.interval_append test 31456 31472 31488
  Check122.part31456
  Check122.part31472))))
#print axioms Check122.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check123.part31488 : Interval test 31488 31504 :=
  interval_of_check _ 31488 16 (by decide +kernel)
theorem Check123.part31504 : Interval test 31504 31520 :=
  interval_of_check _ 31504 16 (by decide +kernel)
theorem Check123.part31520 : Interval test 31520 31536 :=
  interval_of_check _ 31520 16 (by decide +kernel)
theorem Check123.part31536 : Interval test 31536 31552 :=
  interval_of_check _ 31536 16 (by decide +kernel)
theorem Check123.part31552 : Interval test 31552 31568 :=
  interval_of_check _ 31552 16 (by decide +kernel)
theorem Check123.part31568 : Interval test 31568 31584 :=
  interval_of_check _ 31568 16 (by decide +kernel)
theorem Check123.part31584 : Interval test 31584 31600 :=
  interval_of_check _ 31584 16 (by decide +kernel)
theorem Check123.part31600 : Interval test 31600 31616 :=
  interval_of_check _ 31600 16 (by decide +kernel)
theorem Check123.part31616 : Interval test 31616 31632 :=
  interval_of_check _ 31616 16 (by decide +kernel)
theorem Check123.part31632 : Interval test 31632 31648 :=
  interval_of_check _ 31632 16 (by decide +kernel)
theorem Check123.part31648 : Interval test 31648 31664 :=
  interval_of_check _ 31648 16 (by decide +kernel)
theorem Check123.part31664 : Interval test 31664 31680 :=
  interval_of_check _ 31664 16 (by decide +kernel)
theorem Check123.part31680 : Interval test 31680 31696 :=
  interval_of_check _ 31680 16 (by decide +kernel)
theorem Check123.part31696 : Interval test 31696 31712 :=
  interval_of_check _ 31696 16 (by decide +kernel)
theorem Check123.part31712 : Interval test 31712 31728 :=
  interval_of_check _ 31712 16 (by decide +kernel)
theorem Check123.part31728 : Interval test 31728 31744 :=
  interval_of_check _ 31728 16 (by decide +kernel)
theorem Check123.checked : Interval test 31488 31744 :=
  (FiniteChecks.interval_append test 31488 31616 31744
  (FiniteChecks.interval_append test 31488 31552 31616
  (FiniteChecks.interval_append test 31488 31520 31552
  (FiniteChecks.interval_append test 31488 31504 31520
  Check123.part31488
  Check123.part31504)
  (FiniteChecks.interval_append test 31520 31536 31552
  Check123.part31520
  Check123.part31536))
  (FiniteChecks.interval_append test 31552 31584 31616
  (FiniteChecks.interval_append test 31552 31568 31584
  Check123.part31552
  Check123.part31568)
  (FiniteChecks.interval_append test 31584 31600 31616
  Check123.part31584
  Check123.part31600)))
  (FiniteChecks.interval_append test 31616 31680 31744
  (FiniteChecks.interval_append test 31616 31648 31680
  (FiniteChecks.interval_append test 31616 31632 31648
  Check123.part31616
  Check123.part31632)
  (FiniteChecks.interval_append test 31648 31664 31680
  Check123.part31648
  Check123.part31664))
  (FiniteChecks.interval_append test 31680 31712 31744
  (FiniteChecks.interval_append test 31680 31696 31712
  Check123.part31680
  Check123.part31696)
  (FiniteChecks.interval_append test 31712 31728 31744
  Check123.part31712
  Check123.part31728))))
#print axioms Check123.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check124.part31744 : Interval test 31744 31760 :=
  interval_of_check _ 31744 16 (by decide +kernel)
theorem Check124.part31760 : Interval test 31760 31776 :=
  interval_of_check _ 31760 16 (by decide +kernel)
theorem Check124.part31776 : Interval test 31776 31792 :=
  interval_of_check _ 31776 16 (by decide +kernel)
theorem Check124.part31792 : Interval test 31792 31808 :=
  interval_of_check _ 31792 16 (by decide +kernel)
theorem Check124.part31808 : Interval test 31808 31824 :=
  interval_of_check _ 31808 16 (by decide +kernel)
theorem Check124.part31824 : Interval test 31824 31840 :=
  interval_of_check _ 31824 16 (by decide +kernel)
theorem Check124.part31840 : Interval test 31840 31856 :=
  interval_of_check _ 31840 16 (by decide +kernel)
theorem Check124.part31856 : Interval test 31856 31872 :=
  interval_of_check _ 31856 16 (by decide +kernel)
theorem Check124.part31872 : Interval test 31872 31888 :=
  interval_of_check _ 31872 16 (by decide +kernel)
theorem Check124.part31888 : Interval test 31888 31904 :=
  interval_of_check _ 31888 16 (by decide +kernel)
theorem Check124.part31904 : Interval test 31904 31920 :=
  interval_of_check _ 31904 16 (by decide +kernel)
theorem Check124.part31920 : Interval test 31920 31936 :=
  interval_of_check _ 31920 16 (by decide +kernel)
theorem Check124.part31936 : Interval test 31936 31952 :=
  interval_of_check _ 31936 16 (by decide +kernel)
theorem Check124.part31952 : Interval test 31952 31968 :=
  interval_of_check _ 31952 16 (by decide +kernel)
theorem Check124.part31968 : Interval test 31968 31984 :=
  interval_of_check _ 31968 16 (by decide +kernel)
theorem Check124.part31984 : Interval test 31984 32000 :=
  interval_of_check _ 31984 16 (by decide +kernel)
theorem Check124.checked : Interval test 31744 32000 :=
  (FiniteChecks.interval_append test 31744 31872 32000
  (FiniteChecks.interval_append test 31744 31808 31872
  (FiniteChecks.interval_append test 31744 31776 31808
  (FiniteChecks.interval_append test 31744 31760 31776
  Check124.part31744
  Check124.part31760)
  (FiniteChecks.interval_append test 31776 31792 31808
  Check124.part31776
  Check124.part31792))
  (FiniteChecks.interval_append test 31808 31840 31872
  (FiniteChecks.interval_append test 31808 31824 31840
  Check124.part31808
  Check124.part31824)
  (FiniteChecks.interval_append test 31840 31856 31872
  Check124.part31840
  Check124.part31856)))
  (FiniteChecks.interval_append test 31872 31936 32000
  (FiniteChecks.interval_append test 31872 31904 31936
  (FiniteChecks.interval_append test 31872 31888 31904
  Check124.part31872
  Check124.part31888)
  (FiniteChecks.interval_append test 31904 31920 31936
  Check124.part31904
  Check124.part31920))
  (FiniteChecks.interval_append test 31936 31968 32000
  (FiniteChecks.interval_append test 31936 31952 31968
  Check124.part31936
  Check124.part31952)
  (FiniteChecks.interval_append test 31968 31984 32000
  Check124.part31968
  Check124.part31984))))
#print axioms Check124.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check125.part32000 : Interval test 32000 32016 :=
  interval_of_check _ 32000 16 (by decide +kernel)
theorem Check125.part32016 : Interval test 32016 32032 :=
  interval_of_check _ 32016 16 (by decide +kernel)
theorem Check125.part32032 : Interval test 32032 32048 :=
  interval_of_check _ 32032 16 (by decide +kernel)
theorem Check125.part32048 : Interval test 32048 32064 :=
  interval_of_check _ 32048 16 (by decide +kernel)
theorem Check125.part32064 : Interval test 32064 32080 :=
  interval_of_check _ 32064 16 (by decide +kernel)
theorem Check125.part32080 : Interval test 32080 32096 :=
  interval_of_check _ 32080 16 (by decide +kernel)
theorem Check125.part32096 : Interval test 32096 32112 :=
  interval_of_check _ 32096 16 (by decide +kernel)
theorem Check125.part32112 : Interval test 32112 32128 :=
  interval_of_check _ 32112 16 (by decide +kernel)
theorem Check125.part32128 : Interval test 32128 32144 :=
  interval_of_check _ 32128 16 (by decide +kernel)
theorem Check125.part32144 : Interval test 32144 32160 :=
  interval_of_check _ 32144 16 (by decide +kernel)
theorem Check125.part32160 : Interval test 32160 32176 :=
  interval_of_check _ 32160 16 (by decide +kernel)
theorem Check125.part32176 : Interval test 32176 32192 :=
  interval_of_check _ 32176 16 (by decide +kernel)
theorem Check125.part32192 : Interval test 32192 32208 :=
  interval_of_check _ 32192 16 (by decide +kernel)
theorem Check125.part32208 : Interval test 32208 32224 :=
  interval_of_check _ 32208 16 (by decide +kernel)
theorem Check125.part32224 : Interval test 32224 32240 :=
  interval_of_check _ 32224 16 (by decide +kernel)
theorem Check125.part32240 : Interval test 32240 32256 :=
  interval_of_check _ 32240 16 (by decide +kernel)
theorem Check125.checked : Interval test 32000 32256 :=
  (FiniteChecks.interval_append test 32000 32128 32256
  (FiniteChecks.interval_append test 32000 32064 32128
  (FiniteChecks.interval_append test 32000 32032 32064
  (FiniteChecks.interval_append test 32000 32016 32032
  Check125.part32000
  Check125.part32016)
  (FiniteChecks.interval_append test 32032 32048 32064
  Check125.part32032
  Check125.part32048))
  (FiniteChecks.interval_append test 32064 32096 32128
  (FiniteChecks.interval_append test 32064 32080 32096
  Check125.part32064
  Check125.part32080)
  (FiniteChecks.interval_append test 32096 32112 32128
  Check125.part32096
  Check125.part32112)))
  (FiniteChecks.interval_append test 32128 32192 32256
  (FiniteChecks.interval_append test 32128 32160 32192
  (FiniteChecks.interval_append test 32128 32144 32160
  Check125.part32128
  Check125.part32144)
  (FiniteChecks.interval_append test 32160 32176 32192
  Check125.part32160
  Check125.part32176))
  (FiniteChecks.interval_append test 32192 32224 32256
  (FiniteChecks.interval_append test 32192 32208 32224
  Check125.part32192
  Check125.part32208)
  (FiniteChecks.interval_append test 32224 32240 32256
  Check125.part32224
  Check125.part32240))))
#print axioms Check125.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check126.part32256 : Interval test 32256 32272 :=
  interval_of_check _ 32256 16 (by decide +kernel)
theorem Check126.part32272 : Interval test 32272 32288 :=
  interval_of_check _ 32272 16 (by decide +kernel)
theorem Check126.part32288 : Interval test 32288 32304 :=
  interval_of_check _ 32288 16 (by decide +kernel)
theorem Check126.part32304 : Interval test 32304 32320 :=
  interval_of_check _ 32304 16 (by decide +kernel)
theorem Check126.part32320 : Interval test 32320 32336 :=
  interval_of_check _ 32320 16 (by decide +kernel)
theorem Check126.part32336 : Interval test 32336 32352 :=
  interval_of_check _ 32336 16 (by decide +kernel)
theorem Check126.part32352 : Interval test 32352 32368 :=
  interval_of_check _ 32352 16 (by decide +kernel)
theorem Check126.part32368 : Interval test 32368 32384 :=
  interval_of_check _ 32368 16 (by decide +kernel)
theorem Check126.part32384 : Interval test 32384 32400 :=
  interval_of_check _ 32384 16 (by decide +kernel)
theorem Check126.part32400 : Interval test 32400 32416 :=
  interval_of_check _ 32400 16 (by decide +kernel)
theorem Check126.part32416 : Interval test 32416 32432 :=
  interval_of_check _ 32416 16 (by decide +kernel)
theorem Check126.part32432 : Interval test 32432 32448 :=
  interval_of_check _ 32432 16 (by decide +kernel)
theorem Check126.part32448 : Interval test 32448 32464 :=
  interval_of_check _ 32448 16 (by decide +kernel)
theorem Check126.part32464 : Interval test 32464 32480 :=
  interval_of_check _ 32464 16 (by decide +kernel)
theorem Check126.part32480 : Interval test 32480 32496 :=
  interval_of_check _ 32480 16 (by decide +kernel)
theorem Check126.part32496 : Interval test 32496 32512 :=
  interval_of_check _ 32496 16 (by decide +kernel)
theorem Check126.checked : Interval test 32256 32512 :=
  (FiniteChecks.interval_append test 32256 32384 32512
  (FiniteChecks.interval_append test 32256 32320 32384
  (FiniteChecks.interval_append test 32256 32288 32320
  (FiniteChecks.interval_append test 32256 32272 32288
  Check126.part32256
  Check126.part32272)
  (FiniteChecks.interval_append test 32288 32304 32320
  Check126.part32288
  Check126.part32304))
  (FiniteChecks.interval_append test 32320 32352 32384
  (FiniteChecks.interval_append test 32320 32336 32352
  Check126.part32320
  Check126.part32336)
  (FiniteChecks.interval_append test 32352 32368 32384
  Check126.part32352
  Check126.part32368)))
  (FiniteChecks.interval_append test 32384 32448 32512
  (FiniteChecks.interval_append test 32384 32416 32448
  (FiniteChecks.interval_append test 32384 32400 32416
  Check126.part32384
  Check126.part32400)
  (FiniteChecks.interval_append test 32416 32432 32448
  Check126.part32416
  Check126.part32432))
  (FiniteChecks.interval_append test 32448 32480 32512
  (FiniteChecks.interval_append test 32448 32464 32480
  Check126.part32448
  Check126.part32464)
  (FiniteChecks.interval_append test 32480 32496 32512
  Check126.part32480
  Check126.part32496))))
#print axioms Check126.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check127.part32512 : Interval test 32512 32528 :=
  interval_of_check _ 32512 16 (by decide +kernel)
theorem Check127.part32528 : Interval test 32528 32544 :=
  interval_of_check _ 32528 16 (by decide +kernel)
theorem Check127.part32544 : Interval test 32544 32560 :=
  interval_of_check _ 32544 16 (by decide +kernel)
theorem Check127.part32560 : Interval test 32560 32576 :=
  interval_of_check _ 32560 16 (by decide +kernel)
theorem Check127.part32576 : Interval test 32576 32592 :=
  interval_of_check _ 32576 16 (by decide +kernel)
theorem Check127.part32592 : Interval test 32592 32608 :=
  interval_of_check _ 32592 16 (by decide +kernel)
theorem Check127.part32608 : Interval test 32608 32624 :=
  interval_of_check _ 32608 16 (by decide +kernel)
theorem Check127.part32624 : Interval test 32624 32640 :=
  interval_of_check _ 32624 16 (by decide +kernel)
theorem Check127.part32640 : Interval test 32640 32656 :=
  interval_of_check _ 32640 16 (by decide +kernel)
theorem Check127.part32656 : Interval test 32656 32672 :=
  interval_of_check _ 32656 16 (by decide +kernel)
theorem Check127.part32672 : Interval test 32672 32688 :=
  interval_of_check _ 32672 16 (by decide +kernel)
theorem Check127.part32688 : Interval test 32688 32704 :=
  interval_of_check _ 32688 16 (by decide +kernel)
theorem Check127.part32704 : Interval test 32704 32720 :=
  interval_of_check _ 32704 16 (by decide +kernel)
theorem Check127.part32720 : Interval test 32720 32736 :=
  interval_of_check _ 32720 16 (by decide +kernel)
theorem Check127.part32736 : Interval test 32736 32752 :=
  interval_of_check _ 32736 16 (by decide +kernel)
theorem Check127.part32752 : Interval test 32752 32768 :=
  interval_of_check _ 32752 16 (by decide +kernel)
theorem Check127.checked : Interval test 32512 32768 :=
  (FiniteChecks.interval_append test 32512 32640 32768
  (FiniteChecks.interval_append test 32512 32576 32640
  (FiniteChecks.interval_append test 32512 32544 32576
  (FiniteChecks.interval_append test 32512 32528 32544
  Check127.part32512
  Check127.part32528)
  (FiniteChecks.interval_append test 32544 32560 32576
  Check127.part32544
  Check127.part32560))
  (FiniteChecks.interval_append test 32576 32608 32640
  (FiniteChecks.interval_append test 32576 32592 32608
  Check127.part32576
  Check127.part32592)
  (FiniteChecks.interval_append test 32608 32624 32640
  Check127.part32608
  Check127.part32624)))
  (FiniteChecks.interval_append test 32640 32704 32768
  (FiniteChecks.interval_append test 32640 32672 32704
  (FiniteChecks.interval_append test 32640 32656 32672
  Check127.part32640
  Check127.part32656)
  (FiniteChecks.interval_append test 32672 32688 32704
  Check127.part32672
  Check127.part32688))
  (FiniteChecks.interval_append test 32704 32736 32768
  (FiniteChecks.interval_append test 32704 32720 32736
  Check127.part32704
  Check127.part32720)
  (FiniteChecks.interval_append test 32736 32752 32768
  Check127.part32736
  Check127.part32752))))
#print axioms Check127.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check128.part32768 : Interval test 32768 32784 :=
  interval_of_check _ 32768 16 (by decide +kernel)
theorem Check128.part32784 : Interval test 32784 32800 :=
  interval_of_check _ 32784 16 (by decide +kernel)
theorem Check128.part32800 : Interval test 32800 32816 :=
  interval_of_check _ 32800 16 (by decide +kernel)
theorem Check128.part32816 : Interval test 32816 32832 :=
  interval_of_check _ 32816 16 (by decide +kernel)
theorem Check128.part32832 : Interval test 32832 32848 :=
  interval_of_check _ 32832 16 (by decide +kernel)
theorem Check128.part32848 : Interval test 32848 32864 :=
  interval_of_check _ 32848 16 (by decide +kernel)
theorem Check128.part32864 : Interval test 32864 32880 :=
  interval_of_check _ 32864 16 (by decide +kernel)
theorem Check128.part32880 : Interval test 32880 32896 :=
  interval_of_check _ 32880 16 (by decide +kernel)
theorem Check128.part32896 : Interval test 32896 32912 :=
  interval_of_check _ 32896 16 (by decide +kernel)
theorem Check128.part32912 : Interval test 32912 32928 :=
  interval_of_check _ 32912 16 (by decide +kernel)
theorem Check128.part32928 : Interval test 32928 32944 :=
  interval_of_check _ 32928 16 (by decide +kernel)
theorem Check128.part32944 : Interval test 32944 32960 :=
  interval_of_check _ 32944 16 (by decide +kernel)
theorem Check128.part32960 : Interval test 32960 32976 :=
  interval_of_check _ 32960 16 (by decide +kernel)
theorem Check128.part32976 : Interval test 32976 32992 :=
  interval_of_check _ 32976 16 (by decide +kernel)
theorem Check128.part32992 : Interval test 32992 33008 :=
  interval_of_check _ 32992 16 (by decide +kernel)
theorem Check128.part33008 : Interval test 33008 33024 :=
  interval_of_check _ 33008 16 (by decide +kernel)
theorem Check128.checked : Interval test 32768 33024 :=
  (FiniteChecks.interval_append test 32768 32896 33024
  (FiniteChecks.interval_append test 32768 32832 32896
  (FiniteChecks.interval_append test 32768 32800 32832
  (FiniteChecks.interval_append test 32768 32784 32800
  Check128.part32768
  Check128.part32784)
  (FiniteChecks.interval_append test 32800 32816 32832
  Check128.part32800
  Check128.part32816))
  (FiniteChecks.interval_append test 32832 32864 32896
  (FiniteChecks.interval_append test 32832 32848 32864
  Check128.part32832
  Check128.part32848)
  (FiniteChecks.interval_append test 32864 32880 32896
  Check128.part32864
  Check128.part32880)))
  (FiniteChecks.interval_append test 32896 32960 33024
  (FiniteChecks.interval_append test 32896 32928 32960
  (FiniteChecks.interval_append test 32896 32912 32928
  Check128.part32896
  Check128.part32912)
  (FiniteChecks.interval_append test 32928 32944 32960
  Check128.part32928
  Check128.part32944))
  (FiniteChecks.interval_append test 32960 32992 33024
  (FiniteChecks.interval_append test 32960 32976 32992
  Check128.part32960
  Check128.part32976)
  (FiniteChecks.interval_append test 32992 33008 33024
  Check128.part32992
  Check128.part33008))))
#print axioms Check128.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check129.part33024 : Interval test 33024 33040 :=
  interval_of_check _ 33024 16 (by decide +kernel)
theorem Check129.part33040 : Interval test 33040 33056 :=
  interval_of_check _ 33040 16 (by decide +kernel)
theorem Check129.part33056 : Interval test 33056 33072 :=
  interval_of_check _ 33056 16 (by decide +kernel)
theorem Check129.part33072 : Interval test 33072 33088 :=
  interval_of_check _ 33072 16 (by decide +kernel)
theorem Check129.part33088 : Interval test 33088 33104 :=
  interval_of_check _ 33088 16 (by decide +kernel)
theorem Check129.part33104 : Interval test 33104 33120 :=
  interval_of_check _ 33104 16 (by decide +kernel)
theorem Check129.part33120 : Interval test 33120 33136 :=
  interval_of_check _ 33120 16 (by decide +kernel)
theorem Check129.part33136 : Interval test 33136 33152 :=
  interval_of_check _ 33136 16 (by decide +kernel)
theorem Check129.part33152 : Interval test 33152 33168 :=
  interval_of_check _ 33152 16 (by decide +kernel)
theorem Check129.part33168 : Interval test 33168 33184 :=
  interval_of_check _ 33168 16 (by decide +kernel)
theorem Check129.part33184 : Interval test 33184 33200 :=
  interval_of_check _ 33184 16 (by decide +kernel)
theorem Check129.part33200 : Interval test 33200 33216 :=
  interval_of_check _ 33200 16 (by decide +kernel)
theorem Check129.part33216 : Interval test 33216 33232 :=
  interval_of_check _ 33216 16 (by decide +kernel)
theorem Check129.part33232 : Interval test 33232 33248 :=
  interval_of_check _ 33232 16 (by decide +kernel)
theorem Check129.part33248 : Interval test 33248 33264 :=
  interval_of_check _ 33248 16 (by decide +kernel)
theorem Check129.part33264 : Interval test 33264 33280 :=
  interval_of_check _ 33264 16 (by decide +kernel)
theorem Check129.checked : Interval test 33024 33280 :=
  (FiniteChecks.interval_append test 33024 33152 33280
  (FiniteChecks.interval_append test 33024 33088 33152
  (FiniteChecks.interval_append test 33024 33056 33088
  (FiniteChecks.interval_append test 33024 33040 33056
  Check129.part33024
  Check129.part33040)
  (FiniteChecks.interval_append test 33056 33072 33088
  Check129.part33056
  Check129.part33072))
  (FiniteChecks.interval_append test 33088 33120 33152
  (FiniteChecks.interval_append test 33088 33104 33120
  Check129.part33088
  Check129.part33104)
  (FiniteChecks.interval_append test 33120 33136 33152
  Check129.part33120
  Check129.part33136)))
  (FiniteChecks.interval_append test 33152 33216 33280
  (FiniteChecks.interval_append test 33152 33184 33216
  (FiniteChecks.interval_append test 33152 33168 33184
  Check129.part33152
  Check129.part33168)
  (FiniteChecks.interval_append test 33184 33200 33216
  Check129.part33184
  Check129.part33200))
  (FiniteChecks.interval_append test 33216 33248 33280
  (FiniteChecks.interval_append test 33216 33232 33248
  Check129.part33216
  Check129.part33232)
  (FiniteChecks.interval_append test 33248 33264 33280
  Check129.part33248
  Check129.part33264))))
#print axioms Check129.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check130.part33280 : Interval test 33280 33296 :=
  interval_of_check _ 33280 16 (by decide +kernel)
theorem Check130.part33296 : Interval test 33296 33312 :=
  interval_of_check _ 33296 16 (by decide +kernel)
theorem Check130.part33312 : Interval test 33312 33328 :=
  interval_of_check _ 33312 16 (by decide +kernel)
theorem Check130.part33328 : Interval test 33328 33344 :=
  interval_of_check _ 33328 16 (by decide +kernel)
theorem Check130.part33344 : Interval test 33344 33360 :=
  interval_of_check _ 33344 16 (by decide +kernel)
theorem Check130.part33360 : Interval test 33360 33376 :=
  interval_of_check _ 33360 16 (by decide +kernel)
theorem Check130.part33376 : Interval test 33376 33392 :=
  interval_of_check _ 33376 16 (by decide +kernel)
theorem Check130.part33392 : Interval test 33392 33408 :=
  interval_of_check _ 33392 16 (by decide +kernel)
theorem Check130.part33408 : Interval test 33408 33424 :=
  interval_of_check _ 33408 16 (by decide +kernel)
theorem Check130.part33424 : Interval test 33424 33440 :=
  interval_of_check _ 33424 16 (by decide +kernel)
theorem Check130.part33440 : Interval test 33440 33456 :=
  interval_of_check _ 33440 16 (by decide +kernel)
theorem Check130.part33456 : Interval test 33456 33472 :=
  interval_of_check _ 33456 16 (by decide +kernel)
theorem Check130.part33472 : Interval test 33472 33488 :=
  interval_of_check _ 33472 16 (by decide +kernel)
theorem Check130.part33488 : Interval test 33488 33504 :=
  interval_of_check _ 33488 16 (by decide +kernel)
theorem Check130.part33504 : Interval test 33504 33520 :=
  interval_of_check _ 33504 16 (by decide +kernel)
theorem Check130.part33520 : Interval test 33520 33536 :=
  interval_of_check _ 33520 16 (by decide +kernel)
theorem Check130.checked : Interval test 33280 33536 :=
  (FiniteChecks.interval_append test 33280 33408 33536
  (FiniteChecks.interval_append test 33280 33344 33408
  (FiniteChecks.interval_append test 33280 33312 33344
  (FiniteChecks.interval_append test 33280 33296 33312
  Check130.part33280
  Check130.part33296)
  (FiniteChecks.interval_append test 33312 33328 33344
  Check130.part33312
  Check130.part33328))
  (FiniteChecks.interval_append test 33344 33376 33408
  (FiniteChecks.interval_append test 33344 33360 33376
  Check130.part33344
  Check130.part33360)
  (FiniteChecks.interval_append test 33376 33392 33408
  Check130.part33376
  Check130.part33392)))
  (FiniteChecks.interval_append test 33408 33472 33536
  (FiniteChecks.interval_append test 33408 33440 33472
  (FiniteChecks.interval_append test 33408 33424 33440
  Check130.part33408
  Check130.part33424)
  (FiniteChecks.interval_append test 33440 33456 33472
  Check130.part33440
  Check130.part33456))
  (FiniteChecks.interval_append test 33472 33504 33536
  (FiniteChecks.interval_append test 33472 33488 33504
  Check130.part33472
  Check130.part33488)
  (FiniteChecks.interval_append test 33504 33520 33536
  Check130.part33504
  Check130.part33520))))
#print axioms Check130.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check131.part33536 : Interval test 33536 33552 :=
  interval_of_check _ 33536 16 (by decide +kernel)
theorem Check131.part33552 : Interval test 33552 33568 :=
  interval_of_check _ 33552 16 (by decide +kernel)
theorem Check131.part33568 : Interval test 33568 33584 :=
  interval_of_check _ 33568 16 (by decide +kernel)
theorem Check131.part33584 : Interval test 33584 33600 :=
  interval_of_check _ 33584 16 (by decide +kernel)
theorem Check131.part33600 : Interval test 33600 33616 :=
  interval_of_check _ 33600 16 (by decide +kernel)
theorem Check131.part33616 : Interval test 33616 33632 :=
  interval_of_check _ 33616 16 (by decide +kernel)
theorem Check131.part33632 : Interval test 33632 33648 :=
  interval_of_check _ 33632 16 (by decide +kernel)
theorem Check131.part33648 : Interval test 33648 33664 :=
  interval_of_check _ 33648 16 (by decide +kernel)
theorem Check131.part33664 : Interval test 33664 33680 :=
  interval_of_check _ 33664 16 (by decide +kernel)
theorem Check131.part33680 : Interval test 33680 33696 :=
  interval_of_check _ 33680 16 (by decide +kernel)
theorem Check131.part33696 : Interval test 33696 33712 :=
  interval_of_check _ 33696 16 (by decide +kernel)
theorem Check131.part33712 : Interval test 33712 33728 :=
  interval_of_check _ 33712 16 (by decide +kernel)
theorem Check131.part33728 : Interval test 33728 33744 :=
  interval_of_check _ 33728 16 (by decide +kernel)
theorem Check131.part33744 : Interval test 33744 33760 :=
  interval_of_check _ 33744 16 (by decide +kernel)
theorem Check131.part33760 : Interval test 33760 33776 :=
  interval_of_check _ 33760 16 (by decide +kernel)
theorem Check131.part33776 : Interval test 33776 33792 :=
  interval_of_check _ 33776 16 (by decide +kernel)
theorem Check131.checked : Interval test 33536 33792 :=
  (FiniteChecks.interval_append test 33536 33664 33792
  (FiniteChecks.interval_append test 33536 33600 33664
  (FiniteChecks.interval_append test 33536 33568 33600
  (FiniteChecks.interval_append test 33536 33552 33568
  Check131.part33536
  Check131.part33552)
  (FiniteChecks.interval_append test 33568 33584 33600
  Check131.part33568
  Check131.part33584))
  (FiniteChecks.interval_append test 33600 33632 33664
  (FiniteChecks.interval_append test 33600 33616 33632
  Check131.part33600
  Check131.part33616)
  (FiniteChecks.interval_append test 33632 33648 33664
  Check131.part33632
  Check131.part33648)))
  (FiniteChecks.interval_append test 33664 33728 33792
  (FiniteChecks.interval_append test 33664 33696 33728
  (FiniteChecks.interval_append test 33664 33680 33696
  Check131.part33664
  Check131.part33680)
  (FiniteChecks.interval_append test 33696 33712 33728
  Check131.part33696
  Check131.part33712))
  (FiniteChecks.interval_append test 33728 33760 33792
  (FiniteChecks.interval_append test 33728 33744 33760
  Check131.part33728
  Check131.part33744)
  (FiniteChecks.interval_append test 33760 33776 33792
  Check131.part33760
  Check131.part33776))))
#print axioms Check131.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check132.part33792 : Interval test 33792 33808 :=
  interval_of_check _ 33792 16 (by decide +kernel)
theorem Check132.part33808 : Interval test 33808 33824 :=
  interval_of_check _ 33808 16 (by decide +kernel)
theorem Check132.part33824 : Interval test 33824 33840 :=
  interval_of_check _ 33824 16 (by decide +kernel)
theorem Check132.part33840 : Interval test 33840 33856 :=
  interval_of_check _ 33840 16 (by decide +kernel)
theorem Check132.part33856 : Interval test 33856 33872 :=
  interval_of_check _ 33856 16 (by decide +kernel)
theorem Check132.part33872 : Interval test 33872 33888 :=
  interval_of_check _ 33872 16 (by decide +kernel)
theorem Check132.part33888 : Interval test 33888 33904 :=
  interval_of_check _ 33888 16 (by decide +kernel)
theorem Check132.part33904 : Interval test 33904 33920 :=
  interval_of_check _ 33904 16 (by decide +kernel)
theorem Check132.part33920 : Interval test 33920 33936 :=
  interval_of_check _ 33920 16 (by decide +kernel)
theorem Check132.part33936 : Interval test 33936 33952 :=
  interval_of_check _ 33936 16 (by decide +kernel)
theorem Check132.part33952 : Interval test 33952 33968 :=
  interval_of_check _ 33952 16 (by decide +kernel)
theorem Check132.part33968 : Interval test 33968 33984 :=
  interval_of_check _ 33968 16 (by decide +kernel)
theorem Check132.part33984 : Interval test 33984 34000 :=
  interval_of_check _ 33984 16 (by decide +kernel)
theorem Check132.part34000 : Interval test 34000 34016 :=
  interval_of_check _ 34000 16 (by decide +kernel)
theorem Check132.part34016 : Interval test 34016 34032 :=
  interval_of_check _ 34016 16 (by decide +kernel)
theorem Check132.part34032 : Interval test 34032 34048 :=
  interval_of_check _ 34032 16 (by decide +kernel)
theorem Check132.checked : Interval test 33792 34048 :=
  (FiniteChecks.interval_append test 33792 33920 34048
  (FiniteChecks.interval_append test 33792 33856 33920
  (FiniteChecks.interval_append test 33792 33824 33856
  (FiniteChecks.interval_append test 33792 33808 33824
  Check132.part33792
  Check132.part33808)
  (FiniteChecks.interval_append test 33824 33840 33856
  Check132.part33824
  Check132.part33840))
  (FiniteChecks.interval_append test 33856 33888 33920
  (FiniteChecks.interval_append test 33856 33872 33888
  Check132.part33856
  Check132.part33872)
  (FiniteChecks.interval_append test 33888 33904 33920
  Check132.part33888
  Check132.part33904)))
  (FiniteChecks.interval_append test 33920 33984 34048
  (FiniteChecks.interval_append test 33920 33952 33984
  (FiniteChecks.interval_append test 33920 33936 33952
  Check132.part33920
  Check132.part33936)
  (FiniteChecks.interval_append test 33952 33968 33984
  Check132.part33952
  Check132.part33968))
  (FiniteChecks.interval_append test 33984 34016 34048
  (FiniteChecks.interval_append test 33984 34000 34016
  Check132.part33984
  Check132.part34000)
  (FiniteChecks.interval_append test 34016 34032 34048
  Check132.part34016
  Check132.part34032))))
#print axioms Check132.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check133.part34048 : Interval test 34048 34064 :=
  interval_of_check _ 34048 16 (by decide +kernel)
theorem Check133.part34064 : Interval test 34064 34080 :=
  interval_of_check _ 34064 16 (by decide +kernel)
theorem Check133.part34080 : Interval test 34080 34096 :=
  interval_of_check _ 34080 16 (by decide +kernel)
theorem Check133.part34096 : Interval test 34096 34112 :=
  interval_of_check _ 34096 16 (by decide +kernel)
theorem Check133.part34112 : Interval test 34112 34128 :=
  interval_of_check _ 34112 16 (by decide +kernel)
theorem Check133.part34128 : Interval test 34128 34144 :=
  interval_of_check _ 34128 16 (by decide +kernel)
theorem Check133.part34144 : Interval test 34144 34160 :=
  interval_of_check _ 34144 16 (by decide +kernel)
theorem Check133.part34160 : Interval test 34160 34176 :=
  interval_of_check _ 34160 16 (by decide +kernel)
theorem Check133.part34176 : Interval test 34176 34192 :=
  interval_of_check _ 34176 16 (by decide +kernel)
theorem Check133.part34192 : Interval test 34192 34208 :=
  interval_of_check _ 34192 16 (by decide +kernel)
theorem Check133.part34208 : Interval test 34208 34224 :=
  interval_of_check _ 34208 16 (by decide +kernel)
theorem Check133.part34224 : Interval test 34224 34240 :=
  interval_of_check _ 34224 16 (by decide +kernel)
theorem Check133.part34240 : Interval test 34240 34256 :=
  interval_of_check _ 34240 16 (by decide +kernel)
theorem Check133.part34256 : Interval test 34256 34272 :=
  interval_of_check _ 34256 16 (by decide +kernel)
theorem Check133.part34272 : Interval test 34272 34288 :=
  interval_of_check _ 34272 16 (by decide +kernel)
theorem Check133.part34288 : Interval test 34288 34304 :=
  interval_of_check _ 34288 16 (by decide +kernel)
theorem Check133.checked : Interval test 34048 34304 :=
  (FiniteChecks.interval_append test 34048 34176 34304
  (FiniteChecks.interval_append test 34048 34112 34176
  (FiniteChecks.interval_append test 34048 34080 34112
  (FiniteChecks.interval_append test 34048 34064 34080
  Check133.part34048
  Check133.part34064)
  (FiniteChecks.interval_append test 34080 34096 34112
  Check133.part34080
  Check133.part34096))
  (FiniteChecks.interval_append test 34112 34144 34176
  (FiniteChecks.interval_append test 34112 34128 34144
  Check133.part34112
  Check133.part34128)
  (FiniteChecks.interval_append test 34144 34160 34176
  Check133.part34144
  Check133.part34160)))
  (FiniteChecks.interval_append test 34176 34240 34304
  (FiniteChecks.interval_append test 34176 34208 34240
  (FiniteChecks.interval_append test 34176 34192 34208
  Check133.part34176
  Check133.part34192)
  (FiniteChecks.interval_append test 34208 34224 34240
  Check133.part34208
  Check133.part34224))
  (FiniteChecks.interval_append test 34240 34272 34304
  (FiniteChecks.interval_append test 34240 34256 34272
  Check133.part34240
  Check133.part34256)
  (FiniteChecks.interval_append test 34272 34288 34304
  Check133.part34272
  Check133.part34288))))
#print axioms Check133.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check134.part34304 : Interval test 34304 34320 :=
  interval_of_check _ 34304 16 (by decide +kernel)
theorem Check134.part34320 : Interval test 34320 34336 :=
  interval_of_check _ 34320 16 (by decide +kernel)
theorem Check134.part34336 : Interval test 34336 34352 :=
  interval_of_check _ 34336 16 (by decide +kernel)
theorem Check134.part34352 : Interval test 34352 34368 :=
  interval_of_check _ 34352 16 (by decide +kernel)
theorem Check134.part34368 : Interval test 34368 34384 :=
  interval_of_check _ 34368 16 (by decide +kernel)
theorem Check134.part34384 : Interval test 34384 34400 :=
  interval_of_check _ 34384 16 (by decide +kernel)
theorem Check134.part34400 : Interval test 34400 34416 :=
  interval_of_check _ 34400 16 (by decide +kernel)
theorem Check134.part34416 : Interval test 34416 34432 :=
  interval_of_check _ 34416 16 (by decide +kernel)
theorem Check134.part34432 : Interval test 34432 34448 :=
  interval_of_check _ 34432 16 (by decide +kernel)
theorem Check134.part34448 : Interval test 34448 34464 :=
  interval_of_check _ 34448 16 (by decide +kernel)
theorem Check134.part34464 : Interval test 34464 34480 :=
  interval_of_check _ 34464 16 (by decide +kernel)
theorem Check134.part34480 : Interval test 34480 34496 :=
  interval_of_check _ 34480 16 (by decide +kernel)
theorem Check134.part34496 : Interval test 34496 34512 :=
  interval_of_check _ 34496 16 (by decide +kernel)
theorem Check134.part34512 : Interval test 34512 34528 :=
  interval_of_check _ 34512 16 (by decide +kernel)
theorem Check134.part34528 : Interval test 34528 34544 :=
  interval_of_check _ 34528 16 (by decide +kernel)
theorem Check134.part34544 : Interval test 34544 34560 :=
  interval_of_check _ 34544 16 (by decide +kernel)
theorem Check134.checked : Interval test 34304 34560 :=
  (FiniteChecks.interval_append test 34304 34432 34560
  (FiniteChecks.interval_append test 34304 34368 34432
  (FiniteChecks.interval_append test 34304 34336 34368
  (FiniteChecks.interval_append test 34304 34320 34336
  Check134.part34304
  Check134.part34320)
  (FiniteChecks.interval_append test 34336 34352 34368
  Check134.part34336
  Check134.part34352))
  (FiniteChecks.interval_append test 34368 34400 34432
  (FiniteChecks.interval_append test 34368 34384 34400
  Check134.part34368
  Check134.part34384)
  (FiniteChecks.interval_append test 34400 34416 34432
  Check134.part34400
  Check134.part34416)))
  (FiniteChecks.interval_append test 34432 34496 34560
  (FiniteChecks.interval_append test 34432 34464 34496
  (FiniteChecks.interval_append test 34432 34448 34464
  Check134.part34432
  Check134.part34448)
  (FiniteChecks.interval_append test 34464 34480 34496
  Check134.part34464
  Check134.part34480))
  (FiniteChecks.interval_append test 34496 34528 34560
  (FiniteChecks.interval_append test 34496 34512 34528
  Check134.part34496
  Check134.part34512)
  (FiniteChecks.interval_append test 34528 34544 34560
  Check134.part34528
  Check134.part34544))))
#print axioms Check134.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check135.part34560 : Interval test 34560 34576 :=
  interval_of_check _ 34560 16 (by decide +kernel)
theorem Check135.part34576 : Interval test 34576 34592 :=
  interval_of_check _ 34576 16 (by decide +kernel)
theorem Check135.part34592 : Interval test 34592 34608 :=
  interval_of_check _ 34592 16 (by decide +kernel)
theorem Check135.part34608 : Interval test 34608 34624 :=
  interval_of_check _ 34608 16 (by decide +kernel)
theorem Check135.part34624 : Interval test 34624 34640 :=
  interval_of_check _ 34624 16 (by decide +kernel)
theorem Check135.part34640 : Interval test 34640 34656 :=
  interval_of_check _ 34640 16 (by decide +kernel)
theorem Check135.part34656 : Interval test 34656 34672 :=
  interval_of_check _ 34656 16 (by decide +kernel)
theorem Check135.part34672 : Interval test 34672 34688 :=
  interval_of_check _ 34672 16 (by decide +kernel)
theorem Check135.part34688 : Interval test 34688 34704 :=
  interval_of_check _ 34688 16 (by decide +kernel)
theorem Check135.part34704 : Interval test 34704 34720 :=
  interval_of_check _ 34704 16 (by decide +kernel)
theorem Check135.part34720 : Interval test 34720 34736 :=
  interval_of_check _ 34720 16 (by decide +kernel)
theorem Check135.part34736 : Interval test 34736 34752 :=
  interval_of_check _ 34736 16 (by decide +kernel)
theorem Check135.part34752 : Interval test 34752 34768 :=
  interval_of_check _ 34752 16 (by decide +kernel)
theorem Check135.part34768 : Interval test 34768 34784 :=
  interval_of_check _ 34768 16 (by decide +kernel)
theorem Check135.part34784 : Interval test 34784 34800 :=
  interval_of_check _ 34784 16 (by decide +kernel)
theorem Check135.part34800 : Interval test 34800 34816 :=
  interval_of_check _ 34800 16 (by decide +kernel)
theorem Check135.checked : Interval test 34560 34816 :=
  (FiniteChecks.interval_append test 34560 34688 34816
  (FiniteChecks.interval_append test 34560 34624 34688
  (FiniteChecks.interval_append test 34560 34592 34624
  (FiniteChecks.interval_append test 34560 34576 34592
  Check135.part34560
  Check135.part34576)
  (FiniteChecks.interval_append test 34592 34608 34624
  Check135.part34592
  Check135.part34608))
  (FiniteChecks.interval_append test 34624 34656 34688
  (FiniteChecks.interval_append test 34624 34640 34656
  Check135.part34624
  Check135.part34640)
  (FiniteChecks.interval_append test 34656 34672 34688
  Check135.part34656
  Check135.part34672)))
  (FiniteChecks.interval_append test 34688 34752 34816
  (FiniteChecks.interval_append test 34688 34720 34752
  (FiniteChecks.interval_append test 34688 34704 34720
  Check135.part34688
  Check135.part34704)
  (FiniteChecks.interval_append test 34720 34736 34752
  Check135.part34720
  Check135.part34736))
  (FiniteChecks.interval_append test 34752 34784 34816
  (FiniteChecks.interval_append test 34752 34768 34784
  Check135.part34752
  Check135.part34768)
  (FiniteChecks.interval_append test 34784 34800 34816
  Check135.part34784
  Check135.part34800))))
#print axioms Check135.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check136.part34816 : Interval test 34816 34832 :=
  interval_of_check _ 34816 16 (by decide +kernel)
theorem Check136.part34832 : Interval test 34832 34848 :=
  interval_of_check _ 34832 16 (by decide +kernel)
theorem Check136.part34848 : Interval test 34848 34864 :=
  interval_of_check _ 34848 16 (by decide +kernel)
theorem Check136.part34864 : Interval test 34864 34880 :=
  interval_of_check _ 34864 16 (by decide +kernel)
theorem Check136.part34880 : Interval test 34880 34896 :=
  interval_of_check _ 34880 16 (by decide +kernel)
theorem Check136.part34896 : Interval test 34896 34912 :=
  interval_of_check _ 34896 16 (by decide +kernel)
theorem Check136.part34912 : Interval test 34912 34928 :=
  interval_of_check _ 34912 16 (by decide +kernel)
theorem Check136.part34928 : Interval test 34928 34944 :=
  interval_of_check _ 34928 16 (by decide +kernel)
theorem Check136.part34944 : Interval test 34944 34960 :=
  interval_of_check _ 34944 16 (by decide +kernel)
theorem Check136.part34960 : Interval test 34960 34976 :=
  interval_of_check _ 34960 16 (by decide +kernel)
theorem Check136.part34976 : Interval test 34976 34992 :=
  interval_of_check _ 34976 16 (by decide +kernel)
theorem Check136.part34992 : Interval test 34992 35008 :=
  interval_of_check _ 34992 16 (by decide +kernel)
theorem Check136.part35008 : Interval test 35008 35024 :=
  interval_of_check _ 35008 16 (by decide +kernel)
theorem Check136.part35024 : Interval test 35024 35040 :=
  interval_of_check _ 35024 16 (by decide +kernel)
theorem Check136.part35040 : Interval test 35040 35056 :=
  interval_of_check _ 35040 16 (by decide +kernel)
theorem Check136.part35056 : Interval test 35056 35072 :=
  interval_of_check _ 35056 16 (by decide +kernel)
theorem Check136.checked : Interval test 34816 35072 :=
  (FiniteChecks.interval_append test 34816 34944 35072
  (FiniteChecks.interval_append test 34816 34880 34944
  (FiniteChecks.interval_append test 34816 34848 34880
  (FiniteChecks.interval_append test 34816 34832 34848
  Check136.part34816
  Check136.part34832)
  (FiniteChecks.interval_append test 34848 34864 34880
  Check136.part34848
  Check136.part34864))
  (FiniteChecks.interval_append test 34880 34912 34944
  (FiniteChecks.interval_append test 34880 34896 34912
  Check136.part34880
  Check136.part34896)
  (FiniteChecks.interval_append test 34912 34928 34944
  Check136.part34912
  Check136.part34928)))
  (FiniteChecks.interval_append test 34944 35008 35072
  (FiniteChecks.interval_append test 34944 34976 35008
  (FiniteChecks.interval_append test 34944 34960 34976
  Check136.part34944
  Check136.part34960)
  (FiniteChecks.interval_append test 34976 34992 35008
  Check136.part34976
  Check136.part34992))
  (FiniteChecks.interval_append test 35008 35040 35072
  (FiniteChecks.interval_append test 35008 35024 35040
  Check136.part35008
  Check136.part35024)
  (FiniteChecks.interval_append test 35040 35056 35072
  Check136.part35040
  Check136.part35056))))
#print axioms Check136.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check137.part35072 : Interval test 35072 35088 :=
  interval_of_check _ 35072 16 (by decide +kernel)
theorem Check137.part35088 : Interval test 35088 35104 :=
  interval_of_check _ 35088 16 (by decide +kernel)
theorem Check137.part35104 : Interval test 35104 35120 :=
  interval_of_check _ 35104 16 (by decide +kernel)
theorem Check137.part35120 : Interval test 35120 35136 :=
  interval_of_check _ 35120 16 (by decide +kernel)
theorem Check137.part35136 : Interval test 35136 35152 :=
  interval_of_check _ 35136 16 (by decide +kernel)
theorem Check137.part35152 : Interval test 35152 35168 :=
  interval_of_check _ 35152 16 (by decide +kernel)
theorem Check137.part35168 : Interval test 35168 35184 :=
  interval_of_check _ 35168 16 (by decide +kernel)
theorem Check137.part35184 : Interval test 35184 35200 :=
  interval_of_check _ 35184 16 (by decide +kernel)
theorem Check137.part35200 : Interval test 35200 35216 :=
  interval_of_check _ 35200 16 (by decide +kernel)
theorem Check137.part35216 : Interval test 35216 35232 :=
  interval_of_check _ 35216 16 (by decide +kernel)
theorem Check137.part35232 : Interval test 35232 35248 :=
  interval_of_check _ 35232 16 (by decide +kernel)
theorem Check137.part35248 : Interval test 35248 35264 :=
  interval_of_check _ 35248 16 (by decide +kernel)
theorem Check137.part35264 : Interval test 35264 35280 :=
  interval_of_check _ 35264 16 (by decide +kernel)
theorem Check137.part35280 : Interval test 35280 35296 :=
  interval_of_check _ 35280 16 (by decide +kernel)
theorem Check137.part35296 : Interval test 35296 35312 :=
  interval_of_check _ 35296 16 (by decide +kernel)
theorem Check137.part35312 : Interval test 35312 35328 :=
  interval_of_check _ 35312 16 (by decide +kernel)
theorem Check137.checked : Interval test 35072 35328 :=
  (FiniteChecks.interval_append test 35072 35200 35328
  (FiniteChecks.interval_append test 35072 35136 35200
  (FiniteChecks.interval_append test 35072 35104 35136
  (FiniteChecks.interval_append test 35072 35088 35104
  Check137.part35072
  Check137.part35088)
  (FiniteChecks.interval_append test 35104 35120 35136
  Check137.part35104
  Check137.part35120))
  (FiniteChecks.interval_append test 35136 35168 35200
  (FiniteChecks.interval_append test 35136 35152 35168
  Check137.part35136
  Check137.part35152)
  (FiniteChecks.interval_append test 35168 35184 35200
  Check137.part35168
  Check137.part35184)))
  (FiniteChecks.interval_append test 35200 35264 35328
  (FiniteChecks.interval_append test 35200 35232 35264
  (FiniteChecks.interval_append test 35200 35216 35232
  Check137.part35200
  Check137.part35216)
  (FiniteChecks.interval_append test 35232 35248 35264
  Check137.part35232
  Check137.part35248))
  (FiniteChecks.interval_append test 35264 35296 35328
  (FiniteChecks.interval_append test 35264 35280 35296
  Check137.part35264
  Check137.part35280)
  (FiniteChecks.interval_append test 35296 35312 35328
  Check137.part35296
  Check137.part35312))))
#print axioms Check137.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check138.part35328 : Interval test 35328 35344 :=
  interval_of_check _ 35328 16 (by decide +kernel)
theorem Check138.part35344 : Interval test 35344 35360 :=
  interval_of_check _ 35344 16 (by decide +kernel)
theorem Check138.part35360 : Interval test 35360 35376 :=
  interval_of_check _ 35360 16 (by decide +kernel)
theorem Check138.part35376 : Interval test 35376 35392 :=
  interval_of_check _ 35376 16 (by decide +kernel)
theorem Check138.part35392 : Interval test 35392 35408 :=
  interval_of_check _ 35392 16 (by decide +kernel)
theorem Check138.part35408 : Interval test 35408 35424 :=
  interval_of_check _ 35408 16 (by decide +kernel)
theorem Check138.part35424 : Interval test 35424 35440 :=
  interval_of_check _ 35424 16 (by decide +kernel)
theorem Check138.part35440 : Interval test 35440 35456 :=
  interval_of_check _ 35440 16 (by decide +kernel)
theorem Check138.part35456 : Interval test 35456 35472 :=
  interval_of_check _ 35456 16 (by decide +kernel)
theorem Check138.part35472 : Interval test 35472 35488 :=
  interval_of_check _ 35472 16 (by decide +kernel)
theorem Check138.part35488 : Interval test 35488 35504 :=
  interval_of_check _ 35488 16 (by decide +kernel)
theorem Check138.part35504 : Interval test 35504 35520 :=
  interval_of_check _ 35504 16 (by decide +kernel)
theorem Check138.part35520 : Interval test 35520 35536 :=
  interval_of_check _ 35520 16 (by decide +kernel)
theorem Check138.part35536 : Interval test 35536 35552 :=
  interval_of_check _ 35536 16 (by decide +kernel)
theorem Check138.part35552 : Interval test 35552 35568 :=
  interval_of_check _ 35552 16 (by decide +kernel)
theorem Check138.part35568 : Interval test 35568 35584 :=
  interval_of_check _ 35568 16 (by decide +kernel)
theorem Check138.checked : Interval test 35328 35584 :=
  (FiniteChecks.interval_append test 35328 35456 35584
  (FiniteChecks.interval_append test 35328 35392 35456
  (FiniteChecks.interval_append test 35328 35360 35392
  (FiniteChecks.interval_append test 35328 35344 35360
  Check138.part35328
  Check138.part35344)
  (FiniteChecks.interval_append test 35360 35376 35392
  Check138.part35360
  Check138.part35376))
  (FiniteChecks.interval_append test 35392 35424 35456
  (FiniteChecks.interval_append test 35392 35408 35424
  Check138.part35392
  Check138.part35408)
  (FiniteChecks.interval_append test 35424 35440 35456
  Check138.part35424
  Check138.part35440)))
  (FiniteChecks.interval_append test 35456 35520 35584
  (FiniteChecks.interval_append test 35456 35488 35520
  (FiniteChecks.interval_append test 35456 35472 35488
  Check138.part35456
  Check138.part35472)
  (FiniteChecks.interval_append test 35488 35504 35520
  Check138.part35488
  Check138.part35504))
  (FiniteChecks.interval_append test 35520 35552 35584
  (FiniteChecks.interval_append test 35520 35536 35552
  Check138.part35520
  Check138.part35536)
  (FiniteChecks.interval_append test 35552 35568 35584
  Check138.part35552
  Check138.part35568))))
#print axioms Check138.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check139.part35584 : Interval test 35584 35600 :=
  interval_of_check _ 35584 16 (by decide +kernel)
theorem Check139.part35600 : Interval test 35600 35616 :=
  interval_of_check _ 35600 16 (by decide +kernel)
theorem Check139.part35616 : Interval test 35616 35632 :=
  interval_of_check _ 35616 16 (by decide +kernel)
theorem Check139.part35632 : Interval test 35632 35648 :=
  interval_of_check _ 35632 16 (by decide +kernel)
theorem Check139.part35648 : Interval test 35648 35664 :=
  interval_of_check _ 35648 16 (by decide +kernel)
theorem Check139.part35664 : Interval test 35664 35680 :=
  interval_of_check _ 35664 16 (by decide +kernel)
theorem Check139.part35680 : Interval test 35680 35696 :=
  interval_of_check _ 35680 16 (by decide +kernel)
theorem Check139.part35696 : Interval test 35696 35712 :=
  interval_of_check _ 35696 16 (by decide +kernel)
theorem Check139.part35712 : Interval test 35712 35728 :=
  interval_of_check _ 35712 16 (by decide +kernel)
theorem Check139.part35728 : Interval test 35728 35744 :=
  interval_of_check _ 35728 16 (by decide +kernel)
theorem Check139.part35744 : Interval test 35744 35760 :=
  interval_of_check _ 35744 16 (by decide +kernel)
theorem Check139.part35760 : Interval test 35760 35776 :=
  interval_of_check _ 35760 16 (by decide +kernel)
theorem Check139.part35776 : Interval test 35776 35792 :=
  interval_of_check _ 35776 16 (by decide +kernel)
theorem Check139.part35792 : Interval test 35792 35808 :=
  interval_of_check _ 35792 16 (by decide +kernel)
theorem Check139.part35808 : Interval test 35808 35824 :=
  interval_of_check _ 35808 16 (by decide +kernel)
theorem Check139.part35824 : Interval test 35824 35840 :=
  interval_of_check _ 35824 16 (by decide +kernel)
theorem Check139.checked : Interval test 35584 35840 :=
  (FiniteChecks.interval_append test 35584 35712 35840
  (FiniteChecks.interval_append test 35584 35648 35712
  (FiniteChecks.interval_append test 35584 35616 35648
  (FiniteChecks.interval_append test 35584 35600 35616
  Check139.part35584
  Check139.part35600)
  (FiniteChecks.interval_append test 35616 35632 35648
  Check139.part35616
  Check139.part35632))
  (FiniteChecks.interval_append test 35648 35680 35712
  (FiniteChecks.interval_append test 35648 35664 35680
  Check139.part35648
  Check139.part35664)
  (FiniteChecks.interval_append test 35680 35696 35712
  Check139.part35680
  Check139.part35696)))
  (FiniteChecks.interval_append test 35712 35776 35840
  (FiniteChecks.interval_append test 35712 35744 35776
  (FiniteChecks.interval_append test 35712 35728 35744
  Check139.part35712
  Check139.part35728)
  (FiniteChecks.interval_append test 35744 35760 35776
  Check139.part35744
  Check139.part35760))
  (FiniteChecks.interval_append test 35776 35808 35840
  (FiniteChecks.interval_append test 35776 35792 35808
  Check139.part35776
  Check139.part35792)
  (FiniteChecks.interval_append test 35808 35824 35840
  Check139.part35808
  Check139.part35824))))
#print axioms Check139.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
