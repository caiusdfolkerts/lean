module
prelude
public import SharedSix0CellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check320.part40960 : Interval test 40960 40976 :=
  interval_of_check _ 40960 16 (by decide +kernel)
theorem Check320.part40976 : Interval test 40976 40992 :=
  interval_of_check _ 40976 16 (by decide +kernel)
theorem Check320.part40992 : Interval test 40992 41008 :=
  interval_of_check _ 40992 16 (by decide +kernel)
theorem Check320.part41008 : Interval test 41008 41024 :=
  interval_of_check _ 41008 16 (by decide +kernel)
theorem Check320.part41024 : Interval test 41024 41040 :=
  interval_of_check _ 41024 16 (by decide +kernel)
theorem Check320.part41040 : Interval test 41040 41056 :=
  interval_of_check _ 41040 16 (by decide +kernel)
theorem Check320.part41056 : Interval test 41056 41072 :=
  interval_of_check _ 41056 16 (by decide +kernel)
theorem Check320.part41072 : Interval test 41072 41088 :=
  interval_of_check _ 41072 16 (by decide +kernel)
theorem Check320.checked : Interval test 40960 41088 :=
  (FiniteChecks.interval_append test 40960 41024 41088
  (FiniteChecks.interval_append test 40960 40992 41024
  (FiniteChecks.interval_append test 40960 40976 40992
  Check320.part40960
  Check320.part40976)
  (FiniteChecks.interval_append test 40992 41008 41024
  Check320.part40992
  Check320.part41008))
  (FiniteChecks.interval_append test 41024 41056 41088
  (FiniteChecks.interval_append test 41024 41040 41056
  Check320.part41024
  Check320.part41040)
  (FiniteChecks.interval_append test 41056 41072 41088
  Check320.part41056
  Check320.part41072)))
#print axioms Check320.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check321.part41088 : Interval test 41088 41104 :=
  interval_of_check _ 41088 16 (by decide +kernel)
theorem Check321.part41104 : Interval test 41104 41120 :=
  interval_of_check _ 41104 16 (by decide +kernel)
theorem Check321.part41120 : Interval test 41120 41136 :=
  interval_of_check _ 41120 16 (by decide +kernel)
theorem Check321.part41136 : Interval test 41136 41152 :=
  interval_of_check _ 41136 16 (by decide +kernel)
theorem Check321.part41152 : Interval test 41152 41168 :=
  interval_of_check _ 41152 16 (by decide +kernel)
theorem Check321.part41168 : Interval test 41168 41184 :=
  interval_of_check _ 41168 16 (by decide +kernel)
theorem Check321.part41184 : Interval test 41184 41200 :=
  interval_of_check _ 41184 16 (by decide +kernel)
theorem Check321.part41200 : Interval test 41200 41216 :=
  interval_of_check _ 41200 16 (by decide +kernel)
theorem Check321.checked : Interval test 41088 41216 :=
  (FiniteChecks.interval_append test 41088 41152 41216
  (FiniteChecks.interval_append test 41088 41120 41152
  (FiniteChecks.interval_append test 41088 41104 41120
  Check321.part41088
  Check321.part41104)
  (FiniteChecks.interval_append test 41120 41136 41152
  Check321.part41120
  Check321.part41136))
  (FiniteChecks.interval_append test 41152 41184 41216
  (FiniteChecks.interval_append test 41152 41168 41184
  Check321.part41152
  Check321.part41168)
  (FiniteChecks.interval_append test 41184 41200 41216
  Check321.part41184
  Check321.part41200)))
#print axioms Check321.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check322.part41216 : Interval test 41216 41232 :=
  interval_of_check _ 41216 16 (by decide +kernel)
theorem Check322.part41232 : Interval test 41232 41248 :=
  interval_of_check _ 41232 16 (by decide +kernel)
theorem Check322.part41248 : Interval test 41248 41264 :=
  interval_of_check _ 41248 16 (by decide +kernel)
theorem Check322.part41264 : Interval test 41264 41280 :=
  interval_of_check _ 41264 16 (by decide +kernel)
theorem Check322.part41280 : Interval test 41280 41296 :=
  interval_of_check _ 41280 16 (by decide +kernel)
theorem Check322.part41296 : Interval test 41296 41312 :=
  interval_of_check _ 41296 16 (by decide +kernel)
theorem Check322.part41312 : Interval test 41312 41328 :=
  interval_of_check _ 41312 16 (by decide +kernel)
theorem Check322.part41328 : Interval test 41328 41344 :=
  interval_of_check _ 41328 16 (by decide +kernel)
theorem Check322.checked : Interval test 41216 41344 :=
  (FiniteChecks.interval_append test 41216 41280 41344
  (FiniteChecks.interval_append test 41216 41248 41280
  (FiniteChecks.interval_append test 41216 41232 41248
  Check322.part41216
  Check322.part41232)
  (FiniteChecks.interval_append test 41248 41264 41280
  Check322.part41248
  Check322.part41264))
  (FiniteChecks.interval_append test 41280 41312 41344
  (FiniteChecks.interval_append test 41280 41296 41312
  Check322.part41280
  Check322.part41296)
  (FiniteChecks.interval_append test 41312 41328 41344
  Check322.part41312
  Check322.part41328)))
#print axioms Check322.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check323.part41344 : Interval test 41344 41360 :=
  interval_of_check _ 41344 16 (by decide +kernel)
theorem Check323.part41360 : Interval test 41360 41376 :=
  interval_of_check _ 41360 16 (by decide +kernel)
theorem Check323.part41376 : Interval test 41376 41392 :=
  interval_of_check _ 41376 16 (by decide +kernel)
theorem Check323.part41392 : Interval test 41392 41408 :=
  interval_of_check _ 41392 16 (by decide +kernel)
theorem Check323.part41408 : Interval test 41408 41424 :=
  interval_of_check _ 41408 16 (by decide +kernel)
theorem Check323.part41424 : Interval test 41424 41440 :=
  interval_of_check _ 41424 16 (by decide +kernel)
theorem Check323.part41440 : Interval test 41440 41456 :=
  interval_of_check _ 41440 16 (by decide +kernel)
theorem Check323.part41456 : Interval test 41456 41472 :=
  interval_of_check _ 41456 16 (by decide +kernel)
theorem Check323.checked : Interval test 41344 41472 :=
  (FiniteChecks.interval_append test 41344 41408 41472
  (FiniteChecks.interval_append test 41344 41376 41408
  (FiniteChecks.interval_append test 41344 41360 41376
  Check323.part41344
  Check323.part41360)
  (FiniteChecks.interval_append test 41376 41392 41408
  Check323.part41376
  Check323.part41392))
  (FiniteChecks.interval_append test 41408 41440 41472
  (FiniteChecks.interval_append test 41408 41424 41440
  Check323.part41408
  Check323.part41424)
  (FiniteChecks.interval_append test 41440 41456 41472
  Check323.part41440
  Check323.part41456)))
#print axioms Check323.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check324.part41472 : Interval test 41472 41488 :=
  interval_of_check _ 41472 16 (by decide +kernel)
theorem Check324.part41488 : Interval test 41488 41504 :=
  interval_of_check _ 41488 16 (by decide +kernel)
theorem Check324.part41504 : Interval test 41504 41520 :=
  interval_of_check _ 41504 16 (by decide +kernel)
theorem Check324.part41520 : Interval test 41520 41536 :=
  interval_of_check _ 41520 16 (by decide +kernel)
theorem Check324.part41536 : Interval test 41536 41552 :=
  interval_of_check _ 41536 16 (by decide +kernel)
theorem Check324.part41552 : Interval test 41552 41568 :=
  interval_of_check _ 41552 16 (by decide +kernel)
theorem Check324.part41568 : Interval test 41568 41584 :=
  interval_of_check _ 41568 16 (by decide +kernel)
theorem Check324.part41584 : Interval test 41584 41600 :=
  interval_of_check _ 41584 16 (by decide +kernel)
theorem Check324.checked : Interval test 41472 41600 :=
  (FiniteChecks.interval_append test 41472 41536 41600
  (FiniteChecks.interval_append test 41472 41504 41536
  (FiniteChecks.interval_append test 41472 41488 41504
  Check324.part41472
  Check324.part41488)
  (FiniteChecks.interval_append test 41504 41520 41536
  Check324.part41504
  Check324.part41520))
  (FiniteChecks.interval_append test 41536 41568 41600
  (FiniteChecks.interval_append test 41536 41552 41568
  Check324.part41536
  Check324.part41552)
  (FiniteChecks.interval_append test 41568 41584 41600
  Check324.part41568
  Check324.part41584)))
#print axioms Check324.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check325.part41600 : Interval test 41600 41616 :=
  interval_of_check _ 41600 16 (by decide +kernel)
theorem Check325.part41616 : Interval test 41616 41632 :=
  interval_of_check _ 41616 16 (by decide +kernel)
theorem Check325.part41632 : Interval test 41632 41648 :=
  interval_of_check _ 41632 16 (by decide +kernel)
theorem Check325.part41648 : Interval test 41648 41664 :=
  interval_of_check _ 41648 16 (by decide +kernel)
theorem Check325.part41664 : Interval test 41664 41680 :=
  interval_of_check _ 41664 16 (by decide +kernel)
theorem Check325.part41680 : Interval test 41680 41696 :=
  interval_of_check _ 41680 16 (by decide +kernel)
theorem Check325.part41696 : Interval test 41696 41712 :=
  interval_of_check _ 41696 16 (by decide +kernel)
theorem Check325.part41712 : Interval test 41712 41728 :=
  interval_of_check _ 41712 16 (by decide +kernel)
theorem Check325.checked : Interval test 41600 41728 :=
  (FiniteChecks.interval_append test 41600 41664 41728
  (FiniteChecks.interval_append test 41600 41632 41664
  (FiniteChecks.interval_append test 41600 41616 41632
  Check325.part41600
  Check325.part41616)
  (FiniteChecks.interval_append test 41632 41648 41664
  Check325.part41632
  Check325.part41648))
  (FiniteChecks.interval_append test 41664 41696 41728
  (FiniteChecks.interval_append test 41664 41680 41696
  Check325.part41664
  Check325.part41680)
  (FiniteChecks.interval_append test 41696 41712 41728
  Check325.part41696
  Check325.part41712)))
#print axioms Check325.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check326.part41728 : Interval test 41728 41744 :=
  interval_of_check _ 41728 16 (by decide +kernel)
theorem Check326.part41744 : Interval test 41744 41760 :=
  interval_of_check _ 41744 16 (by decide +kernel)
theorem Check326.part41760 : Interval test 41760 41776 :=
  interval_of_check _ 41760 16 (by decide +kernel)
theorem Check326.part41776 : Interval test 41776 41792 :=
  interval_of_check _ 41776 16 (by decide +kernel)
theorem Check326.part41792 : Interval test 41792 41808 :=
  interval_of_check _ 41792 16 (by decide +kernel)
theorem Check326.part41808 : Interval test 41808 41824 :=
  interval_of_check _ 41808 16 (by decide +kernel)
theorem Check326.part41824 : Interval test 41824 41840 :=
  interval_of_check _ 41824 16 (by decide +kernel)
theorem Check326.part41840 : Interval test 41840 41856 :=
  interval_of_check _ 41840 16 (by decide +kernel)
theorem Check326.checked : Interval test 41728 41856 :=
  (FiniteChecks.interval_append test 41728 41792 41856
  (FiniteChecks.interval_append test 41728 41760 41792
  (FiniteChecks.interval_append test 41728 41744 41760
  Check326.part41728
  Check326.part41744)
  (FiniteChecks.interval_append test 41760 41776 41792
  Check326.part41760
  Check326.part41776))
  (FiniteChecks.interval_append test 41792 41824 41856
  (FiniteChecks.interval_append test 41792 41808 41824
  Check326.part41792
  Check326.part41808)
  (FiniteChecks.interval_append test 41824 41840 41856
  Check326.part41824
  Check326.part41840)))
#print axioms Check326.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check327.part41856 : Interval test 41856 41872 :=
  interval_of_check _ 41856 16 (by decide +kernel)
theorem Check327.part41872 : Interval test 41872 41888 :=
  interval_of_check _ 41872 16 (by decide +kernel)
theorem Check327.part41888 : Interval test 41888 41904 :=
  interval_of_check _ 41888 16 (by decide +kernel)
theorem Check327.part41904 : Interval test 41904 41920 :=
  interval_of_check _ 41904 16 (by decide +kernel)
theorem Check327.part41920 : Interval test 41920 41936 :=
  interval_of_check _ 41920 16 (by decide +kernel)
theorem Check327.part41936 : Interval test 41936 41952 :=
  interval_of_check _ 41936 16 (by decide +kernel)
theorem Check327.part41952 : Interval test 41952 41968 :=
  interval_of_check _ 41952 16 (by decide +kernel)
theorem Check327.part41968 : Interval test 41968 41984 :=
  interval_of_check _ 41968 16 (by decide +kernel)
theorem Check327.checked : Interval test 41856 41984 :=
  (FiniteChecks.interval_append test 41856 41920 41984
  (FiniteChecks.interval_append test 41856 41888 41920
  (FiniteChecks.interval_append test 41856 41872 41888
  Check327.part41856
  Check327.part41872)
  (FiniteChecks.interval_append test 41888 41904 41920
  Check327.part41888
  Check327.part41904))
  (FiniteChecks.interval_append test 41920 41952 41984
  (FiniteChecks.interval_append test 41920 41936 41952
  Check327.part41920
  Check327.part41936)
  (FiniteChecks.interval_append test 41952 41968 41984
  Check327.part41952
  Check327.part41968)))
#print axioms Check327.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check328.part41984 : Interval test 41984 42000 :=
  interval_of_check _ 41984 16 (by decide +kernel)
theorem Check328.part42000 : Interval test 42000 42016 :=
  interval_of_check _ 42000 16 (by decide +kernel)
theorem Check328.part42016 : Interval test 42016 42032 :=
  interval_of_check _ 42016 16 (by decide +kernel)
theorem Check328.part42032 : Interval test 42032 42048 :=
  interval_of_check _ 42032 16 (by decide +kernel)
theorem Check328.part42048 : Interval test 42048 42064 :=
  interval_of_check _ 42048 16 (by decide +kernel)
theorem Check328.part42064 : Interval test 42064 42080 :=
  interval_of_check _ 42064 16 (by decide +kernel)
theorem Check328.part42080 : Interval test 42080 42096 :=
  interval_of_check _ 42080 16 (by decide +kernel)
theorem Check328.part42096 : Interval test 42096 42112 :=
  interval_of_check _ 42096 16 (by decide +kernel)
theorem Check328.checked : Interval test 41984 42112 :=
  (FiniteChecks.interval_append test 41984 42048 42112
  (FiniteChecks.interval_append test 41984 42016 42048
  (FiniteChecks.interval_append test 41984 42000 42016
  Check328.part41984
  Check328.part42000)
  (FiniteChecks.interval_append test 42016 42032 42048
  Check328.part42016
  Check328.part42032))
  (FiniteChecks.interval_append test 42048 42080 42112
  (FiniteChecks.interval_append test 42048 42064 42080
  Check328.part42048
  Check328.part42064)
  (FiniteChecks.interval_append test 42080 42096 42112
  Check328.part42080
  Check328.part42096)))
#print axioms Check328.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check329.part42112 : Interval test 42112 42128 :=
  interval_of_check _ 42112 16 (by decide +kernel)
theorem Check329.part42128 : Interval test 42128 42144 :=
  interval_of_check _ 42128 16 (by decide +kernel)
theorem Check329.part42144 : Interval test 42144 42160 :=
  interval_of_check _ 42144 16 (by decide +kernel)
theorem Check329.part42160 : Interval test 42160 42176 :=
  interval_of_check _ 42160 16 (by decide +kernel)
theorem Check329.part42176 : Interval test 42176 42192 :=
  interval_of_check _ 42176 16 (by decide +kernel)
theorem Check329.part42192 : Interval test 42192 42208 :=
  interval_of_check _ 42192 16 (by decide +kernel)
theorem Check329.part42208 : Interval test 42208 42224 :=
  interval_of_check _ 42208 16 (by decide +kernel)
theorem Check329.part42224 : Interval test 42224 42240 :=
  interval_of_check _ 42224 16 (by decide +kernel)
theorem Check329.checked : Interval test 42112 42240 :=
  (FiniteChecks.interval_append test 42112 42176 42240
  (FiniteChecks.interval_append test 42112 42144 42176
  (FiniteChecks.interval_append test 42112 42128 42144
  Check329.part42112
  Check329.part42128)
  (FiniteChecks.interval_append test 42144 42160 42176
  Check329.part42144
  Check329.part42160))
  (FiniteChecks.interval_append test 42176 42208 42240
  (FiniteChecks.interval_append test 42176 42192 42208
  Check329.part42176
  Check329.part42192)
  (FiniteChecks.interval_append test 42208 42224 42240
  Check329.part42208
  Check329.part42224)))
#print axioms Check329.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check330.part42240 : Interval test 42240 42256 :=
  interval_of_check _ 42240 16 (by decide +kernel)
theorem Check330.part42256 : Interval test 42256 42272 :=
  interval_of_check _ 42256 16 (by decide +kernel)
theorem Check330.part42272 : Interval test 42272 42288 :=
  interval_of_check _ 42272 16 (by decide +kernel)
theorem Check330.part42288 : Interval test 42288 42304 :=
  interval_of_check _ 42288 16 (by decide +kernel)
theorem Check330.part42304 : Interval test 42304 42320 :=
  interval_of_check _ 42304 16 (by decide +kernel)
theorem Check330.part42320 : Interval test 42320 42336 :=
  interval_of_check _ 42320 16 (by decide +kernel)
theorem Check330.part42336 : Interval test 42336 42352 :=
  interval_of_check _ 42336 16 (by decide +kernel)
theorem Check330.part42352 : Interval test 42352 42368 :=
  interval_of_check _ 42352 16 (by decide +kernel)
theorem Check330.checked : Interval test 42240 42368 :=
  (FiniteChecks.interval_append test 42240 42304 42368
  (FiniteChecks.interval_append test 42240 42272 42304
  (FiniteChecks.interval_append test 42240 42256 42272
  Check330.part42240
  Check330.part42256)
  (FiniteChecks.interval_append test 42272 42288 42304
  Check330.part42272
  Check330.part42288))
  (FiniteChecks.interval_append test 42304 42336 42368
  (FiniteChecks.interval_append test 42304 42320 42336
  Check330.part42304
  Check330.part42320)
  (FiniteChecks.interval_append test 42336 42352 42368
  Check330.part42336
  Check330.part42352)))
#print axioms Check330.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check331.part42368 : Interval test 42368 42384 :=
  interval_of_check _ 42368 16 (by decide +kernel)
theorem Check331.part42384 : Interval test 42384 42400 :=
  interval_of_check _ 42384 16 (by decide +kernel)
theorem Check331.part42400 : Interval test 42400 42416 :=
  interval_of_check _ 42400 16 (by decide +kernel)
theorem Check331.part42416 : Interval test 42416 42432 :=
  interval_of_check _ 42416 16 (by decide +kernel)
theorem Check331.part42432 : Interval test 42432 42448 :=
  interval_of_check _ 42432 16 (by decide +kernel)
theorem Check331.part42448 : Interval test 42448 42464 :=
  interval_of_check _ 42448 16 (by decide +kernel)
theorem Check331.part42464 : Interval test 42464 42480 :=
  interval_of_check _ 42464 16 (by decide +kernel)
theorem Check331.part42480 : Interval test 42480 42496 :=
  interval_of_check _ 42480 16 (by decide +kernel)
theorem Check331.checked : Interval test 42368 42496 :=
  (FiniteChecks.interval_append test 42368 42432 42496
  (FiniteChecks.interval_append test 42368 42400 42432
  (FiniteChecks.interval_append test 42368 42384 42400
  Check331.part42368
  Check331.part42384)
  (FiniteChecks.interval_append test 42400 42416 42432
  Check331.part42400
  Check331.part42416))
  (FiniteChecks.interval_append test 42432 42464 42496
  (FiniteChecks.interval_append test 42432 42448 42464
  Check331.part42432
  Check331.part42448)
  (FiniteChecks.interval_append test 42464 42480 42496
  Check331.part42464
  Check331.part42480)))
#print axioms Check331.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check332.part42496 : Interval test 42496 42512 :=
  interval_of_check _ 42496 16 (by decide +kernel)
theorem Check332.part42512 : Interval test 42512 42528 :=
  interval_of_check _ 42512 16 (by decide +kernel)
theorem Check332.part42528 : Interval test 42528 42544 :=
  interval_of_check _ 42528 16 (by decide +kernel)
theorem Check332.part42544 : Interval test 42544 42560 :=
  interval_of_check _ 42544 16 (by decide +kernel)
theorem Check332.part42560 : Interval test 42560 42576 :=
  interval_of_check _ 42560 16 (by decide +kernel)
theorem Check332.part42576 : Interval test 42576 42592 :=
  interval_of_check _ 42576 16 (by decide +kernel)
theorem Check332.part42592 : Interval test 42592 42608 :=
  interval_of_check _ 42592 16 (by decide +kernel)
theorem Check332.part42608 : Interval test 42608 42624 :=
  interval_of_check _ 42608 16 (by decide +kernel)
theorem Check332.checked : Interval test 42496 42624 :=
  (FiniteChecks.interval_append test 42496 42560 42624
  (FiniteChecks.interval_append test 42496 42528 42560
  (FiniteChecks.interval_append test 42496 42512 42528
  Check332.part42496
  Check332.part42512)
  (FiniteChecks.interval_append test 42528 42544 42560
  Check332.part42528
  Check332.part42544))
  (FiniteChecks.interval_append test 42560 42592 42624
  (FiniteChecks.interval_append test 42560 42576 42592
  Check332.part42560
  Check332.part42576)
  (FiniteChecks.interval_append test 42592 42608 42624
  Check332.part42592
  Check332.part42608)))
#print axioms Check332.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check333.part42624 : Interval test 42624 42640 :=
  interval_of_check _ 42624 16 (by decide +kernel)
theorem Check333.part42640 : Interval test 42640 42656 :=
  interval_of_check _ 42640 16 (by decide +kernel)
theorem Check333.part42656 : Interval test 42656 42672 :=
  interval_of_check _ 42656 16 (by decide +kernel)
theorem Check333.part42672 : Interval test 42672 42688 :=
  interval_of_check _ 42672 16 (by decide +kernel)
theorem Check333.part42688 : Interval test 42688 42704 :=
  interval_of_check _ 42688 16 (by decide +kernel)
theorem Check333.part42704 : Interval test 42704 42720 :=
  interval_of_check _ 42704 16 (by decide +kernel)
theorem Check333.part42720 : Interval test 42720 42736 :=
  interval_of_check _ 42720 16 (by decide +kernel)
theorem Check333.part42736 : Interval test 42736 42752 :=
  interval_of_check _ 42736 16 (by decide +kernel)
theorem Check333.checked : Interval test 42624 42752 :=
  (FiniteChecks.interval_append test 42624 42688 42752
  (FiniteChecks.interval_append test 42624 42656 42688
  (FiniteChecks.interval_append test 42624 42640 42656
  Check333.part42624
  Check333.part42640)
  (FiniteChecks.interval_append test 42656 42672 42688
  Check333.part42656
  Check333.part42672))
  (FiniteChecks.interval_append test 42688 42720 42752
  (FiniteChecks.interval_append test 42688 42704 42720
  Check333.part42688
  Check333.part42704)
  (FiniteChecks.interval_append test 42720 42736 42752
  Check333.part42720
  Check333.part42736)))
#print axioms Check333.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check334.part42752 : Interval test 42752 42768 :=
  interval_of_check _ 42752 16 (by decide +kernel)
theorem Check334.part42768 : Interval test 42768 42784 :=
  interval_of_check _ 42768 16 (by decide +kernel)
theorem Check334.part42784 : Interval test 42784 42800 :=
  interval_of_check _ 42784 16 (by decide +kernel)
theorem Check334.part42800 : Interval test 42800 42816 :=
  interval_of_check _ 42800 16 (by decide +kernel)
theorem Check334.part42816 : Interval test 42816 42832 :=
  interval_of_check _ 42816 16 (by decide +kernel)
theorem Check334.part42832 : Interval test 42832 42848 :=
  interval_of_check _ 42832 16 (by decide +kernel)
theorem Check334.part42848 : Interval test 42848 42864 :=
  interval_of_check _ 42848 16 (by decide +kernel)
theorem Check334.part42864 : Interval test 42864 42880 :=
  interval_of_check _ 42864 16 (by decide +kernel)
theorem Check334.checked : Interval test 42752 42880 :=
  (FiniteChecks.interval_append test 42752 42816 42880
  (FiniteChecks.interval_append test 42752 42784 42816
  (FiniteChecks.interval_append test 42752 42768 42784
  Check334.part42752
  Check334.part42768)
  (FiniteChecks.interval_append test 42784 42800 42816
  Check334.part42784
  Check334.part42800))
  (FiniteChecks.interval_append test 42816 42848 42880
  (FiniteChecks.interval_append test 42816 42832 42848
  Check334.part42816
  Check334.part42832)
  (FiniteChecks.interval_append test 42848 42864 42880
  Check334.part42848
  Check334.part42864)))
#print axioms Check334.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check335.part42880 : Interval test 42880 42896 :=
  interval_of_check _ 42880 16 (by decide +kernel)
theorem Check335.part42896 : Interval test 42896 42912 :=
  interval_of_check _ 42896 16 (by decide +kernel)
theorem Check335.part42912 : Interval test 42912 42928 :=
  interval_of_check _ 42912 16 (by decide +kernel)
theorem Check335.part42928 : Interval test 42928 42944 :=
  interval_of_check _ 42928 16 (by decide +kernel)
theorem Check335.part42944 : Interval test 42944 42960 :=
  interval_of_check _ 42944 16 (by decide +kernel)
theorem Check335.part42960 : Interval test 42960 42976 :=
  interval_of_check _ 42960 16 (by decide +kernel)
theorem Check335.part42976 : Interval test 42976 42992 :=
  interval_of_check _ 42976 16 (by decide +kernel)
theorem Check335.part42992 : Interval test 42992 43008 :=
  interval_of_check _ 42992 16 (by decide +kernel)
theorem Check335.checked : Interval test 42880 43008 :=
  (FiniteChecks.interval_append test 42880 42944 43008
  (FiniteChecks.interval_append test 42880 42912 42944
  (FiniteChecks.interval_append test 42880 42896 42912
  Check335.part42880
  Check335.part42896)
  (FiniteChecks.interval_append test 42912 42928 42944
  Check335.part42912
  Check335.part42928))
  (FiniteChecks.interval_append test 42944 42976 43008
  (FiniteChecks.interval_append test 42944 42960 42976
  Check335.part42944
  Check335.part42960)
  (FiniteChecks.interval_append test 42976 42992 43008
  Check335.part42976
  Check335.part42992)))
#print axioms Check335.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check336.part43008 : Interval test 43008 43024 :=
  interval_of_check _ 43008 16 (by decide +kernel)
theorem Check336.part43024 : Interval test 43024 43040 :=
  interval_of_check _ 43024 16 (by decide +kernel)
theorem Check336.part43040 : Interval test 43040 43056 :=
  interval_of_check _ 43040 16 (by decide +kernel)
theorem Check336.part43056 : Interval test 43056 43072 :=
  interval_of_check _ 43056 16 (by decide +kernel)
theorem Check336.part43072 : Interval test 43072 43088 :=
  interval_of_check _ 43072 16 (by decide +kernel)
theorem Check336.part43088 : Interval test 43088 43104 :=
  interval_of_check _ 43088 16 (by decide +kernel)
theorem Check336.part43104 : Interval test 43104 43120 :=
  interval_of_check _ 43104 16 (by decide +kernel)
theorem Check336.part43120 : Interval test 43120 43136 :=
  interval_of_check _ 43120 16 (by decide +kernel)
theorem Check336.checked : Interval test 43008 43136 :=
  (FiniteChecks.interval_append test 43008 43072 43136
  (FiniteChecks.interval_append test 43008 43040 43072
  (FiniteChecks.interval_append test 43008 43024 43040
  Check336.part43008
  Check336.part43024)
  (FiniteChecks.interval_append test 43040 43056 43072
  Check336.part43040
  Check336.part43056))
  (FiniteChecks.interval_append test 43072 43104 43136
  (FiniteChecks.interval_append test 43072 43088 43104
  Check336.part43072
  Check336.part43088)
  (FiniteChecks.interval_append test 43104 43120 43136
  Check336.part43104
  Check336.part43120)))
#print axioms Check336.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check337.part43136 : Interval test 43136 43152 :=
  interval_of_check _ 43136 16 (by decide +kernel)
theorem Check337.part43152 : Interval test 43152 43168 :=
  interval_of_check _ 43152 16 (by decide +kernel)
theorem Check337.part43168 : Interval test 43168 43184 :=
  interval_of_check _ 43168 16 (by decide +kernel)
theorem Check337.part43184 : Interval test 43184 43200 :=
  interval_of_check _ 43184 16 (by decide +kernel)
theorem Check337.part43200 : Interval test 43200 43216 :=
  interval_of_check _ 43200 16 (by decide +kernel)
theorem Check337.part43216 : Interval test 43216 43232 :=
  interval_of_check _ 43216 16 (by decide +kernel)
theorem Check337.part43232 : Interval test 43232 43248 :=
  interval_of_check _ 43232 16 (by decide +kernel)
theorem Check337.part43248 : Interval test 43248 43264 :=
  interval_of_check _ 43248 16 (by decide +kernel)
theorem Check337.checked : Interval test 43136 43264 :=
  (FiniteChecks.interval_append test 43136 43200 43264
  (FiniteChecks.interval_append test 43136 43168 43200
  (FiniteChecks.interval_append test 43136 43152 43168
  Check337.part43136
  Check337.part43152)
  (FiniteChecks.interval_append test 43168 43184 43200
  Check337.part43168
  Check337.part43184))
  (FiniteChecks.interval_append test 43200 43232 43264
  (FiniteChecks.interval_append test 43200 43216 43232
  Check337.part43200
  Check337.part43216)
  (FiniteChecks.interval_append test 43232 43248 43264
  Check337.part43232
  Check337.part43248)))
#print axioms Check337.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check338.part43264 : Interval test 43264 43280 :=
  interval_of_check _ 43264 16 (by decide +kernel)
theorem Check338.part43280 : Interval test 43280 43296 :=
  interval_of_check _ 43280 16 (by decide +kernel)
theorem Check338.part43296 : Interval test 43296 43312 :=
  interval_of_check _ 43296 16 (by decide +kernel)
theorem Check338.part43312 : Interval test 43312 43328 :=
  interval_of_check _ 43312 16 (by decide +kernel)
theorem Check338.part43328 : Interval test 43328 43344 :=
  interval_of_check _ 43328 16 (by decide +kernel)
theorem Check338.part43344 : Interval test 43344 43360 :=
  interval_of_check _ 43344 16 (by decide +kernel)
theorem Check338.part43360 : Interval test 43360 43376 :=
  interval_of_check _ 43360 16 (by decide +kernel)
theorem Check338.part43376 : Interval test 43376 43392 :=
  interval_of_check _ 43376 16 (by decide +kernel)
theorem Check338.checked : Interval test 43264 43392 :=
  (FiniteChecks.interval_append test 43264 43328 43392
  (FiniteChecks.interval_append test 43264 43296 43328
  (FiniteChecks.interval_append test 43264 43280 43296
  Check338.part43264
  Check338.part43280)
  (FiniteChecks.interval_append test 43296 43312 43328
  Check338.part43296
  Check338.part43312))
  (FiniteChecks.interval_append test 43328 43360 43392
  (FiniteChecks.interval_append test 43328 43344 43360
  Check338.part43328
  Check338.part43344)
  (FiniteChecks.interval_append test 43360 43376 43392
  Check338.part43360
  Check338.part43376)))
#print axioms Check338.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check339.part43392 : Interval test 43392 43408 :=
  interval_of_check _ 43392 16 (by decide +kernel)
theorem Check339.part43408 : Interval test 43408 43424 :=
  interval_of_check _ 43408 16 (by decide +kernel)
theorem Check339.part43424 : Interval test 43424 43440 :=
  interval_of_check _ 43424 16 (by decide +kernel)
theorem Check339.part43440 : Interval test 43440 43456 :=
  interval_of_check _ 43440 16 (by decide +kernel)
theorem Check339.part43456 : Interval test 43456 43472 :=
  interval_of_check _ 43456 16 (by decide +kernel)
theorem Check339.part43472 : Interval test 43472 43488 :=
  interval_of_check _ 43472 16 (by decide +kernel)
theorem Check339.part43488 : Interval test 43488 43504 :=
  interval_of_check _ 43488 16 (by decide +kernel)
theorem Check339.part43504 : Interval test 43504 43520 :=
  interval_of_check _ 43504 16 (by decide +kernel)
theorem Check339.checked : Interval test 43392 43520 :=
  (FiniteChecks.interval_append test 43392 43456 43520
  (FiniteChecks.interval_append test 43392 43424 43456
  (FiniteChecks.interval_append test 43392 43408 43424
  Check339.part43392
  Check339.part43408)
  (FiniteChecks.interval_append test 43424 43440 43456
  Check339.part43424
  Check339.part43440))
  (FiniteChecks.interval_append test 43456 43488 43520
  (FiniteChecks.interval_append test 43456 43472 43488
  Check339.part43456
  Check339.part43472)
  (FiniteChecks.interval_append test 43488 43504 43520
  Check339.part43488
  Check339.part43504)))
#print axioms Check339.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
