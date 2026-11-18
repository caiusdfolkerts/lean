module
prelude
public import SharedSix0CellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check180.part23040 : Interval test 23040 23056 :=
  interval_of_check _ 23040 16 (by decide +kernel)
theorem Check180.part23056 : Interval test 23056 23072 :=
  interval_of_check _ 23056 16 (by decide +kernel)
theorem Check180.part23072 : Interval test 23072 23088 :=
  interval_of_check _ 23072 16 (by decide +kernel)
theorem Check180.part23088 : Interval test 23088 23104 :=
  interval_of_check _ 23088 16 (by decide +kernel)
theorem Check180.part23104 : Interval test 23104 23120 :=
  interval_of_check _ 23104 16 (by decide +kernel)
theorem Check180.part23120 : Interval test 23120 23136 :=
  interval_of_check _ 23120 16 (by decide +kernel)
theorem Check180.part23136 : Interval test 23136 23152 :=
  interval_of_check _ 23136 16 (by decide +kernel)
theorem Check180.part23152 : Interval test 23152 23168 :=
  interval_of_check _ 23152 16 (by decide +kernel)
theorem Check180.checked : Interval test 23040 23168 :=
  (FiniteChecks.interval_append test 23040 23104 23168
  (FiniteChecks.interval_append test 23040 23072 23104
  (FiniteChecks.interval_append test 23040 23056 23072
  Check180.part23040
  Check180.part23056)
  (FiniteChecks.interval_append test 23072 23088 23104
  Check180.part23072
  Check180.part23088))
  (FiniteChecks.interval_append test 23104 23136 23168
  (FiniteChecks.interval_append test 23104 23120 23136
  Check180.part23104
  Check180.part23120)
  (FiniteChecks.interval_append test 23136 23152 23168
  Check180.part23136
  Check180.part23152)))
#print axioms Check180.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check181.part23168 : Interval test 23168 23184 :=
  interval_of_check _ 23168 16 (by decide +kernel)
theorem Check181.part23184 : Interval test 23184 23200 :=
  interval_of_check _ 23184 16 (by decide +kernel)
theorem Check181.part23200 : Interval test 23200 23216 :=
  interval_of_check _ 23200 16 (by decide +kernel)
theorem Check181.part23216 : Interval test 23216 23232 :=
  interval_of_check _ 23216 16 (by decide +kernel)
theorem Check181.part23232 : Interval test 23232 23248 :=
  interval_of_check _ 23232 16 (by decide +kernel)
theorem Check181.part23248 : Interval test 23248 23264 :=
  interval_of_check _ 23248 16 (by decide +kernel)
theorem Check181.part23264 : Interval test 23264 23280 :=
  interval_of_check _ 23264 16 (by decide +kernel)
theorem Check181.part23280 : Interval test 23280 23296 :=
  interval_of_check _ 23280 16 (by decide +kernel)
theorem Check181.checked : Interval test 23168 23296 :=
  (FiniteChecks.interval_append test 23168 23232 23296
  (FiniteChecks.interval_append test 23168 23200 23232
  (FiniteChecks.interval_append test 23168 23184 23200
  Check181.part23168
  Check181.part23184)
  (FiniteChecks.interval_append test 23200 23216 23232
  Check181.part23200
  Check181.part23216))
  (FiniteChecks.interval_append test 23232 23264 23296
  (FiniteChecks.interval_append test 23232 23248 23264
  Check181.part23232
  Check181.part23248)
  (FiniteChecks.interval_append test 23264 23280 23296
  Check181.part23264
  Check181.part23280)))
#print axioms Check181.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check182.part23296 : Interval test 23296 23312 :=
  interval_of_check _ 23296 16 (by decide +kernel)
theorem Check182.part23312 : Interval test 23312 23328 :=
  interval_of_check _ 23312 16 (by decide +kernel)
theorem Check182.part23328 : Interval test 23328 23344 :=
  interval_of_check _ 23328 16 (by decide +kernel)
theorem Check182.part23344 : Interval test 23344 23360 :=
  interval_of_check _ 23344 16 (by decide +kernel)
theorem Check182.part23360 : Interval test 23360 23376 :=
  interval_of_check _ 23360 16 (by decide +kernel)
theorem Check182.part23376 : Interval test 23376 23392 :=
  interval_of_check _ 23376 16 (by decide +kernel)
theorem Check182.part23392 : Interval test 23392 23408 :=
  interval_of_check _ 23392 16 (by decide +kernel)
theorem Check182.part23408 : Interval test 23408 23424 :=
  interval_of_check _ 23408 16 (by decide +kernel)
theorem Check182.checked : Interval test 23296 23424 :=
  (FiniteChecks.interval_append test 23296 23360 23424
  (FiniteChecks.interval_append test 23296 23328 23360
  (FiniteChecks.interval_append test 23296 23312 23328
  Check182.part23296
  Check182.part23312)
  (FiniteChecks.interval_append test 23328 23344 23360
  Check182.part23328
  Check182.part23344))
  (FiniteChecks.interval_append test 23360 23392 23424
  (FiniteChecks.interval_append test 23360 23376 23392
  Check182.part23360
  Check182.part23376)
  (FiniteChecks.interval_append test 23392 23408 23424
  Check182.part23392
  Check182.part23408)))
#print axioms Check182.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check183.part23424 : Interval test 23424 23440 :=
  interval_of_check _ 23424 16 (by decide +kernel)
theorem Check183.part23440 : Interval test 23440 23456 :=
  interval_of_check _ 23440 16 (by decide +kernel)
theorem Check183.part23456 : Interval test 23456 23472 :=
  interval_of_check _ 23456 16 (by decide +kernel)
theorem Check183.part23472 : Interval test 23472 23488 :=
  interval_of_check _ 23472 16 (by decide +kernel)
theorem Check183.part23488 : Interval test 23488 23504 :=
  interval_of_check _ 23488 16 (by decide +kernel)
theorem Check183.part23504 : Interval test 23504 23520 :=
  interval_of_check _ 23504 16 (by decide +kernel)
theorem Check183.part23520 : Interval test 23520 23536 :=
  interval_of_check _ 23520 16 (by decide +kernel)
theorem Check183.part23536 : Interval test 23536 23552 :=
  interval_of_check _ 23536 16 (by decide +kernel)
theorem Check183.checked : Interval test 23424 23552 :=
  (FiniteChecks.interval_append test 23424 23488 23552
  (FiniteChecks.interval_append test 23424 23456 23488
  (FiniteChecks.interval_append test 23424 23440 23456
  Check183.part23424
  Check183.part23440)
  (FiniteChecks.interval_append test 23456 23472 23488
  Check183.part23456
  Check183.part23472))
  (FiniteChecks.interval_append test 23488 23520 23552
  (FiniteChecks.interval_append test 23488 23504 23520
  Check183.part23488
  Check183.part23504)
  (FiniteChecks.interval_append test 23520 23536 23552
  Check183.part23520
  Check183.part23536)))
#print axioms Check183.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check184.part23552 : Interval test 23552 23568 :=
  interval_of_check _ 23552 16 (by decide +kernel)
theorem Check184.part23568 : Interval test 23568 23584 :=
  interval_of_check _ 23568 16 (by decide +kernel)
theorem Check184.part23584 : Interval test 23584 23600 :=
  interval_of_check _ 23584 16 (by decide +kernel)
theorem Check184.part23600 : Interval test 23600 23616 :=
  interval_of_check _ 23600 16 (by decide +kernel)
theorem Check184.part23616 : Interval test 23616 23632 :=
  interval_of_check _ 23616 16 (by decide +kernel)
theorem Check184.part23632 : Interval test 23632 23648 :=
  interval_of_check _ 23632 16 (by decide +kernel)
theorem Check184.part23648 : Interval test 23648 23664 :=
  interval_of_check _ 23648 16 (by decide +kernel)
theorem Check184.part23664 : Interval test 23664 23680 :=
  interval_of_check _ 23664 16 (by decide +kernel)
theorem Check184.checked : Interval test 23552 23680 :=
  (FiniteChecks.interval_append test 23552 23616 23680
  (FiniteChecks.interval_append test 23552 23584 23616
  (FiniteChecks.interval_append test 23552 23568 23584
  Check184.part23552
  Check184.part23568)
  (FiniteChecks.interval_append test 23584 23600 23616
  Check184.part23584
  Check184.part23600))
  (FiniteChecks.interval_append test 23616 23648 23680
  (FiniteChecks.interval_append test 23616 23632 23648
  Check184.part23616
  Check184.part23632)
  (FiniteChecks.interval_append test 23648 23664 23680
  Check184.part23648
  Check184.part23664)))
#print axioms Check184.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check185.part23680 : Interval test 23680 23696 :=
  interval_of_check _ 23680 16 (by decide +kernel)
theorem Check185.part23696 : Interval test 23696 23712 :=
  interval_of_check _ 23696 16 (by decide +kernel)
theorem Check185.part23712 : Interval test 23712 23728 :=
  interval_of_check _ 23712 16 (by decide +kernel)
theorem Check185.part23728 : Interval test 23728 23744 :=
  interval_of_check _ 23728 16 (by decide +kernel)
theorem Check185.part23744 : Interval test 23744 23760 :=
  interval_of_check _ 23744 16 (by decide +kernel)
theorem Check185.part23760 : Interval test 23760 23776 :=
  interval_of_check _ 23760 16 (by decide +kernel)
theorem Check185.part23776 : Interval test 23776 23792 :=
  interval_of_check _ 23776 16 (by decide +kernel)
theorem Check185.part23792 : Interval test 23792 23808 :=
  interval_of_check _ 23792 16 (by decide +kernel)
theorem Check185.checked : Interval test 23680 23808 :=
  (FiniteChecks.interval_append test 23680 23744 23808
  (FiniteChecks.interval_append test 23680 23712 23744
  (FiniteChecks.interval_append test 23680 23696 23712
  Check185.part23680
  Check185.part23696)
  (FiniteChecks.interval_append test 23712 23728 23744
  Check185.part23712
  Check185.part23728))
  (FiniteChecks.interval_append test 23744 23776 23808
  (FiniteChecks.interval_append test 23744 23760 23776
  Check185.part23744
  Check185.part23760)
  (FiniteChecks.interval_append test 23776 23792 23808
  Check185.part23776
  Check185.part23792)))
#print axioms Check185.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check186.part23808 : Interval test 23808 23824 :=
  interval_of_check _ 23808 16 (by decide +kernel)
theorem Check186.part23824 : Interval test 23824 23840 :=
  interval_of_check _ 23824 16 (by decide +kernel)
theorem Check186.part23840 : Interval test 23840 23856 :=
  interval_of_check _ 23840 16 (by decide +kernel)
theorem Check186.part23856 : Interval test 23856 23872 :=
  interval_of_check _ 23856 16 (by decide +kernel)
theorem Check186.part23872 : Interval test 23872 23888 :=
  interval_of_check _ 23872 16 (by decide +kernel)
theorem Check186.part23888 : Interval test 23888 23904 :=
  interval_of_check _ 23888 16 (by decide +kernel)
theorem Check186.part23904 : Interval test 23904 23920 :=
  interval_of_check _ 23904 16 (by decide +kernel)
theorem Check186.part23920 : Interval test 23920 23936 :=
  interval_of_check _ 23920 16 (by decide +kernel)
theorem Check186.checked : Interval test 23808 23936 :=
  (FiniteChecks.interval_append test 23808 23872 23936
  (FiniteChecks.interval_append test 23808 23840 23872
  (FiniteChecks.interval_append test 23808 23824 23840
  Check186.part23808
  Check186.part23824)
  (FiniteChecks.interval_append test 23840 23856 23872
  Check186.part23840
  Check186.part23856))
  (FiniteChecks.interval_append test 23872 23904 23936
  (FiniteChecks.interval_append test 23872 23888 23904
  Check186.part23872
  Check186.part23888)
  (FiniteChecks.interval_append test 23904 23920 23936
  Check186.part23904
  Check186.part23920)))
#print axioms Check186.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check187.part23936 : Interval test 23936 23952 :=
  interval_of_check _ 23936 16 (by decide +kernel)
theorem Check187.part23952 : Interval test 23952 23968 :=
  interval_of_check _ 23952 16 (by decide +kernel)
theorem Check187.part23968 : Interval test 23968 23984 :=
  interval_of_check _ 23968 16 (by decide +kernel)
theorem Check187.part23984 : Interval test 23984 24000 :=
  interval_of_check _ 23984 16 (by decide +kernel)
theorem Check187.part24000 : Interval test 24000 24016 :=
  interval_of_check _ 24000 16 (by decide +kernel)
theorem Check187.part24016 : Interval test 24016 24032 :=
  interval_of_check _ 24016 16 (by decide +kernel)
theorem Check187.part24032 : Interval test 24032 24048 :=
  interval_of_check _ 24032 16 (by decide +kernel)
theorem Check187.part24048 : Interval test 24048 24064 :=
  interval_of_check _ 24048 16 (by decide +kernel)
theorem Check187.checked : Interval test 23936 24064 :=
  (FiniteChecks.interval_append test 23936 24000 24064
  (FiniteChecks.interval_append test 23936 23968 24000
  (FiniteChecks.interval_append test 23936 23952 23968
  Check187.part23936
  Check187.part23952)
  (FiniteChecks.interval_append test 23968 23984 24000
  Check187.part23968
  Check187.part23984))
  (FiniteChecks.interval_append test 24000 24032 24064
  (FiniteChecks.interval_append test 24000 24016 24032
  Check187.part24000
  Check187.part24016)
  (FiniteChecks.interval_append test 24032 24048 24064
  Check187.part24032
  Check187.part24048)))
#print axioms Check187.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check188.part24064 : Interval test 24064 24080 :=
  interval_of_check _ 24064 16 (by decide +kernel)
theorem Check188.part24080 : Interval test 24080 24096 :=
  interval_of_check _ 24080 16 (by decide +kernel)
theorem Check188.part24096 : Interval test 24096 24112 :=
  interval_of_check _ 24096 16 (by decide +kernel)
theorem Check188.part24112 : Interval test 24112 24128 :=
  interval_of_check _ 24112 16 (by decide +kernel)
theorem Check188.part24128 : Interval test 24128 24144 :=
  interval_of_check _ 24128 16 (by decide +kernel)
theorem Check188.part24144 : Interval test 24144 24160 :=
  interval_of_check _ 24144 16 (by decide +kernel)
theorem Check188.part24160 : Interval test 24160 24176 :=
  interval_of_check _ 24160 16 (by decide +kernel)
theorem Check188.part24176 : Interval test 24176 24192 :=
  interval_of_check _ 24176 16 (by decide +kernel)
theorem Check188.checked : Interval test 24064 24192 :=
  (FiniteChecks.interval_append test 24064 24128 24192
  (FiniteChecks.interval_append test 24064 24096 24128
  (FiniteChecks.interval_append test 24064 24080 24096
  Check188.part24064
  Check188.part24080)
  (FiniteChecks.interval_append test 24096 24112 24128
  Check188.part24096
  Check188.part24112))
  (FiniteChecks.interval_append test 24128 24160 24192
  (FiniteChecks.interval_append test 24128 24144 24160
  Check188.part24128
  Check188.part24144)
  (FiniteChecks.interval_append test 24160 24176 24192
  Check188.part24160
  Check188.part24176)))
#print axioms Check188.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check189.part24192 : Interval test 24192 24208 :=
  interval_of_check _ 24192 16 (by decide +kernel)
theorem Check189.part24208 : Interval test 24208 24224 :=
  interval_of_check _ 24208 16 (by decide +kernel)
theorem Check189.part24224 : Interval test 24224 24240 :=
  interval_of_check _ 24224 16 (by decide +kernel)
theorem Check189.part24240 : Interval test 24240 24256 :=
  interval_of_check _ 24240 16 (by decide +kernel)
theorem Check189.part24256 : Interval test 24256 24272 :=
  interval_of_check _ 24256 16 (by decide +kernel)
theorem Check189.part24272 : Interval test 24272 24288 :=
  interval_of_check _ 24272 16 (by decide +kernel)
theorem Check189.part24288 : Interval test 24288 24304 :=
  interval_of_check _ 24288 16 (by decide +kernel)
theorem Check189.part24304 : Interval test 24304 24320 :=
  interval_of_check _ 24304 16 (by decide +kernel)
theorem Check189.checked : Interval test 24192 24320 :=
  (FiniteChecks.interval_append test 24192 24256 24320
  (FiniteChecks.interval_append test 24192 24224 24256
  (FiniteChecks.interval_append test 24192 24208 24224
  Check189.part24192
  Check189.part24208)
  (FiniteChecks.interval_append test 24224 24240 24256
  Check189.part24224
  Check189.part24240))
  (FiniteChecks.interval_append test 24256 24288 24320
  (FiniteChecks.interval_append test 24256 24272 24288
  Check189.part24256
  Check189.part24272)
  (FiniteChecks.interval_append test 24288 24304 24320
  Check189.part24288
  Check189.part24304)))
#print axioms Check189.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check190.part24320 : Interval test 24320 24336 :=
  interval_of_check _ 24320 16 (by decide +kernel)
theorem Check190.part24336 : Interval test 24336 24352 :=
  interval_of_check _ 24336 16 (by decide +kernel)
theorem Check190.part24352 : Interval test 24352 24368 :=
  interval_of_check _ 24352 16 (by decide +kernel)
theorem Check190.part24368 : Interval test 24368 24384 :=
  interval_of_check _ 24368 16 (by decide +kernel)
theorem Check190.part24384 : Interval test 24384 24400 :=
  interval_of_check _ 24384 16 (by decide +kernel)
theorem Check190.part24400 : Interval test 24400 24416 :=
  interval_of_check _ 24400 16 (by decide +kernel)
theorem Check190.part24416 : Interval test 24416 24432 :=
  interval_of_check _ 24416 16 (by decide +kernel)
theorem Check190.part24432 : Interval test 24432 24448 :=
  interval_of_check _ 24432 16 (by decide +kernel)
theorem Check190.checked : Interval test 24320 24448 :=
  (FiniteChecks.interval_append test 24320 24384 24448
  (FiniteChecks.interval_append test 24320 24352 24384
  (FiniteChecks.interval_append test 24320 24336 24352
  Check190.part24320
  Check190.part24336)
  (FiniteChecks.interval_append test 24352 24368 24384
  Check190.part24352
  Check190.part24368))
  (FiniteChecks.interval_append test 24384 24416 24448
  (FiniteChecks.interval_append test 24384 24400 24416
  Check190.part24384
  Check190.part24400)
  (FiniteChecks.interval_append test 24416 24432 24448
  Check190.part24416
  Check190.part24432)))
#print axioms Check190.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check191.part24448 : Interval test 24448 24464 :=
  interval_of_check _ 24448 16 (by decide +kernel)
theorem Check191.part24464 : Interval test 24464 24480 :=
  interval_of_check _ 24464 16 (by decide +kernel)
theorem Check191.part24480 : Interval test 24480 24496 :=
  interval_of_check _ 24480 16 (by decide +kernel)
theorem Check191.part24496 : Interval test 24496 24512 :=
  interval_of_check _ 24496 16 (by decide +kernel)
theorem Check191.part24512 : Interval test 24512 24528 :=
  interval_of_check _ 24512 16 (by decide +kernel)
theorem Check191.part24528 : Interval test 24528 24544 :=
  interval_of_check _ 24528 16 (by decide +kernel)
theorem Check191.part24544 : Interval test 24544 24560 :=
  interval_of_check _ 24544 16 (by decide +kernel)
theorem Check191.part24560 : Interval test 24560 24576 :=
  interval_of_check _ 24560 16 (by decide +kernel)
theorem Check191.checked : Interval test 24448 24576 :=
  (FiniteChecks.interval_append test 24448 24512 24576
  (FiniteChecks.interval_append test 24448 24480 24512
  (FiniteChecks.interval_append test 24448 24464 24480
  Check191.part24448
  Check191.part24464)
  (FiniteChecks.interval_append test 24480 24496 24512
  Check191.part24480
  Check191.part24496))
  (FiniteChecks.interval_append test 24512 24544 24576
  (FiniteChecks.interval_append test 24512 24528 24544
  Check191.part24512
  Check191.part24528)
  (FiniteChecks.interval_append test 24544 24560 24576
  Check191.part24544
  Check191.part24560)))
#print axioms Check191.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check192.part24576 : Interval test 24576 24592 :=
  interval_of_check _ 24576 16 (by decide +kernel)
theorem Check192.part24592 : Interval test 24592 24608 :=
  interval_of_check _ 24592 16 (by decide +kernel)
theorem Check192.part24608 : Interval test 24608 24624 :=
  interval_of_check _ 24608 16 (by decide +kernel)
theorem Check192.part24624 : Interval test 24624 24640 :=
  interval_of_check _ 24624 16 (by decide +kernel)
theorem Check192.part24640 : Interval test 24640 24656 :=
  interval_of_check _ 24640 16 (by decide +kernel)
theorem Check192.part24656 : Interval test 24656 24672 :=
  interval_of_check _ 24656 16 (by decide +kernel)
theorem Check192.part24672 : Interval test 24672 24688 :=
  interval_of_check _ 24672 16 (by decide +kernel)
theorem Check192.part24688 : Interval test 24688 24704 :=
  interval_of_check _ 24688 16 (by decide +kernel)
theorem Check192.checked : Interval test 24576 24704 :=
  (FiniteChecks.interval_append test 24576 24640 24704
  (FiniteChecks.interval_append test 24576 24608 24640
  (FiniteChecks.interval_append test 24576 24592 24608
  Check192.part24576
  Check192.part24592)
  (FiniteChecks.interval_append test 24608 24624 24640
  Check192.part24608
  Check192.part24624))
  (FiniteChecks.interval_append test 24640 24672 24704
  (FiniteChecks.interval_append test 24640 24656 24672
  Check192.part24640
  Check192.part24656)
  (FiniteChecks.interval_append test 24672 24688 24704
  Check192.part24672
  Check192.part24688)))
#print axioms Check192.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check193.part24704 : Interval test 24704 24720 :=
  interval_of_check _ 24704 16 (by decide +kernel)
theorem Check193.part24720 : Interval test 24720 24736 :=
  interval_of_check _ 24720 16 (by decide +kernel)
theorem Check193.part24736 : Interval test 24736 24752 :=
  interval_of_check _ 24736 16 (by decide +kernel)
theorem Check193.part24752 : Interval test 24752 24768 :=
  interval_of_check _ 24752 16 (by decide +kernel)
theorem Check193.part24768 : Interval test 24768 24784 :=
  interval_of_check _ 24768 16 (by decide +kernel)
theorem Check193.part24784 : Interval test 24784 24800 :=
  interval_of_check _ 24784 16 (by decide +kernel)
theorem Check193.part24800 : Interval test 24800 24816 :=
  interval_of_check _ 24800 16 (by decide +kernel)
theorem Check193.part24816 : Interval test 24816 24832 :=
  interval_of_check _ 24816 16 (by decide +kernel)
theorem Check193.checked : Interval test 24704 24832 :=
  (FiniteChecks.interval_append test 24704 24768 24832
  (FiniteChecks.interval_append test 24704 24736 24768
  (FiniteChecks.interval_append test 24704 24720 24736
  Check193.part24704
  Check193.part24720)
  (FiniteChecks.interval_append test 24736 24752 24768
  Check193.part24736
  Check193.part24752))
  (FiniteChecks.interval_append test 24768 24800 24832
  (FiniteChecks.interval_append test 24768 24784 24800
  Check193.part24768
  Check193.part24784)
  (FiniteChecks.interval_append test 24800 24816 24832
  Check193.part24800
  Check193.part24816)))
#print axioms Check193.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check194.part24832 : Interval test 24832 24848 :=
  interval_of_check _ 24832 16 (by decide +kernel)
theorem Check194.part24848 : Interval test 24848 24864 :=
  interval_of_check _ 24848 16 (by decide +kernel)
theorem Check194.part24864 : Interval test 24864 24880 :=
  interval_of_check _ 24864 16 (by decide +kernel)
theorem Check194.part24880 : Interval test 24880 24896 :=
  interval_of_check _ 24880 16 (by decide +kernel)
theorem Check194.part24896 : Interval test 24896 24912 :=
  interval_of_check _ 24896 16 (by decide +kernel)
theorem Check194.part24912 : Interval test 24912 24928 :=
  interval_of_check _ 24912 16 (by decide +kernel)
theorem Check194.part24928 : Interval test 24928 24944 :=
  interval_of_check _ 24928 16 (by decide +kernel)
theorem Check194.part24944 : Interval test 24944 24960 :=
  interval_of_check _ 24944 16 (by decide +kernel)
theorem Check194.checked : Interval test 24832 24960 :=
  (FiniteChecks.interval_append test 24832 24896 24960
  (FiniteChecks.interval_append test 24832 24864 24896
  (FiniteChecks.interval_append test 24832 24848 24864
  Check194.part24832
  Check194.part24848)
  (FiniteChecks.interval_append test 24864 24880 24896
  Check194.part24864
  Check194.part24880))
  (FiniteChecks.interval_append test 24896 24928 24960
  (FiniteChecks.interval_append test 24896 24912 24928
  Check194.part24896
  Check194.part24912)
  (FiniteChecks.interval_append test 24928 24944 24960
  Check194.part24928
  Check194.part24944)))
#print axioms Check194.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check195.part24960 : Interval test 24960 24976 :=
  interval_of_check _ 24960 16 (by decide +kernel)
theorem Check195.part24976 : Interval test 24976 24992 :=
  interval_of_check _ 24976 16 (by decide +kernel)
theorem Check195.part24992 : Interval test 24992 25008 :=
  interval_of_check _ 24992 16 (by decide +kernel)
theorem Check195.part25008 : Interval test 25008 25024 :=
  interval_of_check _ 25008 16 (by decide +kernel)
theorem Check195.part25024 : Interval test 25024 25040 :=
  interval_of_check _ 25024 16 (by decide +kernel)
theorem Check195.part25040 : Interval test 25040 25056 :=
  interval_of_check _ 25040 16 (by decide +kernel)
theorem Check195.part25056 : Interval test 25056 25072 :=
  interval_of_check _ 25056 16 (by decide +kernel)
theorem Check195.part25072 : Interval test 25072 25088 :=
  interval_of_check _ 25072 16 (by decide +kernel)
theorem Check195.checked : Interval test 24960 25088 :=
  (FiniteChecks.interval_append test 24960 25024 25088
  (FiniteChecks.interval_append test 24960 24992 25024
  (FiniteChecks.interval_append test 24960 24976 24992
  Check195.part24960
  Check195.part24976)
  (FiniteChecks.interval_append test 24992 25008 25024
  Check195.part24992
  Check195.part25008))
  (FiniteChecks.interval_append test 25024 25056 25088
  (FiniteChecks.interval_append test 25024 25040 25056
  Check195.part25024
  Check195.part25040)
  (FiniteChecks.interval_append test 25056 25072 25088
  Check195.part25056
  Check195.part25072)))
#print axioms Check195.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check196.part25088 : Interval test 25088 25104 :=
  interval_of_check _ 25088 16 (by decide +kernel)
theorem Check196.part25104 : Interval test 25104 25120 :=
  interval_of_check _ 25104 16 (by decide +kernel)
theorem Check196.part25120 : Interval test 25120 25136 :=
  interval_of_check _ 25120 16 (by decide +kernel)
theorem Check196.part25136 : Interval test 25136 25152 :=
  interval_of_check _ 25136 16 (by decide +kernel)
theorem Check196.part25152 : Interval test 25152 25168 :=
  interval_of_check _ 25152 16 (by decide +kernel)
theorem Check196.part25168 : Interval test 25168 25184 :=
  interval_of_check _ 25168 16 (by decide +kernel)
theorem Check196.part25184 : Interval test 25184 25200 :=
  interval_of_check _ 25184 16 (by decide +kernel)
theorem Check196.part25200 : Interval test 25200 25216 :=
  interval_of_check _ 25200 16 (by decide +kernel)
theorem Check196.checked : Interval test 25088 25216 :=
  (FiniteChecks.interval_append test 25088 25152 25216
  (FiniteChecks.interval_append test 25088 25120 25152
  (FiniteChecks.interval_append test 25088 25104 25120
  Check196.part25088
  Check196.part25104)
  (FiniteChecks.interval_append test 25120 25136 25152
  Check196.part25120
  Check196.part25136))
  (FiniteChecks.interval_append test 25152 25184 25216
  (FiniteChecks.interval_append test 25152 25168 25184
  Check196.part25152
  Check196.part25168)
  (FiniteChecks.interval_append test 25184 25200 25216
  Check196.part25184
  Check196.part25200)))
#print axioms Check196.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check197.part25216 : Interval test 25216 25232 :=
  interval_of_check _ 25216 16 (by decide +kernel)
theorem Check197.part25232 : Interval test 25232 25248 :=
  interval_of_check _ 25232 16 (by decide +kernel)
theorem Check197.part25248 : Interval test 25248 25264 :=
  interval_of_check _ 25248 16 (by decide +kernel)
theorem Check197.part25264 : Interval test 25264 25280 :=
  interval_of_check _ 25264 16 (by decide +kernel)
theorem Check197.part25280 : Interval test 25280 25296 :=
  interval_of_check _ 25280 16 (by decide +kernel)
theorem Check197.part25296 : Interval test 25296 25312 :=
  interval_of_check _ 25296 16 (by decide +kernel)
theorem Check197.part25312 : Interval test 25312 25328 :=
  interval_of_check _ 25312 16 (by decide +kernel)
theorem Check197.part25328 : Interval test 25328 25344 :=
  interval_of_check _ 25328 16 (by decide +kernel)
theorem Check197.checked : Interval test 25216 25344 :=
  (FiniteChecks.interval_append test 25216 25280 25344
  (FiniteChecks.interval_append test 25216 25248 25280
  (FiniteChecks.interval_append test 25216 25232 25248
  Check197.part25216
  Check197.part25232)
  (FiniteChecks.interval_append test 25248 25264 25280
  Check197.part25248
  Check197.part25264))
  (FiniteChecks.interval_append test 25280 25312 25344
  (FiniteChecks.interval_append test 25280 25296 25312
  Check197.part25280
  Check197.part25296)
  (FiniteChecks.interval_append test 25312 25328 25344
  Check197.part25312
  Check197.part25328)))
#print axioms Check197.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check198.part25344 : Interval test 25344 25360 :=
  interval_of_check _ 25344 16 (by decide +kernel)
theorem Check198.part25360 : Interval test 25360 25376 :=
  interval_of_check _ 25360 16 (by decide +kernel)
theorem Check198.part25376 : Interval test 25376 25392 :=
  interval_of_check _ 25376 16 (by decide +kernel)
theorem Check198.part25392 : Interval test 25392 25408 :=
  interval_of_check _ 25392 16 (by decide +kernel)
theorem Check198.part25408 : Interval test 25408 25424 :=
  interval_of_check _ 25408 16 (by decide +kernel)
theorem Check198.part25424 : Interval test 25424 25440 :=
  interval_of_check _ 25424 16 (by decide +kernel)
theorem Check198.part25440 : Interval test 25440 25456 :=
  interval_of_check _ 25440 16 (by decide +kernel)
theorem Check198.part25456 : Interval test 25456 25472 :=
  interval_of_check _ 25456 16 (by decide +kernel)
theorem Check198.checked : Interval test 25344 25472 :=
  (FiniteChecks.interval_append test 25344 25408 25472
  (FiniteChecks.interval_append test 25344 25376 25408
  (FiniteChecks.interval_append test 25344 25360 25376
  Check198.part25344
  Check198.part25360)
  (FiniteChecks.interval_append test 25376 25392 25408
  Check198.part25376
  Check198.part25392))
  (FiniteChecks.interval_append test 25408 25440 25472
  (FiniteChecks.interval_append test 25408 25424 25440
  Check198.part25408
  Check198.part25424)
  (FiniteChecks.interval_append test 25440 25456 25472
  Check198.part25440
  Check198.part25456)))
#print axioms Check198.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check199.part25472 : Interval test 25472 25488 :=
  interval_of_check _ 25472 16 (by decide +kernel)
theorem Check199.part25488 : Interval test 25488 25504 :=
  interval_of_check _ 25488 16 (by decide +kernel)
theorem Check199.part25504 : Interval test 25504 25520 :=
  interval_of_check _ 25504 16 (by decide +kernel)
theorem Check199.part25520 : Interval test 25520 25536 :=
  interval_of_check _ 25520 16 (by decide +kernel)
theorem Check199.part25536 : Interval test 25536 25552 :=
  interval_of_check _ 25536 16 (by decide +kernel)
theorem Check199.part25552 : Interval test 25552 25568 :=
  interval_of_check _ 25552 16 (by decide +kernel)
theorem Check199.part25568 : Interval test 25568 25584 :=
  interval_of_check _ 25568 16 (by decide +kernel)
theorem Check199.part25584 : Interval test 25584 25600 :=
  interval_of_check _ 25584 16 (by decide +kernel)
theorem Check199.checked : Interval test 25472 25600 :=
  (FiniteChecks.interval_append test 25472 25536 25600
  (FiniteChecks.interval_append test 25472 25504 25536
  (FiniteChecks.interval_append test 25472 25488 25504
  Check199.part25472
  Check199.part25488)
  (FiniteChecks.interval_append test 25504 25520 25536
  Check199.part25504
  Check199.part25520))
  (FiniteChecks.interval_append test 25536 25568 25600
  (FiniteChecks.interval_append test 25536 25552 25568
  Check199.part25536
  Check199.part25552)
  (FiniteChecks.interval_append test 25568 25584 25600
  Check199.part25568
  Check199.part25584)))
#print axioms Check199.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
