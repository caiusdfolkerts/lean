module
prelude
public import SharedSix0CellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check040.part5120 : Interval test 5120 5136 :=
  interval_of_check _ 5120 16 (by decide +kernel)
theorem Check040.part5136 : Interval test 5136 5152 :=
  interval_of_check _ 5136 16 (by decide +kernel)
theorem Check040.part5152 : Interval test 5152 5168 :=
  interval_of_check _ 5152 16 (by decide +kernel)
theorem Check040.part5168 : Interval test 5168 5184 :=
  interval_of_check _ 5168 16 (by decide +kernel)
theorem Check040.part5184 : Interval test 5184 5200 :=
  interval_of_check _ 5184 16 (by decide +kernel)
theorem Check040.part5200 : Interval test 5200 5216 :=
  interval_of_check _ 5200 16 (by decide +kernel)
theorem Check040.part5216 : Interval test 5216 5232 :=
  interval_of_check _ 5216 16 (by decide +kernel)
theorem Check040.part5232 : Interval test 5232 5248 :=
  interval_of_check _ 5232 16 (by decide +kernel)
theorem Check040.checked : Interval test 5120 5248 :=
  (FiniteChecks.interval_append test 5120 5184 5248
  (FiniteChecks.interval_append test 5120 5152 5184
  (FiniteChecks.interval_append test 5120 5136 5152
  Check040.part5120
  Check040.part5136)
  (FiniteChecks.interval_append test 5152 5168 5184
  Check040.part5152
  Check040.part5168))
  (FiniteChecks.interval_append test 5184 5216 5248
  (FiniteChecks.interval_append test 5184 5200 5216
  Check040.part5184
  Check040.part5200)
  (FiniteChecks.interval_append test 5216 5232 5248
  Check040.part5216
  Check040.part5232)))
#print axioms Check040.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check041.part5248 : Interval test 5248 5264 :=
  interval_of_check _ 5248 16 (by decide +kernel)
theorem Check041.part5264 : Interval test 5264 5280 :=
  interval_of_check _ 5264 16 (by decide +kernel)
theorem Check041.part5280 : Interval test 5280 5296 :=
  interval_of_check _ 5280 16 (by decide +kernel)
theorem Check041.part5296 : Interval test 5296 5312 :=
  interval_of_check _ 5296 16 (by decide +kernel)
theorem Check041.part5312 : Interval test 5312 5328 :=
  interval_of_check _ 5312 16 (by decide +kernel)
theorem Check041.part5328 : Interval test 5328 5344 :=
  interval_of_check _ 5328 16 (by decide +kernel)
theorem Check041.part5344 : Interval test 5344 5360 :=
  interval_of_check _ 5344 16 (by decide +kernel)
theorem Check041.part5360 : Interval test 5360 5376 :=
  interval_of_check _ 5360 16 (by decide +kernel)
theorem Check041.checked : Interval test 5248 5376 :=
  (FiniteChecks.interval_append test 5248 5312 5376
  (FiniteChecks.interval_append test 5248 5280 5312
  (FiniteChecks.interval_append test 5248 5264 5280
  Check041.part5248
  Check041.part5264)
  (FiniteChecks.interval_append test 5280 5296 5312
  Check041.part5280
  Check041.part5296))
  (FiniteChecks.interval_append test 5312 5344 5376
  (FiniteChecks.interval_append test 5312 5328 5344
  Check041.part5312
  Check041.part5328)
  (FiniteChecks.interval_append test 5344 5360 5376
  Check041.part5344
  Check041.part5360)))
#print axioms Check041.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check042.part5376 : Interval test 5376 5392 :=
  interval_of_check _ 5376 16 (by decide +kernel)
theorem Check042.part5392 : Interval test 5392 5408 :=
  interval_of_check _ 5392 16 (by decide +kernel)
theorem Check042.part5408 : Interval test 5408 5424 :=
  interval_of_check _ 5408 16 (by decide +kernel)
theorem Check042.part5424 : Interval test 5424 5440 :=
  interval_of_check _ 5424 16 (by decide +kernel)
theorem Check042.part5440 : Interval test 5440 5456 :=
  interval_of_check _ 5440 16 (by decide +kernel)
theorem Check042.part5456 : Interval test 5456 5472 :=
  interval_of_check _ 5456 16 (by decide +kernel)
theorem Check042.part5472 : Interval test 5472 5488 :=
  interval_of_check _ 5472 16 (by decide +kernel)
theorem Check042.part5488 : Interval test 5488 5504 :=
  interval_of_check _ 5488 16 (by decide +kernel)
theorem Check042.checked : Interval test 5376 5504 :=
  (FiniteChecks.interval_append test 5376 5440 5504
  (FiniteChecks.interval_append test 5376 5408 5440
  (FiniteChecks.interval_append test 5376 5392 5408
  Check042.part5376
  Check042.part5392)
  (FiniteChecks.interval_append test 5408 5424 5440
  Check042.part5408
  Check042.part5424))
  (FiniteChecks.interval_append test 5440 5472 5504
  (FiniteChecks.interval_append test 5440 5456 5472
  Check042.part5440
  Check042.part5456)
  (FiniteChecks.interval_append test 5472 5488 5504
  Check042.part5472
  Check042.part5488)))
#print axioms Check042.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check043.part5504 : Interval test 5504 5520 :=
  interval_of_check _ 5504 16 (by decide +kernel)
theorem Check043.part5520 : Interval test 5520 5536 :=
  interval_of_check _ 5520 16 (by decide +kernel)
theorem Check043.part5536 : Interval test 5536 5552 :=
  interval_of_check _ 5536 16 (by decide +kernel)
theorem Check043.part5552 : Interval test 5552 5568 :=
  interval_of_check _ 5552 16 (by decide +kernel)
theorem Check043.part5568 : Interval test 5568 5584 :=
  interval_of_check _ 5568 16 (by decide +kernel)
theorem Check043.part5584 : Interval test 5584 5600 :=
  interval_of_check _ 5584 16 (by decide +kernel)
theorem Check043.part5600 : Interval test 5600 5616 :=
  interval_of_check _ 5600 16 (by decide +kernel)
theorem Check043.part5616 : Interval test 5616 5632 :=
  interval_of_check _ 5616 16 (by decide +kernel)
theorem Check043.checked : Interval test 5504 5632 :=
  (FiniteChecks.interval_append test 5504 5568 5632
  (FiniteChecks.interval_append test 5504 5536 5568
  (FiniteChecks.interval_append test 5504 5520 5536
  Check043.part5504
  Check043.part5520)
  (FiniteChecks.interval_append test 5536 5552 5568
  Check043.part5536
  Check043.part5552))
  (FiniteChecks.interval_append test 5568 5600 5632
  (FiniteChecks.interval_append test 5568 5584 5600
  Check043.part5568
  Check043.part5584)
  (FiniteChecks.interval_append test 5600 5616 5632
  Check043.part5600
  Check043.part5616)))
#print axioms Check043.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check044.part5632 : Interval test 5632 5648 :=
  interval_of_check _ 5632 16 (by decide +kernel)
theorem Check044.part5648 : Interval test 5648 5664 :=
  interval_of_check _ 5648 16 (by decide +kernel)
theorem Check044.part5664 : Interval test 5664 5680 :=
  interval_of_check _ 5664 16 (by decide +kernel)
theorem Check044.part5680 : Interval test 5680 5696 :=
  interval_of_check _ 5680 16 (by decide +kernel)
theorem Check044.part5696 : Interval test 5696 5712 :=
  interval_of_check _ 5696 16 (by decide +kernel)
theorem Check044.part5712 : Interval test 5712 5728 :=
  interval_of_check _ 5712 16 (by decide +kernel)
theorem Check044.part5728 : Interval test 5728 5744 :=
  interval_of_check _ 5728 16 (by decide +kernel)
theorem Check044.part5744 : Interval test 5744 5760 :=
  interval_of_check _ 5744 16 (by decide +kernel)
theorem Check044.checked : Interval test 5632 5760 :=
  (FiniteChecks.interval_append test 5632 5696 5760
  (FiniteChecks.interval_append test 5632 5664 5696
  (FiniteChecks.interval_append test 5632 5648 5664
  Check044.part5632
  Check044.part5648)
  (FiniteChecks.interval_append test 5664 5680 5696
  Check044.part5664
  Check044.part5680))
  (FiniteChecks.interval_append test 5696 5728 5760
  (FiniteChecks.interval_append test 5696 5712 5728
  Check044.part5696
  Check044.part5712)
  (FiniteChecks.interval_append test 5728 5744 5760
  Check044.part5728
  Check044.part5744)))
#print axioms Check044.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check045.part5760 : Interval test 5760 5776 :=
  interval_of_check _ 5760 16 (by decide +kernel)
theorem Check045.part5776 : Interval test 5776 5792 :=
  interval_of_check _ 5776 16 (by decide +kernel)
theorem Check045.part5792 : Interval test 5792 5808 :=
  interval_of_check _ 5792 16 (by decide +kernel)
theorem Check045.part5808 : Interval test 5808 5824 :=
  interval_of_check _ 5808 16 (by decide +kernel)
theorem Check045.part5824 : Interval test 5824 5840 :=
  interval_of_check _ 5824 16 (by decide +kernel)
theorem Check045.part5840 : Interval test 5840 5856 :=
  interval_of_check _ 5840 16 (by decide +kernel)
theorem Check045.part5856 : Interval test 5856 5872 :=
  interval_of_check _ 5856 16 (by decide +kernel)
theorem Check045.part5872 : Interval test 5872 5888 :=
  interval_of_check _ 5872 16 (by decide +kernel)
theorem Check045.checked : Interval test 5760 5888 :=
  (FiniteChecks.interval_append test 5760 5824 5888
  (FiniteChecks.interval_append test 5760 5792 5824
  (FiniteChecks.interval_append test 5760 5776 5792
  Check045.part5760
  Check045.part5776)
  (FiniteChecks.interval_append test 5792 5808 5824
  Check045.part5792
  Check045.part5808))
  (FiniteChecks.interval_append test 5824 5856 5888
  (FiniteChecks.interval_append test 5824 5840 5856
  Check045.part5824
  Check045.part5840)
  (FiniteChecks.interval_append test 5856 5872 5888
  Check045.part5856
  Check045.part5872)))
#print axioms Check045.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check046.part5888 : Interval test 5888 5904 :=
  interval_of_check _ 5888 16 (by decide +kernel)
theorem Check046.part5904 : Interval test 5904 5920 :=
  interval_of_check _ 5904 16 (by decide +kernel)
theorem Check046.part5920 : Interval test 5920 5936 :=
  interval_of_check _ 5920 16 (by decide +kernel)
theorem Check046.part5936 : Interval test 5936 5952 :=
  interval_of_check _ 5936 16 (by decide +kernel)
theorem Check046.part5952 : Interval test 5952 5968 :=
  interval_of_check _ 5952 16 (by decide +kernel)
theorem Check046.part5968 : Interval test 5968 5984 :=
  interval_of_check _ 5968 16 (by decide +kernel)
theorem Check046.part5984 : Interval test 5984 6000 :=
  interval_of_check _ 5984 16 (by decide +kernel)
theorem Check046.part6000 : Interval test 6000 6016 :=
  interval_of_check _ 6000 16 (by decide +kernel)
theorem Check046.checked : Interval test 5888 6016 :=
  (FiniteChecks.interval_append test 5888 5952 6016
  (FiniteChecks.interval_append test 5888 5920 5952
  (FiniteChecks.interval_append test 5888 5904 5920
  Check046.part5888
  Check046.part5904)
  (FiniteChecks.interval_append test 5920 5936 5952
  Check046.part5920
  Check046.part5936))
  (FiniteChecks.interval_append test 5952 5984 6016
  (FiniteChecks.interval_append test 5952 5968 5984
  Check046.part5952
  Check046.part5968)
  (FiniteChecks.interval_append test 5984 6000 6016
  Check046.part5984
  Check046.part6000)))
#print axioms Check046.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check047.part6016 : Interval test 6016 6032 :=
  interval_of_check _ 6016 16 (by decide +kernel)
theorem Check047.part6032 : Interval test 6032 6048 :=
  interval_of_check _ 6032 16 (by decide +kernel)
theorem Check047.part6048 : Interval test 6048 6064 :=
  interval_of_check _ 6048 16 (by decide +kernel)
theorem Check047.part6064 : Interval test 6064 6080 :=
  interval_of_check _ 6064 16 (by decide +kernel)
theorem Check047.part6080 : Interval test 6080 6096 :=
  interval_of_check _ 6080 16 (by decide +kernel)
theorem Check047.part6096 : Interval test 6096 6112 :=
  interval_of_check _ 6096 16 (by decide +kernel)
theorem Check047.part6112 : Interval test 6112 6128 :=
  interval_of_check _ 6112 16 (by decide +kernel)
theorem Check047.part6128 : Interval test 6128 6144 :=
  interval_of_check _ 6128 16 (by decide +kernel)
theorem Check047.checked : Interval test 6016 6144 :=
  (FiniteChecks.interval_append test 6016 6080 6144
  (FiniteChecks.interval_append test 6016 6048 6080
  (FiniteChecks.interval_append test 6016 6032 6048
  Check047.part6016
  Check047.part6032)
  (FiniteChecks.interval_append test 6048 6064 6080
  Check047.part6048
  Check047.part6064))
  (FiniteChecks.interval_append test 6080 6112 6144
  (FiniteChecks.interval_append test 6080 6096 6112
  Check047.part6080
  Check047.part6096)
  (FiniteChecks.interval_append test 6112 6128 6144
  Check047.part6112
  Check047.part6128)))
#print axioms Check047.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check048.part6144 : Interval test 6144 6160 :=
  interval_of_check _ 6144 16 (by decide +kernel)
theorem Check048.part6160 : Interval test 6160 6176 :=
  interval_of_check _ 6160 16 (by decide +kernel)
theorem Check048.part6176 : Interval test 6176 6192 :=
  interval_of_check _ 6176 16 (by decide +kernel)
theorem Check048.part6192 : Interval test 6192 6208 :=
  interval_of_check _ 6192 16 (by decide +kernel)
theorem Check048.part6208 : Interval test 6208 6224 :=
  interval_of_check _ 6208 16 (by decide +kernel)
theorem Check048.part6224 : Interval test 6224 6240 :=
  interval_of_check _ 6224 16 (by decide +kernel)
theorem Check048.part6240 : Interval test 6240 6256 :=
  interval_of_check _ 6240 16 (by decide +kernel)
theorem Check048.part6256 : Interval test 6256 6272 :=
  interval_of_check _ 6256 16 (by decide +kernel)
theorem Check048.checked : Interval test 6144 6272 :=
  (FiniteChecks.interval_append test 6144 6208 6272
  (FiniteChecks.interval_append test 6144 6176 6208
  (FiniteChecks.interval_append test 6144 6160 6176
  Check048.part6144
  Check048.part6160)
  (FiniteChecks.interval_append test 6176 6192 6208
  Check048.part6176
  Check048.part6192))
  (FiniteChecks.interval_append test 6208 6240 6272
  (FiniteChecks.interval_append test 6208 6224 6240
  Check048.part6208
  Check048.part6224)
  (FiniteChecks.interval_append test 6240 6256 6272
  Check048.part6240
  Check048.part6256)))
#print axioms Check048.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check049.part6272 : Interval test 6272 6288 :=
  interval_of_check _ 6272 16 (by decide +kernel)
theorem Check049.part6288 : Interval test 6288 6304 :=
  interval_of_check _ 6288 16 (by decide +kernel)
theorem Check049.part6304 : Interval test 6304 6320 :=
  interval_of_check _ 6304 16 (by decide +kernel)
theorem Check049.part6320 : Interval test 6320 6336 :=
  interval_of_check _ 6320 16 (by decide +kernel)
theorem Check049.part6336 : Interval test 6336 6352 :=
  interval_of_check _ 6336 16 (by decide +kernel)
theorem Check049.part6352 : Interval test 6352 6368 :=
  interval_of_check _ 6352 16 (by decide +kernel)
theorem Check049.part6368 : Interval test 6368 6384 :=
  interval_of_check _ 6368 16 (by decide +kernel)
theorem Check049.part6384 : Interval test 6384 6400 :=
  interval_of_check _ 6384 16 (by decide +kernel)
theorem Check049.checked : Interval test 6272 6400 :=
  (FiniteChecks.interval_append test 6272 6336 6400
  (FiniteChecks.interval_append test 6272 6304 6336
  (FiniteChecks.interval_append test 6272 6288 6304
  Check049.part6272
  Check049.part6288)
  (FiniteChecks.interval_append test 6304 6320 6336
  Check049.part6304
  Check049.part6320))
  (FiniteChecks.interval_append test 6336 6368 6400
  (FiniteChecks.interval_append test 6336 6352 6368
  Check049.part6336
  Check049.part6352)
  (FiniteChecks.interval_append test 6368 6384 6400
  Check049.part6368
  Check049.part6384)))
#print axioms Check049.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check050.part6400 : Interval test 6400 6416 :=
  interval_of_check _ 6400 16 (by decide +kernel)
theorem Check050.part6416 : Interval test 6416 6432 :=
  interval_of_check _ 6416 16 (by decide +kernel)
theorem Check050.part6432 : Interval test 6432 6448 :=
  interval_of_check _ 6432 16 (by decide +kernel)
theorem Check050.part6448 : Interval test 6448 6464 :=
  interval_of_check _ 6448 16 (by decide +kernel)
theorem Check050.part6464 : Interval test 6464 6480 :=
  interval_of_check _ 6464 16 (by decide +kernel)
theorem Check050.part6480 : Interval test 6480 6496 :=
  interval_of_check _ 6480 16 (by decide +kernel)
theorem Check050.part6496 : Interval test 6496 6512 :=
  interval_of_check _ 6496 16 (by decide +kernel)
theorem Check050.part6512 : Interval test 6512 6528 :=
  interval_of_check _ 6512 16 (by decide +kernel)
theorem Check050.checked : Interval test 6400 6528 :=
  (FiniteChecks.interval_append test 6400 6464 6528
  (FiniteChecks.interval_append test 6400 6432 6464
  (FiniteChecks.interval_append test 6400 6416 6432
  Check050.part6400
  Check050.part6416)
  (FiniteChecks.interval_append test 6432 6448 6464
  Check050.part6432
  Check050.part6448))
  (FiniteChecks.interval_append test 6464 6496 6528
  (FiniteChecks.interval_append test 6464 6480 6496
  Check050.part6464
  Check050.part6480)
  (FiniteChecks.interval_append test 6496 6512 6528
  Check050.part6496
  Check050.part6512)))
#print axioms Check050.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check051.part6528 : Interval test 6528 6544 :=
  interval_of_check _ 6528 16 (by decide +kernel)
theorem Check051.part6544 : Interval test 6544 6560 :=
  interval_of_check _ 6544 16 (by decide +kernel)
theorem Check051.part6560 : Interval test 6560 6576 :=
  interval_of_check _ 6560 16 (by decide +kernel)
theorem Check051.part6576 : Interval test 6576 6592 :=
  interval_of_check _ 6576 16 (by decide +kernel)
theorem Check051.part6592 : Interval test 6592 6608 :=
  interval_of_check _ 6592 16 (by decide +kernel)
theorem Check051.part6608 : Interval test 6608 6624 :=
  interval_of_check _ 6608 16 (by decide +kernel)
theorem Check051.part6624 : Interval test 6624 6640 :=
  interval_of_check _ 6624 16 (by decide +kernel)
theorem Check051.part6640 : Interval test 6640 6656 :=
  interval_of_check _ 6640 16 (by decide +kernel)
theorem Check051.checked : Interval test 6528 6656 :=
  (FiniteChecks.interval_append test 6528 6592 6656
  (FiniteChecks.interval_append test 6528 6560 6592
  (FiniteChecks.interval_append test 6528 6544 6560
  Check051.part6528
  Check051.part6544)
  (FiniteChecks.interval_append test 6560 6576 6592
  Check051.part6560
  Check051.part6576))
  (FiniteChecks.interval_append test 6592 6624 6656
  (FiniteChecks.interval_append test 6592 6608 6624
  Check051.part6592
  Check051.part6608)
  (FiniteChecks.interval_append test 6624 6640 6656
  Check051.part6624
  Check051.part6640)))
#print axioms Check051.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check052.part6656 : Interval test 6656 6672 :=
  interval_of_check _ 6656 16 (by decide +kernel)
theorem Check052.part6672 : Interval test 6672 6688 :=
  interval_of_check _ 6672 16 (by decide +kernel)
theorem Check052.part6688 : Interval test 6688 6704 :=
  interval_of_check _ 6688 16 (by decide +kernel)
theorem Check052.part6704 : Interval test 6704 6720 :=
  interval_of_check _ 6704 16 (by decide +kernel)
theorem Check052.part6720 : Interval test 6720 6736 :=
  interval_of_check _ 6720 16 (by decide +kernel)
theorem Check052.part6736 : Interval test 6736 6752 :=
  interval_of_check _ 6736 16 (by decide +kernel)
theorem Check052.part6752 : Interval test 6752 6768 :=
  interval_of_check _ 6752 16 (by decide +kernel)
theorem Check052.part6768 : Interval test 6768 6784 :=
  interval_of_check _ 6768 16 (by decide +kernel)
theorem Check052.checked : Interval test 6656 6784 :=
  (FiniteChecks.interval_append test 6656 6720 6784
  (FiniteChecks.interval_append test 6656 6688 6720
  (FiniteChecks.interval_append test 6656 6672 6688
  Check052.part6656
  Check052.part6672)
  (FiniteChecks.interval_append test 6688 6704 6720
  Check052.part6688
  Check052.part6704))
  (FiniteChecks.interval_append test 6720 6752 6784
  (FiniteChecks.interval_append test 6720 6736 6752
  Check052.part6720
  Check052.part6736)
  (FiniteChecks.interval_append test 6752 6768 6784
  Check052.part6752
  Check052.part6768)))
#print axioms Check052.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check053.part6784 : Interval test 6784 6800 :=
  interval_of_check _ 6784 16 (by decide +kernel)
theorem Check053.part6800 : Interval test 6800 6816 :=
  interval_of_check _ 6800 16 (by decide +kernel)
theorem Check053.part6816 : Interval test 6816 6832 :=
  interval_of_check _ 6816 16 (by decide +kernel)
theorem Check053.part6832 : Interval test 6832 6848 :=
  interval_of_check _ 6832 16 (by decide +kernel)
theorem Check053.part6848 : Interval test 6848 6864 :=
  interval_of_check _ 6848 16 (by decide +kernel)
theorem Check053.part6864 : Interval test 6864 6880 :=
  interval_of_check _ 6864 16 (by decide +kernel)
theorem Check053.part6880 : Interval test 6880 6896 :=
  interval_of_check _ 6880 16 (by decide +kernel)
theorem Check053.part6896 : Interval test 6896 6912 :=
  interval_of_check _ 6896 16 (by decide +kernel)
theorem Check053.checked : Interval test 6784 6912 :=
  (FiniteChecks.interval_append test 6784 6848 6912
  (FiniteChecks.interval_append test 6784 6816 6848
  (FiniteChecks.interval_append test 6784 6800 6816
  Check053.part6784
  Check053.part6800)
  (FiniteChecks.interval_append test 6816 6832 6848
  Check053.part6816
  Check053.part6832))
  (FiniteChecks.interval_append test 6848 6880 6912
  (FiniteChecks.interval_append test 6848 6864 6880
  Check053.part6848
  Check053.part6864)
  (FiniteChecks.interval_append test 6880 6896 6912
  Check053.part6880
  Check053.part6896)))
#print axioms Check053.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check054.part6912 : Interval test 6912 6928 :=
  interval_of_check _ 6912 16 (by decide +kernel)
theorem Check054.part6928 : Interval test 6928 6944 :=
  interval_of_check _ 6928 16 (by decide +kernel)
theorem Check054.part6944 : Interval test 6944 6960 :=
  interval_of_check _ 6944 16 (by decide +kernel)
theorem Check054.part6960 : Interval test 6960 6976 :=
  interval_of_check _ 6960 16 (by decide +kernel)
theorem Check054.part6976 : Interval test 6976 6992 :=
  interval_of_check _ 6976 16 (by decide +kernel)
theorem Check054.part6992 : Interval test 6992 7008 :=
  interval_of_check _ 6992 16 (by decide +kernel)
theorem Check054.part7008 : Interval test 7008 7024 :=
  interval_of_check _ 7008 16 (by decide +kernel)
theorem Check054.part7024 : Interval test 7024 7040 :=
  interval_of_check _ 7024 16 (by decide +kernel)
theorem Check054.checked : Interval test 6912 7040 :=
  (FiniteChecks.interval_append test 6912 6976 7040
  (FiniteChecks.interval_append test 6912 6944 6976
  (FiniteChecks.interval_append test 6912 6928 6944
  Check054.part6912
  Check054.part6928)
  (FiniteChecks.interval_append test 6944 6960 6976
  Check054.part6944
  Check054.part6960))
  (FiniteChecks.interval_append test 6976 7008 7040
  (FiniteChecks.interval_append test 6976 6992 7008
  Check054.part6976
  Check054.part6992)
  (FiniteChecks.interval_append test 7008 7024 7040
  Check054.part7008
  Check054.part7024)))
#print axioms Check054.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check055.part7040 : Interval test 7040 7056 :=
  interval_of_check _ 7040 16 (by decide +kernel)
theorem Check055.part7056 : Interval test 7056 7072 :=
  interval_of_check _ 7056 16 (by decide +kernel)
theorem Check055.part7072 : Interval test 7072 7088 :=
  interval_of_check _ 7072 16 (by decide +kernel)
theorem Check055.part7088 : Interval test 7088 7104 :=
  interval_of_check _ 7088 16 (by decide +kernel)
theorem Check055.part7104 : Interval test 7104 7120 :=
  interval_of_check _ 7104 16 (by decide +kernel)
theorem Check055.part7120 : Interval test 7120 7136 :=
  interval_of_check _ 7120 16 (by decide +kernel)
theorem Check055.part7136 : Interval test 7136 7152 :=
  interval_of_check _ 7136 16 (by decide +kernel)
theorem Check055.part7152 : Interval test 7152 7168 :=
  interval_of_check _ 7152 16 (by decide +kernel)
theorem Check055.checked : Interval test 7040 7168 :=
  (FiniteChecks.interval_append test 7040 7104 7168
  (FiniteChecks.interval_append test 7040 7072 7104
  (FiniteChecks.interval_append test 7040 7056 7072
  Check055.part7040
  Check055.part7056)
  (FiniteChecks.interval_append test 7072 7088 7104
  Check055.part7072
  Check055.part7088))
  (FiniteChecks.interval_append test 7104 7136 7168
  (FiniteChecks.interval_append test 7104 7120 7136
  Check055.part7104
  Check055.part7120)
  (FiniteChecks.interval_append test 7136 7152 7168
  Check055.part7136
  Check055.part7152)))
#print axioms Check055.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check056.part7168 : Interval test 7168 7184 :=
  interval_of_check _ 7168 16 (by decide +kernel)
theorem Check056.part7184 : Interval test 7184 7200 :=
  interval_of_check _ 7184 16 (by decide +kernel)
theorem Check056.part7200 : Interval test 7200 7216 :=
  interval_of_check _ 7200 16 (by decide +kernel)
theorem Check056.part7216 : Interval test 7216 7232 :=
  interval_of_check _ 7216 16 (by decide +kernel)
theorem Check056.part7232 : Interval test 7232 7248 :=
  interval_of_check _ 7232 16 (by decide +kernel)
theorem Check056.part7248 : Interval test 7248 7264 :=
  interval_of_check _ 7248 16 (by decide +kernel)
theorem Check056.part7264 : Interval test 7264 7280 :=
  interval_of_check _ 7264 16 (by decide +kernel)
theorem Check056.part7280 : Interval test 7280 7296 :=
  interval_of_check _ 7280 16 (by decide +kernel)
theorem Check056.checked : Interval test 7168 7296 :=
  (FiniteChecks.interval_append test 7168 7232 7296
  (FiniteChecks.interval_append test 7168 7200 7232
  (FiniteChecks.interval_append test 7168 7184 7200
  Check056.part7168
  Check056.part7184)
  (FiniteChecks.interval_append test 7200 7216 7232
  Check056.part7200
  Check056.part7216))
  (FiniteChecks.interval_append test 7232 7264 7296
  (FiniteChecks.interval_append test 7232 7248 7264
  Check056.part7232
  Check056.part7248)
  (FiniteChecks.interval_append test 7264 7280 7296
  Check056.part7264
  Check056.part7280)))
#print axioms Check056.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check057.part7296 : Interval test 7296 7312 :=
  interval_of_check _ 7296 16 (by decide +kernel)
theorem Check057.part7312 : Interval test 7312 7328 :=
  interval_of_check _ 7312 16 (by decide +kernel)
theorem Check057.part7328 : Interval test 7328 7344 :=
  interval_of_check _ 7328 16 (by decide +kernel)
theorem Check057.part7344 : Interval test 7344 7360 :=
  interval_of_check _ 7344 16 (by decide +kernel)
theorem Check057.part7360 : Interval test 7360 7376 :=
  interval_of_check _ 7360 16 (by decide +kernel)
theorem Check057.part7376 : Interval test 7376 7392 :=
  interval_of_check _ 7376 16 (by decide +kernel)
theorem Check057.part7392 : Interval test 7392 7408 :=
  interval_of_check _ 7392 16 (by decide +kernel)
theorem Check057.part7408 : Interval test 7408 7424 :=
  interval_of_check _ 7408 16 (by decide +kernel)
theorem Check057.checked : Interval test 7296 7424 :=
  (FiniteChecks.interval_append test 7296 7360 7424
  (FiniteChecks.interval_append test 7296 7328 7360
  (FiniteChecks.interval_append test 7296 7312 7328
  Check057.part7296
  Check057.part7312)
  (FiniteChecks.interval_append test 7328 7344 7360
  Check057.part7328
  Check057.part7344))
  (FiniteChecks.interval_append test 7360 7392 7424
  (FiniteChecks.interval_append test 7360 7376 7392
  Check057.part7360
  Check057.part7376)
  (FiniteChecks.interval_append test 7392 7408 7424
  Check057.part7392
  Check057.part7408)))
#print axioms Check057.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check058.part7424 : Interval test 7424 7440 :=
  interval_of_check _ 7424 16 (by decide +kernel)
theorem Check058.part7440 : Interval test 7440 7456 :=
  interval_of_check _ 7440 16 (by decide +kernel)
theorem Check058.part7456 : Interval test 7456 7472 :=
  interval_of_check _ 7456 16 (by decide +kernel)
theorem Check058.part7472 : Interval test 7472 7488 :=
  interval_of_check _ 7472 16 (by decide +kernel)
theorem Check058.part7488 : Interval test 7488 7504 :=
  interval_of_check _ 7488 16 (by decide +kernel)
theorem Check058.part7504 : Interval test 7504 7520 :=
  interval_of_check _ 7504 16 (by decide +kernel)
theorem Check058.part7520 : Interval test 7520 7536 :=
  interval_of_check _ 7520 16 (by decide +kernel)
theorem Check058.part7536 : Interval test 7536 7552 :=
  interval_of_check _ 7536 16 (by decide +kernel)
theorem Check058.checked : Interval test 7424 7552 :=
  (FiniteChecks.interval_append test 7424 7488 7552
  (FiniteChecks.interval_append test 7424 7456 7488
  (FiniteChecks.interval_append test 7424 7440 7456
  Check058.part7424
  Check058.part7440)
  (FiniteChecks.interval_append test 7456 7472 7488
  Check058.part7456
  Check058.part7472))
  (FiniteChecks.interval_append test 7488 7520 7552
  (FiniteChecks.interval_append test 7488 7504 7520
  Check058.part7488
  Check058.part7504)
  (FiniteChecks.interval_append test 7520 7536 7552
  Check058.part7520
  Check058.part7536)))
#print axioms Check058.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check059.part7552 : Interval test 7552 7568 :=
  interval_of_check _ 7552 16 (by decide +kernel)
theorem Check059.part7568 : Interval test 7568 7584 :=
  interval_of_check _ 7568 16 (by decide +kernel)
theorem Check059.part7584 : Interval test 7584 7600 :=
  interval_of_check _ 7584 16 (by decide +kernel)
theorem Check059.part7600 : Interval test 7600 7616 :=
  interval_of_check _ 7600 16 (by decide +kernel)
theorem Check059.part7616 : Interval test 7616 7632 :=
  interval_of_check _ 7616 16 (by decide +kernel)
theorem Check059.part7632 : Interval test 7632 7648 :=
  interval_of_check _ 7632 16 (by decide +kernel)
theorem Check059.part7648 : Interval test 7648 7664 :=
  interval_of_check _ 7648 16 (by decide +kernel)
theorem Check059.part7664 : Interval test 7664 7680 :=
  interval_of_check _ 7664 16 (by decide +kernel)
theorem Check059.checked : Interval test 7552 7680 :=
  (FiniteChecks.interval_append test 7552 7616 7680
  (FiniteChecks.interval_append test 7552 7584 7616
  (FiniteChecks.interval_append test 7552 7568 7584
  Check059.part7552
  Check059.part7568)
  (FiniteChecks.interval_append test 7584 7600 7616
  Check059.part7584
  Check059.part7600))
  (FiniteChecks.interval_append test 7616 7648 7680
  (FiniteChecks.interval_append test 7616 7632 7648
  Check059.part7616
  Check059.part7632)
  (FiniteChecks.interval_append test 7648 7664 7680
  Check059.part7648
  Check059.part7664)))
#print axioms Check059.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
