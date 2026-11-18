module
prelude
public import SharedSix0IncidenceData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check020.part5120 : Interval test 5120 5136 :=
  interval_of_check _ 5120 16 (by decide +kernel)
theorem Check020.part5136 : Interval test 5136 5152 :=
  interval_of_check _ 5136 16 (by decide +kernel)
theorem Check020.part5152 : Interval test 5152 5168 :=
  interval_of_check _ 5152 16 (by decide +kernel)
theorem Check020.part5168 : Interval test 5168 5184 :=
  interval_of_check _ 5168 16 (by decide +kernel)
theorem Check020.part5184 : Interval test 5184 5200 :=
  interval_of_check _ 5184 16 (by decide +kernel)
theorem Check020.part5200 : Interval test 5200 5216 :=
  interval_of_check _ 5200 16 (by decide +kernel)
theorem Check020.part5216 : Interval test 5216 5232 :=
  interval_of_check _ 5216 16 (by decide +kernel)
theorem Check020.part5232 : Interval test 5232 5248 :=
  interval_of_check _ 5232 16 (by decide +kernel)
theorem Check020.part5248 : Interval test 5248 5264 :=
  interval_of_check _ 5248 16 (by decide +kernel)
theorem Check020.part5264 : Interval test 5264 5280 :=
  interval_of_check _ 5264 16 (by decide +kernel)
theorem Check020.part5280 : Interval test 5280 5296 :=
  interval_of_check _ 5280 16 (by decide +kernel)
theorem Check020.part5296 : Interval test 5296 5312 :=
  interval_of_check _ 5296 16 (by decide +kernel)
theorem Check020.part5312 : Interval test 5312 5328 :=
  interval_of_check _ 5312 16 (by decide +kernel)
theorem Check020.part5328 : Interval test 5328 5344 :=
  interval_of_check _ 5328 16 (by decide +kernel)
theorem Check020.part5344 : Interval test 5344 5360 :=
  interval_of_check _ 5344 16 (by decide +kernel)
theorem Check020.part5360 : Interval test 5360 5376 :=
  interval_of_check _ 5360 16 (by decide +kernel)
theorem Check020.checked : Interval test 5120 5376 :=
  (FiniteChecks.interval_append test 5120 5248 5376
  (FiniteChecks.interval_append test 5120 5184 5248
  (FiniteChecks.interval_append test 5120 5152 5184
  (FiniteChecks.interval_append test 5120 5136 5152
  Check020.part5120
  Check020.part5136)
  (FiniteChecks.interval_append test 5152 5168 5184
  Check020.part5152
  Check020.part5168))
  (FiniteChecks.interval_append test 5184 5216 5248
  (FiniteChecks.interval_append test 5184 5200 5216
  Check020.part5184
  Check020.part5200)
  (FiniteChecks.interval_append test 5216 5232 5248
  Check020.part5216
  Check020.part5232)))
  (FiniteChecks.interval_append test 5248 5312 5376
  (FiniteChecks.interval_append test 5248 5280 5312
  (FiniteChecks.interval_append test 5248 5264 5280
  Check020.part5248
  Check020.part5264)
  (FiniteChecks.interval_append test 5280 5296 5312
  Check020.part5280
  Check020.part5296))
  (FiniteChecks.interval_append test 5312 5344 5376
  (FiniteChecks.interval_append test 5312 5328 5344
  Check020.part5312
  Check020.part5328)
  (FiniteChecks.interval_append test 5344 5360 5376
  Check020.part5344
  Check020.part5360))))
#print axioms Check020.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check021.part5376 : Interval test 5376 5392 :=
  interval_of_check _ 5376 16 (by decide +kernel)
theorem Check021.part5392 : Interval test 5392 5408 :=
  interval_of_check _ 5392 16 (by decide +kernel)
theorem Check021.part5408 : Interval test 5408 5424 :=
  interval_of_check _ 5408 16 (by decide +kernel)
theorem Check021.part5424 : Interval test 5424 5440 :=
  interval_of_check _ 5424 16 (by decide +kernel)
theorem Check021.part5440 : Interval test 5440 5456 :=
  interval_of_check _ 5440 16 (by decide +kernel)
theorem Check021.part5456 : Interval test 5456 5472 :=
  interval_of_check _ 5456 16 (by decide +kernel)
theorem Check021.part5472 : Interval test 5472 5488 :=
  interval_of_check _ 5472 16 (by decide +kernel)
theorem Check021.part5488 : Interval test 5488 5504 :=
  interval_of_check _ 5488 16 (by decide +kernel)
theorem Check021.part5504 : Interval test 5504 5520 :=
  interval_of_check _ 5504 16 (by decide +kernel)
theorem Check021.part5520 : Interval test 5520 5536 :=
  interval_of_check _ 5520 16 (by decide +kernel)
theorem Check021.part5536 : Interval test 5536 5552 :=
  interval_of_check _ 5536 16 (by decide +kernel)
theorem Check021.part5552 : Interval test 5552 5568 :=
  interval_of_check _ 5552 16 (by decide +kernel)
theorem Check021.part5568 : Interval test 5568 5584 :=
  interval_of_check _ 5568 16 (by decide +kernel)
theorem Check021.part5584 : Interval test 5584 5600 :=
  interval_of_check _ 5584 16 (by decide +kernel)
theorem Check021.part5600 : Interval test 5600 5616 :=
  interval_of_check _ 5600 16 (by decide +kernel)
theorem Check021.part5616 : Interval test 5616 5632 :=
  interval_of_check _ 5616 16 (by decide +kernel)
theorem Check021.checked : Interval test 5376 5632 :=
  (FiniteChecks.interval_append test 5376 5504 5632
  (FiniteChecks.interval_append test 5376 5440 5504
  (FiniteChecks.interval_append test 5376 5408 5440
  (FiniteChecks.interval_append test 5376 5392 5408
  Check021.part5376
  Check021.part5392)
  (FiniteChecks.interval_append test 5408 5424 5440
  Check021.part5408
  Check021.part5424))
  (FiniteChecks.interval_append test 5440 5472 5504
  (FiniteChecks.interval_append test 5440 5456 5472
  Check021.part5440
  Check021.part5456)
  (FiniteChecks.interval_append test 5472 5488 5504
  Check021.part5472
  Check021.part5488)))
  (FiniteChecks.interval_append test 5504 5568 5632
  (FiniteChecks.interval_append test 5504 5536 5568
  (FiniteChecks.interval_append test 5504 5520 5536
  Check021.part5504
  Check021.part5520)
  (FiniteChecks.interval_append test 5536 5552 5568
  Check021.part5536
  Check021.part5552))
  (FiniteChecks.interval_append test 5568 5600 5632
  (FiniteChecks.interval_append test 5568 5584 5600
  Check021.part5568
  Check021.part5584)
  (FiniteChecks.interval_append test 5600 5616 5632
  Check021.part5600
  Check021.part5616))))
#print axioms Check021.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check022.part5632 : Interval test 5632 5648 :=
  interval_of_check _ 5632 16 (by decide +kernel)
theorem Check022.part5648 : Interval test 5648 5664 :=
  interval_of_check _ 5648 16 (by decide +kernel)
theorem Check022.part5664 : Interval test 5664 5680 :=
  interval_of_check _ 5664 16 (by decide +kernel)
theorem Check022.part5680 : Interval test 5680 5696 :=
  interval_of_check _ 5680 16 (by decide +kernel)
theorem Check022.part5696 : Interval test 5696 5712 :=
  interval_of_check _ 5696 16 (by decide +kernel)
theorem Check022.part5712 : Interval test 5712 5728 :=
  interval_of_check _ 5712 16 (by decide +kernel)
theorem Check022.part5728 : Interval test 5728 5744 :=
  interval_of_check _ 5728 16 (by decide +kernel)
theorem Check022.part5744 : Interval test 5744 5760 :=
  interval_of_check _ 5744 16 (by decide +kernel)
theorem Check022.part5760 : Interval test 5760 5776 :=
  interval_of_check _ 5760 16 (by decide +kernel)
theorem Check022.part5776 : Interval test 5776 5792 :=
  interval_of_check _ 5776 16 (by decide +kernel)
theorem Check022.part5792 : Interval test 5792 5808 :=
  interval_of_check _ 5792 16 (by decide +kernel)
theorem Check022.part5808 : Interval test 5808 5824 :=
  interval_of_check _ 5808 16 (by decide +kernel)
theorem Check022.part5824 : Interval test 5824 5840 :=
  interval_of_check _ 5824 16 (by decide +kernel)
theorem Check022.part5840 : Interval test 5840 5856 :=
  interval_of_check _ 5840 16 (by decide +kernel)
theorem Check022.part5856 : Interval test 5856 5872 :=
  interval_of_check _ 5856 16 (by decide +kernel)
theorem Check022.part5872 : Interval test 5872 5888 :=
  interval_of_check _ 5872 16 (by decide +kernel)
theorem Check022.checked : Interval test 5632 5888 :=
  (FiniteChecks.interval_append test 5632 5760 5888
  (FiniteChecks.interval_append test 5632 5696 5760
  (FiniteChecks.interval_append test 5632 5664 5696
  (FiniteChecks.interval_append test 5632 5648 5664
  Check022.part5632
  Check022.part5648)
  (FiniteChecks.interval_append test 5664 5680 5696
  Check022.part5664
  Check022.part5680))
  (FiniteChecks.interval_append test 5696 5728 5760
  (FiniteChecks.interval_append test 5696 5712 5728
  Check022.part5696
  Check022.part5712)
  (FiniteChecks.interval_append test 5728 5744 5760
  Check022.part5728
  Check022.part5744)))
  (FiniteChecks.interval_append test 5760 5824 5888
  (FiniteChecks.interval_append test 5760 5792 5824
  (FiniteChecks.interval_append test 5760 5776 5792
  Check022.part5760
  Check022.part5776)
  (FiniteChecks.interval_append test 5792 5808 5824
  Check022.part5792
  Check022.part5808))
  (FiniteChecks.interval_append test 5824 5856 5888
  (FiniteChecks.interval_append test 5824 5840 5856
  Check022.part5824
  Check022.part5840)
  (FiniteChecks.interval_append test 5856 5872 5888
  Check022.part5856
  Check022.part5872))))
#print axioms Check022.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check023.part5888 : Interval test 5888 5904 :=
  interval_of_check _ 5888 16 (by decide +kernel)
theorem Check023.part5904 : Interval test 5904 5920 :=
  interval_of_check _ 5904 16 (by decide +kernel)
theorem Check023.part5920 : Interval test 5920 5936 :=
  interval_of_check _ 5920 16 (by decide +kernel)
theorem Check023.part5936 : Interval test 5936 5952 :=
  interval_of_check _ 5936 16 (by decide +kernel)
theorem Check023.part5952 : Interval test 5952 5968 :=
  interval_of_check _ 5952 16 (by decide +kernel)
theorem Check023.part5968 : Interval test 5968 5984 :=
  interval_of_check _ 5968 16 (by decide +kernel)
theorem Check023.part5984 : Interval test 5984 6000 :=
  interval_of_check _ 5984 16 (by decide +kernel)
theorem Check023.part6000 : Interval test 6000 6016 :=
  interval_of_check _ 6000 16 (by decide +kernel)
theorem Check023.part6016 : Interval test 6016 6032 :=
  interval_of_check _ 6016 16 (by decide +kernel)
theorem Check023.part6032 : Interval test 6032 6048 :=
  interval_of_check _ 6032 16 (by decide +kernel)
theorem Check023.part6048 : Interval test 6048 6064 :=
  interval_of_check _ 6048 16 (by decide +kernel)
theorem Check023.part6064 : Interval test 6064 6080 :=
  interval_of_check _ 6064 16 (by decide +kernel)
theorem Check023.part6080 : Interval test 6080 6096 :=
  interval_of_check _ 6080 16 (by decide +kernel)
theorem Check023.part6096 : Interval test 6096 6112 :=
  interval_of_check _ 6096 16 (by decide +kernel)
theorem Check023.part6112 : Interval test 6112 6128 :=
  interval_of_check _ 6112 16 (by decide +kernel)
theorem Check023.part6128 : Interval test 6128 6144 :=
  interval_of_check _ 6128 16 (by decide +kernel)
theorem Check023.checked : Interval test 5888 6144 :=
  (FiniteChecks.interval_append test 5888 6016 6144
  (FiniteChecks.interval_append test 5888 5952 6016
  (FiniteChecks.interval_append test 5888 5920 5952
  (FiniteChecks.interval_append test 5888 5904 5920
  Check023.part5888
  Check023.part5904)
  (FiniteChecks.interval_append test 5920 5936 5952
  Check023.part5920
  Check023.part5936))
  (FiniteChecks.interval_append test 5952 5984 6016
  (FiniteChecks.interval_append test 5952 5968 5984
  Check023.part5952
  Check023.part5968)
  (FiniteChecks.interval_append test 5984 6000 6016
  Check023.part5984
  Check023.part6000)))
  (FiniteChecks.interval_append test 6016 6080 6144
  (FiniteChecks.interval_append test 6016 6048 6080
  (FiniteChecks.interval_append test 6016 6032 6048
  Check023.part6016
  Check023.part6032)
  (FiniteChecks.interval_append test 6048 6064 6080
  Check023.part6048
  Check023.part6064))
  (FiniteChecks.interval_append test 6080 6112 6144
  (FiniteChecks.interval_append test 6080 6096 6112
  Check023.part6080
  Check023.part6096)
  (FiniteChecks.interval_append test 6112 6128 6144
  Check023.part6112
  Check023.part6128))))
#print axioms Check023.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check024.part6144 : Interval test 6144 6160 :=
  interval_of_check _ 6144 16 (by decide +kernel)
theorem Check024.part6160 : Interval test 6160 6176 :=
  interval_of_check _ 6160 16 (by decide +kernel)
theorem Check024.part6176 : Interval test 6176 6192 :=
  interval_of_check _ 6176 16 (by decide +kernel)
theorem Check024.part6192 : Interval test 6192 6208 :=
  interval_of_check _ 6192 16 (by decide +kernel)
theorem Check024.part6208 : Interval test 6208 6224 :=
  interval_of_check _ 6208 16 (by decide +kernel)
theorem Check024.part6224 : Interval test 6224 6240 :=
  interval_of_check _ 6224 16 (by decide +kernel)
theorem Check024.part6240 : Interval test 6240 6256 :=
  interval_of_check _ 6240 16 (by decide +kernel)
theorem Check024.part6256 : Interval test 6256 6272 :=
  interval_of_check _ 6256 16 (by decide +kernel)
theorem Check024.part6272 : Interval test 6272 6288 :=
  interval_of_check _ 6272 16 (by decide +kernel)
theorem Check024.part6288 : Interval test 6288 6304 :=
  interval_of_check _ 6288 16 (by decide +kernel)
theorem Check024.part6304 : Interval test 6304 6320 :=
  interval_of_check _ 6304 16 (by decide +kernel)
theorem Check024.part6320 : Interval test 6320 6336 :=
  interval_of_check _ 6320 16 (by decide +kernel)
theorem Check024.part6336 : Interval test 6336 6352 :=
  interval_of_check _ 6336 16 (by decide +kernel)
theorem Check024.part6352 : Interval test 6352 6368 :=
  interval_of_check _ 6352 16 (by decide +kernel)
theorem Check024.part6368 : Interval test 6368 6384 :=
  interval_of_check _ 6368 16 (by decide +kernel)
theorem Check024.part6384 : Interval test 6384 6400 :=
  interval_of_check _ 6384 16 (by decide +kernel)
theorem Check024.checked : Interval test 6144 6400 :=
  (FiniteChecks.interval_append test 6144 6272 6400
  (FiniteChecks.interval_append test 6144 6208 6272
  (FiniteChecks.interval_append test 6144 6176 6208
  (FiniteChecks.interval_append test 6144 6160 6176
  Check024.part6144
  Check024.part6160)
  (FiniteChecks.interval_append test 6176 6192 6208
  Check024.part6176
  Check024.part6192))
  (FiniteChecks.interval_append test 6208 6240 6272
  (FiniteChecks.interval_append test 6208 6224 6240
  Check024.part6208
  Check024.part6224)
  (FiniteChecks.interval_append test 6240 6256 6272
  Check024.part6240
  Check024.part6256)))
  (FiniteChecks.interval_append test 6272 6336 6400
  (FiniteChecks.interval_append test 6272 6304 6336
  (FiniteChecks.interval_append test 6272 6288 6304
  Check024.part6272
  Check024.part6288)
  (FiniteChecks.interval_append test 6304 6320 6336
  Check024.part6304
  Check024.part6320))
  (FiniteChecks.interval_append test 6336 6368 6400
  (FiniteChecks.interval_append test 6336 6352 6368
  Check024.part6336
  Check024.part6352)
  (FiniteChecks.interval_append test 6368 6384 6400
  Check024.part6368
  Check024.part6384))))
#print axioms Check024.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check025.part6400 : Interval test 6400 6416 :=
  interval_of_check _ 6400 16 (by decide +kernel)
theorem Check025.part6416 : Interval test 6416 6432 :=
  interval_of_check _ 6416 16 (by decide +kernel)
theorem Check025.part6432 : Interval test 6432 6448 :=
  interval_of_check _ 6432 16 (by decide +kernel)
theorem Check025.part6448 : Interval test 6448 6464 :=
  interval_of_check _ 6448 16 (by decide +kernel)
theorem Check025.part6464 : Interval test 6464 6480 :=
  interval_of_check _ 6464 16 (by decide +kernel)
theorem Check025.part6480 : Interval test 6480 6496 :=
  interval_of_check _ 6480 16 (by decide +kernel)
theorem Check025.part6496 : Interval test 6496 6512 :=
  interval_of_check _ 6496 16 (by decide +kernel)
theorem Check025.part6512 : Interval test 6512 6528 :=
  interval_of_check _ 6512 16 (by decide +kernel)
theorem Check025.part6528 : Interval test 6528 6544 :=
  interval_of_check _ 6528 16 (by decide +kernel)
theorem Check025.part6544 : Interval test 6544 6560 :=
  interval_of_check _ 6544 16 (by decide +kernel)
theorem Check025.part6560 : Interval test 6560 6576 :=
  interval_of_check _ 6560 16 (by decide +kernel)
theorem Check025.part6576 : Interval test 6576 6592 :=
  interval_of_check _ 6576 16 (by decide +kernel)
theorem Check025.part6592 : Interval test 6592 6608 :=
  interval_of_check _ 6592 16 (by decide +kernel)
theorem Check025.part6608 : Interval test 6608 6624 :=
  interval_of_check _ 6608 16 (by decide +kernel)
theorem Check025.part6624 : Interval test 6624 6640 :=
  interval_of_check _ 6624 16 (by decide +kernel)
theorem Check025.part6640 : Interval test 6640 6656 :=
  interval_of_check _ 6640 16 (by decide +kernel)
theorem Check025.checked : Interval test 6400 6656 :=
  (FiniteChecks.interval_append test 6400 6528 6656
  (FiniteChecks.interval_append test 6400 6464 6528
  (FiniteChecks.interval_append test 6400 6432 6464
  (FiniteChecks.interval_append test 6400 6416 6432
  Check025.part6400
  Check025.part6416)
  (FiniteChecks.interval_append test 6432 6448 6464
  Check025.part6432
  Check025.part6448))
  (FiniteChecks.interval_append test 6464 6496 6528
  (FiniteChecks.interval_append test 6464 6480 6496
  Check025.part6464
  Check025.part6480)
  (FiniteChecks.interval_append test 6496 6512 6528
  Check025.part6496
  Check025.part6512)))
  (FiniteChecks.interval_append test 6528 6592 6656
  (FiniteChecks.interval_append test 6528 6560 6592
  (FiniteChecks.interval_append test 6528 6544 6560
  Check025.part6528
  Check025.part6544)
  (FiniteChecks.interval_append test 6560 6576 6592
  Check025.part6560
  Check025.part6576))
  (FiniteChecks.interval_append test 6592 6624 6656
  (FiniteChecks.interval_append test 6592 6608 6624
  Check025.part6592
  Check025.part6608)
  (FiniteChecks.interval_append test 6624 6640 6656
  Check025.part6624
  Check025.part6640))))
#print axioms Check025.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check026.part6656 : Interval test 6656 6672 :=
  interval_of_check _ 6656 16 (by decide +kernel)
theorem Check026.part6672 : Interval test 6672 6688 :=
  interval_of_check _ 6672 16 (by decide +kernel)
theorem Check026.part6688 : Interval test 6688 6704 :=
  interval_of_check _ 6688 16 (by decide +kernel)
theorem Check026.part6704 : Interval test 6704 6720 :=
  interval_of_check _ 6704 16 (by decide +kernel)
theorem Check026.part6720 : Interval test 6720 6736 :=
  interval_of_check _ 6720 16 (by decide +kernel)
theorem Check026.part6736 : Interval test 6736 6752 :=
  interval_of_check _ 6736 16 (by decide +kernel)
theorem Check026.part6752 : Interval test 6752 6768 :=
  interval_of_check _ 6752 16 (by decide +kernel)
theorem Check026.part6768 : Interval test 6768 6784 :=
  interval_of_check _ 6768 16 (by decide +kernel)
theorem Check026.part6784 : Interval test 6784 6800 :=
  interval_of_check _ 6784 16 (by decide +kernel)
theorem Check026.part6800 : Interval test 6800 6816 :=
  interval_of_check _ 6800 16 (by decide +kernel)
theorem Check026.part6816 : Interval test 6816 6832 :=
  interval_of_check _ 6816 16 (by decide +kernel)
theorem Check026.part6832 : Interval test 6832 6848 :=
  interval_of_check _ 6832 16 (by decide +kernel)
theorem Check026.part6848 : Interval test 6848 6864 :=
  interval_of_check _ 6848 16 (by decide +kernel)
theorem Check026.part6864 : Interval test 6864 6880 :=
  interval_of_check _ 6864 16 (by decide +kernel)
theorem Check026.part6880 : Interval test 6880 6896 :=
  interval_of_check _ 6880 16 (by decide +kernel)
theorem Check026.part6896 : Interval test 6896 6912 :=
  interval_of_check _ 6896 16 (by decide +kernel)
theorem Check026.checked : Interval test 6656 6912 :=
  (FiniteChecks.interval_append test 6656 6784 6912
  (FiniteChecks.interval_append test 6656 6720 6784
  (FiniteChecks.interval_append test 6656 6688 6720
  (FiniteChecks.interval_append test 6656 6672 6688
  Check026.part6656
  Check026.part6672)
  (FiniteChecks.interval_append test 6688 6704 6720
  Check026.part6688
  Check026.part6704))
  (FiniteChecks.interval_append test 6720 6752 6784
  (FiniteChecks.interval_append test 6720 6736 6752
  Check026.part6720
  Check026.part6736)
  (FiniteChecks.interval_append test 6752 6768 6784
  Check026.part6752
  Check026.part6768)))
  (FiniteChecks.interval_append test 6784 6848 6912
  (FiniteChecks.interval_append test 6784 6816 6848
  (FiniteChecks.interval_append test 6784 6800 6816
  Check026.part6784
  Check026.part6800)
  (FiniteChecks.interval_append test 6816 6832 6848
  Check026.part6816
  Check026.part6832))
  (FiniteChecks.interval_append test 6848 6880 6912
  (FiniteChecks.interval_append test 6848 6864 6880
  Check026.part6848
  Check026.part6864)
  (FiniteChecks.interval_append test 6880 6896 6912
  Check026.part6880
  Check026.part6896))))
#print axioms Check026.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check027.part6912 : Interval test 6912 6928 :=
  interval_of_check _ 6912 16 (by decide +kernel)
theorem Check027.part6928 : Interval test 6928 6944 :=
  interval_of_check _ 6928 16 (by decide +kernel)
theorem Check027.part6944 : Interval test 6944 6960 :=
  interval_of_check _ 6944 16 (by decide +kernel)
theorem Check027.part6960 : Interval test 6960 6976 :=
  interval_of_check _ 6960 16 (by decide +kernel)
theorem Check027.part6976 : Interval test 6976 6992 :=
  interval_of_check _ 6976 16 (by decide +kernel)
theorem Check027.part6992 : Interval test 6992 7008 :=
  interval_of_check _ 6992 16 (by decide +kernel)
theorem Check027.part7008 : Interval test 7008 7024 :=
  interval_of_check _ 7008 16 (by decide +kernel)
theorem Check027.part7024 : Interval test 7024 7040 :=
  interval_of_check _ 7024 16 (by decide +kernel)
theorem Check027.part7040 : Interval test 7040 7056 :=
  interval_of_check _ 7040 16 (by decide +kernel)
theorem Check027.part7056 : Interval test 7056 7072 :=
  interval_of_check _ 7056 16 (by decide +kernel)
theorem Check027.part7072 : Interval test 7072 7088 :=
  interval_of_check _ 7072 16 (by decide +kernel)
theorem Check027.part7088 : Interval test 7088 7104 :=
  interval_of_check _ 7088 16 (by decide +kernel)
theorem Check027.part7104 : Interval test 7104 7120 :=
  interval_of_check _ 7104 16 (by decide +kernel)
theorem Check027.part7120 : Interval test 7120 7136 :=
  interval_of_check _ 7120 16 (by decide +kernel)
theorem Check027.part7136 : Interval test 7136 7152 :=
  interval_of_check _ 7136 16 (by decide +kernel)
theorem Check027.part7152 : Interval test 7152 7168 :=
  interval_of_check _ 7152 16 (by decide +kernel)
theorem Check027.checked : Interval test 6912 7168 :=
  (FiniteChecks.interval_append test 6912 7040 7168
  (FiniteChecks.interval_append test 6912 6976 7040
  (FiniteChecks.interval_append test 6912 6944 6976
  (FiniteChecks.interval_append test 6912 6928 6944
  Check027.part6912
  Check027.part6928)
  (FiniteChecks.interval_append test 6944 6960 6976
  Check027.part6944
  Check027.part6960))
  (FiniteChecks.interval_append test 6976 7008 7040
  (FiniteChecks.interval_append test 6976 6992 7008
  Check027.part6976
  Check027.part6992)
  (FiniteChecks.interval_append test 7008 7024 7040
  Check027.part7008
  Check027.part7024)))
  (FiniteChecks.interval_append test 7040 7104 7168
  (FiniteChecks.interval_append test 7040 7072 7104
  (FiniteChecks.interval_append test 7040 7056 7072
  Check027.part7040
  Check027.part7056)
  (FiniteChecks.interval_append test 7072 7088 7104
  Check027.part7072
  Check027.part7088))
  (FiniteChecks.interval_append test 7104 7136 7168
  (FiniteChecks.interval_append test 7104 7120 7136
  Check027.part7104
  Check027.part7120)
  (FiniteChecks.interval_append test 7136 7152 7168
  Check027.part7136
  Check027.part7152))))
#print axioms Check027.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check028.part7168 : Interval test 7168 7184 :=
  interval_of_check _ 7168 16 (by decide +kernel)
theorem Check028.part7184 : Interval test 7184 7200 :=
  interval_of_check _ 7184 16 (by decide +kernel)
theorem Check028.part7200 : Interval test 7200 7216 :=
  interval_of_check _ 7200 16 (by decide +kernel)
theorem Check028.part7216 : Interval test 7216 7232 :=
  interval_of_check _ 7216 16 (by decide +kernel)
theorem Check028.part7232 : Interval test 7232 7248 :=
  interval_of_check _ 7232 16 (by decide +kernel)
theorem Check028.part7248 : Interval test 7248 7264 :=
  interval_of_check _ 7248 16 (by decide +kernel)
theorem Check028.part7264 : Interval test 7264 7280 :=
  interval_of_check _ 7264 16 (by decide +kernel)
theorem Check028.part7280 : Interval test 7280 7296 :=
  interval_of_check _ 7280 16 (by decide +kernel)
theorem Check028.part7296 : Interval test 7296 7312 :=
  interval_of_check _ 7296 16 (by decide +kernel)
theorem Check028.part7312 : Interval test 7312 7328 :=
  interval_of_check _ 7312 16 (by decide +kernel)
theorem Check028.part7328 : Interval test 7328 7344 :=
  interval_of_check _ 7328 16 (by decide +kernel)
theorem Check028.part7344 : Interval test 7344 7360 :=
  interval_of_check _ 7344 16 (by decide +kernel)
theorem Check028.part7360 : Interval test 7360 7376 :=
  interval_of_check _ 7360 16 (by decide +kernel)
theorem Check028.part7376 : Interval test 7376 7392 :=
  interval_of_check _ 7376 16 (by decide +kernel)
theorem Check028.part7392 : Interval test 7392 7408 :=
  interval_of_check _ 7392 16 (by decide +kernel)
theorem Check028.part7408 : Interval test 7408 7424 :=
  interval_of_check _ 7408 16 (by decide +kernel)
theorem Check028.checked : Interval test 7168 7424 :=
  (FiniteChecks.interval_append test 7168 7296 7424
  (FiniteChecks.interval_append test 7168 7232 7296
  (FiniteChecks.interval_append test 7168 7200 7232
  (FiniteChecks.interval_append test 7168 7184 7200
  Check028.part7168
  Check028.part7184)
  (FiniteChecks.interval_append test 7200 7216 7232
  Check028.part7200
  Check028.part7216))
  (FiniteChecks.interval_append test 7232 7264 7296
  (FiniteChecks.interval_append test 7232 7248 7264
  Check028.part7232
  Check028.part7248)
  (FiniteChecks.interval_append test 7264 7280 7296
  Check028.part7264
  Check028.part7280)))
  (FiniteChecks.interval_append test 7296 7360 7424
  (FiniteChecks.interval_append test 7296 7328 7360
  (FiniteChecks.interval_append test 7296 7312 7328
  Check028.part7296
  Check028.part7312)
  (FiniteChecks.interval_append test 7328 7344 7360
  Check028.part7328
  Check028.part7344))
  (FiniteChecks.interval_append test 7360 7392 7424
  (FiniteChecks.interval_append test 7360 7376 7392
  Check028.part7360
  Check028.part7376)
  (FiniteChecks.interval_append test 7392 7408 7424
  Check028.part7392
  Check028.part7408))))
#print axioms Check028.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check029.part7424 : Interval test 7424 7440 :=
  interval_of_check _ 7424 16 (by decide +kernel)
theorem Check029.part7440 : Interval test 7440 7456 :=
  interval_of_check _ 7440 16 (by decide +kernel)
theorem Check029.part7456 : Interval test 7456 7472 :=
  interval_of_check _ 7456 16 (by decide +kernel)
theorem Check029.part7472 : Interval test 7472 7488 :=
  interval_of_check _ 7472 16 (by decide +kernel)
theorem Check029.part7488 : Interval test 7488 7504 :=
  interval_of_check _ 7488 16 (by decide +kernel)
theorem Check029.part7504 : Interval test 7504 7520 :=
  interval_of_check _ 7504 16 (by decide +kernel)
theorem Check029.part7520 : Interval test 7520 7536 :=
  interval_of_check _ 7520 16 (by decide +kernel)
theorem Check029.part7536 : Interval test 7536 7552 :=
  interval_of_check _ 7536 16 (by decide +kernel)
theorem Check029.part7552 : Interval test 7552 7568 :=
  interval_of_check _ 7552 16 (by decide +kernel)
theorem Check029.part7568 : Interval test 7568 7584 :=
  interval_of_check _ 7568 16 (by decide +kernel)
theorem Check029.part7584 : Interval test 7584 7600 :=
  interval_of_check _ 7584 16 (by decide +kernel)
theorem Check029.part7600 : Interval test 7600 7616 :=
  interval_of_check _ 7600 16 (by decide +kernel)
theorem Check029.part7616 : Interval test 7616 7632 :=
  interval_of_check _ 7616 16 (by decide +kernel)
theorem Check029.part7632 : Interval test 7632 7648 :=
  interval_of_check _ 7632 16 (by decide +kernel)
theorem Check029.part7648 : Interval test 7648 7664 :=
  interval_of_check _ 7648 16 (by decide +kernel)
theorem Check029.part7664 : Interval test 7664 7680 :=
  interval_of_check _ 7664 16 (by decide +kernel)
theorem Check029.checked : Interval test 7424 7680 :=
  (FiniteChecks.interval_append test 7424 7552 7680
  (FiniteChecks.interval_append test 7424 7488 7552
  (FiniteChecks.interval_append test 7424 7456 7488
  (FiniteChecks.interval_append test 7424 7440 7456
  Check029.part7424
  Check029.part7440)
  (FiniteChecks.interval_append test 7456 7472 7488
  Check029.part7456
  Check029.part7472))
  (FiniteChecks.interval_append test 7488 7520 7552
  (FiniteChecks.interval_append test 7488 7504 7520
  Check029.part7488
  Check029.part7504)
  (FiniteChecks.interval_append test 7520 7536 7552
  Check029.part7520
  Check029.part7536)))
  (FiniteChecks.interval_append test 7552 7616 7680
  (FiniteChecks.interval_append test 7552 7584 7616
  (FiniteChecks.interval_append test 7552 7568 7584
  Check029.part7552
  Check029.part7568)
  (FiniteChecks.interval_append test 7584 7600 7616
  Check029.part7584
  Check029.part7600))
  (FiniteChecks.interval_append test 7616 7648 7680
  (FiniteChecks.interval_append test 7616 7632 7648
  Check029.part7616
  Check029.part7632)
  (FiniteChecks.interval_append test 7648 7664 7680
  Check029.part7648
  Check029.part7664))))
#print axioms Check029.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check030.part7680 : Interval test 7680 7696 :=
  interval_of_check _ 7680 16 (by decide +kernel)
theorem Check030.part7696 : Interval test 7696 7712 :=
  interval_of_check _ 7696 16 (by decide +kernel)
theorem Check030.part7712 : Interval test 7712 7728 :=
  interval_of_check _ 7712 16 (by decide +kernel)
theorem Check030.part7728 : Interval test 7728 7744 :=
  interval_of_check _ 7728 16 (by decide +kernel)
theorem Check030.part7744 : Interval test 7744 7760 :=
  interval_of_check _ 7744 16 (by decide +kernel)
theorem Check030.part7760 : Interval test 7760 7776 :=
  interval_of_check _ 7760 16 (by decide +kernel)
theorem Check030.part7776 : Interval test 7776 7792 :=
  interval_of_check _ 7776 16 (by decide +kernel)
theorem Check030.part7792 : Interval test 7792 7808 :=
  interval_of_check _ 7792 16 (by decide +kernel)
theorem Check030.part7808 : Interval test 7808 7824 :=
  interval_of_check _ 7808 16 (by decide +kernel)
theorem Check030.part7824 : Interval test 7824 7840 :=
  interval_of_check _ 7824 16 (by decide +kernel)
theorem Check030.part7840 : Interval test 7840 7856 :=
  interval_of_check _ 7840 16 (by decide +kernel)
theorem Check030.part7856 : Interval test 7856 7872 :=
  interval_of_check _ 7856 16 (by decide +kernel)
theorem Check030.part7872 : Interval test 7872 7888 :=
  interval_of_check _ 7872 16 (by decide +kernel)
theorem Check030.part7888 : Interval test 7888 7904 :=
  interval_of_check _ 7888 16 (by decide +kernel)
theorem Check030.part7904 : Interval test 7904 7920 :=
  interval_of_check _ 7904 16 (by decide +kernel)
theorem Check030.part7920 : Interval test 7920 7936 :=
  interval_of_check _ 7920 16 (by decide +kernel)
theorem Check030.checked : Interval test 7680 7936 :=
  (FiniteChecks.interval_append test 7680 7808 7936
  (FiniteChecks.interval_append test 7680 7744 7808
  (FiniteChecks.interval_append test 7680 7712 7744
  (FiniteChecks.interval_append test 7680 7696 7712
  Check030.part7680
  Check030.part7696)
  (FiniteChecks.interval_append test 7712 7728 7744
  Check030.part7712
  Check030.part7728))
  (FiniteChecks.interval_append test 7744 7776 7808
  (FiniteChecks.interval_append test 7744 7760 7776
  Check030.part7744
  Check030.part7760)
  (FiniteChecks.interval_append test 7776 7792 7808
  Check030.part7776
  Check030.part7792)))
  (FiniteChecks.interval_append test 7808 7872 7936
  (FiniteChecks.interval_append test 7808 7840 7872
  (FiniteChecks.interval_append test 7808 7824 7840
  Check030.part7808
  Check030.part7824)
  (FiniteChecks.interval_append test 7840 7856 7872
  Check030.part7840
  Check030.part7856))
  (FiniteChecks.interval_append test 7872 7904 7936
  (FiniteChecks.interval_append test 7872 7888 7904
  Check030.part7872
  Check030.part7888)
  (FiniteChecks.interval_append test 7904 7920 7936
  Check030.part7904
  Check030.part7920))))
#print axioms Check030.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check031.part7936 : Interval test 7936 7952 :=
  interval_of_check _ 7936 16 (by decide +kernel)
theorem Check031.part7952 : Interval test 7952 7968 :=
  interval_of_check _ 7952 16 (by decide +kernel)
theorem Check031.part7968 : Interval test 7968 7984 :=
  interval_of_check _ 7968 16 (by decide +kernel)
theorem Check031.part7984 : Interval test 7984 8000 :=
  interval_of_check _ 7984 16 (by decide +kernel)
theorem Check031.part8000 : Interval test 8000 8016 :=
  interval_of_check _ 8000 16 (by decide +kernel)
theorem Check031.part8016 : Interval test 8016 8032 :=
  interval_of_check _ 8016 16 (by decide +kernel)
theorem Check031.part8032 : Interval test 8032 8048 :=
  interval_of_check _ 8032 16 (by decide +kernel)
theorem Check031.part8048 : Interval test 8048 8064 :=
  interval_of_check _ 8048 16 (by decide +kernel)
theorem Check031.part8064 : Interval test 8064 8080 :=
  interval_of_check _ 8064 16 (by decide +kernel)
theorem Check031.part8080 : Interval test 8080 8096 :=
  interval_of_check _ 8080 16 (by decide +kernel)
theorem Check031.part8096 : Interval test 8096 8112 :=
  interval_of_check _ 8096 16 (by decide +kernel)
theorem Check031.part8112 : Interval test 8112 8128 :=
  interval_of_check _ 8112 16 (by decide +kernel)
theorem Check031.part8128 : Interval test 8128 8144 :=
  interval_of_check _ 8128 16 (by decide +kernel)
theorem Check031.part8144 : Interval test 8144 8160 :=
  interval_of_check _ 8144 16 (by decide +kernel)
theorem Check031.part8160 : Interval test 8160 8176 :=
  interval_of_check _ 8160 16 (by decide +kernel)
theorem Check031.part8176 : Interval test 8176 8192 :=
  interval_of_check _ 8176 16 (by decide +kernel)
theorem Check031.checked : Interval test 7936 8192 :=
  (FiniteChecks.interval_append test 7936 8064 8192
  (FiniteChecks.interval_append test 7936 8000 8064
  (FiniteChecks.interval_append test 7936 7968 8000
  (FiniteChecks.interval_append test 7936 7952 7968
  Check031.part7936
  Check031.part7952)
  (FiniteChecks.interval_append test 7968 7984 8000
  Check031.part7968
  Check031.part7984))
  (FiniteChecks.interval_append test 8000 8032 8064
  (FiniteChecks.interval_append test 8000 8016 8032
  Check031.part8000
  Check031.part8016)
  (FiniteChecks.interval_append test 8032 8048 8064
  Check031.part8032
  Check031.part8048)))
  (FiniteChecks.interval_append test 8064 8128 8192
  (FiniteChecks.interval_append test 8064 8096 8128
  (FiniteChecks.interval_append test 8064 8080 8096
  Check031.part8064
  Check031.part8080)
  (FiniteChecks.interval_append test 8096 8112 8128
  Check031.part8096
  Check031.part8112))
  (FiniteChecks.interval_append test 8128 8160 8192
  (FiniteChecks.interval_append test 8128 8144 8160
  Check031.part8128
  Check031.part8144)
  (FiniteChecks.interval_append test 8160 8176 8192
  Check031.part8160
  Check031.part8176))))
#print axioms Check031.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check032.part8192 : Interval test 8192 8208 :=
  interval_of_check _ 8192 16 (by decide +kernel)
theorem Check032.part8208 : Interval test 8208 8224 :=
  interval_of_check _ 8208 16 (by decide +kernel)
theorem Check032.part8224 : Interval test 8224 8240 :=
  interval_of_check _ 8224 16 (by decide +kernel)
theorem Check032.part8240 : Interval test 8240 8256 :=
  interval_of_check _ 8240 16 (by decide +kernel)
theorem Check032.part8256 : Interval test 8256 8272 :=
  interval_of_check _ 8256 16 (by decide +kernel)
theorem Check032.part8272 : Interval test 8272 8288 :=
  interval_of_check _ 8272 16 (by decide +kernel)
theorem Check032.part8288 : Interval test 8288 8304 :=
  interval_of_check _ 8288 16 (by decide +kernel)
theorem Check032.part8304 : Interval test 8304 8320 :=
  interval_of_check _ 8304 16 (by decide +kernel)
theorem Check032.part8320 : Interval test 8320 8336 :=
  interval_of_check _ 8320 16 (by decide +kernel)
theorem Check032.part8336 : Interval test 8336 8352 :=
  interval_of_check _ 8336 16 (by decide +kernel)
theorem Check032.part8352 : Interval test 8352 8368 :=
  interval_of_check _ 8352 16 (by decide +kernel)
theorem Check032.part8368 : Interval test 8368 8384 :=
  interval_of_check _ 8368 16 (by decide +kernel)
theorem Check032.part8384 : Interval test 8384 8400 :=
  interval_of_check _ 8384 16 (by decide +kernel)
theorem Check032.part8400 : Interval test 8400 8416 :=
  interval_of_check _ 8400 16 (by decide +kernel)
theorem Check032.part8416 : Interval test 8416 8432 :=
  interval_of_check _ 8416 16 (by decide +kernel)
theorem Check032.part8432 : Interval test 8432 8448 :=
  interval_of_check _ 8432 16 (by decide +kernel)
theorem Check032.checked : Interval test 8192 8448 :=
  (FiniteChecks.interval_append test 8192 8320 8448
  (FiniteChecks.interval_append test 8192 8256 8320
  (FiniteChecks.interval_append test 8192 8224 8256
  (FiniteChecks.interval_append test 8192 8208 8224
  Check032.part8192
  Check032.part8208)
  (FiniteChecks.interval_append test 8224 8240 8256
  Check032.part8224
  Check032.part8240))
  (FiniteChecks.interval_append test 8256 8288 8320
  (FiniteChecks.interval_append test 8256 8272 8288
  Check032.part8256
  Check032.part8272)
  (FiniteChecks.interval_append test 8288 8304 8320
  Check032.part8288
  Check032.part8304)))
  (FiniteChecks.interval_append test 8320 8384 8448
  (FiniteChecks.interval_append test 8320 8352 8384
  (FiniteChecks.interval_append test 8320 8336 8352
  Check032.part8320
  Check032.part8336)
  (FiniteChecks.interval_append test 8352 8368 8384
  Check032.part8352
  Check032.part8368))
  (FiniteChecks.interval_append test 8384 8416 8448
  (FiniteChecks.interval_append test 8384 8400 8416
  Check032.part8384
  Check032.part8400)
  (FiniteChecks.interval_append test 8416 8432 8448
  Check032.part8416
  Check032.part8432))))
#print axioms Check032.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check033.part8448 : Interval test 8448 8464 :=
  interval_of_check _ 8448 16 (by decide +kernel)
theorem Check033.part8464 : Interval test 8464 8480 :=
  interval_of_check _ 8464 16 (by decide +kernel)
theorem Check033.part8480 : Interval test 8480 8496 :=
  interval_of_check _ 8480 16 (by decide +kernel)
theorem Check033.part8496 : Interval test 8496 8512 :=
  interval_of_check _ 8496 16 (by decide +kernel)
theorem Check033.part8512 : Interval test 8512 8528 :=
  interval_of_check _ 8512 16 (by decide +kernel)
theorem Check033.part8528 : Interval test 8528 8544 :=
  interval_of_check _ 8528 16 (by decide +kernel)
theorem Check033.part8544 : Interval test 8544 8560 :=
  interval_of_check _ 8544 16 (by decide +kernel)
theorem Check033.part8560 : Interval test 8560 8576 :=
  interval_of_check _ 8560 16 (by decide +kernel)
theorem Check033.part8576 : Interval test 8576 8592 :=
  interval_of_check _ 8576 16 (by decide +kernel)
theorem Check033.part8592 : Interval test 8592 8608 :=
  interval_of_check _ 8592 16 (by decide +kernel)
theorem Check033.part8608 : Interval test 8608 8624 :=
  interval_of_check _ 8608 16 (by decide +kernel)
theorem Check033.part8624 : Interval test 8624 8640 :=
  interval_of_check _ 8624 16 (by decide +kernel)
theorem Check033.part8640 : Interval test 8640 8656 :=
  interval_of_check _ 8640 16 (by decide +kernel)
theorem Check033.part8656 : Interval test 8656 8672 :=
  interval_of_check _ 8656 16 (by decide +kernel)
theorem Check033.part8672 : Interval test 8672 8688 :=
  interval_of_check _ 8672 16 (by decide +kernel)
theorem Check033.part8688 : Interval test 8688 8704 :=
  interval_of_check _ 8688 16 (by decide +kernel)
theorem Check033.checked : Interval test 8448 8704 :=
  (FiniteChecks.interval_append test 8448 8576 8704
  (FiniteChecks.interval_append test 8448 8512 8576
  (FiniteChecks.interval_append test 8448 8480 8512
  (FiniteChecks.interval_append test 8448 8464 8480
  Check033.part8448
  Check033.part8464)
  (FiniteChecks.interval_append test 8480 8496 8512
  Check033.part8480
  Check033.part8496))
  (FiniteChecks.interval_append test 8512 8544 8576
  (FiniteChecks.interval_append test 8512 8528 8544
  Check033.part8512
  Check033.part8528)
  (FiniteChecks.interval_append test 8544 8560 8576
  Check033.part8544
  Check033.part8560)))
  (FiniteChecks.interval_append test 8576 8640 8704
  (FiniteChecks.interval_append test 8576 8608 8640
  (FiniteChecks.interval_append test 8576 8592 8608
  Check033.part8576
  Check033.part8592)
  (FiniteChecks.interval_append test 8608 8624 8640
  Check033.part8608
  Check033.part8624))
  (FiniteChecks.interval_append test 8640 8672 8704
  (FiniteChecks.interval_append test 8640 8656 8672
  Check033.part8640
  Check033.part8656)
  (FiniteChecks.interval_append test 8672 8688 8704
  Check033.part8672
  Check033.part8688))))
#print axioms Check033.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check034.part8704 : Interval test 8704 8720 :=
  interval_of_check _ 8704 16 (by decide +kernel)
theorem Check034.part8720 : Interval test 8720 8736 :=
  interval_of_check _ 8720 16 (by decide +kernel)
theorem Check034.part8736 : Interval test 8736 8752 :=
  interval_of_check _ 8736 16 (by decide +kernel)
theorem Check034.part8752 : Interval test 8752 8768 :=
  interval_of_check _ 8752 16 (by decide +kernel)
theorem Check034.part8768 : Interval test 8768 8784 :=
  interval_of_check _ 8768 16 (by decide +kernel)
theorem Check034.part8784 : Interval test 8784 8800 :=
  interval_of_check _ 8784 16 (by decide +kernel)
theorem Check034.part8800 : Interval test 8800 8816 :=
  interval_of_check _ 8800 16 (by decide +kernel)
theorem Check034.part8816 : Interval test 8816 8832 :=
  interval_of_check _ 8816 16 (by decide +kernel)
theorem Check034.part8832 : Interval test 8832 8848 :=
  interval_of_check _ 8832 16 (by decide +kernel)
theorem Check034.part8848 : Interval test 8848 8864 :=
  interval_of_check _ 8848 16 (by decide +kernel)
theorem Check034.part8864 : Interval test 8864 8880 :=
  interval_of_check _ 8864 16 (by decide +kernel)
theorem Check034.part8880 : Interval test 8880 8896 :=
  interval_of_check _ 8880 16 (by decide +kernel)
theorem Check034.part8896 : Interval test 8896 8912 :=
  interval_of_check _ 8896 16 (by decide +kernel)
theorem Check034.part8912 : Interval test 8912 8928 :=
  interval_of_check _ 8912 16 (by decide +kernel)
theorem Check034.part8928 : Interval test 8928 8944 :=
  interval_of_check _ 8928 16 (by decide +kernel)
theorem Check034.part8944 : Interval test 8944 8960 :=
  interval_of_check _ 8944 16 (by decide +kernel)
theorem Check034.checked : Interval test 8704 8960 :=
  (FiniteChecks.interval_append test 8704 8832 8960
  (FiniteChecks.interval_append test 8704 8768 8832
  (FiniteChecks.interval_append test 8704 8736 8768
  (FiniteChecks.interval_append test 8704 8720 8736
  Check034.part8704
  Check034.part8720)
  (FiniteChecks.interval_append test 8736 8752 8768
  Check034.part8736
  Check034.part8752))
  (FiniteChecks.interval_append test 8768 8800 8832
  (FiniteChecks.interval_append test 8768 8784 8800
  Check034.part8768
  Check034.part8784)
  (FiniteChecks.interval_append test 8800 8816 8832
  Check034.part8800
  Check034.part8816)))
  (FiniteChecks.interval_append test 8832 8896 8960
  (FiniteChecks.interval_append test 8832 8864 8896
  (FiniteChecks.interval_append test 8832 8848 8864
  Check034.part8832
  Check034.part8848)
  (FiniteChecks.interval_append test 8864 8880 8896
  Check034.part8864
  Check034.part8880))
  (FiniteChecks.interval_append test 8896 8928 8960
  (FiniteChecks.interval_append test 8896 8912 8928
  Check034.part8896
  Check034.part8912)
  (FiniteChecks.interval_append test 8928 8944 8960
  Check034.part8928
  Check034.part8944))))
#print axioms Check034.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check035.part8960 : Interval test 8960 8976 :=
  interval_of_check _ 8960 16 (by decide +kernel)
theorem Check035.part8976 : Interval test 8976 8992 :=
  interval_of_check _ 8976 16 (by decide +kernel)
theorem Check035.part8992 : Interval test 8992 9008 :=
  interval_of_check _ 8992 16 (by decide +kernel)
theorem Check035.part9008 : Interval test 9008 9024 :=
  interval_of_check _ 9008 16 (by decide +kernel)
theorem Check035.part9024 : Interval test 9024 9040 :=
  interval_of_check _ 9024 16 (by decide +kernel)
theorem Check035.part9040 : Interval test 9040 9056 :=
  interval_of_check _ 9040 16 (by decide +kernel)
theorem Check035.part9056 : Interval test 9056 9072 :=
  interval_of_check _ 9056 16 (by decide +kernel)
theorem Check035.part9072 : Interval test 9072 9088 :=
  interval_of_check _ 9072 16 (by decide +kernel)
theorem Check035.part9088 : Interval test 9088 9104 :=
  interval_of_check _ 9088 16 (by decide +kernel)
theorem Check035.part9104 : Interval test 9104 9120 :=
  interval_of_check _ 9104 16 (by decide +kernel)
theorem Check035.part9120 : Interval test 9120 9136 :=
  interval_of_check _ 9120 16 (by decide +kernel)
theorem Check035.part9136 : Interval test 9136 9152 :=
  interval_of_check _ 9136 16 (by decide +kernel)
theorem Check035.part9152 : Interval test 9152 9168 :=
  interval_of_check _ 9152 16 (by decide +kernel)
theorem Check035.part9168 : Interval test 9168 9184 :=
  interval_of_check _ 9168 16 (by decide +kernel)
theorem Check035.part9184 : Interval test 9184 9200 :=
  interval_of_check _ 9184 16 (by decide +kernel)
theorem Check035.part9200 : Interval test 9200 9216 :=
  interval_of_check _ 9200 16 (by decide +kernel)
theorem Check035.checked : Interval test 8960 9216 :=
  (FiniteChecks.interval_append test 8960 9088 9216
  (FiniteChecks.interval_append test 8960 9024 9088
  (FiniteChecks.interval_append test 8960 8992 9024
  (FiniteChecks.interval_append test 8960 8976 8992
  Check035.part8960
  Check035.part8976)
  (FiniteChecks.interval_append test 8992 9008 9024
  Check035.part8992
  Check035.part9008))
  (FiniteChecks.interval_append test 9024 9056 9088
  (FiniteChecks.interval_append test 9024 9040 9056
  Check035.part9024
  Check035.part9040)
  (FiniteChecks.interval_append test 9056 9072 9088
  Check035.part9056
  Check035.part9072)))
  (FiniteChecks.interval_append test 9088 9152 9216
  (FiniteChecks.interval_append test 9088 9120 9152
  (FiniteChecks.interval_append test 9088 9104 9120
  Check035.part9088
  Check035.part9104)
  (FiniteChecks.interval_append test 9120 9136 9152
  Check035.part9120
  Check035.part9136))
  (FiniteChecks.interval_append test 9152 9184 9216
  (FiniteChecks.interval_append test 9152 9168 9184
  Check035.part9152
  Check035.part9168)
  (FiniteChecks.interval_append test 9184 9200 9216
  Check035.part9184
  Check035.part9200))))
#print axioms Check035.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check036.part9216 : Interval test 9216 9232 :=
  interval_of_check _ 9216 16 (by decide +kernel)
theorem Check036.part9232 : Interval test 9232 9248 :=
  interval_of_check _ 9232 16 (by decide +kernel)
theorem Check036.part9248 : Interval test 9248 9264 :=
  interval_of_check _ 9248 16 (by decide +kernel)
theorem Check036.part9264 : Interval test 9264 9280 :=
  interval_of_check _ 9264 16 (by decide +kernel)
theorem Check036.part9280 : Interval test 9280 9296 :=
  interval_of_check _ 9280 16 (by decide +kernel)
theorem Check036.part9296 : Interval test 9296 9312 :=
  interval_of_check _ 9296 16 (by decide +kernel)
theorem Check036.part9312 : Interval test 9312 9328 :=
  interval_of_check _ 9312 16 (by decide +kernel)
theorem Check036.part9328 : Interval test 9328 9344 :=
  interval_of_check _ 9328 16 (by decide +kernel)
theorem Check036.part9344 : Interval test 9344 9360 :=
  interval_of_check _ 9344 16 (by decide +kernel)
theorem Check036.part9360 : Interval test 9360 9376 :=
  interval_of_check _ 9360 16 (by decide +kernel)
theorem Check036.part9376 : Interval test 9376 9392 :=
  interval_of_check _ 9376 16 (by decide +kernel)
theorem Check036.part9392 : Interval test 9392 9408 :=
  interval_of_check _ 9392 16 (by decide +kernel)
theorem Check036.part9408 : Interval test 9408 9424 :=
  interval_of_check _ 9408 16 (by decide +kernel)
theorem Check036.part9424 : Interval test 9424 9440 :=
  interval_of_check _ 9424 16 (by decide +kernel)
theorem Check036.part9440 : Interval test 9440 9456 :=
  interval_of_check _ 9440 16 (by decide +kernel)
theorem Check036.part9456 : Interval test 9456 9472 :=
  interval_of_check _ 9456 16 (by decide +kernel)
theorem Check036.checked : Interval test 9216 9472 :=
  (FiniteChecks.interval_append test 9216 9344 9472
  (FiniteChecks.interval_append test 9216 9280 9344
  (FiniteChecks.interval_append test 9216 9248 9280
  (FiniteChecks.interval_append test 9216 9232 9248
  Check036.part9216
  Check036.part9232)
  (FiniteChecks.interval_append test 9248 9264 9280
  Check036.part9248
  Check036.part9264))
  (FiniteChecks.interval_append test 9280 9312 9344
  (FiniteChecks.interval_append test 9280 9296 9312
  Check036.part9280
  Check036.part9296)
  (FiniteChecks.interval_append test 9312 9328 9344
  Check036.part9312
  Check036.part9328)))
  (FiniteChecks.interval_append test 9344 9408 9472
  (FiniteChecks.interval_append test 9344 9376 9408
  (FiniteChecks.interval_append test 9344 9360 9376
  Check036.part9344
  Check036.part9360)
  (FiniteChecks.interval_append test 9376 9392 9408
  Check036.part9376
  Check036.part9392))
  (FiniteChecks.interval_append test 9408 9440 9472
  (FiniteChecks.interval_append test 9408 9424 9440
  Check036.part9408
  Check036.part9424)
  (FiniteChecks.interval_append test 9440 9456 9472
  Check036.part9440
  Check036.part9456))))
#print axioms Check036.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check037.part9472 : Interval test 9472 9488 :=
  interval_of_check _ 9472 16 (by decide +kernel)
theorem Check037.part9488 : Interval test 9488 9504 :=
  interval_of_check _ 9488 16 (by decide +kernel)
theorem Check037.part9504 : Interval test 9504 9520 :=
  interval_of_check _ 9504 16 (by decide +kernel)
theorem Check037.part9520 : Interval test 9520 9536 :=
  interval_of_check _ 9520 16 (by decide +kernel)
theorem Check037.part9536 : Interval test 9536 9552 :=
  interval_of_check _ 9536 16 (by decide +kernel)
theorem Check037.part9552 : Interval test 9552 9568 :=
  interval_of_check _ 9552 16 (by decide +kernel)
theorem Check037.part9568 : Interval test 9568 9584 :=
  interval_of_check _ 9568 16 (by decide +kernel)
theorem Check037.part9584 : Interval test 9584 9600 :=
  interval_of_check _ 9584 16 (by decide +kernel)
theorem Check037.part9600 : Interval test 9600 9616 :=
  interval_of_check _ 9600 16 (by decide +kernel)
theorem Check037.part9616 : Interval test 9616 9632 :=
  interval_of_check _ 9616 16 (by decide +kernel)
theorem Check037.part9632 : Interval test 9632 9648 :=
  interval_of_check _ 9632 16 (by decide +kernel)
theorem Check037.part9648 : Interval test 9648 9664 :=
  interval_of_check _ 9648 16 (by decide +kernel)
theorem Check037.part9664 : Interval test 9664 9680 :=
  interval_of_check _ 9664 16 (by decide +kernel)
theorem Check037.part9680 : Interval test 9680 9696 :=
  interval_of_check _ 9680 16 (by decide +kernel)
theorem Check037.part9696 : Interval test 9696 9712 :=
  interval_of_check _ 9696 16 (by decide +kernel)
theorem Check037.part9712 : Interval test 9712 9728 :=
  interval_of_check _ 9712 16 (by decide +kernel)
theorem Check037.checked : Interval test 9472 9728 :=
  (FiniteChecks.interval_append test 9472 9600 9728
  (FiniteChecks.interval_append test 9472 9536 9600
  (FiniteChecks.interval_append test 9472 9504 9536
  (FiniteChecks.interval_append test 9472 9488 9504
  Check037.part9472
  Check037.part9488)
  (FiniteChecks.interval_append test 9504 9520 9536
  Check037.part9504
  Check037.part9520))
  (FiniteChecks.interval_append test 9536 9568 9600
  (FiniteChecks.interval_append test 9536 9552 9568
  Check037.part9536
  Check037.part9552)
  (FiniteChecks.interval_append test 9568 9584 9600
  Check037.part9568
  Check037.part9584)))
  (FiniteChecks.interval_append test 9600 9664 9728
  (FiniteChecks.interval_append test 9600 9632 9664
  (FiniteChecks.interval_append test 9600 9616 9632
  Check037.part9600
  Check037.part9616)
  (FiniteChecks.interval_append test 9632 9648 9664
  Check037.part9632
  Check037.part9648))
  (FiniteChecks.interval_append test 9664 9696 9728
  (FiniteChecks.interval_append test 9664 9680 9696
  Check037.part9664
  Check037.part9680)
  (FiniteChecks.interval_append test 9696 9712 9728
  Check037.part9696
  Check037.part9712))))
#print axioms Check037.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check038.part9728 : Interval test 9728 9744 :=
  interval_of_check _ 9728 16 (by decide +kernel)
theorem Check038.part9744 : Interval test 9744 9760 :=
  interval_of_check _ 9744 16 (by decide +kernel)
theorem Check038.part9760 : Interval test 9760 9776 :=
  interval_of_check _ 9760 16 (by decide +kernel)
theorem Check038.part9776 : Interval test 9776 9792 :=
  interval_of_check _ 9776 16 (by decide +kernel)
theorem Check038.part9792 : Interval test 9792 9808 :=
  interval_of_check _ 9792 16 (by decide +kernel)
theorem Check038.part9808 : Interval test 9808 9824 :=
  interval_of_check _ 9808 16 (by decide +kernel)
theorem Check038.part9824 : Interval test 9824 9840 :=
  interval_of_check _ 9824 16 (by decide +kernel)
theorem Check038.part9840 : Interval test 9840 9856 :=
  interval_of_check _ 9840 16 (by decide +kernel)
theorem Check038.part9856 : Interval test 9856 9872 :=
  interval_of_check _ 9856 16 (by decide +kernel)
theorem Check038.part9872 : Interval test 9872 9888 :=
  interval_of_check _ 9872 16 (by decide +kernel)
theorem Check038.part9888 : Interval test 9888 9904 :=
  interval_of_check _ 9888 16 (by decide +kernel)
theorem Check038.part9904 : Interval test 9904 9920 :=
  interval_of_check _ 9904 16 (by decide +kernel)
theorem Check038.part9920 : Interval test 9920 9936 :=
  interval_of_check _ 9920 16 (by decide +kernel)
theorem Check038.part9936 : Interval test 9936 9952 :=
  interval_of_check _ 9936 16 (by decide +kernel)
theorem Check038.part9952 : Interval test 9952 9968 :=
  interval_of_check _ 9952 16 (by decide +kernel)
theorem Check038.part9968 : Interval test 9968 9984 :=
  interval_of_check _ 9968 16 (by decide +kernel)
theorem Check038.checked : Interval test 9728 9984 :=
  (FiniteChecks.interval_append test 9728 9856 9984
  (FiniteChecks.interval_append test 9728 9792 9856
  (FiniteChecks.interval_append test 9728 9760 9792
  (FiniteChecks.interval_append test 9728 9744 9760
  Check038.part9728
  Check038.part9744)
  (FiniteChecks.interval_append test 9760 9776 9792
  Check038.part9760
  Check038.part9776))
  (FiniteChecks.interval_append test 9792 9824 9856
  (FiniteChecks.interval_append test 9792 9808 9824
  Check038.part9792
  Check038.part9808)
  (FiniteChecks.interval_append test 9824 9840 9856
  Check038.part9824
  Check038.part9840)))
  (FiniteChecks.interval_append test 9856 9920 9984
  (FiniteChecks.interval_append test 9856 9888 9920
  (FiniteChecks.interval_append test 9856 9872 9888
  Check038.part9856
  Check038.part9872)
  (FiniteChecks.interval_append test 9888 9904 9920
  Check038.part9888
  Check038.part9904))
  (FiniteChecks.interval_append test 9920 9952 9984
  (FiniteChecks.interval_append test 9920 9936 9952
  Check038.part9920
  Check038.part9936)
  (FiniteChecks.interval_append test 9952 9968 9984
  Check038.part9952
  Check038.part9968))))
#print axioms Check038.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check039.part9984 : Interval test 9984 10000 :=
  interval_of_check _ 9984 16 (by decide +kernel)
theorem Check039.part10000 : Interval test 10000 10016 :=
  interval_of_check _ 10000 16 (by decide +kernel)
theorem Check039.part10016 : Interval test 10016 10032 :=
  interval_of_check _ 10016 16 (by decide +kernel)
theorem Check039.part10032 : Interval test 10032 10048 :=
  interval_of_check _ 10032 16 (by decide +kernel)
theorem Check039.part10048 : Interval test 10048 10064 :=
  interval_of_check _ 10048 16 (by decide +kernel)
theorem Check039.part10064 : Interval test 10064 10080 :=
  interval_of_check _ 10064 16 (by decide +kernel)
theorem Check039.part10080 : Interval test 10080 10096 :=
  interval_of_check _ 10080 16 (by decide +kernel)
theorem Check039.part10096 : Interval test 10096 10112 :=
  interval_of_check _ 10096 16 (by decide +kernel)
theorem Check039.part10112 : Interval test 10112 10128 :=
  interval_of_check _ 10112 16 (by decide +kernel)
theorem Check039.part10128 : Interval test 10128 10144 :=
  interval_of_check _ 10128 16 (by decide +kernel)
theorem Check039.part10144 : Interval test 10144 10160 :=
  interval_of_check _ 10144 16 (by decide +kernel)
theorem Check039.part10160 : Interval test 10160 10176 :=
  interval_of_check _ 10160 16 (by decide +kernel)
theorem Check039.part10176 : Interval test 10176 10192 :=
  interval_of_check _ 10176 16 (by decide +kernel)
theorem Check039.part10192 : Interval test 10192 10208 :=
  interval_of_check _ 10192 16 (by decide +kernel)
theorem Check039.part10208 : Interval test 10208 10224 :=
  interval_of_check _ 10208 16 (by decide +kernel)
theorem Check039.part10224 : Interval test 10224 10240 :=
  interval_of_check _ 10224 16 (by decide +kernel)
theorem Check039.checked : Interval test 9984 10240 :=
  (FiniteChecks.interval_append test 9984 10112 10240
  (FiniteChecks.interval_append test 9984 10048 10112
  (FiniteChecks.interval_append test 9984 10016 10048
  (FiniteChecks.interval_append test 9984 10000 10016
  Check039.part9984
  Check039.part10000)
  (FiniteChecks.interval_append test 10016 10032 10048
  Check039.part10016
  Check039.part10032))
  (FiniteChecks.interval_append test 10048 10080 10112
  (FiniteChecks.interval_append test 10048 10064 10080
  Check039.part10048
  Check039.part10064)
  (FiniteChecks.interval_append test 10080 10096 10112
  Check039.part10080
  Check039.part10096)))
  (FiniteChecks.interval_append test 10112 10176 10240
  (FiniteChecks.interval_append test 10112 10144 10176
  (FiniteChecks.interval_append test 10112 10128 10144
  Check039.part10112
  Check039.part10128)
  (FiniteChecks.interval_append test 10144 10160 10176
  Check039.part10144
  Check039.part10160))
  (FiniteChecks.interval_append test 10176 10208 10240
  (FiniteChecks.interval_append test 10176 10192 10208
  Check039.part10176
  Check039.part10192)
  (FiniteChecks.interval_append test 10208 10224 10240
  Check039.part10208
  Check039.part10224))))
#print axioms Check039.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
