module
prelude
public import SharedSix0CellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check140.part17920 : Interval test 17920 17936 :=
  interval_of_check _ 17920 16 (by decide +kernel)
theorem Check140.part17936 : Interval test 17936 17952 :=
  interval_of_check _ 17936 16 (by decide +kernel)
theorem Check140.part17952 : Interval test 17952 17968 :=
  interval_of_check _ 17952 16 (by decide +kernel)
theorem Check140.part17968 : Interval test 17968 17984 :=
  interval_of_check _ 17968 16 (by decide +kernel)
theorem Check140.part17984 : Interval test 17984 18000 :=
  interval_of_check _ 17984 16 (by decide +kernel)
theorem Check140.part18000 : Interval test 18000 18016 :=
  interval_of_check _ 18000 16 (by decide +kernel)
theorem Check140.part18016 : Interval test 18016 18032 :=
  interval_of_check _ 18016 16 (by decide +kernel)
theorem Check140.part18032 : Interval test 18032 18048 :=
  interval_of_check _ 18032 16 (by decide +kernel)
theorem Check140.checked : Interval test 17920 18048 :=
  (FiniteChecks.interval_append test 17920 17984 18048
  (FiniteChecks.interval_append test 17920 17952 17984
  (FiniteChecks.interval_append test 17920 17936 17952
  Check140.part17920
  Check140.part17936)
  (FiniteChecks.interval_append test 17952 17968 17984
  Check140.part17952
  Check140.part17968))
  (FiniteChecks.interval_append test 17984 18016 18048
  (FiniteChecks.interval_append test 17984 18000 18016
  Check140.part17984
  Check140.part18000)
  (FiniteChecks.interval_append test 18016 18032 18048
  Check140.part18016
  Check140.part18032)))
#print axioms Check140.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check141.part18048 : Interval test 18048 18064 :=
  interval_of_check _ 18048 16 (by decide +kernel)
theorem Check141.part18064 : Interval test 18064 18080 :=
  interval_of_check _ 18064 16 (by decide +kernel)
theorem Check141.part18080 : Interval test 18080 18096 :=
  interval_of_check _ 18080 16 (by decide +kernel)
theorem Check141.part18096 : Interval test 18096 18112 :=
  interval_of_check _ 18096 16 (by decide +kernel)
theorem Check141.part18112 : Interval test 18112 18128 :=
  interval_of_check _ 18112 16 (by decide +kernel)
theorem Check141.part18128 : Interval test 18128 18144 :=
  interval_of_check _ 18128 16 (by decide +kernel)
theorem Check141.part18144 : Interval test 18144 18160 :=
  interval_of_check _ 18144 16 (by decide +kernel)
theorem Check141.part18160 : Interval test 18160 18176 :=
  interval_of_check _ 18160 16 (by decide +kernel)
theorem Check141.checked : Interval test 18048 18176 :=
  (FiniteChecks.interval_append test 18048 18112 18176
  (FiniteChecks.interval_append test 18048 18080 18112
  (FiniteChecks.interval_append test 18048 18064 18080
  Check141.part18048
  Check141.part18064)
  (FiniteChecks.interval_append test 18080 18096 18112
  Check141.part18080
  Check141.part18096))
  (FiniteChecks.interval_append test 18112 18144 18176
  (FiniteChecks.interval_append test 18112 18128 18144
  Check141.part18112
  Check141.part18128)
  (FiniteChecks.interval_append test 18144 18160 18176
  Check141.part18144
  Check141.part18160)))
#print axioms Check141.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check142.part18176 : Interval test 18176 18192 :=
  interval_of_check _ 18176 16 (by decide +kernel)
theorem Check142.part18192 : Interval test 18192 18208 :=
  interval_of_check _ 18192 16 (by decide +kernel)
theorem Check142.part18208 : Interval test 18208 18224 :=
  interval_of_check _ 18208 16 (by decide +kernel)
theorem Check142.part18224 : Interval test 18224 18240 :=
  interval_of_check _ 18224 16 (by decide +kernel)
theorem Check142.part18240 : Interval test 18240 18256 :=
  interval_of_check _ 18240 16 (by decide +kernel)
theorem Check142.part18256 : Interval test 18256 18272 :=
  interval_of_check _ 18256 16 (by decide +kernel)
theorem Check142.part18272 : Interval test 18272 18288 :=
  interval_of_check _ 18272 16 (by decide +kernel)
theorem Check142.part18288 : Interval test 18288 18304 :=
  interval_of_check _ 18288 16 (by decide +kernel)
theorem Check142.checked : Interval test 18176 18304 :=
  (FiniteChecks.interval_append test 18176 18240 18304
  (FiniteChecks.interval_append test 18176 18208 18240
  (FiniteChecks.interval_append test 18176 18192 18208
  Check142.part18176
  Check142.part18192)
  (FiniteChecks.interval_append test 18208 18224 18240
  Check142.part18208
  Check142.part18224))
  (FiniteChecks.interval_append test 18240 18272 18304
  (FiniteChecks.interval_append test 18240 18256 18272
  Check142.part18240
  Check142.part18256)
  (FiniteChecks.interval_append test 18272 18288 18304
  Check142.part18272
  Check142.part18288)))
#print axioms Check142.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check143.part18304 : Interval test 18304 18320 :=
  interval_of_check _ 18304 16 (by decide +kernel)
theorem Check143.part18320 : Interval test 18320 18336 :=
  interval_of_check _ 18320 16 (by decide +kernel)
theorem Check143.part18336 : Interval test 18336 18352 :=
  interval_of_check _ 18336 16 (by decide +kernel)
theorem Check143.part18352 : Interval test 18352 18368 :=
  interval_of_check _ 18352 16 (by decide +kernel)
theorem Check143.part18368 : Interval test 18368 18384 :=
  interval_of_check _ 18368 16 (by decide +kernel)
theorem Check143.part18384 : Interval test 18384 18400 :=
  interval_of_check _ 18384 16 (by decide +kernel)
theorem Check143.part18400 : Interval test 18400 18416 :=
  interval_of_check _ 18400 16 (by decide +kernel)
theorem Check143.part18416 : Interval test 18416 18432 :=
  interval_of_check _ 18416 16 (by decide +kernel)
theorem Check143.checked : Interval test 18304 18432 :=
  (FiniteChecks.interval_append test 18304 18368 18432
  (FiniteChecks.interval_append test 18304 18336 18368
  (FiniteChecks.interval_append test 18304 18320 18336
  Check143.part18304
  Check143.part18320)
  (FiniteChecks.interval_append test 18336 18352 18368
  Check143.part18336
  Check143.part18352))
  (FiniteChecks.interval_append test 18368 18400 18432
  (FiniteChecks.interval_append test 18368 18384 18400
  Check143.part18368
  Check143.part18384)
  (FiniteChecks.interval_append test 18400 18416 18432
  Check143.part18400
  Check143.part18416)))
#print axioms Check143.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check144.part18432 : Interval test 18432 18448 :=
  interval_of_check _ 18432 16 (by decide +kernel)
theorem Check144.part18448 : Interval test 18448 18464 :=
  interval_of_check _ 18448 16 (by decide +kernel)
theorem Check144.part18464 : Interval test 18464 18480 :=
  interval_of_check _ 18464 16 (by decide +kernel)
theorem Check144.part18480 : Interval test 18480 18496 :=
  interval_of_check _ 18480 16 (by decide +kernel)
theorem Check144.part18496 : Interval test 18496 18512 :=
  interval_of_check _ 18496 16 (by decide +kernel)
theorem Check144.part18512 : Interval test 18512 18528 :=
  interval_of_check _ 18512 16 (by decide +kernel)
theorem Check144.part18528 : Interval test 18528 18544 :=
  interval_of_check _ 18528 16 (by decide +kernel)
theorem Check144.part18544 : Interval test 18544 18560 :=
  interval_of_check _ 18544 16 (by decide +kernel)
theorem Check144.checked : Interval test 18432 18560 :=
  (FiniteChecks.interval_append test 18432 18496 18560
  (FiniteChecks.interval_append test 18432 18464 18496
  (FiniteChecks.interval_append test 18432 18448 18464
  Check144.part18432
  Check144.part18448)
  (FiniteChecks.interval_append test 18464 18480 18496
  Check144.part18464
  Check144.part18480))
  (FiniteChecks.interval_append test 18496 18528 18560
  (FiniteChecks.interval_append test 18496 18512 18528
  Check144.part18496
  Check144.part18512)
  (FiniteChecks.interval_append test 18528 18544 18560
  Check144.part18528
  Check144.part18544)))
#print axioms Check144.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check145.part18560 : Interval test 18560 18576 :=
  interval_of_check _ 18560 16 (by decide +kernel)
theorem Check145.part18576 : Interval test 18576 18592 :=
  interval_of_check _ 18576 16 (by decide +kernel)
theorem Check145.part18592 : Interval test 18592 18608 :=
  interval_of_check _ 18592 16 (by decide +kernel)
theorem Check145.part18608 : Interval test 18608 18624 :=
  interval_of_check _ 18608 16 (by decide +kernel)
theorem Check145.part18624 : Interval test 18624 18640 :=
  interval_of_check _ 18624 16 (by decide +kernel)
theorem Check145.part18640 : Interval test 18640 18656 :=
  interval_of_check _ 18640 16 (by decide +kernel)
theorem Check145.part18656 : Interval test 18656 18672 :=
  interval_of_check _ 18656 16 (by decide +kernel)
theorem Check145.part18672 : Interval test 18672 18688 :=
  interval_of_check _ 18672 16 (by decide +kernel)
theorem Check145.checked : Interval test 18560 18688 :=
  (FiniteChecks.interval_append test 18560 18624 18688
  (FiniteChecks.interval_append test 18560 18592 18624
  (FiniteChecks.interval_append test 18560 18576 18592
  Check145.part18560
  Check145.part18576)
  (FiniteChecks.interval_append test 18592 18608 18624
  Check145.part18592
  Check145.part18608))
  (FiniteChecks.interval_append test 18624 18656 18688
  (FiniteChecks.interval_append test 18624 18640 18656
  Check145.part18624
  Check145.part18640)
  (FiniteChecks.interval_append test 18656 18672 18688
  Check145.part18656
  Check145.part18672)))
#print axioms Check145.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check146.part18688 : Interval test 18688 18704 :=
  interval_of_check _ 18688 16 (by decide +kernel)
theorem Check146.part18704 : Interval test 18704 18720 :=
  interval_of_check _ 18704 16 (by decide +kernel)
theorem Check146.part18720 : Interval test 18720 18736 :=
  interval_of_check _ 18720 16 (by decide +kernel)
theorem Check146.part18736 : Interval test 18736 18752 :=
  interval_of_check _ 18736 16 (by decide +kernel)
theorem Check146.part18752 : Interval test 18752 18768 :=
  interval_of_check _ 18752 16 (by decide +kernel)
theorem Check146.part18768 : Interval test 18768 18784 :=
  interval_of_check _ 18768 16 (by decide +kernel)
theorem Check146.part18784 : Interval test 18784 18800 :=
  interval_of_check _ 18784 16 (by decide +kernel)
theorem Check146.part18800 : Interval test 18800 18816 :=
  interval_of_check _ 18800 16 (by decide +kernel)
theorem Check146.checked : Interval test 18688 18816 :=
  (FiniteChecks.interval_append test 18688 18752 18816
  (FiniteChecks.interval_append test 18688 18720 18752
  (FiniteChecks.interval_append test 18688 18704 18720
  Check146.part18688
  Check146.part18704)
  (FiniteChecks.interval_append test 18720 18736 18752
  Check146.part18720
  Check146.part18736))
  (FiniteChecks.interval_append test 18752 18784 18816
  (FiniteChecks.interval_append test 18752 18768 18784
  Check146.part18752
  Check146.part18768)
  (FiniteChecks.interval_append test 18784 18800 18816
  Check146.part18784
  Check146.part18800)))
#print axioms Check146.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check147.part18816 : Interval test 18816 18832 :=
  interval_of_check _ 18816 16 (by decide +kernel)
theorem Check147.part18832 : Interval test 18832 18848 :=
  interval_of_check _ 18832 16 (by decide +kernel)
theorem Check147.part18848 : Interval test 18848 18864 :=
  interval_of_check _ 18848 16 (by decide +kernel)
theorem Check147.part18864 : Interval test 18864 18880 :=
  interval_of_check _ 18864 16 (by decide +kernel)
theorem Check147.part18880 : Interval test 18880 18896 :=
  interval_of_check _ 18880 16 (by decide +kernel)
theorem Check147.part18896 : Interval test 18896 18912 :=
  interval_of_check _ 18896 16 (by decide +kernel)
theorem Check147.part18912 : Interval test 18912 18928 :=
  interval_of_check _ 18912 16 (by decide +kernel)
theorem Check147.part18928 : Interval test 18928 18944 :=
  interval_of_check _ 18928 16 (by decide +kernel)
theorem Check147.checked : Interval test 18816 18944 :=
  (FiniteChecks.interval_append test 18816 18880 18944
  (FiniteChecks.interval_append test 18816 18848 18880
  (FiniteChecks.interval_append test 18816 18832 18848
  Check147.part18816
  Check147.part18832)
  (FiniteChecks.interval_append test 18848 18864 18880
  Check147.part18848
  Check147.part18864))
  (FiniteChecks.interval_append test 18880 18912 18944
  (FiniteChecks.interval_append test 18880 18896 18912
  Check147.part18880
  Check147.part18896)
  (FiniteChecks.interval_append test 18912 18928 18944
  Check147.part18912
  Check147.part18928)))
#print axioms Check147.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check148.part18944 : Interval test 18944 18960 :=
  interval_of_check _ 18944 16 (by decide +kernel)
theorem Check148.part18960 : Interval test 18960 18976 :=
  interval_of_check _ 18960 16 (by decide +kernel)
theorem Check148.part18976 : Interval test 18976 18992 :=
  interval_of_check _ 18976 16 (by decide +kernel)
theorem Check148.part18992 : Interval test 18992 19008 :=
  interval_of_check _ 18992 16 (by decide +kernel)
theorem Check148.part19008 : Interval test 19008 19024 :=
  interval_of_check _ 19008 16 (by decide +kernel)
theorem Check148.part19024 : Interval test 19024 19040 :=
  interval_of_check _ 19024 16 (by decide +kernel)
theorem Check148.part19040 : Interval test 19040 19056 :=
  interval_of_check _ 19040 16 (by decide +kernel)
theorem Check148.part19056 : Interval test 19056 19072 :=
  interval_of_check _ 19056 16 (by decide +kernel)
theorem Check148.checked : Interval test 18944 19072 :=
  (FiniteChecks.interval_append test 18944 19008 19072
  (FiniteChecks.interval_append test 18944 18976 19008
  (FiniteChecks.interval_append test 18944 18960 18976
  Check148.part18944
  Check148.part18960)
  (FiniteChecks.interval_append test 18976 18992 19008
  Check148.part18976
  Check148.part18992))
  (FiniteChecks.interval_append test 19008 19040 19072
  (FiniteChecks.interval_append test 19008 19024 19040
  Check148.part19008
  Check148.part19024)
  (FiniteChecks.interval_append test 19040 19056 19072
  Check148.part19040
  Check148.part19056)))
#print axioms Check148.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check149.part19072 : Interval test 19072 19088 :=
  interval_of_check _ 19072 16 (by decide +kernel)
theorem Check149.part19088 : Interval test 19088 19104 :=
  interval_of_check _ 19088 16 (by decide +kernel)
theorem Check149.part19104 : Interval test 19104 19120 :=
  interval_of_check _ 19104 16 (by decide +kernel)
theorem Check149.part19120 : Interval test 19120 19136 :=
  interval_of_check _ 19120 16 (by decide +kernel)
theorem Check149.part19136 : Interval test 19136 19152 :=
  interval_of_check _ 19136 16 (by decide +kernel)
theorem Check149.part19152 : Interval test 19152 19168 :=
  interval_of_check _ 19152 16 (by decide +kernel)
theorem Check149.part19168 : Interval test 19168 19184 :=
  interval_of_check _ 19168 16 (by decide +kernel)
theorem Check149.part19184 : Interval test 19184 19200 :=
  interval_of_check _ 19184 16 (by decide +kernel)
theorem Check149.checked : Interval test 19072 19200 :=
  (FiniteChecks.interval_append test 19072 19136 19200
  (FiniteChecks.interval_append test 19072 19104 19136
  (FiniteChecks.interval_append test 19072 19088 19104
  Check149.part19072
  Check149.part19088)
  (FiniteChecks.interval_append test 19104 19120 19136
  Check149.part19104
  Check149.part19120))
  (FiniteChecks.interval_append test 19136 19168 19200
  (FiniteChecks.interval_append test 19136 19152 19168
  Check149.part19136
  Check149.part19152)
  (FiniteChecks.interval_append test 19168 19184 19200
  Check149.part19168
  Check149.part19184)))
#print axioms Check149.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check150.part19200 : Interval test 19200 19216 :=
  interval_of_check _ 19200 16 (by decide +kernel)
theorem Check150.part19216 : Interval test 19216 19232 :=
  interval_of_check _ 19216 16 (by decide +kernel)
theorem Check150.part19232 : Interval test 19232 19248 :=
  interval_of_check _ 19232 16 (by decide +kernel)
theorem Check150.part19248 : Interval test 19248 19264 :=
  interval_of_check _ 19248 16 (by decide +kernel)
theorem Check150.part19264 : Interval test 19264 19280 :=
  interval_of_check _ 19264 16 (by decide +kernel)
theorem Check150.part19280 : Interval test 19280 19296 :=
  interval_of_check _ 19280 16 (by decide +kernel)
theorem Check150.part19296 : Interval test 19296 19312 :=
  interval_of_check _ 19296 16 (by decide +kernel)
theorem Check150.part19312 : Interval test 19312 19328 :=
  interval_of_check _ 19312 16 (by decide +kernel)
theorem Check150.checked : Interval test 19200 19328 :=
  (FiniteChecks.interval_append test 19200 19264 19328
  (FiniteChecks.interval_append test 19200 19232 19264
  (FiniteChecks.interval_append test 19200 19216 19232
  Check150.part19200
  Check150.part19216)
  (FiniteChecks.interval_append test 19232 19248 19264
  Check150.part19232
  Check150.part19248))
  (FiniteChecks.interval_append test 19264 19296 19328
  (FiniteChecks.interval_append test 19264 19280 19296
  Check150.part19264
  Check150.part19280)
  (FiniteChecks.interval_append test 19296 19312 19328
  Check150.part19296
  Check150.part19312)))
#print axioms Check150.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check151.part19328 : Interval test 19328 19344 :=
  interval_of_check _ 19328 16 (by decide +kernel)
theorem Check151.part19344 : Interval test 19344 19360 :=
  interval_of_check _ 19344 16 (by decide +kernel)
theorem Check151.part19360 : Interval test 19360 19376 :=
  interval_of_check _ 19360 16 (by decide +kernel)
theorem Check151.part19376 : Interval test 19376 19392 :=
  interval_of_check _ 19376 16 (by decide +kernel)
theorem Check151.part19392 : Interval test 19392 19408 :=
  interval_of_check _ 19392 16 (by decide +kernel)
theorem Check151.part19408 : Interval test 19408 19424 :=
  interval_of_check _ 19408 16 (by decide +kernel)
theorem Check151.part19424 : Interval test 19424 19440 :=
  interval_of_check _ 19424 16 (by decide +kernel)
theorem Check151.part19440 : Interval test 19440 19456 :=
  interval_of_check _ 19440 16 (by decide +kernel)
theorem Check151.checked : Interval test 19328 19456 :=
  (FiniteChecks.interval_append test 19328 19392 19456
  (FiniteChecks.interval_append test 19328 19360 19392
  (FiniteChecks.interval_append test 19328 19344 19360
  Check151.part19328
  Check151.part19344)
  (FiniteChecks.interval_append test 19360 19376 19392
  Check151.part19360
  Check151.part19376))
  (FiniteChecks.interval_append test 19392 19424 19456
  (FiniteChecks.interval_append test 19392 19408 19424
  Check151.part19392
  Check151.part19408)
  (FiniteChecks.interval_append test 19424 19440 19456
  Check151.part19424
  Check151.part19440)))
#print axioms Check151.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check152.part19456 : Interval test 19456 19472 :=
  interval_of_check _ 19456 16 (by decide +kernel)
theorem Check152.part19472 : Interval test 19472 19488 :=
  interval_of_check _ 19472 16 (by decide +kernel)
theorem Check152.part19488 : Interval test 19488 19504 :=
  interval_of_check _ 19488 16 (by decide +kernel)
theorem Check152.part19504 : Interval test 19504 19520 :=
  interval_of_check _ 19504 16 (by decide +kernel)
theorem Check152.part19520 : Interval test 19520 19536 :=
  interval_of_check _ 19520 16 (by decide +kernel)
theorem Check152.part19536 : Interval test 19536 19552 :=
  interval_of_check _ 19536 16 (by decide +kernel)
theorem Check152.part19552 : Interval test 19552 19568 :=
  interval_of_check _ 19552 16 (by decide +kernel)
theorem Check152.part19568 : Interval test 19568 19584 :=
  interval_of_check _ 19568 16 (by decide +kernel)
theorem Check152.checked : Interval test 19456 19584 :=
  (FiniteChecks.interval_append test 19456 19520 19584
  (FiniteChecks.interval_append test 19456 19488 19520
  (FiniteChecks.interval_append test 19456 19472 19488
  Check152.part19456
  Check152.part19472)
  (FiniteChecks.interval_append test 19488 19504 19520
  Check152.part19488
  Check152.part19504))
  (FiniteChecks.interval_append test 19520 19552 19584
  (FiniteChecks.interval_append test 19520 19536 19552
  Check152.part19520
  Check152.part19536)
  (FiniteChecks.interval_append test 19552 19568 19584
  Check152.part19552
  Check152.part19568)))
#print axioms Check152.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check153.part19584 : Interval test 19584 19600 :=
  interval_of_check _ 19584 16 (by decide +kernel)
theorem Check153.part19600 : Interval test 19600 19616 :=
  interval_of_check _ 19600 16 (by decide +kernel)
theorem Check153.part19616 : Interval test 19616 19632 :=
  interval_of_check _ 19616 16 (by decide +kernel)
theorem Check153.part19632 : Interval test 19632 19648 :=
  interval_of_check _ 19632 16 (by decide +kernel)
theorem Check153.part19648 : Interval test 19648 19664 :=
  interval_of_check _ 19648 16 (by decide +kernel)
theorem Check153.part19664 : Interval test 19664 19680 :=
  interval_of_check _ 19664 16 (by decide +kernel)
theorem Check153.part19680 : Interval test 19680 19696 :=
  interval_of_check _ 19680 16 (by decide +kernel)
theorem Check153.part19696 : Interval test 19696 19712 :=
  interval_of_check _ 19696 16 (by decide +kernel)
theorem Check153.checked : Interval test 19584 19712 :=
  (FiniteChecks.interval_append test 19584 19648 19712
  (FiniteChecks.interval_append test 19584 19616 19648
  (FiniteChecks.interval_append test 19584 19600 19616
  Check153.part19584
  Check153.part19600)
  (FiniteChecks.interval_append test 19616 19632 19648
  Check153.part19616
  Check153.part19632))
  (FiniteChecks.interval_append test 19648 19680 19712
  (FiniteChecks.interval_append test 19648 19664 19680
  Check153.part19648
  Check153.part19664)
  (FiniteChecks.interval_append test 19680 19696 19712
  Check153.part19680
  Check153.part19696)))
#print axioms Check153.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check154.part19712 : Interval test 19712 19728 :=
  interval_of_check _ 19712 16 (by decide +kernel)
theorem Check154.part19728 : Interval test 19728 19744 :=
  interval_of_check _ 19728 16 (by decide +kernel)
theorem Check154.part19744 : Interval test 19744 19760 :=
  interval_of_check _ 19744 16 (by decide +kernel)
theorem Check154.part19760 : Interval test 19760 19776 :=
  interval_of_check _ 19760 16 (by decide +kernel)
theorem Check154.part19776 : Interval test 19776 19792 :=
  interval_of_check _ 19776 16 (by decide +kernel)
theorem Check154.part19792 : Interval test 19792 19808 :=
  interval_of_check _ 19792 16 (by decide +kernel)
theorem Check154.part19808 : Interval test 19808 19824 :=
  interval_of_check _ 19808 16 (by decide +kernel)
theorem Check154.part19824 : Interval test 19824 19840 :=
  interval_of_check _ 19824 16 (by decide +kernel)
theorem Check154.checked : Interval test 19712 19840 :=
  (FiniteChecks.interval_append test 19712 19776 19840
  (FiniteChecks.interval_append test 19712 19744 19776
  (FiniteChecks.interval_append test 19712 19728 19744
  Check154.part19712
  Check154.part19728)
  (FiniteChecks.interval_append test 19744 19760 19776
  Check154.part19744
  Check154.part19760))
  (FiniteChecks.interval_append test 19776 19808 19840
  (FiniteChecks.interval_append test 19776 19792 19808
  Check154.part19776
  Check154.part19792)
  (FiniteChecks.interval_append test 19808 19824 19840
  Check154.part19808
  Check154.part19824)))
#print axioms Check154.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check155.part19840 : Interval test 19840 19856 :=
  interval_of_check _ 19840 16 (by decide +kernel)
theorem Check155.part19856 : Interval test 19856 19872 :=
  interval_of_check _ 19856 16 (by decide +kernel)
theorem Check155.part19872 : Interval test 19872 19888 :=
  interval_of_check _ 19872 16 (by decide +kernel)
theorem Check155.part19888 : Interval test 19888 19904 :=
  interval_of_check _ 19888 16 (by decide +kernel)
theorem Check155.part19904 : Interval test 19904 19920 :=
  interval_of_check _ 19904 16 (by decide +kernel)
theorem Check155.part19920 : Interval test 19920 19936 :=
  interval_of_check _ 19920 16 (by decide +kernel)
theorem Check155.part19936 : Interval test 19936 19952 :=
  interval_of_check _ 19936 16 (by decide +kernel)
theorem Check155.part19952 : Interval test 19952 19968 :=
  interval_of_check _ 19952 16 (by decide +kernel)
theorem Check155.checked : Interval test 19840 19968 :=
  (FiniteChecks.interval_append test 19840 19904 19968
  (FiniteChecks.interval_append test 19840 19872 19904
  (FiniteChecks.interval_append test 19840 19856 19872
  Check155.part19840
  Check155.part19856)
  (FiniteChecks.interval_append test 19872 19888 19904
  Check155.part19872
  Check155.part19888))
  (FiniteChecks.interval_append test 19904 19936 19968
  (FiniteChecks.interval_append test 19904 19920 19936
  Check155.part19904
  Check155.part19920)
  (FiniteChecks.interval_append test 19936 19952 19968
  Check155.part19936
  Check155.part19952)))
#print axioms Check155.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check156.part19968 : Interval test 19968 19984 :=
  interval_of_check _ 19968 16 (by decide +kernel)
theorem Check156.part19984 : Interval test 19984 20000 :=
  interval_of_check _ 19984 16 (by decide +kernel)
theorem Check156.part20000 : Interval test 20000 20016 :=
  interval_of_check _ 20000 16 (by decide +kernel)
theorem Check156.part20016 : Interval test 20016 20032 :=
  interval_of_check _ 20016 16 (by decide +kernel)
theorem Check156.part20032 : Interval test 20032 20048 :=
  interval_of_check _ 20032 16 (by decide +kernel)
theorem Check156.part20048 : Interval test 20048 20064 :=
  interval_of_check _ 20048 16 (by decide +kernel)
theorem Check156.part20064 : Interval test 20064 20080 :=
  interval_of_check _ 20064 16 (by decide +kernel)
theorem Check156.part20080 : Interval test 20080 20096 :=
  interval_of_check _ 20080 16 (by decide +kernel)
theorem Check156.checked : Interval test 19968 20096 :=
  (FiniteChecks.interval_append test 19968 20032 20096
  (FiniteChecks.interval_append test 19968 20000 20032
  (FiniteChecks.interval_append test 19968 19984 20000
  Check156.part19968
  Check156.part19984)
  (FiniteChecks.interval_append test 20000 20016 20032
  Check156.part20000
  Check156.part20016))
  (FiniteChecks.interval_append test 20032 20064 20096
  (FiniteChecks.interval_append test 20032 20048 20064
  Check156.part20032
  Check156.part20048)
  (FiniteChecks.interval_append test 20064 20080 20096
  Check156.part20064
  Check156.part20080)))
#print axioms Check156.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check157.part20096 : Interval test 20096 20112 :=
  interval_of_check _ 20096 16 (by decide +kernel)
theorem Check157.part20112 : Interval test 20112 20128 :=
  interval_of_check _ 20112 16 (by decide +kernel)
theorem Check157.part20128 : Interval test 20128 20144 :=
  interval_of_check _ 20128 16 (by decide +kernel)
theorem Check157.part20144 : Interval test 20144 20160 :=
  interval_of_check _ 20144 16 (by decide +kernel)
theorem Check157.part20160 : Interval test 20160 20176 :=
  interval_of_check _ 20160 16 (by decide +kernel)
theorem Check157.part20176 : Interval test 20176 20192 :=
  interval_of_check _ 20176 16 (by decide +kernel)
theorem Check157.part20192 : Interval test 20192 20208 :=
  interval_of_check _ 20192 16 (by decide +kernel)
theorem Check157.part20208 : Interval test 20208 20224 :=
  interval_of_check _ 20208 16 (by decide +kernel)
theorem Check157.checked : Interval test 20096 20224 :=
  (FiniteChecks.interval_append test 20096 20160 20224
  (FiniteChecks.interval_append test 20096 20128 20160
  (FiniteChecks.interval_append test 20096 20112 20128
  Check157.part20096
  Check157.part20112)
  (FiniteChecks.interval_append test 20128 20144 20160
  Check157.part20128
  Check157.part20144))
  (FiniteChecks.interval_append test 20160 20192 20224
  (FiniteChecks.interval_append test 20160 20176 20192
  Check157.part20160
  Check157.part20176)
  (FiniteChecks.interval_append test 20192 20208 20224
  Check157.part20192
  Check157.part20208)))
#print axioms Check157.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check158.part20224 : Interval test 20224 20240 :=
  interval_of_check _ 20224 16 (by decide +kernel)
theorem Check158.part20240 : Interval test 20240 20256 :=
  interval_of_check _ 20240 16 (by decide +kernel)
theorem Check158.part20256 : Interval test 20256 20272 :=
  interval_of_check _ 20256 16 (by decide +kernel)
theorem Check158.part20272 : Interval test 20272 20288 :=
  interval_of_check _ 20272 16 (by decide +kernel)
theorem Check158.part20288 : Interval test 20288 20304 :=
  interval_of_check _ 20288 16 (by decide +kernel)
theorem Check158.part20304 : Interval test 20304 20320 :=
  interval_of_check _ 20304 16 (by decide +kernel)
theorem Check158.part20320 : Interval test 20320 20336 :=
  interval_of_check _ 20320 16 (by decide +kernel)
theorem Check158.part20336 : Interval test 20336 20352 :=
  interval_of_check _ 20336 16 (by decide +kernel)
theorem Check158.checked : Interval test 20224 20352 :=
  (FiniteChecks.interval_append test 20224 20288 20352
  (FiniteChecks.interval_append test 20224 20256 20288
  (FiniteChecks.interval_append test 20224 20240 20256
  Check158.part20224
  Check158.part20240)
  (FiniteChecks.interval_append test 20256 20272 20288
  Check158.part20256
  Check158.part20272))
  (FiniteChecks.interval_append test 20288 20320 20352
  (FiniteChecks.interval_append test 20288 20304 20320
  Check158.part20288
  Check158.part20304)
  (FiniteChecks.interval_append test 20320 20336 20352
  Check158.part20320
  Check158.part20336)))
#print axioms Check158.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check159.part20352 : Interval test 20352 20368 :=
  interval_of_check _ 20352 16 (by decide +kernel)
theorem Check159.part20368 : Interval test 20368 20384 :=
  interval_of_check _ 20368 16 (by decide +kernel)
theorem Check159.part20384 : Interval test 20384 20400 :=
  interval_of_check _ 20384 16 (by decide +kernel)
theorem Check159.part20400 : Interval test 20400 20416 :=
  interval_of_check _ 20400 16 (by decide +kernel)
theorem Check159.part20416 : Interval test 20416 20432 :=
  interval_of_check _ 20416 16 (by decide +kernel)
theorem Check159.part20432 : Interval test 20432 20448 :=
  interval_of_check _ 20432 16 (by decide +kernel)
theorem Check159.part20448 : Interval test 20448 20464 :=
  interval_of_check _ 20448 16 (by decide +kernel)
theorem Check159.part20464 : Interval test 20464 20480 :=
  interval_of_check _ 20464 16 (by decide +kernel)
theorem Check159.checked : Interval test 20352 20480 :=
  (FiniteChecks.interval_append test 20352 20416 20480
  (FiniteChecks.interval_append test 20352 20384 20416
  (FiniteChecks.interval_append test 20352 20368 20384
  Check159.part20352
  Check159.part20368)
  (FiniteChecks.interval_append test 20384 20400 20416
  Check159.part20384
  Check159.part20400))
  (FiniteChecks.interval_append test 20416 20448 20480
  (FiniteChecks.interval_append test 20416 20432 20448
  Check159.part20416
  Check159.part20432)
  (FiniteChecks.interval_append test 20448 20464 20480
  Check159.part20448
  Check159.part20464)))
#print axioms Check159.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
