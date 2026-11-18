module
prelude
public import SharedSix0CellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check220.part28160 : Interval test 28160 28176 :=
  interval_of_check _ 28160 16 (by decide +kernel)
theorem Check220.part28176 : Interval test 28176 28192 :=
  interval_of_check _ 28176 16 (by decide +kernel)
theorem Check220.part28192 : Interval test 28192 28208 :=
  interval_of_check _ 28192 16 (by decide +kernel)
theorem Check220.part28208 : Interval test 28208 28224 :=
  interval_of_check _ 28208 16 (by decide +kernel)
theorem Check220.part28224 : Interval test 28224 28240 :=
  interval_of_check _ 28224 16 (by decide +kernel)
theorem Check220.part28240 : Interval test 28240 28256 :=
  interval_of_check _ 28240 16 (by decide +kernel)
theorem Check220.part28256 : Interval test 28256 28272 :=
  interval_of_check _ 28256 16 (by decide +kernel)
theorem Check220.part28272 : Interval test 28272 28288 :=
  interval_of_check _ 28272 16 (by decide +kernel)
theorem Check220.checked : Interval test 28160 28288 :=
  (FiniteChecks.interval_append test 28160 28224 28288
  (FiniteChecks.interval_append test 28160 28192 28224
  (FiniteChecks.interval_append test 28160 28176 28192
  Check220.part28160
  Check220.part28176)
  (FiniteChecks.interval_append test 28192 28208 28224
  Check220.part28192
  Check220.part28208))
  (FiniteChecks.interval_append test 28224 28256 28288
  (FiniteChecks.interval_append test 28224 28240 28256
  Check220.part28224
  Check220.part28240)
  (FiniteChecks.interval_append test 28256 28272 28288
  Check220.part28256
  Check220.part28272)))
#print axioms Check220.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check221.part28288 : Interval test 28288 28304 :=
  interval_of_check _ 28288 16 (by decide +kernel)
theorem Check221.part28304 : Interval test 28304 28320 :=
  interval_of_check _ 28304 16 (by decide +kernel)
theorem Check221.part28320 : Interval test 28320 28336 :=
  interval_of_check _ 28320 16 (by decide +kernel)
theorem Check221.part28336 : Interval test 28336 28352 :=
  interval_of_check _ 28336 16 (by decide +kernel)
theorem Check221.part28352 : Interval test 28352 28368 :=
  interval_of_check _ 28352 16 (by decide +kernel)
theorem Check221.part28368 : Interval test 28368 28384 :=
  interval_of_check _ 28368 16 (by decide +kernel)
theorem Check221.part28384 : Interval test 28384 28400 :=
  interval_of_check _ 28384 16 (by decide +kernel)
theorem Check221.part28400 : Interval test 28400 28416 :=
  interval_of_check _ 28400 16 (by decide +kernel)
theorem Check221.checked : Interval test 28288 28416 :=
  (FiniteChecks.interval_append test 28288 28352 28416
  (FiniteChecks.interval_append test 28288 28320 28352
  (FiniteChecks.interval_append test 28288 28304 28320
  Check221.part28288
  Check221.part28304)
  (FiniteChecks.interval_append test 28320 28336 28352
  Check221.part28320
  Check221.part28336))
  (FiniteChecks.interval_append test 28352 28384 28416
  (FiniteChecks.interval_append test 28352 28368 28384
  Check221.part28352
  Check221.part28368)
  (FiniteChecks.interval_append test 28384 28400 28416
  Check221.part28384
  Check221.part28400)))
#print axioms Check221.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check222.part28416 : Interval test 28416 28432 :=
  interval_of_check _ 28416 16 (by decide +kernel)
theorem Check222.part28432 : Interval test 28432 28448 :=
  interval_of_check _ 28432 16 (by decide +kernel)
theorem Check222.part28448 : Interval test 28448 28464 :=
  interval_of_check _ 28448 16 (by decide +kernel)
theorem Check222.part28464 : Interval test 28464 28480 :=
  interval_of_check _ 28464 16 (by decide +kernel)
theorem Check222.part28480 : Interval test 28480 28496 :=
  interval_of_check _ 28480 16 (by decide +kernel)
theorem Check222.part28496 : Interval test 28496 28512 :=
  interval_of_check _ 28496 16 (by decide +kernel)
theorem Check222.part28512 : Interval test 28512 28528 :=
  interval_of_check _ 28512 16 (by decide +kernel)
theorem Check222.part28528 : Interval test 28528 28544 :=
  interval_of_check _ 28528 16 (by decide +kernel)
theorem Check222.checked : Interval test 28416 28544 :=
  (FiniteChecks.interval_append test 28416 28480 28544
  (FiniteChecks.interval_append test 28416 28448 28480
  (FiniteChecks.interval_append test 28416 28432 28448
  Check222.part28416
  Check222.part28432)
  (FiniteChecks.interval_append test 28448 28464 28480
  Check222.part28448
  Check222.part28464))
  (FiniteChecks.interval_append test 28480 28512 28544
  (FiniteChecks.interval_append test 28480 28496 28512
  Check222.part28480
  Check222.part28496)
  (FiniteChecks.interval_append test 28512 28528 28544
  Check222.part28512
  Check222.part28528)))
#print axioms Check222.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check223.part28544 : Interval test 28544 28560 :=
  interval_of_check _ 28544 16 (by decide +kernel)
theorem Check223.part28560 : Interval test 28560 28576 :=
  interval_of_check _ 28560 16 (by decide +kernel)
theorem Check223.part28576 : Interval test 28576 28592 :=
  interval_of_check _ 28576 16 (by decide +kernel)
theorem Check223.part28592 : Interval test 28592 28608 :=
  interval_of_check _ 28592 16 (by decide +kernel)
theorem Check223.part28608 : Interval test 28608 28624 :=
  interval_of_check _ 28608 16 (by decide +kernel)
theorem Check223.part28624 : Interval test 28624 28640 :=
  interval_of_check _ 28624 16 (by decide +kernel)
theorem Check223.part28640 : Interval test 28640 28656 :=
  interval_of_check _ 28640 16 (by decide +kernel)
theorem Check223.part28656 : Interval test 28656 28672 :=
  interval_of_check _ 28656 16 (by decide +kernel)
theorem Check223.checked : Interval test 28544 28672 :=
  (FiniteChecks.interval_append test 28544 28608 28672
  (FiniteChecks.interval_append test 28544 28576 28608
  (FiniteChecks.interval_append test 28544 28560 28576
  Check223.part28544
  Check223.part28560)
  (FiniteChecks.interval_append test 28576 28592 28608
  Check223.part28576
  Check223.part28592))
  (FiniteChecks.interval_append test 28608 28640 28672
  (FiniteChecks.interval_append test 28608 28624 28640
  Check223.part28608
  Check223.part28624)
  (FiniteChecks.interval_append test 28640 28656 28672
  Check223.part28640
  Check223.part28656)))
#print axioms Check223.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check224.part28672 : Interval test 28672 28688 :=
  interval_of_check _ 28672 16 (by decide +kernel)
theorem Check224.part28688 : Interval test 28688 28704 :=
  interval_of_check _ 28688 16 (by decide +kernel)
theorem Check224.part28704 : Interval test 28704 28720 :=
  interval_of_check _ 28704 16 (by decide +kernel)
theorem Check224.part28720 : Interval test 28720 28736 :=
  interval_of_check _ 28720 16 (by decide +kernel)
theorem Check224.part28736 : Interval test 28736 28752 :=
  interval_of_check _ 28736 16 (by decide +kernel)
theorem Check224.part28752 : Interval test 28752 28768 :=
  interval_of_check _ 28752 16 (by decide +kernel)
theorem Check224.part28768 : Interval test 28768 28784 :=
  interval_of_check _ 28768 16 (by decide +kernel)
theorem Check224.part28784 : Interval test 28784 28800 :=
  interval_of_check _ 28784 16 (by decide +kernel)
theorem Check224.checked : Interval test 28672 28800 :=
  (FiniteChecks.interval_append test 28672 28736 28800
  (FiniteChecks.interval_append test 28672 28704 28736
  (FiniteChecks.interval_append test 28672 28688 28704
  Check224.part28672
  Check224.part28688)
  (FiniteChecks.interval_append test 28704 28720 28736
  Check224.part28704
  Check224.part28720))
  (FiniteChecks.interval_append test 28736 28768 28800
  (FiniteChecks.interval_append test 28736 28752 28768
  Check224.part28736
  Check224.part28752)
  (FiniteChecks.interval_append test 28768 28784 28800
  Check224.part28768
  Check224.part28784)))
#print axioms Check224.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check225.part28800 : Interval test 28800 28816 :=
  interval_of_check _ 28800 16 (by decide +kernel)
theorem Check225.part28816 : Interval test 28816 28832 :=
  interval_of_check _ 28816 16 (by decide +kernel)
theorem Check225.part28832 : Interval test 28832 28848 :=
  interval_of_check _ 28832 16 (by decide +kernel)
theorem Check225.part28848 : Interval test 28848 28864 :=
  interval_of_check _ 28848 16 (by decide +kernel)
theorem Check225.part28864 : Interval test 28864 28880 :=
  interval_of_check _ 28864 16 (by decide +kernel)
theorem Check225.part28880 : Interval test 28880 28896 :=
  interval_of_check _ 28880 16 (by decide +kernel)
theorem Check225.part28896 : Interval test 28896 28912 :=
  interval_of_check _ 28896 16 (by decide +kernel)
theorem Check225.part28912 : Interval test 28912 28928 :=
  interval_of_check _ 28912 16 (by decide +kernel)
theorem Check225.checked : Interval test 28800 28928 :=
  (FiniteChecks.interval_append test 28800 28864 28928
  (FiniteChecks.interval_append test 28800 28832 28864
  (FiniteChecks.interval_append test 28800 28816 28832
  Check225.part28800
  Check225.part28816)
  (FiniteChecks.interval_append test 28832 28848 28864
  Check225.part28832
  Check225.part28848))
  (FiniteChecks.interval_append test 28864 28896 28928
  (FiniteChecks.interval_append test 28864 28880 28896
  Check225.part28864
  Check225.part28880)
  (FiniteChecks.interval_append test 28896 28912 28928
  Check225.part28896
  Check225.part28912)))
#print axioms Check225.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check226.part28928 : Interval test 28928 28944 :=
  interval_of_check _ 28928 16 (by decide +kernel)
theorem Check226.part28944 : Interval test 28944 28960 :=
  interval_of_check _ 28944 16 (by decide +kernel)
theorem Check226.part28960 : Interval test 28960 28976 :=
  interval_of_check _ 28960 16 (by decide +kernel)
theorem Check226.part28976 : Interval test 28976 28992 :=
  interval_of_check _ 28976 16 (by decide +kernel)
theorem Check226.part28992 : Interval test 28992 29008 :=
  interval_of_check _ 28992 16 (by decide +kernel)
theorem Check226.part29008 : Interval test 29008 29024 :=
  interval_of_check _ 29008 16 (by decide +kernel)
theorem Check226.part29024 : Interval test 29024 29040 :=
  interval_of_check _ 29024 16 (by decide +kernel)
theorem Check226.part29040 : Interval test 29040 29056 :=
  interval_of_check _ 29040 16 (by decide +kernel)
theorem Check226.checked : Interval test 28928 29056 :=
  (FiniteChecks.interval_append test 28928 28992 29056
  (FiniteChecks.interval_append test 28928 28960 28992
  (FiniteChecks.interval_append test 28928 28944 28960
  Check226.part28928
  Check226.part28944)
  (FiniteChecks.interval_append test 28960 28976 28992
  Check226.part28960
  Check226.part28976))
  (FiniteChecks.interval_append test 28992 29024 29056
  (FiniteChecks.interval_append test 28992 29008 29024
  Check226.part28992
  Check226.part29008)
  (FiniteChecks.interval_append test 29024 29040 29056
  Check226.part29024
  Check226.part29040)))
#print axioms Check226.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check227.part29056 : Interval test 29056 29072 :=
  interval_of_check _ 29056 16 (by decide +kernel)
theorem Check227.part29072 : Interval test 29072 29088 :=
  interval_of_check _ 29072 16 (by decide +kernel)
theorem Check227.part29088 : Interval test 29088 29104 :=
  interval_of_check _ 29088 16 (by decide +kernel)
theorem Check227.part29104 : Interval test 29104 29120 :=
  interval_of_check _ 29104 16 (by decide +kernel)
theorem Check227.part29120 : Interval test 29120 29136 :=
  interval_of_check _ 29120 16 (by decide +kernel)
theorem Check227.part29136 : Interval test 29136 29152 :=
  interval_of_check _ 29136 16 (by decide +kernel)
theorem Check227.part29152 : Interval test 29152 29168 :=
  interval_of_check _ 29152 16 (by decide +kernel)
theorem Check227.part29168 : Interval test 29168 29184 :=
  interval_of_check _ 29168 16 (by decide +kernel)
theorem Check227.checked : Interval test 29056 29184 :=
  (FiniteChecks.interval_append test 29056 29120 29184
  (FiniteChecks.interval_append test 29056 29088 29120
  (FiniteChecks.interval_append test 29056 29072 29088
  Check227.part29056
  Check227.part29072)
  (FiniteChecks.interval_append test 29088 29104 29120
  Check227.part29088
  Check227.part29104))
  (FiniteChecks.interval_append test 29120 29152 29184
  (FiniteChecks.interval_append test 29120 29136 29152
  Check227.part29120
  Check227.part29136)
  (FiniteChecks.interval_append test 29152 29168 29184
  Check227.part29152
  Check227.part29168)))
#print axioms Check227.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check228.part29184 : Interval test 29184 29200 :=
  interval_of_check _ 29184 16 (by decide +kernel)
theorem Check228.part29200 : Interval test 29200 29216 :=
  interval_of_check _ 29200 16 (by decide +kernel)
theorem Check228.part29216 : Interval test 29216 29232 :=
  interval_of_check _ 29216 16 (by decide +kernel)
theorem Check228.part29232 : Interval test 29232 29248 :=
  interval_of_check _ 29232 16 (by decide +kernel)
theorem Check228.part29248 : Interval test 29248 29264 :=
  interval_of_check _ 29248 16 (by decide +kernel)
theorem Check228.part29264 : Interval test 29264 29280 :=
  interval_of_check _ 29264 16 (by decide +kernel)
theorem Check228.part29280 : Interval test 29280 29296 :=
  interval_of_check _ 29280 16 (by decide +kernel)
theorem Check228.part29296 : Interval test 29296 29312 :=
  interval_of_check _ 29296 16 (by decide +kernel)
theorem Check228.checked : Interval test 29184 29312 :=
  (FiniteChecks.interval_append test 29184 29248 29312
  (FiniteChecks.interval_append test 29184 29216 29248
  (FiniteChecks.interval_append test 29184 29200 29216
  Check228.part29184
  Check228.part29200)
  (FiniteChecks.interval_append test 29216 29232 29248
  Check228.part29216
  Check228.part29232))
  (FiniteChecks.interval_append test 29248 29280 29312
  (FiniteChecks.interval_append test 29248 29264 29280
  Check228.part29248
  Check228.part29264)
  (FiniteChecks.interval_append test 29280 29296 29312
  Check228.part29280
  Check228.part29296)))
#print axioms Check228.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check229.part29312 : Interval test 29312 29328 :=
  interval_of_check _ 29312 16 (by decide +kernel)
theorem Check229.part29328 : Interval test 29328 29344 :=
  interval_of_check _ 29328 16 (by decide +kernel)
theorem Check229.part29344 : Interval test 29344 29360 :=
  interval_of_check _ 29344 16 (by decide +kernel)
theorem Check229.part29360 : Interval test 29360 29376 :=
  interval_of_check _ 29360 16 (by decide +kernel)
theorem Check229.part29376 : Interval test 29376 29392 :=
  interval_of_check _ 29376 16 (by decide +kernel)
theorem Check229.part29392 : Interval test 29392 29408 :=
  interval_of_check _ 29392 16 (by decide +kernel)
theorem Check229.part29408 : Interval test 29408 29424 :=
  interval_of_check _ 29408 16 (by decide +kernel)
theorem Check229.part29424 : Interval test 29424 29440 :=
  interval_of_check _ 29424 16 (by decide +kernel)
theorem Check229.checked : Interval test 29312 29440 :=
  (FiniteChecks.interval_append test 29312 29376 29440
  (FiniteChecks.interval_append test 29312 29344 29376
  (FiniteChecks.interval_append test 29312 29328 29344
  Check229.part29312
  Check229.part29328)
  (FiniteChecks.interval_append test 29344 29360 29376
  Check229.part29344
  Check229.part29360))
  (FiniteChecks.interval_append test 29376 29408 29440
  (FiniteChecks.interval_append test 29376 29392 29408
  Check229.part29376
  Check229.part29392)
  (FiniteChecks.interval_append test 29408 29424 29440
  Check229.part29408
  Check229.part29424)))
#print axioms Check229.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check230.part29440 : Interval test 29440 29456 :=
  interval_of_check _ 29440 16 (by decide +kernel)
theorem Check230.part29456 : Interval test 29456 29472 :=
  interval_of_check _ 29456 16 (by decide +kernel)
theorem Check230.part29472 : Interval test 29472 29488 :=
  interval_of_check _ 29472 16 (by decide +kernel)
theorem Check230.part29488 : Interval test 29488 29504 :=
  interval_of_check _ 29488 16 (by decide +kernel)
theorem Check230.part29504 : Interval test 29504 29520 :=
  interval_of_check _ 29504 16 (by decide +kernel)
theorem Check230.part29520 : Interval test 29520 29536 :=
  interval_of_check _ 29520 16 (by decide +kernel)
theorem Check230.part29536 : Interval test 29536 29552 :=
  interval_of_check _ 29536 16 (by decide +kernel)
theorem Check230.part29552 : Interval test 29552 29568 :=
  interval_of_check _ 29552 16 (by decide +kernel)
theorem Check230.checked : Interval test 29440 29568 :=
  (FiniteChecks.interval_append test 29440 29504 29568
  (FiniteChecks.interval_append test 29440 29472 29504
  (FiniteChecks.interval_append test 29440 29456 29472
  Check230.part29440
  Check230.part29456)
  (FiniteChecks.interval_append test 29472 29488 29504
  Check230.part29472
  Check230.part29488))
  (FiniteChecks.interval_append test 29504 29536 29568
  (FiniteChecks.interval_append test 29504 29520 29536
  Check230.part29504
  Check230.part29520)
  (FiniteChecks.interval_append test 29536 29552 29568
  Check230.part29536
  Check230.part29552)))
#print axioms Check230.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check231.part29568 : Interval test 29568 29584 :=
  interval_of_check _ 29568 16 (by decide +kernel)
theorem Check231.part29584 : Interval test 29584 29600 :=
  interval_of_check _ 29584 16 (by decide +kernel)
theorem Check231.part29600 : Interval test 29600 29616 :=
  interval_of_check _ 29600 16 (by decide +kernel)
theorem Check231.part29616 : Interval test 29616 29632 :=
  interval_of_check _ 29616 16 (by decide +kernel)
theorem Check231.part29632 : Interval test 29632 29648 :=
  interval_of_check _ 29632 16 (by decide +kernel)
theorem Check231.part29648 : Interval test 29648 29664 :=
  interval_of_check _ 29648 16 (by decide +kernel)
theorem Check231.part29664 : Interval test 29664 29680 :=
  interval_of_check _ 29664 16 (by decide +kernel)
theorem Check231.part29680 : Interval test 29680 29696 :=
  interval_of_check _ 29680 16 (by decide +kernel)
theorem Check231.checked : Interval test 29568 29696 :=
  (FiniteChecks.interval_append test 29568 29632 29696
  (FiniteChecks.interval_append test 29568 29600 29632
  (FiniteChecks.interval_append test 29568 29584 29600
  Check231.part29568
  Check231.part29584)
  (FiniteChecks.interval_append test 29600 29616 29632
  Check231.part29600
  Check231.part29616))
  (FiniteChecks.interval_append test 29632 29664 29696
  (FiniteChecks.interval_append test 29632 29648 29664
  Check231.part29632
  Check231.part29648)
  (FiniteChecks.interval_append test 29664 29680 29696
  Check231.part29664
  Check231.part29680)))
#print axioms Check231.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check232.part29696 : Interval test 29696 29712 :=
  interval_of_check _ 29696 16 (by decide +kernel)
theorem Check232.part29712 : Interval test 29712 29728 :=
  interval_of_check _ 29712 16 (by decide +kernel)
theorem Check232.part29728 : Interval test 29728 29744 :=
  interval_of_check _ 29728 16 (by decide +kernel)
theorem Check232.part29744 : Interval test 29744 29760 :=
  interval_of_check _ 29744 16 (by decide +kernel)
theorem Check232.part29760 : Interval test 29760 29776 :=
  interval_of_check _ 29760 16 (by decide +kernel)
theorem Check232.part29776 : Interval test 29776 29792 :=
  interval_of_check _ 29776 16 (by decide +kernel)
theorem Check232.part29792 : Interval test 29792 29808 :=
  interval_of_check _ 29792 16 (by decide +kernel)
theorem Check232.part29808 : Interval test 29808 29824 :=
  interval_of_check _ 29808 16 (by decide +kernel)
theorem Check232.checked : Interval test 29696 29824 :=
  (FiniteChecks.interval_append test 29696 29760 29824
  (FiniteChecks.interval_append test 29696 29728 29760
  (FiniteChecks.interval_append test 29696 29712 29728
  Check232.part29696
  Check232.part29712)
  (FiniteChecks.interval_append test 29728 29744 29760
  Check232.part29728
  Check232.part29744))
  (FiniteChecks.interval_append test 29760 29792 29824
  (FiniteChecks.interval_append test 29760 29776 29792
  Check232.part29760
  Check232.part29776)
  (FiniteChecks.interval_append test 29792 29808 29824
  Check232.part29792
  Check232.part29808)))
#print axioms Check232.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check233.part29824 : Interval test 29824 29840 :=
  interval_of_check _ 29824 16 (by decide +kernel)
theorem Check233.part29840 : Interval test 29840 29856 :=
  interval_of_check _ 29840 16 (by decide +kernel)
theorem Check233.part29856 : Interval test 29856 29872 :=
  interval_of_check _ 29856 16 (by decide +kernel)
theorem Check233.part29872 : Interval test 29872 29888 :=
  interval_of_check _ 29872 16 (by decide +kernel)
theorem Check233.part29888 : Interval test 29888 29904 :=
  interval_of_check _ 29888 16 (by decide +kernel)
theorem Check233.part29904 : Interval test 29904 29920 :=
  interval_of_check _ 29904 16 (by decide +kernel)
theorem Check233.part29920 : Interval test 29920 29936 :=
  interval_of_check _ 29920 16 (by decide +kernel)
theorem Check233.part29936 : Interval test 29936 29952 :=
  interval_of_check _ 29936 16 (by decide +kernel)
theorem Check233.checked : Interval test 29824 29952 :=
  (FiniteChecks.interval_append test 29824 29888 29952
  (FiniteChecks.interval_append test 29824 29856 29888
  (FiniteChecks.interval_append test 29824 29840 29856
  Check233.part29824
  Check233.part29840)
  (FiniteChecks.interval_append test 29856 29872 29888
  Check233.part29856
  Check233.part29872))
  (FiniteChecks.interval_append test 29888 29920 29952
  (FiniteChecks.interval_append test 29888 29904 29920
  Check233.part29888
  Check233.part29904)
  (FiniteChecks.interval_append test 29920 29936 29952
  Check233.part29920
  Check233.part29936)))
#print axioms Check233.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check234.part29952 : Interval test 29952 29968 :=
  interval_of_check _ 29952 16 (by decide +kernel)
theorem Check234.part29968 : Interval test 29968 29984 :=
  interval_of_check _ 29968 16 (by decide +kernel)
theorem Check234.part29984 : Interval test 29984 30000 :=
  interval_of_check _ 29984 16 (by decide +kernel)
theorem Check234.part30000 : Interval test 30000 30016 :=
  interval_of_check _ 30000 16 (by decide +kernel)
theorem Check234.part30016 : Interval test 30016 30032 :=
  interval_of_check _ 30016 16 (by decide +kernel)
theorem Check234.part30032 : Interval test 30032 30048 :=
  interval_of_check _ 30032 16 (by decide +kernel)
theorem Check234.part30048 : Interval test 30048 30064 :=
  interval_of_check _ 30048 16 (by decide +kernel)
theorem Check234.part30064 : Interval test 30064 30080 :=
  interval_of_check _ 30064 16 (by decide +kernel)
theorem Check234.checked : Interval test 29952 30080 :=
  (FiniteChecks.interval_append test 29952 30016 30080
  (FiniteChecks.interval_append test 29952 29984 30016
  (FiniteChecks.interval_append test 29952 29968 29984
  Check234.part29952
  Check234.part29968)
  (FiniteChecks.interval_append test 29984 30000 30016
  Check234.part29984
  Check234.part30000))
  (FiniteChecks.interval_append test 30016 30048 30080
  (FiniteChecks.interval_append test 30016 30032 30048
  Check234.part30016
  Check234.part30032)
  (FiniteChecks.interval_append test 30048 30064 30080
  Check234.part30048
  Check234.part30064)))
#print axioms Check234.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check235.part30080 : Interval test 30080 30096 :=
  interval_of_check _ 30080 16 (by decide +kernel)
theorem Check235.part30096 : Interval test 30096 30112 :=
  interval_of_check _ 30096 16 (by decide +kernel)
theorem Check235.part30112 : Interval test 30112 30128 :=
  interval_of_check _ 30112 16 (by decide +kernel)
theorem Check235.part30128 : Interval test 30128 30144 :=
  interval_of_check _ 30128 16 (by decide +kernel)
theorem Check235.part30144 : Interval test 30144 30160 :=
  interval_of_check _ 30144 16 (by decide +kernel)
theorem Check235.part30160 : Interval test 30160 30176 :=
  interval_of_check _ 30160 16 (by decide +kernel)
theorem Check235.part30176 : Interval test 30176 30192 :=
  interval_of_check _ 30176 16 (by decide +kernel)
theorem Check235.part30192 : Interval test 30192 30208 :=
  interval_of_check _ 30192 16 (by decide +kernel)
theorem Check235.checked : Interval test 30080 30208 :=
  (FiniteChecks.interval_append test 30080 30144 30208
  (FiniteChecks.interval_append test 30080 30112 30144
  (FiniteChecks.interval_append test 30080 30096 30112
  Check235.part30080
  Check235.part30096)
  (FiniteChecks.interval_append test 30112 30128 30144
  Check235.part30112
  Check235.part30128))
  (FiniteChecks.interval_append test 30144 30176 30208
  (FiniteChecks.interval_append test 30144 30160 30176
  Check235.part30144
  Check235.part30160)
  (FiniteChecks.interval_append test 30176 30192 30208
  Check235.part30176
  Check235.part30192)))
#print axioms Check235.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check236.part30208 : Interval test 30208 30224 :=
  interval_of_check _ 30208 16 (by decide +kernel)
theorem Check236.part30224 : Interval test 30224 30240 :=
  interval_of_check _ 30224 16 (by decide +kernel)
theorem Check236.part30240 : Interval test 30240 30256 :=
  interval_of_check _ 30240 16 (by decide +kernel)
theorem Check236.part30256 : Interval test 30256 30272 :=
  interval_of_check _ 30256 16 (by decide +kernel)
theorem Check236.part30272 : Interval test 30272 30288 :=
  interval_of_check _ 30272 16 (by decide +kernel)
theorem Check236.part30288 : Interval test 30288 30304 :=
  interval_of_check _ 30288 16 (by decide +kernel)
theorem Check236.part30304 : Interval test 30304 30320 :=
  interval_of_check _ 30304 16 (by decide +kernel)
theorem Check236.part30320 : Interval test 30320 30336 :=
  interval_of_check _ 30320 16 (by decide +kernel)
theorem Check236.checked : Interval test 30208 30336 :=
  (FiniteChecks.interval_append test 30208 30272 30336
  (FiniteChecks.interval_append test 30208 30240 30272
  (FiniteChecks.interval_append test 30208 30224 30240
  Check236.part30208
  Check236.part30224)
  (FiniteChecks.interval_append test 30240 30256 30272
  Check236.part30240
  Check236.part30256))
  (FiniteChecks.interval_append test 30272 30304 30336
  (FiniteChecks.interval_append test 30272 30288 30304
  Check236.part30272
  Check236.part30288)
  (FiniteChecks.interval_append test 30304 30320 30336
  Check236.part30304
  Check236.part30320)))
#print axioms Check236.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check237.part30336 : Interval test 30336 30352 :=
  interval_of_check _ 30336 16 (by decide +kernel)
theorem Check237.part30352 : Interval test 30352 30368 :=
  interval_of_check _ 30352 16 (by decide +kernel)
theorem Check237.part30368 : Interval test 30368 30384 :=
  interval_of_check _ 30368 16 (by decide +kernel)
theorem Check237.part30384 : Interval test 30384 30400 :=
  interval_of_check _ 30384 16 (by decide +kernel)
theorem Check237.part30400 : Interval test 30400 30416 :=
  interval_of_check _ 30400 16 (by decide +kernel)
theorem Check237.part30416 : Interval test 30416 30432 :=
  interval_of_check _ 30416 16 (by decide +kernel)
theorem Check237.part30432 : Interval test 30432 30448 :=
  interval_of_check _ 30432 16 (by decide +kernel)
theorem Check237.part30448 : Interval test 30448 30464 :=
  interval_of_check _ 30448 16 (by decide +kernel)
theorem Check237.checked : Interval test 30336 30464 :=
  (FiniteChecks.interval_append test 30336 30400 30464
  (FiniteChecks.interval_append test 30336 30368 30400
  (FiniteChecks.interval_append test 30336 30352 30368
  Check237.part30336
  Check237.part30352)
  (FiniteChecks.interval_append test 30368 30384 30400
  Check237.part30368
  Check237.part30384))
  (FiniteChecks.interval_append test 30400 30432 30464
  (FiniteChecks.interval_append test 30400 30416 30432
  Check237.part30400
  Check237.part30416)
  (FiniteChecks.interval_append test 30432 30448 30464
  Check237.part30432
  Check237.part30448)))
#print axioms Check237.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check238.part30464 : Interval test 30464 30480 :=
  interval_of_check _ 30464 16 (by decide +kernel)
theorem Check238.part30480 : Interval test 30480 30496 :=
  interval_of_check _ 30480 16 (by decide +kernel)
theorem Check238.part30496 : Interval test 30496 30512 :=
  interval_of_check _ 30496 16 (by decide +kernel)
theorem Check238.part30512 : Interval test 30512 30528 :=
  interval_of_check _ 30512 16 (by decide +kernel)
theorem Check238.part30528 : Interval test 30528 30544 :=
  interval_of_check _ 30528 16 (by decide +kernel)
theorem Check238.part30544 : Interval test 30544 30560 :=
  interval_of_check _ 30544 16 (by decide +kernel)
theorem Check238.part30560 : Interval test 30560 30576 :=
  interval_of_check _ 30560 16 (by decide +kernel)
theorem Check238.part30576 : Interval test 30576 30592 :=
  interval_of_check _ 30576 16 (by decide +kernel)
theorem Check238.checked : Interval test 30464 30592 :=
  (FiniteChecks.interval_append test 30464 30528 30592
  (FiniteChecks.interval_append test 30464 30496 30528
  (FiniteChecks.interval_append test 30464 30480 30496
  Check238.part30464
  Check238.part30480)
  (FiniteChecks.interval_append test 30496 30512 30528
  Check238.part30496
  Check238.part30512))
  (FiniteChecks.interval_append test 30528 30560 30592
  (FiniteChecks.interval_append test 30528 30544 30560
  Check238.part30528
  Check238.part30544)
  (FiniteChecks.interval_append test 30560 30576 30592
  Check238.part30560
  Check238.part30576)))
#print axioms Check238.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check239.part30592 : Interval test 30592 30608 :=
  interval_of_check _ 30592 16 (by decide +kernel)
theorem Check239.part30608 : Interval test 30608 30624 :=
  interval_of_check _ 30608 16 (by decide +kernel)
theorem Check239.part30624 : Interval test 30624 30640 :=
  interval_of_check _ 30624 16 (by decide +kernel)
theorem Check239.part30640 : Interval test 30640 30656 :=
  interval_of_check _ 30640 16 (by decide +kernel)
theorem Check239.part30656 : Interval test 30656 30672 :=
  interval_of_check _ 30656 16 (by decide +kernel)
theorem Check239.part30672 : Interval test 30672 30688 :=
  interval_of_check _ 30672 16 (by decide +kernel)
theorem Check239.part30688 : Interval test 30688 30704 :=
  interval_of_check _ 30688 16 (by decide +kernel)
theorem Check239.part30704 : Interval test 30704 30720 :=
  interval_of_check _ 30704 16 (by decide +kernel)
theorem Check239.checked : Interval test 30592 30720 :=
  (FiniteChecks.interval_append test 30592 30656 30720
  (FiniteChecks.interval_append test 30592 30624 30656
  (FiniteChecks.interval_append test 30592 30608 30624
  Check239.part30592
  Check239.part30608)
  (FiniteChecks.interval_append test 30624 30640 30656
  Check239.part30624
  Check239.part30640))
  (FiniteChecks.interval_append test 30656 30688 30720
  (FiniteChecks.interval_append test 30656 30672 30688
  Check239.part30656
  Check239.part30672)
  (FiniteChecks.interval_append test 30688 30704 30720
  Check239.part30688
  Check239.part30704)))
#print axioms Check239.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
