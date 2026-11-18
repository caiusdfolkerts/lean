module
prelude
public import SharedSix0CellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check280.part35840 : Interval test 35840 35856 :=
  interval_of_check _ 35840 16 (by decide +kernel)
theorem Check280.part35856 : Interval test 35856 35872 :=
  interval_of_check _ 35856 16 (by decide +kernel)
theorem Check280.part35872 : Interval test 35872 35888 :=
  interval_of_check _ 35872 16 (by decide +kernel)
theorem Check280.part35888 : Interval test 35888 35904 :=
  interval_of_check _ 35888 16 (by decide +kernel)
theorem Check280.part35904 : Interval test 35904 35920 :=
  interval_of_check _ 35904 16 (by decide +kernel)
theorem Check280.part35920 : Interval test 35920 35936 :=
  interval_of_check _ 35920 16 (by decide +kernel)
theorem Check280.part35936 : Interval test 35936 35952 :=
  interval_of_check _ 35936 16 (by decide +kernel)
theorem Check280.part35952 : Interval test 35952 35968 :=
  interval_of_check _ 35952 16 (by decide +kernel)
theorem Check280.checked : Interval test 35840 35968 :=
  (FiniteChecks.interval_append test 35840 35904 35968
  (FiniteChecks.interval_append test 35840 35872 35904
  (FiniteChecks.interval_append test 35840 35856 35872
  Check280.part35840
  Check280.part35856)
  (FiniteChecks.interval_append test 35872 35888 35904
  Check280.part35872
  Check280.part35888))
  (FiniteChecks.interval_append test 35904 35936 35968
  (FiniteChecks.interval_append test 35904 35920 35936
  Check280.part35904
  Check280.part35920)
  (FiniteChecks.interval_append test 35936 35952 35968
  Check280.part35936
  Check280.part35952)))
#print axioms Check280.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check281.part35968 : Interval test 35968 35984 :=
  interval_of_check _ 35968 16 (by decide +kernel)
theorem Check281.part35984 : Interval test 35984 36000 :=
  interval_of_check _ 35984 16 (by decide +kernel)
theorem Check281.part36000 : Interval test 36000 36016 :=
  interval_of_check _ 36000 16 (by decide +kernel)
theorem Check281.part36016 : Interval test 36016 36032 :=
  interval_of_check _ 36016 16 (by decide +kernel)
theorem Check281.part36032 : Interval test 36032 36048 :=
  interval_of_check _ 36032 16 (by decide +kernel)
theorem Check281.part36048 : Interval test 36048 36064 :=
  interval_of_check _ 36048 16 (by decide +kernel)
theorem Check281.part36064 : Interval test 36064 36080 :=
  interval_of_check _ 36064 16 (by decide +kernel)
theorem Check281.part36080 : Interval test 36080 36096 :=
  interval_of_check _ 36080 16 (by decide +kernel)
theorem Check281.checked : Interval test 35968 36096 :=
  (FiniteChecks.interval_append test 35968 36032 36096
  (FiniteChecks.interval_append test 35968 36000 36032
  (FiniteChecks.interval_append test 35968 35984 36000
  Check281.part35968
  Check281.part35984)
  (FiniteChecks.interval_append test 36000 36016 36032
  Check281.part36000
  Check281.part36016))
  (FiniteChecks.interval_append test 36032 36064 36096
  (FiniteChecks.interval_append test 36032 36048 36064
  Check281.part36032
  Check281.part36048)
  (FiniteChecks.interval_append test 36064 36080 36096
  Check281.part36064
  Check281.part36080)))
#print axioms Check281.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check282.part36096 : Interval test 36096 36112 :=
  interval_of_check _ 36096 16 (by decide +kernel)
theorem Check282.part36112 : Interval test 36112 36128 :=
  interval_of_check _ 36112 16 (by decide +kernel)
theorem Check282.part36128 : Interval test 36128 36144 :=
  interval_of_check _ 36128 16 (by decide +kernel)
theorem Check282.part36144 : Interval test 36144 36160 :=
  interval_of_check _ 36144 16 (by decide +kernel)
theorem Check282.part36160 : Interval test 36160 36176 :=
  interval_of_check _ 36160 16 (by decide +kernel)
theorem Check282.part36176 : Interval test 36176 36192 :=
  interval_of_check _ 36176 16 (by decide +kernel)
theorem Check282.part36192 : Interval test 36192 36208 :=
  interval_of_check _ 36192 16 (by decide +kernel)
theorem Check282.part36208 : Interval test 36208 36224 :=
  interval_of_check _ 36208 16 (by decide +kernel)
theorem Check282.checked : Interval test 36096 36224 :=
  (FiniteChecks.interval_append test 36096 36160 36224
  (FiniteChecks.interval_append test 36096 36128 36160
  (FiniteChecks.interval_append test 36096 36112 36128
  Check282.part36096
  Check282.part36112)
  (FiniteChecks.interval_append test 36128 36144 36160
  Check282.part36128
  Check282.part36144))
  (FiniteChecks.interval_append test 36160 36192 36224
  (FiniteChecks.interval_append test 36160 36176 36192
  Check282.part36160
  Check282.part36176)
  (FiniteChecks.interval_append test 36192 36208 36224
  Check282.part36192
  Check282.part36208)))
#print axioms Check282.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check283.part36224 : Interval test 36224 36240 :=
  interval_of_check _ 36224 16 (by decide +kernel)
theorem Check283.part36240 : Interval test 36240 36256 :=
  interval_of_check _ 36240 16 (by decide +kernel)
theorem Check283.part36256 : Interval test 36256 36272 :=
  interval_of_check _ 36256 16 (by decide +kernel)
theorem Check283.part36272 : Interval test 36272 36288 :=
  interval_of_check _ 36272 16 (by decide +kernel)
theorem Check283.part36288 : Interval test 36288 36304 :=
  interval_of_check _ 36288 16 (by decide +kernel)
theorem Check283.part36304 : Interval test 36304 36320 :=
  interval_of_check _ 36304 16 (by decide +kernel)
theorem Check283.part36320 : Interval test 36320 36336 :=
  interval_of_check _ 36320 16 (by decide +kernel)
theorem Check283.part36336 : Interval test 36336 36352 :=
  interval_of_check _ 36336 16 (by decide +kernel)
theorem Check283.checked : Interval test 36224 36352 :=
  (FiniteChecks.interval_append test 36224 36288 36352
  (FiniteChecks.interval_append test 36224 36256 36288
  (FiniteChecks.interval_append test 36224 36240 36256
  Check283.part36224
  Check283.part36240)
  (FiniteChecks.interval_append test 36256 36272 36288
  Check283.part36256
  Check283.part36272))
  (FiniteChecks.interval_append test 36288 36320 36352
  (FiniteChecks.interval_append test 36288 36304 36320
  Check283.part36288
  Check283.part36304)
  (FiniteChecks.interval_append test 36320 36336 36352
  Check283.part36320
  Check283.part36336)))
#print axioms Check283.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check284.part36352 : Interval test 36352 36368 :=
  interval_of_check _ 36352 16 (by decide +kernel)
theorem Check284.part36368 : Interval test 36368 36384 :=
  interval_of_check _ 36368 16 (by decide +kernel)
theorem Check284.part36384 : Interval test 36384 36400 :=
  interval_of_check _ 36384 16 (by decide +kernel)
theorem Check284.part36400 : Interval test 36400 36416 :=
  interval_of_check _ 36400 16 (by decide +kernel)
theorem Check284.part36416 : Interval test 36416 36432 :=
  interval_of_check _ 36416 16 (by decide +kernel)
theorem Check284.part36432 : Interval test 36432 36448 :=
  interval_of_check _ 36432 16 (by decide +kernel)
theorem Check284.part36448 : Interval test 36448 36464 :=
  interval_of_check _ 36448 16 (by decide +kernel)
theorem Check284.part36464 : Interval test 36464 36480 :=
  interval_of_check _ 36464 16 (by decide +kernel)
theorem Check284.checked : Interval test 36352 36480 :=
  (FiniteChecks.interval_append test 36352 36416 36480
  (FiniteChecks.interval_append test 36352 36384 36416
  (FiniteChecks.interval_append test 36352 36368 36384
  Check284.part36352
  Check284.part36368)
  (FiniteChecks.interval_append test 36384 36400 36416
  Check284.part36384
  Check284.part36400))
  (FiniteChecks.interval_append test 36416 36448 36480
  (FiniteChecks.interval_append test 36416 36432 36448
  Check284.part36416
  Check284.part36432)
  (FiniteChecks.interval_append test 36448 36464 36480
  Check284.part36448
  Check284.part36464)))
#print axioms Check284.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check285.part36480 : Interval test 36480 36496 :=
  interval_of_check _ 36480 16 (by decide +kernel)
theorem Check285.part36496 : Interval test 36496 36512 :=
  interval_of_check _ 36496 16 (by decide +kernel)
theorem Check285.part36512 : Interval test 36512 36528 :=
  interval_of_check _ 36512 16 (by decide +kernel)
theorem Check285.part36528 : Interval test 36528 36544 :=
  interval_of_check _ 36528 16 (by decide +kernel)
theorem Check285.part36544 : Interval test 36544 36560 :=
  interval_of_check _ 36544 16 (by decide +kernel)
theorem Check285.part36560 : Interval test 36560 36576 :=
  interval_of_check _ 36560 16 (by decide +kernel)
theorem Check285.part36576 : Interval test 36576 36592 :=
  interval_of_check _ 36576 16 (by decide +kernel)
theorem Check285.part36592 : Interval test 36592 36608 :=
  interval_of_check _ 36592 16 (by decide +kernel)
theorem Check285.checked : Interval test 36480 36608 :=
  (FiniteChecks.interval_append test 36480 36544 36608
  (FiniteChecks.interval_append test 36480 36512 36544
  (FiniteChecks.interval_append test 36480 36496 36512
  Check285.part36480
  Check285.part36496)
  (FiniteChecks.interval_append test 36512 36528 36544
  Check285.part36512
  Check285.part36528))
  (FiniteChecks.interval_append test 36544 36576 36608
  (FiniteChecks.interval_append test 36544 36560 36576
  Check285.part36544
  Check285.part36560)
  (FiniteChecks.interval_append test 36576 36592 36608
  Check285.part36576
  Check285.part36592)))
#print axioms Check285.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check286.part36608 : Interval test 36608 36624 :=
  interval_of_check _ 36608 16 (by decide +kernel)
theorem Check286.part36624 : Interval test 36624 36640 :=
  interval_of_check _ 36624 16 (by decide +kernel)
theorem Check286.part36640 : Interval test 36640 36656 :=
  interval_of_check _ 36640 16 (by decide +kernel)
theorem Check286.part36656 : Interval test 36656 36672 :=
  interval_of_check _ 36656 16 (by decide +kernel)
theorem Check286.part36672 : Interval test 36672 36688 :=
  interval_of_check _ 36672 16 (by decide +kernel)
theorem Check286.part36688 : Interval test 36688 36704 :=
  interval_of_check _ 36688 16 (by decide +kernel)
theorem Check286.part36704 : Interval test 36704 36720 :=
  interval_of_check _ 36704 16 (by decide +kernel)
theorem Check286.part36720 : Interval test 36720 36736 :=
  interval_of_check _ 36720 16 (by decide +kernel)
theorem Check286.checked : Interval test 36608 36736 :=
  (FiniteChecks.interval_append test 36608 36672 36736
  (FiniteChecks.interval_append test 36608 36640 36672
  (FiniteChecks.interval_append test 36608 36624 36640
  Check286.part36608
  Check286.part36624)
  (FiniteChecks.interval_append test 36640 36656 36672
  Check286.part36640
  Check286.part36656))
  (FiniteChecks.interval_append test 36672 36704 36736
  (FiniteChecks.interval_append test 36672 36688 36704
  Check286.part36672
  Check286.part36688)
  (FiniteChecks.interval_append test 36704 36720 36736
  Check286.part36704
  Check286.part36720)))
#print axioms Check286.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check287.part36736 : Interval test 36736 36752 :=
  interval_of_check _ 36736 16 (by decide +kernel)
theorem Check287.part36752 : Interval test 36752 36768 :=
  interval_of_check _ 36752 16 (by decide +kernel)
theorem Check287.part36768 : Interval test 36768 36784 :=
  interval_of_check _ 36768 16 (by decide +kernel)
theorem Check287.part36784 : Interval test 36784 36800 :=
  interval_of_check _ 36784 16 (by decide +kernel)
theorem Check287.part36800 : Interval test 36800 36816 :=
  interval_of_check _ 36800 16 (by decide +kernel)
theorem Check287.part36816 : Interval test 36816 36832 :=
  interval_of_check _ 36816 16 (by decide +kernel)
theorem Check287.part36832 : Interval test 36832 36848 :=
  interval_of_check _ 36832 16 (by decide +kernel)
theorem Check287.part36848 : Interval test 36848 36864 :=
  interval_of_check _ 36848 16 (by decide +kernel)
theorem Check287.checked : Interval test 36736 36864 :=
  (FiniteChecks.interval_append test 36736 36800 36864
  (FiniteChecks.interval_append test 36736 36768 36800
  (FiniteChecks.interval_append test 36736 36752 36768
  Check287.part36736
  Check287.part36752)
  (FiniteChecks.interval_append test 36768 36784 36800
  Check287.part36768
  Check287.part36784))
  (FiniteChecks.interval_append test 36800 36832 36864
  (FiniteChecks.interval_append test 36800 36816 36832
  Check287.part36800
  Check287.part36816)
  (FiniteChecks.interval_append test 36832 36848 36864
  Check287.part36832
  Check287.part36848)))
#print axioms Check287.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check288.part36864 : Interval test 36864 36880 :=
  interval_of_check _ 36864 16 (by decide +kernel)
theorem Check288.part36880 : Interval test 36880 36896 :=
  interval_of_check _ 36880 16 (by decide +kernel)
theorem Check288.part36896 : Interval test 36896 36912 :=
  interval_of_check _ 36896 16 (by decide +kernel)
theorem Check288.part36912 : Interval test 36912 36928 :=
  interval_of_check _ 36912 16 (by decide +kernel)
theorem Check288.part36928 : Interval test 36928 36944 :=
  interval_of_check _ 36928 16 (by decide +kernel)
theorem Check288.part36944 : Interval test 36944 36960 :=
  interval_of_check _ 36944 16 (by decide +kernel)
theorem Check288.part36960 : Interval test 36960 36976 :=
  interval_of_check _ 36960 16 (by decide +kernel)
theorem Check288.part36976 : Interval test 36976 36992 :=
  interval_of_check _ 36976 16 (by decide +kernel)
theorem Check288.checked : Interval test 36864 36992 :=
  (FiniteChecks.interval_append test 36864 36928 36992
  (FiniteChecks.interval_append test 36864 36896 36928
  (FiniteChecks.interval_append test 36864 36880 36896
  Check288.part36864
  Check288.part36880)
  (FiniteChecks.interval_append test 36896 36912 36928
  Check288.part36896
  Check288.part36912))
  (FiniteChecks.interval_append test 36928 36960 36992
  (FiniteChecks.interval_append test 36928 36944 36960
  Check288.part36928
  Check288.part36944)
  (FiniteChecks.interval_append test 36960 36976 36992
  Check288.part36960
  Check288.part36976)))
#print axioms Check288.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check289.part36992 : Interval test 36992 37008 :=
  interval_of_check _ 36992 16 (by decide +kernel)
theorem Check289.part37008 : Interval test 37008 37024 :=
  interval_of_check _ 37008 16 (by decide +kernel)
theorem Check289.part37024 : Interval test 37024 37040 :=
  interval_of_check _ 37024 16 (by decide +kernel)
theorem Check289.part37040 : Interval test 37040 37056 :=
  interval_of_check _ 37040 16 (by decide +kernel)
theorem Check289.part37056 : Interval test 37056 37072 :=
  interval_of_check _ 37056 16 (by decide +kernel)
theorem Check289.part37072 : Interval test 37072 37088 :=
  interval_of_check _ 37072 16 (by decide +kernel)
theorem Check289.part37088 : Interval test 37088 37104 :=
  interval_of_check _ 37088 16 (by decide +kernel)
theorem Check289.part37104 : Interval test 37104 37120 :=
  interval_of_check _ 37104 16 (by decide +kernel)
theorem Check289.checked : Interval test 36992 37120 :=
  (FiniteChecks.interval_append test 36992 37056 37120
  (FiniteChecks.interval_append test 36992 37024 37056
  (FiniteChecks.interval_append test 36992 37008 37024
  Check289.part36992
  Check289.part37008)
  (FiniteChecks.interval_append test 37024 37040 37056
  Check289.part37024
  Check289.part37040))
  (FiniteChecks.interval_append test 37056 37088 37120
  (FiniteChecks.interval_append test 37056 37072 37088
  Check289.part37056
  Check289.part37072)
  (FiniteChecks.interval_append test 37088 37104 37120
  Check289.part37088
  Check289.part37104)))
#print axioms Check289.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check290.part37120 : Interval test 37120 37136 :=
  interval_of_check _ 37120 16 (by decide +kernel)
theorem Check290.part37136 : Interval test 37136 37152 :=
  interval_of_check _ 37136 16 (by decide +kernel)
theorem Check290.part37152 : Interval test 37152 37168 :=
  interval_of_check _ 37152 16 (by decide +kernel)
theorem Check290.part37168 : Interval test 37168 37184 :=
  interval_of_check _ 37168 16 (by decide +kernel)
theorem Check290.part37184 : Interval test 37184 37200 :=
  interval_of_check _ 37184 16 (by decide +kernel)
theorem Check290.part37200 : Interval test 37200 37216 :=
  interval_of_check _ 37200 16 (by decide +kernel)
theorem Check290.part37216 : Interval test 37216 37232 :=
  interval_of_check _ 37216 16 (by decide +kernel)
theorem Check290.part37232 : Interval test 37232 37248 :=
  interval_of_check _ 37232 16 (by decide +kernel)
theorem Check290.checked : Interval test 37120 37248 :=
  (FiniteChecks.interval_append test 37120 37184 37248
  (FiniteChecks.interval_append test 37120 37152 37184
  (FiniteChecks.interval_append test 37120 37136 37152
  Check290.part37120
  Check290.part37136)
  (FiniteChecks.interval_append test 37152 37168 37184
  Check290.part37152
  Check290.part37168))
  (FiniteChecks.interval_append test 37184 37216 37248
  (FiniteChecks.interval_append test 37184 37200 37216
  Check290.part37184
  Check290.part37200)
  (FiniteChecks.interval_append test 37216 37232 37248
  Check290.part37216
  Check290.part37232)))
#print axioms Check290.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check291.part37248 : Interval test 37248 37264 :=
  interval_of_check _ 37248 16 (by decide +kernel)
theorem Check291.part37264 : Interval test 37264 37280 :=
  interval_of_check _ 37264 16 (by decide +kernel)
theorem Check291.part37280 : Interval test 37280 37296 :=
  interval_of_check _ 37280 16 (by decide +kernel)
theorem Check291.part37296 : Interval test 37296 37312 :=
  interval_of_check _ 37296 16 (by decide +kernel)
theorem Check291.part37312 : Interval test 37312 37328 :=
  interval_of_check _ 37312 16 (by decide +kernel)
theorem Check291.part37328 : Interval test 37328 37344 :=
  interval_of_check _ 37328 16 (by decide +kernel)
theorem Check291.part37344 : Interval test 37344 37360 :=
  interval_of_check _ 37344 16 (by decide +kernel)
theorem Check291.part37360 : Interval test 37360 37376 :=
  interval_of_check _ 37360 16 (by decide +kernel)
theorem Check291.checked : Interval test 37248 37376 :=
  (FiniteChecks.interval_append test 37248 37312 37376
  (FiniteChecks.interval_append test 37248 37280 37312
  (FiniteChecks.interval_append test 37248 37264 37280
  Check291.part37248
  Check291.part37264)
  (FiniteChecks.interval_append test 37280 37296 37312
  Check291.part37280
  Check291.part37296))
  (FiniteChecks.interval_append test 37312 37344 37376
  (FiniteChecks.interval_append test 37312 37328 37344
  Check291.part37312
  Check291.part37328)
  (FiniteChecks.interval_append test 37344 37360 37376
  Check291.part37344
  Check291.part37360)))
#print axioms Check291.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check292.part37376 : Interval test 37376 37392 :=
  interval_of_check _ 37376 16 (by decide +kernel)
theorem Check292.part37392 : Interval test 37392 37408 :=
  interval_of_check _ 37392 16 (by decide +kernel)
theorem Check292.part37408 : Interval test 37408 37424 :=
  interval_of_check _ 37408 16 (by decide +kernel)
theorem Check292.part37424 : Interval test 37424 37440 :=
  interval_of_check _ 37424 16 (by decide +kernel)
theorem Check292.part37440 : Interval test 37440 37456 :=
  interval_of_check _ 37440 16 (by decide +kernel)
theorem Check292.part37456 : Interval test 37456 37472 :=
  interval_of_check _ 37456 16 (by decide +kernel)
theorem Check292.part37472 : Interval test 37472 37488 :=
  interval_of_check _ 37472 16 (by decide +kernel)
theorem Check292.part37488 : Interval test 37488 37504 :=
  interval_of_check _ 37488 16 (by decide +kernel)
theorem Check292.checked : Interval test 37376 37504 :=
  (FiniteChecks.interval_append test 37376 37440 37504
  (FiniteChecks.interval_append test 37376 37408 37440
  (FiniteChecks.interval_append test 37376 37392 37408
  Check292.part37376
  Check292.part37392)
  (FiniteChecks.interval_append test 37408 37424 37440
  Check292.part37408
  Check292.part37424))
  (FiniteChecks.interval_append test 37440 37472 37504
  (FiniteChecks.interval_append test 37440 37456 37472
  Check292.part37440
  Check292.part37456)
  (FiniteChecks.interval_append test 37472 37488 37504
  Check292.part37472
  Check292.part37488)))
#print axioms Check292.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check293.part37504 : Interval test 37504 37520 :=
  interval_of_check _ 37504 16 (by decide +kernel)
theorem Check293.part37520 : Interval test 37520 37536 :=
  interval_of_check _ 37520 16 (by decide +kernel)
theorem Check293.part37536 : Interval test 37536 37552 :=
  interval_of_check _ 37536 16 (by decide +kernel)
theorem Check293.part37552 : Interval test 37552 37568 :=
  interval_of_check _ 37552 16 (by decide +kernel)
theorem Check293.part37568 : Interval test 37568 37584 :=
  interval_of_check _ 37568 16 (by decide +kernel)
theorem Check293.part37584 : Interval test 37584 37600 :=
  interval_of_check _ 37584 16 (by decide +kernel)
theorem Check293.part37600 : Interval test 37600 37616 :=
  interval_of_check _ 37600 16 (by decide +kernel)
theorem Check293.part37616 : Interval test 37616 37632 :=
  interval_of_check _ 37616 16 (by decide +kernel)
theorem Check293.checked : Interval test 37504 37632 :=
  (FiniteChecks.interval_append test 37504 37568 37632
  (FiniteChecks.interval_append test 37504 37536 37568
  (FiniteChecks.interval_append test 37504 37520 37536
  Check293.part37504
  Check293.part37520)
  (FiniteChecks.interval_append test 37536 37552 37568
  Check293.part37536
  Check293.part37552))
  (FiniteChecks.interval_append test 37568 37600 37632
  (FiniteChecks.interval_append test 37568 37584 37600
  Check293.part37568
  Check293.part37584)
  (FiniteChecks.interval_append test 37600 37616 37632
  Check293.part37600
  Check293.part37616)))
#print axioms Check293.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check294.part37632 : Interval test 37632 37648 :=
  interval_of_check _ 37632 16 (by decide +kernel)
theorem Check294.part37648 : Interval test 37648 37664 :=
  interval_of_check _ 37648 16 (by decide +kernel)
theorem Check294.part37664 : Interval test 37664 37680 :=
  interval_of_check _ 37664 16 (by decide +kernel)
theorem Check294.part37680 : Interval test 37680 37696 :=
  interval_of_check _ 37680 16 (by decide +kernel)
theorem Check294.part37696 : Interval test 37696 37712 :=
  interval_of_check _ 37696 16 (by decide +kernel)
theorem Check294.part37712 : Interval test 37712 37728 :=
  interval_of_check _ 37712 16 (by decide +kernel)
theorem Check294.part37728 : Interval test 37728 37744 :=
  interval_of_check _ 37728 16 (by decide +kernel)
theorem Check294.part37744 : Interval test 37744 37760 :=
  interval_of_check _ 37744 16 (by decide +kernel)
theorem Check294.checked : Interval test 37632 37760 :=
  (FiniteChecks.interval_append test 37632 37696 37760
  (FiniteChecks.interval_append test 37632 37664 37696
  (FiniteChecks.interval_append test 37632 37648 37664
  Check294.part37632
  Check294.part37648)
  (FiniteChecks.interval_append test 37664 37680 37696
  Check294.part37664
  Check294.part37680))
  (FiniteChecks.interval_append test 37696 37728 37760
  (FiniteChecks.interval_append test 37696 37712 37728
  Check294.part37696
  Check294.part37712)
  (FiniteChecks.interval_append test 37728 37744 37760
  Check294.part37728
  Check294.part37744)))
#print axioms Check294.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check295.part37760 : Interval test 37760 37776 :=
  interval_of_check _ 37760 16 (by decide +kernel)
theorem Check295.part37776 : Interval test 37776 37792 :=
  interval_of_check _ 37776 16 (by decide +kernel)
theorem Check295.part37792 : Interval test 37792 37808 :=
  interval_of_check _ 37792 16 (by decide +kernel)
theorem Check295.part37808 : Interval test 37808 37824 :=
  interval_of_check _ 37808 16 (by decide +kernel)
theorem Check295.part37824 : Interval test 37824 37840 :=
  interval_of_check _ 37824 16 (by decide +kernel)
theorem Check295.part37840 : Interval test 37840 37856 :=
  interval_of_check _ 37840 16 (by decide +kernel)
theorem Check295.part37856 : Interval test 37856 37872 :=
  interval_of_check _ 37856 16 (by decide +kernel)
theorem Check295.part37872 : Interval test 37872 37888 :=
  interval_of_check _ 37872 16 (by decide +kernel)
theorem Check295.checked : Interval test 37760 37888 :=
  (FiniteChecks.interval_append test 37760 37824 37888
  (FiniteChecks.interval_append test 37760 37792 37824
  (FiniteChecks.interval_append test 37760 37776 37792
  Check295.part37760
  Check295.part37776)
  (FiniteChecks.interval_append test 37792 37808 37824
  Check295.part37792
  Check295.part37808))
  (FiniteChecks.interval_append test 37824 37856 37888
  (FiniteChecks.interval_append test 37824 37840 37856
  Check295.part37824
  Check295.part37840)
  (FiniteChecks.interval_append test 37856 37872 37888
  Check295.part37856
  Check295.part37872)))
#print axioms Check295.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check296.part37888 : Interval test 37888 37904 :=
  interval_of_check _ 37888 16 (by decide +kernel)
theorem Check296.part37904 : Interval test 37904 37920 :=
  interval_of_check _ 37904 16 (by decide +kernel)
theorem Check296.part37920 : Interval test 37920 37936 :=
  interval_of_check _ 37920 16 (by decide +kernel)
theorem Check296.part37936 : Interval test 37936 37952 :=
  interval_of_check _ 37936 16 (by decide +kernel)
theorem Check296.part37952 : Interval test 37952 37968 :=
  interval_of_check _ 37952 16 (by decide +kernel)
theorem Check296.part37968 : Interval test 37968 37984 :=
  interval_of_check _ 37968 16 (by decide +kernel)
theorem Check296.part37984 : Interval test 37984 38000 :=
  interval_of_check _ 37984 16 (by decide +kernel)
theorem Check296.part38000 : Interval test 38000 38016 :=
  interval_of_check _ 38000 16 (by decide +kernel)
theorem Check296.checked : Interval test 37888 38016 :=
  (FiniteChecks.interval_append test 37888 37952 38016
  (FiniteChecks.interval_append test 37888 37920 37952
  (FiniteChecks.interval_append test 37888 37904 37920
  Check296.part37888
  Check296.part37904)
  (FiniteChecks.interval_append test 37920 37936 37952
  Check296.part37920
  Check296.part37936))
  (FiniteChecks.interval_append test 37952 37984 38016
  (FiniteChecks.interval_append test 37952 37968 37984
  Check296.part37952
  Check296.part37968)
  (FiniteChecks.interval_append test 37984 38000 38016
  Check296.part37984
  Check296.part38000)))
#print axioms Check296.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check297.part38016 : Interval test 38016 38032 :=
  interval_of_check _ 38016 16 (by decide +kernel)
theorem Check297.part38032 : Interval test 38032 38048 :=
  interval_of_check _ 38032 16 (by decide +kernel)
theorem Check297.part38048 : Interval test 38048 38064 :=
  interval_of_check _ 38048 16 (by decide +kernel)
theorem Check297.part38064 : Interval test 38064 38080 :=
  interval_of_check _ 38064 16 (by decide +kernel)
theorem Check297.part38080 : Interval test 38080 38096 :=
  interval_of_check _ 38080 16 (by decide +kernel)
theorem Check297.part38096 : Interval test 38096 38112 :=
  interval_of_check _ 38096 16 (by decide +kernel)
theorem Check297.part38112 : Interval test 38112 38128 :=
  interval_of_check _ 38112 16 (by decide +kernel)
theorem Check297.part38128 : Interval test 38128 38144 :=
  interval_of_check _ 38128 16 (by decide +kernel)
theorem Check297.checked : Interval test 38016 38144 :=
  (FiniteChecks.interval_append test 38016 38080 38144
  (FiniteChecks.interval_append test 38016 38048 38080
  (FiniteChecks.interval_append test 38016 38032 38048
  Check297.part38016
  Check297.part38032)
  (FiniteChecks.interval_append test 38048 38064 38080
  Check297.part38048
  Check297.part38064))
  (FiniteChecks.interval_append test 38080 38112 38144
  (FiniteChecks.interval_append test 38080 38096 38112
  Check297.part38080
  Check297.part38096)
  (FiniteChecks.interval_append test 38112 38128 38144
  Check297.part38112
  Check297.part38128)))
#print axioms Check297.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check298.part38144 : Interval test 38144 38160 :=
  interval_of_check _ 38144 16 (by decide +kernel)
theorem Check298.part38160 : Interval test 38160 38176 :=
  interval_of_check _ 38160 16 (by decide +kernel)
theorem Check298.part38176 : Interval test 38176 38192 :=
  interval_of_check _ 38176 16 (by decide +kernel)
theorem Check298.part38192 : Interval test 38192 38208 :=
  interval_of_check _ 38192 16 (by decide +kernel)
theorem Check298.part38208 : Interval test 38208 38224 :=
  interval_of_check _ 38208 16 (by decide +kernel)
theorem Check298.part38224 : Interval test 38224 38240 :=
  interval_of_check _ 38224 16 (by decide +kernel)
theorem Check298.part38240 : Interval test 38240 38256 :=
  interval_of_check _ 38240 16 (by decide +kernel)
theorem Check298.part38256 : Interval test 38256 38272 :=
  interval_of_check _ 38256 16 (by decide +kernel)
theorem Check298.checked : Interval test 38144 38272 :=
  (FiniteChecks.interval_append test 38144 38208 38272
  (FiniteChecks.interval_append test 38144 38176 38208
  (FiniteChecks.interval_append test 38144 38160 38176
  Check298.part38144
  Check298.part38160)
  (FiniteChecks.interval_append test 38176 38192 38208
  Check298.part38176
  Check298.part38192))
  (FiniteChecks.interval_append test 38208 38240 38272
  (FiniteChecks.interval_append test 38208 38224 38240
  Check298.part38208
  Check298.part38224)
  (FiniteChecks.interval_append test 38240 38256 38272
  Check298.part38240
  Check298.part38256)))
#print axioms Check298.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check299.part38272 : Interval test 38272 38288 :=
  interval_of_check _ 38272 16 (by decide +kernel)
theorem Check299.part38288 : Interval test 38288 38304 :=
  interval_of_check _ 38288 16 (by decide +kernel)
theorem Check299.part38304 : Interval test 38304 38320 :=
  interval_of_check _ 38304 16 (by decide +kernel)
theorem Check299.part38320 : Interval test 38320 38336 :=
  interval_of_check _ 38320 16 (by decide +kernel)
theorem Check299.part38336 : Interval test 38336 38352 :=
  interval_of_check _ 38336 16 (by decide +kernel)
theorem Check299.part38352 : Interval test 38352 38368 :=
  interval_of_check _ 38352 16 (by decide +kernel)
theorem Check299.part38368 : Interval test 38368 38384 :=
  interval_of_check _ 38368 16 (by decide +kernel)
theorem Check299.part38384 : Interval test 38384 38400 :=
  interval_of_check _ 38384 16 (by decide +kernel)
theorem Check299.checked : Interval test 38272 38400 :=
  (FiniteChecks.interval_append test 38272 38336 38400
  (FiniteChecks.interval_append test 38272 38304 38336
  (FiniteChecks.interval_append test 38272 38288 38304
  Check299.part38272
  Check299.part38288)
  (FiniteChecks.interval_append test 38304 38320 38336
  Check299.part38304
  Check299.part38320))
  (FiniteChecks.interval_append test 38336 38368 38400
  (FiniteChecks.interval_append test 38336 38352 38368
  Check299.part38336
  Check299.part38352)
  (FiniteChecks.interval_append test 38368 38384 38400
  Check299.part38368
  Check299.part38384)))
#print axioms Check299.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
