module
prelude
public import SharedSix0IncidenceData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check140.part35840 : Interval test 35840 35856 :=
  interval_of_check _ 35840 16 (by decide +kernel)
theorem Check140.part35856 : Interval test 35856 35872 :=
  interval_of_check _ 35856 16 (by decide +kernel)
theorem Check140.part35872 : Interval test 35872 35888 :=
  interval_of_check _ 35872 16 (by decide +kernel)
theorem Check140.part35888 : Interval test 35888 35904 :=
  interval_of_check _ 35888 16 (by decide +kernel)
theorem Check140.part35904 : Interval test 35904 35920 :=
  interval_of_check _ 35904 16 (by decide +kernel)
theorem Check140.part35920 : Interval test 35920 35936 :=
  interval_of_check _ 35920 16 (by decide +kernel)
theorem Check140.part35936 : Interval test 35936 35952 :=
  interval_of_check _ 35936 16 (by decide +kernel)
theorem Check140.part35952 : Interval test 35952 35968 :=
  interval_of_check _ 35952 16 (by decide +kernel)
theorem Check140.part35968 : Interval test 35968 35984 :=
  interval_of_check _ 35968 16 (by decide +kernel)
theorem Check140.part35984 : Interval test 35984 36000 :=
  interval_of_check _ 35984 16 (by decide +kernel)
theorem Check140.part36000 : Interval test 36000 36016 :=
  interval_of_check _ 36000 16 (by decide +kernel)
theorem Check140.part36016 : Interval test 36016 36032 :=
  interval_of_check _ 36016 16 (by decide +kernel)
theorem Check140.part36032 : Interval test 36032 36048 :=
  interval_of_check _ 36032 16 (by decide +kernel)
theorem Check140.part36048 : Interval test 36048 36064 :=
  interval_of_check _ 36048 16 (by decide +kernel)
theorem Check140.part36064 : Interval test 36064 36080 :=
  interval_of_check _ 36064 16 (by decide +kernel)
theorem Check140.part36080 : Interval test 36080 36096 :=
  interval_of_check _ 36080 16 (by decide +kernel)
theorem Check140.checked : Interval test 35840 36096 :=
  (FiniteChecks.interval_append test 35840 35968 36096
  (FiniteChecks.interval_append test 35840 35904 35968
  (FiniteChecks.interval_append test 35840 35872 35904
  (FiniteChecks.interval_append test 35840 35856 35872
  Check140.part35840
  Check140.part35856)
  (FiniteChecks.interval_append test 35872 35888 35904
  Check140.part35872
  Check140.part35888))
  (FiniteChecks.interval_append test 35904 35936 35968
  (FiniteChecks.interval_append test 35904 35920 35936
  Check140.part35904
  Check140.part35920)
  (FiniteChecks.interval_append test 35936 35952 35968
  Check140.part35936
  Check140.part35952)))
  (FiniteChecks.interval_append test 35968 36032 36096
  (FiniteChecks.interval_append test 35968 36000 36032
  (FiniteChecks.interval_append test 35968 35984 36000
  Check140.part35968
  Check140.part35984)
  (FiniteChecks.interval_append test 36000 36016 36032
  Check140.part36000
  Check140.part36016))
  (FiniteChecks.interval_append test 36032 36064 36096
  (FiniteChecks.interval_append test 36032 36048 36064
  Check140.part36032
  Check140.part36048)
  (FiniteChecks.interval_append test 36064 36080 36096
  Check140.part36064
  Check140.part36080))))
#print axioms Check140.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check141.part36096 : Interval test 36096 36112 :=
  interval_of_check _ 36096 16 (by decide +kernel)
theorem Check141.part36112 : Interval test 36112 36128 :=
  interval_of_check _ 36112 16 (by decide +kernel)
theorem Check141.part36128 : Interval test 36128 36144 :=
  interval_of_check _ 36128 16 (by decide +kernel)
theorem Check141.part36144 : Interval test 36144 36160 :=
  interval_of_check _ 36144 16 (by decide +kernel)
theorem Check141.part36160 : Interval test 36160 36176 :=
  interval_of_check _ 36160 16 (by decide +kernel)
theorem Check141.part36176 : Interval test 36176 36192 :=
  interval_of_check _ 36176 16 (by decide +kernel)
theorem Check141.part36192 : Interval test 36192 36208 :=
  interval_of_check _ 36192 16 (by decide +kernel)
theorem Check141.part36208 : Interval test 36208 36224 :=
  interval_of_check _ 36208 16 (by decide +kernel)
theorem Check141.part36224 : Interval test 36224 36240 :=
  interval_of_check _ 36224 16 (by decide +kernel)
theorem Check141.part36240 : Interval test 36240 36256 :=
  interval_of_check _ 36240 16 (by decide +kernel)
theorem Check141.part36256 : Interval test 36256 36272 :=
  interval_of_check _ 36256 16 (by decide +kernel)
theorem Check141.part36272 : Interval test 36272 36288 :=
  interval_of_check _ 36272 16 (by decide +kernel)
theorem Check141.part36288 : Interval test 36288 36304 :=
  interval_of_check _ 36288 16 (by decide +kernel)
theorem Check141.part36304 : Interval test 36304 36320 :=
  interval_of_check _ 36304 16 (by decide +kernel)
theorem Check141.part36320 : Interval test 36320 36336 :=
  interval_of_check _ 36320 16 (by decide +kernel)
theorem Check141.part36336 : Interval test 36336 36352 :=
  interval_of_check _ 36336 16 (by decide +kernel)
theorem Check141.checked : Interval test 36096 36352 :=
  (FiniteChecks.interval_append test 36096 36224 36352
  (FiniteChecks.interval_append test 36096 36160 36224
  (FiniteChecks.interval_append test 36096 36128 36160
  (FiniteChecks.interval_append test 36096 36112 36128
  Check141.part36096
  Check141.part36112)
  (FiniteChecks.interval_append test 36128 36144 36160
  Check141.part36128
  Check141.part36144))
  (FiniteChecks.interval_append test 36160 36192 36224
  (FiniteChecks.interval_append test 36160 36176 36192
  Check141.part36160
  Check141.part36176)
  (FiniteChecks.interval_append test 36192 36208 36224
  Check141.part36192
  Check141.part36208)))
  (FiniteChecks.interval_append test 36224 36288 36352
  (FiniteChecks.interval_append test 36224 36256 36288
  (FiniteChecks.interval_append test 36224 36240 36256
  Check141.part36224
  Check141.part36240)
  (FiniteChecks.interval_append test 36256 36272 36288
  Check141.part36256
  Check141.part36272))
  (FiniteChecks.interval_append test 36288 36320 36352
  (FiniteChecks.interval_append test 36288 36304 36320
  Check141.part36288
  Check141.part36304)
  (FiniteChecks.interval_append test 36320 36336 36352
  Check141.part36320
  Check141.part36336))))
#print axioms Check141.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check142.part36352 : Interval test 36352 36368 :=
  interval_of_check _ 36352 16 (by decide +kernel)
theorem Check142.part36368 : Interval test 36368 36384 :=
  interval_of_check _ 36368 16 (by decide +kernel)
theorem Check142.part36384 : Interval test 36384 36400 :=
  interval_of_check _ 36384 16 (by decide +kernel)
theorem Check142.part36400 : Interval test 36400 36416 :=
  interval_of_check _ 36400 16 (by decide +kernel)
theorem Check142.part36416 : Interval test 36416 36432 :=
  interval_of_check _ 36416 16 (by decide +kernel)
theorem Check142.part36432 : Interval test 36432 36448 :=
  interval_of_check _ 36432 16 (by decide +kernel)
theorem Check142.part36448 : Interval test 36448 36464 :=
  interval_of_check _ 36448 16 (by decide +kernel)
theorem Check142.part36464 : Interval test 36464 36480 :=
  interval_of_check _ 36464 16 (by decide +kernel)
theorem Check142.part36480 : Interval test 36480 36496 :=
  interval_of_check _ 36480 16 (by decide +kernel)
theorem Check142.part36496 : Interval test 36496 36512 :=
  interval_of_check _ 36496 16 (by decide +kernel)
theorem Check142.part36512 : Interval test 36512 36528 :=
  interval_of_check _ 36512 16 (by decide +kernel)
theorem Check142.part36528 : Interval test 36528 36544 :=
  interval_of_check _ 36528 16 (by decide +kernel)
theorem Check142.part36544 : Interval test 36544 36560 :=
  interval_of_check _ 36544 16 (by decide +kernel)
theorem Check142.part36560 : Interval test 36560 36576 :=
  interval_of_check _ 36560 16 (by decide +kernel)
theorem Check142.part36576 : Interval test 36576 36592 :=
  interval_of_check _ 36576 16 (by decide +kernel)
theorem Check142.part36592 : Interval test 36592 36608 :=
  interval_of_check _ 36592 16 (by decide +kernel)
theorem Check142.checked : Interval test 36352 36608 :=
  (FiniteChecks.interval_append test 36352 36480 36608
  (FiniteChecks.interval_append test 36352 36416 36480
  (FiniteChecks.interval_append test 36352 36384 36416
  (FiniteChecks.interval_append test 36352 36368 36384
  Check142.part36352
  Check142.part36368)
  (FiniteChecks.interval_append test 36384 36400 36416
  Check142.part36384
  Check142.part36400))
  (FiniteChecks.interval_append test 36416 36448 36480
  (FiniteChecks.interval_append test 36416 36432 36448
  Check142.part36416
  Check142.part36432)
  (FiniteChecks.interval_append test 36448 36464 36480
  Check142.part36448
  Check142.part36464)))
  (FiniteChecks.interval_append test 36480 36544 36608
  (FiniteChecks.interval_append test 36480 36512 36544
  (FiniteChecks.interval_append test 36480 36496 36512
  Check142.part36480
  Check142.part36496)
  (FiniteChecks.interval_append test 36512 36528 36544
  Check142.part36512
  Check142.part36528))
  (FiniteChecks.interval_append test 36544 36576 36608
  (FiniteChecks.interval_append test 36544 36560 36576
  Check142.part36544
  Check142.part36560)
  (FiniteChecks.interval_append test 36576 36592 36608
  Check142.part36576
  Check142.part36592))))
#print axioms Check142.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check143.part36608 : Interval test 36608 36624 :=
  interval_of_check _ 36608 16 (by decide +kernel)
theorem Check143.part36624 : Interval test 36624 36640 :=
  interval_of_check _ 36624 16 (by decide +kernel)
theorem Check143.part36640 : Interval test 36640 36656 :=
  interval_of_check _ 36640 16 (by decide +kernel)
theorem Check143.part36656 : Interval test 36656 36672 :=
  interval_of_check _ 36656 16 (by decide +kernel)
theorem Check143.part36672 : Interval test 36672 36688 :=
  interval_of_check _ 36672 16 (by decide +kernel)
theorem Check143.part36688 : Interval test 36688 36704 :=
  interval_of_check _ 36688 16 (by decide +kernel)
theorem Check143.part36704 : Interval test 36704 36720 :=
  interval_of_check _ 36704 16 (by decide +kernel)
theorem Check143.part36720 : Interval test 36720 36736 :=
  interval_of_check _ 36720 16 (by decide +kernel)
theorem Check143.part36736 : Interval test 36736 36752 :=
  interval_of_check _ 36736 16 (by decide +kernel)
theorem Check143.part36752 : Interval test 36752 36768 :=
  interval_of_check _ 36752 16 (by decide +kernel)
theorem Check143.part36768 : Interval test 36768 36784 :=
  interval_of_check _ 36768 16 (by decide +kernel)
theorem Check143.part36784 : Interval test 36784 36800 :=
  interval_of_check _ 36784 16 (by decide +kernel)
theorem Check143.part36800 : Interval test 36800 36816 :=
  interval_of_check _ 36800 16 (by decide +kernel)
theorem Check143.part36816 : Interval test 36816 36832 :=
  interval_of_check _ 36816 16 (by decide +kernel)
theorem Check143.part36832 : Interval test 36832 36848 :=
  interval_of_check _ 36832 16 (by decide +kernel)
theorem Check143.part36848 : Interval test 36848 36864 :=
  interval_of_check _ 36848 16 (by decide +kernel)
theorem Check143.checked : Interval test 36608 36864 :=
  (FiniteChecks.interval_append test 36608 36736 36864
  (FiniteChecks.interval_append test 36608 36672 36736
  (FiniteChecks.interval_append test 36608 36640 36672
  (FiniteChecks.interval_append test 36608 36624 36640
  Check143.part36608
  Check143.part36624)
  (FiniteChecks.interval_append test 36640 36656 36672
  Check143.part36640
  Check143.part36656))
  (FiniteChecks.interval_append test 36672 36704 36736
  (FiniteChecks.interval_append test 36672 36688 36704
  Check143.part36672
  Check143.part36688)
  (FiniteChecks.interval_append test 36704 36720 36736
  Check143.part36704
  Check143.part36720)))
  (FiniteChecks.interval_append test 36736 36800 36864
  (FiniteChecks.interval_append test 36736 36768 36800
  (FiniteChecks.interval_append test 36736 36752 36768
  Check143.part36736
  Check143.part36752)
  (FiniteChecks.interval_append test 36768 36784 36800
  Check143.part36768
  Check143.part36784))
  (FiniteChecks.interval_append test 36800 36832 36864
  (FiniteChecks.interval_append test 36800 36816 36832
  Check143.part36800
  Check143.part36816)
  (FiniteChecks.interval_append test 36832 36848 36864
  Check143.part36832
  Check143.part36848))))
#print axioms Check143.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check144.part36864 : Interval test 36864 36880 :=
  interval_of_check _ 36864 16 (by decide +kernel)
theorem Check144.part36880 : Interval test 36880 36896 :=
  interval_of_check _ 36880 16 (by decide +kernel)
theorem Check144.part36896 : Interval test 36896 36912 :=
  interval_of_check _ 36896 16 (by decide +kernel)
theorem Check144.part36912 : Interval test 36912 36928 :=
  interval_of_check _ 36912 16 (by decide +kernel)
theorem Check144.part36928 : Interval test 36928 36944 :=
  interval_of_check _ 36928 16 (by decide +kernel)
theorem Check144.part36944 : Interval test 36944 36960 :=
  interval_of_check _ 36944 16 (by decide +kernel)
theorem Check144.part36960 : Interval test 36960 36976 :=
  interval_of_check _ 36960 16 (by decide +kernel)
theorem Check144.part36976 : Interval test 36976 36992 :=
  interval_of_check _ 36976 16 (by decide +kernel)
theorem Check144.part36992 : Interval test 36992 37008 :=
  interval_of_check _ 36992 16 (by decide +kernel)
theorem Check144.part37008 : Interval test 37008 37024 :=
  interval_of_check _ 37008 16 (by decide +kernel)
theorem Check144.part37024 : Interval test 37024 37040 :=
  interval_of_check _ 37024 16 (by decide +kernel)
theorem Check144.part37040 : Interval test 37040 37056 :=
  interval_of_check _ 37040 16 (by decide +kernel)
theorem Check144.part37056 : Interval test 37056 37072 :=
  interval_of_check _ 37056 16 (by decide +kernel)
theorem Check144.part37072 : Interval test 37072 37088 :=
  interval_of_check _ 37072 16 (by decide +kernel)
theorem Check144.part37088 : Interval test 37088 37104 :=
  interval_of_check _ 37088 16 (by decide +kernel)
theorem Check144.part37104 : Interval test 37104 37120 :=
  interval_of_check _ 37104 16 (by decide +kernel)
theorem Check144.checked : Interval test 36864 37120 :=
  (FiniteChecks.interval_append test 36864 36992 37120
  (FiniteChecks.interval_append test 36864 36928 36992
  (FiniteChecks.interval_append test 36864 36896 36928
  (FiniteChecks.interval_append test 36864 36880 36896
  Check144.part36864
  Check144.part36880)
  (FiniteChecks.interval_append test 36896 36912 36928
  Check144.part36896
  Check144.part36912))
  (FiniteChecks.interval_append test 36928 36960 36992
  (FiniteChecks.interval_append test 36928 36944 36960
  Check144.part36928
  Check144.part36944)
  (FiniteChecks.interval_append test 36960 36976 36992
  Check144.part36960
  Check144.part36976)))
  (FiniteChecks.interval_append test 36992 37056 37120
  (FiniteChecks.interval_append test 36992 37024 37056
  (FiniteChecks.interval_append test 36992 37008 37024
  Check144.part36992
  Check144.part37008)
  (FiniteChecks.interval_append test 37024 37040 37056
  Check144.part37024
  Check144.part37040))
  (FiniteChecks.interval_append test 37056 37088 37120
  (FiniteChecks.interval_append test 37056 37072 37088
  Check144.part37056
  Check144.part37072)
  (FiniteChecks.interval_append test 37088 37104 37120
  Check144.part37088
  Check144.part37104))))
#print axioms Check144.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check145.part37120 : Interval test 37120 37136 :=
  interval_of_check _ 37120 16 (by decide +kernel)
theorem Check145.part37136 : Interval test 37136 37152 :=
  interval_of_check _ 37136 16 (by decide +kernel)
theorem Check145.part37152 : Interval test 37152 37168 :=
  interval_of_check _ 37152 16 (by decide +kernel)
theorem Check145.part37168 : Interval test 37168 37184 :=
  interval_of_check _ 37168 16 (by decide +kernel)
theorem Check145.part37184 : Interval test 37184 37200 :=
  interval_of_check _ 37184 16 (by decide +kernel)
theorem Check145.part37200 : Interval test 37200 37216 :=
  interval_of_check _ 37200 16 (by decide +kernel)
theorem Check145.part37216 : Interval test 37216 37232 :=
  interval_of_check _ 37216 16 (by decide +kernel)
theorem Check145.part37232 : Interval test 37232 37248 :=
  interval_of_check _ 37232 16 (by decide +kernel)
theorem Check145.part37248 : Interval test 37248 37264 :=
  interval_of_check _ 37248 16 (by decide +kernel)
theorem Check145.part37264 : Interval test 37264 37280 :=
  interval_of_check _ 37264 16 (by decide +kernel)
theorem Check145.part37280 : Interval test 37280 37296 :=
  interval_of_check _ 37280 16 (by decide +kernel)
theorem Check145.part37296 : Interval test 37296 37312 :=
  interval_of_check _ 37296 16 (by decide +kernel)
theorem Check145.part37312 : Interval test 37312 37328 :=
  interval_of_check _ 37312 16 (by decide +kernel)
theorem Check145.part37328 : Interval test 37328 37344 :=
  interval_of_check _ 37328 16 (by decide +kernel)
theorem Check145.part37344 : Interval test 37344 37360 :=
  interval_of_check _ 37344 16 (by decide +kernel)
theorem Check145.part37360 : Interval test 37360 37376 :=
  interval_of_check _ 37360 16 (by decide +kernel)
theorem Check145.checked : Interval test 37120 37376 :=
  (FiniteChecks.interval_append test 37120 37248 37376
  (FiniteChecks.interval_append test 37120 37184 37248
  (FiniteChecks.interval_append test 37120 37152 37184
  (FiniteChecks.interval_append test 37120 37136 37152
  Check145.part37120
  Check145.part37136)
  (FiniteChecks.interval_append test 37152 37168 37184
  Check145.part37152
  Check145.part37168))
  (FiniteChecks.interval_append test 37184 37216 37248
  (FiniteChecks.interval_append test 37184 37200 37216
  Check145.part37184
  Check145.part37200)
  (FiniteChecks.interval_append test 37216 37232 37248
  Check145.part37216
  Check145.part37232)))
  (FiniteChecks.interval_append test 37248 37312 37376
  (FiniteChecks.interval_append test 37248 37280 37312
  (FiniteChecks.interval_append test 37248 37264 37280
  Check145.part37248
  Check145.part37264)
  (FiniteChecks.interval_append test 37280 37296 37312
  Check145.part37280
  Check145.part37296))
  (FiniteChecks.interval_append test 37312 37344 37376
  (FiniteChecks.interval_append test 37312 37328 37344
  Check145.part37312
  Check145.part37328)
  (FiniteChecks.interval_append test 37344 37360 37376
  Check145.part37344
  Check145.part37360))))
#print axioms Check145.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check146.part37376 : Interval test 37376 37392 :=
  interval_of_check _ 37376 16 (by decide +kernel)
theorem Check146.part37392 : Interval test 37392 37408 :=
  interval_of_check _ 37392 16 (by decide +kernel)
theorem Check146.part37408 : Interval test 37408 37424 :=
  interval_of_check _ 37408 16 (by decide +kernel)
theorem Check146.part37424 : Interval test 37424 37440 :=
  interval_of_check _ 37424 16 (by decide +kernel)
theorem Check146.part37440 : Interval test 37440 37456 :=
  interval_of_check _ 37440 16 (by decide +kernel)
theorem Check146.part37456 : Interval test 37456 37472 :=
  interval_of_check _ 37456 16 (by decide +kernel)
theorem Check146.part37472 : Interval test 37472 37488 :=
  interval_of_check _ 37472 16 (by decide +kernel)
theorem Check146.part37488 : Interval test 37488 37504 :=
  interval_of_check _ 37488 16 (by decide +kernel)
theorem Check146.part37504 : Interval test 37504 37520 :=
  interval_of_check _ 37504 16 (by decide +kernel)
theorem Check146.part37520 : Interval test 37520 37536 :=
  interval_of_check _ 37520 16 (by decide +kernel)
theorem Check146.part37536 : Interval test 37536 37552 :=
  interval_of_check _ 37536 16 (by decide +kernel)
theorem Check146.part37552 : Interval test 37552 37568 :=
  interval_of_check _ 37552 16 (by decide +kernel)
theorem Check146.part37568 : Interval test 37568 37584 :=
  interval_of_check _ 37568 16 (by decide +kernel)
theorem Check146.part37584 : Interval test 37584 37600 :=
  interval_of_check _ 37584 16 (by decide +kernel)
theorem Check146.part37600 : Interval test 37600 37616 :=
  interval_of_check _ 37600 16 (by decide +kernel)
theorem Check146.part37616 : Interval test 37616 37632 :=
  interval_of_check _ 37616 16 (by decide +kernel)
theorem Check146.checked : Interval test 37376 37632 :=
  (FiniteChecks.interval_append test 37376 37504 37632
  (FiniteChecks.interval_append test 37376 37440 37504
  (FiniteChecks.interval_append test 37376 37408 37440
  (FiniteChecks.interval_append test 37376 37392 37408
  Check146.part37376
  Check146.part37392)
  (FiniteChecks.interval_append test 37408 37424 37440
  Check146.part37408
  Check146.part37424))
  (FiniteChecks.interval_append test 37440 37472 37504
  (FiniteChecks.interval_append test 37440 37456 37472
  Check146.part37440
  Check146.part37456)
  (FiniteChecks.interval_append test 37472 37488 37504
  Check146.part37472
  Check146.part37488)))
  (FiniteChecks.interval_append test 37504 37568 37632
  (FiniteChecks.interval_append test 37504 37536 37568
  (FiniteChecks.interval_append test 37504 37520 37536
  Check146.part37504
  Check146.part37520)
  (FiniteChecks.interval_append test 37536 37552 37568
  Check146.part37536
  Check146.part37552))
  (FiniteChecks.interval_append test 37568 37600 37632
  (FiniteChecks.interval_append test 37568 37584 37600
  Check146.part37568
  Check146.part37584)
  (FiniteChecks.interval_append test 37600 37616 37632
  Check146.part37600
  Check146.part37616))))
#print axioms Check146.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check147.part37632 : Interval test 37632 37648 :=
  interval_of_check _ 37632 16 (by decide +kernel)
theorem Check147.part37648 : Interval test 37648 37664 :=
  interval_of_check _ 37648 16 (by decide +kernel)
theorem Check147.part37664 : Interval test 37664 37680 :=
  interval_of_check _ 37664 16 (by decide +kernel)
theorem Check147.part37680 : Interval test 37680 37696 :=
  interval_of_check _ 37680 16 (by decide +kernel)
theorem Check147.part37696 : Interval test 37696 37712 :=
  interval_of_check _ 37696 16 (by decide +kernel)
theorem Check147.part37712 : Interval test 37712 37728 :=
  interval_of_check _ 37712 16 (by decide +kernel)
theorem Check147.part37728 : Interval test 37728 37744 :=
  interval_of_check _ 37728 16 (by decide +kernel)
theorem Check147.part37744 : Interval test 37744 37760 :=
  interval_of_check _ 37744 16 (by decide +kernel)
theorem Check147.part37760 : Interval test 37760 37776 :=
  interval_of_check _ 37760 16 (by decide +kernel)
theorem Check147.part37776 : Interval test 37776 37792 :=
  interval_of_check _ 37776 16 (by decide +kernel)
theorem Check147.part37792 : Interval test 37792 37808 :=
  interval_of_check _ 37792 16 (by decide +kernel)
theorem Check147.part37808 : Interval test 37808 37824 :=
  interval_of_check _ 37808 16 (by decide +kernel)
theorem Check147.part37824 : Interval test 37824 37840 :=
  interval_of_check _ 37824 16 (by decide +kernel)
theorem Check147.part37840 : Interval test 37840 37856 :=
  interval_of_check _ 37840 16 (by decide +kernel)
theorem Check147.part37856 : Interval test 37856 37872 :=
  interval_of_check _ 37856 16 (by decide +kernel)
theorem Check147.part37872 : Interval test 37872 37888 :=
  interval_of_check _ 37872 16 (by decide +kernel)
theorem Check147.checked : Interval test 37632 37888 :=
  (FiniteChecks.interval_append test 37632 37760 37888
  (FiniteChecks.interval_append test 37632 37696 37760
  (FiniteChecks.interval_append test 37632 37664 37696
  (FiniteChecks.interval_append test 37632 37648 37664
  Check147.part37632
  Check147.part37648)
  (FiniteChecks.interval_append test 37664 37680 37696
  Check147.part37664
  Check147.part37680))
  (FiniteChecks.interval_append test 37696 37728 37760
  (FiniteChecks.interval_append test 37696 37712 37728
  Check147.part37696
  Check147.part37712)
  (FiniteChecks.interval_append test 37728 37744 37760
  Check147.part37728
  Check147.part37744)))
  (FiniteChecks.interval_append test 37760 37824 37888
  (FiniteChecks.interval_append test 37760 37792 37824
  (FiniteChecks.interval_append test 37760 37776 37792
  Check147.part37760
  Check147.part37776)
  (FiniteChecks.interval_append test 37792 37808 37824
  Check147.part37792
  Check147.part37808))
  (FiniteChecks.interval_append test 37824 37856 37888
  (FiniteChecks.interval_append test 37824 37840 37856
  Check147.part37824
  Check147.part37840)
  (FiniteChecks.interval_append test 37856 37872 37888
  Check147.part37856
  Check147.part37872))))
#print axioms Check147.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check148.part37888 : Interval test 37888 37904 :=
  interval_of_check _ 37888 16 (by decide +kernel)
theorem Check148.part37904 : Interval test 37904 37920 :=
  interval_of_check _ 37904 16 (by decide +kernel)
theorem Check148.part37920 : Interval test 37920 37936 :=
  interval_of_check _ 37920 16 (by decide +kernel)
theorem Check148.part37936 : Interval test 37936 37952 :=
  interval_of_check _ 37936 16 (by decide +kernel)
theorem Check148.part37952 : Interval test 37952 37968 :=
  interval_of_check _ 37952 16 (by decide +kernel)
theorem Check148.part37968 : Interval test 37968 37984 :=
  interval_of_check _ 37968 16 (by decide +kernel)
theorem Check148.part37984 : Interval test 37984 38000 :=
  interval_of_check _ 37984 16 (by decide +kernel)
theorem Check148.part38000 : Interval test 38000 38016 :=
  interval_of_check _ 38000 16 (by decide +kernel)
theorem Check148.part38016 : Interval test 38016 38032 :=
  interval_of_check _ 38016 16 (by decide +kernel)
theorem Check148.part38032 : Interval test 38032 38048 :=
  interval_of_check _ 38032 16 (by decide +kernel)
theorem Check148.part38048 : Interval test 38048 38064 :=
  interval_of_check _ 38048 16 (by decide +kernel)
theorem Check148.part38064 : Interval test 38064 38080 :=
  interval_of_check _ 38064 16 (by decide +kernel)
theorem Check148.part38080 : Interval test 38080 38096 :=
  interval_of_check _ 38080 16 (by decide +kernel)
theorem Check148.part38096 : Interval test 38096 38112 :=
  interval_of_check _ 38096 16 (by decide +kernel)
theorem Check148.part38112 : Interval test 38112 38128 :=
  interval_of_check _ 38112 16 (by decide +kernel)
theorem Check148.part38128 : Interval test 38128 38144 :=
  interval_of_check _ 38128 16 (by decide +kernel)
theorem Check148.checked : Interval test 37888 38144 :=
  (FiniteChecks.interval_append test 37888 38016 38144
  (FiniteChecks.interval_append test 37888 37952 38016
  (FiniteChecks.interval_append test 37888 37920 37952
  (FiniteChecks.interval_append test 37888 37904 37920
  Check148.part37888
  Check148.part37904)
  (FiniteChecks.interval_append test 37920 37936 37952
  Check148.part37920
  Check148.part37936))
  (FiniteChecks.interval_append test 37952 37984 38016
  (FiniteChecks.interval_append test 37952 37968 37984
  Check148.part37952
  Check148.part37968)
  (FiniteChecks.interval_append test 37984 38000 38016
  Check148.part37984
  Check148.part38000)))
  (FiniteChecks.interval_append test 38016 38080 38144
  (FiniteChecks.interval_append test 38016 38048 38080
  (FiniteChecks.interval_append test 38016 38032 38048
  Check148.part38016
  Check148.part38032)
  (FiniteChecks.interval_append test 38048 38064 38080
  Check148.part38048
  Check148.part38064))
  (FiniteChecks.interval_append test 38080 38112 38144
  (FiniteChecks.interval_append test 38080 38096 38112
  Check148.part38080
  Check148.part38096)
  (FiniteChecks.interval_append test 38112 38128 38144
  Check148.part38112
  Check148.part38128))))
#print axioms Check148.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check149.part38144 : Interval test 38144 38160 :=
  interval_of_check _ 38144 16 (by decide +kernel)
theorem Check149.part38160 : Interval test 38160 38176 :=
  interval_of_check _ 38160 16 (by decide +kernel)
theorem Check149.part38176 : Interval test 38176 38192 :=
  interval_of_check _ 38176 16 (by decide +kernel)
theorem Check149.part38192 : Interval test 38192 38208 :=
  interval_of_check _ 38192 16 (by decide +kernel)
theorem Check149.part38208 : Interval test 38208 38224 :=
  interval_of_check _ 38208 16 (by decide +kernel)
theorem Check149.part38224 : Interval test 38224 38240 :=
  interval_of_check _ 38224 16 (by decide +kernel)
theorem Check149.part38240 : Interval test 38240 38256 :=
  interval_of_check _ 38240 16 (by decide +kernel)
theorem Check149.part38256 : Interval test 38256 38272 :=
  interval_of_check _ 38256 16 (by decide +kernel)
theorem Check149.part38272 : Interval test 38272 38288 :=
  interval_of_check _ 38272 16 (by decide +kernel)
theorem Check149.part38288 : Interval test 38288 38304 :=
  interval_of_check _ 38288 16 (by decide +kernel)
theorem Check149.part38304 : Interval test 38304 38320 :=
  interval_of_check _ 38304 16 (by decide +kernel)
theorem Check149.part38320 : Interval test 38320 38336 :=
  interval_of_check _ 38320 16 (by decide +kernel)
theorem Check149.part38336 : Interval test 38336 38352 :=
  interval_of_check _ 38336 16 (by decide +kernel)
theorem Check149.part38352 : Interval test 38352 38368 :=
  interval_of_check _ 38352 16 (by decide +kernel)
theorem Check149.part38368 : Interval test 38368 38384 :=
  interval_of_check _ 38368 16 (by decide +kernel)
theorem Check149.part38384 : Interval test 38384 38400 :=
  interval_of_check _ 38384 16 (by decide +kernel)
theorem Check149.checked : Interval test 38144 38400 :=
  (FiniteChecks.interval_append test 38144 38272 38400
  (FiniteChecks.interval_append test 38144 38208 38272
  (FiniteChecks.interval_append test 38144 38176 38208
  (FiniteChecks.interval_append test 38144 38160 38176
  Check149.part38144
  Check149.part38160)
  (FiniteChecks.interval_append test 38176 38192 38208
  Check149.part38176
  Check149.part38192))
  (FiniteChecks.interval_append test 38208 38240 38272
  (FiniteChecks.interval_append test 38208 38224 38240
  Check149.part38208
  Check149.part38224)
  (FiniteChecks.interval_append test 38240 38256 38272
  Check149.part38240
  Check149.part38256)))
  (FiniteChecks.interval_append test 38272 38336 38400
  (FiniteChecks.interval_append test 38272 38304 38336
  (FiniteChecks.interval_append test 38272 38288 38304
  Check149.part38272
  Check149.part38288)
  (FiniteChecks.interval_append test 38304 38320 38336
  Check149.part38304
  Check149.part38320))
  (FiniteChecks.interval_append test 38336 38368 38400
  (FiniteChecks.interval_append test 38336 38352 38368
  Check149.part38336
  Check149.part38352)
  (FiniteChecks.interval_append test 38368 38384 38400
  Check149.part38368
  Check149.part38384))))
#print axioms Check149.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check150.part38400 : Interval test 38400 38416 :=
  interval_of_check _ 38400 16 (by decide +kernel)
theorem Check150.part38416 : Interval test 38416 38432 :=
  interval_of_check _ 38416 16 (by decide +kernel)
theorem Check150.part38432 : Interval test 38432 38448 :=
  interval_of_check _ 38432 16 (by decide +kernel)
theorem Check150.part38448 : Interval test 38448 38464 :=
  interval_of_check _ 38448 16 (by decide +kernel)
theorem Check150.part38464 : Interval test 38464 38480 :=
  interval_of_check _ 38464 16 (by decide +kernel)
theorem Check150.part38480 : Interval test 38480 38496 :=
  interval_of_check _ 38480 16 (by decide +kernel)
theorem Check150.part38496 : Interval test 38496 38512 :=
  interval_of_check _ 38496 16 (by decide +kernel)
theorem Check150.part38512 : Interval test 38512 38528 :=
  interval_of_check _ 38512 16 (by decide +kernel)
theorem Check150.part38528 : Interval test 38528 38544 :=
  interval_of_check _ 38528 16 (by decide +kernel)
theorem Check150.part38544 : Interval test 38544 38560 :=
  interval_of_check _ 38544 16 (by decide +kernel)
theorem Check150.part38560 : Interval test 38560 38576 :=
  interval_of_check _ 38560 16 (by decide +kernel)
theorem Check150.part38576 : Interval test 38576 38592 :=
  interval_of_check _ 38576 16 (by decide +kernel)
theorem Check150.part38592 : Interval test 38592 38608 :=
  interval_of_check _ 38592 16 (by decide +kernel)
theorem Check150.part38608 : Interval test 38608 38624 :=
  interval_of_check _ 38608 16 (by decide +kernel)
theorem Check150.part38624 : Interval test 38624 38640 :=
  interval_of_check _ 38624 16 (by decide +kernel)
theorem Check150.part38640 : Interval test 38640 38656 :=
  interval_of_check _ 38640 16 (by decide +kernel)
theorem Check150.checked : Interval test 38400 38656 :=
  (FiniteChecks.interval_append test 38400 38528 38656
  (FiniteChecks.interval_append test 38400 38464 38528
  (FiniteChecks.interval_append test 38400 38432 38464
  (FiniteChecks.interval_append test 38400 38416 38432
  Check150.part38400
  Check150.part38416)
  (FiniteChecks.interval_append test 38432 38448 38464
  Check150.part38432
  Check150.part38448))
  (FiniteChecks.interval_append test 38464 38496 38528
  (FiniteChecks.interval_append test 38464 38480 38496
  Check150.part38464
  Check150.part38480)
  (FiniteChecks.interval_append test 38496 38512 38528
  Check150.part38496
  Check150.part38512)))
  (FiniteChecks.interval_append test 38528 38592 38656
  (FiniteChecks.interval_append test 38528 38560 38592
  (FiniteChecks.interval_append test 38528 38544 38560
  Check150.part38528
  Check150.part38544)
  (FiniteChecks.interval_append test 38560 38576 38592
  Check150.part38560
  Check150.part38576))
  (FiniteChecks.interval_append test 38592 38624 38656
  (FiniteChecks.interval_append test 38592 38608 38624
  Check150.part38592
  Check150.part38608)
  (FiniteChecks.interval_append test 38624 38640 38656
  Check150.part38624
  Check150.part38640))))
#print axioms Check150.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check151.part38656 : Interval test 38656 38672 :=
  interval_of_check _ 38656 16 (by decide +kernel)
theorem Check151.part38672 : Interval test 38672 38688 :=
  interval_of_check _ 38672 16 (by decide +kernel)
theorem Check151.part38688 : Interval test 38688 38704 :=
  interval_of_check _ 38688 16 (by decide +kernel)
theorem Check151.part38704 : Interval test 38704 38720 :=
  interval_of_check _ 38704 16 (by decide +kernel)
theorem Check151.part38720 : Interval test 38720 38736 :=
  interval_of_check _ 38720 16 (by decide +kernel)
theorem Check151.part38736 : Interval test 38736 38752 :=
  interval_of_check _ 38736 16 (by decide +kernel)
theorem Check151.part38752 : Interval test 38752 38768 :=
  interval_of_check _ 38752 16 (by decide +kernel)
theorem Check151.part38768 : Interval test 38768 38784 :=
  interval_of_check _ 38768 16 (by decide +kernel)
theorem Check151.part38784 : Interval test 38784 38800 :=
  interval_of_check _ 38784 16 (by decide +kernel)
theorem Check151.part38800 : Interval test 38800 38816 :=
  interval_of_check _ 38800 16 (by decide +kernel)
theorem Check151.part38816 : Interval test 38816 38832 :=
  interval_of_check _ 38816 16 (by decide +kernel)
theorem Check151.part38832 : Interval test 38832 38848 :=
  interval_of_check _ 38832 16 (by decide +kernel)
theorem Check151.part38848 : Interval test 38848 38864 :=
  interval_of_check _ 38848 16 (by decide +kernel)
theorem Check151.part38864 : Interval test 38864 38880 :=
  interval_of_check _ 38864 16 (by decide +kernel)
theorem Check151.part38880 : Interval test 38880 38896 :=
  interval_of_check _ 38880 16 (by decide +kernel)
theorem Check151.part38896 : Interval test 38896 38912 :=
  interval_of_check _ 38896 16 (by decide +kernel)
theorem Check151.checked : Interval test 38656 38912 :=
  (FiniteChecks.interval_append test 38656 38784 38912
  (FiniteChecks.interval_append test 38656 38720 38784
  (FiniteChecks.interval_append test 38656 38688 38720
  (FiniteChecks.interval_append test 38656 38672 38688
  Check151.part38656
  Check151.part38672)
  (FiniteChecks.interval_append test 38688 38704 38720
  Check151.part38688
  Check151.part38704))
  (FiniteChecks.interval_append test 38720 38752 38784
  (FiniteChecks.interval_append test 38720 38736 38752
  Check151.part38720
  Check151.part38736)
  (FiniteChecks.interval_append test 38752 38768 38784
  Check151.part38752
  Check151.part38768)))
  (FiniteChecks.interval_append test 38784 38848 38912
  (FiniteChecks.interval_append test 38784 38816 38848
  (FiniteChecks.interval_append test 38784 38800 38816
  Check151.part38784
  Check151.part38800)
  (FiniteChecks.interval_append test 38816 38832 38848
  Check151.part38816
  Check151.part38832))
  (FiniteChecks.interval_append test 38848 38880 38912
  (FiniteChecks.interval_append test 38848 38864 38880
  Check151.part38848
  Check151.part38864)
  (FiniteChecks.interval_append test 38880 38896 38912
  Check151.part38880
  Check151.part38896))))
#print axioms Check151.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check152.part38912 : Interval test 38912 38928 :=
  interval_of_check _ 38912 16 (by decide +kernel)
theorem Check152.part38928 : Interval test 38928 38944 :=
  interval_of_check _ 38928 16 (by decide +kernel)
theorem Check152.part38944 : Interval test 38944 38960 :=
  interval_of_check _ 38944 16 (by decide +kernel)
theorem Check152.part38960 : Interval test 38960 38976 :=
  interval_of_check _ 38960 16 (by decide +kernel)
theorem Check152.part38976 : Interval test 38976 38992 :=
  interval_of_check _ 38976 16 (by decide +kernel)
theorem Check152.part38992 : Interval test 38992 39008 :=
  interval_of_check _ 38992 16 (by decide +kernel)
theorem Check152.part39008 : Interval test 39008 39024 :=
  interval_of_check _ 39008 16 (by decide +kernel)
theorem Check152.part39024 : Interval test 39024 39040 :=
  interval_of_check _ 39024 16 (by decide +kernel)
theorem Check152.part39040 : Interval test 39040 39056 :=
  interval_of_check _ 39040 16 (by decide +kernel)
theorem Check152.part39056 : Interval test 39056 39072 :=
  interval_of_check _ 39056 16 (by decide +kernel)
theorem Check152.part39072 : Interval test 39072 39088 :=
  interval_of_check _ 39072 16 (by decide +kernel)
theorem Check152.part39088 : Interval test 39088 39104 :=
  interval_of_check _ 39088 16 (by decide +kernel)
theorem Check152.part39104 : Interval test 39104 39120 :=
  interval_of_check _ 39104 16 (by decide +kernel)
theorem Check152.part39120 : Interval test 39120 39136 :=
  interval_of_check _ 39120 16 (by decide +kernel)
theorem Check152.part39136 : Interval test 39136 39152 :=
  interval_of_check _ 39136 16 (by decide +kernel)
theorem Check152.part39152 : Interval test 39152 39168 :=
  interval_of_check _ 39152 16 (by decide +kernel)
theorem Check152.checked : Interval test 38912 39168 :=
  (FiniteChecks.interval_append test 38912 39040 39168
  (FiniteChecks.interval_append test 38912 38976 39040
  (FiniteChecks.interval_append test 38912 38944 38976
  (FiniteChecks.interval_append test 38912 38928 38944
  Check152.part38912
  Check152.part38928)
  (FiniteChecks.interval_append test 38944 38960 38976
  Check152.part38944
  Check152.part38960))
  (FiniteChecks.interval_append test 38976 39008 39040
  (FiniteChecks.interval_append test 38976 38992 39008
  Check152.part38976
  Check152.part38992)
  (FiniteChecks.interval_append test 39008 39024 39040
  Check152.part39008
  Check152.part39024)))
  (FiniteChecks.interval_append test 39040 39104 39168
  (FiniteChecks.interval_append test 39040 39072 39104
  (FiniteChecks.interval_append test 39040 39056 39072
  Check152.part39040
  Check152.part39056)
  (FiniteChecks.interval_append test 39072 39088 39104
  Check152.part39072
  Check152.part39088))
  (FiniteChecks.interval_append test 39104 39136 39168
  (FiniteChecks.interval_append test 39104 39120 39136
  Check152.part39104
  Check152.part39120)
  (FiniteChecks.interval_append test 39136 39152 39168
  Check152.part39136
  Check152.part39152))))
#print axioms Check152.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check153.part39168 : Interval test 39168 39184 :=
  interval_of_check _ 39168 16 (by decide +kernel)
theorem Check153.part39184 : Interval test 39184 39200 :=
  interval_of_check _ 39184 16 (by decide +kernel)
theorem Check153.part39200 : Interval test 39200 39216 :=
  interval_of_check _ 39200 16 (by decide +kernel)
theorem Check153.part39216 : Interval test 39216 39232 :=
  interval_of_check _ 39216 16 (by decide +kernel)
theorem Check153.part39232 : Interval test 39232 39248 :=
  interval_of_check _ 39232 16 (by decide +kernel)
theorem Check153.part39248 : Interval test 39248 39264 :=
  interval_of_check _ 39248 16 (by decide +kernel)
theorem Check153.part39264 : Interval test 39264 39280 :=
  interval_of_check _ 39264 16 (by decide +kernel)
theorem Check153.part39280 : Interval test 39280 39296 :=
  interval_of_check _ 39280 16 (by decide +kernel)
theorem Check153.part39296 : Interval test 39296 39312 :=
  interval_of_check _ 39296 16 (by decide +kernel)
theorem Check153.part39312 : Interval test 39312 39328 :=
  interval_of_check _ 39312 16 (by decide +kernel)
theorem Check153.part39328 : Interval test 39328 39344 :=
  interval_of_check _ 39328 16 (by decide +kernel)
theorem Check153.part39344 : Interval test 39344 39360 :=
  interval_of_check _ 39344 16 (by decide +kernel)
theorem Check153.part39360 : Interval test 39360 39376 :=
  interval_of_check _ 39360 16 (by decide +kernel)
theorem Check153.part39376 : Interval test 39376 39392 :=
  interval_of_check _ 39376 16 (by decide +kernel)
theorem Check153.part39392 : Interval test 39392 39408 :=
  interval_of_check _ 39392 16 (by decide +kernel)
theorem Check153.part39408 : Interval test 39408 39424 :=
  interval_of_check _ 39408 16 (by decide +kernel)
theorem Check153.checked : Interval test 39168 39424 :=
  (FiniteChecks.interval_append test 39168 39296 39424
  (FiniteChecks.interval_append test 39168 39232 39296
  (FiniteChecks.interval_append test 39168 39200 39232
  (FiniteChecks.interval_append test 39168 39184 39200
  Check153.part39168
  Check153.part39184)
  (FiniteChecks.interval_append test 39200 39216 39232
  Check153.part39200
  Check153.part39216))
  (FiniteChecks.interval_append test 39232 39264 39296
  (FiniteChecks.interval_append test 39232 39248 39264
  Check153.part39232
  Check153.part39248)
  (FiniteChecks.interval_append test 39264 39280 39296
  Check153.part39264
  Check153.part39280)))
  (FiniteChecks.interval_append test 39296 39360 39424
  (FiniteChecks.interval_append test 39296 39328 39360
  (FiniteChecks.interval_append test 39296 39312 39328
  Check153.part39296
  Check153.part39312)
  (FiniteChecks.interval_append test 39328 39344 39360
  Check153.part39328
  Check153.part39344))
  (FiniteChecks.interval_append test 39360 39392 39424
  (FiniteChecks.interval_append test 39360 39376 39392
  Check153.part39360
  Check153.part39376)
  (FiniteChecks.interval_append test 39392 39408 39424
  Check153.part39392
  Check153.part39408))))
#print axioms Check153.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check154.part39424 : Interval test 39424 39440 :=
  interval_of_check _ 39424 16 (by decide +kernel)
theorem Check154.part39440 : Interval test 39440 39456 :=
  interval_of_check _ 39440 16 (by decide +kernel)
theorem Check154.part39456 : Interval test 39456 39472 :=
  interval_of_check _ 39456 16 (by decide +kernel)
theorem Check154.part39472 : Interval test 39472 39488 :=
  interval_of_check _ 39472 16 (by decide +kernel)
theorem Check154.part39488 : Interval test 39488 39504 :=
  interval_of_check _ 39488 16 (by decide +kernel)
theorem Check154.part39504 : Interval test 39504 39520 :=
  interval_of_check _ 39504 16 (by decide +kernel)
theorem Check154.part39520 : Interval test 39520 39536 :=
  interval_of_check _ 39520 16 (by decide +kernel)
theorem Check154.part39536 : Interval test 39536 39552 :=
  interval_of_check _ 39536 16 (by decide +kernel)
theorem Check154.part39552 : Interval test 39552 39568 :=
  interval_of_check _ 39552 16 (by decide +kernel)
theorem Check154.part39568 : Interval test 39568 39584 :=
  interval_of_check _ 39568 16 (by decide +kernel)
theorem Check154.part39584 : Interval test 39584 39600 :=
  interval_of_check _ 39584 16 (by decide +kernel)
theorem Check154.part39600 : Interval test 39600 39616 :=
  interval_of_check _ 39600 16 (by decide +kernel)
theorem Check154.part39616 : Interval test 39616 39632 :=
  interval_of_check _ 39616 16 (by decide +kernel)
theorem Check154.part39632 : Interval test 39632 39648 :=
  interval_of_check _ 39632 16 (by decide +kernel)
theorem Check154.part39648 : Interval test 39648 39664 :=
  interval_of_check _ 39648 16 (by decide +kernel)
theorem Check154.part39664 : Interval test 39664 39680 :=
  interval_of_check _ 39664 16 (by decide +kernel)
theorem Check154.checked : Interval test 39424 39680 :=
  (FiniteChecks.interval_append test 39424 39552 39680
  (FiniteChecks.interval_append test 39424 39488 39552
  (FiniteChecks.interval_append test 39424 39456 39488
  (FiniteChecks.interval_append test 39424 39440 39456
  Check154.part39424
  Check154.part39440)
  (FiniteChecks.interval_append test 39456 39472 39488
  Check154.part39456
  Check154.part39472))
  (FiniteChecks.interval_append test 39488 39520 39552
  (FiniteChecks.interval_append test 39488 39504 39520
  Check154.part39488
  Check154.part39504)
  (FiniteChecks.interval_append test 39520 39536 39552
  Check154.part39520
  Check154.part39536)))
  (FiniteChecks.interval_append test 39552 39616 39680
  (FiniteChecks.interval_append test 39552 39584 39616
  (FiniteChecks.interval_append test 39552 39568 39584
  Check154.part39552
  Check154.part39568)
  (FiniteChecks.interval_append test 39584 39600 39616
  Check154.part39584
  Check154.part39600))
  (FiniteChecks.interval_append test 39616 39648 39680
  (FiniteChecks.interval_append test 39616 39632 39648
  Check154.part39616
  Check154.part39632)
  (FiniteChecks.interval_append test 39648 39664 39680
  Check154.part39648
  Check154.part39664))))
#print axioms Check154.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check155.part39680 : Interval test 39680 39696 :=
  interval_of_check _ 39680 16 (by decide +kernel)
theorem Check155.part39696 : Interval test 39696 39712 :=
  interval_of_check _ 39696 16 (by decide +kernel)
theorem Check155.part39712 : Interval test 39712 39728 :=
  interval_of_check _ 39712 16 (by decide +kernel)
theorem Check155.part39728 : Interval test 39728 39744 :=
  interval_of_check _ 39728 16 (by decide +kernel)
theorem Check155.part39744 : Interval test 39744 39760 :=
  interval_of_check _ 39744 16 (by decide +kernel)
theorem Check155.part39760 : Interval test 39760 39776 :=
  interval_of_check _ 39760 16 (by decide +kernel)
theorem Check155.part39776 : Interval test 39776 39792 :=
  interval_of_check _ 39776 16 (by decide +kernel)
theorem Check155.part39792 : Interval test 39792 39808 :=
  interval_of_check _ 39792 16 (by decide +kernel)
theorem Check155.part39808 : Interval test 39808 39824 :=
  interval_of_check _ 39808 16 (by decide +kernel)
theorem Check155.part39824 : Interval test 39824 39840 :=
  interval_of_check _ 39824 16 (by decide +kernel)
theorem Check155.part39840 : Interval test 39840 39856 :=
  interval_of_check _ 39840 16 (by decide +kernel)
theorem Check155.part39856 : Interval test 39856 39872 :=
  interval_of_check _ 39856 16 (by decide +kernel)
theorem Check155.part39872 : Interval test 39872 39888 :=
  interval_of_check _ 39872 16 (by decide +kernel)
theorem Check155.part39888 : Interval test 39888 39904 :=
  interval_of_check _ 39888 16 (by decide +kernel)
theorem Check155.part39904 : Interval test 39904 39920 :=
  interval_of_check _ 39904 16 (by decide +kernel)
theorem Check155.part39920 : Interval test 39920 39936 :=
  interval_of_check _ 39920 16 (by decide +kernel)
theorem Check155.checked : Interval test 39680 39936 :=
  (FiniteChecks.interval_append test 39680 39808 39936
  (FiniteChecks.interval_append test 39680 39744 39808
  (FiniteChecks.interval_append test 39680 39712 39744
  (FiniteChecks.interval_append test 39680 39696 39712
  Check155.part39680
  Check155.part39696)
  (FiniteChecks.interval_append test 39712 39728 39744
  Check155.part39712
  Check155.part39728))
  (FiniteChecks.interval_append test 39744 39776 39808
  (FiniteChecks.interval_append test 39744 39760 39776
  Check155.part39744
  Check155.part39760)
  (FiniteChecks.interval_append test 39776 39792 39808
  Check155.part39776
  Check155.part39792)))
  (FiniteChecks.interval_append test 39808 39872 39936
  (FiniteChecks.interval_append test 39808 39840 39872
  (FiniteChecks.interval_append test 39808 39824 39840
  Check155.part39808
  Check155.part39824)
  (FiniteChecks.interval_append test 39840 39856 39872
  Check155.part39840
  Check155.part39856))
  (FiniteChecks.interval_append test 39872 39904 39936
  (FiniteChecks.interval_append test 39872 39888 39904
  Check155.part39872
  Check155.part39888)
  (FiniteChecks.interval_append test 39904 39920 39936
  Check155.part39904
  Check155.part39920))))
#print axioms Check155.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check156.part39936 : Interval test 39936 39952 :=
  interval_of_check _ 39936 16 (by decide +kernel)
theorem Check156.part39952 : Interval test 39952 39968 :=
  interval_of_check _ 39952 16 (by decide +kernel)
theorem Check156.part39968 : Interval test 39968 39984 :=
  interval_of_check _ 39968 16 (by decide +kernel)
theorem Check156.part39984 : Interval test 39984 40000 :=
  interval_of_check _ 39984 16 (by decide +kernel)
theorem Check156.part40000 : Interval test 40000 40016 :=
  interval_of_check _ 40000 16 (by decide +kernel)
theorem Check156.part40016 : Interval test 40016 40032 :=
  interval_of_check _ 40016 16 (by decide +kernel)
theorem Check156.part40032 : Interval test 40032 40048 :=
  interval_of_check _ 40032 16 (by decide +kernel)
theorem Check156.part40048 : Interval test 40048 40064 :=
  interval_of_check _ 40048 16 (by decide +kernel)
theorem Check156.part40064 : Interval test 40064 40080 :=
  interval_of_check _ 40064 16 (by decide +kernel)
theorem Check156.part40080 : Interval test 40080 40096 :=
  interval_of_check _ 40080 16 (by decide +kernel)
theorem Check156.part40096 : Interval test 40096 40112 :=
  interval_of_check _ 40096 16 (by decide +kernel)
theorem Check156.part40112 : Interval test 40112 40128 :=
  interval_of_check _ 40112 16 (by decide +kernel)
theorem Check156.part40128 : Interval test 40128 40144 :=
  interval_of_check _ 40128 16 (by decide +kernel)
theorem Check156.part40144 : Interval test 40144 40160 :=
  interval_of_check _ 40144 16 (by decide +kernel)
theorem Check156.part40160 : Interval test 40160 40176 :=
  interval_of_check _ 40160 16 (by decide +kernel)
theorem Check156.part40176 : Interval test 40176 40192 :=
  interval_of_check _ 40176 16 (by decide +kernel)
theorem Check156.checked : Interval test 39936 40192 :=
  (FiniteChecks.interval_append test 39936 40064 40192
  (FiniteChecks.interval_append test 39936 40000 40064
  (FiniteChecks.interval_append test 39936 39968 40000
  (FiniteChecks.interval_append test 39936 39952 39968
  Check156.part39936
  Check156.part39952)
  (FiniteChecks.interval_append test 39968 39984 40000
  Check156.part39968
  Check156.part39984))
  (FiniteChecks.interval_append test 40000 40032 40064
  (FiniteChecks.interval_append test 40000 40016 40032
  Check156.part40000
  Check156.part40016)
  (FiniteChecks.interval_append test 40032 40048 40064
  Check156.part40032
  Check156.part40048)))
  (FiniteChecks.interval_append test 40064 40128 40192
  (FiniteChecks.interval_append test 40064 40096 40128
  (FiniteChecks.interval_append test 40064 40080 40096
  Check156.part40064
  Check156.part40080)
  (FiniteChecks.interval_append test 40096 40112 40128
  Check156.part40096
  Check156.part40112))
  (FiniteChecks.interval_append test 40128 40160 40192
  (FiniteChecks.interval_append test 40128 40144 40160
  Check156.part40128
  Check156.part40144)
  (FiniteChecks.interval_append test 40160 40176 40192
  Check156.part40160
  Check156.part40176))))
#print axioms Check156.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check157.part40192 : Interval test 40192 40208 :=
  interval_of_check _ 40192 16 (by decide +kernel)
theorem Check157.part40208 : Interval test 40208 40224 :=
  interval_of_check _ 40208 16 (by decide +kernel)
theorem Check157.part40224 : Interval test 40224 40240 :=
  interval_of_check _ 40224 16 (by decide +kernel)
theorem Check157.part40240 : Interval test 40240 40256 :=
  interval_of_check _ 40240 16 (by decide +kernel)
theorem Check157.part40256 : Interval test 40256 40272 :=
  interval_of_check _ 40256 16 (by decide +kernel)
theorem Check157.part40272 : Interval test 40272 40288 :=
  interval_of_check _ 40272 16 (by decide +kernel)
theorem Check157.part40288 : Interval test 40288 40304 :=
  interval_of_check _ 40288 16 (by decide +kernel)
theorem Check157.part40304 : Interval test 40304 40320 :=
  interval_of_check _ 40304 16 (by decide +kernel)
theorem Check157.part40320 : Interval test 40320 40336 :=
  interval_of_check _ 40320 16 (by decide +kernel)
theorem Check157.part40336 : Interval test 40336 40352 :=
  interval_of_check _ 40336 16 (by decide +kernel)
theorem Check157.part40352 : Interval test 40352 40368 :=
  interval_of_check _ 40352 16 (by decide +kernel)
theorem Check157.part40368 : Interval test 40368 40384 :=
  interval_of_check _ 40368 16 (by decide +kernel)
theorem Check157.part40384 : Interval test 40384 40400 :=
  interval_of_check _ 40384 16 (by decide +kernel)
theorem Check157.part40400 : Interval test 40400 40416 :=
  interval_of_check _ 40400 16 (by decide +kernel)
theorem Check157.part40416 : Interval test 40416 40432 :=
  interval_of_check _ 40416 16 (by decide +kernel)
theorem Check157.part40432 : Interval test 40432 40448 :=
  interval_of_check _ 40432 16 (by decide +kernel)
theorem Check157.checked : Interval test 40192 40448 :=
  (FiniteChecks.interval_append test 40192 40320 40448
  (FiniteChecks.interval_append test 40192 40256 40320
  (FiniteChecks.interval_append test 40192 40224 40256
  (FiniteChecks.interval_append test 40192 40208 40224
  Check157.part40192
  Check157.part40208)
  (FiniteChecks.interval_append test 40224 40240 40256
  Check157.part40224
  Check157.part40240))
  (FiniteChecks.interval_append test 40256 40288 40320
  (FiniteChecks.interval_append test 40256 40272 40288
  Check157.part40256
  Check157.part40272)
  (FiniteChecks.interval_append test 40288 40304 40320
  Check157.part40288
  Check157.part40304)))
  (FiniteChecks.interval_append test 40320 40384 40448
  (FiniteChecks.interval_append test 40320 40352 40384
  (FiniteChecks.interval_append test 40320 40336 40352
  Check157.part40320
  Check157.part40336)
  (FiniteChecks.interval_append test 40352 40368 40384
  Check157.part40352
  Check157.part40368))
  (FiniteChecks.interval_append test 40384 40416 40448
  (FiniteChecks.interval_append test 40384 40400 40416
  Check157.part40384
  Check157.part40400)
  (FiniteChecks.interval_append test 40416 40432 40448
  Check157.part40416
  Check157.part40432))))
#print axioms Check157.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check158.part40448 : Interval test 40448 40464 :=
  interval_of_check _ 40448 16 (by decide +kernel)
theorem Check158.part40464 : Interval test 40464 40480 :=
  interval_of_check _ 40464 16 (by decide +kernel)
theorem Check158.part40480 : Interval test 40480 40496 :=
  interval_of_check _ 40480 16 (by decide +kernel)
theorem Check158.part40496 : Interval test 40496 40512 :=
  interval_of_check _ 40496 16 (by decide +kernel)
theorem Check158.part40512 : Interval test 40512 40528 :=
  interval_of_check _ 40512 16 (by decide +kernel)
theorem Check158.part40528 : Interval test 40528 40544 :=
  interval_of_check _ 40528 16 (by decide +kernel)
theorem Check158.part40544 : Interval test 40544 40560 :=
  interval_of_check _ 40544 16 (by decide +kernel)
theorem Check158.part40560 : Interval test 40560 40576 :=
  interval_of_check _ 40560 16 (by decide +kernel)
theorem Check158.part40576 : Interval test 40576 40592 :=
  interval_of_check _ 40576 16 (by decide +kernel)
theorem Check158.part40592 : Interval test 40592 40608 :=
  interval_of_check _ 40592 16 (by decide +kernel)
theorem Check158.part40608 : Interval test 40608 40624 :=
  interval_of_check _ 40608 16 (by decide +kernel)
theorem Check158.part40624 : Interval test 40624 40640 :=
  interval_of_check _ 40624 16 (by decide +kernel)
theorem Check158.part40640 : Interval test 40640 40656 :=
  interval_of_check _ 40640 16 (by decide +kernel)
theorem Check158.part40656 : Interval test 40656 40672 :=
  interval_of_check _ 40656 16 (by decide +kernel)
theorem Check158.part40672 : Interval test 40672 40688 :=
  interval_of_check _ 40672 16 (by decide +kernel)
theorem Check158.part40688 : Interval test 40688 40704 :=
  interval_of_check _ 40688 16 (by decide +kernel)
theorem Check158.checked : Interval test 40448 40704 :=
  (FiniteChecks.interval_append test 40448 40576 40704
  (FiniteChecks.interval_append test 40448 40512 40576
  (FiniteChecks.interval_append test 40448 40480 40512
  (FiniteChecks.interval_append test 40448 40464 40480
  Check158.part40448
  Check158.part40464)
  (FiniteChecks.interval_append test 40480 40496 40512
  Check158.part40480
  Check158.part40496))
  (FiniteChecks.interval_append test 40512 40544 40576
  (FiniteChecks.interval_append test 40512 40528 40544
  Check158.part40512
  Check158.part40528)
  (FiniteChecks.interval_append test 40544 40560 40576
  Check158.part40544
  Check158.part40560)))
  (FiniteChecks.interval_append test 40576 40640 40704
  (FiniteChecks.interval_append test 40576 40608 40640
  (FiniteChecks.interval_append test 40576 40592 40608
  Check158.part40576
  Check158.part40592)
  (FiniteChecks.interval_append test 40608 40624 40640
  Check158.part40608
  Check158.part40624))
  (FiniteChecks.interval_append test 40640 40672 40704
  (FiniteChecks.interval_append test 40640 40656 40672
  Check158.part40640
  Check158.part40656)
  (FiniteChecks.interval_append test 40672 40688 40704
  Check158.part40672
  Check158.part40688))))
#print axioms Check158.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check159.part40704 : Interval test 40704 40720 :=
  interval_of_check _ 40704 16 (by decide +kernel)
theorem Check159.part40720 : Interval test 40720 40736 :=
  interval_of_check _ 40720 16 (by decide +kernel)
theorem Check159.part40736 : Interval test 40736 40752 :=
  interval_of_check _ 40736 16 (by decide +kernel)
theorem Check159.part40752 : Interval test 40752 40768 :=
  interval_of_check _ 40752 16 (by decide +kernel)
theorem Check159.part40768 : Interval test 40768 40784 :=
  interval_of_check _ 40768 16 (by decide +kernel)
theorem Check159.part40784 : Interval test 40784 40800 :=
  interval_of_check _ 40784 16 (by decide +kernel)
theorem Check159.part40800 : Interval test 40800 40816 :=
  interval_of_check _ 40800 16 (by decide +kernel)
theorem Check159.part40816 : Interval test 40816 40832 :=
  interval_of_check _ 40816 16 (by decide +kernel)
theorem Check159.part40832 : Interval test 40832 40848 :=
  interval_of_check _ 40832 16 (by decide +kernel)
theorem Check159.part40848 : Interval test 40848 40864 :=
  interval_of_check _ 40848 16 (by decide +kernel)
theorem Check159.part40864 : Interval test 40864 40880 :=
  interval_of_check _ 40864 16 (by decide +kernel)
theorem Check159.part40880 : Interval test 40880 40896 :=
  interval_of_check _ 40880 16 (by decide +kernel)
theorem Check159.part40896 : Interval test 40896 40912 :=
  interval_of_check _ 40896 16 (by decide +kernel)
theorem Check159.part40912 : Interval test 40912 40928 :=
  interval_of_check _ 40912 16 (by decide +kernel)
theorem Check159.part40928 : Interval test 40928 40944 :=
  interval_of_check _ 40928 16 (by decide +kernel)
theorem Check159.part40944 : Interval test 40944 40960 :=
  interval_of_check _ 40944 16 (by decide +kernel)
theorem Check159.checked : Interval test 40704 40960 :=
  (FiniteChecks.interval_append test 40704 40832 40960
  (FiniteChecks.interval_append test 40704 40768 40832
  (FiniteChecks.interval_append test 40704 40736 40768
  (FiniteChecks.interval_append test 40704 40720 40736
  Check159.part40704
  Check159.part40720)
  (FiniteChecks.interval_append test 40736 40752 40768
  Check159.part40736
  Check159.part40752))
  (FiniteChecks.interval_append test 40768 40800 40832
  (FiniteChecks.interval_append test 40768 40784 40800
  Check159.part40768
  Check159.part40784)
  (FiniteChecks.interval_append test 40800 40816 40832
  Check159.part40800
  Check159.part40816)))
  (FiniteChecks.interval_append test 40832 40896 40960
  (FiniteChecks.interval_append test 40832 40864 40896
  (FiniteChecks.interval_append test 40832 40848 40864
  Check159.part40832
  Check159.part40848)
  (FiniteChecks.interval_append test 40864 40880 40896
  Check159.part40864
  Check159.part40880))
  (FiniteChecks.interval_append test 40896 40928 40960
  (FiniteChecks.interval_append test 40896 40912 40928
  Check159.part40896
  Check159.part40912)
  (FiniteChecks.interval_append test 40928 40944 40960
  Check159.part40928
  Check159.part40944))))
#print axioms Check159.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
