module
prelude
public import SharedSix0IncidenceData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check060.part15360 : Interval test 15360 15376 :=
  interval_of_check _ 15360 16 (by decide +kernel)
theorem Check060.part15376 : Interval test 15376 15392 :=
  interval_of_check _ 15376 16 (by decide +kernel)
theorem Check060.part15392 : Interval test 15392 15408 :=
  interval_of_check _ 15392 16 (by decide +kernel)
theorem Check060.part15408 : Interval test 15408 15424 :=
  interval_of_check _ 15408 16 (by decide +kernel)
theorem Check060.part15424 : Interval test 15424 15440 :=
  interval_of_check _ 15424 16 (by decide +kernel)
theorem Check060.part15440 : Interval test 15440 15456 :=
  interval_of_check _ 15440 16 (by decide +kernel)
theorem Check060.part15456 : Interval test 15456 15472 :=
  interval_of_check _ 15456 16 (by decide +kernel)
theorem Check060.part15472 : Interval test 15472 15488 :=
  interval_of_check _ 15472 16 (by decide +kernel)
theorem Check060.part15488 : Interval test 15488 15504 :=
  interval_of_check _ 15488 16 (by decide +kernel)
theorem Check060.part15504 : Interval test 15504 15520 :=
  interval_of_check _ 15504 16 (by decide +kernel)
theorem Check060.part15520 : Interval test 15520 15536 :=
  interval_of_check _ 15520 16 (by decide +kernel)
theorem Check060.part15536 : Interval test 15536 15552 :=
  interval_of_check _ 15536 16 (by decide +kernel)
theorem Check060.part15552 : Interval test 15552 15568 :=
  interval_of_check _ 15552 16 (by decide +kernel)
theorem Check060.part15568 : Interval test 15568 15584 :=
  interval_of_check _ 15568 16 (by decide +kernel)
theorem Check060.part15584 : Interval test 15584 15600 :=
  interval_of_check _ 15584 16 (by decide +kernel)
theorem Check060.part15600 : Interval test 15600 15616 :=
  interval_of_check _ 15600 16 (by decide +kernel)
theorem Check060.checked : Interval test 15360 15616 :=
  (FiniteChecks.interval_append test 15360 15488 15616
  (FiniteChecks.interval_append test 15360 15424 15488
  (FiniteChecks.interval_append test 15360 15392 15424
  (FiniteChecks.interval_append test 15360 15376 15392
  Check060.part15360
  Check060.part15376)
  (FiniteChecks.interval_append test 15392 15408 15424
  Check060.part15392
  Check060.part15408))
  (FiniteChecks.interval_append test 15424 15456 15488
  (FiniteChecks.interval_append test 15424 15440 15456
  Check060.part15424
  Check060.part15440)
  (FiniteChecks.interval_append test 15456 15472 15488
  Check060.part15456
  Check060.part15472)))
  (FiniteChecks.interval_append test 15488 15552 15616
  (FiniteChecks.interval_append test 15488 15520 15552
  (FiniteChecks.interval_append test 15488 15504 15520
  Check060.part15488
  Check060.part15504)
  (FiniteChecks.interval_append test 15520 15536 15552
  Check060.part15520
  Check060.part15536))
  (FiniteChecks.interval_append test 15552 15584 15616
  (FiniteChecks.interval_append test 15552 15568 15584
  Check060.part15552
  Check060.part15568)
  (FiniteChecks.interval_append test 15584 15600 15616
  Check060.part15584
  Check060.part15600))))
#print axioms Check060.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check061.part15616 : Interval test 15616 15632 :=
  interval_of_check _ 15616 16 (by decide +kernel)
theorem Check061.part15632 : Interval test 15632 15648 :=
  interval_of_check _ 15632 16 (by decide +kernel)
theorem Check061.part15648 : Interval test 15648 15664 :=
  interval_of_check _ 15648 16 (by decide +kernel)
theorem Check061.part15664 : Interval test 15664 15680 :=
  interval_of_check _ 15664 16 (by decide +kernel)
theorem Check061.part15680 : Interval test 15680 15696 :=
  interval_of_check _ 15680 16 (by decide +kernel)
theorem Check061.part15696 : Interval test 15696 15712 :=
  interval_of_check _ 15696 16 (by decide +kernel)
theorem Check061.part15712 : Interval test 15712 15728 :=
  interval_of_check _ 15712 16 (by decide +kernel)
theorem Check061.part15728 : Interval test 15728 15744 :=
  interval_of_check _ 15728 16 (by decide +kernel)
theorem Check061.part15744 : Interval test 15744 15760 :=
  interval_of_check _ 15744 16 (by decide +kernel)
theorem Check061.part15760 : Interval test 15760 15776 :=
  interval_of_check _ 15760 16 (by decide +kernel)
theorem Check061.part15776 : Interval test 15776 15792 :=
  interval_of_check _ 15776 16 (by decide +kernel)
theorem Check061.part15792 : Interval test 15792 15808 :=
  interval_of_check _ 15792 16 (by decide +kernel)
theorem Check061.part15808 : Interval test 15808 15824 :=
  interval_of_check _ 15808 16 (by decide +kernel)
theorem Check061.part15824 : Interval test 15824 15840 :=
  interval_of_check _ 15824 16 (by decide +kernel)
theorem Check061.part15840 : Interval test 15840 15856 :=
  interval_of_check _ 15840 16 (by decide +kernel)
theorem Check061.part15856 : Interval test 15856 15872 :=
  interval_of_check _ 15856 16 (by decide +kernel)
theorem Check061.checked : Interval test 15616 15872 :=
  (FiniteChecks.interval_append test 15616 15744 15872
  (FiniteChecks.interval_append test 15616 15680 15744
  (FiniteChecks.interval_append test 15616 15648 15680
  (FiniteChecks.interval_append test 15616 15632 15648
  Check061.part15616
  Check061.part15632)
  (FiniteChecks.interval_append test 15648 15664 15680
  Check061.part15648
  Check061.part15664))
  (FiniteChecks.interval_append test 15680 15712 15744
  (FiniteChecks.interval_append test 15680 15696 15712
  Check061.part15680
  Check061.part15696)
  (FiniteChecks.interval_append test 15712 15728 15744
  Check061.part15712
  Check061.part15728)))
  (FiniteChecks.interval_append test 15744 15808 15872
  (FiniteChecks.interval_append test 15744 15776 15808
  (FiniteChecks.interval_append test 15744 15760 15776
  Check061.part15744
  Check061.part15760)
  (FiniteChecks.interval_append test 15776 15792 15808
  Check061.part15776
  Check061.part15792))
  (FiniteChecks.interval_append test 15808 15840 15872
  (FiniteChecks.interval_append test 15808 15824 15840
  Check061.part15808
  Check061.part15824)
  (FiniteChecks.interval_append test 15840 15856 15872
  Check061.part15840
  Check061.part15856))))
#print axioms Check061.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check062.part15872 : Interval test 15872 15888 :=
  interval_of_check _ 15872 16 (by decide +kernel)
theorem Check062.part15888 : Interval test 15888 15904 :=
  interval_of_check _ 15888 16 (by decide +kernel)
theorem Check062.part15904 : Interval test 15904 15920 :=
  interval_of_check _ 15904 16 (by decide +kernel)
theorem Check062.part15920 : Interval test 15920 15936 :=
  interval_of_check _ 15920 16 (by decide +kernel)
theorem Check062.part15936 : Interval test 15936 15952 :=
  interval_of_check _ 15936 16 (by decide +kernel)
theorem Check062.part15952 : Interval test 15952 15968 :=
  interval_of_check _ 15952 16 (by decide +kernel)
theorem Check062.part15968 : Interval test 15968 15984 :=
  interval_of_check _ 15968 16 (by decide +kernel)
theorem Check062.part15984 : Interval test 15984 16000 :=
  interval_of_check _ 15984 16 (by decide +kernel)
theorem Check062.part16000 : Interval test 16000 16016 :=
  interval_of_check _ 16000 16 (by decide +kernel)
theorem Check062.part16016 : Interval test 16016 16032 :=
  interval_of_check _ 16016 16 (by decide +kernel)
theorem Check062.part16032 : Interval test 16032 16048 :=
  interval_of_check _ 16032 16 (by decide +kernel)
theorem Check062.part16048 : Interval test 16048 16064 :=
  interval_of_check _ 16048 16 (by decide +kernel)
theorem Check062.part16064 : Interval test 16064 16080 :=
  interval_of_check _ 16064 16 (by decide +kernel)
theorem Check062.part16080 : Interval test 16080 16096 :=
  interval_of_check _ 16080 16 (by decide +kernel)
theorem Check062.part16096 : Interval test 16096 16112 :=
  interval_of_check _ 16096 16 (by decide +kernel)
theorem Check062.part16112 : Interval test 16112 16128 :=
  interval_of_check _ 16112 16 (by decide +kernel)
theorem Check062.checked : Interval test 15872 16128 :=
  (FiniteChecks.interval_append test 15872 16000 16128
  (FiniteChecks.interval_append test 15872 15936 16000
  (FiniteChecks.interval_append test 15872 15904 15936
  (FiniteChecks.interval_append test 15872 15888 15904
  Check062.part15872
  Check062.part15888)
  (FiniteChecks.interval_append test 15904 15920 15936
  Check062.part15904
  Check062.part15920))
  (FiniteChecks.interval_append test 15936 15968 16000
  (FiniteChecks.interval_append test 15936 15952 15968
  Check062.part15936
  Check062.part15952)
  (FiniteChecks.interval_append test 15968 15984 16000
  Check062.part15968
  Check062.part15984)))
  (FiniteChecks.interval_append test 16000 16064 16128
  (FiniteChecks.interval_append test 16000 16032 16064
  (FiniteChecks.interval_append test 16000 16016 16032
  Check062.part16000
  Check062.part16016)
  (FiniteChecks.interval_append test 16032 16048 16064
  Check062.part16032
  Check062.part16048))
  (FiniteChecks.interval_append test 16064 16096 16128
  (FiniteChecks.interval_append test 16064 16080 16096
  Check062.part16064
  Check062.part16080)
  (FiniteChecks.interval_append test 16096 16112 16128
  Check062.part16096
  Check062.part16112))))
#print axioms Check062.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check063.part16128 : Interval test 16128 16144 :=
  interval_of_check _ 16128 16 (by decide +kernel)
theorem Check063.part16144 : Interval test 16144 16160 :=
  interval_of_check _ 16144 16 (by decide +kernel)
theorem Check063.part16160 : Interval test 16160 16176 :=
  interval_of_check _ 16160 16 (by decide +kernel)
theorem Check063.part16176 : Interval test 16176 16192 :=
  interval_of_check _ 16176 16 (by decide +kernel)
theorem Check063.part16192 : Interval test 16192 16208 :=
  interval_of_check _ 16192 16 (by decide +kernel)
theorem Check063.part16208 : Interval test 16208 16224 :=
  interval_of_check _ 16208 16 (by decide +kernel)
theorem Check063.part16224 : Interval test 16224 16240 :=
  interval_of_check _ 16224 16 (by decide +kernel)
theorem Check063.part16240 : Interval test 16240 16256 :=
  interval_of_check _ 16240 16 (by decide +kernel)
theorem Check063.part16256 : Interval test 16256 16272 :=
  interval_of_check _ 16256 16 (by decide +kernel)
theorem Check063.part16272 : Interval test 16272 16288 :=
  interval_of_check _ 16272 16 (by decide +kernel)
theorem Check063.part16288 : Interval test 16288 16304 :=
  interval_of_check _ 16288 16 (by decide +kernel)
theorem Check063.part16304 : Interval test 16304 16320 :=
  interval_of_check _ 16304 16 (by decide +kernel)
theorem Check063.part16320 : Interval test 16320 16336 :=
  interval_of_check _ 16320 16 (by decide +kernel)
theorem Check063.part16336 : Interval test 16336 16352 :=
  interval_of_check _ 16336 16 (by decide +kernel)
theorem Check063.part16352 : Interval test 16352 16368 :=
  interval_of_check _ 16352 16 (by decide +kernel)
theorem Check063.part16368 : Interval test 16368 16384 :=
  interval_of_check _ 16368 16 (by decide +kernel)
theorem Check063.checked : Interval test 16128 16384 :=
  (FiniteChecks.interval_append test 16128 16256 16384
  (FiniteChecks.interval_append test 16128 16192 16256
  (FiniteChecks.interval_append test 16128 16160 16192
  (FiniteChecks.interval_append test 16128 16144 16160
  Check063.part16128
  Check063.part16144)
  (FiniteChecks.interval_append test 16160 16176 16192
  Check063.part16160
  Check063.part16176))
  (FiniteChecks.interval_append test 16192 16224 16256
  (FiniteChecks.interval_append test 16192 16208 16224
  Check063.part16192
  Check063.part16208)
  (FiniteChecks.interval_append test 16224 16240 16256
  Check063.part16224
  Check063.part16240)))
  (FiniteChecks.interval_append test 16256 16320 16384
  (FiniteChecks.interval_append test 16256 16288 16320
  (FiniteChecks.interval_append test 16256 16272 16288
  Check063.part16256
  Check063.part16272)
  (FiniteChecks.interval_append test 16288 16304 16320
  Check063.part16288
  Check063.part16304))
  (FiniteChecks.interval_append test 16320 16352 16384
  (FiniteChecks.interval_append test 16320 16336 16352
  Check063.part16320
  Check063.part16336)
  (FiniteChecks.interval_append test 16352 16368 16384
  Check063.part16352
  Check063.part16368))))
#print axioms Check063.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check064.part16384 : Interval test 16384 16400 :=
  interval_of_check _ 16384 16 (by decide +kernel)
theorem Check064.part16400 : Interval test 16400 16416 :=
  interval_of_check _ 16400 16 (by decide +kernel)
theorem Check064.part16416 : Interval test 16416 16432 :=
  interval_of_check _ 16416 16 (by decide +kernel)
theorem Check064.part16432 : Interval test 16432 16448 :=
  interval_of_check _ 16432 16 (by decide +kernel)
theorem Check064.part16448 : Interval test 16448 16464 :=
  interval_of_check _ 16448 16 (by decide +kernel)
theorem Check064.part16464 : Interval test 16464 16480 :=
  interval_of_check _ 16464 16 (by decide +kernel)
theorem Check064.part16480 : Interval test 16480 16496 :=
  interval_of_check _ 16480 16 (by decide +kernel)
theorem Check064.part16496 : Interval test 16496 16512 :=
  interval_of_check _ 16496 16 (by decide +kernel)
theorem Check064.part16512 : Interval test 16512 16528 :=
  interval_of_check _ 16512 16 (by decide +kernel)
theorem Check064.part16528 : Interval test 16528 16544 :=
  interval_of_check _ 16528 16 (by decide +kernel)
theorem Check064.part16544 : Interval test 16544 16560 :=
  interval_of_check _ 16544 16 (by decide +kernel)
theorem Check064.part16560 : Interval test 16560 16576 :=
  interval_of_check _ 16560 16 (by decide +kernel)
theorem Check064.part16576 : Interval test 16576 16592 :=
  interval_of_check _ 16576 16 (by decide +kernel)
theorem Check064.part16592 : Interval test 16592 16608 :=
  interval_of_check _ 16592 16 (by decide +kernel)
theorem Check064.part16608 : Interval test 16608 16624 :=
  interval_of_check _ 16608 16 (by decide +kernel)
theorem Check064.part16624 : Interval test 16624 16640 :=
  interval_of_check _ 16624 16 (by decide +kernel)
theorem Check064.checked : Interval test 16384 16640 :=
  (FiniteChecks.interval_append test 16384 16512 16640
  (FiniteChecks.interval_append test 16384 16448 16512
  (FiniteChecks.interval_append test 16384 16416 16448
  (FiniteChecks.interval_append test 16384 16400 16416
  Check064.part16384
  Check064.part16400)
  (FiniteChecks.interval_append test 16416 16432 16448
  Check064.part16416
  Check064.part16432))
  (FiniteChecks.interval_append test 16448 16480 16512
  (FiniteChecks.interval_append test 16448 16464 16480
  Check064.part16448
  Check064.part16464)
  (FiniteChecks.interval_append test 16480 16496 16512
  Check064.part16480
  Check064.part16496)))
  (FiniteChecks.interval_append test 16512 16576 16640
  (FiniteChecks.interval_append test 16512 16544 16576
  (FiniteChecks.interval_append test 16512 16528 16544
  Check064.part16512
  Check064.part16528)
  (FiniteChecks.interval_append test 16544 16560 16576
  Check064.part16544
  Check064.part16560))
  (FiniteChecks.interval_append test 16576 16608 16640
  (FiniteChecks.interval_append test 16576 16592 16608
  Check064.part16576
  Check064.part16592)
  (FiniteChecks.interval_append test 16608 16624 16640
  Check064.part16608
  Check064.part16624))))
#print axioms Check064.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check065.part16640 : Interval test 16640 16656 :=
  interval_of_check _ 16640 16 (by decide +kernel)
theorem Check065.part16656 : Interval test 16656 16672 :=
  interval_of_check _ 16656 16 (by decide +kernel)
theorem Check065.part16672 : Interval test 16672 16688 :=
  interval_of_check _ 16672 16 (by decide +kernel)
theorem Check065.part16688 : Interval test 16688 16704 :=
  interval_of_check _ 16688 16 (by decide +kernel)
theorem Check065.part16704 : Interval test 16704 16720 :=
  interval_of_check _ 16704 16 (by decide +kernel)
theorem Check065.part16720 : Interval test 16720 16736 :=
  interval_of_check _ 16720 16 (by decide +kernel)
theorem Check065.part16736 : Interval test 16736 16752 :=
  interval_of_check _ 16736 16 (by decide +kernel)
theorem Check065.part16752 : Interval test 16752 16768 :=
  interval_of_check _ 16752 16 (by decide +kernel)
theorem Check065.part16768 : Interval test 16768 16784 :=
  interval_of_check _ 16768 16 (by decide +kernel)
theorem Check065.part16784 : Interval test 16784 16800 :=
  interval_of_check _ 16784 16 (by decide +kernel)
theorem Check065.part16800 : Interval test 16800 16816 :=
  interval_of_check _ 16800 16 (by decide +kernel)
theorem Check065.part16816 : Interval test 16816 16832 :=
  interval_of_check _ 16816 16 (by decide +kernel)
theorem Check065.part16832 : Interval test 16832 16848 :=
  interval_of_check _ 16832 16 (by decide +kernel)
theorem Check065.part16848 : Interval test 16848 16864 :=
  interval_of_check _ 16848 16 (by decide +kernel)
theorem Check065.part16864 : Interval test 16864 16880 :=
  interval_of_check _ 16864 16 (by decide +kernel)
theorem Check065.part16880 : Interval test 16880 16896 :=
  interval_of_check _ 16880 16 (by decide +kernel)
theorem Check065.checked : Interval test 16640 16896 :=
  (FiniteChecks.interval_append test 16640 16768 16896
  (FiniteChecks.interval_append test 16640 16704 16768
  (FiniteChecks.interval_append test 16640 16672 16704
  (FiniteChecks.interval_append test 16640 16656 16672
  Check065.part16640
  Check065.part16656)
  (FiniteChecks.interval_append test 16672 16688 16704
  Check065.part16672
  Check065.part16688))
  (FiniteChecks.interval_append test 16704 16736 16768
  (FiniteChecks.interval_append test 16704 16720 16736
  Check065.part16704
  Check065.part16720)
  (FiniteChecks.interval_append test 16736 16752 16768
  Check065.part16736
  Check065.part16752)))
  (FiniteChecks.interval_append test 16768 16832 16896
  (FiniteChecks.interval_append test 16768 16800 16832
  (FiniteChecks.interval_append test 16768 16784 16800
  Check065.part16768
  Check065.part16784)
  (FiniteChecks.interval_append test 16800 16816 16832
  Check065.part16800
  Check065.part16816))
  (FiniteChecks.interval_append test 16832 16864 16896
  (FiniteChecks.interval_append test 16832 16848 16864
  Check065.part16832
  Check065.part16848)
  (FiniteChecks.interval_append test 16864 16880 16896
  Check065.part16864
  Check065.part16880))))
#print axioms Check065.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check066.part16896 : Interval test 16896 16912 :=
  interval_of_check _ 16896 16 (by decide +kernel)
theorem Check066.part16912 : Interval test 16912 16928 :=
  interval_of_check _ 16912 16 (by decide +kernel)
theorem Check066.part16928 : Interval test 16928 16944 :=
  interval_of_check _ 16928 16 (by decide +kernel)
theorem Check066.part16944 : Interval test 16944 16960 :=
  interval_of_check _ 16944 16 (by decide +kernel)
theorem Check066.part16960 : Interval test 16960 16976 :=
  interval_of_check _ 16960 16 (by decide +kernel)
theorem Check066.part16976 : Interval test 16976 16992 :=
  interval_of_check _ 16976 16 (by decide +kernel)
theorem Check066.part16992 : Interval test 16992 17008 :=
  interval_of_check _ 16992 16 (by decide +kernel)
theorem Check066.part17008 : Interval test 17008 17024 :=
  interval_of_check _ 17008 16 (by decide +kernel)
theorem Check066.part17024 : Interval test 17024 17040 :=
  interval_of_check _ 17024 16 (by decide +kernel)
theorem Check066.part17040 : Interval test 17040 17056 :=
  interval_of_check _ 17040 16 (by decide +kernel)
theorem Check066.part17056 : Interval test 17056 17072 :=
  interval_of_check _ 17056 16 (by decide +kernel)
theorem Check066.part17072 : Interval test 17072 17088 :=
  interval_of_check _ 17072 16 (by decide +kernel)
theorem Check066.part17088 : Interval test 17088 17104 :=
  interval_of_check _ 17088 16 (by decide +kernel)
theorem Check066.part17104 : Interval test 17104 17120 :=
  interval_of_check _ 17104 16 (by decide +kernel)
theorem Check066.part17120 : Interval test 17120 17136 :=
  interval_of_check _ 17120 16 (by decide +kernel)
theorem Check066.part17136 : Interval test 17136 17152 :=
  interval_of_check _ 17136 16 (by decide +kernel)
theorem Check066.checked : Interval test 16896 17152 :=
  (FiniteChecks.interval_append test 16896 17024 17152
  (FiniteChecks.interval_append test 16896 16960 17024
  (FiniteChecks.interval_append test 16896 16928 16960
  (FiniteChecks.interval_append test 16896 16912 16928
  Check066.part16896
  Check066.part16912)
  (FiniteChecks.interval_append test 16928 16944 16960
  Check066.part16928
  Check066.part16944))
  (FiniteChecks.interval_append test 16960 16992 17024
  (FiniteChecks.interval_append test 16960 16976 16992
  Check066.part16960
  Check066.part16976)
  (FiniteChecks.interval_append test 16992 17008 17024
  Check066.part16992
  Check066.part17008)))
  (FiniteChecks.interval_append test 17024 17088 17152
  (FiniteChecks.interval_append test 17024 17056 17088
  (FiniteChecks.interval_append test 17024 17040 17056
  Check066.part17024
  Check066.part17040)
  (FiniteChecks.interval_append test 17056 17072 17088
  Check066.part17056
  Check066.part17072))
  (FiniteChecks.interval_append test 17088 17120 17152
  (FiniteChecks.interval_append test 17088 17104 17120
  Check066.part17088
  Check066.part17104)
  (FiniteChecks.interval_append test 17120 17136 17152
  Check066.part17120
  Check066.part17136))))
#print axioms Check066.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check067.part17152 : Interval test 17152 17168 :=
  interval_of_check _ 17152 16 (by decide +kernel)
theorem Check067.part17168 : Interval test 17168 17184 :=
  interval_of_check _ 17168 16 (by decide +kernel)
theorem Check067.part17184 : Interval test 17184 17200 :=
  interval_of_check _ 17184 16 (by decide +kernel)
theorem Check067.part17200 : Interval test 17200 17216 :=
  interval_of_check _ 17200 16 (by decide +kernel)
theorem Check067.part17216 : Interval test 17216 17232 :=
  interval_of_check _ 17216 16 (by decide +kernel)
theorem Check067.part17232 : Interval test 17232 17248 :=
  interval_of_check _ 17232 16 (by decide +kernel)
theorem Check067.part17248 : Interval test 17248 17264 :=
  interval_of_check _ 17248 16 (by decide +kernel)
theorem Check067.part17264 : Interval test 17264 17280 :=
  interval_of_check _ 17264 16 (by decide +kernel)
theorem Check067.part17280 : Interval test 17280 17296 :=
  interval_of_check _ 17280 16 (by decide +kernel)
theorem Check067.part17296 : Interval test 17296 17312 :=
  interval_of_check _ 17296 16 (by decide +kernel)
theorem Check067.part17312 : Interval test 17312 17328 :=
  interval_of_check _ 17312 16 (by decide +kernel)
theorem Check067.part17328 : Interval test 17328 17344 :=
  interval_of_check _ 17328 16 (by decide +kernel)
theorem Check067.part17344 : Interval test 17344 17360 :=
  interval_of_check _ 17344 16 (by decide +kernel)
theorem Check067.part17360 : Interval test 17360 17376 :=
  interval_of_check _ 17360 16 (by decide +kernel)
theorem Check067.part17376 : Interval test 17376 17392 :=
  interval_of_check _ 17376 16 (by decide +kernel)
theorem Check067.part17392 : Interval test 17392 17408 :=
  interval_of_check _ 17392 16 (by decide +kernel)
theorem Check067.checked : Interval test 17152 17408 :=
  (FiniteChecks.interval_append test 17152 17280 17408
  (FiniteChecks.interval_append test 17152 17216 17280
  (FiniteChecks.interval_append test 17152 17184 17216
  (FiniteChecks.interval_append test 17152 17168 17184
  Check067.part17152
  Check067.part17168)
  (FiniteChecks.interval_append test 17184 17200 17216
  Check067.part17184
  Check067.part17200))
  (FiniteChecks.interval_append test 17216 17248 17280
  (FiniteChecks.interval_append test 17216 17232 17248
  Check067.part17216
  Check067.part17232)
  (FiniteChecks.interval_append test 17248 17264 17280
  Check067.part17248
  Check067.part17264)))
  (FiniteChecks.interval_append test 17280 17344 17408
  (FiniteChecks.interval_append test 17280 17312 17344
  (FiniteChecks.interval_append test 17280 17296 17312
  Check067.part17280
  Check067.part17296)
  (FiniteChecks.interval_append test 17312 17328 17344
  Check067.part17312
  Check067.part17328))
  (FiniteChecks.interval_append test 17344 17376 17408
  (FiniteChecks.interval_append test 17344 17360 17376
  Check067.part17344
  Check067.part17360)
  (FiniteChecks.interval_append test 17376 17392 17408
  Check067.part17376
  Check067.part17392))))
#print axioms Check067.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check068.part17408 : Interval test 17408 17424 :=
  interval_of_check _ 17408 16 (by decide +kernel)
theorem Check068.part17424 : Interval test 17424 17440 :=
  interval_of_check _ 17424 16 (by decide +kernel)
theorem Check068.part17440 : Interval test 17440 17456 :=
  interval_of_check _ 17440 16 (by decide +kernel)
theorem Check068.part17456 : Interval test 17456 17472 :=
  interval_of_check _ 17456 16 (by decide +kernel)
theorem Check068.part17472 : Interval test 17472 17488 :=
  interval_of_check _ 17472 16 (by decide +kernel)
theorem Check068.part17488 : Interval test 17488 17504 :=
  interval_of_check _ 17488 16 (by decide +kernel)
theorem Check068.part17504 : Interval test 17504 17520 :=
  interval_of_check _ 17504 16 (by decide +kernel)
theorem Check068.part17520 : Interval test 17520 17536 :=
  interval_of_check _ 17520 16 (by decide +kernel)
theorem Check068.part17536 : Interval test 17536 17552 :=
  interval_of_check _ 17536 16 (by decide +kernel)
theorem Check068.part17552 : Interval test 17552 17568 :=
  interval_of_check _ 17552 16 (by decide +kernel)
theorem Check068.part17568 : Interval test 17568 17584 :=
  interval_of_check _ 17568 16 (by decide +kernel)
theorem Check068.part17584 : Interval test 17584 17600 :=
  interval_of_check _ 17584 16 (by decide +kernel)
theorem Check068.part17600 : Interval test 17600 17616 :=
  interval_of_check _ 17600 16 (by decide +kernel)
theorem Check068.part17616 : Interval test 17616 17632 :=
  interval_of_check _ 17616 16 (by decide +kernel)
theorem Check068.part17632 : Interval test 17632 17648 :=
  interval_of_check _ 17632 16 (by decide +kernel)
theorem Check068.part17648 : Interval test 17648 17664 :=
  interval_of_check _ 17648 16 (by decide +kernel)
theorem Check068.checked : Interval test 17408 17664 :=
  (FiniteChecks.interval_append test 17408 17536 17664
  (FiniteChecks.interval_append test 17408 17472 17536
  (FiniteChecks.interval_append test 17408 17440 17472
  (FiniteChecks.interval_append test 17408 17424 17440
  Check068.part17408
  Check068.part17424)
  (FiniteChecks.interval_append test 17440 17456 17472
  Check068.part17440
  Check068.part17456))
  (FiniteChecks.interval_append test 17472 17504 17536
  (FiniteChecks.interval_append test 17472 17488 17504
  Check068.part17472
  Check068.part17488)
  (FiniteChecks.interval_append test 17504 17520 17536
  Check068.part17504
  Check068.part17520)))
  (FiniteChecks.interval_append test 17536 17600 17664
  (FiniteChecks.interval_append test 17536 17568 17600
  (FiniteChecks.interval_append test 17536 17552 17568
  Check068.part17536
  Check068.part17552)
  (FiniteChecks.interval_append test 17568 17584 17600
  Check068.part17568
  Check068.part17584))
  (FiniteChecks.interval_append test 17600 17632 17664
  (FiniteChecks.interval_append test 17600 17616 17632
  Check068.part17600
  Check068.part17616)
  (FiniteChecks.interval_append test 17632 17648 17664
  Check068.part17632
  Check068.part17648))))
#print axioms Check068.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check069.part17664 : Interval test 17664 17680 :=
  interval_of_check _ 17664 16 (by decide +kernel)
theorem Check069.part17680 : Interval test 17680 17696 :=
  interval_of_check _ 17680 16 (by decide +kernel)
theorem Check069.part17696 : Interval test 17696 17712 :=
  interval_of_check _ 17696 16 (by decide +kernel)
theorem Check069.part17712 : Interval test 17712 17728 :=
  interval_of_check _ 17712 16 (by decide +kernel)
theorem Check069.part17728 : Interval test 17728 17744 :=
  interval_of_check _ 17728 16 (by decide +kernel)
theorem Check069.part17744 : Interval test 17744 17760 :=
  interval_of_check _ 17744 16 (by decide +kernel)
theorem Check069.part17760 : Interval test 17760 17776 :=
  interval_of_check _ 17760 16 (by decide +kernel)
theorem Check069.part17776 : Interval test 17776 17792 :=
  interval_of_check _ 17776 16 (by decide +kernel)
theorem Check069.part17792 : Interval test 17792 17808 :=
  interval_of_check _ 17792 16 (by decide +kernel)
theorem Check069.part17808 : Interval test 17808 17824 :=
  interval_of_check _ 17808 16 (by decide +kernel)
theorem Check069.part17824 : Interval test 17824 17840 :=
  interval_of_check _ 17824 16 (by decide +kernel)
theorem Check069.part17840 : Interval test 17840 17856 :=
  interval_of_check _ 17840 16 (by decide +kernel)
theorem Check069.part17856 : Interval test 17856 17872 :=
  interval_of_check _ 17856 16 (by decide +kernel)
theorem Check069.part17872 : Interval test 17872 17888 :=
  interval_of_check _ 17872 16 (by decide +kernel)
theorem Check069.part17888 : Interval test 17888 17904 :=
  interval_of_check _ 17888 16 (by decide +kernel)
theorem Check069.part17904 : Interval test 17904 17920 :=
  interval_of_check _ 17904 16 (by decide +kernel)
theorem Check069.checked : Interval test 17664 17920 :=
  (FiniteChecks.interval_append test 17664 17792 17920
  (FiniteChecks.interval_append test 17664 17728 17792
  (FiniteChecks.interval_append test 17664 17696 17728
  (FiniteChecks.interval_append test 17664 17680 17696
  Check069.part17664
  Check069.part17680)
  (FiniteChecks.interval_append test 17696 17712 17728
  Check069.part17696
  Check069.part17712))
  (FiniteChecks.interval_append test 17728 17760 17792
  (FiniteChecks.interval_append test 17728 17744 17760
  Check069.part17728
  Check069.part17744)
  (FiniteChecks.interval_append test 17760 17776 17792
  Check069.part17760
  Check069.part17776)))
  (FiniteChecks.interval_append test 17792 17856 17920
  (FiniteChecks.interval_append test 17792 17824 17856
  (FiniteChecks.interval_append test 17792 17808 17824
  Check069.part17792
  Check069.part17808)
  (FiniteChecks.interval_append test 17824 17840 17856
  Check069.part17824
  Check069.part17840))
  (FiniteChecks.interval_append test 17856 17888 17920
  (FiniteChecks.interval_append test 17856 17872 17888
  Check069.part17856
  Check069.part17872)
  (FiniteChecks.interval_append test 17888 17904 17920
  Check069.part17888
  Check069.part17904))))
#print axioms Check069.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check070.part17920 : Interval test 17920 17936 :=
  interval_of_check _ 17920 16 (by decide +kernel)
theorem Check070.part17936 : Interval test 17936 17952 :=
  interval_of_check _ 17936 16 (by decide +kernel)
theorem Check070.part17952 : Interval test 17952 17968 :=
  interval_of_check _ 17952 16 (by decide +kernel)
theorem Check070.part17968 : Interval test 17968 17984 :=
  interval_of_check _ 17968 16 (by decide +kernel)
theorem Check070.part17984 : Interval test 17984 18000 :=
  interval_of_check _ 17984 16 (by decide +kernel)
theorem Check070.part18000 : Interval test 18000 18016 :=
  interval_of_check _ 18000 16 (by decide +kernel)
theorem Check070.part18016 : Interval test 18016 18032 :=
  interval_of_check _ 18016 16 (by decide +kernel)
theorem Check070.part18032 : Interval test 18032 18048 :=
  interval_of_check _ 18032 16 (by decide +kernel)
theorem Check070.part18048 : Interval test 18048 18064 :=
  interval_of_check _ 18048 16 (by decide +kernel)
theorem Check070.part18064 : Interval test 18064 18080 :=
  interval_of_check _ 18064 16 (by decide +kernel)
theorem Check070.part18080 : Interval test 18080 18096 :=
  interval_of_check _ 18080 16 (by decide +kernel)
theorem Check070.part18096 : Interval test 18096 18112 :=
  interval_of_check _ 18096 16 (by decide +kernel)
theorem Check070.part18112 : Interval test 18112 18128 :=
  interval_of_check _ 18112 16 (by decide +kernel)
theorem Check070.part18128 : Interval test 18128 18144 :=
  interval_of_check _ 18128 16 (by decide +kernel)
theorem Check070.part18144 : Interval test 18144 18160 :=
  interval_of_check _ 18144 16 (by decide +kernel)
theorem Check070.part18160 : Interval test 18160 18176 :=
  interval_of_check _ 18160 16 (by decide +kernel)
theorem Check070.checked : Interval test 17920 18176 :=
  (FiniteChecks.interval_append test 17920 18048 18176
  (FiniteChecks.interval_append test 17920 17984 18048
  (FiniteChecks.interval_append test 17920 17952 17984
  (FiniteChecks.interval_append test 17920 17936 17952
  Check070.part17920
  Check070.part17936)
  (FiniteChecks.interval_append test 17952 17968 17984
  Check070.part17952
  Check070.part17968))
  (FiniteChecks.interval_append test 17984 18016 18048
  (FiniteChecks.interval_append test 17984 18000 18016
  Check070.part17984
  Check070.part18000)
  (FiniteChecks.interval_append test 18016 18032 18048
  Check070.part18016
  Check070.part18032)))
  (FiniteChecks.interval_append test 18048 18112 18176
  (FiniteChecks.interval_append test 18048 18080 18112
  (FiniteChecks.interval_append test 18048 18064 18080
  Check070.part18048
  Check070.part18064)
  (FiniteChecks.interval_append test 18080 18096 18112
  Check070.part18080
  Check070.part18096))
  (FiniteChecks.interval_append test 18112 18144 18176
  (FiniteChecks.interval_append test 18112 18128 18144
  Check070.part18112
  Check070.part18128)
  (FiniteChecks.interval_append test 18144 18160 18176
  Check070.part18144
  Check070.part18160))))
#print axioms Check070.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check071.part18176 : Interval test 18176 18192 :=
  interval_of_check _ 18176 16 (by decide +kernel)
theorem Check071.part18192 : Interval test 18192 18208 :=
  interval_of_check _ 18192 16 (by decide +kernel)
theorem Check071.part18208 : Interval test 18208 18224 :=
  interval_of_check _ 18208 16 (by decide +kernel)
theorem Check071.part18224 : Interval test 18224 18240 :=
  interval_of_check _ 18224 16 (by decide +kernel)
theorem Check071.part18240 : Interval test 18240 18256 :=
  interval_of_check _ 18240 16 (by decide +kernel)
theorem Check071.part18256 : Interval test 18256 18272 :=
  interval_of_check _ 18256 16 (by decide +kernel)
theorem Check071.part18272 : Interval test 18272 18288 :=
  interval_of_check _ 18272 16 (by decide +kernel)
theorem Check071.part18288 : Interval test 18288 18304 :=
  interval_of_check _ 18288 16 (by decide +kernel)
theorem Check071.part18304 : Interval test 18304 18320 :=
  interval_of_check _ 18304 16 (by decide +kernel)
theorem Check071.part18320 : Interval test 18320 18336 :=
  interval_of_check _ 18320 16 (by decide +kernel)
theorem Check071.part18336 : Interval test 18336 18352 :=
  interval_of_check _ 18336 16 (by decide +kernel)
theorem Check071.part18352 : Interval test 18352 18368 :=
  interval_of_check _ 18352 16 (by decide +kernel)
theorem Check071.part18368 : Interval test 18368 18384 :=
  interval_of_check _ 18368 16 (by decide +kernel)
theorem Check071.part18384 : Interval test 18384 18400 :=
  interval_of_check _ 18384 16 (by decide +kernel)
theorem Check071.part18400 : Interval test 18400 18416 :=
  interval_of_check _ 18400 16 (by decide +kernel)
theorem Check071.part18416 : Interval test 18416 18432 :=
  interval_of_check _ 18416 16 (by decide +kernel)
theorem Check071.checked : Interval test 18176 18432 :=
  (FiniteChecks.interval_append test 18176 18304 18432
  (FiniteChecks.interval_append test 18176 18240 18304
  (FiniteChecks.interval_append test 18176 18208 18240
  (FiniteChecks.interval_append test 18176 18192 18208
  Check071.part18176
  Check071.part18192)
  (FiniteChecks.interval_append test 18208 18224 18240
  Check071.part18208
  Check071.part18224))
  (FiniteChecks.interval_append test 18240 18272 18304
  (FiniteChecks.interval_append test 18240 18256 18272
  Check071.part18240
  Check071.part18256)
  (FiniteChecks.interval_append test 18272 18288 18304
  Check071.part18272
  Check071.part18288)))
  (FiniteChecks.interval_append test 18304 18368 18432
  (FiniteChecks.interval_append test 18304 18336 18368
  (FiniteChecks.interval_append test 18304 18320 18336
  Check071.part18304
  Check071.part18320)
  (FiniteChecks.interval_append test 18336 18352 18368
  Check071.part18336
  Check071.part18352))
  (FiniteChecks.interval_append test 18368 18400 18432
  (FiniteChecks.interval_append test 18368 18384 18400
  Check071.part18368
  Check071.part18384)
  (FiniteChecks.interval_append test 18400 18416 18432
  Check071.part18400
  Check071.part18416))))
#print axioms Check071.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check072.part18432 : Interval test 18432 18448 :=
  interval_of_check _ 18432 16 (by decide +kernel)
theorem Check072.part18448 : Interval test 18448 18464 :=
  interval_of_check _ 18448 16 (by decide +kernel)
theorem Check072.part18464 : Interval test 18464 18480 :=
  interval_of_check _ 18464 16 (by decide +kernel)
theorem Check072.part18480 : Interval test 18480 18496 :=
  interval_of_check _ 18480 16 (by decide +kernel)
theorem Check072.part18496 : Interval test 18496 18512 :=
  interval_of_check _ 18496 16 (by decide +kernel)
theorem Check072.part18512 : Interval test 18512 18528 :=
  interval_of_check _ 18512 16 (by decide +kernel)
theorem Check072.part18528 : Interval test 18528 18544 :=
  interval_of_check _ 18528 16 (by decide +kernel)
theorem Check072.part18544 : Interval test 18544 18560 :=
  interval_of_check _ 18544 16 (by decide +kernel)
theorem Check072.part18560 : Interval test 18560 18576 :=
  interval_of_check _ 18560 16 (by decide +kernel)
theorem Check072.part18576 : Interval test 18576 18592 :=
  interval_of_check _ 18576 16 (by decide +kernel)
theorem Check072.part18592 : Interval test 18592 18608 :=
  interval_of_check _ 18592 16 (by decide +kernel)
theorem Check072.part18608 : Interval test 18608 18624 :=
  interval_of_check _ 18608 16 (by decide +kernel)
theorem Check072.part18624 : Interval test 18624 18640 :=
  interval_of_check _ 18624 16 (by decide +kernel)
theorem Check072.part18640 : Interval test 18640 18656 :=
  interval_of_check _ 18640 16 (by decide +kernel)
theorem Check072.part18656 : Interval test 18656 18672 :=
  interval_of_check _ 18656 16 (by decide +kernel)
theorem Check072.part18672 : Interval test 18672 18688 :=
  interval_of_check _ 18672 16 (by decide +kernel)
theorem Check072.checked : Interval test 18432 18688 :=
  (FiniteChecks.interval_append test 18432 18560 18688
  (FiniteChecks.interval_append test 18432 18496 18560
  (FiniteChecks.interval_append test 18432 18464 18496
  (FiniteChecks.interval_append test 18432 18448 18464
  Check072.part18432
  Check072.part18448)
  (FiniteChecks.interval_append test 18464 18480 18496
  Check072.part18464
  Check072.part18480))
  (FiniteChecks.interval_append test 18496 18528 18560
  (FiniteChecks.interval_append test 18496 18512 18528
  Check072.part18496
  Check072.part18512)
  (FiniteChecks.interval_append test 18528 18544 18560
  Check072.part18528
  Check072.part18544)))
  (FiniteChecks.interval_append test 18560 18624 18688
  (FiniteChecks.interval_append test 18560 18592 18624
  (FiniteChecks.interval_append test 18560 18576 18592
  Check072.part18560
  Check072.part18576)
  (FiniteChecks.interval_append test 18592 18608 18624
  Check072.part18592
  Check072.part18608))
  (FiniteChecks.interval_append test 18624 18656 18688
  (FiniteChecks.interval_append test 18624 18640 18656
  Check072.part18624
  Check072.part18640)
  (FiniteChecks.interval_append test 18656 18672 18688
  Check072.part18656
  Check072.part18672))))
#print axioms Check072.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check073.part18688 : Interval test 18688 18704 :=
  interval_of_check _ 18688 16 (by decide +kernel)
theorem Check073.part18704 : Interval test 18704 18720 :=
  interval_of_check _ 18704 16 (by decide +kernel)
theorem Check073.part18720 : Interval test 18720 18736 :=
  interval_of_check _ 18720 16 (by decide +kernel)
theorem Check073.part18736 : Interval test 18736 18752 :=
  interval_of_check _ 18736 16 (by decide +kernel)
theorem Check073.part18752 : Interval test 18752 18768 :=
  interval_of_check _ 18752 16 (by decide +kernel)
theorem Check073.part18768 : Interval test 18768 18784 :=
  interval_of_check _ 18768 16 (by decide +kernel)
theorem Check073.part18784 : Interval test 18784 18800 :=
  interval_of_check _ 18784 16 (by decide +kernel)
theorem Check073.part18800 : Interval test 18800 18816 :=
  interval_of_check _ 18800 16 (by decide +kernel)
theorem Check073.part18816 : Interval test 18816 18832 :=
  interval_of_check _ 18816 16 (by decide +kernel)
theorem Check073.part18832 : Interval test 18832 18848 :=
  interval_of_check _ 18832 16 (by decide +kernel)
theorem Check073.part18848 : Interval test 18848 18864 :=
  interval_of_check _ 18848 16 (by decide +kernel)
theorem Check073.part18864 : Interval test 18864 18880 :=
  interval_of_check _ 18864 16 (by decide +kernel)
theorem Check073.part18880 : Interval test 18880 18896 :=
  interval_of_check _ 18880 16 (by decide +kernel)
theorem Check073.part18896 : Interval test 18896 18912 :=
  interval_of_check _ 18896 16 (by decide +kernel)
theorem Check073.part18912 : Interval test 18912 18928 :=
  interval_of_check _ 18912 16 (by decide +kernel)
theorem Check073.part18928 : Interval test 18928 18944 :=
  interval_of_check _ 18928 16 (by decide +kernel)
theorem Check073.checked : Interval test 18688 18944 :=
  (FiniteChecks.interval_append test 18688 18816 18944
  (FiniteChecks.interval_append test 18688 18752 18816
  (FiniteChecks.interval_append test 18688 18720 18752
  (FiniteChecks.interval_append test 18688 18704 18720
  Check073.part18688
  Check073.part18704)
  (FiniteChecks.interval_append test 18720 18736 18752
  Check073.part18720
  Check073.part18736))
  (FiniteChecks.interval_append test 18752 18784 18816
  (FiniteChecks.interval_append test 18752 18768 18784
  Check073.part18752
  Check073.part18768)
  (FiniteChecks.interval_append test 18784 18800 18816
  Check073.part18784
  Check073.part18800)))
  (FiniteChecks.interval_append test 18816 18880 18944
  (FiniteChecks.interval_append test 18816 18848 18880
  (FiniteChecks.interval_append test 18816 18832 18848
  Check073.part18816
  Check073.part18832)
  (FiniteChecks.interval_append test 18848 18864 18880
  Check073.part18848
  Check073.part18864))
  (FiniteChecks.interval_append test 18880 18912 18944
  (FiniteChecks.interval_append test 18880 18896 18912
  Check073.part18880
  Check073.part18896)
  (FiniteChecks.interval_append test 18912 18928 18944
  Check073.part18912
  Check073.part18928))))
#print axioms Check073.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check074.part18944 : Interval test 18944 18960 :=
  interval_of_check _ 18944 16 (by decide +kernel)
theorem Check074.part18960 : Interval test 18960 18976 :=
  interval_of_check _ 18960 16 (by decide +kernel)
theorem Check074.part18976 : Interval test 18976 18992 :=
  interval_of_check _ 18976 16 (by decide +kernel)
theorem Check074.part18992 : Interval test 18992 19008 :=
  interval_of_check _ 18992 16 (by decide +kernel)
theorem Check074.part19008 : Interval test 19008 19024 :=
  interval_of_check _ 19008 16 (by decide +kernel)
theorem Check074.part19024 : Interval test 19024 19040 :=
  interval_of_check _ 19024 16 (by decide +kernel)
theorem Check074.part19040 : Interval test 19040 19056 :=
  interval_of_check _ 19040 16 (by decide +kernel)
theorem Check074.part19056 : Interval test 19056 19072 :=
  interval_of_check _ 19056 16 (by decide +kernel)
theorem Check074.part19072 : Interval test 19072 19088 :=
  interval_of_check _ 19072 16 (by decide +kernel)
theorem Check074.part19088 : Interval test 19088 19104 :=
  interval_of_check _ 19088 16 (by decide +kernel)
theorem Check074.part19104 : Interval test 19104 19120 :=
  interval_of_check _ 19104 16 (by decide +kernel)
theorem Check074.part19120 : Interval test 19120 19136 :=
  interval_of_check _ 19120 16 (by decide +kernel)
theorem Check074.part19136 : Interval test 19136 19152 :=
  interval_of_check _ 19136 16 (by decide +kernel)
theorem Check074.part19152 : Interval test 19152 19168 :=
  interval_of_check _ 19152 16 (by decide +kernel)
theorem Check074.part19168 : Interval test 19168 19184 :=
  interval_of_check _ 19168 16 (by decide +kernel)
theorem Check074.part19184 : Interval test 19184 19200 :=
  interval_of_check _ 19184 16 (by decide +kernel)
theorem Check074.checked : Interval test 18944 19200 :=
  (FiniteChecks.interval_append test 18944 19072 19200
  (FiniteChecks.interval_append test 18944 19008 19072
  (FiniteChecks.interval_append test 18944 18976 19008
  (FiniteChecks.interval_append test 18944 18960 18976
  Check074.part18944
  Check074.part18960)
  (FiniteChecks.interval_append test 18976 18992 19008
  Check074.part18976
  Check074.part18992))
  (FiniteChecks.interval_append test 19008 19040 19072
  (FiniteChecks.interval_append test 19008 19024 19040
  Check074.part19008
  Check074.part19024)
  (FiniteChecks.interval_append test 19040 19056 19072
  Check074.part19040
  Check074.part19056)))
  (FiniteChecks.interval_append test 19072 19136 19200
  (FiniteChecks.interval_append test 19072 19104 19136
  (FiniteChecks.interval_append test 19072 19088 19104
  Check074.part19072
  Check074.part19088)
  (FiniteChecks.interval_append test 19104 19120 19136
  Check074.part19104
  Check074.part19120))
  (FiniteChecks.interval_append test 19136 19168 19200
  (FiniteChecks.interval_append test 19136 19152 19168
  Check074.part19136
  Check074.part19152)
  (FiniteChecks.interval_append test 19168 19184 19200
  Check074.part19168
  Check074.part19184))))
#print axioms Check074.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check075.part19200 : Interval test 19200 19216 :=
  interval_of_check _ 19200 16 (by decide +kernel)
theorem Check075.part19216 : Interval test 19216 19232 :=
  interval_of_check _ 19216 16 (by decide +kernel)
theorem Check075.part19232 : Interval test 19232 19248 :=
  interval_of_check _ 19232 16 (by decide +kernel)
theorem Check075.part19248 : Interval test 19248 19264 :=
  interval_of_check _ 19248 16 (by decide +kernel)
theorem Check075.part19264 : Interval test 19264 19280 :=
  interval_of_check _ 19264 16 (by decide +kernel)
theorem Check075.part19280 : Interval test 19280 19296 :=
  interval_of_check _ 19280 16 (by decide +kernel)
theorem Check075.part19296 : Interval test 19296 19312 :=
  interval_of_check _ 19296 16 (by decide +kernel)
theorem Check075.part19312 : Interval test 19312 19328 :=
  interval_of_check _ 19312 16 (by decide +kernel)
theorem Check075.part19328 : Interval test 19328 19344 :=
  interval_of_check _ 19328 16 (by decide +kernel)
theorem Check075.part19344 : Interval test 19344 19360 :=
  interval_of_check _ 19344 16 (by decide +kernel)
theorem Check075.part19360 : Interval test 19360 19376 :=
  interval_of_check _ 19360 16 (by decide +kernel)
theorem Check075.part19376 : Interval test 19376 19392 :=
  interval_of_check _ 19376 16 (by decide +kernel)
theorem Check075.part19392 : Interval test 19392 19408 :=
  interval_of_check _ 19392 16 (by decide +kernel)
theorem Check075.part19408 : Interval test 19408 19424 :=
  interval_of_check _ 19408 16 (by decide +kernel)
theorem Check075.part19424 : Interval test 19424 19440 :=
  interval_of_check _ 19424 16 (by decide +kernel)
theorem Check075.part19440 : Interval test 19440 19456 :=
  interval_of_check _ 19440 16 (by decide +kernel)
theorem Check075.checked : Interval test 19200 19456 :=
  (FiniteChecks.interval_append test 19200 19328 19456
  (FiniteChecks.interval_append test 19200 19264 19328
  (FiniteChecks.interval_append test 19200 19232 19264
  (FiniteChecks.interval_append test 19200 19216 19232
  Check075.part19200
  Check075.part19216)
  (FiniteChecks.interval_append test 19232 19248 19264
  Check075.part19232
  Check075.part19248))
  (FiniteChecks.interval_append test 19264 19296 19328
  (FiniteChecks.interval_append test 19264 19280 19296
  Check075.part19264
  Check075.part19280)
  (FiniteChecks.interval_append test 19296 19312 19328
  Check075.part19296
  Check075.part19312)))
  (FiniteChecks.interval_append test 19328 19392 19456
  (FiniteChecks.interval_append test 19328 19360 19392
  (FiniteChecks.interval_append test 19328 19344 19360
  Check075.part19328
  Check075.part19344)
  (FiniteChecks.interval_append test 19360 19376 19392
  Check075.part19360
  Check075.part19376))
  (FiniteChecks.interval_append test 19392 19424 19456
  (FiniteChecks.interval_append test 19392 19408 19424
  Check075.part19392
  Check075.part19408)
  (FiniteChecks.interval_append test 19424 19440 19456
  Check075.part19424
  Check075.part19440))))
#print axioms Check075.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check076.part19456 : Interval test 19456 19472 :=
  interval_of_check _ 19456 16 (by decide +kernel)
theorem Check076.part19472 : Interval test 19472 19488 :=
  interval_of_check _ 19472 16 (by decide +kernel)
theorem Check076.part19488 : Interval test 19488 19504 :=
  interval_of_check _ 19488 16 (by decide +kernel)
theorem Check076.part19504 : Interval test 19504 19520 :=
  interval_of_check _ 19504 16 (by decide +kernel)
theorem Check076.part19520 : Interval test 19520 19536 :=
  interval_of_check _ 19520 16 (by decide +kernel)
theorem Check076.part19536 : Interval test 19536 19552 :=
  interval_of_check _ 19536 16 (by decide +kernel)
theorem Check076.part19552 : Interval test 19552 19568 :=
  interval_of_check _ 19552 16 (by decide +kernel)
theorem Check076.part19568 : Interval test 19568 19584 :=
  interval_of_check _ 19568 16 (by decide +kernel)
theorem Check076.part19584 : Interval test 19584 19600 :=
  interval_of_check _ 19584 16 (by decide +kernel)
theorem Check076.part19600 : Interval test 19600 19616 :=
  interval_of_check _ 19600 16 (by decide +kernel)
theorem Check076.part19616 : Interval test 19616 19632 :=
  interval_of_check _ 19616 16 (by decide +kernel)
theorem Check076.part19632 : Interval test 19632 19648 :=
  interval_of_check _ 19632 16 (by decide +kernel)
theorem Check076.part19648 : Interval test 19648 19664 :=
  interval_of_check _ 19648 16 (by decide +kernel)
theorem Check076.part19664 : Interval test 19664 19680 :=
  interval_of_check _ 19664 16 (by decide +kernel)
theorem Check076.part19680 : Interval test 19680 19696 :=
  interval_of_check _ 19680 16 (by decide +kernel)
theorem Check076.part19696 : Interval test 19696 19712 :=
  interval_of_check _ 19696 16 (by decide +kernel)
theorem Check076.checked : Interval test 19456 19712 :=
  (FiniteChecks.interval_append test 19456 19584 19712
  (FiniteChecks.interval_append test 19456 19520 19584
  (FiniteChecks.interval_append test 19456 19488 19520
  (FiniteChecks.interval_append test 19456 19472 19488
  Check076.part19456
  Check076.part19472)
  (FiniteChecks.interval_append test 19488 19504 19520
  Check076.part19488
  Check076.part19504))
  (FiniteChecks.interval_append test 19520 19552 19584
  (FiniteChecks.interval_append test 19520 19536 19552
  Check076.part19520
  Check076.part19536)
  (FiniteChecks.interval_append test 19552 19568 19584
  Check076.part19552
  Check076.part19568)))
  (FiniteChecks.interval_append test 19584 19648 19712
  (FiniteChecks.interval_append test 19584 19616 19648
  (FiniteChecks.interval_append test 19584 19600 19616
  Check076.part19584
  Check076.part19600)
  (FiniteChecks.interval_append test 19616 19632 19648
  Check076.part19616
  Check076.part19632))
  (FiniteChecks.interval_append test 19648 19680 19712
  (FiniteChecks.interval_append test 19648 19664 19680
  Check076.part19648
  Check076.part19664)
  (FiniteChecks.interval_append test 19680 19696 19712
  Check076.part19680
  Check076.part19696))))
#print axioms Check076.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check077.part19712 : Interval test 19712 19728 :=
  interval_of_check _ 19712 16 (by decide +kernel)
theorem Check077.part19728 : Interval test 19728 19744 :=
  interval_of_check _ 19728 16 (by decide +kernel)
theorem Check077.part19744 : Interval test 19744 19760 :=
  interval_of_check _ 19744 16 (by decide +kernel)
theorem Check077.part19760 : Interval test 19760 19776 :=
  interval_of_check _ 19760 16 (by decide +kernel)
theorem Check077.part19776 : Interval test 19776 19792 :=
  interval_of_check _ 19776 16 (by decide +kernel)
theorem Check077.part19792 : Interval test 19792 19808 :=
  interval_of_check _ 19792 16 (by decide +kernel)
theorem Check077.part19808 : Interval test 19808 19824 :=
  interval_of_check _ 19808 16 (by decide +kernel)
theorem Check077.part19824 : Interval test 19824 19840 :=
  interval_of_check _ 19824 16 (by decide +kernel)
theorem Check077.part19840 : Interval test 19840 19856 :=
  interval_of_check _ 19840 16 (by decide +kernel)
theorem Check077.part19856 : Interval test 19856 19872 :=
  interval_of_check _ 19856 16 (by decide +kernel)
theorem Check077.part19872 : Interval test 19872 19888 :=
  interval_of_check _ 19872 16 (by decide +kernel)
theorem Check077.part19888 : Interval test 19888 19904 :=
  interval_of_check _ 19888 16 (by decide +kernel)
theorem Check077.part19904 : Interval test 19904 19920 :=
  interval_of_check _ 19904 16 (by decide +kernel)
theorem Check077.part19920 : Interval test 19920 19936 :=
  interval_of_check _ 19920 16 (by decide +kernel)
theorem Check077.part19936 : Interval test 19936 19952 :=
  interval_of_check _ 19936 16 (by decide +kernel)
theorem Check077.part19952 : Interval test 19952 19968 :=
  interval_of_check _ 19952 16 (by decide +kernel)
theorem Check077.checked : Interval test 19712 19968 :=
  (FiniteChecks.interval_append test 19712 19840 19968
  (FiniteChecks.interval_append test 19712 19776 19840
  (FiniteChecks.interval_append test 19712 19744 19776
  (FiniteChecks.interval_append test 19712 19728 19744
  Check077.part19712
  Check077.part19728)
  (FiniteChecks.interval_append test 19744 19760 19776
  Check077.part19744
  Check077.part19760))
  (FiniteChecks.interval_append test 19776 19808 19840
  (FiniteChecks.interval_append test 19776 19792 19808
  Check077.part19776
  Check077.part19792)
  (FiniteChecks.interval_append test 19808 19824 19840
  Check077.part19808
  Check077.part19824)))
  (FiniteChecks.interval_append test 19840 19904 19968
  (FiniteChecks.interval_append test 19840 19872 19904
  (FiniteChecks.interval_append test 19840 19856 19872
  Check077.part19840
  Check077.part19856)
  (FiniteChecks.interval_append test 19872 19888 19904
  Check077.part19872
  Check077.part19888))
  (FiniteChecks.interval_append test 19904 19936 19968
  (FiniteChecks.interval_append test 19904 19920 19936
  Check077.part19904
  Check077.part19920)
  (FiniteChecks.interval_append test 19936 19952 19968
  Check077.part19936
  Check077.part19952))))
#print axioms Check077.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check078.part19968 : Interval test 19968 19984 :=
  interval_of_check _ 19968 16 (by decide +kernel)
theorem Check078.part19984 : Interval test 19984 20000 :=
  interval_of_check _ 19984 16 (by decide +kernel)
theorem Check078.part20000 : Interval test 20000 20016 :=
  interval_of_check _ 20000 16 (by decide +kernel)
theorem Check078.part20016 : Interval test 20016 20032 :=
  interval_of_check _ 20016 16 (by decide +kernel)
theorem Check078.part20032 : Interval test 20032 20048 :=
  interval_of_check _ 20032 16 (by decide +kernel)
theorem Check078.part20048 : Interval test 20048 20064 :=
  interval_of_check _ 20048 16 (by decide +kernel)
theorem Check078.part20064 : Interval test 20064 20080 :=
  interval_of_check _ 20064 16 (by decide +kernel)
theorem Check078.part20080 : Interval test 20080 20096 :=
  interval_of_check _ 20080 16 (by decide +kernel)
theorem Check078.part20096 : Interval test 20096 20112 :=
  interval_of_check _ 20096 16 (by decide +kernel)
theorem Check078.part20112 : Interval test 20112 20128 :=
  interval_of_check _ 20112 16 (by decide +kernel)
theorem Check078.part20128 : Interval test 20128 20144 :=
  interval_of_check _ 20128 16 (by decide +kernel)
theorem Check078.part20144 : Interval test 20144 20160 :=
  interval_of_check _ 20144 16 (by decide +kernel)
theorem Check078.part20160 : Interval test 20160 20176 :=
  interval_of_check _ 20160 16 (by decide +kernel)
theorem Check078.part20176 : Interval test 20176 20192 :=
  interval_of_check _ 20176 16 (by decide +kernel)
theorem Check078.part20192 : Interval test 20192 20208 :=
  interval_of_check _ 20192 16 (by decide +kernel)
theorem Check078.part20208 : Interval test 20208 20224 :=
  interval_of_check _ 20208 16 (by decide +kernel)
theorem Check078.checked : Interval test 19968 20224 :=
  (FiniteChecks.interval_append test 19968 20096 20224
  (FiniteChecks.interval_append test 19968 20032 20096
  (FiniteChecks.interval_append test 19968 20000 20032
  (FiniteChecks.interval_append test 19968 19984 20000
  Check078.part19968
  Check078.part19984)
  (FiniteChecks.interval_append test 20000 20016 20032
  Check078.part20000
  Check078.part20016))
  (FiniteChecks.interval_append test 20032 20064 20096
  (FiniteChecks.interval_append test 20032 20048 20064
  Check078.part20032
  Check078.part20048)
  (FiniteChecks.interval_append test 20064 20080 20096
  Check078.part20064
  Check078.part20080)))
  (FiniteChecks.interval_append test 20096 20160 20224
  (FiniteChecks.interval_append test 20096 20128 20160
  (FiniteChecks.interval_append test 20096 20112 20128
  Check078.part20096
  Check078.part20112)
  (FiniteChecks.interval_append test 20128 20144 20160
  Check078.part20128
  Check078.part20144))
  (FiniteChecks.interval_append test 20160 20192 20224
  (FiniteChecks.interval_append test 20160 20176 20192
  Check078.part20160
  Check078.part20176)
  (FiniteChecks.interval_append test 20192 20208 20224
  Check078.part20192
  Check078.part20208))))
#print axioms Check078.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check079.part20224 : Interval test 20224 20240 :=
  interval_of_check _ 20224 16 (by decide +kernel)
theorem Check079.part20240 : Interval test 20240 20256 :=
  interval_of_check _ 20240 16 (by decide +kernel)
theorem Check079.part20256 : Interval test 20256 20272 :=
  interval_of_check _ 20256 16 (by decide +kernel)
theorem Check079.part20272 : Interval test 20272 20288 :=
  interval_of_check _ 20272 16 (by decide +kernel)
theorem Check079.part20288 : Interval test 20288 20304 :=
  interval_of_check _ 20288 16 (by decide +kernel)
theorem Check079.part20304 : Interval test 20304 20320 :=
  interval_of_check _ 20304 16 (by decide +kernel)
theorem Check079.part20320 : Interval test 20320 20336 :=
  interval_of_check _ 20320 16 (by decide +kernel)
theorem Check079.part20336 : Interval test 20336 20352 :=
  interval_of_check _ 20336 16 (by decide +kernel)
theorem Check079.part20352 : Interval test 20352 20368 :=
  interval_of_check _ 20352 16 (by decide +kernel)
theorem Check079.part20368 : Interval test 20368 20384 :=
  interval_of_check _ 20368 16 (by decide +kernel)
theorem Check079.part20384 : Interval test 20384 20400 :=
  interval_of_check _ 20384 16 (by decide +kernel)
theorem Check079.part20400 : Interval test 20400 20416 :=
  interval_of_check _ 20400 16 (by decide +kernel)
theorem Check079.part20416 : Interval test 20416 20432 :=
  interval_of_check _ 20416 16 (by decide +kernel)
theorem Check079.part20432 : Interval test 20432 20448 :=
  interval_of_check _ 20432 16 (by decide +kernel)
theorem Check079.part20448 : Interval test 20448 20464 :=
  interval_of_check _ 20448 16 (by decide +kernel)
theorem Check079.part20464 : Interval test 20464 20480 :=
  interval_of_check _ 20464 16 (by decide +kernel)
theorem Check079.checked : Interval test 20224 20480 :=
  (FiniteChecks.interval_append test 20224 20352 20480
  (FiniteChecks.interval_append test 20224 20288 20352
  (FiniteChecks.interval_append test 20224 20256 20288
  (FiniteChecks.interval_append test 20224 20240 20256
  Check079.part20224
  Check079.part20240)
  (FiniteChecks.interval_append test 20256 20272 20288
  Check079.part20256
  Check079.part20272))
  (FiniteChecks.interval_append test 20288 20320 20352
  (FiniteChecks.interval_append test 20288 20304 20320
  Check079.part20288
  Check079.part20304)
  (FiniteChecks.interval_append test 20320 20336 20352
  Check079.part20320
  Check079.part20336)))
  (FiniteChecks.interval_append test 20352 20416 20480
  (FiniteChecks.interval_append test 20352 20384 20416
  (FiniteChecks.interval_append test 20352 20368 20384
  Check079.part20352
  Check079.part20368)
  (FiniteChecks.interval_append test 20384 20400 20416
  Check079.part20384
  Check079.part20400))
  (FiniteChecks.interval_append test 20416 20448 20480
  (FiniteChecks.interval_append test 20416 20432 20448
  Check079.part20416
  Check079.part20432)
  (FiniteChecks.interval_append test 20448 20464 20480
  Check079.part20448
  Check079.part20464))))
#print axioms Check079.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
