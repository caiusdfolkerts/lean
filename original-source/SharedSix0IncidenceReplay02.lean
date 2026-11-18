module
prelude
public import SharedSix0IncidenceData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check040.part10240 : Interval test 10240 10256 :=
  interval_of_check _ 10240 16 (by decide +kernel)
theorem Check040.part10256 : Interval test 10256 10272 :=
  interval_of_check _ 10256 16 (by decide +kernel)
theorem Check040.part10272 : Interval test 10272 10288 :=
  interval_of_check _ 10272 16 (by decide +kernel)
theorem Check040.part10288 : Interval test 10288 10304 :=
  interval_of_check _ 10288 16 (by decide +kernel)
theorem Check040.part10304 : Interval test 10304 10320 :=
  interval_of_check _ 10304 16 (by decide +kernel)
theorem Check040.part10320 : Interval test 10320 10336 :=
  interval_of_check _ 10320 16 (by decide +kernel)
theorem Check040.part10336 : Interval test 10336 10352 :=
  interval_of_check _ 10336 16 (by decide +kernel)
theorem Check040.part10352 : Interval test 10352 10368 :=
  interval_of_check _ 10352 16 (by decide +kernel)
theorem Check040.part10368 : Interval test 10368 10384 :=
  interval_of_check _ 10368 16 (by decide +kernel)
theorem Check040.part10384 : Interval test 10384 10400 :=
  interval_of_check _ 10384 16 (by decide +kernel)
theorem Check040.part10400 : Interval test 10400 10416 :=
  interval_of_check _ 10400 16 (by decide +kernel)
theorem Check040.part10416 : Interval test 10416 10432 :=
  interval_of_check _ 10416 16 (by decide +kernel)
theorem Check040.part10432 : Interval test 10432 10448 :=
  interval_of_check _ 10432 16 (by decide +kernel)
theorem Check040.part10448 : Interval test 10448 10464 :=
  interval_of_check _ 10448 16 (by decide +kernel)
theorem Check040.part10464 : Interval test 10464 10480 :=
  interval_of_check _ 10464 16 (by decide +kernel)
theorem Check040.part10480 : Interval test 10480 10496 :=
  interval_of_check _ 10480 16 (by decide +kernel)
theorem Check040.checked : Interval test 10240 10496 :=
  (FiniteChecks.interval_append test 10240 10368 10496
  (FiniteChecks.interval_append test 10240 10304 10368
  (FiniteChecks.interval_append test 10240 10272 10304
  (FiniteChecks.interval_append test 10240 10256 10272
  Check040.part10240
  Check040.part10256)
  (FiniteChecks.interval_append test 10272 10288 10304
  Check040.part10272
  Check040.part10288))
  (FiniteChecks.interval_append test 10304 10336 10368
  (FiniteChecks.interval_append test 10304 10320 10336
  Check040.part10304
  Check040.part10320)
  (FiniteChecks.interval_append test 10336 10352 10368
  Check040.part10336
  Check040.part10352)))
  (FiniteChecks.interval_append test 10368 10432 10496
  (FiniteChecks.interval_append test 10368 10400 10432
  (FiniteChecks.interval_append test 10368 10384 10400
  Check040.part10368
  Check040.part10384)
  (FiniteChecks.interval_append test 10400 10416 10432
  Check040.part10400
  Check040.part10416))
  (FiniteChecks.interval_append test 10432 10464 10496
  (FiniteChecks.interval_append test 10432 10448 10464
  Check040.part10432
  Check040.part10448)
  (FiniteChecks.interval_append test 10464 10480 10496
  Check040.part10464
  Check040.part10480))))
#print axioms Check040.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check041.part10496 : Interval test 10496 10512 :=
  interval_of_check _ 10496 16 (by decide +kernel)
theorem Check041.part10512 : Interval test 10512 10528 :=
  interval_of_check _ 10512 16 (by decide +kernel)
theorem Check041.part10528 : Interval test 10528 10544 :=
  interval_of_check _ 10528 16 (by decide +kernel)
theorem Check041.part10544 : Interval test 10544 10560 :=
  interval_of_check _ 10544 16 (by decide +kernel)
theorem Check041.part10560 : Interval test 10560 10576 :=
  interval_of_check _ 10560 16 (by decide +kernel)
theorem Check041.part10576 : Interval test 10576 10592 :=
  interval_of_check _ 10576 16 (by decide +kernel)
theorem Check041.part10592 : Interval test 10592 10608 :=
  interval_of_check _ 10592 16 (by decide +kernel)
theorem Check041.part10608 : Interval test 10608 10624 :=
  interval_of_check _ 10608 16 (by decide +kernel)
theorem Check041.part10624 : Interval test 10624 10640 :=
  interval_of_check _ 10624 16 (by decide +kernel)
theorem Check041.part10640 : Interval test 10640 10656 :=
  interval_of_check _ 10640 16 (by decide +kernel)
theorem Check041.part10656 : Interval test 10656 10672 :=
  interval_of_check _ 10656 16 (by decide +kernel)
theorem Check041.part10672 : Interval test 10672 10688 :=
  interval_of_check _ 10672 16 (by decide +kernel)
theorem Check041.part10688 : Interval test 10688 10704 :=
  interval_of_check _ 10688 16 (by decide +kernel)
theorem Check041.part10704 : Interval test 10704 10720 :=
  interval_of_check _ 10704 16 (by decide +kernel)
theorem Check041.part10720 : Interval test 10720 10736 :=
  interval_of_check _ 10720 16 (by decide +kernel)
theorem Check041.part10736 : Interval test 10736 10752 :=
  interval_of_check _ 10736 16 (by decide +kernel)
theorem Check041.checked : Interval test 10496 10752 :=
  (FiniteChecks.interval_append test 10496 10624 10752
  (FiniteChecks.interval_append test 10496 10560 10624
  (FiniteChecks.interval_append test 10496 10528 10560
  (FiniteChecks.interval_append test 10496 10512 10528
  Check041.part10496
  Check041.part10512)
  (FiniteChecks.interval_append test 10528 10544 10560
  Check041.part10528
  Check041.part10544))
  (FiniteChecks.interval_append test 10560 10592 10624
  (FiniteChecks.interval_append test 10560 10576 10592
  Check041.part10560
  Check041.part10576)
  (FiniteChecks.interval_append test 10592 10608 10624
  Check041.part10592
  Check041.part10608)))
  (FiniteChecks.interval_append test 10624 10688 10752
  (FiniteChecks.interval_append test 10624 10656 10688
  (FiniteChecks.interval_append test 10624 10640 10656
  Check041.part10624
  Check041.part10640)
  (FiniteChecks.interval_append test 10656 10672 10688
  Check041.part10656
  Check041.part10672))
  (FiniteChecks.interval_append test 10688 10720 10752
  (FiniteChecks.interval_append test 10688 10704 10720
  Check041.part10688
  Check041.part10704)
  (FiniteChecks.interval_append test 10720 10736 10752
  Check041.part10720
  Check041.part10736))))
#print axioms Check041.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check042.part10752 : Interval test 10752 10768 :=
  interval_of_check _ 10752 16 (by decide +kernel)
theorem Check042.part10768 : Interval test 10768 10784 :=
  interval_of_check _ 10768 16 (by decide +kernel)
theorem Check042.part10784 : Interval test 10784 10800 :=
  interval_of_check _ 10784 16 (by decide +kernel)
theorem Check042.part10800 : Interval test 10800 10816 :=
  interval_of_check _ 10800 16 (by decide +kernel)
theorem Check042.part10816 : Interval test 10816 10832 :=
  interval_of_check _ 10816 16 (by decide +kernel)
theorem Check042.part10832 : Interval test 10832 10848 :=
  interval_of_check _ 10832 16 (by decide +kernel)
theorem Check042.part10848 : Interval test 10848 10864 :=
  interval_of_check _ 10848 16 (by decide +kernel)
theorem Check042.part10864 : Interval test 10864 10880 :=
  interval_of_check _ 10864 16 (by decide +kernel)
theorem Check042.part10880 : Interval test 10880 10896 :=
  interval_of_check _ 10880 16 (by decide +kernel)
theorem Check042.part10896 : Interval test 10896 10912 :=
  interval_of_check _ 10896 16 (by decide +kernel)
theorem Check042.part10912 : Interval test 10912 10928 :=
  interval_of_check _ 10912 16 (by decide +kernel)
theorem Check042.part10928 : Interval test 10928 10944 :=
  interval_of_check _ 10928 16 (by decide +kernel)
theorem Check042.part10944 : Interval test 10944 10960 :=
  interval_of_check _ 10944 16 (by decide +kernel)
theorem Check042.part10960 : Interval test 10960 10976 :=
  interval_of_check _ 10960 16 (by decide +kernel)
theorem Check042.part10976 : Interval test 10976 10992 :=
  interval_of_check _ 10976 16 (by decide +kernel)
theorem Check042.part10992 : Interval test 10992 11008 :=
  interval_of_check _ 10992 16 (by decide +kernel)
theorem Check042.checked : Interval test 10752 11008 :=
  (FiniteChecks.interval_append test 10752 10880 11008
  (FiniteChecks.interval_append test 10752 10816 10880
  (FiniteChecks.interval_append test 10752 10784 10816
  (FiniteChecks.interval_append test 10752 10768 10784
  Check042.part10752
  Check042.part10768)
  (FiniteChecks.interval_append test 10784 10800 10816
  Check042.part10784
  Check042.part10800))
  (FiniteChecks.interval_append test 10816 10848 10880
  (FiniteChecks.interval_append test 10816 10832 10848
  Check042.part10816
  Check042.part10832)
  (FiniteChecks.interval_append test 10848 10864 10880
  Check042.part10848
  Check042.part10864)))
  (FiniteChecks.interval_append test 10880 10944 11008
  (FiniteChecks.interval_append test 10880 10912 10944
  (FiniteChecks.interval_append test 10880 10896 10912
  Check042.part10880
  Check042.part10896)
  (FiniteChecks.interval_append test 10912 10928 10944
  Check042.part10912
  Check042.part10928))
  (FiniteChecks.interval_append test 10944 10976 11008
  (FiniteChecks.interval_append test 10944 10960 10976
  Check042.part10944
  Check042.part10960)
  (FiniteChecks.interval_append test 10976 10992 11008
  Check042.part10976
  Check042.part10992))))
#print axioms Check042.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check043.part11008 : Interval test 11008 11024 :=
  interval_of_check _ 11008 16 (by decide +kernel)
theorem Check043.part11024 : Interval test 11024 11040 :=
  interval_of_check _ 11024 16 (by decide +kernel)
theorem Check043.part11040 : Interval test 11040 11056 :=
  interval_of_check _ 11040 16 (by decide +kernel)
theorem Check043.part11056 : Interval test 11056 11072 :=
  interval_of_check _ 11056 16 (by decide +kernel)
theorem Check043.part11072 : Interval test 11072 11088 :=
  interval_of_check _ 11072 16 (by decide +kernel)
theorem Check043.part11088 : Interval test 11088 11104 :=
  interval_of_check _ 11088 16 (by decide +kernel)
theorem Check043.part11104 : Interval test 11104 11120 :=
  interval_of_check _ 11104 16 (by decide +kernel)
theorem Check043.part11120 : Interval test 11120 11136 :=
  interval_of_check _ 11120 16 (by decide +kernel)
theorem Check043.part11136 : Interval test 11136 11152 :=
  interval_of_check _ 11136 16 (by decide +kernel)
theorem Check043.part11152 : Interval test 11152 11168 :=
  interval_of_check _ 11152 16 (by decide +kernel)
theorem Check043.part11168 : Interval test 11168 11184 :=
  interval_of_check _ 11168 16 (by decide +kernel)
theorem Check043.part11184 : Interval test 11184 11200 :=
  interval_of_check _ 11184 16 (by decide +kernel)
theorem Check043.part11200 : Interval test 11200 11216 :=
  interval_of_check _ 11200 16 (by decide +kernel)
theorem Check043.part11216 : Interval test 11216 11232 :=
  interval_of_check _ 11216 16 (by decide +kernel)
theorem Check043.part11232 : Interval test 11232 11248 :=
  interval_of_check _ 11232 16 (by decide +kernel)
theorem Check043.part11248 : Interval test 11248 11264 :=
  interval_of_check _ 11248 16 (by decide +kernel)
theorem Check043.checked : Interval test 11008 11264 :=
  (FiniteChecks.interval_append test 11008 11136 11264
  (FiniteChecks.interval_append test 11008 11072 11136
  (FiniteChecks.interval_append test 11008 11040 11072
  (FiniteChecks.interval_append test 11008 11024 11040
  Check043.part11008
  Check043.part11024)
  (FiniteChecks.interval_append test 11040 11056 11072
  Check043.part11040
  Check043.part11056))
  (FiniteChecks.interval_append test 11072 11104 11136
  (FiniteChecks.interval_append test 11072 11088 11104
  Check043.part11072
  Check043.part11088)
  (FiniteChecks.interval_append test 11104 11120 11136
  Check043.part11104
  Check043.part11120)))
  (FiniteChecks.interval_append test 11136 11200 11264
  (FiniteChecks.interval_append test 11136 11168 11200
  (FiniteChecks.interval_append test 11136 11152 11168
  Check043.part11136
  Check043.part11152)
  (FiniteChecks.interval_append test 11168 11184 11200
  Check043.part11168
  Check043.part11184))
  (FiniteChecks.interval_append test 11200 11232 11264
  (FiniteChecks.interval_append test 11200 11216 11232
  Check043.part11200
  Check043.part11216)
  (FiniteChecks.interval_append test 11232 11248 11264
  Check043.part11232
  Check043.part11248))))
#print axioms Check043.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check044.part11264 : Interval test 11264 11280 :=
  interval_of_check _ 11264 16 (by decide +kernel)
theorem Check044.part11280 : Interval test 11280 11296 :=
  interval_of_check _ 11280 16 (by decide +kernel)
theorem Check044.part11296 : Interval test 11296 11312 :=
  interval_of_check _ 11296 16 (by decide +kernel)
theorem Check044.part11312 : Interval test 11312 11328 :=
  interval_of_check _ 11312 16 (by decide +kernel)
theorem Check044.part11328 : Interval test 11328 11344 :=
  interval_of_check _ 11328 16 (by decide +kernel)
theorem Check044.part11344 : Interval test 11344 11360 :=
  interval_of_check _ 11344 16 (by decide +kernel)
theorem Check044.part11360 : Interval test 11360 11376 :=
  interval_of_check _ 11360 16 (by decide +kernel)
theorem Check044.part11376 : Interval test 11376 11392 :=
  interval_of_check _ 11376 16 (by decide +kernel)
theorem Check044.part11392 : Interval test 11392 11408 :=
  interval_of_check _ 11392 16 (by decide +kernel)
theorem Check044.part11408 : Interval test 11408 11424 :=
  interval_of_check _ 11408 16 (by decide +kernel)
theorem Check044.part11424 : Interval test 11424 11440 :=
  interval_of_check _ 11424 16 (by decide +kernel)
theorem Check044.part11440 : Interval test 11440 11456 :=
  interval_of_check _ 11440 16 (by decide +kernel)
theorem Check044.part11456 : Interval test 11456 11472 :=
  interval_of_check _ 11456 16 (by decide +kernel)
theorem Check044.part11472 : Interval test 11472 11488 :=
  interval_of_check _ 11472 16 (by decide +kernel)
theorem Check044.part11488 : Interval test 11488 11504 :=
  interval_of_check _ 11488 16 (by decide +kernel)
theorem Check044.part11504 : Interval test 11504 11520 :=
  interval_of_check _ 11504 16 (by decide +kernel)
theorem Check044.checked : Interval test 11264 11520 :=
  (FiniteChecks.interval_append test 11264 11392 11520
  (FiniteChecks.interval_append test 11264 11328 11392
  (FiniteChecks.interval_append test 11264 11296 11328
  (FiniteChecks.interval_append test 11264 11280 11296
  Check044.part11264
  Check044.part11280)
  (FiniteChecks.interval_append test 11296 11312 11328
  Check044.part11296
  Check044.part11312))
  (FiniteChecks.interval_append test 11328 11360 11392
  (FiniteChecks.interval_append test 11328 11344 11360
  Check044.part11328
  Check044.part11344)
  (FiniteChecks.interval_append test 11360 11376 11392
  Check044.part11360
  Check044.part11376)))
  (FiniteChecks.interval_append test 11392 11456 11520
  (FiniteChecks.interval_append test 11392 11424 11456
  (FiniteChecks.interval_append test 11392 11408 11424
  Check044.part11392
  Check044.part11408)
  (FiniteChecks.interval_append test 11424 11440 11456
  Check044.part11424
  Check044.part11440))
  (FiniteChecks.interval_append test 11456 11488 11520
  (FiniteChecks.interval_append test 11456 11472 11488
  Check044.part11456
  Check044.part11472)
  (FiniteChecks.interval_append test 11488 11504 11520
  Check044.part11488
  Check044.part11504))))
#print axioms Check044.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check045.part11520 : Interval test 11520 11536 :=
  interval_of_check _ 11520 16 (by decide +kernel)
theorem Check045.part11536 : Interval test 11536 11552 :=
  interval_of_check _ 11536 16 (by decide +kernel)
theorem Check045.part11552 : Interval test 11552 11568 :=
  interval_of_check _ 11552 16 (by decide +kernel)
theorem Check045.part11568 : Interval test 11568 11584 :=
  interval_of_check _ 11568 16 (by decide +kernel)
theorem Check045.part11584 : Interval test 11584 11600 :=
  interval_of_check _ 11584 16 (by decide +kernel)
theorem Check045.part11600 : Interval test 11600 11616 :=
  interval_of_check _ 11600 16 (by decide +kernel)
theorem Check045.part11616 : Interval test 11616 11632 :=
  interval_of_check _ 11616 16 (by decide +kernel)
theorem Check045.part11632 : Interval test 11632 11648 :=
  interval_of_check _ 11632 16 (by decide +kernel)
theorem Check045.part11648 : Interval test 11648 11664 :=
  interval_of_check _ 11648 16 (by decide +kernel)
theorem Check045.part11664 : Interval test 11664 11680 :=
  interval_of_check _ 11664 16 (by decide +kernel)
theorem Check045.part11680 : Interval test 11680 11696 :=
  interval_of_check _ 11680 16 (by decide +kernel)
theorem Check045.part11696 : Interval test 11696 11712 :=
  interval_of_check _ 11696 16 (by decide +kernel)
theorem Check045.part11712 : Interval test 11712 11728 :=
  interval_of_check _ 11712 16 (by decide +kernel)
theorem Check045.part11728 : Interval test 11728 11744 :=
  interval_of_check _ 11728 16 (by decide +kernel)
theorem Check045.part11744 : Interval test 11744 11760 :=
  interval_of_check _ 11744 16 (by decide +kernel)
theorem Check045.part11760 : Interval test 11760 11776 :=
  interval_of_check _ 11760 16 (by decide +kernel)
theorem Check045.checked : Interval test 11520 11776 :=
  (FiniteChecks.interval_append test 11520 11648 11776
  (FiniteChecks.interval_append test 11520 11584 11648
  (FiniteChecks.interval_append test 11520 11552 11584
  (FiniteChecks.interval_append test 11520 11536 11552
  Check045.part11520
  Check045.part11536)
  (FiniteChecks.interval_append test 11552 11568 11584
  Check045.part11552
  Check045.part11568))
  (FiniteChecks.interval_append test 11584 11616 11648
  (FiniteChecks.interval_append test 11584 11600 11616
  Check045.part11584
  Check045.part11600)
  (FiniteChecks.interval_append test 11616 11632 11648
  Check045.part11616
  Check045.part11632)))
  (FiniteChecks.interval_append test 11648 11712 11776
  (FiniteChecks.interval_append test 11648 11680 11712
  (FiniteChecks.interval_append test 11648 11664 11680
  Check045.part11648
  Check045.part11664)
  (FiniteChecks.interval_append test 11680 11696 11712
  Check045.part11680
  Check045.part11696))
  (FiniteChecks.interval_append test 11712 11744 11776
  (FiniteChecks.interval_append test 11712 11728 11744
  Check045.part11712
  Check045.part11728)
  (FiniteChecks.interval_append test 11744 11760 11776
  Check045.part11744
  Check045.part11760))))
#print axioms Check045.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check046.part11776 : Interval test 11776 11792 :=
  interval_of_check _ 11776 16 (by decide +kernel)
theorem Check046.part11792 : Interval test 11792 11808 :=
  interval_of_check _ 11792 16 (by decide +kernel)
theorem Check046.part11808 : Interval test 11808 11824 :=
  interval_of_check _ 11808 16 (by decide +kernel)
theorem Check046.part11824 : Interval test 11824 11840 :=
  interval_of_check _ 11824 16 (by decide +kernel)
theorem Check046.part11840 : Interval test 11840 11856 :=
  interval_of_check _ 11840 16 (by decide +kernel)
theorem Check046.part11856 : Interval test 11856 11872 :=
  interval_of_check _ 11856 16 (by decide +kernel)
theorem Check046.part11872 : Interval test 11872 11888 :=
  interval_of_check _ 11872 16 (by decide +kernel)
theorem Check046.part11888 : Interval test 11888 11904 :=
  interval_of_check _ 11888 16 (by decide +kernel)
theorem Check046.part11904 : Interval test 11904 11920 :=
  interval_of_check _ 11904 16 (by decide +kernel)
theorem Check046.part11920 : Interval test 11920 11936 :=
  interval_of_check _ 11920 16 (by decide +kernel)
theorem Check046.part11936 : Interval test 11936 11952 :=
  interval_of_check _ 11936 16 (by decide +kernel)
theorem Check046.part11952 : Interval test 11952 11968 :=
  interval_of_check _ 11952 16 (by decide +kernel)
theorem Check046.part11968 : Interval test 11968 11984 :=
  interval_of_check _ 11968 16 (by decide +kernel)
theorem Check046.part11984 : Interval test 11984 12000 :=
  interval_of_check _ 11984 16 (by decide +kernel)
theorem Check046.part12000 : Interval test 12000 12016 :=
  interval_of_check _ 12000 16 (by decide +kernel)
theorem Check046.part12016 : Interval test 12016 12032 :=
  interval_of_check _ 12016 16 (by decide +kernel)
theorem Check046.checked : Interval test 11776 12032 :=
  (FiniteChecks.interval_append test 11776 11904 12032
  (FiniteChecks.interval_append test 11776 11840 11904
  (FiniteChecks.interval_append test 11776 11808 11840
  (FiniteChecks.interval_append test 11776 11792 11808
  Check046.part11776
  Check046.part11792)
  (FiniteChecks.interval_append test 11808 11824 11840
  Check046.part11808
  Check046.part11824))
  (FiniteChecks.interval_append test 11840 11872 11904
  (FiniteChecks.interval_append test 11840 11856 11872
  Check046.part11840
  Check046.part11856)
  (FiniteChecks.interval_append test 11872 11888 11904
  Check046.part11872
  Check046.part11888)))
  (FiniteChecks.interval_append test 11904 11968 12032
  (FiniteChecks.interval_append test 11904 11936 11968
  (FiniteChecks.interval_append test 11904 11920 11936
  Check046.part11904
  Check046.part11920)
  (FiniteChecks.interval_append test 11936 11952 11968
  Check046.part11936
  Check046.part11952))
  (FiniteChecks.interval_append test 11968 12000 12032
  (FiniteChecks.interval_append test 11968 11984 12000
  Check046.part11968
  Check046.part11984)
  (FiniteChecks.interval_append test 12000 12016 12032
  Check046.part12000
  Check046.part12016))))
#print axioms Check046.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check047.part12032 : Interval test 12032 12048 :=
  interval_of_check _ 12032 16 (by decide +kernel)
theorem Check047.part12048 : Interval test 12048 12064 :=
  interval_of_check _ 12048 16 (by decide +kernel)
theorem Check047.part12064 : Interval test 12064 12080 :=
  interval_of_check _ 12064 16 (by decide +kernel)
theorem Check047.part12080 : Interval test 12080 12096 :=
  interval_of_check _ 12080 16 (by decide +kernel)
theorem Check047.part12096 : Interval test 12096 12112 :=
  interval_of_check _ 12096 16 (by decide +kernel)
theorem Check047.part12112 : Interval test 12112 12128 :=
  interval_of_check _ 12112 16 (by decide +kernel)
theorem Check047.part12128 : Interval test 12128 12144 :=
  interval_of_check _ 12128 16 (by decide +kernel)
theorem Check047.part12144 : Interval test 12144 12160 :=
  interval_of_check _ 12144 16 (by decide +kernel)
theorem Check047.part12160 : Interval test 12160 12176 :=
  interval_of_check _ 12160 16 (by decide +kernel)
theorem Check047.part12176 : Interval test 12176 12192 :=
  interval_of_check _ 12176 16 (by decide +kernel)
theorem Check047.part12192 : Interval test 12192 12208 :=
  interval_of_check _ 12192 16 (by decide +kernel)
theorem Check047.part12208 : Interval test 12208 12224 :=
  interval_of_check _ 12208 16 (by decide +kernel)
theorem Check047.part12224 : Interval test 12224 12240 :=
  interval_of_check _ 12224 16 (by decide +kernel)
theorem Check047.part12240 : Interval test 12240 12256 :=
  interval_of_check _ 12240 16 (by decide +kernel)
theorem Check047.part12256 : Interval test 12256 12272 :=
  interval_of_check _ 12256 16 (by decide +kernel)
theorem Check047.part12272 : Interval test 12272 12288 :=
  interval_of_check _ 12272 16 (by decide +kernel)
theorem Check047.checked : Interval test 12032 12288 :=
  (FiniteChecks.interval_append test 12032 12160 12288
  (FiniteChecks.interval_append test 12032 12096 12160
  (FiniteChecks.interval_append test 12032 12064 12096
  (FiniteChecks.interval_append test 12032 12048 12064
  Check047.part12032
  Check047.part12048)
  (FiniteChecks.interval_append test 12064 12080 12096
  Check047.part12064
  Check047.part12080))
  (FiniteChecks.interval_append test 12096 12128 12160
  (FiniteChecks.interval_append test 12096 12112 12128
  Check047.part12096
  Check047.part12112)
  (FiniteChecks.interval_append test 12128 12144 12160
  Check047.part12128
  Check047.part12144)))
  (FiniteChecks.interval_append test 12160 12224 12288
  (FiniteChecks.interval_append test 12160 12192 12224
  (FiniteChecks.interval_append test 12160 12176 12192
  Check047.part12160
  Check047.part12176)
  (FiniteChecks.interval_append test 12192 12208 12224
  Check047.part12192
  Check047.part12208))
  (FiniteChecks.interval_append test 12224 12256 12288
  (FiniteChecks.interval_append test 12224 12240 12256
  Check047.part12224
  Check047.part12240)
  (FiniteChecks.interval_append test 12256 12272 12288
  Check047.part12256
  Check047.part12272))))
#print axioms Check047.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check048.part12288 : Interval test 12288 12304 :=
  interval_of_check _ 12288 16 (by decide +kernel)
theorem Check048.part12304 : Interval test 12304 12320 :=
  interval_of_check _ 12304 16 (by decide +kernel)
theorem Check048.part12320 : Interval test 12320 12336 :=
  interval_of_check _ 12320 16 (by decide +kernel)
theorem Check048.part12336 : Interval test 12336 12352 :=
  interval_of_check _ 12336 16 (by decide +kernel)
theorem Check048.part12352 : Interval test 12352 12368 :=
  interval_of_check _ 12352 16 (by decide +kernel)
theorem Check048.part12368 : Interval test 12368 12384 :=
  interval_of_check _ 12368 16 (by decide +kernel)
theorem Check048.part12384 : Interval test 12384 12400 :=
  interval_of_check _ 12384 16 (by decide +kernel)
theorem Check048.part12400 : Interval test 12400 12416 :=
  interval_of_check _ 12400 16 (by decide +kernel)
theorem Check048.part12416 : Interval test 12416 12432 :=
  interval_of_check _ 12416 16 (by decide +kernel)
theorem Check048.part12432 : Interval test 12432 12448 :=
  interval_of_check _ 12432 16 (by decide +kernel)
theorem Check048.part12448 : Interval test 12448 12464 :=
  interval_of_check _ 12448 16 (by decide +kernel)
theorem Check048.part12464 : Interval test 12464 12480 :=
  interval_of_check _ 12464 16 (by decide +kernel)
theorem Check048.part12480 : Interval test 12480 12496 :=
  interval_of_check _ 12480 16 (by decide +kernel)
theorem Check048.part12496 : Interval test 12496 12512 :=
  interval_of_check _ 12496 16 (by decide +kernel)
theorem Check048.part12512 : Interval test 12512 12528 :=
  interval_of_check _ 12512 16 (by decide +kernel)
theorem Check048.part12528 : Interval test 12528 12544 :=
  interval_of_check _ 12528 16 (by decide +kernel)
theorem Check048.checked : Interval test 12288 12544 :=
  (FiniteChecks.interval_append test 12288 12416 12544
  (FiniteChecks.interval_append test 12288 12352 12416
  (FiniteChecks.interval_append test 12288 12320 12352
  (FiniteChecks.interval_append test 12288 12304 12320
  Check048.part12288
  Check048.part12304)
  (FiniteChecks.interval_append test 12320 12336 12352
  Check048.part12320
  Check048.part12336))
  (FiniteChecks.interval_append test 12352 12384 12416
  (FiniteChecks.interval_append test 12352 12368 12384
  Check048.part12352
  Check048.part12368)
  (FiniteChecks.interval_append test 12384 12400 12416
  Check048.part12384
  Check048.part12400)))
  (FiniteChecks.interval_append test 12416 12480 12544
  (FiniteChecks.interval_append test 12416 12448 12480
  (FiniteChecks.interval_append test 12416 12432 12448
  Check048.part12416
  Check048.part12432)
  (FiniteChecks.interval_append test 12448 12464 12480
  Check048.part12448
  Check048.part12464))
  (FiniteChecks.interval_append test 12480 12512 12544
  (FiniteChecks.interval_append test 12480 12496 12512
  Check048.part12480
  Check048.part12496)
  (FiniteChecks.interval_append test 12512 12528 12544
  Check048.part12512
  Check048.part12528))))
#print axioms Check048.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check049.part12544 : Interval test 12544 12560 :=
  interval_of_check _ 12544 16 (by decide +kernel)
theorem Check049.part12560 : Interval test 12560 12576 :=
  interval_of_check _ 12560 16 (by decide +kernel)
theorem Check049.part12576 : Interval test 12576 12592 :=
  interval_of_check _ 12576 16 (by decide +kernel)
theorem Check049.part12592 : Interval test 12592 12608 :=
  interval_of_check _ 12592 16 (by decide +kernel)
theorem Check049.part12608 : Interval test 12608 12624 :=
  interval_of_check _ 12608 16 (by decide +kernel)
theorem Check049.part12624 : Interval test 12624 12640 :=
  interval_of_check _ 12624 16 (by decide +kernel)
theorem Check049.part12640 : Interval test 12640 12656 :=
  interval_of_check _ 12640 16 (by decide +kernel)
theorem Check049.part12656 : Interval test 12656 12672 :=
  interval_of_check _ 12656 16 (by decide +kernel)
theorem Check049.part12672 : Interval test 12672 12688 :=
  interval_of_check _ 12672 16 (by decide +kernel)
theorem Check049.part12688 : Interval test 12688 12704 :=
  interval_of_check _ 12688 16 (by decide +kernel)
theorem Check049.part12704 : Interval test 12704 12720 :=
  interval_of_check _ 12704 16 (by decide +kernel)
theorem Check049.part12720 : Interval test 12720 12736 :=
  interval_of_check _ 12720 16 (by decide +kernel)
theorem Check049.part12736 : Interval test 12736 12752 :=
  interval_of_check _ 12736 16 (by decide +kernel)
theorem Check049.part12752 : Interval test 12752 12768 :=
  interval_of_check _ 12752 16 (by decide +kernel)
theorem Check049.part12768 : Interval test 12768 12784 :=
  interval_of_check _ 12768 16 (by decide +kernel)
theorem Check049.part12784 : Interval test 12784 12800 :=
  interval_of_check _ 12784 16 (by decide +kernel)
theorem Check049.checked : Interval test 12544 12800 :=
  (FiniteChecks.interval_append test 12544 12672 12800
  (FiniteChecks.interval_append test 12544 12608 12672
  (FiniteChecks.interval_append test 12544 12576 12608
  (FiniteChecks.interval_append test 12544 12560 12576
  Check049.part12544
  Check049.part12560)
  (FiniteChecks.interval_append test 12576 12592 12608
  Check049.part12576
  Check049.part12592))
  (FiniteChecks.interval_append test 12608 12640 12672
  (FiniteChecks.interval_append test 12608 12624 12640
  Check049.part12608
  Check049.part12624)
  (FiniteChecks.interval_append test 12640 12656 12672
  Check049.part12640
  Check049.part12656)))
  (FiniteChecks.interval_append test 12672 12736 12800
  (FiniteChecks.interval_append test 12672 12704 12736
  (FiniteChecks.interval_append test 12672 12688 12704
  Check049.part12672
  Check049.part12688)
  (FiniteChecks.interval_append test 12704 12720 12736
  Check049.part12704
  Check049.part12720))
  (FiniteChecks.interval_append test 12736 12768 12800
  (FiniteChecks.interval_append test 12736 12752 12768
  Check049.part12736
  Check049.part12752)
  (FiniteChecks.interval_append test 12768 12784 12800
  Check049.part12768
  Check049.part12784))))
#print axioms Check049.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check050.part12800 : Interval test 12800 12816 :=
  interval_of_check _ 12800 16 (by decide +kernel)
theorem Check050.part12816 : Interval test 12816 12832 :=
  interval_of_check _ 12816 16 (by decide +kernel)
theorem Check050.part12832 : Interval test 12832 12848 :=
  interval_of_check _ 12832 16 (by decide +kernel)
theorem Check050.part12848 : Interval test 12848 12864 :=
  interval_of_check _ 12848 16 (by decide +kernel)
theorem Check050.part12864 : Interval test 12864 12880 :=
  interval_of_check _ 12864 16 (by decide +kernel)
theorem Check050.part12880 : Interval test 12880 12896 :=
  interval_of_check _ 12880 16 (by decide +kernel)
theorem Check050.part12896 : Interval test 12896 12912 :=
  interval_of_check _ 12896 16 (by decide +kernel)
theorem Check050.part12912 : Interval test 12912 12928 :=
  interval_of_check _ 12912 16 (by decide +kernel)
theorem Check050.part12928 : Interval test 12928 12944 :=
  interval_of_check _ 12928 16 (by decide +kernel)
theorem Check050.part12944 : Interval test 12944 12960 :=
  interval_of_check _ 12944 16 (by decide +kernel)
theorem Check050.part12960 : Interval test 12960 12976 :=
  interval_of_check _ 12960 16 (by decide +kernel)
theorem Check050.part12976 : Interval test 12976 12992 :=
  interval_of_check _ 12976 16 (by decide +kernel)
theorem Check050.part12992 : Interval test 12992 13008 :=
  interval_of_check _ 12992 16 (by decide +kernel)
theorem Check050.part13008 : Interval test 13008 13024 :=
  interval_of_check _ 13008 16 (by decide +kernel)
theorem Check050.part13024 : Interval test 13024 13040 :=
  interval_of_check _ 13024 16 (by decide +kernel)
theorem Check050.part13040 : Interval test 13040 13056 :=
  interval_of_check _ 13040 16 (by decide +kernel)
theorem Check050.checked : Interval test 12800 13056 :=
  (FiniteChecks.interval_append test 12800 12928 13056
  (FiniteChecks.interval_append test 12800 12864 12928
  (FiniteChecks.interval_append test 12800 12832 12864
  (FiniteChecks.interval_append test 12800 12816 12832
  Check050.part12800
  Check050.part12816)
  (FiniteChecks.interval_append test 12832 12848 12864
  Check050.part12832
  Check050.part12848))
  (FiniteChecks.interval_append test 12864 12896 12928
  (FiniteChecks.interval_append test 12864 12880 12896
  Check050.part12864
  Check050.part12880)
  (FiniteChecks.interval_append test 12896 12912 12928
  Check050.part12896
  Check050.part12912)))
  (FiniteChecks.interval_append test 12928 12992 13056
  (FiniteChecks.interval_append test 12928 12960 12992
  (FiniteChecks.interval_append test 12928 12944 12960
  Check050.part12928
  Check050.part12944)
  (FiniteChecks.interval_append test 12960 12976 12992
  Check050.part12960
  Check050.part12976))
  (FiniteChecks.interval_append test 12992 13024 13056
  (FiniteChecks.interval_append test 12992 13008 13024
  Check050.part12992
  Check050.part13008)
  (FiniteChecks.interval_append test 13024 13040 13056
  Check050.part13024
  Check050.part13040))))
#print axioms Check050.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check051.part13056 : Interval test 13056 13072 :=
  interval_of_check _ 13056 16 (by decide +kernel)
theorem Check051.part13072 : Interval test 13072 13088 :=
  interval_of_check _ 13072 16 (by decide +kernel)
theorem Check051.part13088 : Interval test 13088 13104 :=
  interval_of_check _ 13088 16 (by decide +kernel)
theorem Check051.part13104 : Interval test 13104 13120 :=
  interval_of_check _ 13104 16 (by decide +kernel)
theorem Check051.part13120 : Interval test 13120 13136 :=
  interval_of_check _ 13120 16 (by decide +kernel)
theorem Check051.part13136 : Interval test 13136 13152 :=
  interval_of_check _ 13136 16 (by decide +kernel)
theorem Check051.part13152 : Interval test 13152 13168 :=
  interval_of_check _ 13152 16 (by decide +kernel)
theorem Check051.part13168 : Interval test 13168 13184 :=
  interval_of_check _ 13168 16 (by decide +kernel)
theorem Check051.part13184 : Interval test 13184 13200 :=
  interval_of_check _ 13184 16 (by decide +kernel)
theorem Check051.part13200 : Interval test 13200 13216 :=
  interval_of_check _ 13200 16 (by decide +kernel)
theorem Check051.part13216 : Interval test 13216 13232 :=
  interval_of_check _ 13216 16 (by decide +kernel)
theorem Check051.part13232 : Interval test 13232 13248 :=
  interval_of_check _ 13232 16 (by decide +kernel)
theorem Check051.part13248 : Interval test 13248 13264 :=
  interval_of_check _ 13248 16 (by decide +kernel)
theorem Check051.part13264 : Interval test 13264 13280 :=
  interval_of_check _ 13264 16 (by decide +kernel)
theorem Check051.part13280 : Interval test 13280 13296 :=
  interval_of_check _ 13280 16 (by decide +kernel)
theorem Check051.part13296 : Interval test 13296 13312 :=
  interval_of_check _ 13296 16 (by decide +kernel)
theorem Check051.checked : Interval test 13056 13312 :=
  (FiniteChecks.interval_append test 13056 13184 13312
  (FiniteChecks.interval_append test 13056 13120 13184
  (FiniteChecks.interval_append test 13056 13088 13120
  (FiniteChecks.interval_append test 13056 13072 13088
  Check051.part13056
  Check051.part13072)
  (FiniteChecks.interval_append test 13088 13104 13120
  Check051.part13088
  Check051.part13104))
  (FiniteChecks.interval_append test 13120 13152 13184
  (FiniteChecks.interval_append test 13120 13136 13152
  Check051.part13120
  Check051.part13136)
  (FiniteChecks.interval_append test 13152 13168 13184
  Check051.part13152
  Check051.part13168)))
  (FiniteChecks.interval_append test 13184 13248 13312
  (FiniteChecks.interval_append test 13184 13216 13248
  (FiniteChecks.interval_append test 13184 13200 13216
  Check051.part13184
  Check051.part13200)
  (FiniteChecks.interval_append test 13216 13232 13248
  Check051.part13216
  Check051.part13232))
  (FiniteChecks.interval_append test 13248 13280 13312
  (FiniteChecks.interval_append test 13248 13264 13280
  Check051.part13248
  Check051.part13264)
  (FiniteChecks.interval_append test 13280 13296 13312
  Check051.part13280
  Check051.part13296))))
#print axioms Check051.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check052.part13312 : Interval test 13312 13328 :=
  interval_of_check _ 13312 16 (by decide +kernel)
theorem Check052.part13328 : Interval test 13328 13344 :=
  interval_of_check _ 13328 16 (by decide +kernel)
theorem Check052.part13344 : Interval test 13344 13360 :=
  interval_of_check _ 13344 16 (by decide +kernel)
theorem Check052.part13360 : Interval test 13360 13376 :=
  interval_of_check _ 13360 16 (by decide +kernel)
theorem Check052.part13376 : Interval test 13376 13392 :=
  interval_of_check _ 13376 16 (by decide +kernel)
theorem Check052.part13392 : Interval test 13392 13408 :=
  interval_of_check _ 13392 16 (by decide +kernel)
theorem Check052.part13408 : Interval test 13408 13424 :=
  interval_of_check _ 13408 16 (by decide +kernel)
theorem Check052.part13424 : Interval test 13424 13440 :=
  interval_of_check _ 13424 16 (by decide +kernel)
theorem Check052.part13440 : Interval test 13440 13456 :=
  interval_of_check _ 13440 16 (by decide +kernel)
theorem Check052.part13456 : Interval test 13456 13472 :=
  interval_of_check _ 13456 16 (by decide +kernel)
theorem Check052.part13472 : Interval test 13472 13488 :=
  interval_of_check _ 13472 16 (by decide +kernel)
theorem Check052.part13488 : Interval test 13488 13504 :=
  interval_of_check _ 13488 16 (by decide +kernel)
theorem Check052.part13504 : Interval test 13504 13520 :=
  interval_of_check _ 13504 16 (by decide +kernel)
theorem Check052.part13520 : Interval test 13520 13536 :=
  interval_of_check _ 13520 16 (by decide +kernel)
theorem Check052.part13536 : Interval test 13536 13552 :=
  interval_of_check _ 13536 16 (by decide +kernel)
theorem Check052.part13552 : Interval test 13552 13568 :=
  interval_of_check _ 13552 16 (by decide +kernel)
theorem Check052.checked : Interval test 13312 13568 :=
  (FiniteChecks.interval_append test 13312 13440 13568
  (FiniteChecks.interval_append test 13312 13376 13440
  (FiniteChecks.interval_append test 13312 13344 13376
  (FiniteChecks.interval_append test 13312 13328 13344
  Check052.part13312
  Check052.part13328)
  (FiniteChecks.interval_append test 13344 13360 13376
  Check052.part13344
  Check052.part13360))
  (FiniteChecks.interval_append test 13376 13408 13440
  (FiniteChecks.interval_append test 13376 13392 13408
  Check052.part13376
  Check052.part13392)
  (FiniteChecks.interval_append test 13408 13424 13440
  Check052.part13408
  Check052.part13424)))
  (FiniteChecks.interval_append test 13440 13504 13568
  (FiniteChecks.interval_append test 13440 13472 13504
  (FiniteChecks.interval_append test 13440 13456 13472
  Check052.part13440
  Check052.part13456)
  (FiniteChecks.interval_append test 13472 13488 13504
  Check052.part13472
  Check052.part13488))
  (FiniteChecks.interval_append test 13504 13536 13568
  (FiniteChecks.interval_append test 13504 13520 13536
  Check052.part13504
  Check052.part13520)
  (FiniteChecks.interval_append test 13536 13552 13568
  Check052.part13536
  Check052.part13552))))
#print axioms Check052.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check053.part13568 : Interval test 13568 13584 :=
  interval_of_check _ 13568 16 (by decide +kernel)
theorem Check053.part13584 : Interval test 13584 13600 :=
  interval_of_check _ 13584 16 (by decide +kernel)
theorem Check053.part13600 : Interval test 13600 13616 :=
  interval_of_check _ 13600 16 (by decide +kernel)
theorem Check053.part13616 : Interval test 13616 13632 :=
  interval_of_check _ 13616 16 (by decide +kernel)
theorem Check053.part13632 : Interval test 13632 13648 :=
  interval_of_check _ 13632 16 (by decide +kernel)
theorem Check053.part13648 : Interval test 13648 13664 :=
  interval_of_check _ 13648 16 (by decide +kernel)
theorem Check053.part13664 : Interval test 13664 13680 :=
  interval_of_check _ 13664 16 (by decide +kernel)
theorem Check053.part13680 : Interval test 13680 13696 :=
  interval_of_check _ 13680 16 (by decide +kernel)
theorem Check053.part13696 : Interval test 13696 13712 :=
  interval_of_check _ 13696 16 (by decide +kernel)
theorem Check053.part13712 : Interval test 13712 13728 :=
  interval_of_check _ 13712 16 (by decide +kernel)
theorem Check053.part13728 : Interval test 13728 13744 :=
  interval_of_check _ 13728 16 (by decide +kernel)
theorem Check053.part13744 : Interval test 13744 13760 :=
  interval_of_check _ 13744 16 (by decide +kernel)
theorem Check053.part13760 : Interval test 13760 13776 :=
  interval_of_check _ 13760 16 (by decide +kernel)
theorem Check053.part13776 : Interval test 13776 13792 :=
  interval_of_check _ 13776 16 (by decide +kernel)
theorem Check053.part13792 : Interval test 13792 13808 :=
  interval_of_check _ 13792 16 (by decide +kernel)
theorem Check053.part13808 : Interval test 13808 13824 :=
  interval_of_check _ 13808 16 (by decide +kernel)
theorem Check053.checked : Interval test 13568 13824 :=
  (FiniteChecks.interval_append test 13568 13696 13824
  (FiniteChecks.interval_append test 13568 13632 13696
  (FiniteChecks.interval_append test 13568 13600 13632
  (FiniteChecks.interval_append test 13568 13584 13600
  Check053.part13568
  Check053.part13584)
  (FiniteChecks.interval_append test 13600 13616 13632
  Check053.part13600
  Check053.part13616))
  (FiniteChecks.interval_append test 13632 13664 13696
  (FiniteChecks.interval_append test 13632 13648 13664
  Check053.part13632
  Check053.part13648)
  (FiniteChecks.interval_append test 13664 13680 13696
  Check053.part13664
  Check053.part13680)))
  (FiniteChecks.interval_append test 13696 13760 13824
  (FiniteChecks.interval_append test 13696 13728 13760
  (FiniteChecks.interval_append test 13696 13712 13728
  Check053.part13696
  Check053.part13712)
  (FiniteChecks.interval_append test 13728 13744 13760
  Check053.part13728
  Check053.part13744))
  (FiniteChecks.interval_append test 13760 13792 13824
  (FiniteChecks.interval_append test 13760 13776 13792
  Check053.part13760
  Check053.part13776)
  (FiniteChecks.interval_append test 13792 13808 13824
  Check053.part13792
  Check053.part13808))))
#print axioms Check053.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check054.part13824 : Interval test 13824 13840 :=
  interval_of_check _ 13824 16 (by decide +kernel)
theorem Check054.part13840 : Interval test 13840 13856 :=
  interval_of_check _ 13840 16 (by decide +kernel)
theorem Check054.part13856 : Interval test 13856 13872 :=
  interval_of_check _ 13856 16 (by decide +kernel)
theorem Check054.part13872 : Interval test 13872 13888 :=
  interval_of_check _ 13872 16 (by decide +kernel)
theorem Check054.part13888 : Interval test 13888 13904 :=
  interval_of_check _ 13888 16 (by decide +kernel)
theorem Check054.part13904 : Interval test 13904 13920 :=
  interval_of_check _ 13904 16 (by decide +kernel)
theorem Check054.part13920 : Interval test 13920 13936 :=
  interval_of_check _ 13920 16 (by decide +kernel)
theorem Check054.part13936 : Interval test 13936 13952 :=
  interval_of_check _ 13936 16 (by decide +kernel)
theorem Check054.part13952 : Interval test 13952 13968 :=
  interval_of_check _ 13952 16 (by decide +kernel)
theorem Check054.part13968 : Interval test 13968 13984 :=
  interval_of_check _ 13968 16 (by decide +kernel)
theorem Check054.part13984 : Interval test 13984 14000 :=
  interval_of_check _ 13984 16 (by decide +kernel)
theorem Check054.part14000 : Interval test 14000 14016 :=
  interval_of_check _ 14000 16 (by decide +kernel)
theorem Check054.part14016 : Interval test 14016 14032 :=
  interval_of_check _ 14016 16 (by decide +kernel)
theorem Check054.part14032 : Interval test 14032 14048 :=
  interval_of_check _ 14032 16 (by decide +kernel)
theorem Check054.part14048 : Interval test 14048 14064 :=
  interval_of_check _ 14048 16 (by decide +kernel)
theorem Check054.part14064 : Interval test 14064 14080 :=
  interval_of_check _ 14064 16 (by decide +kernel)
theorem Check054.checked : Interval test 13824 14080 :=
  (FiniteChecks.interval_append test 13824 13952 14080
  (FiniteChecks.interval_append test 13824 13888 13952
  (FiniteChecks.interval_append test 13824 13856 13888
  (FiniteChecks.interval_append test 13824 13840 13856
  Check054.part13824
  Check054.part13840)
  (FiniteChecks.interval_append test 13856 13872 13888
  Check054.part13856
  Check054.part13872))
  (FiniteChecks.interval_append test 13888 13920 13952
  (FiniteChecks.interval_append test 13888 13904 13920
  Check054.part13888
  Check054.part13904)
  (FiniteChecks.interval_append test 13920 13936 13952
  Check054.part13920
  Check054.part13936)))
  (FiniteChecks.interval_append test 13952 14016 14080
  (FiniteChecks.interval_append test 13952 13984 14016
  (FiniteChecks.interval_append test 13952 13968 13984
  Check054.part13952
  Check054.part13968)
  (FiniteChecks.interval_append test 13984 14000 14016
  Check054.part13984
  Check054.part14000))
  (FiniteChecks.interval_append test 14016 14048 14080
  (FiniteChecks.interval_append test 14016 14032 14048
  Check054.part14016
  Check054.part14032)
  (FiniteChecks.interval_append test 14048 14064 14080
  Check054.part14048
  Check054.part14064))))
#print axioms Check054.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check055.part14080 : Interval test 14080 14096 :=
  interval_of_check _ 14080 16 (by decide +kernel)
theorem Check055.part14096 : Interval test 14096 14112 :=
  interval_of_check _ 14096 16 (by decide +kernel)
theorem Check055.part14112 : Interval test 14112 14128 :=
  interval_of_check _ 14112 16 (by decide +kernel)
theorem Check055.part14128 : Interval test 14128 14144 :=
  interval_of_check _ 14128 16 (by decide +kernel)
theorem Check055.part14144 : Interval test 14144 14160 :=
  interval_of_check _ 14144 16 (by decide +kernel)
theorem Check055.part14160 : Interval test 14160 14176 :=
  interval_of_check _ 14160 16 (by decide +kernel)
theorem Check055.part14176 : Interval test 14176 14192 :=
  interval_of_check _ 14176 16 (by decide +kernel)
theorem Check055.part14192 : Interval test 14192 14208 :=
  interval_of_check _ 14192 16 (by decide +kernel)
theorem Check055.part14208 : Interval test 14208 14224 :=
  interval_of_check _ 14208 16 (by decide +kernel)
theorem Check055.part14224 : Interval test 14224 14240 :=
  interval_of_check _ 14224 16 (by decide +kernel)
theorem Check055.part14240 : Interval test 14240 14256 :=
  interval_of_check _ 14240 16 (by decide +kernel)
theorem Check055.part14256 : Interval test 14256 14272 :=
  interval_of_check _ 14256 16 (by decide +kernel)
theorem Check055.part14272 : Interval test 14272 14288 :=
  interval_of_check _ 14272 16 (by decide +kernel)
theorem Check055.part14288 : Interval test 14288 14304 :=
  interval_of_check _ 14288 16 (by decide +kernel)
theorem Check055.part14304 : Interval test 14304 14320 :=
  interval_of_check _ 14304 16 (by decide +kernel)
theorem Check055.part14320 : Interval test 14320 14336 :=
  interval_of_check _ 14320 16 (by decide +kernel)
theorem Check055.checked : Interval test 14080 14336 :=
  (FiniteChecks.interval_append test 14080 14208 14336
  (FiniteChecks.interval_append test 14080 14144 14208
  (FiniteChecks.interval_append test 14080 14112 14144
  (FiniteChecks.interval_append test 14080 14096 14112
  Check055.part14080
  Check055.part14096)
  (FiniteChecks.interval_append test 14112 14128 14144
  Check055.part14112
  Check055.part14128))
  (FiniteChecks.interval_append test 14144 14176 14208
  (FiniteChecks.interval_append test 14144 14160 14176
  Check055.part14144
  Check055.part14160)
  (FiniteChecks.interval_append test 14176 14192 14208
  Check055.part14176
  Check055.part14192)))
  (FiniteChecks.interval_append test 14208 14272 14336
  (FiniteChecks.interval_append test 14208 14240 14272
  (FiniteChecks.interval_append test 14208 14224 14240
  Check055.part14208
  Check055.part14224)
  (FiniteChecks.interval_append test 14240 14256 14272
  Check055.part14240
  Check055.part14256))
  (FiniteChecks.interval_append test 14272 14304 14336
  (FiniteChecks.interval_append test 14272 14288 14304
  Check055.part14272
  Check055.part14288)
  (FiniteChecks.interval_append test 14304 14320 14336
  Check055.part14304
  Check055.part14320))))
#print axioms Check055.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check056.part14336 : Interval test 14336 14352 :=
  interval_of_check _ 14336 16 (by decide +kernel)
theorem Check056.part14352 : Interval test 14352 14368 :=
  interval_of_check _ 14352 16 (by decide +kernel)
theorem Check056.part14368 : Interval test 14368 14384 :=
  interval_of_check _ 14368 16 (by decide +kernel)
theorem Check056.part14384 : Interval test 14384 14400 :=
  interval_of_check _ 14384 16 (by decide +kernel)
theorem Check056.part14400 : Interval test 14400 14416 :=
  interval_of_check _ 14400 16 (by decide +kernel)
theorem Check056.part14416 : Interval test 14416 14432 :=
  interval_of_check _ 14416 16 (by decide +kernel)
theorem Check056.part14432 : Interval test 14432 14448 :=
  interval_of_check _ 14432 16 (by decide +kernel)
theorem Check056.part14448 : Interval test 14448 14464 :=
  interval_of_check _ 14448 16 (by decide +kernel)
theorem Check056.part14464 : Interval test 14464 14480 :=
  interval_of_check _ 14464 16 (by decide +kernel)
theorem Check056.part14480 : Interval test 14480 14496 :=
  interval_of_check _ 14480 16 (by decide +kernel)
theorem Check056.part14496 : Interval test 14496 14512 :=
  interval_of_check _ 14496 16 (by decide +kernel)
theorem Check056.part14512 : Interval test 14512 14528 :=
  interval_of_check _ 14512 16 (by decide +kernel)
theorem Check056.part14528 : Interval test 14528 14544 :=
  interval_of_check _ 14528 16 (by decide +kernel)
theorem Check056.part14544 : Interval test 14544 14560 :=
  interval_of_check _ 14544 16 (by decide +kernel)
theorem Check056.part14560 : Interval test 14560 14576 :=
  interval_of_check _ 14560 16 (by decide +kernel)
theorem Check056.part14576 : Interval test 14576 14592 :=
  interval_of_check _ 14576 16 (by decide +kernel)
theorem Check056.checked : Interval test 14336 14592 :=
  (FiniteChecks.interval_append test 14336 14464 14592
  (FiniteChecks.interval_append test 14336 14400 14464
  (FiniteChecks.interval_append test 14336 14368 14400
  (FiniteChecks.interval_append test 14336 14352 14368
  Check056.part14336
  Check056.part14352)
  (FiniteChecks.interval_append test 14368 14384 14400
  Check056.part14368
  Check056.part14384))
  (FiniteChecks.interval_append test 14400 14432 14464
  (FiniteChecks.interval_append test 14400 14416 14432
  Check056.part14400
  Check056.part14416)
  (FiniteChecks.interval_append test 14432 14448 14464
  Check056.part14432
  Check056.part14448)))
  (FiniteChecks.interval_append test 14464 14528 14592
  (FiniteChecks.interval_append test 14464 14496 14528
  (FiniteChecks.interval_append test 14464 14480 14496
  Check056.part14464
  Check056.part14480)
  (FiniteChecks.interval_append test 14496 14512 14528
  Check056.part14496
  Check056.part14512))
  (FiniteChecks.interval_append test 14528 14560 14592
  (FiniteChecks.interval_append test 14528 14544 14560
  Check056.part14528
  Check056.part14544)
  (FiniteChecks.interval_append test 14560 14576 14592
  Check056.part14560
  Check056.part14576))))
#print axioms Check056.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check057.part14592 : Interval test 14592 14608 :=
  interval_of_check _ 14592 16 (by decide +kernel)
theorem Check057.part14608 : Interval test 14608 14624 :=
  interval_of_check _ 14608 16 (by decide +kernel)
theorem Check057.part14624 : Interval test 14624 14640 :=
  interval_of_check _ 14624 16 (by decide +kernel)
theorem Check057.part14640 : Interval test 14640 14656 :=
  interval_of_check _ 14640 16 (by decide +kernel)
theorem Check057.part14656 : Interval test 14656 14672 :=
  interval_of_check _ 14656 16 (by decide +kernel)
theorem Check057.part14672 : Interval test 14672 14688 :=
  interval_of_check _ 14672 16 (by decide +kernel)
theorem Check057.part14688 : Interval test 14688 14704 :=
  interval_of_check _ 14688 16 (by decide +kernel)
theorem Check057.part14704 : Interval test 14704 14720 :=
  interval_of_check _ 14704 16 (by decide +kernel)
theorem Check057.part14720 : Interval test 14720 14736 :=
  interval_of_check _ 14720 16 (by decide +kernel)
theorem Check057.part14736 : Interval test 14736 14752 :=
  interval_of_check _ 14736 16 (by decide +kernel)
theorem Check057.part14752 : Interval test 14752 14768 :=
  interval_of_check _ 14752 16 (by decide +kernel)
theorem Check057.part14768 : Interval test 14768 14784 :=
  interval_of_check _ 14768 16 (by decide +kernel)
theorem Check057.part14784 : Interval test 14784 14800 :=
  interval_of_check _ 14784 16 (by decide +kernel)
theorem Check057.part14800 : Interval test 14800 14816 :=
  interval_of_check _ 14800 16 (by decide +kernel)
theorem Check057.part14816 : Interval test 14816 14832 :=
  interval_of_check _ 14816 16 (by decide +kernel)
theorem Check057.part14832 : Interval test 14832 14848 :=
  interval_of_check _ 14832 16 (by decide +kernel)
theorem Check057.checked : Interval test 14592 14848 :=
  (FiniteChecks.interval_append test 14592 14720 14848
  (FiniteChecks.interval_append test 14592 14656 14720
  (FiniteChecks.interval_append test 14592 14624 14656
  (FiniteChecks.interval_append test 14592 14608 14624
  Check057.part14592
  Check057.part14608)
  (FiniteChecks.interval_append test 14624 14640 14656
  Check057.part14624
  Check057.part14640))
  (FiniteChecks.interval_append test 14656 14688 14720
  (FiniteChecks.interval_append test 14656 14672 14688
  Check057.part14656
  Check057.part14672)
  (FiniteChecks.interval_append test 14688 14704 14720
  Check057.part14688
  Check057.part14704)))
  (FiniteChecks.interval_append test 14720 14784 14848
  (FiniteChecks.interval_append test 14720 14752 14784
  (FiniteChecks.interval_append test 14720 14736 14752
  Check057.part14720
  Check057.part14736)
  (FiniteChecks.interval_append test 14752 14768 14784
  Check057.part14752
  Check057.part14768))
  (FiniteChecks.interval_append test 14784 14816 14848
  (FiniteChecks.interval_append test 14784 14800 14816
  Check057.part14784
  Check057.part14800)
  (FiniteChecks.interval_append test 14816 14832 14848
  Check057.part14816
  Check057.part14832))))
#print axioms Check057.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check058.part14848 : Interval test 14848 14864 :=
  interval_of_check _ 14848 16 (by decide +kernel)
theorem Check058.part14864 : Interval test 14864 14880 :=
  interval_of_check _ 14864 16 (by decide +kernel)
theorem Check058.part14880 : Interval test 14880 14896 :=
  interval_of_check _ 14880 16 (by decide +kernel)
theorem Check058.part14896 : Interval test 14896 14912 :=
  interval_of_check _ 14896 16 (by decide +kernel)
theorem Check058.part14912 : Interval test 14912 14928 :=
  interval_of_check _ 14912 16 (by decide +kernel)
theorem Check058.part14928 : Interval test 14928 14944 :=
  interval_of_check _ 14928 16 (by decide +kernel)
theorem Check058.part14944 : Interval test 14944 14960 :=
  interval_of_check _ 14944 16 (by decide +kernel)
theorem Check058.part14960 : Interval test 14960 14976 :=
  interval_of_check _ 14960 16 (by decide +kernel)
theorem Check058.part14976 : Interval test 14976 14992 :=
  interval_of_check _ 14976 16 (by decide +kernel)
theorem Check058.part14992 : Interval test 14992 15008 :=
  interval_of_check _ 14992 16 (by decide +kernel)
theorem Check058.part15008 : Interval test 15008 15024 :=
  interval_of_check _ 15008 16 (by decide +kernel)
theorem Check058.part15024 : Interval test 15024 15040 :=
  interval_of_check _ 15024 16 (by decide +kernel)
theorem Check058.part15040 : Interval test 15040 15056 :=
  interval_of_check _ 15040 16 (by decide +kernel)
theorem Check058.part15056 : Interval test 15056 15072 :=
  interval_of_check _ 15056 16 (by decide +kernel)
theorem Check058.part15072 : Interval test 15072 15088 :=
  interval_of_check _ 15072 16 (by decide +kernel)
theorem Check058.part15088 : Interval test 15088 15104 :=
  interval_of_check _ 15088 16 (by decide +kernel)
theorem Check058.checked : Interval test 14848 15104 :=
  (FiniteChecks.interval_append test 14848 14976 15104
  (FiniteChecks.interval_append test 14848 14912 14976
  (FiniteChecks.interval_append test 14848 14880 14912
  (FiniteChecks.interval_append test 14848 14864 14880
  Check058.part14848
  Check058.part14864)
  (FiniteChecks.interval_append test 14880 14896 14912
  Check058.part14880
  Check058.part14896))
  (FiniteChecks.interval_append test 14912 14944 14976
  (FiniteChecks.interval_append test 14912 14928 14944
  Check058.part14912
  Check058.part14928)
  (FiniteChecks.interval_append test 14944 14960 14976
  Check058.part14944
  Check058.part14960)))
  (FiniteChecks.interval_append test 14976 15040 15104
  (FiniteChecks.interval_append test 14976 15008 15040
  (FiniteChecks.interval_append test 14976 14992 15008
  Check058.part14976
  Check058.part14992)
  (FiniteChecks.interval_append test 15008 15024 15040
  Check058.part15008
  Check058.part15024))
  (FiniteChecks.interval_append test 15040 15072 15104
  (FiniteChecks.interval_append test 15040 15056 15072
  Check058.part15040
  Check058.part15056)
  (FiniteChecks.interval_append test 15072 15088 15104
  Check058.part15072
  Check058.part15088))))
#print axioms Check058.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0Incidence
open ConcreteGrowth FiniteChecks SharedPoolIncidence
theorem Check059.part15104 : Interval test 15104 15120 :=
  interval_of_check _ 15104 16 (by decide +kernel)
theorem Check059.part15120 : Interval test 15120 15136 :=
  interval_of_check _ 15120 16 (by decide +kernel)
theorem Check059.part15136 : Interval test 15136 15152 :=
  interval_of_check _ 15136 16 (by decide +kernel)
theorem Check059.part15152 : Interval test 15152 15168 :=
  interval_of_check _ 15152 16 (by decide +kernel)
theorem Check059.part15168 : Interval test 15168 15184 :=
  interval_of_check _ 15168 16 (by decide +kernel)
theorem Check059.part15184 : Interval test 15184 15200 :=
  interval_of_check _ 15184 16 (by decide +kernel)
theorem Check059.part15200 : Interval test 15200 15216 :=
  interval_of_check _ 15200 16 (by decide +kernel)
theorem Check059.part15216 : Interval test 15216 15232 :=
  interval_of_check _ 15216 16 (by decide +kernel)
theorem Check059.part15232 : Interval test 15232 15248 :=
  interval_of_check _ 15232 16 (by decide +kernel)
theorem Check059.part15248 : Interval test 15248 15264 :=
  interval_of_check _ 15248 16 (by decide +kernel)
theorem Check059.part15264 : Interval test 15264 15280 :=
  interval_of_check _ 15264 16 (by decide +kernel)
theorem Check059.part15280 : Interval test 15280 15296 :=
  interval_of_check _ 15280 16 (by decide +kernel)
theorem Check059.part15296 : Interval test 15296 15312 :=
  interval_of_check _ 15296 16 (by decide +kernel)
theorem Check059.part15312 : Interval test 15312 15328 :=
  interval_of_check _ 15312 16 (by decide +kernel)
theorem Check059.part15328 : Interval test 15328 15344 :=
  interval_of_check _ 15328 16 (by decide +kernel)
theorem Check059.part15344 : Interval test 15344 15360 :=
  interval_of_check _ 15344 16 (by decide +kernel)
theorem Check059.checked : Interval test 15104 15360 :=
  (FiniteChecks.interval_append test 15104 15232 15360
  (FiniteChecks.interval_append test 15104 15168 15232
  (FiniteChecks.interval_append test 15104 15136 15168
  (FiniteChecks.interval_append test 15104 15120 15136
  Check059.part15104
  Check059.part15120)
  (FiniteChecks.interval_append test 15136 15152 15168
  Check059.part15136
  Check059.part15152))
  (FiniteChecks.interval_append test 15168 15200 15232
  (FiniteChecks.interval_append test 15168 15184 15200
  Check059.part15168
  Check059.part15184)
  (FiniteChecks.interval_append test 15200 15216 15232
  Check059.part15200
  Check059.part15216)))
  (FiniteChecks.interval_append test 15232 15296 15360
  (FiniteChecks.interval_append test 15232 15264 15296
  (FiniteChecks.interval_append test 15232 15248 15264
  Check059.part15232
  Check059.part15248)
  (FiniteChecks.interval_append test 15264 15280 15296
  Check059.part15264
  Check059.part15280))
  (FiniteChecks.interval_append test 15296 15328 15360
  (FiniteChecks.interval_append test 15296 15312 15328
  Check059.part15296
  Check059.part15312)
  (FiniteChecks.interval_append test 15328 15344 15360
  Check059.part15328
  Check059.part15344))))
#print axioms Check059.checked
end Papers.RationalityTen.SharedSix0Incidence

end
end
