module
prelude
public import SharedTriangleCountsData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open Papers.RationalityTen FiniteChecks

namespace Papers.RationalityTen.SharedTriangleCounts
theorem Check080.part10240 : Interval test 10240 10248 :=
  interval_of_check _ 10240 8 (by decide +kernel)
theorem Check080.part10248 : Interval test 10248 10256 :=
  interval_of_check _ 10248 8 (by decide +kernel)
theorem Check080.part10256 : Interval test 10256 10264 :=
  interval_of_check _ 10256 8 (by decide +kernel)
theorem Check080.part10264 : Interval test 10264 10272 :=
  interval_of_check _ 10264 8 (by decide +kernel)
theorem Check080.part10272 : Interval test 10272 10280 :=
  interval_of_check _ 10272 8 (by decide +kernel)
theorem Check080.part10280 : Interval test 10280 10288 :=
  interval_of_check _ 10280 8 (by decide +kernel)
theorem Check080.part10288 : Interval test 10288 10296 :=
  interval_of_check _ 10288 8 (by decide +kernel)
theorem Check080.part10296 : Interval test 10296 10304 :=
  interval_of_check _ 10296 8 (by decide +kernel)
theorem Check080.part10304 : Interval test 10304 10312 :=
  interval_of_check _ 10304 8 (by decide +kernel)
theorem Check080.part10312 : Interval test 10312 10320 :=
  interval_of_check _ 10312 8 (by decide +kernel)
theorem Check080.part10320 : Interval test 10320 10328 :=
  interval_of_check _ 10320 8 (by decide +kernel)
theorem Check080.part10328 : Interval test 10328 10336 :=
  interval_of_check _ 10328 8 (by decide +kernel)
theorem Check080.part10336 : Interval test 10336 10344 :=
  interval_of_check _ 10336 8 (by decide +kernel)
theorem Check080.part10344 : Interval test 10344 10352 :=
  interval_of_check _ 10344 8 (by decide +kernel)
theorem Check080.part10352 : Interval test 10352 10360 :=
  interval_of_check _ 10352 8 (by decide +kernel)
theorem Check080.part10360 : Interval test 10360 10368 :=
  interval_of_check _ 10360 8 (by decide +kernel)
theorem Check080.checked : Interval test 10240 10368 :=
  (FiniteChecks.interval_append test 10240 10304 10368
  (FiniteChecks.interval_append test 10240 10272 10304
  (FiniteChecks.interval_append test 10240 10256 10272
  (FiniteChecks.interval_append test 10240 10248 10256
  Check080.part10240
  Check080.part10248)
  (FiniteChecks.interval_append test 10256 10264 10272
  Check080.part10256
  Check080.part10264))
  (FiniteChecks.interval_append test 10272 10288 10304
  (FiniteChecks.interval_append test 10272 10280 10288
  Check080.part10272
  Check080.part10280)
  (FiniteChecks.interval_append test 10288 10296 10304
  Check080.part10288
  Check080.part10296)))
  (FiniteChecks.interval_append test 10304 10336 10368
  (FiniteChecks.interval_append test 10304 10320 10336
  (FiniteChecks.interval_append test 10304 10312 10320
  Check080.part10304
  Check080.part10312)
  (FiniteChecks.interval_append test 10320 10328 10336
  Check080.part10320
  Check080.part10328))
  (FiniteChecks.interval_append test 10336 10352 10368
  (FiniteChecks.interval_append test 10336 10344 10352
  Check080.part10336
  Check080.part10344)
  (FiniteChecks.interval_append test 10352 10360 10368
  Check080.part10352
  Check080.part10360))))
theorem Check081.part10368 : Interval test 10368 10376 :=
  interval_of_check _ 10368 8 (by decide +kernel)
theorem Check081.part10376 : Interval test 10376 10384 :=
  interval_of_check _ 10376 8 (by decide +kernel)
theorem Check081.part10384 : Interval test 10384 10392 :=
  interval_of_check _ 10384 8 (by decide +kernel)
theorem Check081.part10392 : Interval test 10392 10400 :=
  interval_of_check _ 10392 8 (by decide +kernel)
theorem Check081.part10400 : Interval test 10400 10408 :=
  interval_of_check _ 10400 8 (by decide +kernel)
theorem Check081.part10408 : Interval test 10408 10416 :=
  interval_of_check _ 10408 8 (by decide +kernel)
theorem Check081.part10416 : Interval test 10416 10424 :=
  interval_of_check _ 10416 8 (by decide +kernel)
theorem Check081.part10424 : Interval test 10424 10432 :=
  interval_of_check _ 10424 8 (by decide +kernel)
theorem Check081.part10432 : Interval test 10432 10440 :=
  interval_of_check _ 10432 8 (by decide +kernel)
theorem Check081.part10440 : Interval test 10440 10448 :=
  interval_of_check _ 10440 8 (by decide +kernel)
theorem Check081.part10448 : Interval test 10448 10456 :=
  interval_of_check _ 10448 8 (by decide +kernel)
theorem Check081.part10456 : Interval test 10456 10464 :=
  interval_of_check _ 10456 8 (by decide +kernel)
theorem Check081.part10464 : Interval test 10464 10472 :=
  interval_of_check _ 10464 8 (by decide +kernel)
theorem Check081.part10472 : Interval test 10472 10480 :=
  interval_of_check _ 10472 8 (by decide +kernel)
theorem Check081.part10480 : Interval test 10480 10488 :=
  interval_of_check _ 10480 8 (by decide +kernel)
theorem Check081.part10488 : Interval test 10488 10496 :=
  interval_of_check _ 10488 8 (by decide +kernel)
theorem Check081.checked : Interval test 10368 10496 :=
  (FiniteChecks.interval_append test 10368 10432 10496
  (FiniteChecks.interval_append test 10368 10400 10432
  (FiniteChecks.interval_append test 10368 10384 10400
  (FiniteChecks.interval_append test 10368 10376 10384
  Check081.part10368
  Check081.part10376)
  (FiniteChecks.interval_append test 10384 10392 10400
  Check081.part10384
  Check081.part10392))
  (FiniteChecks.interval_append test 10400 10416 10432
  (FiniteChecks.interval_append test 10400 10408 10416
  Check081.part10400
  Check081.part10408)
  (FiniteChecks.interval_append test 10416 10424 10432
  Check081.part10416
  Check081.part10424)))
  (FiniteChecks.interval_append test 10432 10464 10496
  (FiniteChecks.interval_append test 10432 10448 10464
  (FiniteChecks.interval_append test 10432 10440 10448
  Check081.part10432
  Check081.part10440)
  (FiniteChecks.interval_append test 10448 10456 10464
  Check081.part10448
  Check081.part10456))
  (FiniteChecks.interval_append test 10464 10480 10496
  (FiniteChecks.interval_append test 10464 10472 10480
  Check081.part10464
  Check081.part10472)
  (FiniteChecks.interval_append test 10480 10488 10496
  Check081.part10480
  Check081.part10488))))
theorem Check082.part10496 : Interval test 10496 10504 :=
  interval_of_check _ 10496 8 (by decide +kernel)
theorem Check082.part10504 : Interval test 10504 10512 :=
  interval_of_check _ 10504 8 (by decide +kernel)
theorem Check082.part10512 : Interval test 10512 10520 :=
  interval_of_check _ 10512 8 (by decide +kernel)
theorem Check082.part10520 : Interval test 10520 10528 :=
  interval_of_check _ 10520 8 (by decide +kernel)
theorem Check082.part10528 : Interval test 10528 10536 :=
  interval_of_check _ 10528 8 (by decide +kernel)
theorem Check082.part10536 : Interval test 10536 10544 :=
  interval_of_check _ 10536 8 (by decide +kernel)
theorem Check082.part10544 : Interval test 10544 10552 :=
  interval_of_check _ 10544 8 (by decide +kernel)
theorem Check082.part10552 : Interval test 10552 10560 :=
  interval_of_check _ 10552 8 (by decide +kernel)
theorem Check082.part10560 : Interval test 10560 10568 :=
  interval_of_check _ 10560 8 (by decide +kernel)
theorem Check082.part10568 : Interval test 10568 10576 :=
  interval_of_check _ 10568 8 (by decide +kernel)
theorem Check082.part10576 : Interval test 10576 10584 :=
  interval_of_check _ 10576 8 (by decide +kernel)
theorem Check082.part10584 : Interval test 10584 10592 :=
  interval_of_check _ 10584 8 (by decide +kernel)
theorem Check082.part10592 : Interval test 10592 10600 :=
  interval_of_check _ 10592 8 (by decide +kernel)
theorem Check082.part10600 : Interval test 10600 10608 :=
  interval_of_check _ 10600 8 (by decide +kernel)
theorem Check082.part10608 : Interval test 10608 10616 :=
  interval_of_check _ 10608 8 (by decide +kernel)
theorem Check082.part10616 : Interval test 10616 10624 :=
  interval_of_check _ 10616 8 (by decide +kernel)
theorem Check082.checked : Interval test 10496 10624 :=
  (FiniteChecks.interval_append test 10496 10560 10624
  (FiniteChecks.interval_append test 10496 10528 10560
  (FiniteChecks.interval_append test 10496 10512 10528
  (FiniteChecks.interval_append test 10496 10504 10512
  Check082.part10496
  Check082.part10504)
  (FiniteChecks.interval_append test 10512 10520 10528
  Check082.part10512
  Check082.part10520))
  (FiniteChecks.interval_append test 10528 10544 10560
  (FiniteChecks.interval_append test 10528 10536 10544
  Check082.part10528
  Check082.part10536)
  (FiniteChecks.interval_append test 10544 10552 10560
  Check082.part10544
  Check082.part10552)))
  (FiniteChecks.interval_append test 10560 10592 10624
  (FiniteChecks.interval_append test 10560 10576 10592
  (FiniteChecks.interval_append test 10560 10568 10576
  Check082.part10560
  Check082.part10568)
  (FiniteChecks.interval_append test 10576 10584 10592
  Check082.part10576
  Check082.part10584))
  (FiniteChecks.interval_append test 10592 10608 10624
  (FiniteChecks.interval_append test 10592 10600 10608
  Check082.part10592
  Check082.part10600)
  (FiniteChecks.interval_append test 10608 10616 10624
  Check082.part10608
  Check082.part10616))))
theorem Check083.part10624 : Interval test 10624 10632 :=
  interval_of_check _ 10624 8 (by decide +kernel)
theorem Check083.part10632 : Interval test 10632 10640 :=
  interval_of_check _ 10632 8 (by decide +kernel)
theorem Check083.part10640 : Interval test 10640 10648 :=
  interval_of_check _ 10640 8 (by decide +kernel)
theorem Check083.part10648 : Interval test 10648 10656 :=
  interval_of_check _ 10648 8 (by decide +kernel)
theorem Check083.part10656 : Interval test 10656 10664 :=
  interval_of_check _ 10656 8 (by decide +kernel)
theorem Check083.part10664 : Interval test 10664 10672 :=
  interval_of_check _ 10664 8 (by decide +kernel)
theorem Check083.part10672 : Interval test 10672 10680 :=
  interval_of_check _ 10672 8 (by decide +kernel)
theorem Check083.part10680 : Interval test 10680 10688 :=
  interval_of_check _ 10680 8 (by decide +kernel)
theorem Check083.part10688 : Interval test 10688 10696 :=
  interval_of_check _ 10688 8 (by decide +kernel)
theorem Check083.part10696 : Interval test 10696 10704 :=
  interval_of_check _ 10696 8 (by decide +kernel)
theorem Check083.part10704 : Interval test 10704 10712 :=
  interval_of_check _ 10704 8 (by decide +kernel)
theorem Check083.part10712 : Interval test 10712 10720 :=
  interval_of_check _ 10712 8 (by decide +kernel)
theorem Check083.part10720 : Interval test 10720 10728 :=
  interval_of_check _ 10720 8 (by decide +kernel)
theorem Check083.part10728 : Interval test 10728 10736 :=
  interval_of_check _ 10728 8 (by decide +kernel)
theorem Check083.part10736 : Interval test 10736 10744 :=
  interval_of_check _ 10736 8 (by decide +kernel)
theorem Check083.part10744 : Interval test 10744 10752 :=
  interval_of_check _ 10744 8 (by decide +kernel)
theorem Check083.checked : Interval test 10624 10752 :=
  (FiniteChecks.interval_append test 10624 10688 10752
  (FiniteChecks.interval_append test 10624 10656 10688
  (FiniteChecks.interval_append test 10624 10640 10656
  (FiniteChecks.interval_append test 10624 10632 10640
  Check083.part10624
  Check083.part10632)
  (FiniteChecks.interval_append test 10640 10648 10656
  Check083.part10640
  Check083.part10648))
  (FiniteChecks.interval_append test 10656 10672 10688
  (FiniteChecks.interval_append test 10656 10664 10672
  Check083.part10656
  Check083.part10664)
  (FiniteChecks.interval_append test 10672 10680 10688
  Check083.part10672
  Check083.part10680)))
  (FiniteChecks.interval_append test 10688 10720 10752
  (FiniteChecks.interval_append test 10688 10704 10720
  (FiniteChecks.interval_append test 10688 10696 10704
  Check083.part10688
  Check083.part10696)
  (FiniteChecks.interval_append test 10704 10712 10720
  Check083.part10704
  Check083.part10712))
  (FiniteChecks.interval_append test 10720 10736 10752
  (FiniteChecks.interval_append test 10720 10728 10736
  Check083.part10720
  Check083.part10728)
  (FiniteChecks.interval_append test 10736 10744 10752
  Check083.part10736
  Check083.part10744))))
theorem Check084.part10752 : Interval test 10752 10760 :=
  interval_of_check _ 10752 8 (by decide +kernel)
theorem Check084.part10760 : Interval test 10760 10768 :=
  interval_of_check _ 10760 8 (by decide +kernel)
theorem Check084.part10768 : Interval test 10768 10776 :=
  interval_of_check _ 10768 8 (by decide +kernel)
theorem Check084.part10776 : Interval test 10776 10784 :=
  interval_of_check _ 10776 8 (by decide +kernel)
theorem Check084.part10784 : Interval test 10784 10792 :=
  interval_of_check _ 10784 8 (by decide +kernel)
theorem Check084.part10792 : Interval test 10792 10800 :=
  interval_of_check _ 10792 8 (by decide +kernel)
theorem Check084.part10800 : Interval test 10800 10808 :=
  interval_of_check _ 10800 8 (by decide +kernel)
theorem Check084.part10808 : Interval test 10808 10816 :=
  interval_of_check _ 10808 8 (by decide +kernel)
theorem Check084.part10816 : Interval test 10816 10824 :=
  interval_of_check _ 10816 8 (by decide +kernel)
theorem Check084.part10824 : Interval test 10824 10832 :=
  interval_of_check _ 10824 8 (by decide +kernel)
theorem Check084.part10832 : Interval test 10832 10840 :=
  interval_of_check _ 10832 8 (by decide +kernel)
theorem Check084.part10840 : Interval test 10840 10848 :=
  interval_of_check _ 10840 8 (by decide +kernel)
theorem Check084.part10848 : Interval test 10848 10856 :=
  interval_of_check _ 10848 8 (by decide +kernel)
theorem Check084.part10856 : Interval test 10856 10864 :=
  interval_of_check _ 10856 8 (by decide +kernel)
theorem Check084.part10864 : Interval test 10864 10872 :=
  interval_of_check _ 10864 8 (by decide +kernel)
theorem Check084.part10872 : Interval test 10872 10880 :=
  interval_of_check _ 10872 8 (by decide +kernel)
theorem Check084.checked : Interval test 10752 10880 :=
  (FiniteChecks.interval_append test 10752 10816 10880
  (FiniteChecks.interval_append test 10752 10784 10816
  (FiniteChecks.interval_append test 10752 10768 10784
  (FiniteChecks.interval_append test 10752 10760 10768
  Check084.part10752
  Check084.part10760)
  (FiniteChecks.interval_append test 10768 10776 10784
  Check084.part10768
  Check084.part10776))
  (FiniteChecks.interval_append test 10784 10800 10816
  (FiniteChecks.interval_append test 10784 10792 10800
  Check084.part10784
  Check084.part10792)
  (FiniteChecks.interval_append test 10800 10808 10816
  Check084.part10800
  Check084.part10808)))
  (FiniteChecks.interval_append test 10816 10848 10880
  (FiniteChecks.interval_append test 10816 10832 10848
  (FiniteChecks.interval_append test 10816 10824 10832
  Check084.part10816
  Check084.part10824)
  (FiniteChecks.interval_append test 10832 10840 10848
  Check084.part10832
  Check084.part10840))
  (FiniteChecks.interval_append test 10848 10864 10880
  (FiniteChecks.interval_append test 10848 10856 10864
  Check084.part10848
  Check084.part10856)
  (FiniteChecks.interval_append test 10864 10872 10880
  Check084.part10864
  Check084.part10872))))
theorem Check085.part10880 : Interval test 10880 10888 :=
  interval_of_check _ 10880 8 (by decide +kernel)
theorem Check085.part10888 : Interval test 10888 10896 :=
  interval_of_check _ 10888 8 (by decide +kernel)
theorem Check085.part10896 : Interval test 10896 10904 :=
  interval_of_check _ 10896 8 (by decide +kernel)
theorem Check085.part10904 : Interval test 10904 10912 :=
  interval_of_check _ 10904 8 (by decide +kernel)
theorem Check085.part10912 : Interval test 10912 10920 :=
  interval_of_check _ 10912 8 (by decide +kernel)
theorem Check085.part10920 : Interval test 10920 10928 :=
  interval_of_check _ 10920 8 (by decide +kernel)
theorem Check085.part10928 : Interval test 10928 10936 :=
  interval_of_check _ 10928 8 (by decide +kernel)
theorem Check085.part10936 : Interval test 10936 10944 :=
  interval_of_check _ 10936 8 (by decide +kernel)
theorem Check085.part10944 : Interval test 10944 10952 :=
  interval_of_check _ 10944 8 (by decide +kernel)
theorem Check085.part10952 : Interval test 10952 10960 :=
  interval_of_check _ 10952 8 (by decide +kernel)
theorem Check085.part10960 : Interval test 10960 10968 :=
  interval_of_check _ 10960 8 (by decide +kernel)
theorem Check085.part10968 : Interval test 10968 10976 :=
  interval_of_check _ 10968 8 (by decide +kernel)
theorem Check085.part10976 : Interval test 10976 10984 :=
  interval_of_check _ 10976 8 (by decide +kernel)
theorem Check085.part10984 : Interval test 10984 10992 :=
  interval_of_check _ 10984 8 (by decide +kernel)
theorem Check085.part10992 : Interval test 10992 11000 :=
  interval_of_check _ 10992 8 (by decide +kernel)
theorem Check085.part11000 : Interval test 11000 11008 :=
  interval_of_check _ 11000 8 (by decide +kernel)
theorem Check085.checked : Interval test 10880 11008 :=
  (FiniteChecks.interval_append test 10880 10944 11008
  (FiniteChecks.interval_append test 10880 10912 10944
  (FiniteChecks.interval_append test 10880 10896 10912
  (FiniteChecks.interval_append test 10880 10888 10896
  Check085.part10880
  Check085.part10888)
  (FiniteChecks.interval_append test 10896 10904 10912
  Check085.part10896
  Check085.part10904))
  (FiniteChecks.interval_append test 10912 10928 10944
  (FiniteChecks.interval_append test 10912 10920 10928
  Check085.part10912
  Check085.part10920)
  (FiniteChecks.interval_append test 10928 10936 10944
  Check085.part10928
  Check085.part10936)))
  (FiniteChecks.interval_append test 10944 10976 11008
  (FiniteChecks.interval_append test 10944 10960 10976
  (FiniteChecks.interval_append test 10944 10952 10960
  Check085.part10944
  Check085.part10952)
  (FiniteChecks.interval_append test 10960 10968 10976
  Check085.part10960
  Check085.part10968))
  (FiniteChecks.interval_append test 10976 10992 11008
  (FiniteChecks.interval_append test 10976 10984 10992
  Check085.part10976
  Check085.part10984)
  (FiniteChecks.interval_append test 10992 11000 11008
  Check085.part10992
  Check085.part11000))))
theorem Check086.part11008 : Interval test 11008 11016 :=
  interval_of_check _ 11008 8 (by decide +kernel)
theorem Check086.part11016 : Interval test 11016 11024 :=
  interval_of_check _ 11016 8 (by decide +kernel)
theorem Check086.part11024 : Interval test 11024 11032 :=
  interval_of_check _ 11024 8 (by decide +kernel)
theorem Check086.part11032 : Interval test 11032 11040 :=
  interval_of_check _ 11032 8 (by decide +kernel)
theorem Check086.part11040 : Interval test 11040 11048 :=
  interval_of_check _ 11040 8 (by decide +kernel)
theorem Check086.part11048 : Interval test 11048 11056 :=
  interval_of_check _ 11048 8 (by decide +kernel)
theorem Check086.part11056 : Interval test 11056 11064 :=
  interval_of_check _ 11056 8 (by decide +kernel)
theorem Check086.part11064 : Interval test 11064 11072 :=
  interval_of_check _ 11064 8 (by decide +kernel)
theorem Check086.part11072 : Interval test 11072 11080 :=
  interval_of_check _ 11072 8 (by decide +kernel)
theorem Check086.part11080 : Interval test 11080 11088 :=
  interval_of_check _ 11080 8 (by decide +kernel)
theorem Check086.part11088 : Interval test 11088 11096 :=
  interval_of_check _ 11088 8 (by decide +kernel)
theorem Check086.part11096 : Interval test 11096 11104 :=
  interval_of_check _ 11096 8 (by decide +kernel)
theorem Check086.part11104 : Interval test 11104 11112 :=
  interval_of_check _ 11104 8 (by decide +kernel)
theorem Check086.part11112 : Interval test 11112 11120 :=
  interval_of_check _ 11112 8 (by decide +kernel)
theorem Check086.part11120 : Interval test 11120 11128 :=
  interval_of_check _ 11120 8 (by decide +kernel)
theorem Check086.part11128 : Interval test 11128 11136 :=
  interval_of_check _ 11128 8 (by decide +kernel)
theorem Check086.checked : Interval test 11008 11136 :=
  (FiniteChecks.interval_append test 11008 11072 11136
  (FiniteChecks.interval_append test 11008 11040 11072
  (FiniteChecks.interval_append test 11008 11024 11040
  (FiniteChecks.interval_append test 11008 11016 11024
  Check086.part11008
  Check086.part11016)
  (FiniteChecks.interval_append test 11024 11032 11040
  Check086.part11024
  Check086.part11032))
  (FiniteChecks.interval_append test 11040 11056 11072
  (FiniteChecks.interval_append test 11040 11048 11056
  Check086.part11040
  Check086.part11048)
  (FiniteChecks.interval_append test 11056 11064 11072
  Check086.part11056
  Check086.part11064)))
  (FiniteChecks.interval_append test 11072 11104 11136
  (FiniteChecks.interval_append test 11072 11088 11104
  (FiniteChecks.interval_append test 11072 11080 11088
  Check086.part11072
  Check086.part11080)
  (FiniteChecks.interval_append test 11088 11096 11104
  Check086.part11088
  Check086.part11096))
  (FiniteChecks.interval_append test 11104 11120 11136
  (FiniteChecks.interval_append test 11104 11112 11120
  Check086.part11104
  Check086.part11112)
  (FiniteChecks.interval_append test 11120 11128 11136
  Check086.part11120
  Check086.part11128))))
theorem Check087.part11136 : Interval test 11136 11144 :=
  interval_of_check _ 11136 8 (by decide +kernel)
theorem Check087.part11144 : Interval test 11144 11152 :=
  interval_of_check _ 11144 8 (by decide +kernel)
theorem Check087.part11152 : Interval test 11152 11160 :=
  interval_of_check _ 11152 8 (by decide +kernel)
theorem Check087.part11160 : Interval test 11160 11168 :=
  interval_of_check _ 11160 8 (by decide +kernel)
theorem Check087.part11168 : Interval test 11168 11176 :=
  interval_of_check _ 11168 8 (by decide +kernel)
theorem Check087.part11176 : Interval test 11176 11184 :=
  interval_of_check _ 11176 8 (by decide +kernel)
theorem Check087.part11184 : Interval test 11184 11192 :=
  interval_of_check _ 11184 8 (by decide +kernel)
theorem Check087.part11192 : Interval test 11192 11200 :=
  interval_of_check _ 11192 8 (by decide +kernel)
theorem Check087.part11200 : Interval test 11200 11208 :=
  interval_of_check _ 11200 8 (by decide +kernel)
theorem Check087.part11208 : Interval test 11208 11216 :=
  interval_of_check _ 11208 8 (by decide +kernel)
theorem Check087.part11216 : Interval test 11216 11224 :=
  interval_of_check _ 11216 8 (by decide +kernel)
theorem Check087.part11224 : Interval test 11224 11232 :=
  interval_of_check _ 11224 8 (by decide +kernel)
theorem Check087.part11232 : Interval test 11232 11240 :=
  interval_of_check _ 11232 8 (by decide +kernel)
theorem Check087.part11240 : Interval test 11240 11248 :=
  interval_of_check _ 11240 8 (by decide +kernel)
theorem Check087.part11248 : Interval test 11248 11256 :=
  interval_of_check _ 11248 8 (by decide +kernel)
theorem Check087.part11256 : Interval test 11256 11264 :=
  interval_of_check _ 11256 8 (by decide +kernel)
theorem Check087.checked : Interval test 11136 11264 :=
  (FiniteChecks.interval_append test 11136 11200 11264
  (FiniteChecks.interval_append test 11136 11168 11200
  (FiniteChecks.interval_append test 11136 11152 11168
  (FiniteChecks.interval_append test 11136 11144 11152
  Check087.part11136
  Check087.part11144)
  (FiniteChecks.interval_append test 11152 11160 11168
  Check087.part11152
  Check087.part11160))
  (FiniteChecks.interval_append test 11168 11184 11200
  (FiniteChecks.interval_append test 11168 11176 11184
  Check087.part11168
  Check087.part11176)
  (FiniteChecks.interval_append test 11184 11192 11200
  Check087.part11184
  Check087.part11192)))
  (FiniteChecks.interval_append test 11200 11232 11264
  (FiniteChecks.interval_append test 11200 11216 11232
  (FiniteChecks.interval_append test 11200 11208 11216
  Check087.part11200
  Check087.part11208)
  (FiniteChecks.interval_append test 11216 11224 11232
  Check087.part11216
  Check087.part11224))
  (FiniteChecks.interval_append test 11232 11248 11264
  (FiniteChecks.interval_append test 11232 11240 11248
  Check087.part11232
  Check087.part11240)
  (FiniteChecks.interval_append test 11248 11256 11264
  Check087.part11248
  Check087.part11256))))
end Papers.RationalityTen.SharedTriangleCounts
