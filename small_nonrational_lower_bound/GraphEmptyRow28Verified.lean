module
prelude
public import SharedEmptyKeysRow28Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open Papers.RationalityTen FiniteChecks

namespace Papers.RationalityTen.SharedEmptyKeys.Row28
theorem Check000.part0 : Interval test 0 16 :=
  interval_of_check _ 0 16 (by decide +kernel)
theorem Check000.part16 : Interval test 16 32 :=
  interval_of_check _ 16 16 (by decide +kernel)
theorem Check000.part32 : Interval test 32 48 :=
  interval_of_check _ 32 16 (by decide +kernel)
theorem Check000.part48 : Interval test 48 64 :=
  interval_of_check _ 48 16 (by decide +kernel)
theorem Check000.part64 : Interval test 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem Check000.part80 : Interval test 80 96 :=
  interval_of_check _ 80 16 (by decide +kernel)
theorem Check000.part96 : Interval test 96 112 :=
  interval_of_check _ 96 16 (by decide +kernel)
theorem Check000.part112 : Interval test 112 128 :=
  interval_of_check _ 112 16 (by decide +kernel)
theorem Check000.part128 : Interval test 128 144 :=
  interval_of_check _ 128 16 (by decide +kernel)
theorem Check000.part144 : Interval test 144 160 :=
  interval_of_check _ 144 16 (by decide +kernel)
theorem Check000.part160 : Interval test 160 176 :=
  interval_of_check _ 160 16 (by decide +kernel)
theorem Check000.part176 : Interval test 176 192 :=
  interval_of_check _ 176 16 (by decide +kernel)
theorem Check000.part192 : Interval test 192 208 :=
  interval_of_check _ 192 16 (by decide +kernel)
theorem Check000.part208 : Interval test 208 224 :=
  interval_of_check _ 208 16 (by decide +kernel)
theorem Check000.part224 : Interval test 224 240 :=
  interval_of_check _ 224 16 (by decide +kernel)
theorem Check000.part240 : Interval test 240 256 :=
  interval_of_check _ 240 16 (by decide +kernel)
theorem Check000.checked : Interval test 0 256 :=
  (FiniteChecks.interval_append test 0 128 256
  (FiniteChecks.interval_append test 0 64 128
  (FiniteChecks.interval_append test 0 32 64
  (FiniteChecks.interval_append test 0 16 32
  Check000.part0
  Check000.part16)
  (FiniteChecks.interval_append test 32 48 64
  Check000.part32
  Check000.part48))
  (FiniteChecks.interval_append test 64 96 128
  (FiniteChecks.interval_append test 64 80 96
  Check000.part64
  Check000.part80)
  (FiniteChecks.interval_append test 96 112 128
  Check000.part96
  Check000.part112)))
  (FiniteChecks.interval_append test 128 192 256
  (FiniteChecks.interval_append test 128 160 192
  (FiniteChecks.interval_append test 128 144 160
  Check000.part128
  Check000.part144)
  (FiniteChecks.interval_append test 160 176 192
  Check000.part160
  Check000.part176))
  (FiniteChecks.interval_append test 192 224 256
  (FiniteChecks.interval_append test 192 208 224
  Check000.part192
  Check000.part208)
  (FiniteChecks.interval_append test 224 240 256
  Check000.part224
  Check000.part240))))
theorem Check001.part256 : Interval test 256 272 :=
  interval_of_check _ 256 16 (by decide +kernel)
theorem Check001.part272 : Interval test 272 288 :=
  interval_of_check _ 272 16 (by decide +kernel)
theorem Check001.part288 : Interval test 288 304 :=
  interval_of_check _ 288 16 (by decide +kernel)
theorem Check001.part304 : Interval test 304 320 :=
  interval_of_check _ 304 16 (by decide +kernel)
theorem Check001.part320 : Interval test 320 336 :=
  interval_of_check _ 320 16 (by decide +kernel)
theorem Check001.part336 : Interval test 336 352 :=
  interval_of_check _ 336 16 (by decide +kernel)
theorem Check001.part352 : Interval test 352 368 :=
  interval_of_check _ 352 16 (by decide +kernel)
theorem Check001.part368 : Interval test 368 384 :=
  interval_of_check _ 368 16 (by decide +kernel)
theorem Check001.part384 : Interval test 384 400 :=
  interval_of_check _ 384 16 (by decide +kernel)
theorem Check001.part400 : Interval test 400 416 :=
  interval_of_check _ 400 16 (by decide +kernel)
theorem Check001.part416 : Interval test 416 432 :=
  interval_of_check _ 416 16 (by decide +kernel)
theorem Check001.part432 : Interval test 432 448 :=
  interval_of_check _ 432 16 (by decide +kernel)
theorem Check001.part448 : Interval test 448 464 :=
  interval_of_check _ 448 16 (by decide +kernel)
theorem Check001.part464 : Interval test 464 480 :=
  interval_of_check _ 464 16 (by decide +kernel)
theorem Check001.part480 : Interval test 480 496 :=
  interval_of_check _ 480 16 (by decide +kernel)
theorem Check001.part496 : Interval test 496 512 :=
  interval_of_check _ 496 16 (by decide +kernel)
theorem Check001.checked : Interval test 256 512 :=
  (FiniteChecks.interval_append test 256 384 512
  (FiniteChecks.interval_append test 256 320 384
  (FiniteChecks.interval_append test 256 288 320
  (FiniteChecks.interval_append test 256 272 288
  Check001.part256
  Check001.part272)
  (FiniteChecks.interval_append test 288 304 320
  Check001.part288
  Check001.part304))
  (FiniteChecks.interval_append test 320 352 384
  (FiniteChecks.interval_append test 320 336 352
  Check001.part320
  Check001.part336)
  (FiniteChecks.interval_append test 352 368 384
  Check001.part352
  Check001.part368)))
  (FiniteChecks.interval_append test 384 448 512
  (FiniteChecks.interval_append test 384 416 448
  (FiniteChecks.interval_append test 384 400 416
  Check001.part384
  Check001.part400)
  (FiniteChecks.interval_append test 416 432 448
  Check001.part416
  Check001.part432))
  (FiniteChecks.interval_append test 448 480 512
  (FiniteChecks.interval_append test 448 464 480
  Check001.part448
  Check001.part464)
  (FiniteChecks.interval_append test 480 496 512
  Check001.part480
  Check001.part496))))
theorem Check002.part512 : Interval test 512 528 :=
  interval_of_check _ 512 16 (by decide +kernel)
theorem Check002.part528 : Interval test 528 544 :=
  interval_of_check _ 528 16 (by decide +kernel)
theorem Check002.part544 : Interval test 544 560 :=
  interval_of_check _ 544 16 (by decide +kernel)
theorem Check002.part560 : Interval test 560 576 :=
  interval_of_check _ 560 16 (by decide +kernel)
theorem Check002.part576 : Interval test 576 592 :=
  interval_of_check _ 576 16 (by decide +kernel)
theorem Check002.part592 : Interval test 592 608 :=
  interval_of_check _ 592 16 (by decide +kernel)
theorem Check002.part608 : Interval test 608 624 :=
  interval_of_check _ 608 16 (by decide +kernel)
theorem Check002.part624 : Interval test 624 640 :=
  interval_of_check _ 624 16 (by decide +kernel)
theorem Check002.part640 : Interval test 640 656 :=
  interval_of_check _ 640 16 (by decide +kernel)
theorem Check002.part656 : Interval test 656 672 :=
  interval_of_check _ 656 16 (by decide +kernel)
theorem Check002.part672 : Interval test 672 688 :=
  interval_of_check _ 672 16 (by decide +kernel)
theorem Check002.part688 : Interval test 688 704 :=
  interval_of_check _ 688 16 (by decide +kernel)
theorem Check002.part704 : Interval test 704 720 :=
  interval_of_check _ 704 16 (by decide +kernel)
theorem Check002.part720 : Interval test 720 736 :=
  interval_of_check _ 720 16 (by decide +kernel)
theorem Check002.part736 : Interval test 736 752 :=
  interval_of_check _ 736 16 (by decide +kernel)
theorem Check002.part752 : Interval test 752 768 :=
  interval_of_check _ 752 16 (by decide +kernel)
theorem Check002.checked : Interval test 512 768 :=
  (FiniteChecks.interval_append test 512 640 768
  (FiniteChecks.interval_append test 512 576 640
  (FiniteChecks.interval_append test 512 544 576
  (FiniteChecks.interval_append test 512 528 544
  Check002.part512
  Check002.part528)
  (FiniteChecks.interval_append test 544 560 576
  Check002.part544
  Check002.part560))
  (FiniteChecks.interval_append test 576 608 640
  (FiniteChecks.interval_append test 576 592 608
  Check002.part576
  Check002.part592)
  (FiniteChecks.interval_append test 608 624 640
  Check002.part608
  Check002.part624)))
  (FiniteChecks.interval_append test 640 704 768
  (FiniteChecks.interval_append test 640 672 704
  (FiniteChecks.interval_append test 640 656 672
  Check002.part640
  Check002.part656)
  (FiniteChecks.interval_append test 672 688 704
  Check002.part672
  Check002.part688))
  (FiniteChecks.interval_append test 704 736 768
  (FiniteChecks.interval_append test 704 720 736
  Check002.part704
  Check002.part720)
  (FiniteChecks.interval_append test 736 752 768
  Check002.part736
  Check002.part752))))
theorem Check003.part768 : Interval test 768 784 :=
  interval_of_check _ 768 16 (by decide +kernel)
theorem Check003.part784 : Interval test 784 800 :=
  interval_of_check _ 784 16 (by decide +kernel)
theorem Check003.part800 : Interval test 800 816 :=
  interval_of_check _ 800 16 (by decide +kernel)
theorem Check003.part816 : Interval test 816 832 :=
  interval_of_check _ 816 16 (by decide +kernel)
theorem Check003.part832 : Interval test 832 848 :=
  interval_of_check _ 832 16 (by decide +kernel)
theorem Check003.part848 : Interval test 848 864 :=
  interval_of_check _ 848 16 (by decide +kernel)
theorem Check003.part864 : Interval test 864 877 :=
  interval_of_check _ 864 13 (by decide +kernel)
theorem Check003.checked : Interval test 768 877 :=
  (FiniteChecks.interval_append test 768 816 877
  (FiniteChecks.interval_append test 768 784 816
  Check003.part768
  (FiniteChecks.interval_append test 784 800 816
  Check003.part784
  Check003.part800))
  (FiniteChecks.interval_append test 816 848 877
  (FiniteChecks.interval_append test 816 832 848
  Check003.part816
  Check003.part832)
  (FiniteChecks.interval_append test 848 864 877
  Check003.part848
  Check003.part864)))
theorem checked : Interval test 0 877 :=
  (FiniteChecks.interval_append test 0 512 877
  (FiniteChecks.interval_append test 0 256 512
  Check000.checked
  Check001.checked)
  (FiniteChecks.interval_append test 512 768 877
  Check002.checked
  Check003.checked))
theorem key_exact (i : Fin SharedSmallRootCertificates.Row28.rootCount) :
    GraphRoutes.emptyRootKeys.entry (offset + i.val) =
      (28, SharedSmallRootReplay.complement (rootCode i)) := by
  have h := checked i.val (Nat.zero_le _) i.isLt
  simpa only [test, Fin.ofNat_val_eq_self, decide_eq_true_eq] using h
theorem resolved (Result : GraphRouteSelector.Key → Prop)
    (h : ∀ i : Fin SharedSmallRootCertificates.Row28.rootCount,
      Result (28, SharedSmallRootReplay.complement (rootCode i)))
    (i : Fin SharedSmallRootCertificates.Row28.rootCount) :
    Result (GraphRoutes.emptyRootKeys.entry (offset + i.val)) := by
  rw [key_exact i]
  exact h i
end Papers.RationalityTen.SharedEmptyKeys.Row28
