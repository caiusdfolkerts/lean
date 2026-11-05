module
prelude
public import SharedEmptyKeysRow23Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open Papers.RationalityTen FiniteChecks

namespace Papers.RationalityTen.SharedEmptyKeys.Row23
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
theorem Check003.part864 : Interval test 864 880 :=
  interval_of_check _ 864 16 (by decide +kernel)
theorem Check003.part880 : Interval test 880 896 :=
  interval_of_check _ 880 16 (by decide +kernel)
theorem Check003.part896 : Interval test 896 912 :=
  interval_of_check _ 896 16 (by decide +kernel)
theorem Check003.part912 : Interval test 912 928 :=
  interval_of_check _ 912 16 (by decide +kernel)
theorem Check003.part928 : Interval test 928 944 :=
  interval_of_check _ 928 16 (by decide +kernel)
theorem Check003.part944 : Interval test 944 960 :=
  interval_of_check _ 944 16 (by decide +kernel)
theorem Check003.part960 : Interval test 960 976 :=
  interval_of_check _ 960 16 (by decide +kernel)
theorem Check003.part976 : Interval test 976 992 :=
  interval_of_check _ 976 16 (by decide +kernel)
theorem Check003.part992 : Interval test 992 1008 :=
  interval_of_check _ 992 16 (by decide +kernel)
theorem Check003.part1008 : Interval test 1008 1024 :=
  interval_of_check _ 1008 16 (by decide +kernel)
theorem Check003.checked : Interval test 768 1024 :=
  (FiniteChecks.interval_append test 768 896 1024
  (FiniteChecks.interval_append test 768 832 896
  (FiniteChecks.interval_append test 768 800 832
  (FiniteChecks.interval_append test 768 784 800
  Check003.part768
  Check003.part784)
  (FiniteChecks.interval_append test 800 816 832
  Check003.part800
  Check003.part816))
  (FiniteChecks.interval_append test 832 864 896
  (FiniteChecks.interval_append test 832 848 864
  Check003.part832
  Check003.part848)
  (FiniteChecks.interval_append test 864 880 896
  Check003.part864
  Check003.part880)))
  (FiniteChecks.interval_append test 896 960 1024
  (FiniteChecks.interval_append test 896 928 960
  (FiniteChecks.interval_append test 896 912 928
  Check003.part896
  Check003.part912)
  (FiniteChecks.interval_append test 928 944 960
  Check003.part928
  Check003.part944))
  (FiniteChecks.interval_append test 960 992 1024
  (FiniteChecks.interval_append test 960 976 992
  Check003.part960
  Check003.part976)
  (FiniteChecks.interval_append test 992 1008 1024
  Check003.part992
  Check003.part1008))))
theorem Check004.part1024 : Interval test 1024 1040 :=
  interval_of_check _ 1024 16 (by decide +kernel)
theorem Check004.part1040 : Interval test 1040 1056 :=
  interval_of_check _ 1040 16 (by decide +kernel)
theorem Check004.part1056 : Interval test 1056 1072 :=
  interval_of_check _ 1056 16 (by decide +kernel)
theorem Check004.part1072 : Interval test 1072 1088 :=
  interval_of_check _ 1072 16 (by decide +kernel)
theorem Check004.part1088 : Interval test 1088 1104 :=
  interval_of_check _ 1088 16 (by decide +kernel)
theorem Check004.part1104 : Interval test 1104 1120 :=
  interval_of_check _ 1104 16 (by decide +kernel)
theorem Check004.part1120 : Interval test 1120 1136 :=
  interval_of_check _ 1120 16 (by decide +kernel)
theorem Check004.part1136 : Interval test 1136 1152 :=
  interval_of_check _ 1136 16 (by decide +kernel)
theorem Check004.part1152 : Interval test 1152 1168 :=
  interval_of_check _ 1152 16 (by decide +kernel)
theorem Check004.part1168 : Interval test 1168 1184 :=
  interval_of_check _ 1168 16 (by decide +kernel)
theorem Check004.part1184 : Interval test 1184 1200 :=
  interval_of_check _ 1184 16 (by decide +kernel)
theorem Check004.part1200 : Interval test 1200 1216 :=
  interval_of_check _ 1200 16 (by decide +kernel)
theorem Check004.part1216 : Interval test 1216 1232 :=
  interval_of_check _ 1216 16 (by decide +kernel)
theorem Check004.part1232 : Interval test 1232 1248 :=
  interval_of_check _ 1232 16 (by decide +kernel)
theorem Check004.part1248 : Interval test 1248 1264 :=
  interval_of_check _ 1248 16 (by decide +kernel)
theorem Check004.part1264 : Interval test 1264 1280 :=
  interval_of_check _ 1264 16 (by decide +kernel)
theorem Check004.checked : Interval test 1024 1280 :=
  (FiniteChecks.interval_append test 1024 1152 1280
  (FiniteChecks.interval_append test 1024 1088 1152
  (FiniteChecks.interval_append test 1024 1056 1088
  (FiniteChecks.interval_append test 1024 1040 1056
  Check004.part1024
  Check004.part1040)
  (FiniteChecks.interval_append test 1056 1072 1088
  Check004.part1056
  Check004.part1072))
  (FiniteChecks.interval_append test 1088 1120 1152
  (FiniteChecks.interval_append test 1088 1104 1120
  Check004.part1088
  Check004.part1104)
  (FiniteChecks.interval_append test 1120 1136 1152
  Check004.part1120
  Check004.part1136)))
  (FiniteChecks.interval_append test 1152 1216 1280
  (FiniteChecks.interval_append test 1152 1184 1216
  (FiniteChecks.interval_append test 1152 1168 1184
  Check004.part1152
  Check004.part1168)
  (FiniteChecks.interval_append test 1184 1200 1216
  Check004.part1184
  Check004.part1200))
  (FiniteChecks.interval_append test 1216 1248 1280
  (FiniteChecks.interval_append test 1216 1232 1248
  Check004.part1216
  Check004.part1232)
  (FiniteChecks.interval_append test 1248 1264 1280
  Check004.part1248
  Check004.part1264))))
theorem Check005.part1280 : Interval test 1280 1296 :=
  interval_of_check _ 1280 16 (by decide +kernel)
theorem Check005.part1296 : Interval test 1296 1312 :=
  interval_of_check _ 1296 16 (by decide +kernel)
theorem Check005.part1312 : Interval test 1312 1328 :=
  interval_of_check _ 1312 16 (by decide +kernel)
theorem Check005.part1328 : Interval test 1328 1344 :=
  interval_of_check _ 1328 16 (by decide +kernel)
theorem Check005.part1344 : Interval test 1344 1360 :=
  interval_of_check _ 1344 16 (by decide +kernel)
theorem Check005.part1360 : Interval test 1360 1376 :=
  interval_of_check _ 1360 16 (by decide +kernel)
theorem Check005.part1376 : Interval test 1376 1392 :=
  interval_of_check _ 1376 16 (by decide +kernel)
theorem Check005.part1392 : Interval test 1392 1408 :=
  interval_of_check _ 1392 16 (by decide +kernel)
theorem Check005.part1408 : Interval test 1408 1424 :=
  interval_of_check _ 1408 16 (by decide +kernel)
theorem Check005.part1424 : Interval test 1424 1440 :=
  interval_of_check _ 1424 16 (by decide +kernel)
theorem Check005.part1440 : Interval test 1440 1456 :=
  interval_of_check _ 1440 16 (by decide +kernel)
theorem Check005.part1456 : Interval test 1456 1472 :=
  interval_of_check _ 1456 16 (by decide +kernel)
theorem Check005.part1472 : Interval test 1472 1488 :=
  interval_of_check _ 1472 16 (by decide +kernel)
theorem Check005.part1488 : Interval test 1488 1504 :=
  interval_of_check _ 1488 16 (by decide +kernel)
theorem Check005.part1504 : Interval test 1504 1515 :=
  interval_of_check _ 1504 11 (by decide +kernel)
theorem Check005.checked : Interval test 1280 1515 :=
  (FiniteChecks.interval_append test 1280 1392 1515
  (FiniteChecks.interval_append test 1280 1328 1392
  (FiniteChecks.interval_append test 1280 1296 1328
  Check005.part1280
  (FiniteChecks.interval_append test 1296 1312 1328
  Check005.part1296
  Check005.part1312))
  (FiniteChecks.interval_append test 1328 1360 1392
  (FiniteChecks.interval_append test 1328 1344 1360
  Check005.part1328
  Check005.part1344)
  (FiniteChecks.interval_append test 1360 1376 1392
  Check005.part1360
  Check005.part1376)))
  (FiniteChecks.interval_append test 1392 1456 1515
  (FiniteChecks.interval_append test 1392 1424 1456
  (FiniteChecks.interval_append test 1392 1408 1424
  Check005.part1392
  Check005.part1408)
  (FiniteChecks.interval_append test 1424 1440 1456
  Check005.part1424
  Check005.part1440))
  (FiniteChecks.interval_append test 1456 1488 1515
  (FiniteChecks.interval_append test 1456 1472 1488
  Check005.part1456
  Check005.part1472)
  (FiniteChecks.interval_append test 1488 1504 1515
  Check005.part1488
  Check005.part1504))))
theorem checked : Interval test 0 1515 :=
  (FiniteChecks.interval_append test 0 768 1515
  (FiniteChecks.interval_append test 0 256 768
  Check000.checked
  (FiniteChecks.interval_append test 256 512 768
  Check001.checked
  Check002.checked))
  (FiniteChecks.interval_append test 768 1024 1515
  Check003.checked
  (FiniteChecks.interval_append test 1024 1280 1515
  Check004.checked
  Check005.checked)))
theorem key_exact (i : Fin SharedSmallRootCertificates.Row23.rootCount) :
    GraphRoutes.emptyRootKeys.entry (offset + i.val) =
      (23, SharedSmallRootReplay.complement (rootCode i)) := by
  have h := checked i.val (Nat.zero_le _) i.isLt
  simpa only [test, Fin.ofNat_val_eq_self, decide_eq_true_eq] using h
theorem resolved (Result : GraphRouteSelector.Key → Prop)
    (h : ∀ i : Fin SharedSmallRootCertificates.Row23.rootCount,
      Result (23, SharedSmallRootReplay.complement (rootCode i)))
    (i : Fin SharedSmallRootCertificates.Row23.rootCount) :
    Result (GraphRoutes.emptyRootKeys.entry (offset + i.val)) := by
  rw [key_exact i]
  exact h i
end Papers.RationalityTen.SharedEmptyKeys.Row23
