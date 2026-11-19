module
prelude
public import SharedTriangleCountsData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open Papers.RationalityTen FiniteChecks

namespace Papers.RationalityTen.SharedTriangleCounts
theorem Check000.part0 : Interval test 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)
theorem Check000.part8 : Interval test 8 16 :=
  interval_of_check _ 8 8 (by decide +kernel)
theorem Check000.part16 : Interval test 16 24 :=
  interval_of_check _ 16 8 (by decide +kernel)
theorem Check000.part24 : Interval test 24 32 :=
  interval_of_check _ 24 8 (by decide +kernel)
theorem Check000.part32 : Interval test 32 40 :=
  interval_of_check _ 32 8 (by decide +kernel)
theorem Check000.part40 : Interval test 40 48 :=
  interval_of_check _ 40 8 (by decide +kernel)
theorem Check000.part48 : Interval test 48 56 :=
  interval_of_check _ 48 8 (by decide +kernel)
theorem Check000.part56 : Interval test 56 64 :=
  interval_of_check _ 56 8 (by decide +kernel)
theorem Check000.part64 : Interval test 64 72 :=
  interval_of_check _ 64 8 (by decide +kernel)
theorem Check000.part72 : Interval test 72 80 :=
  interval_of_check _ 72 8 (by decide +kernel)
theorem Check000.part80 : Interval test 80 88 :=
  interval_of_check _ 80 8 (by decide +kernel)
theorem Check000.part88 : Interval test 88 96 :=
  interval_of_check _ 88 8 (by decide +kernel)
theorem Check000.part96 : Interval test 96 104 :=
  interval_of_check _ 96 8 (by decide +kernel)
theorem Check000.part104 : Interval test 104 112 :=
  interval_of_check _ 104 8 (by decide +kernel)
theorem Check000.part112 : Interval test 112 120 :=
  interval_of_check _ 112 8 (by decide +kernel)
theorem Check000.part120 : Interval test 120 128 :=
  interval_of_check _ 120 8 (by decide +kernel)
theorem Check000.checked : Interval test 0 128 :=
  (FiniteChecks.interval_append test 0 64 128
  (FiniteChecks.interval_append test 0 32 64
  (FiniteChecks.interval_append test 0 16 32
  (FiniteChecks.interval_append test 0 8 16
  Check000.part0
  Check000.part8)
  (FiniteChecks.interval_append test 16 24 32
  Check000.part16
  Check000.part24))
  (FiniteChecks.interval_append test 32 48 64
  (FiniteChecks.interval_append test 32 40 48
  Check000.part32
  Check000.part40)
  (FiniteChecks.interval_append test 48 56 64
  Check000.part48
  Check000.part56)))
  (FiniteChecks.interval_append test 64 96 128
  (FiniteChecks.interval_append test 64 80 96
  (FiniteChecks.interval_append test 64 72 80
  Check000.part64
  Check000.part72)
  (FiniteChecks.interval_append test 80 88 96
  Check000.part80
  Check000.part88))
  (FiniteChecks.interval_append test 96 112 128
  (FiniteChecks.interval_append test 96 104 112
  Check000.part96
  Check000.part104)
  (FiniteChecks.interval_append test 112 120 128
  Check000.part112
  Check000.part120))))
theorem Check001.part128 : Interval test 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem Check001.part136 : Interval test 136 144 :=
  interval_of_check _ 136 8 (by decide +kernel)
theorem Check001.part144 : Interval test 144 152 :=
  interval_of_check _ 144 8 (by decide +kernel)
theorem Check001.part152 : Interval test 152 160 :=
  interval_of_check _ 152 8 (by decide +kernel)
theorem Check001.part160 : Interval test 160 168 :=
  interval_of_check _ 160 8 (by decide +kernel)
theorem Check001.part168 : Interval test 168 176 :=
  interval_of_check _ 168 8 (by decide +kernel)
theorem Check001.part176 : Interval test 176 184 :=
  interval_of_check _ 176 8 (by decide +kernel)
theorem Check001.part184 : Interval test 184 192 :=
  interval_of_check _ 184 8 (by decide +kernel)
theorem Check001.part192 : Interval test 192 200 :=
  interval_of_check _ 192 8 (by decide +kernel)
theorem Check001.part200 : Interval test 200 208 :=
  interval_of_check _ 200 8 (by decide +kernel)
theorem Check001.part208 : Interval test 208 216 :=
  interval_of_check _ 208 8 (by decide +kernel)
theorem Check001.part216 : Interval test 216 224 :=
  interval_of_check _ 216 8 (by decide +kernel)
theorem Check001.part224 : Interval test 224 232 :=
  interval_of_check _ 224 8 (by decide +kernel)
theorem Check001.part232 : Interval test 232 240 :=
  interval_of_check _ 232 8 (by decide +kernel)
theorem Check001.part240 : Interval test 240 248 :=
  interval_of_check _ 240 8 (by decide +kernel)
theorem Check001.part248 : Interval test 248 256 :=
  interval_of_check _ 248 8 (by decide +kernel)
theorem Check001.checked : Interval test 128 256 :=
  (FiniteChecks.interval_append test 128 192 256
  (FiniteChecks.interval_append test 128 160 192
  (FiniteChecks.interval_append test 128 144 160
  (FiniteChecks.interval_append test 128 136 144
  Check001.part128
  Check001.part136)
  (FiniteChecks.interval_append test 144 152 160
  Check001.part144
  Check001.part152))
  (FiniteChecks.interval_append test 160 176 192
  (FiniteChecks.interval_append test 160 168 176
  Check001.part160
  Check001.part168)
  (FiniteChecks.interval_append test 176 184 192
  Check001.part176
  Check001.part184)))
  (FiniteChecks.interval_append test 192 224 256
  (FiniteChecks.interval_append test 192 208 224
  (FiniteChecks.interval_append test 192 200 208
  Check001.part192
  Check001.part200)
  (FiniteChecks.interval_append test 208 216 224
  Check001.part208
  Check001.part216))
  (FiniteChecks.interval_append test 224 240 256
  (FiniteChecks.interval_append test 224 232 240
  Check001.part224
  Check001.part232)
  (FiniteChecks.interval_append test 240 248 256
  Check001.part240
  Check001.part248))))
theorem Check002.part256 : Interval test 256 264 :=
  interval_of_check _ 256 8 (by decide +kernel)
theorem Check002.part264 : Interval test 264 272 :=
  interval_of_check _ 264 8 (by decide +kernel)
theorem Check002.part272 : Interval test 272 280 :=
  interval_of_check _ 272 8 (by decide +kernel)
theorem Check002.part280 : Interval test 280 288 :=
  interval_of_check _ 280 8 (by decide +kernel)
theorem Check002.part288 : Interval test 288 296 :=
  interval_of_check _ 288 8 (by decide +kernel)
theorem Check002.part296 : Interval test 296 304 :=
  interval_of_check _ 296 8 (by decide +kernel)
theorem Check002.part304 : Interval test 304 312 :=
  interval_of_check _ 304 8 (by decide +kernel)
theorem Check002.part312 : Interval test 312 320 :=
  interval_of_check _ 312 8 (by decide +kernel)
theorem Check002.part320 : Interval test 320 328 :=
  interval_of_check _ 320 8 (by decide +kernel)
theorem Check002.part328 : Interval test 328 336 :=
  interval_of_check _ 328 8 (by decide +kernel)
theorem Check002.part336 : Interval test 336 344 :=
  interval_of_check _ 336 8 (by decide +kernel)
theorem Check002.part344 : Interval test 344 352 :=
  interval_of_check _ 344 8 (by decide +kernel)
theorem Check002.part352 : Interval test 352 360 :=
  interval_of_check _ 352 8 (by decide +kernel)
theorem Check002.part360 : Interval test 360 368 :=
  interval_of_check _ 360 8 (by decide +kernel)
theorem Check002.part368 : Interval test 368 376 :=
  interval_of_check _ 368 8 (by decide +kernel)
theorem Check002.part376 : Interval test 376 384 :=
  interval_of_check _ 376 8 (by decide +kernel)
theorem Check002.checked : Interval test 256 384 :=
  (FiniteChecks.interval_append test 256 320 384
  (FiniteChecks.interval_append test 256 288 320
  (FiniteChecks.interval_append test 256 272 288
  (FiniteChecks.interval_append test 256 264 272
  Check002.part256
  Check002.part264)
  (FiniteChecks.interval_append test 272 280 288
  Check002.part272
  Check002.part280))
  (FiniteChecks.interval_append test 288 304 320
  (FiniteChecks.interval_append test 288 296 304
  Check002.part288
  Check002.part296)
  (FiniteChecks.interval_append test 304 312 320
  Check002.part304
  Check002.part312)))
  (FiniteChecks.interval_append test 320 352 384
  (FiniteChecks.interval_append test 320 336 352
  (FiniteChecks.interval_append test 320 328 336
  Check002.part320
  Check002.part328)
  (FiniteChecks.interval_append test 336 344 352
  Check002.part336
  Check002.part344))
  (FiniteChecks.interval_append test 352 368 384
  (FiniteChecks.interval_append test 352 360 368
  Check002.part352
  Check002.part360)
  (FiniteChecks.interval_append test 368 376 384
  Check002.part368
  Check002.part376))))
theorem Check003.part384 : Interval test 384 392 :=
  interval_of_check _ 384 8 (by decide +kernel)
theorem Check003.part392 : Interval test 392 400 :=
  interval_of_check _ 392 8 (by decide +kernel)
theorem Check003.part400 : Interval test 400 408 :=
  interval_of_check _ 400 8 (by decide +kernel)
theorem Check003.part408 : Interval test 408 416 :=
  interval_of_check _ 408 8 (by decide +kernel)
theorem Check003.part416 : Interval test 416 424 :=
  interval_of_check _ 416 8 (by decide +kernel)
theorem Check003.part424 : Interval test 424 432 :=
  interval_of_check _ 424 8 (by decide +kernel)
theorem Check003.part432 : Interval test 432 440 :=
  interval_of_check _ 432 8 (by decide +kernel)
theorem Check003.part440 : Interval test 440 448 :=
  interval_of_check _ 440 8 (by decide +kernel)
theorem Check003.part448 : Interval test 448 456 :=
  interval_of_check _ 448 8 (by decide +kernel)
theorem Check003.part456 : Interval test 456 464 :=
  interval_of_check _ 456 8 (by decide +kernel)
theorem Check003.part464 : Interval test 464 472 :=
  interval_of_check _ 464 8 (by decide +kernel)
theorem Check003.part472 : Interval test 472 480 :=
  interval_of_check _ 472 8 (by decide +kernel)
theorem Check003.part480 : Interval test 480 488 :=
  interval_of_check _ 480 8 (by decide +kernel)
theorem Check003.part488 : Interval test 488 496 :=
  interval_of_check _ 488 8 (by decide +kernel)
theorem Check003.part496 : Interval test 496 504 :=
  interval_of_check _ 496 8 (by decide +kernel)
theorem Check003.part504 : Interval test 504 512 :=
  interval_of_check _ 504 8 (by decide +kernel)
theorem Check003.checked : Interval test 384 512 :=
  (FiniteChecks.interval_append test 384 448 512
  (FiniteChecks.interval_append test 384 416 448
  (FiniteChecks.interval_append test 384 400 416
  (FiniteChecks.interval_append test 384 392 400
  Check003.part384
  Check003.part392)
  (FiniteChecks.interval_append test 400 408 416
  Check003.part400
  Check003.part408))
  (FiniteChecks.interval_append test 416 432 448
  (FiniteChecks.interval_append test 416 424 432
  Check003.part416
  Check003.part424)
  (FiniteChecks.interval_append test 432 440 448
  Check003.part432
  Check003.part440)))
  (FiniteChecks.interval_append test 448 480 512
  (FiniteChecks.interval_append test 448 464 480
  (FiniteChecks.interval_append test 448 456 464
  Check003.part448
  Check003.part456)
  (FiniteChecks.interval_append test 464 472 480
  Check003.part464
  Check003.part472))
  (FiniteChecks.interval_append test 480 496 512
  (FiniteChecks.interval_append test 480 488 496
  Check003.part480
  Check003.part488)
  (FiniteChecks.interval_append test 496 504 512
  Check003.part496
  Check003.part504))))
theorem Check004.part512 : Interval test 512 520 :=
  interval_of_check _ 512 8 (by decide +kernel)
theorem Check004.part520 : Interval test 520 528 :=
  interval_of_check _ 520 8 (by decide +kernel)
theorem Check004.part528 : Interval test 528 536 :=
  interval_of_check _ 528 8 (by decide +kernel)
theorem Check004.part536 : Interval test 536 544 :=
  interval_of_check _ 536 8 (by decide +kernel)
theorem Check004.part544 : Interval test 544 552 :=
  interval_of_check _ 544 8 (by decide +kernel)
theorem Check004.part552 : Interval test 552 560 :=
  interval_of_check _ 552 8 (by decide +kernel)
theorem Check004.part560 : Interval test 560 568 :=
  interval_of_check _ 560 8 (by decide +kernel)
theorem Check004.part568 : Interval test 568 576 :=
  interval_of_check _ 568 8 (by decide +kernel)
theorem Check004.part576 : Interval test 576 584 :=
  interval_of_check _ 576 8 (by decide +kernel)
theorem Check004.part584 : Interval test 584 592 :=
  interval_of_check _ 584 8 (by decide +kernel)
theorem Check004.part592 : Interval test 592 600 :=
  interval_of_check _ 592 8 (by decide +kernel)
theorem Check004.part600 : Interval test 600 608 :=
  interval_of_check _ 600 8 (by decide +kernel)
theorem Check004.part608 : Interval test 608 616 :=
  interval_of_check _ 608 8 (by decide +kernel)
theorem Check004.part616 : Interval test 616 624 :=
  interval_of_check _ 616 8 (by decide +kernel)
theorem Check004.part624 : Interval test 624 632 :=
  interval_of_check _ 624 8 (by decide +kernel)
theorem Check004.part632 : Interval test 632 640 :=
  interval_of_check _ 632 8 (by decide +kernel)
theorem Check004.checked : Interval test 512 640 :=
  (FiniteChecks.interval_append test 512 576 640
  (FiniteChecks.interval_append test 512 544 576
  (FiniteChecks.interval_append test 512 528 544
  (FiniteChecks.interval_append test 512 520 528
  Check004.part512
  Check004.part520)
  (FiniteChecks.interval_append test 528 536 544
  Check004.part528
  Check004.part536))
  (FiniteChecks.interval_append test 544 560 576
  (FiniteChecks.interval_append test 544 552 560
  Check004.part544
  Check004.part552)
  (FiniteChecks.interval_append test 560 568 576
  Check004.part560
  Check004.part568)))
  (FiniteChecks.interval_append test 576 608 640
  (FiniteChecks.interval_append test 576 592 608
  (FiniteChecks.interval_append test 576 584 592
  Check004.part576
  Check004.part584)
  (FiniteChecks.interval_append test 592 600 608
  Check004.part592
  Check004.part600))
  (FiniteChecks.interval_append test 608 624 640
  (FiniteChecks.interval_append test 608 616 624
  Check004.part608
  Check004.part616)
  (FiniteChecks.interval_append test 624 632 640
  Check004.part624
  Check004.part632))))
theorem Check005.part640 : Interval test 640 648 :=
  interval_of_check _ 640 8 (by decide +kernel)
theorem Check005.part648 : Interval test 648 656 :=
  interval_of_check _ 648 8 (by decide +kernel)
theorem Check005.part656 : Interval test 656 664 :=
  interval_of_check _ 656 8 (by decide +kernel)
theorem Check005.part664 : Interval test 664 672 :=
  interval_of_check _ 664 8 (by decide +kernel)
theorem Check005.part672 : Interval test 672 680 :=
  interval_of_check _ 672 8 (by decide +kernel)
theorem Check005.part680 : Interval test 680 688 :=
  interval_of_check _ 680 8 (by decide +kernel)
theorem Check005.part688 : Interval test 688 696 :=
  interval_of_check _ 688 8 (by decide +kernel)
theorem Check005.part696 : Interval test 696 704 :=
  interval_of_check _ 696 8 (by decide +kernel)
theorem Check005.part704 : Interval test 704 712 :=
  interval_of_check _ 704 8 (by decide +kernel)
theorem Check005.part712 : Interval test 712 720 :=
  interval_of_check _ 712 8 (by decide +kernel)
theorem Check005.part720 : Interval test 720 728 :=
  interval_of_check _ 720 8 (by decide +kernel)
theorem Check005.part728 : Interval test 728 736 :=
  interval_of_check _ 728 8 (by decide +kernel)
theorem Check005.part736 : Interval test 736 744 :=
  interval_of_check _ 736 8 (by decide +kernel)
theorem Check005.part744 : Interval test 744 752 :=
  interval_of_check _ 744 8 (by decide +kernel)
theorem Check005.part752 : Interval test 752 760 :=
  interval_of_check _ 752 8 (by decide +kernel)
theorem Check005.part760 : Interval test 760 768 :=
  interval_of_check _ 760 8 (by decide +kernel)
theorem Check005.checked : Interval test 640 768 :=
  (FiniteChecks.interval_append test 640 704 768
  (FiniteChecks.interval_append test 640 672 704
  (FiniteChecks.interval_append test 640 656 672
  (FiniteChecks.interval_append test 640 648 656
  Check005.part640
  Check005.part648)
  (FiniteChecks.interval_append test 656 664 672
  Check005.part656
  Check005.part664))
  (FiniteChecks.interval_append test 672 688 704
  (FiniteChecks.interval_append test 672 680 688
  Check005.part672
  Check005.part680)
  (FiniteChecks.interval_append test 688 696 704
  Check005.part688
  Check005.part696)))
  (FiniteChecks.interval_append test 704 736 768
  (FiniteChecks.interval_append test 704 720 736
  (FiniteChecks.interval_append test 704 712 720
  Check005.part704
  Check005.part712)
  (FiniteChecks.interval_append test 720 728 736
  Check005.part720
  Check005.part728))
  (FiniteChecks.interval_append test 736 752 768
  (FiniteChecks.interval_append test 736 744 752
  Check005.part736
  Check005.part744)
  (FiniteChecks.interval_append test 752 760 768
  Check005.part752
  Check005.part760))))
theorem Check006.part768 : Interval test 768 776 :=
  interval_of_check _ 768 8 (by decide +kernel)
theorem Check006.part776 : Interval test 776 784 :=
  interval_of_check _ 776 8 (by decide +kernel)
theorem Check006.part784 : Interval test 784 792 :=
  interval_of_check _ 784 8 (by decide +kernel)
theorem Check006.part792 : Interval test 792 800 :=
  interval_of_check _ 792 8 (by decide +kernel)
theorem Check006.part800 : Interval test 800 808 :=
  interval_of_check _ 800 8 (by decide +kernel)
theorem Check006.part808 : Interval test 808 816 :=
  interval_of_check _ 808 8 (by decide +kernel)
theorem Check006.part816 : Interval test 816 824 :=
  interval_of_check _ 816 8 (by decide +kernel)
theorem Check006.part824 : Interval test 824 832 :=
  interval_of_check _ 824 8 (by decide +kernel)
theorem Check006.part832 : Interval test 832 840 :=
  interval_of_check _ 832 8 (by decide +kernel)
theorem Check006.part840 : Interval test 840 848 :=
  interval_of_check _ 840 8 (by decide +kernel)
theorem Check006.part848 : Interval test 848 856 :=
  interval_of_check _ 848 8 (by decide +kernel)
theorem Check006.part856 : Interval test 856 864 :=
  interval_of_check _ 856 8 (by decide +kernel)
theorem Check006.part864 : Interval test 864 872 :=
  interval_of_check _ 864 8 (by decide +kernel)
theorem Check006.part872 : Interval test 872 880 :=
  interval_of_check _ 872 8 (by decide +kernel)
theorem Check006.part880 : Interval test 880 888 :=
  interval_of_check _ 880 8 (by decide +kernel)
theorem Check006.part888 : Interval test 888 896 :=
  interval_of_check _ 888 8 (by decide +kernel)
theorem Check006.checked : Interval test 768 896 :=
  (FiniteChecks.interval_append test 768 832 896
  (FiniteChecks.interval_append test 768 800 832
  (FiniteChecks.interval_append test 768 784 800
  (FiniteChecks.interval_append test 768 776 784
  Check006.part768
  Check006.part776)
  (FiniteChecks.interval_append test 784 792 800
  Check006.part784
  Check006.part792))
  (FiniteChecks.interval_append test 800 816 832
  (FiniteChecks.interval_append test 800 808 816
  Check006.part800
  Check006.part808)
  (FiniteChecks.interval_append test 816 824 832
  Check006.part816
  Check006.part824)))
  (FiniteChecks.interval_append test 832 864 896
  (FiniteChecks.interval_append test 832 848 864
  (FiniteChecks.interval_append test 832 840 848
  Check006.part832
  Check006.part840)
  (FiniteChecks.interval_append test 848 856 864
  Check006.part848
  Check006.part856))
  (FiniteChecks.interval_append test 864 880 896
  (FiniteChecks.interval_append test 864 872 880
  Check006.part864
  Check006.part872)
  (FiniteChecks.interval_append test 880 888 896
  Check006.part880
  Check006.part888))))
theorem Check007.part896 : Interval test 896 904 :=
  interval_of_check _ 896 8 (by decide +kernel)
theorem Check007.part904 : Interval test 904 912 :=
  interval_of_check _ 904 8 (by decide +kernel)
theorem Check007.part912 : Interval test 912 920 :=
  interval_of_check _ 912 8 (by decide +kernel)
theorem Check007.part920 : Interval test 920 928 :=
  interval_of_check _ 920 8 (by decide +kernel)
theorem Check007.part928 : Interval test 928 936 :=
  interval_of_check _ 928 8 (by decide +kernel)
theorem Check007.part936 : Interval test 936 944 :=
  interval_of_check _ 936 8 (by decide +kernel)
theorem Check007.part944 : Interval test 944 952 :=
  interval_of_check _ 944 8 (by decide +kernel)
theorem Check007.part952 : Interval test 952 960 :=
  interval_of_check _ 952 8 (by decide +kernel)
theorem Check007.part960 : Interval test 960 968 :=
  interval_of_check _ 960 8 (by decide +kernel)
theorem Check007.part968 : Interval test 968 976 :=
  interval_of_check _ 968 8 (by decide +kernel)
theorem Check007.part976 : Interval test 976 984 :=
  interval_of_check _ 976 8 (by decide +kernel)
theorem Check007.part984 : Interval test 984 992 :=
  interval_of_check _ 984 8 (by decide +kernel)
theorem Check007.part992 : Interval test 992 1000 :=
  interval_of_check _ 992 8 (by decide +kernel)
theorem Check007.part1000 : Interval test 1000 1008 :=
  interval_of_check _ 1000 8 (by decide +kernel)
theorem Check007.part1008 : Interval test 1008 1016 :=
  interval_of_check _ 1008 8 (by decide +kernel)
theorem Check007.part1016 : Interval test 1016 1024 :=
  interval_of_check _ 1016 8 (by decide +kernel)
theorem Check007.checked : Interval test 896 1024 :=
  (FiniteChecks.interval_append test 896 960 1024
  (FiniteChecks.interval_append test 896 928 960
  (FiniteChecks.interval_append test 896 912 928
  (FiniteChecks.interval_append test 896 904 912
  Check007.part896
  Check007.part904)
  (FiniteChecks.interval_append test 912 920 928
  Check007.part912
  Check007.part920))
  (FiniteChecks.interval_append test 928 944 960
  (FiniteChecks.interval_append test 928 936 944
  Check007.part928
  Check007.part936)
  (FiniteChecks.interval_append test 944 952 960
  Check007.part944
  Check007.part952)))
  (FiniteChecks.interval_append test 960 992 1024
  (FiniteChecks.interval_append test 960 976 992
  (FiniteChecks.interval_append test 960 968 976
  Check007.part960
  Check007.part968)
  (FiniteChecks.interval_append test 976 984 992
  Check007.part976
  Check007.part984))
  (FiniteChecks.interval_append test 992 1008 1024
  (FiniteChecks.interval_append test 992 1000 1008
  Check007.part992
  Check007.part1000)
  (FiniteChecks.interval_append test 1008 1016 1024
  Check007.part1008
  Check007.part1016))))
end Papers.RationalityTen.SharedTriangleCounts
