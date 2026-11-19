module
prelude
public import SharedTriangleCountsData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open Papers.RationalityTen FiniteChecks

namespace Papers.RationalityTen.SharedTriangleCounts
theorem Check024.part3072 : Interval test 3072 3080 :=
  interval_of_check _ 3072 8 (by decide +kernel)
theorem Check024.part3080 : Interval test 3080 3088 :=
  interval_of_check _ 3080 8 (by decide +kernel)
theorem Check024.part3088 : Interval test 3088 3096 :=
  interval_of_check _ 3088 8 (by decide +kernel)
theorem Check024.part3096 : Interval test 3096 3104 :=
  interval_of_check _ 3096 8 (by decide +kernel)
theorem Check024.part3104 : Interval test 3104 3112 :=
  interval_of_check _ 3104 8 (by decide +kernel)
theorem Check024.part3112 : Interval test 3112 3120 :=
  interval_of_check _ 3112 8 (by decide +kernel)
theorem Check024.part3120 : Interval test 3120 3128 :=
  interval_of_check _ 3120 8 (by decide +kernel)
theorem Check024.part3128 : Interval test 3128 3136 :=
  interval_of_check _ 3128 8 (by decide +kernel)
theorem Check024.part3136 : Interval test 3136 3144 :=
  interval_of_check _ 3136 8 (by decide +kernel)
theorem Check024.part3144 : Interval test 3144 3152 :=
  interval_of_check _ 3144 8 (by decide +kernel)
theorem Check024.part3152 : Interval test 3152 3160 :=
  interval_of_check _ 3152 8 (by decide +kernel)
theorem Check024.part3160 : Interval test 3160 3168 :=
  interval_of_check _ 3160 8 (by decide +kernel)
theorem Check024.part3168 : Interval test 3168 3176 :=
  interval_of_check _ 3168 8 (by decide +kernel)
theorem Check024.part3176 : Interval test 3176 3184 :=
  interval_of_check _ 3176 8 (by decide +kernel)
theorem Check024.part3184 : Interval test 3184 3192 :=
  interval_of_check _ 3184 8 (by decide +kernel)
theorem Check024.part3192 : Interval test 3192 3200 :=
  interval_of_check _ 3192 8 (by decide +kernel)
theorem Check024.checked : Interval test 3072 3200 :=
  (FiniteChecks.interval_append test 3072 3136 3200
  (FiniteChecks.interval_append test 3072 3104 3136
  (FiniteChecks.interval_append test 3072 3088 3104
  (FiniteChecks.interval_append test 3072 3080 3088
  Check024.part3072
  Check024.part3080)
  (FiniteChecks.interval_append test 3088 3096 3104
  Check024.part3088
  Check024.part3096))
  (FiniteChecks.interval_append test 3104 3120 3136
  (FiniteChecks.interval_append test 3104 3112 3120
  Check024.part3104
  Check024.part3112)
  (FiniteChecks.interval_append test 3120 3128 3136
  Check024.part3120
  Check024.part3128)))
  (FiniteChecks.interval_append test 3136 3168 3200
  (FiniteChecks.interval_append test 3136 3152 3168
  (FiniteChecks.interval_append test 3136 3144 3152
  Check024.part3136
  Check024.part3144)
  (FiniteChecks.interval_append test 3152 3160 3168
  Check024.part3152
  Check024.part3160))
  (FiniteChecks.interval_append test 3168 3184 3200
  (FiniteChecks.interval_append test 3168 3176 3184
  Check024.part3168
  Check024.part3176)
  (FiniteChecks.interval_append test 3184 3192 3200
  Check024.part3184
  Check024.part3192))))
theorem Check025.part3200 : Interval test 3200 3208 :=
  interval_of_check _ 3200 8 (by decide +kernel)
theorem Check025.part3208 : Interval test 3208 3216 :=
  interval_of_check _ 3208 8 (by decide +kernel)
theorem Check025.part3216 : Interval test 3216 3224 :=
  interval_of_check _ 3216 8 (by decide +kernel)
theorem Check025.part3224 : Interval test 3224 3232 :=
  interval_of_check _ 3224 8 (by decide +kernel)
theorem Check025.part3232 : Interval test 3232 3240 :=
  interval_of_check _ 3232 8 (by decide +kernel)
theorem Check025.part3240 : Interval test 3240 3248 :=
  interval_of_check _ 3240 8 (by decide +kernel)
theorem Check025.part3248 : Interval test 3248 3256 :=
  interval_of_check _ 3248 8 (by decide +kernel)
theorem Check025.part3256 : Interval test 3256 3264 :=
  interval_of_check _ 3256 8 (by decide +kernel)
theorem Check025.part3264 : Interval test 3264 3272 :=
  interval_of_check _ 3264 8 (by decide +kernel)
theorem Check025.part3272 : Interval test 3272 3280 :=
  interval_of_check _ 3272 8 (by decide +kernel)
theorem Check025.part3280 : Interval test 3280 3288 :=
  interval_of_check _ 3280 8 (by decide +kernel)
theorem Check025.part3288 : Interval test 3288 3296 :=
  interval_of_check _ 3288 8 (by decide +kernel)
theorem Check025.part3296 : Interval test 3296 3304 :=
  interval_of_check _ 3296 8 (by decide +kernel)
theorem Check025.part3304 : Interval test 3304 3312 :=
  interval_of_check _ 3304 8 (by decide +kernel)
theorem Check025.part3312 : Interval test 3312 3320 :=
  interval_of_check _ 3312 8 (by decide +kernel)
theorem Check025.part3320 : Interval test 3320 3328 :=
  interval_of_check _ 3320 8 (by decide +kernel)
theorem Check025.checked : Interval test 3200 3328 :=
  (FiniteChecks.interval_append test 3200 3264 3328
  (FiniteChecks.interval_append test 3200 3232 3264
  (FiniteChecks.interval_append test 3200 3216 3232
  (FiniteChecks.interval_append test 3200 3208 3216
  Check025.part3200
  Check025.part3208)
  (FiniteChecks.interval_append test 3216 3224 3232
  Check025.part3216
  Check025.part3224))
  (FiniteChecks.interval_append test 3232 3248 3264
  (FiniteChecks.interval_append test 3232 3240 3248
  Check025.part3232
  Check025.part3240)
  (FiniteChecks.interval_append test 3248 3256 3264
  Check025.part3248
  Check025.part3256)))
  (FiniteChecks.interval_append test 3264 3296 3328
  (FiniteChecks.interval_append test 3264 3280 3296
  (FiniteChecks.interval_append test 3264 3272 3280
  Check025.part3264
  Check025.part3272)
  (FiniteChecks.interval_append test 3280 3288 3296
  Check025.part3280
  Check025.part3288))
  (FiniteChecks.interval_append test 3296 3312 3328
  (FiniteChecks.interval_append test 3296 3304 3312
  Check025.part3296
  Check025.part3304)
  (FiniteChecks.interval_append test 3312 3320 3328
  Check025.part3312
  Check025.part3320))))
theorem Check026.part3328 : Interval test 3328 3336 :=
  interval_of_check _ 3328 8 (by decide +kernel)
theorem Check026.part3336 : Interval test 3336 3344 :=
  interval_of_check _ 3336 8 (by decide +kernel)
theorem Check026.part3344 : Interval test 3344 3352 :=
  interval_of_check _ 3344 8 (by decide +kernel)
theorem Check026.part3352 : Interval test 3352 3360 :=
  interval_of_check _ 3352 8 (by decide +kernel)
theorem Check026.part3360 : Interval test 3360 3368 :=
  interval_of_check _ 3360 8 (by decide +kernel)
theorem Check026.part3368 : Interval test 3368 3376 :=
  interval_of_check _ 3368 8 (by decide +kernel)
theorem Check026.part3376 : Interval test 3376 3384 :=
  interval_of_check _ 3376 8 (by decide +kernel)
theorem Check026.part3384 : Interval test 3384 3392 :=
  interval_of_check _ 3384 8 (by decide +kernel)
theorem Check026.part3392 : Interval test 3392 3400 :=
  interval_of_check _ 3392 8 (by decide +kernel)
theorem Check026.part3400 : Interval test 3400 3408 :=
  interval_of_check _ 3400 8 (by decide +kernel)
theorem Check026.part3408 : Interval test 3408 3416 :=
  interval_of_check _ 3408 8 (by decide +kernel)
theorem Check026.part3416 : Interval test 3416 3424 :=
  interval_of_check _ 3416 8 (by decide +kernel)
theorem Check026.part3424 : Interval test 3424 3432 :=
  interval_of_check _ 3424 8 (by decide +kernel)
theorem Check026.part3432 : Interval test 3432 3440 :=
  interval_of_check _ 3432 8 (by decide +kernel)
theorem Check026.part3440 : Interval test 3440 3448 :=
  interval_of_check _ 3440 8 (by decide +kernel)
theorem Check026.part3448 : Interval test 3448 3456 :=
  interval_of_check _ 3448 8 (by decide +kernel)
theorem Check026.checked : Interval test 3328 3456 :=
  (FiniteChecks.interval_append test 3328 3392 3456
  (FiniteChecks.interval_append test 3328 3360 3392
  (FiniteChecks.interval_append test 3328 3344 3360
  (FiniteChecks.interval_append test 3328 3336 3344
  Check026.part3328
  Check026.part3336)
  (FiniteChecks.interval_append test 3344 3352 3360
  Check026.part3344
  Check026.part3352))
  (FiniteChecks.interval_append test 3360 3376 3392
  (FiniteChecks.interval_append test 3360 3368 3376
  Check026.part3360
  Check026.part3368)
  (FiniteChecks.interval_append test 3376 3384 3392
  Check026.part3376
  Check026.part3384)))
  (FiniteChecks.interval_append test 3392 3424 3456
  (FiniteChecks.interval_append test 3392 3408 3424
  (FiniteChecks.interval_append test 3392 3400 3408
  Check026.part3392
  Check026.part3400)
  (FiniteChecks.interval_append test 3408 3416 3424
  Check026.part3408
  Check026.part3416))
  (FiniteChecks.interval_append test 3424 3440 3456
  (FiniteChecks.interval_append test 3424 3432 3440
  Check026.part3424
  Check026.part3432)
  (FiniteChecks.interval_append test 3440 3448 3456
  Check026.part3440
  Check026.part3448))))
theorem Check027.part3456 : Interval test 3456 3464 :=
  interval_of_check _ 3456 8 (by decide +kernel)
theorem Check027.part3464 : Interval test 3464 3472 :=
  interval_of_check _ 3464 8 (by decide +kernel)
theorem Check027.part3472 : Interval test 3472 3480 :=
  interval_of_check _ 3472 8 (by decide +kernel)
theorem Check027.part3480 : Interval test 3480 3488 :=
  interval_of_check _ 3480 8 (by decide +kernel)
theorem Check027.part3488 : Interval test 3488 3496 :=
  interval_of_check _ 3488 8 (by decide +kernel)
theorem Check027.part3496 : Interval test 3496 3504 :=
  interval_of_check _ 3496 8 (by decide +kernel)
theorem Check027.part3504 : Interval test 3504 3512 :=
  interval_of_check _ 3504 8 (by decide +kernel)
theorem Check027.part3512 : Interval test 3512 3520 :=
  interval_of_check _ 3512 8 (by decide +kernel)
theorem Check027.part3520 : Interval test 3520 3528 :=
  interval_of_check _ 3520 8 (by decide +kernel)
theorem Check027.part3528 : Interval test 3528 3536 :=
  interval_of_check _ 3528 8 (by decide +kernel)
theorem Check027.part3536 : Interval test 3536 3544 :=
  interval_of_check _ 3536 8 (by decide +kernel)
theorem Check027.part3544 : Interval test 3544 3552 :=
  interval_of_check _ 3544 8 (by decide +kernel)
theorem Check027.part3552 : Interval test 3552 3560 :=
  interval_of_check _ 3552 8 (by decide +kernel)
theorem Check027.part3560 : Interval test 3560 3568 :=
  interval_of_check _ 3560 8 (by decide +kernel)
theorem Check027.part3568 : Interval test 3568 3576 :=
  interval_of_check _ 3568 8 (by decide +kernel)
theorem Check027.part3576 : Interval test 3576 3584 :=
  interval_of_check _ 3576 8 (by decide +kernel)
theorem Check027.checked : Interval test 3456 3584 :=
  (FiniteChecks.interval_append test 3456 3520 3584
  (FiniteChecks.interval_append test 3456 3488 3520
  (FiniteChecks.interval_append test 3456 3472 3488
  (FiniteChecks.interval_append test 3456 3464 3472
  Check027.part3456
  Check027.part3464)
  (FiniteChecks.interval_append test 3472 3480 3488
  Check027.part3472
  Check027.part3480))
  (FiniteChecks.interval_append test 3488 3504 3520
  (FiniteChecks.interval_append test 3488 3496 3504
  Check027.part3488
  Check027.part3496)
  (FiniteChecks.interval_append test 3504 3512 3520
  Check027.part3504
  Check027.part3512)))
  (FiniteChecks.interval_append test 3520 3552 3584
  (FiniteChecks.interval_append test 3520 3536 3552
  (FiniteChecks.interval_append test 3520 3528 3536
  Check027.part3520
  Check027.part3528)
  (FiniteChecks.interval_append test 3536 3544 3552
  Check027.part3536
  Check027.part3544))
  (FiniteChecks.interval_append test 3552 3568 3584
  (FiniteChecks.interval_append test 3552 3560 3568
  Check027.part3552
  Check027.part3560)
  (FiniteChecks.interval_append test 3568 3576 3584
  Check027.part3568
  Check027.part3576))))
theorem Check028.part3584 : Interval test 3584 3592 :=
  interval_of_check _ 3584 8 (by decide +kernel)
theorem Check028.part3592 : Interval test 3592 3600 :=
  interval_of_check _ 3592 8 (by decide +kernel)
theorem Check028.part3600 : Interval test 3600 3608 :=
  interval_of_check _ 3600 8 (by decide +kernel)
theorem Check028.part3608 : Interval test 3608 3616 :=
  interval_of_check _ 3608 8 (by decide +kernel)
theorem Check028.part3616 : Interval test 3616 3624 :=
  interval_of_check _ 3616 8 (by decide +kernel)
theorem Check028.part3624 : Interval test 3624 3632 :=
  interval_of_check _ 3624 8 (by decide +kernel)
theorem Check028.part3632 : Interval test 3632 3640 :=
  interval_of_check _ 3632 8 (by decide +kernel)
theorem Check028.part3640 : Interval test 3640 3648 :=
  interval_of_check _ 3640 8 (by decide +kernel)
theorem Check028.part3648 : Interval test 3648 3656 :=
  interval_of_check _ 3648 8 (by decide +kernel)
theorem Check028.part3656 : Interval test 3656 3664 :=
  interval_of_check _ 3656 8 (by decide +kernel)
theorem Check028.part3664 : Interval test 3664 3672 :=
  interval_of_check _ 3664 8 (by decide +kernel)
theorem Check028.part3672 : Interval test 3672 3680 :=
  interval_of_check _ 3672 8 (by decide +kernel)
theorem Check028.part3680 : Interval test 3680 3688 :=
  interval_of_check _ 3680 8 (by decide +kernel)
theorem Check028.part3688 : Interval test 3688 3696 :=
  interval_of_check _ 3688 8 (by decide +kernel)
theorem Check028.part3696 : Interval test 3696 3704 :=
  interval_of_check _ 3696 8 (by decide +kernel)
theorem Check028.part3704 : Interval test 3704 3712 :=
  interval_of_check _ 3704 8 (by decide +kernel)
theorem Check028.checked : Interval test 3584 3712 :=
  (FiniteChecks.interval_append test 3584 3648 3712
  (FiniteChecks.interval_append test 3584 3616 3648
  (FiniteChecks.interval_append test 3584 3600 3616
  (FiniteChecks.interval_append test 3584 3592 3600
  Check028.part3584
  Check028.part3592)
  (FiniteChecks.interval_append test 3600 3608 3616
  Check028.part3600
  Check028.part3608))
  (FiniteChecks.interval_append test 3616 3632 3648
  (FiniteChecks.interval_append test 3616 3624 3632
  Check028.part3616
  Check028.part3624)
  (FiniteChecks.interval_append test 3632 3640 3648
  Check028.part3632
  Check028.part3640)))
  (FiniteChecks.interval_append test 3648 3680 3712
  (FiniteChecks.interval_append test 3648 3664 3680
  (FiniteChecks.interval_append test 3648 3656 3664
  Check028.part3648
  Check028.part3656)
  (FiniteChecks.interval_append test 3664 3672 3680
  Check028.part3664
  Check028.part3672))
  (FiniteChecks.interval_append test 3680 3696 3712
  (FiniteChecks.interval_append test 3680 3688 3696
  Check028.part3680
  Check028.part3688)
  (FiniteChecks.interval_append test 3696 3704 3712
  Check028.part3696
  Check028.part3704))))
theorem Check029.part3712 : Interval test 3712 3720 :=
  interval_of_check _ 3712 8 (by decide +kernel)
theorem Check029.part3720 : Interval test 3720 3728 :=
  interval_of_check _ 3720 8 (by decide +kernel)
theorem Check029.part3728 : Interval test 3728 3736 :=
  interval_of_check _ 3728 8 (by decide +kernel)
theorem Check029.part3736 : Interval test 3736 3744 :=
  interval_of_check _ 3736 8 (by decide +kernel)
theorem Check029.part3744 : Interval test 3744 3752 :=
  interval_of_check _ 3744 8 (by decide +kernel)
theorem Check029.part3752 : Interval test 3752 3760 :=
  interval_of_check _ 3752 8 (by decide +kernel)
theorem Check029.part3760 : Interval test 3760 3768 :=
  interval_of_check _ 3760 8 (by decide +kernel)
theorem Check029.part3768 : Interval test 3768 3776 :=
  interval_of_check _ 3768 8 (by decide +kernel)
theorem Check029.part3776 : Interval test 3776 3784 :=
  interval_of_check _ 3776 8 (by decide +kernel)
theorem Check029.part3784 : Interval test 3784 3792 :=
  interval_of_check _ 3784 8 (by decide +kernel)
theorem Check029.part3792 : Interval test 3792 3800 :=
  interval_of_check _ 3792 8 (by decide +kernel)
theorem Check029.part3800 : Interval test 3800 3808 :=
  interval_of_check _ 3800 8 (by decide +kernel)
theorem Check029.part3808 : Interval test 3808 3816 :=
  interval_of_check _ 3808 8 (by decide +kernel)
theorem Check029.part3816 : Interval test 3816 3824 :=
  interval_of_check _ 3816 8 (by decide +kernel)
theorem Check029.part3824 : Interval test 3824 3832 :=
  interval_of_check _ 3824 8 (by decide +kernel)
theorem Check029.part3832 : Interval test 3832 3840 :=
  interval_of_check _ 3832 8 (by decide +kernel)
theorem Check029.checked : Interval test 3712 3840 :=
  (FiniteChecks.interval_append test 3712 3776 3840
  (FiniteChecks.interval_append test 3712 3744 3776
  (FiniteChecks.interval_append test 3712 3728 3744
  (FiniteChecks.interval_append test 3712 3720 3728
  Check029.part3712
  Check029.part3720)
  (FiniteChecks.interval_append test 3728 3736 3744
  Check029.part3728
  Check029.part3736))
  (FiniteChecks.interval_append test 3744 3760 3776
  (FiniteChecks.interval_append test 3744 3752 3760
  Check029.part3744
  Check029.part3752)
  (FiniteChecks.interval_append test 3760 3768 3776
  Check029.part3760
  Check029.part3768)))
  (FiniteChecks.interval_append test 3776 3808 3840
  (FiniteChecks.interval_append test 3776 3792 3808
  (FiniteChecks.interval_append test 3776 3784 3792
  Check029.part3776
  Check029.part3784)
  (FiniteChecks.interval_append test 3792 3800 3808
  Check029.part3792
  Check029.part3800))
  (FiniteChecks.interval_append test 3808 3824 3840
  (FiniteChecks.interval_append test 3808 3816 3824
  Check029.part3808
  Check029.part3816)
  (FiniteChecks.interval_append test 3824 3832 3840
  Check029.part3824
  Check029.part3832))))
theorem Check030.part3840 : Interval test 3840 3848 :=
  interval_of_check _ 3840 8 (by decide +kernel)
theorem Check030.part3848 : Interval test 3848 3856 :=
  interval_of_check _ 3848 8 (by decide +kernel)
theorem Check030.part3856 : Interval test 3856 3864 :=
  interval_of_check _ 3856 8 (by decide +kernel)
theorem Check030.part3864 : Interval test 3864 3872 :=
  interval_of_check _ 3864 8 (by decide +kernel)
theorem Check030.part3872 : Interval test 3872 3880 :=
  interval_of_check _ 3872 8 (by decide +kernel)
theorem Check030.part3880 : Interval test 3880 3888 :=
  interval_of_check _ 3880 8 (by decide +kernel)
theorem Check030.part3888 : Interval test 3888 3896 :=
  interval_of_check _ 3888 8 (by decide +kernel)
theorem Check030.part3896 : Interval test 3896 3904 :=
  interval_of_check _ 3896 8 (by decide +kernel)
theorem Check030.part3904 : Interval test 3904 3912 :=
  interval_of_check _ 3904 8 (by decide +kernel)
theorem Check030.part3912 : Interval test 3912 3920 :=
  interval_of_check _ 3912 8 (by decide +kernel)
theorem Check030.part3920 : Interval test 3920 3928 :=
  interval_of_check _ 3920 8 (by decide +kernel)
theorem Check030.part3928 : Interval test 3928 3936 :=
  interval_of_check _ 3928 8 (by decide +kernel)
theorem Check030.part3936 : Interval test 3936 3944 :=
  interval_of_check _ 3936 8 (by decide +kernel)
theorem Check030.part3944 : Interval test 3944 3952 :=
  interval_of_check _ 3944 8 (by decide +kernel)
theorem Check030.part3952 : Interval test 3952 3960 :=
  interval_of_check _ 3952 8 (by decide +kernel)
theorem Check030.part3960 : Interval test 3960 3968 :=
  interval_of_check _ 3960 8 (by decide +kernel)
theorem Check030.checked : Interval test 3840 3968 :=
  (FiniteChecks.interval_append test 3840 3904 3968
  (FiniteChecks.interval_append test 3840 3872 3904
  (FiniteChecks.interval_append test 3840 3856 3872
  (FiniteChecks.interval_append test 3840 3848 3856
  Check030.part3840
  Check030.part3848)
  (FiniteChecks.interval_append test 3856 3864 3872
  Check030.part3856
  Check030.part3864))
  (FiniteChecks.interval_append test 3872 3888 3904
  (FiniteChecks.interval_append test 3872 3880 3888
  Check030.part3872
  Check030.part3880)
  (FiniteChecks.interval_append test 3888 3896 3904
  Check030.part3888
  Check030.part3896)))
  (FiniteChecks.interval_append test 3904 3936 3968
  (FiniteChecks.interval_append test 3904 3920 3936
  (FiniteChecks.interval_append test 3904 3912 3920
  Check030.part3904
  Check030.part3912)
  (FiniteChecks.interval_append test 3920 3928 3936
  Check030.part3920
  Check030.part3928))
  (FiniteChecks.interval_append test 3936 3952 3968
  (FiniteChecks.interval_append test 3936 3944 3952
  Check030.part3936
  Check030.part3944)
  (FiniteChecks.interval_append test 3952 3960 3968
  Check030.part3952
  Check030.part3960))))
theorem Check031.part3968 : Interval test 3968 3976 :=
  interval_of_check _ 3968 8 (by decide +kernel)
theorem Check031.part3976 : Interval test 3976 3984 :=
  interval_of_check _ 3976 8 (by decide +kernel)
theorem Check031.part3984 : Interval test 3984 3992 :=
  interval_of_check _ 3984 8 (by decide +kernel)
theorem Check031.part3992 : Interval test 3992 4000 :=
  interval_of_check _ 3992 8 (by decide +kernel)
theorem Check031.part4000 : Interval test 4000 4008 :=
  interval_of_check _ 4000 8 (by decide +kernel)
theorem Check031.part4008 : Interval test 4008 4016 :=
  interval_of_check _ 4008 8 (by decide +kernel)
theorem Check031.part4016 : Interval test 4016 4024 :=
  interval_of_check _ 4016 8 (by decide +kernel)
theorem Check031.part4024 : Interval test 4024 4032 :=
  interval_of_check _ 4024 8 (by decide +kernel)
theorem Check031.part4032 : Interval test 4032 4040 :=
  interval_of_check _ 4032 8 (by decide +kernel)
theorem Check031.part4040 : Interval test 4040 4048 :=
  interval_of_check _ 4040 8 (by decide +kernel)
theorem Check031.part4048 : Interval test 4048 4056 :=
  interval_of_check _ 4048 8 (by decide +kernel)
theorem Check031.part4056 : Interval test 4056 4064 :=
  interval_of_check _ 4056 8 (by decide +kernel)
theorem Check031.part4064 : Interval test 4064 4072 :=
  interval_of_check _ 4064 8 (by decide +kernel)
theorem Check031.part4072 : Interval test 4072 4080 :=
  interval_of_check _ 4072 8 (by decide +kernel)
theorem Check031.part4080 : Interval test 4080 4088 :=
  interval_of_check _ 4080 8 (by decide +kernel)
theorem Check031.part4088 : Interval test 4088 4096 :=
  interval_of_check _ 4088 8 (by decide +kernel)
theorem Check031.checked : Interval test 3968 4096 :=
  (FiniteChecks.interval_append test 3968 4032 4096
  (FiniteChecks.interval_append test 3968 4000 4032
  (FiniteChecks.interval_append test 3968 3984 4000
  (FiniteChecks.interval_append test 3968 3976 3984
  Check031.part3968
  Check031.part3976)
  (FiniteChecks.interval_append test 3984 3992 4000
  Check031.part3984
  Check031.part3992))
  (FiniteChecks.interval_append test 4000 4016 4032
  (FiniteChecks.interval_append test 4000 4008 4016
  Check031.part4000
  Check031.part4008)
  (FiniteChecks.interval_append test 4016 4024 4032
  Check031.part4016
  Check031.part4024)))
  (FiniteChecks.interval_append test 4032 4064 4096
  (FiniteChecks.interval_append test 4032 4048 4064
  (FiniteChecks.interval_append test 4032 4040 4048
  Check031.part4032
  Check031.part4040)
  (FiniteChecks.interval_append test 4048 4056 4064
  Check031.part4048
  Check031.part4056))
  (FiniteChecks.interval_append test 4064 4080 4096
  (FiniteChecks.interval_append test 4064 4072 4080
  Check031.part4064
  Check031.part4072)
  (FiniteChecks.interval_append test 4080 4088 4096
  Check031.part4080
  Check031.part4088))))
end Papers.RationalityTen.SharedTriangleCounts
