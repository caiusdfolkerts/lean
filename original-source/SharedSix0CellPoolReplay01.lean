module
prelude
public import SharedSix0CellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check020.part2560 : Interval test 2560 2576 :=
  interval_of_check _ 2560 16 (by decide +kernel)
theorem Check020.part2576 : Interval test 2576 2592 :=
  interval_of_check _ 2576 16 (by decide +kernel)
theorem Check020.part2592 : Interval test 2592 2608 :=
  interval_of_check _ 2592 16 (by decide +kernel)
theorem Check020.part2608 : Interval test 2608 2624 :=
  interval_of_check _ 2608 16 (by decide +kernel)
theorem Check020.part2624 : Interval test 2624 2640 :=
  interval_of_check _ 2624 16 (by decide +kernel)
theorem Check020.part2640 : Interval test 2640 2656 :=
  interval_of_check _ 2640 16 (by decide +kernel)
theorem Check020.part2656 : Interval test 2656 2672 :=
  interval_of_check _ 2656 16 (by decide +kernel)
theorem Check020.part2672 : Interval test 2672 2688 :=
  interval_of_check _ 2672 16 (by decide +kernel)
theorem Check020.checked : Interval test 2560 2688 :=
  (FiniteChecks.interval_append test 2560 2624 2688
  (FiniteChecks.interval_append test 2560 2592 2624
  (FiniteChecks.interval_append test 2560 2576 2592
  Check020.part2560
  Check020.part2576)
  (FiniteChecks.interval_append test 2592 2608 2624
  Check020.part2592
  Check020.part2608))
  (FiniteChecks.interval_append test 2624 2656 2688
  (FiniteChecks.interval_append test 2624 2640 2656
  Check020.part2624
  Check020.part2640)
  (FiniteChecks.interval_append test 2656 2672 2688
  Check020.part2656
  Check020.part2672)))
#print axioms Check020.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check021.part2688 : Interval test 2688 2704 :=
  interval_of_check _ 2688 16 (by decide +kernel)
theorem Check021.part2704 : Interval test 2704 2720 :=
  interval_of_check _ 2704 16 (by decide +kernel)
theorem Check021.part2720 : Interval test 2720 2736 :=
  interval_of_check _ 2720 16 (by decide +kernel)
theorem Check021.part2736 : Interval test 2736 2752 :=
  interval_of_check _ 2736 16 (by decide +kernel)
theorem Check021.part2752 : Interval test 2752 2768 :=
  interval_of_check _ 2752 16 (by decide +kernel)
theorem Check021.part2768 : Interval test 2768 2784 :=
  interval_of_check _ 2768 16 (by decide +kernel)
theorem Check021.part2784 : Interval test 2784 2800 :=
  interval_of_check _ 2784 16 (by decide +kernel)
theorem Check021.part2800 : Interval test 2800 2816 :=
  interval_of_check _ 2800 16 (by decide +kernel)
theorem Check021.checked : Interval test 2688 2816 :=
  (FiniteChecks.interval_append test 2688 2752 2816
  (FiniteChecks.interval_append test 2688 2720 2752
  (FiniteChecks.interval_append test 2688 2704 2720
  Check021.part2688
  Check021.part2704)
  (FiniteChecks.interval_append test 2720 2736 2752
  Check021.part2720
  Check021.part2736))
  (FiniteChecks.interval_append test 2752 2784 2816
  (FiniteChecks.interval_append test 2752 2768 2784
  Check021.part2752
  Check021.part2768)
  (FiniteChecks.interval_append test 2784 2800 2816
  Check021.part2784
  Check021.part2800)))
#print axioms Check021.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check022.part2816 : Interval test 2816 2832 :=
  interval_of_check _ 2816 16 (by decide +kernel)
theorem Check022.part2832 : Interval test 2832 2848 :=
  interval_of_check _ 2832 16 (by decide +kernel)
theorem Check022.part2848 : Interval test 2848 2864 :=
  interval_of_check _ 2848 16 (by decide +kernel)
theorem Check022.part2864 : Interval test 2864 2880 :=
  interval_of_check _ 2864 16 (by decide +kernel)
theorem Check022.part2880 : Interval test 2880 2896 :=
  interval_of_check _ 2880 16 (by decide +kernel)
theorem Check022.part2896 : Interval test 2896 2912 :=
  interval_of_check _ 2896 16 (by decide +kernel)
theorem Check022.part2912 : Interval test 2912 2928 :=
  interval_of_check _ 2912 16 (by decide +kernel)
theorem Check022.part2928 : Interval test 2928 2944 :=
  interval_of_check _ 2928 16 (by decide +kernel)
theorem Check022.checked : Interval test 2816 2944 :=
  (FiniteChecks.interval_append test 2816 2880 2944
  (FiniteChecks.interval_append test 2816 2848 2880
  (FiniteChecks.interval_append test 2816 2832 2848
  Check022.part2816
  Check022.part2832)
  (FiniteChecks.interval_append test 2848 2864 2880
  Check022.part2848
  Check022.part2864))
  (FiniteChecks.interval_append test 2880 2912 2944
  (FiniteChecks.interval_append test 2880 2896 2912
  Check022.part2880
  Check022.part2896)
  (FiniteChecks.interval_append test 2912 2928 2944
  Check022.part2912
  Check022.part2928)))
#print axioms Check022.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check023.part2944 : Interval test 2944 2960 :=
  interval_of_check _ 2944 16 (by decide +kernel)
theorem Check023.part2960 : Interval test 2960 2976 :=
  interval_of_check _ 2960 16 (by decide +kernel)
theorem Check023.part2976 : Interval test 2976 2992 :=
  interval_of_check _ 2976 16 (by decide +kernel)
theorem Check023.part2992 : Interval test 2992 3008 :=
  interval_of_check _ 2992 16 (by decide +kernel)
theorem Check023.part3008 : Interval test 3008 3024 :=
  interval_of_check _ 3008 16 (by decide +kernel)
theorem Check023.part3024 : Interval test 3024 3040 :=
  interval_of_check _ 3024 16 (by decide +kernel)
theorem Check023.part3040 : Interval test 3040 3056 :=
  interval_of_check _ 3040 16 (by decide +kernel)
theorem Check023.part3056 : Interval test 3056 3072 :=
  interval_of_check _ 3056 16 (by decide +kernel)
theorem Check023.checked : Interval test 2944 3072 :=
  (FiniteChecks.interval_append test 2944 3008 3072
  (FiniteChecks.interval_append test 2944 2976 3008
  (FiniteChecks.interval_append test 2944 2960 2976
  Check023.part2944
  Check023.part2960)
  (FiniteChecks.interval_append test 2976 2992 3008
  Check023.part2976
  Check023.part2992))
  (FiniteChecks.interval_append test 3008 3040 3072
  (FiniteChecks.interval_append test 3008 3024 3040
  Check023.part3008
  Check023.part3024)
  (FiniteChecks.interval_append test 3040 3056 3072
  Check023.part3040
  Check023.part3056)))
#print axioms Check023.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check024.part3072 : Interval test 3072 3088 :=
  interval_of_check _ 3072 16 (by decide +kernel)
theorem Check024.part3088 : Interval test 3088 3104 :=
  interval_of_check _ 3088 16 (by decide +kernel)
theorem Check024.part3104 : Interval test 3104 3120 :=
  interval_of_check _ 3104 16 (by decide +kernel)
theorem Check024.part3120 : Interval test 3120 3136 :=
  interval_of_check _ 3120 16 (by decide +kernel)
theorem Check024.part3136 : Interval test 3136 3152 :=
  interval_of_check _ 3136 16 (by decide +kernel)
theorem Check024.part3152 : Interval test 3152 3168 :=
  interval_of_check _ 3152 16 (by decide +kernel)
theorem Check024.part3168 : Interval test 3168 3184 :=
  interval_of_check _ 3168 16 (by decide +kernel)
theorem Check024.part3184 : Interval test 3184 3200 :=
  interval_of_check _ 3184 16 (by decide +kernel)
theorem Check024.checked : Interval test 3072 3200 :=
  (FiniteChecks.interval_append test 3072 3136 3200
  (FiniteChecks.interval_append test 3072 3104 3136
  (FiniteChecks.interval_append test 3072 3088 3104
  Check024.part3072
  Check024.part3088)
  (FiniteChecks.interval_append test 3104 3120 3136
  Check024.part3104
  Check024.part3120))
  (FiniteChecks.interval_append test 3136 3168 3200
  (FiniteChecks.interval_append test 3136 3152 3168
  Check024.part3136
  Check024.part3152)
  (FiniteChecks.interval_append test 3168 3184 3200
  Check024.part3168
  Check024.part3184)))
#print axioms Check024.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check025.part3200 : Interval test 3200 3216 :=
  interval_of_check _ 3200 16 (by decide +kernel)
theorem Check025.part3216 : Interval test 3216 3232 :=
  interval_of_check _ 3216 16 (by decide +kernel)
theorem Check025.part3232 : Interval test 3232 3248 :=
  interval_of_check _ 3232 16 (by decide +kernel)
theorem Check025.part3248 : Interval test 3248 3264 :=
  interval_of_check _ 3248 16 (by decide +kernel)
theorem Check025.part3264 : Interval test 3264 3280 :=
  interval_of_check _ 3264 16 (by decide +kernel)
theorem Check025.part3280 : Interval test 3280 3296 :=
  interval_of_check _ 3280 16 (by decide +kernel)
theorem Check025.part3296 : Interval test 3296 3312 :=
  interval_of_check _ 3296 16 (by decide +kernel)
theorem Check025.part3312 : Interval test 3312 3328 :=
  interval_of_check _ 3312 16 (by decide +kernel)
theorem Check025.checked : Interval test 3200 3328 :=
  (FiniteChecks.interval_append test 3200 3264 3328
  (FiniteChecks.interval_append test 3200 3232 3264
  (FiniteChecks.interval_append test 3200 3216 3232
  Check025.part3200
  Check025.part3216)
  (FiniteChecks.interval_append test 3232 3248 3264
  Check025.part3232
  Check025.part3248))
  (FiniteChecks.interval_append test 3264 3296 3328
  (FiniteChecks.interval_append test 3264 3280 3296
  Check025.part3264
  Check025.part3280)
  (FiniteChecks.interval_append test 3296 3312 3328
  Check025.part3296
  Check025.part3312)))
#print axioms Check025.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check026.part3328 : Interval test 3328 3344 :=
  interval_of_check _ 3328 16 (by decide +kernel)
theorem Check026.part3344 : Interval test 3344 3360 :=
  interval_of_check _ 3344 16 (by decide +kernel)
theorem Check026.part3360 : Interval test 3360 3376 :=
  interval_of_check _ 3360 16 (by decide +kernel)
theorem Check026.part3376 : Interval test 3376 3392 :=
  interval_of_check _ 3376 16 (by decide +kernel)
theorem Check026.part3392 : Interval test 3392 3408 :=
  interval_of_check _ 3392 16 (by decide +kernel)
theorem Check026.part3408 : Interval test 3408 3424 :=
  interval_of_check _ 3408 16 (by decide +kernel)
theorem Check026.part3424 : Interval test 3424 3440 :=
  interval_of_check _ 3424 16 (by decide +kernel)
theorem Check026.part3440 : Interval test 3440 3456 :=
  interval_of_check _ 3440 16 (by decide +kernel)
theorem Check026.checked : Interval test 3328 3456 :=
  (FiniteChecks.interval_append test 3328 3392 3456
  (FiniteChecks.interval_append test 3328 3360 3392
  (FiniteChecks.interval_append test 3328 3344 3360
  Check026.part3328
  Check026.part3344)
  (FiniteChecks.interval_append test 3360 3376 3392
  Check026.part3360
  Check026.part3376))
  (FiniteChecks.interval_append test 3392 3424 3456
  (FiniteChecks.interval_append test 3392 3408 3424
  Check026.part3392
  Check026.part3408)
  (FiniteChecks.interval_append test 3424 3440 3456
  Check026.part3424
  Check026.part3440)))
#print axioms Check026.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check027.part3456 : Interval test 3456 3472 :=
  interval_of_check _ 3456 16 (by decide +kernel)
theorem Check027.part3472 : Interval test 3472 3488 :=
  interval_of_check _ 3472 16 (by decide +kernel)
theorem Check027.part3488 : Interval test 3488 3504 :=
  interval_of_check _ 3488 16 (by decide +kernel)
theorem Check027.part3504 : Interval test 3504 3520 :=
  interval_of_check _ 3504 16 (by decide +kernel)
theorem Check027.part3520 : Interval test 3520 3536 :=
  interval_of_check _ 3520 16 (by decide +kernel)
theorem Check027.part3536 : Interval test 3536 3552 :=
  interval_of_check _ 3536 16 (by decide +kernel)
theorem Check027.part3552 : Interval test 3552 3568 :=
  interval_of_check _ 3552 16 (by decide +kernel)
theorem Check027.part3568 : Interval test 3568 3584 :=
  interval_of_check _ 3568 16 (by decide +kernel)
theorem Check027.checked : Interval test 3456 3584 :=
  (FiniteChecks.interval_append test 3456 3520 3584
  (FiniteChecks.interval_append test 3456 3488 3520
  (FiniteChecks.interval_append test 3456 3472 3488
  Check027.part3456
  Check027.part3472)
  (FiniteChecks.interval_append test 3488 3504 3520
  Check027.part3488
  Check027.part3504))
  (FiniteChecks.interval_append test 3520 3552 3584
  (FiniteChecks.interval_append test 3520 3536 3552
  Check027.part3520
  Check027.part3536)
  (FiniteChecks.interval_append test 3552 3568 3584
  Check027.part3552
  Check027.part3568)))
#print axioms Check027.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check028.part3584 : Interval test 3584 3600 :=
  interval_of_check _ 3584 16 (by decide +kernel)
theorem Check028.part3600 : Interval test 3600 3616 :=
  interval_of_check _ 3600 16 (by decide +kernel)
theorem Check028.part3616 : Interval test 3616 3632 :=
  interval_of_check _ 3616 16 (by decide +kernel)
theorem Check028.part3632 : Interval test 3632 3648 :=
  interval_of_check _ 3632 16 (by decide +kernel)
theorem Check028.part3648 : Interval test 3648 3664 :=
  interval_of_check _ 3648 16 (by decide +kernel)
theorem Check028.part3664 : Interval test 3664 3680 :=
  interval_of_check _ 3664 16 (by decide +kernel)
theorem Check028.part3680 : Interval test 3680 3696 :=
  interval_of_check _ 3680 16 (by decide +kernel)
theorem Check028.part3696 : Interval test 3696 3712 :=
  interval_of_check _ 3696 16 (by decide +kernel)
theorem Check028.checked : Interval test 3584 3712 :=
  (FiniteChecks.interval_append test 3584 3648 3712
  (FiniteChecks.interval_append test 3584 3616 3648
  (FiniteChecks.interval_append test 3584 3600 3616
  Check028.part3584
  Check028.part3600)
  (FiniteChecks.interval_append test 3616 3632 3648
  Check028.part3616
  Check028.part3632))
  (FiniteChecks.interval_append test 3648 3680 3712
  (FiniteChecks.interval_append test 3648 3664 3680
  Check028.part3648
  Check028.part3664)
  (FiniteChecks.interval_append test 3680 3696 3712
  Check028.part3680
  Check028.part3696)))
#print axioms Check028.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check029.part3712 : Interval test 3712 3728 :=
  interval_of_check _ 3712 16 (by decide +kernel)
theorem Check029.part3728 : Interval test 3728 3744 :=
  interval_of_check _ 3728 16 (by decide +kernel)
theorem Check029.part3744 : Interval test 3744 3760 :=
  interval_of_check _ 3744 16 (by decide +kernel)
theorem Check029.part3760 : Interval test 3760 3776 :=
  interval_of_check _ 3760 16 (by decide +kernel)
theorem Check029.part3776 : Interval test 3776 3792 :=
  interval_of_check _ 3776 16 (by decide +kernel)
theorem Check029.part3792 : Interval test 3792 3808 :=
  interval_of_check _ 3792 16 (by decide +kernel)
theorem Check029.part3808 : Interval test 3808 3824 :=
  interval_of_check _ 3808 16 (by decide +kernel)
theorem Check029.part3824 : Interval test 3824 3840 :=
  interval_of_check _ 3824 16 (by decide +kernel)
theorem Check029.checked : Interval test 3712 3840 :=
  (FiniteChecks.interval_append test 3712 3776 3840
  (FiniteChecks.interval_append test 3712 3744 3776
  (FiniteChecks.interval_append test 3712 3728 3744
  Check029.part3712
  Check029.part3728)
  (FiniteChecks.interval_append test 3744 3760 3776
  Check029.part3744
  Check029.part3760))
  (FiniteChecks.interval_append test 3776 3808 3840
  (FiniteChecks.interval_append test 3776 3792 3808
  Check029.part3776
  Check029.part3792)
  (FiniteChecks.interval_append test 3808 3824 3840
  Check029.part3808
  Check029.part3824)))
#print axioms Check029.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check030.part3840 : Interval test 3840 3856 :=
  interval_of_check _ 3840 16 (by decide +kernel)
theorem Check030.part3856 : Interval test 3856 3872 :=
  interval_of_check _ 3856 16 (by decide +kernel)
theorem Check030.part3872 : Interval test 3872 3888 :=
  interval_of_check _ 3872 16 (by decide +kernel)
theorem Check030.part3888 : Interval test 3888 3904 :=
  interval_of_check _ 3888 16 (by decide +kernel)
theorem Check030.part3904 : Interval test 3904 3920 :=
  interval_of_check _ 3904 16 (by decide +kernel)
theorem Check030.part3920 : Interval test 3920 3936 :=
  interval_of_check _ 3920 16 (by decide +kernel)
theorem Check030.part3936 : Interval test 3936 3952 :=
  interval_of_check _ 3936 16 (by decide +kernel)
theorem Check030.part3952 : Interval test 3952 3968 :=
  interval_of_check _ 3952 16 (by decide +kernel)
theorem Check030.checked : Interval test 3840 3968 :=
  (FiniteChecks.interval_append test 3840 3904 3968
  (FiniteChecks.interval_append test 3840 3872 3904
  (FiniteChecks.interval_append test 3840 3856 3872
  Check030.part3840
  Check030.part3856)
  (FiniteChecks.interval_append test 3872 3888 3904
  Check030.part3872
  Check030.part3888))
  (FiniteChecks.interval_append test 3904 3936 3968
  (FiniteChecks.interval_append test 3904 3920 3936
  Check030.part3904
  Check030.part3920)
  (FiniteChecks.interval_append test 3936 3952 3968
  Check030.part3936
  Check030.part3952)))
#print axioms Check030.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check031.part3968 : Interval test 3968 3984 :=
  interval_of_check _ 3968 16 (by decide +kernel)
theorem Check031.part3984 : Interval test 3984 4000 :=
  interval_of_check _ 3984 16 (by decide +kernel)
theorem Check031.part4000 : Interval test 4000 4016 :=
  interval_of_check _ 4000 16 (by decide +kernel)
theorem Check031.part4016 : Interval test 4016 4032 :=
  interval_of_check _ 4016 16 (by decide +kernel)
theorem Check031.part4032 : Interval test 4032 4048 :=
  interval_of_check _ 4032 16 (by decide +kernel)
theorem Check031.part4048 : Interval test 4048 4064 :=
  interval_of_check _ 4048 16 (by decide +kernel)
theorem Check031.part4064 : Interval test 4064 4080 :=
  interval_of_check _ 4064 16 (by decide +kernel)
theorem Check031.part4080 : Interval test 4080 4096 :=
  interval_of_check _ 4080 16 (by decide +kernel)
theorem Check031.checked : Interval test 3968 4096 :=
  (FiniteChecks.interval_append test 3968 4032 4096
  (FiniteChecks.interval_append test 3968 4000 4032
  (FiniteChecks.interval_append test 3968 3984 4000
  Check031.part3968
  Check031.part3984)
  (FiniteChecks.interval_append test 4000 4016 4032
  Check031.part4000
  Check031.part4016))
  (FiniteChecks.interval_append test 4032 4064 4096
  (FiniteChecks.interval_append test 4032 4048 4064
  Check031.part4032
  Check031.part4048)
  (FiniteChecks.interval_append test 4064 4080 4096
  Check031.part4064
  Check031.part4080)))
#print axioms Check031.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check032.part4096 : Interval test 4096 4112 :=
  interval_of_check _ 4096 16 (by decide +kernel)
theorem Check032.part4112 : Interval test 4112 4128 :=
  interval_of_check _ 4112 16 (by decide +kernel)
theorem Check032.part4128 : Interval test 4128 4144 :=
  interval_of_check _ 4128 16 (by decide +kernel)
theorem Check032.part4144 : Interval test 4144 4160 :=
  interval_of_check _ 4144 16 (by decide +kernel)
theorem Check032.part4160 : Interval test 4160 4176 :=
  interval_of_check _ 4160 16 (by decide +kernel)
theorem Check032.part4176 : Interval test 4176 4192 :=
  interval_of_check _ 4176 16 (by decide +kernel)
theorem Check032.part4192 : Interval test 4192 4208 :=
  interval_of_check _ 4192 16 (by decide +kernel)
theorem Check032.part4208 : Interval test 4208 4224 :=
  interval_of_check _ 4208 16 (by decide +kernel)
theorem Check032.checked : Interval test 4096 4224 :=
  (FiniteChecks.interval_append test 4096 4160 4224
  (FiniteChecks.interval_append test 4096 4128 4160
  (FiniteChecks.interval_append test 4096 4112 4128
  Check032.part4096
  Check032.part4112)
  (FiniteChecks.interval_append test 4128 4144 4160
  Check032.part4128
  Check032.part4144))
  (FiniteChecks.interval_append test 4160 4192 4224
  (FiniteChecks.interval_append test 4160 4176 4192
  Check032.part4160
  Check032.part4176)
  (FiniteChecks.interval_append test 4192 4208 4224
  Check032.part4192
  Check032.part4208)))
#print axioms Check032.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check033.part4224 : Interval test 4224 4240 :=
  interval_of_check _ 4224 16 (by decide +kernel)
theorem Check033.part4240 : Interval test 4240 4256 :=
  interval_of_check _ 4240 16 (by decide +kernel)
theorem Check033.part4256 : Interval test 4256 4272 :=
  interval_of_check _ 4256 16 (by decide +kernel)
theorem Check033.part4272 : Interval test 4272 4288 :=
  interval_of_check _ 4272 16 (by decide +kernel)
theorem Check033.part4288 : Interval test 4288 4304 :=
  interval_of_check _ 4288 16 (by decide +kernel)
theorem Check033.part4304 : Interval test 4304 4320 :=
  interval_of_check _ 4304 16 (by decide +kernel)
theorem Check033.part4320 : Interval test 4320 4336 :=
  interval_of_check _ 4320 16 (by decide +kernel)
theorem Check033.part4336 : Interval test 4336 4352 :=
  interval_of_check _ 4336 16 (by decide +kernel)
theorem Check033.checked : Interval test 4224 4352 :=
  (FiniteChecks.interval_append test 4224 4288 4352
  (FiniteChecks.interval_append test 4224 4256 4288
  (FiniteChecks.interval_append test 4224 4240 4256
  Check033.part4224
  Check033.part4240)
  (FiniteChecks.interval_append test 4256 4272 4288
  Check033.part4256
  Check033.part4272))
  (FiniteChecks.interval_append test 4288 4320 4352
  (FiniteChecks.interval_append test 4288 4304 4320
  Check033.part4288
  Check033.part4304)
  (FiniteChecks.interval_append test 4320 4336 4352
  Check033.part4320
  Check033.part4336)))
#print axioms Check033.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check034.part4352 : Interval test 4352 4368 :=
  interval_of_check _ 4352 16 (by decide +kernel)
theorem Check034.part4368 : Interval test 4368 4384 :=
  interval_of_check _ 4368 16 (by decide +kernel)
theorem Check034.part4384 : Interval test 4384 4400 :=
  interval_of_check _ 4384 16 (by decide +kernel)
theorem Check034.part4400 : Interval test 4400 4416 :=
  interval_of_check _ 4400 16 (by decide +kernel)
theorem Check034.part4416 : Interval test 4416 4432 :=
  interval_of_check _ 4416 16 (by decide +kernel)
theorem Check034.part4432 : Interval test 4432 4448 :=
  interval_of_check _ 4432 16 (by decide +kernel)
theorem Check034.part4448 : Interval test 4448 4464 :=
  interval_of_check _ 4448 16 (by decide +kernel)
theorem Check034.part4464 : Interval test 4464 4480 :=
  interval_of_check _ 4464 16 (by decide +kernel)
theorem Check034.checked : Interval test 4352 4480 :=
  (FiniteChecks.interval_append test 4352 4416 4480
  (FiniteChecks.interval_append test 4352 4384 4416
  (FiniteChecks.interval_append test 4352 4368 4384
  Check034.part4352
  Check034.part4368)
  (FiniteChecks.interval_append test 4384 4400 4416
  Check034.part4384
  Check034.part4400))
  (FiniteChecks.interval_append test 4416 4448 4480
  (FiniteChecks.interval_append test 4416 4432 4448
  Check034.part4416
  Check034.part4432)
  (FiniteChecks.interval_append test 4448 4464 4480
  Check034.part4448
  Check034.part4464)))
#print axioms Check034.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check035.part4480 : Interval test 4480 4496 :=
  interval_of_check _ 4480 16 (by decide +kernel)
theorem Check035.part4496 : Interval test 4496 4512 :=
  interval_of_check _ 4496 16 (by decide +kernel)
theorem Check035.part4512 : Interval test 4512 4528 :=
  interval_of_check _ 4512 16 (by decide +kernel)
theorem Check035.part4528 : Interval test 4528 4544 :=
  interval_of_check _ 4528 16 (by decide +kernel)
theorem Check035.part4544 : Interval test 4544 4560 :=
  interval_of_check _ 4544 16 (by decide +kernel)
theorem Check035.part4560 : Interval test 4560 4576 :=
  interval_of_check _ 4560 16 (by decide +kernel)
theorem Check035.part4576 : Interval test 4576 4592 :=
  interval_of_check _ 4576 16 (by decide +kernel)
theorem Check035.part4592 : Interval test 4592 4608 :=
  interval_of_check _ 4592 16 (by decide +kernel)
theorem Check035.checked : Interval test 4480 4608 :=
  (FiniteChecks.interval_append test 4480 4544 4608
  (FiniteChecks.interval_append test 4480 4512 4544
  (FiniteChecks.interval_append test 4480 4496 4512
  Check035.part4480
  Check035.part4496)
  (FiniteChecks.interval_append test 4512 4528 4544
  Check035.part4512
  Check035.part4528))
  (FiniteChecks.interval_append test 4544 4576 4608
  (FiniteChecks.interval_append test 4544 4560 4576
  Check035.part4544
  Check035.part4560)
  (FiniteChecks.interval_append test 4576 4592 4608
  Check035.part4576
  Check035.part4592)))
#print axioms Check035.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check036.part4608 : Interval test 4608 4624 :=
  interval_of_check _ 4608 16 (by decide +kernel)
theorem Check036.part4624 : Interval test 4624 4640 :=
  interval_of_check _ 4624 16 (by decide +kernel)
theorem Check036.part4640 : Interval test 4640 4656 :=
  interval_of_check _ 4640 16 (by decide +kernel)
theorem Check036.part4656 : Interval test 4656 4672 :=
  interval_of_check _ 4656 16 (by decide +kernel)
theorem Check036.part4672 : Interval test 4672 4688 :=
  interval_of_check _ 4672 16 (by decide +kernel)
theorem Check036.part4688 : Interval test 4688 4704 :=
  interval_of_check _ 4688 16 (by decide +kernel)
theorem Check036.part4704 : Interval test 4704 4720 :=
  interval_of_check _ 4704 16 (by decide +kernel)
theorem Check036.part4720 : Interval test 4720 4736 :=
  interval_of_check _ 4720 16 (by decide +kernel)
theorem Check036.checked : Interval test 4608 4736 :=
  (FiniteChecks.interval_append test 4608 4672 4736
  (FiniteChecks.interval_append test 4608 4640 4672
  (FiniteChecks.interval_append test 4608 4624 4640
  Check036.part4608
  Check036.part4624)
  (FiniteChecks.interval_append test 4640 4656 4672
  Check036.part4640
  Check036.part4656))
  (FiniteChecks.interval_append test 4672 4704 4736
  (FiniteChecks.interval_append test 4672 4688 4704
  Check036.part4672
  Check036.part4688)
  (FiniteChecks.interval_append test 4704 4720 4736
  Check036.part4704
  Check036.part4720)))
#print axioms Check036.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check037.part4736 : Interval test 4736 4752 :=
  interval_of_check _ 4736 16 (by decide +kernel)
theorem Check037.part4752 : Interval test 4752 4768 :=
  interval_of_check _ 4752 16 (by decide +kernel)
theorem Check037.part4768 : Interval test 4768 4784 :=
  interval_of_check _ 4768 16 (by decide +kernel)
theorem Check037.part4784 : Interval test 4784 4800 :=
  interval_of_check _ 4784 16 (by decide +kernel)
theorem Check037.part4800 : Interval test 4800 4816 :=
  interval_of_check _ 4800 16 (by decide +kernel)
theorem Check037.part4816 : Interval test 4816 4832 :=
  interval_of_check _ 4816 16 (by decide +kernel)
theorem Check037.part4832 : Interval test 4832 4848 :=
  interval_of_check _ 4832 16 (by decide +kernel)
theorem Check037.part4848 : Interval test 4848 4864 :=
  interval_of_check _ 4848 16 (by decide +kernel)
theorem Check037.checked : Interval test 4736 4864 :=
  (FiniteChecks.interval_append test 4736 4800 4864
  (FiniteChecks.interval_append test 4736 4768 4800
  (FiniteChecks.interval_append test 4736 4752 4768
  Check037.part4736
  Check037.part4752)
  (FiniteChecks.interval_append test 4768 4784 4800
  Check037.part4768
  Check037.part4784))
  (FiniteChecks.interval_append test 4800 4832 4864
  (FiniteChecks.interval_append test 4800 4816 4832
  Check037.part4800
  Check037.part4816)
  (FiniteChecks.interval_append test 4832 4848 4864
  Check037.part4832
  Check037.part4848)))
#print axioms Check037.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check038.part4864 : Interval test 4864 4880 :=
  interval_of_check _ 4864 16 (by decide +kernel)
theorem Check038.part4880 : Interval test 4880 4896 :=
  interval_of_check _ 4880 16 (by decide +kernel)
theorem Check038.part4896 : Interval test 4896 4912 :=
  interval_of_check _ 4896 16 (by decide +kernel)
theorem Check038.part4912 : Interval test 4912 4928 :=
  interval_of_check _ 4912 16 (by decide +kernel)
theorem Check038.part4928 : Interval test 4928 4944 :=
  interval_of_check _ 4928 16 (by decide +kernel)
theorem Check038.part4944 : Interval test 4944 4960 :=
  interval_of_check _ 4944 16 (by decide +kernel)
theorem Check038.part4960 : Interval test 4960 4976 :=
  interval_of_check _ 4960 16 (by decide +kernel)
theorem Check038.part4976 : Interval test 4976 4992 :=
  interval_of_check _ 4976 16 (by decide +kernel)
theorem Check038.checked : Interval test 4864 4992 :=
  (FiniteChecks.interval_append test 4864 4928 4992
  (FiniteChecks.interval_append test 4864 4896 4928
  (FiniteChecks.interval_append test 4864 4880 4896
  Check038.part4864
  Check038.part4880)
  (FiniteChecks.interval_append test 4896 4912 4928
  Check038.part4896
  Check038.part4912))
  (FiniteChecks.interval_append test 4928 4960 4992
  (FiniteChecks.interval_append test 4928 4944 4960
  Check038.part4928
  Check038.part4944)
  (FiniteChecks.interval_append test 4960 4976 4992
  Check038.part4960
  Check038.part4976)))
#print axioms Check038.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSix0CellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check039.part4992 : Interval test 4992 5008 :=
  interval_of_check _ 4992 16 (by decide +kernel)
theorem Check039.part5008 : Interval test 5008 5024 :=
  interval_of_check _ 5008 16 (by decide +kernel)
theorem Check039.part5024 : Interval test 5024 5040 :=
  interval_of_check _ 5024 16 (by decide +kernel)
theorem Check039.part5040 : Interval test 5040 5056 :=
  interval_of_check _ 5040 16 (by decide +kernel)
theorem Check039.part5056 : Interval test 5056 5072 :=
  interval_of_check _ 5056 16 (by decide +kernel)
theorem Check039.part5072 : Interval test 5072 5088 :=
  interval_of_check _ 5072 16 (by decide +kernel)
theorem Check039.part5088 : Interval test 5088 5104 :=
  interval_of_check _ 5088 16 (by decide +kernel)
theorem Check039.part5104 : Interval test 5104 5120 :=
  interval_of_check _ 5104 16 (by decide +kernel)
theorem Check039.checked : Interval test 4992 5120 :=
  (FiniteChecks.interval_append test 4992 5056 5120
  (FiniteChecks.interval_append test 4992 5024 5056
  (FiniteChecks.interval_append test 4992 5008 5024
  Check039.part4992
  Check039.part5008)
  (FiniteChecks.interval_append test 5024 5040 5056
  Check039.part5024
  Check039.part5040))
  (FiniteChecks.interval_append test 5056 5088 5120
  (FiniteChecks.interval_append test 5056 5072 5088
  Check039.part5056
  Check039.part5072)
  (FiniteChecks.interval_append test 5088 5104 5120
  Check039.part5088
  Check039.part5104)))
#print axioms Check039.checked
end Papers.RationalityTen.SharedSix0CellPool

end
end
