module
prelude
public import FastAdjacentMaskData

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FastAdjacentMask
open Papers.RationalityTen ConcreteGrowth FiniteChecks RawBoundaryMatch
theorem test_block_0 : Interval test 0 128 :=
  interval_of_check test 0 128 (by decide +kernel)

theorem test_block_1 : Interval test 128 256 :=
  interval_of_check test 128 128 (by decide +kernel)

theorem test_block_2 : Interval test 256 384 :=
  interval_of_check test 256 128 (by decide +kernel)

theorem test_block_3 : Interval test 384 512 :=
  interval_of_check test 384 128 (by decide +kernel)

theorem test_block_4 : Interval test 512 640 :=
  interval_of_check test 512 128 (by decide +kernel)

theorem test_block_5 : Interval test 640 768 :=
  interval_of_check test 640 128 (by decide +kernel)

theorem test_block_6 : Interval test 768 896 :=
  interval_of_check test 768 128 (by decide +kernel)

theorem test_block_7 : Interval test 896 1024 :=
  interval_of_check test 896 128 (by decide +kernel)

theorem test_block_8 : Interval test 1024 1152 :=
  interval_of_check test 1024 128 (by decide +kernel)

theorem test_block_9 : Interval test 1152 1280 :=
  interval_of_check test 1152 128 (by decide +kernel)

theorem test_block_10 : Interval test 1280 1408 :=
  interval_of_check test 1280 128 (by decide +kernel)

theorem test_block_11 : Interval test 1408 1536 :=
  interval_of_check test 1408 128 (by decide +kernel)

theorem test_block_12 : Interval test 1536 1664 :=
  interval_of_check test 1536 128 (by decide +kernel)

theorem test_block_13 : Interval test 1664 1792 :=
  interval_of_check test 1664 128 (by decide +kernel)

theorem test_block_14 : Interval test 1792 1920 :=
  interval_of_check test 1792 128 (by decide +kernel)

theorem test_block_15 : Interval test 1920 2048 :=
  interval_of_check test 1920 128 (by decide +kernel)

theorem test_block_16 : Interval test 2048 2176 :=
  interval_of_check test 2048 128 (by decide +kernel)

theorem test_block_17 : Interval test 2176 2304 :=
  interval_of_check test 2176 128 (by decide +kernel)

theorem test_block_18 : Interval test 2304 2432 :=
  interval_of_check test 2304 128 (by decide +kernel)

theorem test_block_19 : Interval test 2432 2560 :=
  interval_of_check test 2432 128 (by decide +kernel)

theorem test_block_20 : Interval test 2560 2688 :=
  interval_of_check test 2560 128 (by decide +kernel)

theorem test_block_21 : Interval test 2688 2816 :=
  interval_of_check test 2688 128 (by decide +kernel)

theorem test_block_22 : Interval test 2816 2944 :=
  interval_of_check test 2816 128 (by decide +kernel)

theorem test_block_23 : Interval test 2944 3072 :=
  interval_of_check test 2944 128 (by decide +kernel)

theorem test_block_24 : Interval test 3072 3200 :=
  interval_of_check test 3072 128 (by decide +kernel)

theorem test_block_25 : Interval test 3200 3328 :=
  interval_of_check test 3200 128 (by decide +kernel)

theorem test_block_26 : Interval test 3328 3456 :=
  interval_of_check test 3328 128 (by decide +kernel)

theorem test_block_27 : Interval test 3456 3584 :=
  interval_of_check test 3456 128 (by decide +kernel)

theorem test_block_28 : Interval test 3584 3712 :=
  interval_of_check test 3584 128 (by decide +kernel)

theorem test_block_29 : Interval test 3712 3840 :=
  interval_of_check test 3712 128 (by decide +kernel)

theorem test_block_30 : Interval test 3840 3968 :=
  interval_of_check test 3840 128 (by decide +kernel)

theorem test_block_31 : Interval test 3968 4096 :=
  interval_of_check test 3968 128 (by decide +kernel)

theorem test_block_32 : Interval test 4096 4224 :=
  interval_of_check test 4096 128 (by decide +kernel)

theorem test_block_33 : Interval test 4224 4352 :=
  interval_of_check test 4224 128 (by decide +kernel)

theorem test_block_34 : Interval test 4352 4480 :=
  interval_of_check test 4352 128 (by decide +kernel)

theorem test_block_35 : Interval test 4480 4608 :=
  interval_of_check test 4480 128 (by decide +kernel)

theorem test_block_36 : Interval test 4608 4736 :=
  interval_of_check test 4608 128 (by decide +kernel)

theorem test_block_37 : Interval test 4736 4864 :=
  interval_of_check test 4736 128 (by decide +kernel)

theorem test_block_38 : Interval test 4864 4992 :=
  interval_of_check test 4864 128 (by decide +kernel)

theorem test_block_39 : Interval test 4992 5120 :=
  interval_of_check test 4992 128 (by decide +kernel)

theorem test_block_40 : Interval test 5120 5248 :=
  interval_of_check test 5120 128 (by decide +kernel)

theorem test_block_41 : Interval test 5248 5376 :=
  interval_of_check test 5248 128 (by decide +kernel)

theorem test_block_42 : Interval test 5376 5504 :=
  interval_of_check test 5376 128 (by decide +kernel)

theorem test_block_43 : Interval test 5504 5632 :=
  interval_of_check test 5504 128 (by decide +kernel)

theorem test_block_44 : Interval test 5632 5760 :=
  interval_of_check test 5632 128 (by decide +kernel)

theorem test_block_45 : Interval test 5760 5888 :=
  interval_of_check test 5760 128 (by decide +kernel)

theorem test_block_46 : Interval test 5888 6016 :=
  interval_of_check test 5888 128 (by decide +kernel)

theorem test_block_47 : Interval test 6016 6144 :=
  interval_of_check test 6016 128 (by decide +kernel)

theorem test_block_48 : Interval test 6144 6272 :=
  interval_of_check test 6144 128 (by decide +kernel)

theorem test_block_49 : Interval test 6272 6400 :=
  interval_of_check test 6272 128 (by decide +kernel)

theorem test_block_50 : Interval test 6400 6528 :=
  interval_of_check test 6400 128 (by decide +kernel)

theorem test_block_51 : Interval test 6528 6656 :=
  interval_of_check test 6528 128 (by decide +kernel)

theorem test_block_52 : Interval test 6656 6784 :=
  interval_of_check test 6656 128 (by decide +kernel)

theorem test_block_53 : Interval test 6784 6912 :=
  interval_of_check test 6784 128 (by decide +kernel)

theorem test_block_54 : Interval test 6912 7040 :=
  interval_of_check test 6912 128 (by decide +kernel)

theorem test_block_55 : Interval test 7040 7168 :=
  interval_of_check test 7040 128 (by decide +kernel)

theorem test_block_56 : Interval test 7168 7296 :=
  interval_of_check test 7168 128 (by decide +kernel)

theorem test_block_57 : Interval test 7296 7424 :=
  interval_of_check test 7296 128 (by decide +kernel)

theorem test_block_58 : Interval test 7424 7552 :=
  interval_of_check test 7424 128 (by decide +kernel)

theorem test_block_59 : Interval test 7552 7680 :=
  interval_of_check test 7552 128 (by decide +kernel)

theorem test_block_60 : Interval test 7680 7808 :=
  interval_of_check test 7680 128 (by decide +kernel)

theorem test_block_61 : Interval test 7808 7936 :=
  interval_of_check test 7808 128 (by decide +kernel)

theorem test_block_62 : Interval test 7936 8064 :=
  interval_of_check test 7936 128 (by decide +kernel)

theorem test_block_63 : Interval test 8064 8192 :=
  interval_of_check test 8064 128 (by decide +kernel)

theorem test_block_64 : Interval test 8192 8320 :=
  interval_of_check test 8192 128 (by decide +kernel)

theorem test_block_65 : Interval test 8320 8448 :=
  interval_of_check test 8320 128 (by decide +kernel)

theorem test_block_66 : Interval test 8448 8576 :=
  interval_of_check test 8448 128 (by decide +kernel)

theorem test_block_67 : Interval test 8576 8704 :=
  interval_of_check test 8576 128 (by decide +kernel)

theorem test_block_68 : Interval test 8704 8832 :=
  interval_of_check test 8704 128 (by decide +kernel)

theorem test_block_69 : Interval test 8832 8960 :=
  interval_of_check test 8832 128 (by decide +kernel)

theorem test_block_70 : Interval test 8960 9088 :=
  interval_of_check test 8960 128 (by decide +kernel)

theorem test_block_71 : Interval test 9088 9216 :=
  interval_of_check test 9088 128 (by decide +kernel)

theorem test_complete : Interval test 0 9216 :=
  (interval_append test 0 4608 9216
  (interval_append test 0 2304 4608
  (interval_append test 0 1152 2304
  (interval_append test 0 512 1152
  (interval_append test 0 256 512
  (interval_append test 0 128 256
  test_block_0
  test_block_1)
  (interval_append test 256 384 512
  test_block_2
  test_block_3))
  (interval_append test 512 768 1152
  (interval_append test 512 640 768
  test_block_4
  test_block_5)
  (interval_append test 768 896 1152
  test_block_6
  (interval_append test 896 1024 1152
  test_block_7
  test_block_8))))
  (interval_append test 1152 1664 2304
  (interval_append test 1152 1408 1664
  (interval_append test 1152 1280 1408
  test_block_9
  test_block_10)
  (interval_append test 1408 1536 1664
  test_block_11
  test_block_12))
  (interval_append test 1664 1920 2304
  (interval_append test 1664 1792 1920
  test_block_13
  test_block_14)
  (interval_append test 1920 2048 2304
  test_block_15
  (interval_append test 2048 2176 2304
  test_block_16
  test_block_17)))))
  (interval_append test 2304 3456 4608
  (interval_append test 2304 2816 3456
  (interval_append test 2304 2560 2816
  (interval_append test 2304 2432 2560
  test_block_18
  test_block_19)
  (interval_append test 2560 2688 2816
  test_block_20
  test_block_21))
  (interval_append test 2816 3072 3456
  (interval_append test 2816 2944 3072
  test_block_22
  test_block_23)
  (interval_append test 3072 3200 3456
  test_block_24
  (interval_append test 3200 3328 3456
  test_block_25
  test_block_26))))
  (interval_append test 3456 3968 4608
  (interval_append test 3456 3712 3968
  (interval_append test 3456 3584 3712
  test_block_27
  test_block_28)
  (interval_append test 3712 3840 3968
  test_block_29
  test_block_30))
  (interval_append test 3968 4224 4608
  (interval_append test 3968 4096 4224
  test_block_31
  test_block_32)
  (interval_append test 4224 4352 4608
  test_block_33
  (interval_append test 4352 4480 4608
  test_block_34
  test_block_35))))))
  (interval_append test 4608 6912 9216
  (interval_append test 4608 5760 6912
  (interval_append test 4608 5120 5760
  (interval_append test 4608 4864 5120
  (interval_append test 4608 4736 4864
  test_block_36
  test_block_37)
  (interval_append test 4864 4992 5120
  test_block_38
  test_block_39))
  (interval_append test 5120 5376 5760
  (interval_append test 5120 5248 5376
  test_block_40
  test_block_41)
  (interval_append test 5376 5504 5760
  test_block_42
  (interval_append test 5504 5632 5760
  test_block_43
  test_block_44))))
  (interval_append test 5760 6272 6912
  (interval_append test 5760 6016 6272
  (interval_append test 5760 5888 6016
  test_block_45
  test_block_46)
  (interval_append test 6016 6144 6272
  test_block_47
  test_block_48))
  (interval_append test 6272 6528 6912
  (interval_append test 6272 6400 6528
  test_block_49
  test_block_50)
  (interval_append test 6528 6656 6912
  test_block_51
  (interval_append test 6656 6784 6912
  test_block_52
  test_block_53)))))
  (interval_append test 6912 8064 9216
  (interval_append test 6912 7424 8064
  (interval_append test 6912 7168 7424
  (interval_append test 6912 7040 7168
  test_block_54
  test_block_55)
  (interval_append test 7168 7296 7424
  test_block_56
  test_block_57))
  (interval_append test 7424 7680 8064
  (interval_append test 7424 7552 7680
  test_block_58
  test_block_59)
  (interval_append test 7680 7808 8064
  test_block_60
  (interval_append test 7808 7936 8064
  test_block_61
  test_block_62))))
  (interval_append test 8064 8576 9216
  (interval_append test 8064 8320 8576
  (interval_append test 8064 8192 8320
  test_block_63
  test_block_64)
  (interval_append test 8320 8448 8576
  test_block_65
  test_block_66))
  (interval_append test 8576 8832 9216
  (interval_append test 8576 8704 8832
  test_block_67
  test_block_68)
  (interval_append test 8832 8960 9216
  test_block_69
  (interval_append test 8960 9088 9216
  test_block_70
  test_block_71)))))))
theorem rawSwap_exact (a mask : Nat) (ha : a < 9) (hm : mask < 1024) :
    rawSwap a mask = renameMask (TenGraphEdges.vertexMap (vertexCode a)) mask := by
  have checked := of_decide_eq_true (test_complete (a*1024+mask)
    (Nat.zero_le _) (by omega))
  have hdiv : (a*1024+mask)/1024 = a := by omega
  have hmod : (a*1024+mask)%1024 = mask := by omega
  simpa only [test, hdiv, hmod] using checked
theorem swap_exact (a mask : Nat) :
    swap a mask = renameMask (TenGraphEdges.vertexMap (vertexCode a)) mask := by
  unfold swap
  split
  · next h => exact rawSwap_exact a mask h.1 h.2
  · rfl
def cellRelabelCheck (a : Nat) (A B : Cell) : Bool :=
  ((decide (B.kind = A.kind) && decide (B.vertices = swap a A.vertices)) &&
    sameSetCheck (A.edges.map (swap a)) B.edges) &&
    sameSetCheck (A.ridgeMasks.map (swap a)) B.ridgeMasks
theorem cellRelabelCheck_eq (a : Nat) (A B : Cell) :
    cellRelabelCheck a A B = RawGraphGrowthFrames.cellRelabelCheck
      (TenGraphEdges.vertexMap (vertexCode a)) A B := by
  have hfun : swap a = renameMask (TenGraphEdges.vertexMap (vertexCode a)) :=
    funext (swap_exact a)
  simp only [cellRelabelCheck, RawGraphGrowthFrames.cellRelabelCheck, hfun]
#print axioms cellRelabelCheck_eq

end Papers.RationalityTen.FastAdjacentMask
