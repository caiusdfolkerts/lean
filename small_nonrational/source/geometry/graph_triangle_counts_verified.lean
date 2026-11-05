module
prelude
public import GraphTriangleReplay000
public import GraphTriangleReplay001
public import GraphTriangleReplay002
public import GraphTriangleReplay003
public import GraphTriangleReplay004
public import GraphTriangleReplay005
public import GraphTriangleReplay006
public import GraphTriangleReplay007
public import GraphTriangleReplay008
public import GraphTriangleReplay009
public import GraphTriangleReplay010
public import GraphTriangleReplay011
public import GraphTriangleReplay012
public import GraphRouteSelector
public import GraphRouteCasesData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open Papers.RationalityTen FiniteChecks
namespace Papers.RationalityTen.SharedTriangleCounts
theorem checked : Interval test 0 13309 :=
  (FiniteChecks.interval_append test 0 6656 13309
  (FiniteChecks.interval_append test 0 3328 6656
  (FiniteChecks.interval_append test 0 1664 3328
  (FiniteChecks.interval_append test 0 768 1664
  (FiniteChecks.interval_append test 0 384 768
  (FiniteChecks.interval_append test 0 128 384
  Check000.checked
  (FiniteChecks.interval_append test 128 256 384
  Check001.checked
  Check002.checked))
  (FiniteChecks.interval_append test 384 512 768
  Check003.checked
  (FiniteChecks.interval_append test 512 640 768
  Check004.checked
  Check005.checked)))
  (FiniteChecks.interval_append test 768 1152 1664
  (FiniteChecks.interval_append test 768 896 1152
  Check006.checked
  (FiniteChecks.interval_append test 896 1024 1152
  Check007.checked
  Check008.checked))
  (FiniteChecks.interval_append test 1152 1408 1664
  (FiniteChecks.interval_append test 1152 1280 1408
  Check009.checked
  Check010.checked)
  (FiniteChecks.interval_append test 1408 1536 1664
  Check011.checked
  Check012.checked))))
  (FiniteChecks.interval_append test 1664 2432 3328
  (FiniteChecks.interval_append test 1664 2048 2432
  (FiniteChecks.interval_append test 1664 1792 2048
  Check013.checked
  (FiniteChecks.interval_append test 1792 1920 2048
  Check014.checked
  Check015.checked))
  (FiniteChecks.interval_append test 2048 2176 2432
  Check016.checked
  (FiniteChecks.interval_append test 2176 2304 2432
  Check017.checked
  Check018.checked)))
  (FiniteChecks.interval_append test 2432 2816 3328
  (FiniteChecks.interval_append test 2432 2560 2816
  Check019.checked
  (FiniteChecks.interval_append test 2560 2688 2816
  Check020.checked
  Check021.checked))
  (FiniteChecks.interval_append test 2816 3072 3328
  (FiniteChecks.interval_append test 2816 2944 3072
  Check022.checked
  Check023.checked)
  (FiniteChecks.interval_append test 3072 3200 3328
  Check024.checked
  Check025.checked)))))
  (FiniteChecks.interval_append test 3328 4992 6656
  (FiniteChecks.interval_append test 3328 4096 4992
  (FiniteChecks.interval_append test 3328 3712 4096
  (FiniteChecks.interval_append test 3328 3456 3712
  Check026.checked
  (FiniteChecks.interval_append test 3456 3584 3712
  Check027.checked
  Check028.checked))
  (FiniteChecks.interval_append test 3712 3840 4096
  Check029.checked
  (FiniteChecks.interval_append test 3840 3968 4096
  Check030.checked
  Check031.checked)))
  (FiniteChecks.interval_append test 4096 4480 4992
  (FiniteChecks.interval_append test 4096 4224 4480
  Check032.checked
  (FiniteChecks.interval_append test 4224 4352 4480
  Check033.checked
  Check034.checked))
  (FiniteChecks.interval_append test 4480 4736 4992
  (FiniteChecks.interval_append test 4480 4608 4736
  Check035.checked
  Check036.checked)
  (FiniteChecks.interval_append test 4736 4864 4992
  Check037.checked
  Check038.checked))))
  (FiniteChecks.interval_append test 4992 5760 6656
  (FiniteChecks.interval_append test 4992 5376 5760
  (FiniteChecks.interval_append test 4992 5120 5376
  Check039.checked
  (FiniteChecks.interval_append test 5120 5248 5376
  Check040.checked
  Check041.checked))
  (FiniteChecks.interval_append test 5376 5504 5760
  Check042.checked
  (FiniteChecks.interval_append test 5504 5632 5760
  Check043.checked
  Check044.checked)))
  (FiniteChecks.interval_append test 5760 6144 6656
  (FiniteChecks.interval_append test 5760 5888 6144
  Check045.checked
  (FiniteChecks.interval_append test 5888 6016 6144
  Check046.checked
  Check047.checked))
  (FiniteChecks.interval_append test 6144 6400 6656
  (FiniteChecks.interval_append test 6144 6272 6400
  Check048.checked
  Check049.checked)
  (FiniteChecks.interval_append test 6400 6528 6656
  Check050.checked
  Check051.checked))))))
  (FiniteChecks.interval_append test 6656 9984 13309
  (FiniteChecks.interval_append test 6656 8320 9984
  (FiniteChecks.interval_append test 6656 7424 8320
  (FiniteChecks.interval_append test 6656 7040 7424
  (FiniteChecks.interval_append test 6656 6784 7040
  Check052.checked
  (FiniteChecks.interval_append test 6784 6912 7040
  Check053.checked
  Check054.checked))
  (FiniteChecks.interval_append test 7040 7168 7424
  Check055.checked
  (FiniteChecks.interval_append test 7168 7296 7424
  Check056.checked
  Check057.checked)))
  (FiniteChecks.interval_append test 7424 7808 8320
  (FiniteChecks.interval_append test 7424 7552 7808
  Check058.checked
  (FiniteChecks.interval_append test 7552 7680 7808
  Check059.checked
  Check060.checked))
  (FiniteChecks.interval_append test 7808 8064 8320
  (FiniteChecks.interval_append test 7808 7936 8064
  Check061.checked
  Check062.checked)
  (FiniteChecks.interval_append test 8064 8192 8320
  Check063.checked
  Check064.checked))))
  (FiniteChecks.interval_append test 8320 9088 9984
  (FiniteChecks.interval_append test 8320 8704 9088
  (FiniteChecks.interval_append test 8320 8448 8704
  Check065.checked
  (FiniteChecks.interval_append test 8448 8576 8704
  Check066.checked
  Check067.checked))
  (FiniteChecks.interval_append test 8704 8832 9088
  Check068.checked
  (FiniteChecks.interval_append test 8832 8960 9088
  Check069.checked
  Check070.checked)))
  (FiniteChecks.interval_append test 9088 9472 9984
  (FiniteChecks.interval_append test 9088 9216 9472
  Check071.checked
  (FiniteChecks.interval_append test 9216 9344 9472
  Check072.checked
  Check073.checked))
  (FiniteChecks.interval_append test 9472 9728 9984
  (FiniteChecks.interval_append test 9472 9600 9728
  Check074.checked
  Check075.checked)
  (FiniteChecks.interval_append test 9728 9856 9984
  Check076.checked
  Check077.checked)))))
  (FiniteChecks.interval_append test 9984 11648 13309
  (FiniteChecks.interval_append test 9984 10752 11648
  (FiniteChecks.interval_append test 9984 10368 10752
  (FiniteChecks.interval_append test 9984 10112 10368
  Check078.checked
  (FiniteChecks.interval_append test 10112 10240 10368
  Check079.checked
  Check080.checked))
  (FiniteChecks.interval_append test 10368 10496 10752
  Check081.checked
  (FiniteChecks.interval_append test 10496 10624 10752
  Check082.checked
  Check083.checked)))
  (FiniteChecks.interval_append test 10752 11136 11648
  (FiniteChecks.interval_append test 10752 10880 11136
  Check084.checked
  (FiniteChecks.interval_append test 10880 11008 11136
  Check085.checked
  Check086.checked))
  (FiniteChecks.interval_append test 11136 11392 11648
  (FiniteChecks.interval_append test 11136 11264 11392
  Check087.checked
  Check088.checked)
  (FiniteChecks.interval_append test 11392 11520 11648
  Check089.checked
  Check090.checked))))
  (FiniteChecks.interval_append test 11648 12416 13309
  (FiniteChecks.interval_append test 11648 12032 12416
  (FiniteChecks.interval_append test 11648 11776 12032
  Check091.checked
  (FiniteChecks.interval_append test 11776 11904 12032
  Check092.checked
  Check093.checked))
  (FiniteChecks.interval_append test 12032 12160 12416
  Check094.checked
  (FiniteChecks.interval_append test 12160 12288 12416
  Check095.checked
  Check096.checked)))
  (FiniteChecks.interval_append test 12416 12800 13309
  (FiniteChecks.interval_append test 12416 12544 12800
  Check097.checked
  (FiniteChecks.interval_append test 12544 12672 12800
  Check098.checked
  Check099.checked))
  (FiniteChecks.interval_append test 12800 13056 13309
  (FiniteChecks.interval_append test 12800 12928 13056
  Check100.checked
  Check101.checked)
  (FiniteChecks.interval_append test 13056 13184 13309
  Check102.checked
  Check103.checked)))))))
theorem valid (i : Fin recordCount) : TriangleCountCertificate.Valid (entry i) := by
  apply TriangleCountCertificate.valid_of_check
  have h := checked i.val (Nat.zero_le _) i.isLt
  simpa only [test, Fin.ofNat_val_eq_self] using h
#print axioms valid
end Papers.RationalityTen.SharedTriangleCounts
namespace Papers.RationalityTen.GraphRoutes
theorem triangle_counts_valid : GraphRouteSelector.TriangleCountsValid triangles := by
  intro i hi
  apply TriangleCountCertificate.valid_of_check
  exact SharedTriangleCounts.checked i (Nat.zero_le _) hi
end Papers.RationalityTen.GraphRoutes
