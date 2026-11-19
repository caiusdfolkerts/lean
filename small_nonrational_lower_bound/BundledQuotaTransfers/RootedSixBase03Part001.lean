module
prelude
public import BundledQuotaTransfers.RootedSixBase03Part000
public import QuotaLeafTransfer
public import FiniteChecks
public import RootedSubsumedForest0717Dispositions
public import RootedSubsumedForest0724Data

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- Original module: RootedQuotaTransfer0716Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0716
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 16 :=
  interval_of_check test0 0 16 (by decide +kernel)

theorem test0_block_1 : Interval test0 16 32 :=
  interval_of_check test0 16 16 (by decide +kernel)

theorem test0_block_2 : Interval test0 32 48 :=
  interval_of_check test0 32 16 (by decide +kernel)

theorem test0_block_3 : Interval test0 48 64 :=
  interval_of_check test0 48 16 (by decide +kernel)

theorem test0_block_4 : Interval test0 64 80 :=
  interval_of_check test0 64 16 (by decide +kernel)

theorem test0_block_5 : Interval test0 80 96 :=
  interval_of_check test0 80 16 (by decide +kernel)

theorem test0_block_6 : Interval test0 96 112 :=
  interval_of_check test0 96 16 (by decide +kernel)

theorem test0_block_7 : Interval test0 112 128 :=
  interval_of_check test0 112 16 (by decide +kernel)

theorem test0_complete : Interval test0 0 128 :=
  (interval_append test0 0 64 128
  (interval_append test0 0 32 64
  (interval_append test0 0 16 32
  test0_block_0
  test0_block_1)
  (interval_append test0 32 48 64
  test0_block_2
  test0_block_3))
  (interval_append test0 64 96 128
  (interval_append test0 64 80 96
  test0_block_4
  test0_block_5)
  (interval_append test0 96 112 128
  test0_block_6
  test0_block_7)))
theorem routeInterval0 : Interval routeTest 0 128 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0716

/- Original module: RootedQuotaTransfer0716Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0716
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test128 (i : Nat) := routeTest (i + 128)
theorem test128_block_0 : Interval test128 0 16 :=
  interval_of_check test128 0 16 (by decide +kernel)

theorem test128_block_1 : Interval test128 16 32 :=
  interval_of_check test128 16 16 (by decide +kernel)

theorem test128_block_2 : Interval test128 32 48 :=
  interval_of_check test128 32 16 (by decide +kernel)

theorem test128_block_3 : Interval test128 48 52 :=
  interval_of_check test128 48 4 (by decide +kernel)

theorem test128_complete : Interval test128 0 52 :=
  (interval_append test128 0 32 52
  (interval_append test128 0 16 32
  test128_block_0
  test128_block_1)
  (interval_append test128 32 48 52
  test128_block_2
  test128_block_3))
theorem routeInterval128 : Interval routeTest 128 180 := by
  intro i hlo hhi
  have h := test128_complete (i - 128) (Nat.zero_le _) (by omega)
  simpa only [test128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0716

/- Original module: RootedQuotaTransfer0716. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0716
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 180 :=
  (interval_append routeTest 0 128 180
  routeInterval0
  routeInterval128)

theorem disposition_checked (j : Fin 180) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0716.quota
      ((RootedForests.RootedSubsumedForest0721.rawLeaves j.val).map RootedCaches.RootedSixBase03.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0716.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0716.rawLeaves 30 RootedForests.RootedSubsumedForest0716.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0716.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0721.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0716

/- Original module: RootedQuotaTransfer0717Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0717
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 717: use the complete forest for case 724, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0717.quota k ≤ RootedForests.RootedSubsumedForest0724.quota k := by
  match k with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | 2 => decide +kernel
  | 3 => decide +kernel
  | 4 => decide +kernel
  | 5 => decide +kernel
  | 6 => decide +kernel
  | 7 => decide +kernel
  | 8 => decide +kernel
  | 9 => decide +kernel
  | 10 => decide +kernel
  | n + 11 => exact Nat.le_refl 0

def routes : Table Route :=
(.branch 1714
 (.branch 857
 (.branch 428
 (.leaf (.quota 1))
 (.branch 642
 (.branch 535
 (.leaf (.quota 1))
 (.branch 588
 (.leaf (.quota 1))
 (.branch 615
 (.branch 601
 (.branch 594
 (.leaf (.quota 1))
 (.branch 597
 (.leaf (.quota 1))
 (.branch 599
 (.branch 598
 (.leaf (.quota 1))
 (.leaf (.reuse 0)))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 749
 (.branch 695
 (.branch 668
 (.leaf (.quota 1))
 (.branch 681
 (.leaf (.quota 1))
 (.branch 688
 (.branch 684
 (.branch 682
 (.leaf (.quota 1))
 (.branch 683
 (.leaf (.reuse 1))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.branch 803
 (.leaf (.quota 1))
 (.branch 830
 (.leaf (.quota 1))
 (.branch 843
 (.branch 836
 (.leaf (.quota 1))
 (.branch 839
 (.branch 837
 (.leaf (.quota 1))
 (.branch 838
 (.leaf (.quota 1))
 (.leaf (.reuse 2))))
 (.branch 841
 (.branch 840
 (.leaf (.reuse 3))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 850
 (.branch 846
 (.leaf (.quota 1))
 (.branch 848
 (.branch 847
 (.leaf (.reuse 4))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 853
 (.leaf (.quota 1))
 (.branch 855
 (.leaf (.quota 1))
 (.branch 856
 (.leaf (.quota 1))
 (.leaf (.reuse 5))))))))))))
 (.branch 1285
 (.branch 1071
 (.branch 964
 (.branch 910
 (.branch 883
 (.branch 870
 (.leaf (.quota 1))
 (.branch 876
 (.branch 873
 (.branch 871
 (.leaf (.reuse 6))
 (.leaf (.quota 1)))
 (.branch 874
 (.leaf (.quota 1))
 (.branch 875
 (.leaf (.quota 1))
 (.leaf (.reuse 7)))))
 (.leaf (.quota 1))))
 (.branch 896
 (.branch 889
 (.leaf (.quota 1))
 (.branch 892
 (.leaf (.quota 1))
 (.branch 894
 (.leaf (.quota 1))
 (.branch 895
 (.leaf (.reuse 8))
 (.leaf (.quota 1))))))
 (.leaf (.quota 1))))
 (.branch 937
 (.leaf (.quota 1))
 (.branch 950
 (.leaf (.quota 1))
 (.branch 957
 (.leaf (.quota 1))
 (.branch 960
 (.branch 958
 (.leaf (.reuse 10))
 (.branch 959
 (.leaf (.quota 1))
 (.leaf (.reuse 11))))
 (.leaf (.quota 1)))))))
 (.branch 1017
 (.branch 990
 (.branch 977
 (.leaf (.quota 1))
 (.branch 983
 (.leaf (.quota 1))
 (.branch 986
 (.leaf (.quota 1))
 (.branch 988
 (.leaf (.quota 1))
 (.branch 989
 (.leaf (.quota 1))
 (.leaf (.reuse 12)))))))
 (.branch 1003
 (.leaf (.quota 1))
 (.branch 1010
 (.leaf (.quota 1))
 (.branch 1013
 (.leaf (.quota 1))
 (.branch 1015
 (.leaf (.quota 1))
 (.branch 1016
 (.leaf (.reuse 13))
 (.leaf (.quota 1))))))))
 (.branch 1044
 (.branch 1030
 (.branch 1023
 (.branch 1020
 (.leaf (.quota 1))
 (.branch 1021
 (.leaf (.quota 1))
 (.branch 1022
 (.leaf (.reuse 14))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 1178
 (.branch 1124
 (.branch 1097
 (.leaf (.quota 1))
 (.branch 1110
 (.leaf (.quota 1))
 (.branch 1117
 (.branch 1113
 (.branch 1111
 (.leaf (.quota 1))
 (.branch 1112
 (.leaf (.quota 1))
 (.leaf (.reuse 15))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.branch 1231
 (.branch 1204
 (.branch 1191
 (.branch 1184
 (.leaf (.quota 1))
 (.branch 1187
 (.branch 1185
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 1197
 (.leaf (.quota 1))
 (.branch 1200
 (.branch 1198
 (.leaf (.quota 1))
 (.branch 1199
 (.leaf (.reuse 17))
 (.leaf (.reuse 18))))
 (.leaf (.quota 1)))))
 (.branch 1217
 (.branch 1210
 (.branch 1207
 (.branch 1205
 (.leaf (.quota 1))
 (.branch 1206
 (.leaf (.reuse 19))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 1213
 (.leaf (.quota 1))
 (.branch 1215
 (.branch 1214
 (.leaf (.quota 1))
 (.leaf (.reuse 20)))
 (.leaf (.quota 1)))))
 (.branch 1224
 (.branch 1220
 (.branch 1218
 (.leaf (.reuse 21))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 1258
 (.branch 1244
 (.branch 1237
 (.branch 1234
 (.leaf (.quota 1))
 (.branch 1235
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 1499
 (.branch 1392
 (.branch 1338
 (.branch 1311
 (.branch 1298
 (.leaf (.quota 1))
 (.branch 1304
 (.branch 1301
 (.leaf (.quota 1))
 (.branch 1302
 (.leaf (.quota 1))
 (.branch 1303
 (.leaf (.reuse 24))
 (.leaf (.quota 1)))))
 (.branch 1307
 (.leaf (.quota 1))
 (.branch 1309
 (.leaf (.quota 1))
 (.branch 1310
 (.leaf (.quota 1))
 (.leaf (.reuse 25)))))))
 (.branch 1324
 (.branch 1317
 (.branch 1314
 (.leaf (.quota 1))
 (.branch 1315
 (.leaf (.quota 1))
 (.branch 1316
 (.leaf (.quota 1))
 (.leaf (.reuse 26)))))
 (.branch 1320
 (.branch 1318
 (.leaf (.reuse 27))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 1445
 (.branch 1418
 (.branch 1405
 (.branch 1398
 (.branch 1395
 (.leaf (.quota 1))
 (.branch 1396
 (.leaf (.quota 1))
 (.branch 1397
 (.leaf (.quota 1))
 (.leaf (.reuse 28)))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 1472
 (.branch 1458
 (.branch 1451
 (.branch 1448
 (.leaf (.quota 1))
 (.branch 1449
 (.leaf (.quota 1))
 (.branch 1450
 (.leaf (.reuse 29))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 1606
 (.branch 1552
 (.branch 1525
 (.leaf (.quota 1))
 (.branch 1538
 (.leaf (.quota 1))
 (.branch 1545
 (.leaf (.quota 1))
 (.branch 1548
 (.branch 1546
 (.leaf (.quota 1))
 (.branch 1547
 (.leaf (.quota 1))
 (.leaf (.reuse 30))))
 (.leaf (.quota 1))))))
 (.leaf (.quota 1)))
 (.branch 1660
 (.branch 1633
 (.branch 1619
 (.branch 1612
 (.branch 1609
 (.leaf (.quota 1))
 (.branch 1610
 (.leaf (.quota 1))
 (.branch 1611
 (.leaf (.reuse 31))
 (.leaf (.quota 1)))))
 (.branch 1615
 (.branch 1613
 (.leaf (.quota 1))
 (.branch 1614
 (.leaf (.reuse 32))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 1626
 (.branch 1622
 (.leaf (.quota 1))
 (.branch 1624
 (.branch 1623
 (.leaf (.reuse 33))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 1646
 (.leaf (.quota 1))
 (.branch 1653
 (.branch 1649
 (.branch 1647
 (.leaf (.reuse 34))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 1656
 (.branch 1654
 (.leaf (.quota 1))
 (.branch 1655
 (.leaf (.quota 1))
 (.leaf (.reuse 35))))
 (.branch 1658
 (.leaf (.quota 1))
 (.branch 1659
 (.leaf (.quota 1))
 (.leaf (.reuse 36))))))))
 (.branch 1687
 (.leaf (.quota 1))
 (.branch 1700
 (.branch 1693
 (.branch 1690
 (.branch 1688
 (.leaf (.quota 1))
 (.branch 1689
 (.leaf (.reuse 37))
 (.leaf (.quota 1))))
 (.branch 1691
 (.leaf (.quota 1))
 (.branch 1692
 (.leaf (.quota 1))
 (.leaf (.reuse 38)))))
 (.branch 1696
 (.leaf (.quota 1))
 (.branch 1698
 (.leaf (.quota 1))
 (.branch 1699
 (.leaf (.reuse 39))
 (.leaf (.quota 1))))))
 (.branch 1707
 (.leaf (.quota 1))
 (.branch 1710
 (.branch 1708
 (.leaf (.quota 1))
 (.branch 1709
 (.leaf (.reuse 40))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))))))))
 (.branch 2571
 (.branch 2142
 (.branch 1928
 (.branch 1821
 (.branch 1767
 (.branch 1740
 (.branch 1727
 (.branch 1720
 (.branch 1717
 (.leaf (.quota 1))
 (.branch 1718
 (.leaf (.reuse 41))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 1733
 (.branch 1730
 (.branch 1728
 (.leaf (.quota 1))
 (.branch 1729
 (.leaf (.quota 1))
 (.leaf (.reuse 42))))
 (.leaf (.quota 1)))
 (.branch 1736
 (.branch 1734
 (.leaf (.quota 1))
 (.branch 1735
 (.leaf (.quota 1))
 (.leaf (.reuse 43))))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 2035
 (.branch 1981
 (.branch 1954
 (.branch 1941
 (.leaf (.quota 1))
 (.branch 1947
 (.branch 1944
 (.leaf (.quota 1))
 (.branch 1945
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1950
 (.branch 1948
 (.leaf (.reuse 46))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 1967
 (.branch 1960
 (.leaf (.quota 1))
 (.branch 1963
 (.leaf (.quota 1))
 (.branch 1965
 (.leaf (.quota 1))
 (.branch 1966
 (.leaf (.quota 1))
 (.leaf (.reuse 47))))))
 (.leaf (.quota 1))))
 (.branch 2008
 (.branch 1994
 (.leaf (.quota 1))
 (.branch 2001
 (.leaf (.quota 1))
 (.branch 2004
 (.branch 2002
 (.leaf (.quota 1))
 (.branch 2003
 (.leaf (.reuse 48))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))
 (.branch 2021
 (.branch 2014
 (.branch 2011
 (.leaf (.quota 1))
 (.branch 2012
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1))))
 (.branch 2356
 (.leaf (.quota 1))
 (.branch 2463
 (.branch 2409
 (.branch 2382
 (.branch 2369
 (.leaf (.quota 1))
 (.branch 2375
 (.leaf (.quota 1))
 (.branch 2378
 (.branch 2376
 (.leaf (.quota 1))
 (.branch 2377
 (.leaf (.reuse 50))
 (.leaf (.quota 1))))
 (.branch 2380
 (.branch 2379
 (.leaf (.quota 1))
 (.leaf (.reuse 51)))
 (.leaf (.quota 1))))))
 (.branch 2395
 (.leaf (.quota 1))
 (.branch 2402
 (.branch 2398
 (.leaf (.quota 1))
 (.branch 2400
 (.branch 2399
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))
 (.branch 2436
 (.branch 2422
 (.branch 2415
 (.leaf (.quota 1))
 (.branch 2418
 (.leaf (.quota 1))
 (.branch 2420
 (.branch 2419
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 2429
 (.branch 2425
 (.branch 2423
 (.leaf (.quota 1))
 (.branch 2424
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 2517
 (.leaf (.quota 1))
 (.branch 2544
 (.branch 2530
 (.leaf (.quota 1))
 (.branch 2537
 (.branch 2533
 (.branch 2531
 (.leaf (.quota 1))
 (.branch 2532
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 2557
 (.branch 2550
 (.leaf (.quota 1))
 (.branch 2553
 (.leaf (.quota 1))
 (.branch 2555
 (.leaf (.quota 1))
 (.branch 2556
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 2564
 (.branch 2560
 (.leaf (.quota 1))
 (.branch 2562
 (.branch 2561
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))))))
 (.branch 2999
 (.branch 2785
 (.branch 2678
 (.branch 2624
 (.branch 2597
 (.leaf (.quota 1))
 (.branch 2610
 (.branch 2603
 (.leaf (.quota 1))
 (.branch 2606
 (.branch 2604
 (.leaf (.reuse 58))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 2617
 (.branch 2613
 (.leaf (.quota 1))
 (.branch 2615
 (.branch 2614
 (.leaf (.reuse 59))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 2892
 (.branch 2838
 (.branch 2811
 (.leaf (.quota 1))
 (.branch 2824
 (.branch 2817
 (.leaf (.quota 1))
 (.branch 2820
 (.leaf (.quota 1))
 (.branch 2822
 (.leaf (.quota 1))
 (.branch 2823
 (.leaf (.reuse 61))
 (.leaf (.quota 1))))))
 (.branch 2831
 (.branch 2827
 (.leaf (.quota 1))
 (.branch 2829
 (.branch 2828
 (.leaf (.reuse 62))
 (.leaf (.quota 1)))
 (.branch 2830
 (.leaf (.quota 1))
 (.leaf (.reuse 63)))))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.branch 2945
 (.branch 2918
 (.leaf (.quota 1))
 (.branch 2931
 (.leaf (.quota 1))
 (.branch 2938
 (.leaf (.quota 1))
 (.branch 2941
 (.leaf (.quota 1))
 (.branch 2943
 (.leaf (.quota 1))
 (.branch 2944
 (.leaf (.reuse 65))
 (.leaf (.quota 1))))))))
 (.branch 2972
 (.branch 2958
 (.branch 2951
 (.leaf (.quota 1))
 (.branch 2954
 (.leaf (.quota 1))
 (.branch 2956
 (.leaf (.quota 1))
 (.branch 2957
 (.leaf (.reuse 66))
 (.leaf (.quota 1))))))
 (.branch 2965
 (.branch 2961
 (.leaf (.quota 1))
 (.branch 2963
 (.branch 2962
 (.leaf (.reuse 67))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 2985
 (.branch 2978
 (.leaf (.quota 1))
 (.branch 2981
 (.branch 2979
 (.leaf (.quota 1))
 (.branch 2980
 (.leaf (.quota 1))
 (.leaf (.reuse 68))))
 (.leaf (.quota 1))))
 (.branch 2992
 (.leaf (.quota 1))
 (.branch 2995
 (.branch 2993
 (.leaf (.quota 1))
 (.branch 2994
 (.leaf (.reuse 69))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))))))
 (.branch 3213
 (.branch 3106
 (.branch 3052
 (.leaf (.quota 1))
 (.branch 3079
 (.leaf (.quota 1))
 (.branch 3092
 (.branch 3085
 (.branch 3082
 (.leaf (.quota 1))
 (.branch 3083
 (.leaf (.quota 1))
 (.branch 3084
 (.leaf (.reuse 70))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 3159
 (.branch 3132
 (.branch 3119
 (.branch 3112
 (.branch 3109
 (.leaf (.quota 1))
 (.branch 3110
 (.leaf (.quota 1))
 (.branch 3111
 (.leaf (.quota 1))
 (.leaf (.reuse 71)))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 3186
 (.leaf (.quota 1))
 (.branch 3199
 (.leaf (.quota 1))
 (.branch 3206
 (.branch 3202
 (.branch 3200
 (.leaf (.quota 1))
 (.branch 3201
 (.leaf (.reuse 72))
 (.leaf (.quota 1))))
 (.branch 3204
 (.branch 3203
 (.leaf (.reuse 73))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 3209
 (.leaf (.quota 1))
 (.branch 3211
 (.branch 3210
 (.leaf (.quota 1))
 (.leaf (.reuse 74)))
 (.leaf (.quota 1)))))))))
 (.branch 3320
 (.branch 3266
 (.branch 3239
 (.leaf (.quota 1))
 (.branch 3252
 (.branch 3245
 (.branch 3242
 (.leaf (.quota 1))
 (.branch 3243
 (.leaf (.reuse 75))
 (.branch 3244
 (.leaf (.quota 1))
 (.leaf (.reuse 76)))))
 (.leaf (.quota 1)))
 (.branch 3259
 (.leaf (.quota 1))
 (.branch 3262
 (.branch 3260
 (.leaf (.reuse 77))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 3293
 (.branch 3279
 (.branch 3272
 (.branch 3269
 (.leaf (.quota 1))
 (.branch 3270
 (.leaf (.reuse 78))
 (.leaf (.quota 1))))
 (.branch 3275
 (.leaf (.quota 1))
 (.branch 3277
 (.branch 3276
 (.leaf (.reuse 79))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.branch 3306
 (.leaf (.quota 1))
 (.branch 3313
 (.leaf (.quota 1))
 (.branch 3316
 (.branch 3314
 (.leaf (.quota 1))
 (.branch 3315
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))))))
 (.branch 3374
 (.branch 3347
 (.branch 3333
 (.branch 3326
 (.leaf (.quota 1))
 (.branch 3329
 (.leaf (.quota 1))
 (.branch 3331
 (.leaf (.quota 1))
 (.branch 3332
 (.leaf (.quota 1))
 (.leaf (.reuse 82))))))
 (.branch 3340
 (.branch 3336
 (.branch 3334
 (.leaf (.reuse 83))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 3343
 (.branch 3341
 (.leaf (.quota 1))
 (.branch 3342
 (.leaf (.reuse 85))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))
 (.branch 3360
 (.branch 3353
 (.leaf (.quota 1))
 (.branch 3356
 (.leaf (.quota 1))
 (.branch 3358
 (.leaf (.quota 1))
 (.branch 3359
 (.leaf (.quota 1))
 (.leaf (.reuse 86))))))
 (.branch 3367
 (.branch 3363
 (.branch 3361
 (.leaf (.quota 1))
 (.branch 3362
 (.leaf (.reuse 87))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 3401
 (.branch 3387
 (.branch 3380
 (.leaf (.quota 1))
 (.branch 3383
 (.branch 3381
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 3394
 (.leaf (.quota 1))
 (.branch 3397
 (.leaf (.quota 1))
 (.branch 3399
 (.branch 3398
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 3414
 (.leaf (.quota 1))
 (.branch 3421
 (.leaf (.quota 1))
 (.branch 3424
 (.leaf (.quota 1))
 (.branch 3426
 (.leaf (.quota 1))
 (.branch 3427
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))))))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0717.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0717.rawLeaves 92 (RootedForests.RootedSubsumedForest0724.rawLeaves i) (routes.get i)

def disposition (j : Fin 3428) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0717.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0717

/- Original module: RootedQuotaTransfer0717Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0717
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 16 :=
  interval_of_check test0 0 16 (by decide +kernel)

theorem test0_block_1 : Interval test0 16 32 :=
  interval_of_check test0 16 16 (by decide +kernel)

theorem test0_block_2 : Interval test0 32 48 :=
  interval_of_check test0 32 16 (by decide +kernel)

theorem test0_block_3 : Interval test0 48 64 :=
  interval_of_check test0 48 16 (by decide +kernel)

theorem test0_block_4 : Interval test0 64 80 :=
  interval_of_check test0 64 16 (by decide +kernel)

theorem test0_block_5 : Interval test0 80 96 :=
  interval_of_check test0 80 16 (by decide +kernel)

theorem test0_block_6 : Interval test0 96 112 :=
  interval_of_check test0 96 16 (by decide +kernel)

theorem test0_block_7 : Interval test0 112 128 :=
  interval_of_check test0 112 16 (by decide +kernel)

theorem test0_complete : Interval test0 0 128 :=
  (interval_append test0 0 64 128
  (interval_append test0 0 32 64
  (interval_append test0 0 16 32
  test0_block_0
  test0_block_1)
  (interval_append test0 32 48 64
  test0_block_2
  test0_block_3))
  (interval_append test0 64 96 128
  (interval_append test0 64 80 96
  test0_block_4
  test0_block_5)
  (interval_append test0 96 112 128
  test0_block_6
  test0_block_7)))
theorem routeInterval0 : Interval routeTest 0 128 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0717

/- Original module: RootedQuotaTransfer0717Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0717
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test128 (i : Nat) := routeTest (i + 128)
theorem test128_block_0 : Interval test128 0 16 :=
  interval_of_check test128 0 16 (by decide +kernel)

theorem test128_block_1 : Interval test128 16 32 :=
  interval_of_check test128 16 16 (by decide +kernel)

theorem test128_block_2 : Interval test128 32 48 :=
  interval_of_check test128 32 16 (by decide +kernel)

theorem test128_block_3 : Interval test128 48 64 :=
  interval_of_check test128 48 16 (by decide +kernel)

theorem test128_block_4 : Interval test128 64 80 :=
  interval_of_check test128 64 16 (by decide +kernel)

theorem test128_block_5 : Interval test128 80 96 :=
  interval_of_check test128 80 16 (by decide +kernel)

theorem test128_block_6 : Interval test128 96 112 :=
  interval_of_check test128 96 16 (by decide +kernel)

theorem test128_block_7 : Interval test128 112 128 :=
  interval_of_check test128 112 16 (by decide +kernel)

theorem test128_complete : Interval test128 0 128 :=
  (interval_append test128 0 64 128
  (interval_append test128 0 32 64
  (interval_append test128 0 16 32
  test128_block_0
  test128_block_1)
  (interval_append test128 32 48 64
  test128_block_2
  test128_block_3))
  (interval_append test128 64 96 128
  (interval_append test128 64 80 96
  test128_block_4
  test128_block_5)
  (interval_append test128 96 112 128
  test128_block_6
  test128_block_7)))
theorem routeInterval128 : Interval routeTest 128 256 := by
  intro i hlo hhi
  have h := test128_complete (i - 128) (Nat.zero_le _) (by omega)
  simpa only [test128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0717

/- Original module: RootedQuotaTransfer0717Proof002. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0717
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test256 (i : Nat) := routeTest (i + 256)
theorem test256_block_0 : Interval test256 0 16 :=
  interval_of_check test256 0 16 (by decide +kernel)

theorem test256_block_1 : Interval test256 16 32 :=
  interval_of_check test256 16 16 (by decide +kernel)

theorem test256_block_2 : Interval test256 32 48 :=
  interval_of_check test256 32 16 (by decide +kernel)

theorem test256_block_3 : Interval test256 48 64 :=
  interval_of_check test256 48 16 (by decide +kernel)

theorem test256_block_4 : Interval test256 64 80 :=
  interval_of_check test256 64 16 (by decide +kernel)

theorem test256_block_5 : Interval test256 80 96 :=
  interval_of_check test256 80 16 (by decide +kernel)

theorem test256_block_6 : Interval test256 96 112 :=
  interval_of_check test256 96 16 (by decide +kernel)

theorem test256_block_7 : Interval test256 112 128 :=
  interval_of_check test256 112 16 (by decide +kernel)

theorem test256_complete : Interval test256 0 128 :=
  (interval_append test256 0 64 128
  (interval_append test256 0 32 64
  (interval_append test256 0 16 32
  test256_block_0
  test256_block_1)
  (interval_append test256 32 48 64
  test256_block_2
  test256_block_3))
  (interval_append test256 64 96 128
  (interval_append test256 64 80 96
  test256_block_4
  test256_block_5)
  (interval_append test256 96 112 128
  test256_block_6
  test256_block_7)))
theorem routeInterval256 : Interval routeTest 256 384 := by
  intro i hlo hhi
  have h := test256_complete (i - 256) (Nat.zero_le _) (by omega)
  simpa only [test256, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0717

/- Original module: RootedQuotaTransfer0717Proof003. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0717
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test384 (i : Nat) := routeTest (i + 384)
theorem test384_block_0 : Interval test384 0 16 :=
  interval_of_check test384 0 16 (by decide +kernel)

theorem test384_block_1 : Interval test384 16 32 :=
  interval_of_check test384 16 16 (by decide +kernel)

theorem test384_block_2 : Interval test384 32 48 :=
  interval_of_check test384 32 16 (by decide +kernel)

theorem test384_block_3 : Interval test384 48 64 :=
  interval_of_check test384 48 16 (by decide +kernel)

theorem test384_block_4 : Interval test384 64 80 :=
  interval_of_check test384 64 16 (by decide +kernel)

theorem test384_block_5 : Interval test384 80 96 :=
  interval_of_check test384 80 16 (by decide +kernel)

theorem test384_block_6 : Interval test384 96 112 :=
  interval_of_check test384 96 16 (by decide +kernel)

theorem test384_block_7 : Interval test384 112 128 :=
  interval_of_check test384 112 16 (by decide +kernel)

theorem test384_complete : Interval test384 0 128 :=
  (interval_append test384 0 64 128
  (interval_append test384 0 32 64
  (interval_append test384 0 16 32
  test384_block_0
  test384_block_1)
  (interval_append test384 32 48 64
  test384_block_2
  test384_block_3))
  (interval_append test384 64 96 128
  (interval_append test384 64 80 96
  test384_block_4
  test384_block_5)
  (interval_append test384 96 112 128
  test384_block_6
  test384_block_7)))
theorem routeInterval384 : Interval routeTest 384 512 := by
  intro i hlo hhi
  have h := test384_complete (i - 384) (Nat.zero_le _) (by omega)
  simpa only [test384, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0717

/- Original module: RootedQuotaTransfer0717Proof004. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0717
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test512 (i : Nat) := routeTest (i + 512)
theorem test512_block_0 : Interval test512 0 16 :=
  interval_of_check test512 0 16 (by decide +kernel)

theorem test512_block_1 : Interval test512 16 32 :=
  interval_of_check test512 16 16 (by decide +kernel)

theorem test512_block_2 : Interval test512 32 48 :=
  interval_of_check test512 32 16 (by decide +kernel)

theorem test512_block_3 : Interval test512 48 64 :=
  interval_of_check test512 48 16 (by decide +kernel)

theorem test512_block_4 : Interval test512 64 80 :=
  interval_of_check test512 64 16 (by decide +kernel)

theorem test512_block_5 : Interval test512 80 96 :=
  interval_of_check test512 80 16 (by decide +kernel)

theorem test512_block_6 : Interval test512 96 112 :=
  interval_of_check test512 96 16 (by decide +kernel)

theorem test512_block_7 : Interval test512 112 128 :=
  interval_of_check test512 112 16 (by decide +kernel)

theorem test512_complete : Interval test512 0 128 :=
  (interval_append test512 0 64 128
  (interval_append test512 0 32 64
  (interval_append test512 0 16 32
  test512_block_0
  test512_block_1)
  (interval_append test512 32 48 64
  test512_block_2
  test512_block_3))
  (interval_append test512 64 96 128
  (interval_append test512 64 80 96
  test512_block_4
  test512_block_5)
  (interval_append test512 96 112 128
  test512_block_6
  test512_block_7)))
theorem routeInterval512 : Interval routeTest 512 640 := by
  intro i hlo hhi
  have h := test512_complete (i - 512) (Nat.zero_le _) (by omega)
  simpa only [test512, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0717

/- Original module: RootedQuotaTransfer0717Proof005. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0717
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test640 (i : Nat) := routeTest (i + 640)
theorem test640_block_0 : Interval test640 0 16 :=
  interval_of_check test640 0 16 (by decide +kernel)

theorem test640_block_1 : Interval test640 16 32 :=
  interval_of_check test640 16 16 (by decide +kernel)

theorem test640_block_2 : Interval test640 32 48 :=
  interval_of_check test640 32 16 (by decide +kernel)

theorem test640_block_3 : Interval test640 48 64 :=
  interval_of_check test640 48 16 (by decide +kernel)

theorem test640_block_4 : Interval test640 64 80 :=
  interval_of_check test640 64 16 (by decide +kernel)

theorem test640_block_5 : Interval test640 80 96 :=
  interval_of_check test640 80 16 (by decide +kernel)

theorem test640_block_6 : Interval test640 96 112 :=
  interval_of_check test640 96 16 (by decide +kernel)

theorem test640_block_7 : Interval test640 112 128 :=
  interval_of_check test640 112 16 (by decide +kernel)

theorem test640_complete : Interval test640 0 128 :=
  (interval_append test640 0 64 128
  (interval_append test640 0 32 64
  (interval_append test640 0 16 32
  test640_block_0
  test640_block_1)
  (interval_append test640 32 48 64
  test640_block_2
  test640_block_3))
  (interval_append test640 64 96 128
  (interval_append test640 64 80 96
  test640_block_4
  test640_block_5)
  (interval_append test640 96 112 128
  test640_block_6
  test640_block_7)))
theorem routeInterval640 : Interval routeTest 640 768 := by
  intro i hlo hhi
  have h := test640_complete (i - 640) (Nat.zero_le _) (by omega)
  simpa only [test640, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0717
