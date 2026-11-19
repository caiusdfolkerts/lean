module
prelude
public import BundledQuotaTransfers.RootedSixBase02Part000
public import QuotaLeafTransfer
public import FiniteChecks
public import RootedSubsumedForest0360Dispositions
public import RootedSubsumedForest0708Data

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- Original module: RootedQuotaTransfer0359Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0359
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

theorem test128_complete : Interval test128 0 64 :=
  (interval_append test128 0 32 64
  (interval_append test128 0 16 32
  test128_block_0
  test128_block_1)
  (interval_append test128 32 48 64
  test128_block_2
  test128_block_3))
theorem routeInterval128 : Interval routeTest 128 192 := by
  intro i hlo hhi
  have h := test128_complete (i - 128) (Nat.zero_le _) (by omega)
  simpa only [test128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0359

/- Original module: RootedQuotaTransfer0359. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0359
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 192 :=
  (interval_append routeTest 0 128 192
  routeInterval0
  routeInterval128)

theorem disposition_checked (j : Fin 192) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0359.quota
      ((RootedForests.RootedSubsumedForest0365.rawLeaves j.val).map RootedCaches.RootedSixBase02.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0359.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0359.rawLeaves 2 RootedForests.RootedSubsumedForest0359.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0359.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0365.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0359

/- Original module: RootedQuotaTransfer0360Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0360
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 360: use the complete forest for case 708, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0360.quota k ≤ RootedForests.RootedSubsumedForest0708.quota k := by
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
(.branch 815
 (.branch 407
 (.branch 203
 (.branch 101
 (.leaf (.quota 1))
 (.branch 152
 (.branch 126
 (.branch 113
 (.leaf (.quota 1))
 (.branch 119
 (.leaf (.quota 1))
 (.branch 122
 (.leaf (.quota 1))
 (.branch 124
 (.branch 123
 (.leaf (.quota 1))
 (.leaf (.reuse 0)))
 (.leaf (.quota 1))))))
 (.branch 139
 (.leaf (.quota 1))
 (.branch 145
 (.branch 142
 (.leaf (.quota 1))
 (.branch 143
 (.leaf (.reuse 1))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))
 (.branch 177
 (.leaf (.quota 1))
 (.branch 190
 (.branch 183
 (.leaf (.quota 1))
 (.branch 186
 (.branch 184
 (.leaf (.quota 1))
 (.branch 185
 (.leaf (.reuse 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))))
 (.branch 305
 (.branch 254
 (.branch 228
 (.branch 215
 (.branch 209
 (.branch 206
 (.branch 204
 (.leaf (.reuse 3))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 611
 (.branch 509
 (.branch 458
 (.leaf (.quota 1))
 (.branch 483
 (.branch 470
 (.leaf (.quota 1))
 (.branch 476
 (.leaf (.quota 1))
 (.branch 479
 (.branch 477
 (.leaf (.quota 1))
 (.branch 478
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))))
 (.branch 496
 (.branch 489
 (.leaf (.quota 1))
 (.branch 492
 (.branch 490
 (.leaf (.quota 1))
 (.branch 491
 (.leaf (.quota 1))
 (.leaf (.reuse 5))))
 (.leaf (.quota 1))))
 (.branch 502
 (.leaf (.quota 1))
 (.branch 505
 (.leaf (.quota 1))
 (.branch 507
 (.branch 506
 (.leaf (.reuse 6))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))))
 (.leaf (.quota 1)))
 (.branch 713
 (.branch 662
 (.branch 636
 (.leaf (.quota 1))
 (.branch 649
 (.leaf (.quota 1))
 (.branch 655
 (.leaf (.quota 1))
 (.branch 658
 (.branch 656
 (.leaf (.reuse 7))
 (.leaf (.quota 1)))
 (.branch 660
 (.leaf (.quota 1))
 (.branch 661
 (.leaf (.quota 1))
 (.leaf (.reuse 8))))))))
 (.branch 687
 (.branch 674
 (.branch 668
 (.leaf (.quota 1))
 (.branch 671
 (.branch 669
 (.leaf (.quota 1))
 (.branch 670
 (.leaf (.reuse 9))
 (.leaf (.reuse 10))))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 764
 (.leaf (.quota 1))
 (.branch 789
 (.leaf (.quota 1))
 (.branch 802
 (.leaf (.quota 1))
 (.branch 808
 (.leaf (.quota 1))
 (.branch 811
 (.branch 809
 (.leaf (.quota 1))
 (.branch 810
 (.leaf (.reuse 11))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))))))))
 (.branch 1223
 (.branch 1019
 (.branch 917
 (.branch 866
 (.branch 840
 (.branch 827
 (.leaf (.quota 1))
 (.branch 833
 (.leaf (.quota 1))
 (.branch 836
 (.branch 834
 (.leaf (.quota 1))
 (.branch 835
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))))
 (.branch 853
 (.branch 846
 (.leaf (.quota 1))
 (.branch 849
 (.branch 847
 (.leaf (.reuse 13))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 859
 (.leaf (.quota 1))
 (.branch 862
 (.branch 860
 (.leaf (.reuse 14))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 891
 (.branch 878
 (.leaf (.quota 1))
 (.branch 884
 (.branch 881
 (.leaf (.quota 1))
 (.branch 882
 (.leaf (.quota 1))
 (.branch 883
 (.leaf (.reuse 16))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1))))
 (.branch 904
 (.branch 897
 (.leaf (.quota 1))
 (.branch 900
 (.branch 898
 (.leaf (.quota 1))
 (.branch 899
 (.leaf (.reuse 17))
 (.leaf (.quota 1))))
 (.branch 902
 (.branch 901
 (.leaf (.reuse 18))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))))
 (.branch 968
 (.branch 942
 (.leaf (.quota 1))
 (.branch 955
 (.leaf (.quota 1))
 (.branch 961
 (.branch 958
 (.branch 956
 (.leaf (.quota 1))
 (.branch 957
 (.leaf (.reuse 20))
 (.leaf (.quota 1))))
 (.branch 959
 (.leaf (.reuse 21))
 (.branch 960
 (.leaf (.reuse 22))
 (.leaf (.reuse 23)))))
 (.leaf (.quota 1)))))
 (.branch 993
 (.branch 980
 (.leaf (.quota 1))
 (.branch 986
 (.leaf (.quota 1))
 (.branch 989
 (.leaf (.quota 1))
 (.branch 991
 (.branch 990
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 1006
 (.leaf (.quota 1))
 (.branch 1012
 (.leaf (.quota 1))
 (.branch 1015
 (.branch 1013
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))))
 (.branch 1121
 (.branch 1070
 (.branch 1044
 (.branch 1031
 (.branch 1025
 (.branch 1022
 (.leaf (.quota 1))
 (.branch 1023
 (.leaf (.quota 1))
 (.branch 1024
 (.leaf (.quota 1))
 (.leaf (.reuse 29)))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 1057
 (.branch 1050
 (.leaf (.quota 1))
 (.branch 1053
 (.branch 1051
 (.leaf (.reuse 32))
 (.leaf (.quota 1)))
 (.branch 1055
 (.leaf (.quota 1))
 (.branch 1056
 (.leaf (.quota 1))
 (.leaf (.reuse 33))))))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 1172
 (.branch 1146
 (.branch 1133
 (.branch 1127
 (.leaf (.quota 1))
 (.branch 1130
 (.leaf (.quota 1))
 (.branch 1131
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.branch 1159
 (.branch 1152
 (.leaf (.quota 1))
 (.branch 1155
 (.branch 1153
 (.leaf (.quota 1))
 (.branch 1154
 (.leaf (.reuse 35))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 1165
 (.branch 1162
 (.branch 1160
 (.leaf (.quota 1))
 (.branch 1161
 (.leaf (.quota 1))
 (.leaf (.reuse 36))))
 (.branch 1163
 (.leaf (.reuse 37))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))))
 (.branch 1427
 (.branch 1325
 (.branch 1274
 (.branch 1248
 (.leaf (.quota 1))
 (.branch 1261
 (.leaf (.quota 1))
 (.branch 1267
 (.leaf (.quota 1))
 (.branch 1270
 (.leaf (.quota 1))
 (.branch 1272
 (.leaf (.quota 1))
 (.branch 1273
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))))
 (.leaf (.quota 1)))
 (.branch 1376
 (.branch 1350
 (.branch 1337
 (.leaf (.quota 1))
 (.branch 1343
 (.branch 1340
 (.leaf (.quota 1))
 (.branch 1341
 (.leaf (.reuse 39))
 (.leaf (.quota 1))))
 (.branch 1346
 (.branch 1344
 (.leaf (.reuse 40))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 1363
 (.branch 1356
 (.branch 1353
 (.branch 1351
 (.leaf (.quota 1))
 (.branch 1352
 (.leaf (.quota 1))
 (.leaf (.reuse 41))))
 (.branch 1354
 (.leaf (.reuse 42))
 (.branch 1355
 (.leaf (.reuse 43))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 1401
 (.branch 1388
 (.branch 1382
 (.branch 1379
 (.branch 1377
 (.leaf (.reuse 44))
 (.branch 1378
 (.leaf (.quota 1))
 (.leaf (.reuse 45))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 1394
 (.branch 1391
 (.branch 1389
 (.leaf (.quota 1))
 (.branch 1390
 (.leaf (.quota 1))
 (.leaf (.reuse 46))))
 (.branch 1392
 (.leaf (.reuse 47))
 (.leaf (.quota 1))))
 (.branch 1397
 (.leaf (.quota 1))
 (.branch 1399
 (.leaf (.quota 1))
 (.branch 1400
 (.leaf (.reuse 48))
 (.leaf (.quota 1)))))))
 (.leaf (.quota 1)))))
 (.branch 1529
 (.leaf (.quota 1))
 (.branch 1580
 (.branch 1554
 (.leaf (.quota 1))
 (.branch 1567
 (.leaf (.quota 1))
 (.branch 1573
 (.leaf (.quota 1))
 (.branch 1576
 (.branch 1574
 (.leaf (.quota 1))
 (.branch 1575
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1))))))
 (.branch 1605
 (.branch 1592
 (.branch 1586
 (.branch 1583
 (.branch 1581
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 1618
 (.branch 1611
 (.leaf (.quota 1))
 (.branch 1614
 (.leaf (.quota 1))
 (.branch 1616
 (.branch 1615
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))
 (.branch 1624
 (.branch 1621
 (.branch 1619
 (.leaf (.quota 1))
 (.branch 1620
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.branch 1627
 (.branch 1625
 (.leaf (.quota 1))
 (.branch 1626
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 1629
 (.leaf (.quota 1))
 (.branch 1630
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0360.quota RootedCaches.RootedSixBase02.rawCells
    RootedForests.RootedSubsumedForest0360.rawLeaves 55 (RootedForests.RootedSubsumedForest0708.rawLeaves i) (routes.get i)

def disposition (j : Fin 1631) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0360.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0360

/- Original module: RootedQuotaTransfer0360Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0360
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0360

/- Original module: RootedQuotaTransfer0360Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0360
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0360

/- Original module: RootedQuotaTransfer0360Proof002. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0360
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0360

/- Original module: RootedQuotaTransfer0360Proof003. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0360
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0360

/- Original module: RootedQuotaTransfer0360Proof004. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0360
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0360

/- Original module: RootedQuotaTransfer0360Proof005. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0360
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0360

/- Original module: RootedQuotaTransfer0360Proof006. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0360
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test768 (i : Nat) := routeTest (i + 768)
theorem test768_block_0 : Interval test768 0 16 :=
  interval_of_check test768 0 16 (by decide +kernel)

theorem test768_block_1 : Interval test768 16 32 :=
  interval_of_check test768 16 16 (by decide +kernel)

theorem test768_block_2 : Interval test768 32 48 :=
  interval_of_check test768 32 16 (by decide +kernel)

theorem test768_block_3 : Interval test768 48 64 :=
  interval_of_check test768 48 16 (by decide +kernel)

theorem test768_block_4 : Interval test768 64 80 :=
  interval_of_check test768 64 16 (by decide +kernel)

theorem test768_block_5 : Interval test768 80 96 :=
  interval_of_check test768 80 16 (by decide +kernel)

theorem test768_block_6 : Interval test768 96 112 :=
  interval_of_check test768 96 16 (by decide +kernel)

theorem test768_block_7 : Interval test768 112 128 :=
  interval_of_check test768 112 16 (by decide +kernel)

theorem test768_complete : Interval test768 0 128 :=
  (interval_append test768 0 64 128
  (interval_append test768 0 32 64
  (interval_append test768 0 16 32
  test768_block_0
  test768_block_1)
  (interval_append test768 32 48 64
  test768_block_2
  test768_block_3))
  (interval_append test768 64 96 128
  (interval_append test768 64 80 96
  test768_block_4
  test768_block_5)
  (interval_append test768 96 112 128
  test768_block_6
  test768_block_7)))
theorem routeInterval768 : Interval routeTest 768 896 := by
  intro i hlo hhi
  have h := test768_complete (i - 768) (Nat.zero_le _) (by omega)
  simpa only [test768, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0360
