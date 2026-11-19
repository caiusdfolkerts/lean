module
prelude
public import BundledQuotaTransfers.RootedSixExtra05Part000
public import QuotaLeafTransfer
public import FiniteChecks
public import RootedSubsumedForest0860Dispositions
public import RootedSubsumedForest0868Data
public import RootedSubsumedForest0862Dispositions
public import RootedSubsumedForest0869Data
public import RootedSubsumedForest0867Dispositions
public import RootedSubsumedForest0870Data

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- Original module: RootedQuotaTransfer0857Proof003. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0857
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0857

/- Original module: RootedQuotaTransfer0857Proof004. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0857
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0857

/- Original module: RootedQuotaTransfer0857Proof005. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0857
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0857

/- Original module: RootedQuotaTransfer0857Proof006. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0857
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

theorem test768_block_4 : Interval test768 64 67 :=
  interval_of_check test768 64 3 (by decide +kernel)

theorem test768_complete : Interval test768 0 67 :=
  (interval_append test768 0 32 67
  (interval_append test768 0 16 32
  test768_block_0
  test768_block_1)
  (interval_append test768 32 48 67
  test768_block_2
  (interval_append test768 48 64 67
  test768_block_3
  test768_block_4)))
theorem routeInterval768 : Interval routeTest 768 835 := by
  intro i hlo hhi
  have h := test768_complete (i - 768) (Nat.zero_le _) (by omega)
  simpa only [test768, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0857

/- Original module: RootedQuotaTransfer0857. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0857
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 835 :=
  (interval_append routeTest 0 384 835
  (interval_append routeTest 0 128 384
  routeInterval0
  (interval_append routeTest 128 256 384
  routeInterval128
  routeInterval256))
  (interval_append routeTest 384 640 835
  (interval_append routeTest 384 512 640
  routeInterval384
  routeInterval512)
  (interval_append routeTest 640 768 835
  routeInterval640
  routeInterval768)))

theorem disposition_checked (j : Fin 835) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0857.quota
      ((RootedForests.RootedSubsumedForest0870.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0857.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0857.rawLeaves 52 RootedForests.RootedSubsumedForest0857.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0857.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0870.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0857

/- Original module: RootedQuotaTransfer0860Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0860
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 860: use the complete forest for case 868, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0860.quota k ≤ RootedForests.RootedSubsumedForest0868.quota k := by
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
(.branch 90
 (.leaf (.quota 1))
 (.branch 135
 (.branch 112
 (.branch 101
 (.branch 95
 (.branch 92
 (.branch 91
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 106
 (.leaf (.quota 1))
 (.branch 109
 (.branch 107
 (.leaf (.quota 1))
 (.branch 108
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))))
 (.branch 123
 (.branch 117
 (.branch 114
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 157
 (.branch 146
 (.branch 140
 (.leaf (.quota 1))
 (.branch 143
 (.leaf (.quota 1))
 (.branch 144
 (.leaf (.quota 1))
 (.branch 145
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 151
 (.leaf (.quota 1))
 (.branch 154
 (.leaf (.quota 1))
 (.branch 155
 (.leaf (.quota 1))
 (.branch 156
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 168
 (.branch 162
 (.branch 159
 (.leaf (.quota 1))
 (.branch 160
 (.leaf (.quota 1))
 (.branch 161
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 165
 (.branch 163
 (.leaf (.quota 1))
 (.branch 164
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 166
 (.leaf (.quota 2))
 (.branch 167
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 174
 (.branch 171
 (.branch 169
 (.leaf (.quota 3))
 (.branch 170
 (.leaf (.quota 3))
 (.leaf (.quota 1))))
 (.branch 172
 (.leaf (.quota 1))
 (.branch 173
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 177
 (.branch 175
 (.leaf (.quota 1))
 (.branch 176
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0860.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0860.rawLeaves 17 (RootedForests.RootedSubsumedForest0868.rawLeaves i) (routes.get i)

def disposition (j : Fin 180) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0860.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0860

/- Original module: RootedQuotaTransfer0860Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0860
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0860

/- Original module: RootedQuotaTransfer0860Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0860
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0860

/- Original module: RootedQuotaTransfer0860. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0860
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 180 :=
  (interval_append routeTest 0 128 180
  routeInterval0
  routeInterval128)

theorem disposition_checked (j : Fin 180) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0860.quota
      ((RootedForests.RootedSubsumedForest0868.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0860.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0860.rawLeaves 17 RootedForests.RootedSubsumedForest0860.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0860.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0868.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0860

/- Original module: RootedQuotaTransfer0862Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0862
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 862: use the complete forest for case 869, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0862.quota k ≤ RootedForests.RootedSubsumedForest0869.quota k := by
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
(.branch 90
 (.branch 45
 (.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.leaf (.quota 1))
 (.branch 3
 (.leaf (.quota 3))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 16
 (.leaf (.quota 1))
 (.branch 19
 (.branch 17
 (.leaf (.quota 1))
 (.branch 18
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.leaf (.quota 1))
 (.branch 25
 (.leaf (.quota 1))
 (.branch 26
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 30
 (.leaf (.quota 1))
 (.branch 31
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1))))
 (.branch 67
 (.leaf (.quota 1))
 (.branch 78
 (.leaf (.quota 1))
 (.branch 84
 (.leaf (.quota 1))
 (.branch 87
 (.branch 85
 (.leaf (.quota 1))
 (.branch 86
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))))))
 (.branch 135
 (.branch 112
 (.branch 101
 (.branch 95
 (.branch 92
 (.leaf (.quota 1))
 (.branch 93
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 123
 (.leaf (.quota 1))
 (.branch 129
 (.leaf (.quota 1))
 (.branch 132
 (.leaf (.quota 1))
 (.branch 133
 (.leaf (.quota 1))
 (.branch 134
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))))
 (.branch 158
 (.branch 146
 (.branch 140
 (.branch 137
 (.branch 136
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 152
 (.leaf (.quota 1))
 (.branch 155
 (.branch 153
 (.leaf (.quota 2))
 (.branch 154
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))))
 (.branch 169
 (.branch 163
 (.branch 160
 (.branch 159
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.branch 166
 (.leaf (.quota 1))
 (.branch 167
 (.leaf (.quota 1))
 (.branch 168
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 175
 (.leaf (.quota 1))
 (.branch 178
 (.branch 176
 (.leaf (.quota 1))
 (.branch 177
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0862.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0862.rawLeaves 31 (RootedForests.RootedSubsumedForest0869.rawLeaves i) (routes.get i)

def disposition (j : Fin 181) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0862.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0862

/- Original module: RootedQuotaTransfer0862Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0862
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0862

/- Original module: RootedQuotaTransfer0862Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0862
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test128 (i : Nat) := routeTest (i + 128)
theorem test128_block_0 : Interval test128 0 16 :=
  interval_of_check test128 0 16 (by decide +kernel)

theorem test128_block_1 : Interval test128 16 32 :=
  interval_of_check test128 16 16 (by decide +kernel)

theorem test128_block_2 : Interval test128 32 48 :=
  interval_of_check test128 32 16 (by decide +kernel)

theorem test128_block_3 : Interval test128 48 53 :=
  interval_of_check test128 48 5 (by decide +kernel)

theorem test128_complete : Interval test128 0 53 :=
  (interval_append test128 0 32 53
  (interval_append test128 0 16 32
  test128_block_0
  test128_block_1)
  (interval_append test128 32 48 53
  test128_block_2
  test128_block_3))
theorem routeInterval128 : Interval routeTest 128 181 := by
  intro i hlo hhi
  have h := test128_complete (i - 128) (Nat.zero_le _) (by omega)
  simpa only [test128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0862

/- Original module: RootedQuotaTransfer0862. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0862
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 181 :=
  (interval_append routeTest 0 128 181
  routeInterval0
  routeInterval128)

theorem disposition_checked (j : Fin 181) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0862.quota
      ((RootedForests.RootedSubsumedForest0869.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0862.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0862.rawLeaves 31 RootedForests.RootedSubsumedForest0862.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0862.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0869.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0862

/- Original module: RootedQuotaTransfer0867Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0867
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 867: use the complete forest for case 870, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0867.quota k ≤ RootedForests.RootedSubsumedForest0870.quota k := by
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
(.branch 417
 (.branch 208
 (.branch 104
 (.branch 52
 (.branch 26
 (.leaf (.quota 1))
 (.branch 39
 (.branch 32
 (.branch 29
 (.branch 27
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 45
 (.branch 42
 (.leaf (.quota 1))
 (.branch 43
 (.leaf (.quota 2))
 (.branch 44
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))))
 (.branch 78
 (.leaf (.quota 1))
 (.branch 91
 (.branch 84
 (.leaf (.quota 1))
 (.branch 87
 (.leaf (.quota 1))
 (.branch 89
 (.leaf (.quota 1))
 (.branch 90
 (.leaf (.reuse 7))
 (.leaf (.quota 1))))))
 (.branch 97
 (.branch 94
 (.branch 92
 (.leaf (.reuse 8))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 156
 (.branch 130
 (.branch 117
 (.branch 110
 (.branch 107
 (.leaf (.quota 1))
 (.branch 108
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 113
 (.branch 111
 (.leaf (.quota 1))
 (.branch 112
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 143
 (.branch 136
 (.branch 133
 (.branch 131
 (.leaf (.quota 1))
 (.branch 132
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.branch 139
 (.leaf (.quota 1))
 (.branch 141
 (.branch 140
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 142
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 149
 (.branch 146
 (.leaf (.quota 1))
 (.branch 147
 (.leaf (.quota 1))
 (.branch 148
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 152
 (.branch 150
 (.leaf (.quota 1))
 (.branch 151
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 154
 (.branch 153
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))))
 (.branch 182
 (.branch 169
 (.leaf (.quota 1))
 (.branch 175
 (.branch 172
 (.branch 170
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 173
 (.leaf (.quota 1))
 (.branch 174
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 178
 (.branch 176
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 180
 (.branch 179
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 195
 (.branch 188
 (.branch 185
 (.branch 183
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 312
 (.branch 260
 (.branch 234
 (.branch 221
 (.branch 214
 (.leaf (.quota 1))
 (.branch 217
 (.branch 215
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 219
 (.branch 218
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 227
 (.leaf (.quota 1))
 (.branch 230
 (.branch 228
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))
 (.branch 247
 (.branch 240
 (.branch 237
 (.branch 235
 (.leaf (.quota 1))
 (.branch 236
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 238
 (.leaf (.quota 1))
 (.branch 239
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 243
 (.branch 241
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 245
 (.branch 244
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 246
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 364
 (.branch 338
 (.branch 325
 (.branch 318
 (.branch 315
 (.branch 313
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 351
 (.leaf (.quota 1))
 (.branch 357
 (.branch 354
 (.branch 352
 (.leaf (.quota 2))
 (.branch 353
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 355
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 360
 (.leaf (.quota 1))
 (.branch 362
 (.leaf (.quota 1))
 (.branch 363
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))))
 (.branch 390
 (.branch 377
 (.leaf (.quota 1))
 (.branch 383
 (.branch 380
 (.branch 378
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 403
 (.branch 396
 (.branch 393
 (.leaf (.quota 1))
 (.branch 394
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.branch 410
 (.leaf (.quota 1))
 (.branch 413
 (.branch 411
 (.leaf (.quota 1))
 (.branch 412
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))))))
 (.branch 626
 (.branch 521
 (.branch 469
 (.branch 443
 (.branch 430
 (.branch 423
 (.branch 420
 (.branch 418
 (.leaf (.quota 1))
 (.branch 419
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 426
 (.leaf (.quota 1))
 (.branch 428
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 436
 (.leaf (.quota 1))
 (.branch 439
 (.branch 437
 (.leaf (.quota 1))
 (.branch 438
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 441
 (.branch 440
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))
 (.branch 456
 (.branch 449
 (.branch 446
 (.branch 444
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 447
 (.leaf (.quota 1))
 (.branch 448
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 452
 (.leaf (.quota 1))
 (.branch 454
 (.branch 453
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))
 (.branch 462
 (.branch 459
 (.branch 457
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 465
 (.leaf (.quota 1))
 (.branch 467
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 495
 (.branch 482
 (.leaf (.quota 1))
 (.branch 488
 (.leaf (.quota 1))
 (.branch 491
 (.leaf (.quota 1))
 (.branch 493
 (.leaf (.quota 1))
 (.branch 494
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))
 (.branch 508
 (.branch 501
 (.branch 498
 (.branch 496
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 514
 (.branch 511
 (.leaf (.quota 1))
 (.branch 512
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1))))))
 (.branch 573
 (.branch 547
 (.branch 534
 (.branch 527
 (.branch 524
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 530
 (.branch 528
 (.leaf (.quota 1))
 (.branch 529
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 532
 (.branch 531
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 540
 (.branch 537
 (.leaf (.quota 1))
 (.branch 538
 (.leaf (.quota 1))
 (.branch 539
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 543
 (.leaf (.quota 1))
 (.branch 545
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 560
 (.branch 553
 (.leaf (.quota 1))
 (.branch 556
 (.leaf (.quota 1))
 (.branch 558
 (.branch 557
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 559
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 566
 (.branch 563
 (.branch 561
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 569
 (.leaf (.quota 1))
 (.branch 571
 (.branch 570
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))))
 (.branch 599
 (.branch 586
 (.branch 579
 (.leaf (.quota 1))
 (.branch 582
 (.leaf (.quota 1))
 (.branch 584
 (.branch 583
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 585
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 592
 (.leaf (.quota 1))
 (.branch 595
 (.leaf (.quota 1))
 (.branch 597
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 612
 (.leaf (.quota 1))
 (.branch 619
 (.leaf (.quota 1))
 (.branch 622
 (.branch 620
 (.leaf (.quota 1))
 (.branch 621
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 624
 (.branch 623
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))))))
 (.branch 730
 (.branch 678
 (.branch 652
 (.branch 639
 (.branch 632
 (.leaf (.quota 1))
 (.branch 635
 (.branch 633
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 637
 (.branch 636
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))
 (.branch 645
 (.branch 642
 (.leaf (.quota 2))
 (.branch 643
 (.leaf (.quota 1))
 (.branch 644
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1))))
 (.branch 665
 (.leaf (.quota 1))
 (.branch 671
 (.branch 668
 (.leaf (.quota 1))
 (.branch 669
 (.leaf (.quota 1))
 (.branch 670
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 1)))))
 (.branch 704
 (.leaf (.quota 1))
 (.branch 717
 (.branch 710
 (.branch 707
 (.leaf (.quota 1))
 (.branch 708
 (.leaf (.reuse 122))
 (.branch 709
 (.leaf (.reuse 123))
 (.leaf (.quota 1)))))
 (.branch 713
 (.branch 711
 (.leaf (.quota 1))
 (.branch 712
 (.leaf (.quota 1))
 (.leaf (.reuse 124))))
 (.leaf (.quota 1))))
 (.branch 723
 (.leaf (.quota 1))
 (.branch 726
 (.branch 724
 (.leaf (.quota 1))
 (.branch 725
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))))))
 (.branch 782
 (.branch 756
 (.branch 743
 (.branch 736
 (.branch 733
 (.branch 731
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 739
 (.branch 737
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 741
 (.leaf (.quota 1))
 (.branch 742
 (.leaf (.quota 1))
 (.leaf (.reuse 129))))))
 (.branch 749
 (.branch 746
 (.leaf (.quota 1))
 (.branch 747
 (.leaf (.quota 1))
 (.branch 748
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 752
 (.leaf (.quota 1))
 (.branch 754
 (.leaf (.quota 1))
 (.branch 755
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 769
 (.branch 762
 (.leaf (.quota 1))
 (.branch 765
 (.branch 763
 (.leaf (.quota 2))
 (.branch 764
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 767
 (.branch 766
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 775
 (.branch 772
 (.branch 770
 (.leaf (.quota 1))
 (.branch 771
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 773
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 778
 (.branch 776
 (.leaf (.quota 2))
 (.branch 777
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 780
 (.branch 779
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))))
 (.branch 808
 (.branch 795
 (.branch 788
 (.branch 785
 (.leaf (.quota 1))
 (.branch 786
 (.leaf (.quota 1))
 (.branch 787
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 791
 (.branch 789
 (.leaf (.quota 1))
 (.branch 790
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 793
 (.branch 792
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))))
 (.branch 801
 (.branch 798
 (.leaf (.quota 1))
 (.branch 799
 (.leaf (.quota 1))
 (.branch 800
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.branch 804
 (.leaf (.quota 2))
 (.branch 806
 (.branch 805
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))))
 (.branch 821
 (.branch 814
 (.branch 811
 (.branch 809
 (.leaf (.quota 1))
 (.branch 810
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 817
 (.branch 815
 (.leaf (.quota 1))
 (.branch 816
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 819
 (.branch 818
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 828
 (.branch 824
 (.branch 822
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0867.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0867.rawLeaves 172 (RootedForests.RootedSubsumedForest0870.rawLeaves i) (routes.get i)

def disposition (j : Fin 835) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0867.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0867

/- Original module: RootedQuotaTransfer0867Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0867
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0867
