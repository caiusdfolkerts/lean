module
prelude
public import QuotaLeafTransfer
public import FiniteChecks
public import RootedSubsumedForest0745Dispositions
public import RootedSubsumedForest0837Data
public import RootedSubsumedForest0746Dispositions
public import RootedSubsumedForest0846Data
public import RootedSubsumedForest0757Dispositions
public import RootedSubsumedForest0840Data
public import RootedSubsumedForest0758Dispositions
public import RootedSubsumedForest0861Data
public import RootedSubsumedForest0759Dispositions
public import RootedSubsumedForest0848Data
public import RootedSubsumedForest0770Dispositions
public import RootedSubsumedForest0817Data
public import RootedSubsumedForest0771Dispositions
public import RootedSubsumedForest0845Data
public import RootedSubsumedForest0777Dispositions
public import RootedSubsumedForest0822Data
public import RootedSubsumedForest0778Dispositions
public import RootedSubsumedForest0850Data
public import RootedSubsumedForest0779Dispositions
public import RootedSubsumedForest0828Data
public import RootedSubsumedForest0787Dispositions
public import RootedSubsumedForest0827Data
public import RootedSubsumedForest0789Dispositions
public import RootedSubsumedForest0830Data
public import RootedSubsumedForest0790Dispositions
public import RootedSubsumedForest0854Data
public import RootedSubsumedForest0794Dispositions
public import RootedSubsumedForest0795Dispositions
public import RootedSubsumedForest0859Data
public import RootedSubsumedForest0804Dispositions
public import RootedSubsumedForest0806Dispositions
public import RootedSubsumedForest0807Dispositions
public import RootedSubsumedForest0808Dispositions
public import RootedSubsumedForest0809Dispositions
public import RootedSubsumedForest0810Dispositions
public import RootedSubsumedForest0819Dispositions
public import RootedSubsumedForest0821Dispositions
public import RootedSubsumedForest0823Dispositions
public import RootedSubsumedForest0864Data
public import RootedSubsumedForest0824Dispositions
public import RootedSubsumedForest0825Dispositions
public import RootedSubsumedForest0865Data
public import RootedSubsumedForest0829Dispositions
public import RootedSubsumedForest0853Data
public import RootedSubsumedForest0831Dispositions
public import RootedSubsumedForest0833Dispositions
public import RootedSubsumedForest0866Data
public import RootedSubsumedForest0834Dispositions
public import RootedSubsumedForest0839Dispositions
public import RootedSubsumedForest0841Dispositions
public import RootedSubsumedForest0868Data
public import RootedSubsumedForest0842Dispositions
public import RootedSubsumedForest0843Dispositions
public import RootedSubsumedForest0869Data
public import RootedSubsumedForest0847Dispositions
public import RootedSubsumedForest0863Data
public import RootedSubsumedForest0849Dispositions
public import RootedSubsumedForest0851Dispositions
public import RootedSubsumedForest0856Dispositions
public import RootedSubsumedForest0857Dispositions
public import RootedSubsumedForest0870Data

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/- Original module: RootedQuotaTransfer0745Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0745
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 745: use the complete forest for case 837, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0745.quota k ≤ RootedForests.RootedSubsumedForest0837.quota k := by
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
(.leaf (.quota 0))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0745.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0745.rawLeaves 1 (RootedForests.RootedSubsumedForest0837.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0745.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0745

/- Original module: RootedQuotaTransfer0745Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0745
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 1 :=
  interval_of_check test0 0 1 (by decide +kernel)

theorem test0_complete : Interval test0 0 1 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 1 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0745

/- Original module: RootedQuotaTransfer0745. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0745
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0745.quota
      ((RootedForests.RootedSubsumedForest0837.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0745.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0745.rawLeaves 1 RootedForests.RootedSubsumedForest0745.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0745.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0837.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0745

/- Original module: RootedQuotaTransfer0746Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0746
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 746: use the complete forest for case 846, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0746.quota k ≤ RootedForests.RootedSubsumedForest0846.quota k := by
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
(.leaf (.quota 0))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0746.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0746.rawLeaves 1 (RootedForests.RootedSubsumedForest0846.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0746.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0746

/- Original module: RootedQuotaTransfer0746Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0746
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 1 :=
  interval_of_check test0 0 1 (by decide +kernel)

theorem test0_complete : Interval test0 0 1 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 1 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0746

/- Original module: RootedQuotaTransfer0746. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0746
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0746.quota
      ((RootedForests.RootedSubsumedForest0846.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0746.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0746.rawLeaves 1 RootedForests.RootedSubsumedForest0746.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0746.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0846.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0746

/- Original module: RootedQuotaTransfer0757Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0757
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 757: use the complete forest for case 840, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0757.quota k ≤ RootedForests.RootedSubsumedForest0840.quota k := by
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
(.leaf (.quota 0))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0757.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0757.rawLeaves 1 (RootedForests.RootedSubsumedForest0840.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0757.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0757

/- Original module: RootedQuotaTransfer0757Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0757
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 1 :=
  interval_of_check test0 0 1 (by decide +kernel)

theorem test0_complete : Interval test0 0 1 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 1 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0757

/- Original module: RootedQuotaTransfer0757. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0757
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0757.quota
      ((RootedForests.RootedSubsumedForest0840.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0757.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0757.rawLeaves 1 RootedForests.RootedSubsumedForest0757.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0757.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0840.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0757

/- Original module: RootedQuotaTransfer0758Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0758
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 758: use the complete forest for case 861, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0758.quota k ≤ RootedForests.RootedSubsumedForest0861.quota k := by
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
(.leaf (.quota 0))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0758.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0758.rawLeaves 1 (RootedForests.RootedSubsumedForest0861.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0758.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0758

/- Original module: RootedQuotaTransfer0758Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0758
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 1 :=
  interval_of_check test0 0 1 (by decide +kernel)

theorem test0_complete : Interval test0 0 1 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 1 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0758

/- Original module: RootedQuotaTransfer0758. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0758
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0758.quota
      ((RootedForests.RootedSubsumedForest0861.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0758.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0758.rawLeaves 1 RootedForests.RootedSubsumedForest0758.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0758.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0861.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0758

/- Original module: RootedQuotaTransfer0759Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0759
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 759: use the complete forest for case 848, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0759.quota k ≤ RootedForests.RootedSubsumedForest0848.quota k := by
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
(.branch 2
 (.leaf (.quota 1))
 (.branch 3
 (.leaf (.quota 2))
 (.leaf (.reuse 1))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0759.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0759.rawLeaves 2 (RootedForests.RootedSubsumedForest0848.rawLeaves i) (routes.get i)

def disposition (j : Fin 4) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0759.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0759

/- Original module: RootedQuotaTransfer0759Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0759
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 4 :=
  interval_of_check test0 0 4 (by decide +kernel)

theorem test0_complete : Interval test0 0 4 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 4 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0759

/- Original module: RootedQuotaTransfer0759. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0759
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 4 :=
  routeInterval0

theorem disposition_checked (j : Fin 4) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0759.quota
      ((RootedForests.RootedSubsumedForest0848.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0759.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0759.rawLeaves 2 RootedForests.RootedSubsumedForest0759.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0759.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0848.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0759

/- Original module: RootedQuotaTransfer0770Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0770
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 770: use the complete forest for case 817, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0770.quota k ≤ RootedForests.RootedSubsumedForest0817.quota k := by
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
(.leaf (.quota 0))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0770.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0770.rawLeaves 1 (RootedForests.RootedSubsumedForest0817.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0770.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0770

/- Original module: RootedQuotaTransfer0770Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0770
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 1 :=
  interval_of_check test0 0 1 (by decide +kernel)

theorem test0_complete : Interval test0 0 1 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 1 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0770

/- Original module: RootedQuotaTransfer0770. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0770
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0770.quota
      ((RootedForests.RootedSubsumedForest0817.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0770.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0770.rawLeaves 1 RootedForests.RootedSubsumedForest0770.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0770.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0817.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0770

/- Original module: RootedQuotaTransfer0771Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0771
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 771: use the complete forest for case 845, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0771.quota k ≤ RootedForests.RootedSubsumedForest0845.quota k := by
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
(.leaf (.quota 1))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0771.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0771.rawLeaves 1 (RootedForests.RootedSubsumedForest0845.rawLeaves i) (routes.get i)

def disposition (j : Fin 4) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0771.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0771

/- Original module: RootedQuotaTransfer0771Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0771
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 4 :=
  interval_of_check test0 0 4 (by decide +kernel)

theorem test0_complete : Interval test0 0 4 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 4 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0771

/- Original module: RootedQuotaTransfer0771. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0771
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 4 :=
  routeInterval0

theorem disposition_checked (j : Fin 4) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0771.quota
      ((RootedForests.RootedSubsumedForest0845.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0771.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0771.rawLeaves 1 RootedForests.RootedSubsumedForest0771.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0771.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0845.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0771

/- Original module: RootedQuotaTransfer0777Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0777
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 777: use the complete forest for case 822, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0777.quota k ≤ RootedForests.RootedSubsumedForest0822.quota k := by
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
(.leaf (.quota 0))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0777.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0777.rawLeaves 1 (RootedForests.RootedSubsumedForest0822.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0777.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0777

/- Original module: RootedQuotaTransfer0777Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0777
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 1 :=
  interval_of_check test0 0 1 (by decide +kernel)

theorem test0_complete : Interval test0 0 1 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 1 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0777

/- Original module: RootedQuotaTransfer0777. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0777
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0777.quota
      ((RootedForests.RootedSubsumedForest0822.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0777.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0777.rawLeaves 1 RootedForests.RootedSubsumedForest0777.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0777.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0822.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0777

/- Original module: RootedQuotaTransfer0778Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0778
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 778: use the complete forest for case 850, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0778.quota k ≤ RootedForests.RootedSubsumedForest0850.quota k := by
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
(.branch 3
 (.leaf (.quota 1))
 (.branch 4
 (.leaf (.quota 1))
 (.branch 5
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0778.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0778.rawLeaves 1 (RootedForests.RootedSubsumedForest0850.rawLeaves i) (routes.get i)

def disposition (j : Fin 6) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0778.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0778

/- Original module: RootedQuotaTransfer0778Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0778
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 6 :=
  interval_of_check test0 0 6 (by decide +kernel)

theorem test0_complete : Interval test0 0 6 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 6 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0778

/- Original module: RootedQuotaTransfer0778. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0778
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 6 :=
  routeInterval0

theorem disposition_checked (j : Fin 6) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0778.quota
      ((RootedForests.RootedSubsumedForest0850.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0778.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0778.rawLeaves 1 RootedForests.RootedSubsumedForest0778.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0778.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0850.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0778

/- Original module: RootedQuotaTransfer0779Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0779
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 779: use the complete forest for case 828, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0779.quota k ≤ RootedForests.RootedSubsumedForest0828.quota k := by
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
(.leaf (.quota 3))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0779.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0779.rawLeaves 2 (RootedForests.RootedSubsumedForest0828.rawLeaves i) (routes.get i)

def disposition (j : Fin 2) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0779.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0779

/- Original module: RootedQuotaTransfer0779Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0779
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 2 :=
  interval_of_check test0 0 2 (by decide +kernel)

theorem test0_complete : Interval test0 0 2 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 2 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0779

/- Original module: RootedQuotaTransfer0779. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0779
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 2 :=
  routeInterval0

theorem disposition_checked (j : Fin 2) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0779.quota
      ((RootedForests.RootedSubsumedForest0828.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0779.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0779.rawLeaves 2 RootedForests.RootedSubsumedForest0779.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0779.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0828.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0779

/- Original module: RootedQuotaTransfer0787Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0787
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 787: use the complete forest for case 827, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0787.quota k ≤ RootedForests.RootedSubsumedForest0827.quota k := by
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
(.branch 1
 (.leaf (.quota 1))
 (.leaf (.quota 10)))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0787.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0787.rawLeaves 1 (RootedForests.RootedSubsumedForest0827.rawLeaves i) (routes.get i)

def disposition (j : Fin 2) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0787.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0787

/- Original module: RootedQuotaTransfer0787Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0787
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 2 :=
  interval_of_check test0 0 2 (by decide +kernel)

theorem test0_complete : Interval test0 0 2 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 2 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0787

/- Original module: RootedQuotaTransfer0787. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0787
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 2 :=
  routeInterval0

theorem disposition_checked (j : Fin 2) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0787.quota
      ((RootedForests.RootedSubsumedForest0827.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0787.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0787.rawLeaves 1 RootedForests.RootedSubsumedForest0787.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0787.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0827.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0787

/- Original module: RootedQuotaTransfer0789Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0789
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 789: use the complete forest for case 830, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0789.quota k ≤ RootedForests.RootedSubsumedForest0830.quota k := by
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
(.branch 1
 (.leaf (.quota 1))
 (.branch 2
 (.leaf (.quota 9))
 (.leaf (.quota 3))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0789.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0789.rawLeaves 2 (RootedForests.RootedSubsumedForest0830.rawLeaves i) (routes.get i)

def disposition (j : Fin 3) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0789.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0789

/- Original module: RootedQuotaTransfer0789Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0789
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 3 :=
  interval_of_check test0 0 3 (by decide +kernel)

theorem test0_complete : Interval test0 0 3 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 3 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0789

/- Original module: RootedQuotaTransfer0789. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0789
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 3 :=
  routeInterval0

theorem disposition_checked (j : Fin 3) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0789.quota
      ((RootedForests.RootedSubsumedForest0830.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0789.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0789.rawLeaves 2 RootedForests.RootedSubsumedForest0789.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0789.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0830.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0789

/- Original module: RootedQuotaTransfer0790Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0790
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 790: use the complete forest for case 854, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0790.quota k ≤ RootedForests.RootedSubsumedForest0854.quota k := by
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
(.leaf (.quota 1))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0790.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0790.rawLeaves 1 (RootedForests.RootedSubsumedForest0854.rawLeaves i) (routes.get i)

def disposition (j : Fin 7) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0790.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0790

/- Original module: RootedQuotaTransfer0790Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0790
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 7 :=
  interval_of_check test0 0 7 (by decide +kernel)

theorem test0_complete : Interval test0 0 7 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 7 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0790

/- Original module: RootedQuotaTransfer0790. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0790
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 7 :=
  routeInterval0

theorem disposition_checked (j : Fin 7) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0790.quota
      ((RootedForests.RootedSubsumedForest0854.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0790.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0790.rawLeaves 1 RootedForests.RootedSubsumedForest0790.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0790.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0854.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0790

/- Original module: RootedQuotaTransfer0794Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0794
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 794: use the complete forest for case 837, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0794.quota k ≤ RootedForests.RootedSubsumedForest0837.quota k := by
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
(.leaf (.quota 0))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0794.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0794.rawLeaves 1 (RootedForests.RootedSubsumedForest0837.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0794.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0794

/- Original module: RootedQuotaTransfer0794Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0794
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 1 :=
  interval_of_check test0 0 1 (by decide +kernel)

theorem test0_complete : Interval test0 0 1 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 1 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0794

/- Original module: RootedQuotaTransfer0794. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0794
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0794.quota
      ((RootedForests.RootedSubsumedForest0837.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0794.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0794.rawLeaves 1 RootedForests.RootedSubsumedForest0794.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0794.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0837.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0794

/- Original module: RootedQuotaTransfer0795Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0795
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 795: use the complete forest for case 859, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0795.quota k ≤ RootedForests.RootedSubsumedForest0859.quota k := by
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
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.quota 1))
 (.leaf (.reuse 0)))
 (.leaf (.quota 1)))
 (.branch 6
 (.leaf (.quota 1))
 (.branch 7
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0795.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0795.rawLeaves 2 (RootedForests.RootedSubsumedForest0859.rawLeaves i) (routes.get i)

def disposition (j : Fin 8) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0795.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0795

/- Original module: RootedQuotaTransfer0795Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0795
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 8 :=
  interval_of_check test0 0 8 (by decide +kernel)

theorem test0_complete : Interval test0 0 8 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 8 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0795

/- Original module: RootedQuotaTransfer0795. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0795
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 8 :=
  routeInterval0

theorem disposition_checked (j : Fin 8) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0795.quota
      ((RootedForests.RootedSubsumedForest0859.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0795.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0795.rawLeaves 2 RootedForests.RootedSubsumedForest0795.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0795.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0859.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0795

/- Original module: RootedQuotaTransfer0804Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0804
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 804: use the complete forest for case 837, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0804.quota k ≤ RootedForests.RootedSubsumedForest0837.quota k := by
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
(.leaf (.quota 0))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0804.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0804.rawLeaves 1 (RootedForests.RootedSubsumedForest0837.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0804.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0804

/- Original module: RootedQuotaTransfer0804Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0804
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 1 :=
  interval_of_check test0 0 1 (by decide +kernel)

theorem test0_complete : Interval test0 0 1 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 1 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0804

/- Original module: RootedQuotaTransfer0804. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0804
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0804.quota
      ((RootedForests.RootedSubsumedForest0837.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0804.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0804.rawLeaves 1 RootedForests.RootedSubsumedForest0804.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0804.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0837.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0804

/- Original module: RootedQuotaTransfer0806Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0806
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 806: use the complete forest for case 859, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0806.quota k ≤ RootedForests.RootedSubsumedForest0859.quota k := by
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
(.leaf (.quota 1))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0806.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0806.rawLeaves 1 (RootedForests.RootedSubsumedForest0859.rawLeaves i) (routes.get i)

def disposition (j : Fin 8) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0806.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0806

/- Original module: RootedQuotaTransfer0806Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0806
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 8 :=
  interval_of_check test0 0 8 (by decide +kernel)

theorem test0_complete : Interval test0 0 8 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 8 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0806

/- Original module: RootedQuotaTransfer0806. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0806
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 8 :=
  routeInterval0

theorem disposition_checked (j : Fin 8) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0806.quota
      ((RootedForests.RootedSubsumedForest0859.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0806.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0806.rawLeaves 1 RootedForests.RootedSubsumedForest0806.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0806.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0859.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0806

/- Original module: RootedQuotaTransfer0807Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0807
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 807: use the complete forest for case 840, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0807.quota k ≤ RootedForests.RootedSubsumedForest0840.quota k := by
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
(.leaf (.quota 0))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0807.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0807.rawLeaves 1 (RootedForests.RootedSubsumedForest0840.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0807.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0807

/- Original module: RootedQuotaTransfer0807Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0807
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 1 :=
  interval_of_check test0 0 1 (by decide +kernel)

theorem test0_complete : Interval test0 0 1 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 1 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0807

/- Original module: RootedQuotaTransfer0807. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0807
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0807.quota
      ((RootedForests.RootedSubsumedForest0840.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0807.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0807.rawLeaves 1 RootedForests.RootedSubsumedForest0807.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0807.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0840.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0807

/- Original module: RootedQuotaTransfer0808Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0808
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 808: use the complete forest for case 846, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0808.quota k ≤ RootedForests.RootedSubsumedForest0846.quota k := by
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
(.leaf (.quota 0))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0808.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0808.rawLeaves 1 (RootedForests.RootedSubsumedForest0846.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0808.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0808

/- Original module: RootedQuotaTransfer0808Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0808
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 1 :=
  interval_of_check test0 0 1 (by decide +kernel)

theorem test0_complete : Interval test0 0 1 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 1 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0808

/- Original module: RootedQuotaTransfer0808. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0808
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0808.quota
      ((RootedForests.RootedSubsumedForest0846.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0808.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0808.rawLeaves 1 RootedForests.RootedSubsumedForest0808.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0808.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0846.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0808

/- Original module: RootedQuotaTransfer0809Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0809
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 809: use the complete forest for case 861, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0809.quota k ≤ RootedForests.RootedSubsumedForest0861.quota k := by
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
(.leaf (.quota 0))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0809.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0809.rawLeaves 1 (RootedForests.RootedSubsumedForest0861.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0809.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0809

/- Original module: RootedQuotaTransfer0809Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0809
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 1 :=
  interval_of_check test0 0 1 (by decide +kernel)

theorem test0_complete : Interval test0 0 1 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 1 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0809

/- Original module: RootedQuotaTransfer0809. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0809
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0809.quota
      ((RootedForests.RootedSubsumedForest0861.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0809.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0809.rawLeaves 1 RootedForests.RootedSubsumedForest0809.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0809.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0861.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0809

/- Original module: RootedQuotaTransfer0810Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0810
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 810: use the complete forest for case 848, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0810.quota k ≤ RootedForests.RootedSubsumedForest0848.quota k := by
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
(.branch 2
 (.branch 1
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0810.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0810.rawLeaves 4 (RootedForests.RootedSubsumedForest0848.rawLeaves i) (routes.get i)

def disposition (j : Fin 4) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0810.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0810

/- Original module: RootedQuotaTransfer0810Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0810
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 4 :=
  interval_of_check test0 0 4 (by decide +kernel)

theorem test0_complete : Interval test0 0 4 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 4 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0810

/- Original module: RootedQuotaTransfer0810. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0810
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 4 :=
  routeInterval0

theorem disposition_checked (j : Fin 4) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0810.quota
      ((RootedForests.RootedSubsumedForest0848.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0810.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0810.rawLeaves 4 RootedForests.RootedSubsumedForest0810.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0810.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0848.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0810

/- Original module: RootedQuotaTransfer0819Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0819
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 819: use the complete forest for case 845, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0819.quota k ≤ RootedForests.RootedSubsumedForest0845.quota k := by
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
(.branch 2
 (.leaf (.quota 1))
 (.branch 3
 (.leaf (.quota 10))
 (.leaf (.quota 1))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0819.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0819.rawLeaves 1 (RootedForests.RootedSubsumedForest0845.rawLeaves i) (routes.get i)

def disposition (j : Fin 4) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0819.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0819

/- Original module: RootedQuotaTransfer0819Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0819
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 4 :=
  interval_of_check test0 0 4 (by decide +kernel)

theorem test0_complete : Interval test0 0 4 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 4 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0819

/- Original module: RootedQuotaTransfer0819. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0819
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 4 :=
  routeInterval0

theorem disposition_checked (j : Fin 4) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0819.quota
      ((RootedForests.RootedSubsumedForest0845.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0819.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0819.rawLeaves 1 RootedForests.RootedSubsumedForest0819.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0819.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0845.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0819

/- Original module: RootedQuotaTransfer0821Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0821
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 821: use the complete forest for case 848, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0821.quota k ≤ RootedForests.RootedSubsumedForest0848.quota k := by
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
(.branch 2
 (.leaf (.quota 1))
 (.leaf (.quota 2)))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0821.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0821.rawLeaves 2 (RootedForests.RootedSubsumedForest0848.rawLeaves i) (routes.get i)

def disposition (j : Fin 4) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0821.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0821

/- Original module: RootedQuotaTransfer0821Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0821
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 4 :=
  interval_of_check test0 0 4 (by decide +kernel)

theorem test0_complete : Interval test0 0 4 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 4 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0821

/- Original module: RootedQuotaTransfer0821. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0821
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 4 :=
  routeInterval0

theorem disposition_checked (j : Fin 4) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0821.quota
      ((RootedForests.RootedSubsumedForest0848.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0821.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0821.rawLeaves 2 RootedForests.RootedSubsumedForest0821.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0821.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0848.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0821

/- Original module: RootedQuotaTransfer0823Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0823
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 823: use the complete forest for case 864, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0823.quota k ≤ RootedForests.RootedSubsumedForest0864.quota k := by
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
(.branch 20
 (.leaf (.quota 1))
 (.branch 30
 (.leaf (.quota 1))
 (.branch 35
 (.leaf (.quota 1))
 (.branch 38
 (.branch 36
 (.leaf (.quota 1))
 (.branch 37
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0823.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0823.rawLeaves 1 (RootedForests.RootedSubsumedForest0864.rawLeaves i) (routes.get i)

def disposition (j : Fin 41) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0823.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0823

/- Original module: RootedQuotaTransfer0823Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0823
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 16 :=
  interval_of_check test0 0 16 (by decide +kernel)

theorem test0_block_1 : Interval test0 16 32 :=
  interval_of_check test0 16 16 (by decide +kernel)

theorem test0_block_2 : Interval test0 32 41 :=
  interval_of_check test0 32 9 (by decide +kernel)

theorem test0_complete : Interval test0 0 41 :=
  (interval_append test0 0 16 41
  test0_block_0
  (interval_append test0 16 32 41
  test0_block_1
  test0_block_2))
theorem routeInterval0 : Interval routeTest 0 41 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0823

/- Original module: RootedQuotaTransfer0823. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0823
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 41 :=
  routeInterval0

theorem disposition_checked (j : Fin 41) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0823.quota
      ((RootedForests.RootedSubsumedForest0864.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0823.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0823.rawLeaves 1 RootedForests.RootedSubsumedForest0823.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0823.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0864.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0823

/- Original module: RootedQuotaTransfer0824Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0824
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 824: use the complete forest for case 850, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0824.quota k ≤ RootedForests.RootedSubsumedForest0850.quota k := by
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
(.branch 3
 (.branch 1
 (.leaf (.quota 1))
 (.branch 2
 (.leaf (.quota 1))
 (.leaf (.quota 9))))
 (.leaf (.quota 1)))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0824.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0824.rawLeaves 2 (RootedForests.RootedSubsumedForest0850.rawLeaves i) (routes.get i)

def disposition (j : Fin 6) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0824.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0824

/- Original module: RootedQuotaTransfer0824Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0824
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 6 :=
  interval_of_check test0 0 6 (by decide +kernel)

theorem test0_complete : Interval test0 0 6 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 6 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0824

/- Original module: RootedQuotaTransfer0824. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0824
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 6 :=
  routeInterval0

theorem disposition_checked (j : Fin 6) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0824.quota
      ((RootedForests.RootedSubsumedForest0850.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0824.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0824.rawLeaves 2 RootedForests.RootedSubsumedForest0824.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0824.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0850.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0824

/- Original module: RootedQuotaTransfer0825Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0825
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 825: use the complete forest for case 865, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0825.quota k ≤ RootedForests.RootedSubsumedForest0865.quota k := by
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
(.branch 18
 (.branch 9
 (.branch 4
 (.leaf (.quota 1))
 (.branch 6
 (.branch 5
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 7
 (.leaf (.quota 1))
 (.branch 8
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.leaf (.quota 1)))
 (.branch 27
 (.branch 22
 (.leaf (.quota 1))
 (.branch 24
 (.branch 23
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))
 (.branch 31
 (.leaf (.quota 1))
 (.branch 33
 (.leaf (.quota 1))
 (.branch 34
 (.leaf (.quota 1))
 (.branch 35
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0825.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0825.rawLeaves 6 (RootedForests.RootedSubsumedForest0865.rawLeaves i) (routes.get i)

def disposition (j : Fin 36) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0825.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0825

/- Original module: RootedQuotaTransfer0825Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0825
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 16 :=
  interval_of_check test0 0 16 (by decide +kernel)

theorem test0_block_1 : Interval test0 16 32 :=
  interval_of_check test0 16 16 (by decide +kernel)

theorem test0_block_2 : Interval test0 32 36 :=
  interval_of_check test0 32 4 (by decide +kernel)

theorem test0_complete : Interval test0 0 36 :=
  (interval_append test0 0 16 36
  test0_block_0
  (interval_append test0 16 32 36
  test0_block_1
  test0_block_2))
theorem routeInterval0 : Interval routeTest 0 36 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0825

/- Original module: RootedQuotaTransfer0825. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0825
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 36 :=
  routeInterval0

theorem disposition_checked (j : Fin 36) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0825.quota
      ((RootedForests.RootedSubsumedForest0865.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0825.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0825.rawLeaves 6 RootedForests.RootedSubsumedForest0825.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0825.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0865.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0825

/- Original module: RootedQuotaTransfer0829Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0829
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 829: use the complete forest for case 853, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0829.quota k ≤ RootedForests.RootedSubsumedForest0853.quota k := by
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
(.leaf (.quota 1))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0829.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0829.rawLeaves 1 (RootedForests.RootedSubsumedForest0853.rawLeaves i) (routes.get i)

def disposition (j : Fin 4) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0829.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0829

/- Original module: RootedQuotaTransfer0829Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0829
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 4 :=
  interval_of_check test0 0 4 (by decide +kernel)

theorem test0_complete : Interval test0 0 4 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 4 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0829

/- Original module: RootedQuotaTransfer0829. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0829
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 4 :=
  routeInterval0

theorem disposition_checked (j : Fin 4) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0829.quota
      ((RootedForests.RootedSubsumedForest0853.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0829.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0829.rawLeaves 1 RootedForests.RootedSubsumedForest0829.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0829.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0853.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0829

/- Original module: RootedQuotaTransfer0831Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0831
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 831: use the complete forest for case 854, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0831.quota k ≤ RootedForests.RootedSubsumedForest0854.quota k := by
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
(.branch 3
 (.branch 1
 (.leaf (.quota 3))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0831.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0831.rawLeaves 1 (RootedForests.RootedSubsumedForest0854.rawLeaves i) (routes.get i)

def disposition (j : Fin 7) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0831.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0831

/- Original module: RootedQuotaTransfer0831Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0831
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 7 :=
  interval_of_check test0 0 7 (by decide +kernel)

theorem test0_complete : Interval test0 0 7 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 7 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0831

/- Original module: RootedQuotaTransfer0831. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0831
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 7 :=
  routeInterval0

theorem disposition_checked (j : Fin 7) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0831.quota
      ((RootedForests.RootedSubsumedForest0854.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0831.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0831.rawLeaves 1 RootedForests.RootedSubsumedForest0831.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0831.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0854.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0831

/- Original module: RootedQuotaTransfer0833Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0833
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 833: use the complete forest for case 866, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0833.quota k ≤ RootedForests.RootedSubsumedForest0866.quota k := by
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
(.leaf (.quota 0))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0833.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0833.rawLeaves 1 (RootedForests.RootedSubsumedForest0866.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0833.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0833

/- Original module: RootedQuotaTransfer0833Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0833
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 1 :=
  interval_of_check test0 0 1 (by decide +kernel)

theorem test0_complete : Interval test0 0 1 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 1 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0833

/- Original module: RootedQuotaTransfer0833. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0833
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0833.quota
      ((RootedForests.RootedSubsumedForest0866.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0833.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0833.rawLeaves 1 RootedForests.RootedSubsumedForest0833.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0833.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0866.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0833

/- Original module: RootedQuotaTransfer0834Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0834
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 834: use the complete forest for case 859, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0834.quota k ≤ RootedForests.RootedSubsumedForest0859.quota k := by
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
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.reuse 0))
 (.leaf (.quota 1)))
 (.leaf (.quota 2)))
 (.branch 6
 (.leaf (.quota 2))
 (.branch 7
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0834.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0834.rawLeaves 8 (RootedForests.RootedSubsumedForest0859.rawLeaves i) (routes.get i)

def disposition (j : Fin 8) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0834.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0834

/- Original module: RootedQuotaTransfer0834Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0834
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 8 :=
  interval_of_check test0 0 8 (by decide +kernel)

theorem test0_complete : Interval test0 0 8 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 8 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0834

/- Original module: RootedQuotaTransfer0834. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0834
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 8 :=
  routeInterval0

theorem disposition_checked (j : Fin 8) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0834.quota
      ((RootedForests.RootedSubsumedForest0859.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0834.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0834.rawLeaves 8 RootedForests.RootedSubsumedForest0834.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0834.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0859.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0834

/- Original module: RootedQuotaTransfer0839Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0839
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 839: use the complete forest for case 859, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0839.quota k ≤ RootedForests.RootedSubsumedForest0859.quota k := by
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
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.branch 6
 (.leaf (.quota 1))
 (.branch 7
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0839.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0839.rawLeaves 2 (RootedForests.RootedSubsumedForest0859.rawLeaves i) (routes.get i)

def disposition (j : Fin 8) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0839.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0839

/- Original module: RootedQuotaTransfer0839Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0839
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 8 :=
  interval_of_check test0 0 8 (by decide +kernel)

theorem test0_complete : Interval test0 0 8 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 8 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0839

/- Original module: RootedQuotaTransfer0839. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0839
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 8 :=
  routeInterval0

theorem disposition_checked (j : Fin 8) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0839.quota
      ((RootedForests.RootedSubsumedForest0859.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0839.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0839.rawLeaves 2 RootedForests.RootedSubsumedForest0839.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0839.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0859.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0839

/- Original module: RootedQuotaTransfer0841Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0841
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 841: use the complete forest for case 868, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0841.quota k ≤ RootedForests.RootedSubsumedForest0868.quota k := by
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
 (.leaf (.quota 1))
 (.branch 106
 (.branch 103
 (.leaf (.quota 1))
 (.branch 104
 (.leaf (.quota 1))
 (.branch 105
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 157
 (.leaf (.quota 1))
 (.branch 168
 (.leaf (.quota 1))
 (.branch 174
 (.branch 171
 (.branch 169
 (.leaf (.quota 1))
 (.branch 170
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 172
 (.leaf (.quota 1))
 (.branch 173
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0841.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0841.rawLeaves 3 (RootedForests.RootedSubsumedForest0868.rawLeaves i) (routes.get i)

def disposition (j : Fin 180) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0841.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0841

/- Original module: RootedQuotaTransfer0841Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0841
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0841

/- Original module: RootedQuotaTransfer0841Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0841
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0841

/- Original module: RootedQuotaTransfer0841. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0841
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 180 :=
  (interval_append routeTest 0 128 180
  routeInterval0
  routeInterval128)

theorem disposition_checked (j : Fin 180) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0841.quota
      ((RootedForests.RootedSubsumedForest0868.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0841.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0841.rawLeaves 3 RootedForests.RootedSubsumedForest0841.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0841.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0868.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0841

/- Original module: RootedQuotaTransfer0842Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0842
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 842: use the complete forest for case 861, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0842.quota k ≤ RootedForests.RootedSubsumedForest0861.quota k := by
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
(.leaf (.quota 0))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0842.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0842.rawLeaves 1 (RootedForests.RootedSubsumedForest0861.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0842.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0842

/- Original module: RootedQuotaTransfer0842Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0842
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 1 :=
  interval_of_check test0 0 1 (by decide +kernel)

theorem test0_complete : Interval test0 0 1 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 1 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0842

/- Original module: RootedQuotaTransfer0842. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0842
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0842.quota
      ((RootedForests.RootedSubsumedForest0861.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0842.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0842.rawLeaves 1 RootedForests.RootedSubsumedForest0842.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0842.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0861.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0842

/- Original module: RootedQuotaTransfer0843Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0843
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 843: use the complete forest for case 869, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0843.quota k ≤ RootedForests.RootedSubsumedForest0869.quota k := by
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
 (.leaf (.quota 1))
 (.branch 8
 (.leaf (.quota 1))
 (.branch 9
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.branch 33
 (.leaf (.quota 1))
 (.branch 39
 (.branch 36
 (.branch 34
 (.leaf (.quota 1))
 (.branch 35
 (.leaf (.quota 1))
 (.leaf (.quota 3))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 67
 (.leaf (.quota 1))
 (.branch 78
 (.leaf (.quota 1))
 (.branch 84
 (.branch 81
 (.leaf (.quota 1))
 (.branch 82
 (.leaf (.quota 1))
 (.branch 83
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 87
 (.leaf (.quota 1))
 (.branch 88
 (.leaf (.quota 1))
 (.branch 89
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))))))
 (.branch 135
 (.branch 112
 (.branch 101
 (.branch 95
 (.branch 92
 (.branch 91
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 123
 (.leaf (.quota 1))
 (.branch 129
 (.branch 126
 (.leaf (.quota 1))
 (.branch 127
 (.leaf (.quota 1))
 (.branch 128
 (.leaf (.reuse 6))
 (.leaf (.quota 1)))))
 (.branch 132
 (.leaf (.quota 1))
 (.branch 133
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 158
 (.branch 146
 (.branch 140
 (.branch 137
 (.leaf (.quota 1))
 (.branch 138
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 143
 (.branch 141
 (.leaf (.quota 1))
 (.branch 142
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 152
 (.leaf (.quota 1))
 (.branch 155
 (.leaf (.quota 1))
 (.branch 156
 (.leaf (.quota 1))
 (.branch 157
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))))
 (.branch 169
 (.branch 163
 (.leaf (.quota 1))
 (.branch 166
 (.leaf (.quota 1))
 (.branch 167
 (.leaf (.reuse 13))
 (.leaf (.quota 1)))))
 (.branch 175
 (.branch 172
 (.leaf (.quota 1))
 (.branch 173
 (.leaf (.quota 1))
 (.branch 174
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 178
 (.branch 176
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 179
 (.leaf (.quota 1))
 (.branch 180
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0843.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0843.rawLeaves 18 (RootedForests.RootedSubsumedForest0869.rawLeaves i) (routes.get i)

def disposition (j : Fin 181) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0843.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0843

/- Original module: RootedQuotaTransfer0843Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0843
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0843

/- Original module: RootedQuotaTransfer0843Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0843
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0843

/- Original module: RootedQuotaTransfer0843. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0843
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 181 :=
  (interval_append routeTest 0 128 181
  routeInterval0
  routeInterval128)

theorem disposition_checked (j : Fin 181) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0843.quota
      ((RootedForests.RootedSubsumedForest0869.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0843.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0843.rawLeaves 18 RootedForests.RootedSubsumedForest0843.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0843.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0869.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0843

/- Original module: RootedQuotaTransfer0847Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0847
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 847: use the complete forest for case 863, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0847.quota k ≤ RootedForests.RootedSubsumedForest0863.quota k := by
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
(.leaf (.quota 1))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0847.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0847.rawLeaves 1 (RootedForests.RootedSubsumedForest0863.rawLeaves i) (routes.get i)

def disposition (j : Fin 3) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0847.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0847

/- Original module: RootedQuotaTransfer0847Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0847
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 3 :=
  interval_of_check test0 0 3 (by decide +kernel)

theorem test0_complete : Interval test0 0 3 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 3 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0847

/- Original module: RootedQuotaTransfer0847. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0847
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 3 :=
  routeInterval0

theorem disposition_checked (j : Fin 3) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0847.quota
      ((RootedForests.RootedSubsumedForest0863.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0847.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0847.rawLeaves 1 RootedForests.RootedSubsumedForest0847.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0847.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0863.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0847

/- Original module: RootedQuotaTransfer0849Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0849
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 849: use the complete forest for case 864, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0849.quota k ≤ RootedForests.RootedSubsumedForest0864.quota k := by
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
(.branch 20
 (.leaf (.quota 1))
 (.branch 30
 (.branch 25
 (.leaf (.quota 1))
 (.branch 27
 (.leaf (.quota 1))
 (.branch 28
 (.leaf (.quota 1))
 (.branch 29
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.leaf (.quota 1))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0849.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0849.rawLeaves 2 (RootedForests.RootedSubsumedForest0864.rawLeaves i) (routes.get i)

def disposition (j : Fin 41) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0849.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0849

/- Original module: RootedQuotaTransfer0849Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0849
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 16 :=
  interval_of_check test0 0 16 (by decide +kernel)

theorem test0_block_1 : Interval test0 16 32 :=
  interval_of_check test0 16 16 (by decide +kernel)

theorem test0_block_2 : Interval test0 32 41 :=
  interval_of_check test0 32 9 (by decide +kernel)

theorem test0_complete : Interval test0 0 41 :=
  (interval_append test0 0 16 41
  test0_block_0
  (interval_append test0 16 32 41
  test0_block_1
  test0_block_2))
theorem routeInterval0 : Interval routeTest 0 41 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0849

/- Original module: RootedQuotaTransfer0849. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0849
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 41 :=
  routeInterval0

theorem disposition_checked (j : Fin 41) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0849.quota
      ((RootedForests.RootedSubsumedForest0864.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0849.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0849.rawLeaves 2 RootedForests.RootedSubsumedForest0849.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0849.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0864.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0849

/- Original module: RootedQuotaTransfer0851Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0851
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 851: use the complete forest for case 865, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0851.quota k ≤ RootedForests.RootedSubsumedForest0865.quota k := by
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
(.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.quota 1))
 (.leaf (.quota 3)))
 (.branch 3
 (.leaf (.quota 9))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 24
 (.leaf (.quota 1))
 (.branch 25
 (.leaf (.quota 1))
 (.branch 26
 (.leaf (.quota 1))
 (.leaf (.quota 2))))))
 (.branch 31
 (.branch 29
 (.branch 28
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))
 (.branch 33
 (.branch 32
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0851.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0851.rawLeaves 13 (RootedForests.RootedSubsumedForest0865.rawLeaves i) (routes.get i)

def disposition (j : Fin 36) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0851.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0851

/- Original module: RootedQuotaTransfer0851Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0851
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 16 :=
  interval_of_check test0 0 16 (by decide +kernel)

theorem test0_block_1 : Interval test0 16 32 :=
  interval_of_check test0 16 16 (by decide +kernel)

theorem test0_block_2 : Interval test0 32 36 :=
  interval_of_check test0 32 4 (by decide +kernel)

theorem test0_complete : Interval test0 0 36 :=
  (interval_append test0 0 16 36
  test0_block_0
  (interval_append test0 16 32 36
  test0_block_1
  test0_block_2))
theorem routeInterval0 : Interval routeTest 0 36 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0851

/- Original module: RootedQuotaTransfer0851. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0851
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 36 :=
  routeInterval0

theorem disposition_checked (j : Fin 36) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0851.quota
      ((RootedForests.RootedSubsumedForest0865.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0851.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0851.rawLeaves 13 RootedForests.RootedSubsumedForest0851.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0851.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0865.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0851

/- Original module: RootedQuotaTransfer0856Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0856
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 856: use the complete forest for case 866, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0856.quota k ≤ RootedForests.RootedSubsumedForest0866.quota k := by
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
(.leaf (.quota 0))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0856.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0856.rawLeaves 1 (RootedForests.RootedSubsumedForest0866.rawLeaves i) (routes.get i)

def disposition (j : Fin 1) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0856.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0856

/- Original module: RootedQuotaTransfer0856Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0856
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

def test0 (i : Nat) := routeTest (i + 0)
theorem test0_block_0 : Interval test0 0 1 :=
  interval_of_check test0 0 1 (by decide +kernel)

theorem test0_complete : Interval test0 0 1 :=
  test0_block_0
theorem routeInterval0 : Interval routeTest 0 1 := by
  intro i hlo hhi
  have h := test0_complete (i - 0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedQuotaTransfers.Case0856

/- Original module: RootedQuotaTransfer0856. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0856
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 1 :=
  routeInterval0

theorem disposition_checked (j : Fin 1) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0856.quota
      ((RootedForests.RootedSubsumedForest0866.rawLeaves j.val).map RootedCaches.RootedSixExtra05.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0856.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0856.rawLeaves 1 RootedForests.RootedSubsumedForest0856.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0856.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0866.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)


end Papers.RationalityTen.RootedQuotaTransfers.Case0856

/- Original module: RootedQuotaTransfer0857Data. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0857
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 857: use the complete forest for case 870, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0857.quota k ≤ RootedForests.RootedSubsumedForest0870.quota k := by
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
 (.leaf (.quota 1))
 (.branch 35
 (.branch 33
 (.leaf (.quota 1))
 (.branch 34
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.branch 78
 (.leaf (.quota 1))
 (.branch 91
 (.branch 84
 (.leaf (.quota 1))
 (.branch 87
 (.leaf (.quota 1))
 (.branch 89
 (.branch 88
 (.leaf (.quota 1))
 (.leaf (.reuse 2)))
 (.leaf (.quota 1)))))
 (.branch 97
 (.branch 94
 (.branch 92
 (.leaf (.quota 1))
 (.branch 93
 (.leaf (.reuse 3))
 (.leaf (.quota 1))))
 (.branch 95
 (.leaf (.quota 1))
 (.branch 96
 (.leaf (.quota 1))
 (.leaf (.quota 2)))))
 (.leaf (.quota 1))))))
 (.leaf (.quota 1)))
 (.branch 312
 (.branch 260
 (.branch 234
 (.leaf (.quota 1))
 (.branch 247
 (.leaf (.quota 1))
 (.branch 253
 (.leaf (.quota 1))
 (.branch 256
 (.branch 254
 (.leaf (.quota 1))
 (.branch 255
 (.leaf (.reuse 5))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))))
 (.branch 286
 (.branch 273
 (.branch 266
 (.leaf (.quota 1))
 (.branch 269
 (.branch 267
 (.leaf (.quota 1))
 (.branch 268
 (.leaf (.quota 1))
 (.leaf (.reuse 6))))
 (.branch 271
 (.branch 270
 (.leaf (.reuse 7))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.branch 299
 (.branch 292
 (.branch 289
 (.branch 287
 (.leaf (.quota 1))
 (.branch 288
 (.leaf (.reuse 8))
 (.leaf (.reuse 9))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.branch 305
 (.branch 302
 (.leaf (.quota 1))
 (.branch 303
 (.leaf (.quota 1))
 (.branch 304
 (.leaf (.quota 1))
 (.leaf (.reuse 10)))))
 (.branch 308
 (.branch 306
 (.leaf (.reuse 11))
 (.branch 307
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))))))
 (.branch 364
 (.leaf (.quota 1))
 (.branch 390
 (.branch 377
 (.branch 370
 (.leaf (.quota 1))
 (.branch 373
 (.branch 371
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.branch 375
 (.branch 374
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 383
 (.leaf (.quota 1))
 (.branch 386
 (.branch 384
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1))))))
 (.branch 626
 (.branch 521
 (.branch 469
 (.branch 443
 (.branch 430
 (.leaf (.quota 1))
 (.branch 436
 (.branch 433
 (.branch 431
 (.leaf (.quota 1))
 (.branch 432
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 434
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 495
 (.branch 482
 (.branch 475
 (.leaf (.quota 1))
 (.branch 478
 (.leaf (.quota 1))
 (.branch 480
 (.branch 479
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))
 (.branch 488
 (.branch 485
 (.branch 483
 (.leaf (.quota 1))
 (.branch 484
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.branch 491
 (.branch 489
 (.leaf (.reuse 20))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 508
 (.branch 501
 (.branch 498
 (.leaf (.quota 1))
 (.branch 499
 (.leaf (.quota 1))
 (.branch 500
 (.leaf (.reuse 21))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 573
 (.branch 547
 (.branch 534
 (.branch 527
 (.branch 524
 (.leaf (.quota 1))
 (.branch 525
 (.leaf (.quota 2))
 (.branch 526
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.branch 540
 (.branch 537
 (.leaf (.quota 1))
 (.branch 538
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 543
 (.branch 541
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.branch 560
 (.branch 553
 (.branch 550
 (.leaf (.quota 1))
 (.branch 551
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 556
 (.branch 554
 (.leaf (.quota 1))
 (.branch 555
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1))))
 (.branch 566
 (.branch 563
 (.branch 561
 (.leaf (.quota 1))
 (.branch 562
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1))))
 (.branch 730
 (.branch 678
 (.branch 652
 (.branch 639
 (.leaf (.quota 1))
 (.branch 645
 (.branch 642
 (.leaf (.quota 1))
 (.branch 643
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 648
 (.branch 646
 (.leaf (.quota 1))
 (.branch 647
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 650
 (.branch 649
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1))))))
 (.branch 665
 (.branch 658
 (.branch 655
 (.leaf (.quota 1))
 (.branch 656
 (.leaf (.quota 1))
 (.branch 657
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 661
 (.branch 659
 (.leaf (.quota 1))
 (.branch 660
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 663
 (.leaf (.quota 1))
 (.branch 664
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
 (.branch 671
 (.branch 668
 (.branch 666
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1)))
 (.branch 782
 (.branch 756
 (.branch 743
 (.leaf (.quota 1))
 (.branch 749
 (.branch 746
 (.branch 744
 (.leaf (.quota 1))
 (.branch 745
 (.leaf (.reuse 38))
 (.leaf (.quota 1))))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.branch 769
 (.branch 762
 (.leaf (.quota 1))
 (.branch 765
 (.leaf (.quota 1))
 (.branch 767
 (.branch 766
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 1)))))
 (.branch 775
 (.leaf (.quota 1))
 (.branch 778
 (.branch 776
 (.leaf (.quota 1))
 (.branch 777
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))))
 (.branch 808
 (.branch 795
 (.branch 788
 (.branch 785
 (.leaf (.quota 1))
 (.branch 786
 (.leaf (.quota 1))
 (.branch 787
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 791
 (.branch 789
 (.leaf (.quota 1))
 (.branch 790
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 1))))
 (.branch 801
 (.branch 798
 (.branch 796
 (.leaf (.quota 1))
 (.branch 797
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 799
 (.leaf (.quota 2))
 (.branch 800
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.leaf (.quota 1))))
 (.branch 821
 (.branch 814
 (.leaf (.quota 1))
 (.branch 817
 (.branch 815
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 1))))
 (.leaf (.quota 1))))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0857.quota RootedCaches.RootedSixExtra05.rawCells
    RootedForests.RootedSubsumedForest0857.rawLeaves 52 (RootedForests.RootedSubsumedForest0870.rawLeaves i) (routes.get i)

def disposition (j : Fin 835) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0857.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0857

/- Original module: RootedQuotaTransfer0857Proof000. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0857
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0857

/- Original module: RootedQuotaTransfer0857Proof001. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0857
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0857

/- Original module: RootedQuotaTransfer0857Proof002. -/
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0857
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

end Papers.RationalityTen.RootedQuotaTransfers.Case0857
