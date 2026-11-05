module
prelude
public import RootedQuotaTransfer0712Proof000

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0712
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer


theorem routeTest_complete : Interval routeTest 0 10 :=
  routeInterval0

theorem disposition_checked (j : Fin 10) :
    RawLeafCertificate.check RootedForests.RootedSubsumedForest0712.quota
      ((RootedForests.RootedSubsumedForest0718.rawLeaves j.val).map RootedCaches.RootedSixBase03.rawCells) (disposition j) = true := by
  exact routeCheck_sound RootedForests.RootedSubsumedForest0712.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0712.rawLeaves 8 RootedForests.RootedSubsumedForest0712.dispositionTable.get
    (fun i hi => RootedForests.RootedSubsumedForest0712.disposition_checked ⟨i, hi⟩)
    (RootedForests.RootedSubsumedForest0718.rawLeaves j.val) (routes.get j.val)
    (routeTest_complete j.val (Nat.zero_le _) j.isLt)

#print axioms disposition_checked

end Papers.RationalityTen.RootedQuotaTransfers.Case0712
