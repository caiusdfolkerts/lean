module
prelude
public import QuotaLeafTransfer
public import FiniteChecks
public import RootedSubsumedForest0712Dispositions
public import RootedSubsumedForest0718Data

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedQuotaTransfers.Case0712
open Papers.RationalityTen ConcreteGrowth FiniteChecks QuotaLeafTransfer

/-! Case 712: use the complete forest for case 718, but retain
the exact original quota and recheck the disposition of every larger leaf. -/

theorem quota_le (k : Nat) : RootedForests.RootedSubsumedForest0712.quota k ≤ RootedForests.RootedSubsumedForest0718.quota k := by
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
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf (.reuse 0))
 (.leaf (.reuse 1)))
 (.branch 3
 (.leaf (.quota 2))
 (.branch 4
 (.leaf (.reuse 2))
 (.leaf (.reuse 3)))))
 (.branch 7
 (.branch 6
 (.leaf (.reuse 4))
 (.leaf (.quota 2)))
 (.branch 8
 (.leaf (.reuse 5))
 (.branch 9
 (.leaf (.reuse 6))
 (.leaf (.quota 1))))))

def routeTest (i : Nat) : Bool :=
  routeCheck RootedForests.RootedSubsumedForest0712.quota RootedCaches.RootedSixBase03.rawCells
    RootedForests.RootedSubsumedForest0712.rawLeaves 8 (RootedForests.RootedSubsumedForest0718.rawLeaves i) (routes.get i)

def disposition (j : Fin 10) : RawLeafCertificate.Certificate :=
  certificate RootedForests.RootedSubsumedForest0712.dispositionTable.get (routes.get j.val)

end Papers.RationalityTen.RootedQuotaTransfers.Case0712
