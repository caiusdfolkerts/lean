module
prelude
public meta import CertificateNumbers
public import PackedRawNatGrowth

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
open Papers.RationalityTen ConcreteGrowth

def nodeBlocks009 : Table PackedRawNatGrowth.Block :=
(.branch 452
 (.branch 451
 (.leaf ⟨(certNat% 0),(certNat% 1)⟩)
 (.leaf ⟨(certNat% 2),(certNat% 3)⟩))
 (.branch 453
 (.leaf ⟨(certNat% 4),(certNat% 5)⟩)
 (.branch 454
 (.leaf ⟨(certNat% 6),(certNat% 7)⟩)
 (.leaf ⟨(certNat% 8),(certNat% 9)⟩))))
def nodeCounters009 : Table Nat :=
(.branch 452
 (.branch 451
 (.leaf (certNat% 10))
 (.leaf (certNat% 11)))
 (.branch 453
 (.leaf (certNat% 12))
 (.branch 454
 (.leaf (certNat% 13))
 (.leaf (certNat% 14)))))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
