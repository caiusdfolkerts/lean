module
prelude
public meta import CertificateNumbers
public import PackedRawNatGrowth

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
open Papers.RationalityTen ConcreteGrowth

def nodeBlocks003 : Table PackedRawNatGrowth.Block :=
(.branch 151
 (.leaf ⟨(certNat% 0),(certNat% 1)⟩)
 (.leaf ⟨(certNat% 2),(certNat% 3)⟩))
def nodeCounters003 : Table Nat :=
(.branch 151
 (.leaf (certNat% 4))
 (.leaf (certNat% 5)))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
