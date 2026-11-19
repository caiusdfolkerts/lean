module
prelude
public meta import CertificateNumbers
public import PackedRawNatGrowth

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0311
open Papers.RationalityTen ConcreteGrowth

def nodeBlocks002 : Table PackedRawNatGrowth.Block :=
(.branch 102
 (.branch 101
 (.leaf ⟨(certNat% 0),(certNat% 1)⟩)
 (.leaf ⟨(certNat% 2),(certNat% 3)⟩))
 (.branch 103
 (.leaf ⟨(certNat% 4),(certNat% 5)⟩)
 (.leaf ⟨(certNat% 6),(certNat% 7)⟩)))
def nodeCounters002 : Table Nat :=
(.branch 102
 (.branch 101
 (.leaf (certNat% 8))
 (.leaf (certNat% 9)))
 (.branch 103
 (.leaf (certNat% 10))
 (.leaf (certNat% 11))))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0311
