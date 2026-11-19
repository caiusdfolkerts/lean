module
prelude
public meta import CertificateNumbers
public import PackedRawNatGrowth

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0741
open Papers.RationalityTen ConcreteGrowth

def nodeBlocks002 : Table PackedRawNatGrowth.Block :=
(.branch 103
 (.branch 101
 (.leaf ⟨(certNat% 0),(certNat% 1)⟩)
 (.branch 102
 (.leaf ⟨(certNat% 2),(certNat% 3)⟩)
 (.leaf ⟨(certNat% 4),(certNat% 5)⟩)))
 (.branch 104
 (.leaf ⟨(certNat% 6),(certNat% 7)⟩)
 (.branch 105
 (.leaf ⟨(certNat% 8),(certNat% 9)⟩)
 (.leaf ⟨(certNat% 10),(certNat% 11)⟩))))
def nodeCounters002 : Table Nat :=
(.branch 103
 (.branch 101
 (.leaf (certNat% 12))
 (.branch 102
 (.leaf (certNat% 13))
 (.leaf (certNat% 14))))
 (.branch 104
 (.leaf (certNat% 15))
 (.branch 105
 (.leaf (certNat% 16))
 (.leaf (certNat% 17)))))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0741
