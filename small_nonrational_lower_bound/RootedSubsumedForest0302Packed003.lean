module
prelude
public meta import CertificateNumbers
public import PackedRawNatGrowth

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
open Papers.RationalityTen ConcreteGrowth

def nodeBlocks003 : Table PackedRawNatGrowth.Block :=
(.branch 152
 (.branch 151
 (.leaf ⟨(certNat% 0),(certNat% 1)⟩)
 (.leaf ⟨(certNat% 2),(certNat% 3)⟩))
 (.branch 153
 (.leaf ⟨(certNat% 4),(certNat% 5)⟩)
 (.branch 154
 (.leaf ⟨(certNat% 6),(certNat% 7)⟩)
 (.leaf ⟨(certNat% 8),(certNat% 9)⟩))))
def nodeCounters003 : Table Nat :=
(.branch 152
 (.branch 151
 (.leaf (certNat% 10))
 (.leaf (certNat% 11)))
 (.branch 153
 (.leaf (certNat% 12))
 (.branch 154
 (.leaf (certNat% 13))
 (.leaf (certNat% 14)))))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
