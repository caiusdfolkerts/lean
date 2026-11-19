module
prelude
public meta import CertificateNumbers
public import PackedRawNatGrowth

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0722
open Papers.RationalityTen ConcreteGrowth

def nodeBlocks007 : Table PackedRawNatGrowth.Block :=
(.branch 353
 (.branch 351
 (.leaf ⟨(certNat% 0),(certNat% 1)⟩)
 (.branch 352
 (.leaf ⟨(certNat% 2),(certNat% 3)⟩)
 (.leaf ⟨(certNat% 4),(certNat% 5)⟩)))
 (.branch 355
 (.branch 354
 (.leaf ⟨(certNat% 6),(certNat% 7)⟩)
 (.leaf ⟨(certNat% 8),(certNat% 9)⟩))
 (.branch 356
 (.leaf ⟨(certNat% 10),(certNat% 11)⟩)
 (.leaf ⟨(certNat% 12),0x0⟩))))
def nodeCounters007 : Table Nat :=
(.branch 353
 (.branch 351
 (.leaf (certNat% 13))
 (.branch 352
 (.leaf (certNat% 14))
 (.leaf (certNat% 15))))
 (.branch 355
 (.branch 354
 (.leaf (certNat% 16))
 (.leaf (certNat% 17)))
 (.branch 356
 (.leaf (certNat% 18))
 (.leaf 0x1))))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0722
