module
prelude
public meta import CertificateNumbers
public import PackedRawNatGrowth

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0300
open Papers.RationalityTen ConcreteGrowth

def nodeBlocks001 : Table PackedRawNatGrowth.Block :=
(.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(certNat% 0),(certNat% 1)⟩)
 (.branch 52
 (.leaf ⟨(certNat% 2),(certNat% 3)⟩)
 (.leaf ⟨(certNat% 4),(certNat% 5)⟩)))
 (.branch 54
 (.leaf ⟨(certNat% 6),(certNat% 7)⟩)
 (.branch 55
 (.leaf ⟨(certNat% 8),(certNat% 9)⟩)
 (.leaf ⟨(certNat% 10),(certNat% 11)⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(certNat% 12),(certNat% 13)⟩)
 (.branch 58
 (.leaf ⟨(certNat% 14),(certNat% 15)⟩)
 (.leaf ⟨(certNat% 16),(certNat% 17)⟩)))
 (.branch 60
 (.leaf ⟨(certNat% 18),(certNat% 19)⟩)
 (.branch 61
 (.leaf ⟨(certNat% 20),(certNat% 21)⟩)
 (.leaf ⟨(certNat% 22),(certNat% 23)⟩)))))
def nodeCounters001 : Table Nat :=
(.branch 56
 (.branch 53
 (.branch 51
 (.leaf (certNat% 24))
 (.branch 52
 (.leaf (certNat% 25))
 (.leaf (certNat% 26))))
 (.branch 54
 (.leaf (certNat% 27))
 (.branch 55
 (.leaf (certNat% 28))
 (.leaf (certNat% 29)))))
 (.branch 59
 (.branch 57
 (.leaf (certNat% 30))
 (.branch 58
 (.leaf (certNat% 31))
 (.leaf (certNat% 32))))
 (.branch 60
 (.leaf (certNat% 33))
 (.branch 61
 (.leaf (certNat% 34))
 (.leaf (certNat% 35))))))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0300
