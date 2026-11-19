module
prelude
public meta import CertificateNumbers
public import PackedRawNatGrowth

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0339
open Papers.RationalityTen ConcreteGrowth

def nodeBlocks002 : Table PackedRawNatGrowth.Block :=
(.branch 107
 (.branch 103
 (.branch 101
 (.leaf ⟨(certNat% 0),(certNat% 1)⟩)
 (.branch 102
 (.leaf ⟨(certNat% 2),(certNat% 3)⟩)
 (.leaf ⟨(certNat% 4),(certNat% 5)⟩)))
 (.branch 105
 (.branch 104
 (.leaf ⟨(certNat% 6),(certNat% 7)⟩)
 (.leaf ⟨(certNat% 8),(certNat% 9)⟩))
 (.branch 106
 (.leaf ⟨(certNat% 10),(certNat% 11)⟩)
 (.leaf ⟨(certNat% 12),(certNat% 13)⟩))))
 (.branch 111
 (.branch 109
 (.branch 108
 (.leaf ⟨(certNat% 14),(certNat% 15)⟩)
 (.leaf ⟨(certNat% 16),(certNat% 17)⟩))
 (.branch 110
 (.leaf ⟨(certNat% 18),(certNat% 19)⟩)
 (.leaf ⟨(certNat% 20),(certNat% 21)⟩)))
 (.branch 113
 (.branch 112
 (.leaf ⟨(certNat% 22),(certNat% 23)⟩)
 (.leaf ⟨(certNat% 24),(certNat% 25)⟩))
 (.branch 114
 (.leaf ⟨(certNat% 26),(certNat% 27)⟩)
 (.leaf ⟨(certNat% 28),(certNat% 29)⟩)))))
def nodeCounters002 : Table Nat :=
(.branch 107
 (.branch 103
 (.branch 101
 (.leaf (certNat% 30))
 (.branch 102
 (.leaf (certNat% 31))
 (.leaf (certNat% 32))))
 (.branch 105
 (.branch 104
 (.leaf (certNat% 33))
 (.leaf (certNat% 34)))
 (.branch 106
 (.leaf (certNat% 35))
 (.leaf (certNat% 36)))))
 (.branch 111
 (.branch 109
 (.branch 108
 (.leaf (certNat% 37))
 (.leaf (certNat% 38)))
 (.branch 110
 (.leaf (certNat% 39))
 (.leaf (certNat% 40))))
 (.branch 113
 (.branch 112
 (.leaf (certNat% 41))
 (.leaf (certNat% 42)))
 (.branch 114
 (.leaf (certNat% 43))
 (.leaf (certNat% 44))))))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0339
