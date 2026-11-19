module
prelude
public meta import CertificateNumbers
public import PackedRawNatGrowth

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0333
open Papers.RationalityTen ConcreteGrowth

def nodeBlocks002 : Table PackedRawNatGrowth.Block :=
(.branch 109
 (.branch 104
 (.branch 102
 (.branch 101
 (.leaf ⟨(certNat% 0),(certNat% 1)⟩)
 (.leaf ⟨(certNat% 2),(certNat% 3)⟩))
 (.branch 103
 (.leaf ⟨(certNat% 4),(certNat% 5)⟩)
 (.leaf ⟨(certNat% 6),(certNat% 7)⟩)))
 (.branch 106
 (.branch 105
 (.leaf ⟨(certNat% 8),(certNat% 9)⟩)
 (.leaf ⟨(certNat% 10),(certNat% 11)⟩))
 (.branch 107
 (.leaf ⟨(certNat% 12),(certNat% 13)⟩)
 (.branch 108
 (.leaf ⟨(certNat% 14),(certNat% 15)⟩)
 (.leaf ⟨(certNat% 16),(certNat% 17)⟩)))))
 (.branch 113
 (.branch 111
 (.branch 110
 (.leaf ⟨(certNat% 18),(certNat% 19)⟩)
 (.leaf ⟨(certNat% 20),(certNat% 21)⟩))
 (.branch 112
 (.leaf ⟨(certNat% 22),(certNat% 23)⟩)
 (.leaf ⟨(certNat% 24),(certNat% 25)⟩)))
 (.branch 115
 (.branch 114
 (.leaf ⟨(certNat% 26),(certNat% 27)⟩)
 (.leaf ⟨(certNat% 28),(certNat% 29)⟩))
 (.branch 116
 (.leaf ⟨(certNat% 30),(certNat% 31)⟩)
 (.branch 117
 (.leaf ⟨(certNat% 32),(certNat% 33)⟩)
 (.leaf ⟨(certNat% 34),(certNat% 35)⟩))))))
def nodeCounters002 : Table Nat :=
(.branch 109
 (.branch 104
 (.branch 102
 (.branch 101
 (.leaf (certNat% 36))
 (.leaf (certNat% 37)))
 (.branch 103
 (.leaf (certNat% 38))
 (.leaf (certNat% 39))))
 (.branch 106
 (.branch 105
 (.leaf (certNat% 40))
 (.leaf (certNat% 41)))
 (.branch 107
 (.leaf (certNat% 42))
 (.branch 108
 (.leaf (certNat% 43))
 (.leaf (certNat% 44))))))
 (.branch 113
 (.branch 111
 (.branch 110
 (.leaf (certNat% 45))
 (.leaf (certNat% 46)))
 (.branch 112
 (.leaf (certNat% 47))
 (.leaf (certNat% 48))))
 (.branch 115
 (.branch 114
 (.leaf (certNat% 49))
 (.leaf (certNat% 50)))
 (.branch 116
 (.leaf (certNat% 51))
 (.branch 117
 (.leaf (certNat% 52))
 (.leaf (certNat% 53)))))))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0333
