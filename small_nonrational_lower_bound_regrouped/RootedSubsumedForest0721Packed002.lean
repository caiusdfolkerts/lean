module
prelude
public meta import CertificateNumbers
public import PackedRawNatGrowth

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0721
open Papers.RationalityTen ConcreteGrowth

def nodeBlocks002 : Table PackedRawNatGrowth.Block :=
(.branch 110
 (.branch 105
 (.branch 102
 (.branch 101
 (.leaf ⟨(certNat% 0),(certNat% 1)⟩)
 (.leaf ⟨(certNat% 2),(certNat% 3)⟩))
 (.branch 103
 (.leaf ⟨(certNat% 4),(certNat% 5)⟩)
 (.branch 104
 (.leaf ⟨(certNat% 6),(certNat% 7)⟩)
 (.leaf ⟨(certNat% 8),(certNat% 9)⟩))))
 (.branch 107
 (.branch 106
 (.leaf ⟨(certNat% 10),(certNat% 11)⟩)
 (.leaf ⟨(certNat% 12),(certNat% 13)⟩))
 (.branch 108
 (.leaf ⟨(certNat% 14),(certNat% 15)⟩)
 (.branch 109
 (.leaf ⟨(certNat% 16),(certNat% 17)⟩)
 (.leaf ⟨(certNat% 18),(certNat% 19)⟩)))))
 (.branch 115
 (.branch 112
 (.branch 111
 (.leaf ⟨(certNat% 20),(certNat% 21)⟩)
 (.leaf ⟨(certNat% 22),(certNat% 23)⟩))
 (.branch 113
 (.leaf ⟨(certNat% 24),(certNat% 25)⟩)
 (.branch 114
 (.leaf ⟨(certNat% 26),(certNat% 27)⟩)
 (.leaf ⟨(certNat% 28),(certNat% 29)⟩))))
 (.branch 118
 (.branch 116
 (.leaf ⟨(certNat% 30),(certNat% 31)⟩)
 (.branch 117
 (.leaf ⟨(certNat% 32),(certNat% 33)⟩)
 (.leaf ⟨(certNat% 34),(certNat% 35)⟩)))
 (.branch 119
 (.leaf ⟨(certNat% 36),(certNat% 37)⟩)
 (.branch 120
 (.leaf ⟨(certNat% 38),(certNat% 39)⟩)
 (.leaf ⟨(certNat% 40),(certNat% 41)⟩))))))
def nodeCounters002 : Table Nat :=
(.branch 110
 (.branch 105
 (.branch 102
 (.branch 101
 (.leaf (certNat% 42))
 (.leaf (certNat% 43)))
 (.branch 103
 (.leaf (certNat% 44))
 (.branch 104
 (.leaf (certNat% 45))
 (.leaf (certNat% 46)))))
 (.branch 107
 (.branch 106
 (.leaf (certNat% 47))
 (.leaf (certNat% 48)))
 (.branch 108
 (.leaf (certNat% 49))
 (.branch 109
 (.leaf (certNat% 50))
 (.leaf (certNat% 51))))))
 (.branch 115
 (.branch 112
 (.branch 111
 (.leaf (certNat% 52))
 (.leaf (certNat% 53)))
 (.branch 113
 (.leaf (certNat% 54))
 (.branch 114
 (.leaf (certNat% 55))
 (.leaf (certNat% 56)))))
 (.branch 118
 (.branch 116
 (.leaf (certNat% 57))
 (.branch 117
 (.leaf (certNat% 58))
 (.leaf (certNat% 59))))
 (.branch 119
 (.leaf (certNat% 60))
 (.branch 120
 (.leaf (certNat% 61))
 (.leaf (certNat% 62)))))))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0721
