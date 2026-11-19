module
prelude
public meta import CertificateNumbers
public import PackedRawNatGrowth

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0352
open Papers.RationalityTen ConcreteGrowth

def nodeBlocks002 : Table PackedRawNatGrowth.Block :=
(.branch 111
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
 (.branch 108
 (.branch 106
 (.leaf ⟨(certNat% 10),(certNat% 11)⟩)
 (.branch 107
 (.leaf ⟨(certNat% 12),(certNat% 13)⟩)
 (.leaf ⟨(certNat% 14),(certNat% 15)⟩)))
 (.branch 109
 (.leaf ⟨(certNat% 16),(certNat% 17)⟩)
 (.branch 110
 (.leaf ⟨(certNat% 18),(certNat% 19)⟩)
 (.leaf ⟨(certNat% 20),(certNat% 21)⟩)))))
 (.branch 117
 (.branch 114
 (.branch 112
 (.leaf ⟨(certNat% 22),(certNat% 23)⟩)
 (.branch 113
 (.leaf ⟨(certNat% 24),(certNat% 25)⟩)
 (.leaf ⟨(certNat% 26),(certNat% 27)⟩)))
 (.branch 115
 (.leaf ⟨(certNat% 28),(certNat% 29)⟩)
 (.branch 116
 (.leaf ⟨(certNat% 30),(certNat% 31)⟩)
 (.leaf ⟨(certNat% 32),(certNat% 33)⟩))))
 (.branch 120
 (.branch 118
 (.leaf ⟨(certNat% 34),(certNat% 35)⟩)
 (.branch 119
 (.leaf ⟨(certNat% 36),(certNat% 37)⟩)
 (.leaf ⟨(certNat% 38),(certNat% 39)⟩)))
 (.branch 121
 (.leaf ⟨(certNat% 40),(certNat% 41)⟩)
 (.branch 122
 (.leaf ⟨(certNat% 42),(certNat% 43)⟩)
 (.leaf ⟨(certNat% 44),(certNat% 45)⟩))))))
def nodeCounters002 : Table Nat :=
(.branch 111
 (.branch 105
 (.branch 102
 (.branch 101
 (.leaf (certNat% 46))
 (.leaf (certNat% 47)))
 (.branch 103
 (.leaf (certNat% 48))
 (.branch 104
 (.leaf (certNat% 49))
 (.leaf (certNat% 50)))))
 (.branch 108
 (.branch 106
 (.leaf (certNat% 51))
 (.branch 107
 (.leaf (certNat% 52))
 (.leaf (certNat% 53))))
 (.branch 109
 (.leaf (certNat% 54))
 (.branch 110
 (.leaf (certNat% 55))
 (.leaf (certNat% 56))))))
 (.branch 117
 (.branch 114
 (.branch 112
 (.leaf (certNat% 57))
 (.branch 113
 (.leaf (certNat% 58))
 (.leaf (certNat% 59))))
 (.branch 115
 (.leaf (certNat% 60))
 (.branch 116
 (.leaf (certNat% 61))
 (.leaf (certNat% 62)))))
 (.branch 120
 (.branch 118
 (.leaf (certNat% 63))
 (.branch 119
 (.leaf (certNat% 64))
 (.leaf (certNat% 65))))
 (.branch 121
 (.leaf (certNat% 66))
 (.branch 122
 (.leaf (certNat% 67))
 (.leaf (certNat% 68)))))))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0352
