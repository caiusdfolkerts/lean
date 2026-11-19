module
prelude
public meta import CertificateNumbers
public import PackedRawNatGrowth

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest17
open Papers.RationalityTen ConcreteGrowth

def nodeBlocks002 : Table PackedRawNatGrowth.Block :=
(.branch 113
 (.branch 106
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
 (.branch 109
 (.branch 107
 (.leaf ⟨(certNat% 12),(certNat% 13)⟩)
 (.branch 108
 (.leaf ⟨(certNat% 14),(certNat% 15)⟩)
 (.leaf ⟨(certNat% 16),(certNat% 17)⟩)))
 (.branch 111
 (.branch 110
 (.leaf ⟨(certNat% 18),(certNat% 19)⟩)
 (.leaf ⟨(certNat% 20),(certNat% 21)⟩))
 (.branch 112
 (.leaf ⟨(certNat% 22),(certNat% 23)⟩)
 (.leaf ⟨(certNat% 24),(certNat% 25)⟩)))))
 (.branch 119
 (.branch 116
 (.branch 114
 (.leaf ⟨(certNat% 26),(certNat% 27)⟩)
 (.branch 115
 (.leaf ⟨(certNat% 28),(certNat% 29)⟩)
 (.leaf ⟨(certNat% 30),(certNat% 31)⟩)))
 (.branch 117
 (.leaf ⟨(certNat% 32),(certNat% 33)⟩)
 (.branch 118
 (.leaf ⟨(certNat% 34),(certNat% 35)⟩)
 (.leaf ⟨(certNat% 36),(certNat% 37)⟩))))
 (.branch 122
 (.branch 120
 (.leaf ⟨(certNat% 38),(certNat% 39)⟩)
 (.branch 121
 (.leaf ⟨(certNat% 40),(certNat% 41)⟩)
 (.leaf ⟨(certNat% 42),(certNat% 43)⟩)))
 (.branch 124
 (.branch 123
 (.leaf ⟨(certNat% 44),(certNat% 45)⟩)
 (.leaf ⟨(certNat% 46),(certNat% 47)⟩))
 (.branch 125
 (.leaf ⟨(certNat% 48),(certNat% 49)⟩)
 (.leaf ⟨(certNat% 50),(certNat% 51)⟩))))))
def nodeCounters002 : Table Nat :=
(.branch 113
 (.branch 106
 (.branch 103
 (.branch 101
 (.leaf (certNat% 52))
 (.branch 102
 (.leaf (certNat% 53))
 (.leaf (certNat% 54))))
 (.branch 104
 (.leaf (certNat% 55))
 (.branch 105
 (.leaf (certNat% 56))
 (.leaf (certNat% 57)))))
 (.branch 109
 (.branch 107
 (.leaf (certNat% 58))
 (.branch 108
 (.leaf (certNat% 59))
 (.leaf (certNat% 60))))
 (.branch 111
 (.branch 110
 (.leaf (certNat% 61))
 (.leaf (certNat% 62)))
 (.branch 112
 (.leaf (certNat% 63))
 (.leaf (certNat% 64))))))
 (.branch 119
 (.branch 116
 (.branch 114
 (.leaf (certNat% 65))
 (.branch 115
 (.leaf (certNat% 66))
 (.leaf (certNat% 67))))
 (.branch 117
 (.leaf (certNat% 68))
 (.branch 118
 (.leaf (certNat% 69))
 (.leaf (certNat% 70)))))
 (.branch 122
 (.branch 120
 (.leaf (certNat% 71))
 (.branch 121
 (.leaf (certNat% 72))
 (.leaf (certNat% 73))))
 (.branch 124
 (.branch 123
 (.leaf (certNat% 74))
 (.leaf (certNat% 75)))
 (.branch 125
 (.leaf (certNat% 76))
 (.leaf (certNat% 77)))))))

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest17
