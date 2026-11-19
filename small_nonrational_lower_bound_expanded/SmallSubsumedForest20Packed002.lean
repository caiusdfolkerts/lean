module
prelude
public meta import CertificateNumbers
public import PackedRawNatGrowth

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest20
open Papers.RationalityTen ConcreteGrowth

def nodeBlocks002 : Table PackedRawNatGrowth.Block :=
(.branch 119
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
 (.branch 114
 (.branch 111
 (.branch 110
 (.leaf ⟨(certNat% 18),(certNat% 19)⟩)
 (.leaf ⟨(certNat% 20),(certNat% 21)⟩))
 (.branch 112
 (.leaf ⟨(certNat% 22),(certNat% 23)⟩)
 (.branch 113
 (.leaf ⟨(certNat% 24),(certNat% 25)⟩)
 (.leaf ⟨(certNat% 26),(certNat% 27)⟩))))
 (.branch 116
 (.branch 115
 (.leaf ⟨(certNat% 28),(certNat% 29)⟩)
 (.leaf ⟨(certNat% 30),(certNat% 31)⟩))
 (.branch 117
 (.leaf ⟨(certNat% 32),(certNat% 33)⟩)
 (.branch 118
 (.leaf ⟨(certNat% 34),(certNat% 35)⟩)
 (.leaf ⟨(certNat% 36),(certNat% 37)⟩))))))
 (.branch 129
 (.branch 124
 (.branch 121
 (.branch 120
 (.leaf ⟨(certNat% 38),(certNat% 39)⟩)
 (.leaf ⟨(certNat% 40),(certNat% 41)⟩))
 (.branch 122
 (.leaf ⟨(certNat% 42),(certNat% 43)⟩)
 (.branch 123
 (.leaf ⟨(certNat% 44),(certNat% 45)⟩)
 (.leaf ⟨(certNat% 46),(certNat% 47)⟩))))
 (.branch 126
 (.branch 125
 (.leaf ⟨(certNat% 48),(certNat% 49)⟩)
 (.leaf ⟨(certNat% 50),(certNat% 51)⟩))
 (.branch 127
 (.leaf ⟨(certNat% 52),(certNat% 53)⟩)
 (.branch 128
 (.leaf ⟨(certNat% 54),(certNat% 55)⟩)
 (.leaf ⟨(certNat% 56),(certNat% 57)⟩)))))
 (.branch 134
 (.branch 131
 (.branch 130
 (.leaf ⟨(certNat% 58),(certNat% 59)⟩)
 (.leaf ⟨(certNat% 60),(certNat% 61)⟩))
 (.branch 132
 (.leaf ⟨(certNat% 62),(certNat% 63)⟩)
 (.branch 133
 (.leaf ⟨(certNat% 64),(certNat% 65)⟩)
 (.leaf ⟨(certNat% 66),(certNat% 67)⟩))))
 (.branch 136
 (.branch 135
 (.leaf ⟨(certNat% 68),(certNat% 69)⟩)
 (.leaf ⟨(certNat% 70),(certNat% 71)⟩))
 (.branch 137
 (.leaf ⟨(certNat% 72),(certNat% 73)⟩)
 (.branch 138
 (.leaf ⟨(certNat% 74),(certNat% 75)⟩)
 (.leaf ⟨(certNat% 76),(certNat% 77)⟩)))))))
def nodeCounters002 : Table Nat :=
(.branch 119
 (.branch 109
 (.branch 104
 (.branch 102
 (.branch 101
 (.leaf (certNat% 78))
 (.leaf (certNat% 79)))
 (.branch 103
 (.leaf (certNat% 80))
 (.leaf (certNat% 81))))
 (.branch 106
 (.branch 105
 (.leaf (certNat% 82))
 (.leaf (certNat% 83)))
 (.branch 107
 (.leaf (certNat% 84))
 (.branch 108
 (.leaf (certNat% 85))
 (.leaf (certNat% 86))))))
 (.branch 114
 (.branch 111
 (.branch 110
 (.leaf (certNat% 87))
 (.leaf (certNat% 88)))
 (.branch 112
 (.leaf (certNat% 89))
 (.branch 113
 (.leaf (certNat% 90))
 (.leaf (certNat% 91)))))
 (.branch 116
 (.branch 115
 (.leaf (certNat% 92))
 (.leaf (certNat% 93)))
 (.branch 117
 (.leaf (certNat% 94))
 (.branch 118
 (.leaf (certNat% 95))
 (.leaf (certNat% 96)))))))
 (.branch 129
 (.branch 124
 (.branch 121
 (.branch 120
 (.leaf (certNat% 97))
 (.leaf (certNat% 98)))
 (.branch 122
 (.leaf (certNat% 99))
 (.branch 123
 (.leaf (certNat% 100))
 (.leaf (certNat% 101)))))
 (.branch 126
 (.branch 125
 (.leaf (certNat% 102))
 (.leaf (certNat% 103)))
 (.branch 127
 (.leaf (certNat% 104))
 (.branch 128
 (.leaf (certNat% 105))
 (.leaf (certNat% 106))))))
 (.branch 134
 (.branch 131
 (.branch 130
 (.leaf (certNat% 107))
 (.leaf (certNat% 108)))
 (.branch 132
 (.leaf (certNat% 109))
 (.branch 133
 (.leaf (certNat% 110))
 (.leaf (certNat% 111)))))
 (.branch 136
 (.branch 135
 (.leaf (certNat% 112))
 (.leaf (certNat% 113)))
 (.branch 137
 (.leaf (certNat% 114))
 (.branch 138
 (.leaf (certNat% 115))
 (.leaf (certNat% 116))))))))

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest20
