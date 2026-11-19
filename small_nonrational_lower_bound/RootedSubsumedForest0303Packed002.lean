module
prelude
public meta import CertificateNumbers
public import PackedRawNatGrowth

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0303
open Papers.RationalityTen ConcreteGrowth

def nodeBlocks002 : Table PackedRawNatGrowth.Block :=
(.branch 122
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
 (.branch 116
 (.branch 113
 (.branch 112
 (.leaf ⟨(certNat% 22),(certNat% 23)⟩)
 (.leaf ⟨(certNat% 24),(certNat% 25)⟩))
 (.branch 114
 (.leaf ⟨(certNat% 26),(certNat% 27)⟩)
 (.branch 115
 (.leaf ⟨(certNat% 28),(certNat% 29)⟩)
 (.leaf ⟨(certNat% 30),(certNat% 31)⟩))))
 (.branch 119
 (.branch 117
 (.leaf ⟨(certNat% 32),(certNat% 33)⟩)
 (.branch 118
 (.leaf ⟨(certNat% 34),(certNat% 35)⟩)
 (.leaf ⟨(certNat% 36),(certNat% 37)⟩)))
 (.branch 120
 (.leaf ⟨(certNat% 38),(certNat% 39)⟩)
 (.branch 121
 (.leaf ⟨(certNat% 40),(certNat% 41)⟩)
 (.leaf ⟨(certNat% 42),(certNat% 43)⟩))))))
 (.branch 133
 (.branch 127
 (.branch 124
 (.branch 123
 (.leaf ⟨(certNat% 44),(certNat% 45)⟩)
 (.leaf ⟨(certNat% 46),(certNat% 47)⟩))
 (.branch 125
 (.leaf ⟨(certNat% 48),(certNat% 49)⟩)
 (.branch 126
 (.leaf ⟨(certNat% 50),(certNat% 51)⟩)
 (.leaf ⟨(certNat% 52),(certNat% 53)⟩))))
 (.branch 130
 (.branch 128
 (.leaf ⟨(certNat% 54),(certNat% 55)⟩)
 (.branch 129
 (.leaf ⟨(certNat% 56),(certNat% 57)⟩)
 (.leaf ⟨(certNat% 58),(certNat% 59)⟩)))
 (.branch 131
 (.leaf ⟨(certNat% 60),(certNat% 61)⟩)
 (.branch 132
 (.leaf ⟨(certNat% 62),(certNat% 63)⟩)
 (.leaf ⟨(certNat% 64),(certNat% 65)⟩)))))
 (.branch 138
 (.branch 135
 (.branch 134
 (.leaf ⟨(certNat% 66),(certNat% 67)⟩)
 (.leaf ⟨(certNat% 68),(certNat% 69)⟩))
 (.branch 136
 (.leaf ⟨(certNat% 70),(certNat% 71)⟩)
 (.branch 137
 (.leaf ⟨(certNat% 72),(certNat% 73)⟩)
 (.leaf ⟨(certNat% 74),(certNat% 75)⟩))))
 (.branch 141
 (.branch 139
 (.leaf ⟨(certNat% 76),(certNat% 77)⟩)
 (.branch 140
 (.leaf ⟨(certNat% 78),(certNat% 79)⟩)
 (.leaf ⟨(certNat% 80),(certNat% 81)⟩)))
 (.branch 142
 (.leaf ⟨(certNat% 82),(certNat% 83)⟩)
 (.branch 143
 (.leaf ⟨(certNat% 84),(certNat% 85)⟩)
 (.leaf ⟨(certNat% 86),(certNat% 87)⟩)))))))
def nodeCounters002 : Table Nat :=
(.branch 122
 (.branch 111
 (.branch 105
 (.branch 102
 (.branch 101
 (.leaf (certNat% 88))
 (.leaf (certNat% 89)))
 (.branch 103
 (.leaf (certNat% 90))
 (.branch 104
 (.leaf (certNat% 91))
 (.leaf (certNat% 92)))))
 (.branch 108
 (.branch 106
 (.leaf (certNat% 93))
 (.branch 107
 (.leaf (certNat% 94))
 (.leaf (certNat% 95))))
 (.branch 109
 (.leaf (certNat% 96))
 (.branch 110
 (.leaf (certNat% 97))
 (.leaf (certNat% 98))))))
 (.branch 116
 (.branch 113
 (.branch 112
 (.leaf (certNat% 99))
 (.leaf (certNat% 100)))
 (.branch 114
 (.leaf (certNat% 101))
 (.branch 115
 (.leaf (certNat% 102))
 (.leaf (certNat% 103)))))
 (.branch 119
 (.branch 117
 (.leaf (certNat% 104))
 (.branch 118
 (.leaf (certNat% 105))
 (.leaf (certNat% 106))))
 (.branch 120
 (.leaf (certNat% 107))
 (.branch 121
 (.leaf (certNat% 108))
 (.leaf (certNat% 109)))))))
 (.branch 133
 (.branch 127
 (.branch 124
 (.branch 123
 (.leaf (certNat% 110))
 (.leaf (certNat% 111)))
 (.branch 125
 (.leaf (certNat% 112))
 (.branch 126
 (.leaf (certNat% 113))
 (.leaf (certNat% 114)))))
 (.branch 130
 (.branch 128
 (.leaf (certNat% 115))
 (.branch 129
 (.leaf (certNat% 116))
 (.leaf (certNat% 117))))
 (.branch 131
 (.leaf (certNat% 118))
 (.branch 132
 (.leaf (certNat% 119))
 (.leaf (certNat% 120))))))
 (.branch 138
 (.branch 135
 (.branch 134
 (.leaf (certNat% 121))
 (.leaf (certNat% 122)))
 (.branch 136
 (.leaf (certNat% 123))
 (.branch 137
 (.leaf (certNat% 124))
 (.leaf (certNat% 125)))))
 (.branch 141
 (.branch 139
 (.leaf (certNat% 126))
 (.branch 140
 (.leaf (certNat% 127))
 (.leaf (certNat% 128))))
 (.branch 142
 (.leaf (certNat% 129))
 (.branch 143
 (.leaf (certNat% 130))
 (.leaf (certNat% 131))))))))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0303
