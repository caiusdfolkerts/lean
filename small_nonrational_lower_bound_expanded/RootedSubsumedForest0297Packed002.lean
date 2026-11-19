module
prelude
public meta import CertificateNumbers
public import PackedRawNatGrowth

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0297
open Papers.RationalityTen ConcreteGrowth

def nodeBlocks002 : Table PackedRawNatGrowth.Block :=
(.branch 123
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
 (.branch 134
 (.branch 128
 (.branch 125
 (.branch 124
 (.leaf ⟨(certNat% 46),(certNat% 47)⟩)
 (.leaf ⟨(certNat% 48),(certNat% 49)⟩))
 (.branch 126
 (.leaf ⟨(certNat% 50),(certNat% 51)⟩)
 (.branch 127
 (.leaf ⟨(certNat% 52),(certNat% 53)⟩)
 (.leaf ⟨(certNat% 54),(certNat% 55)⟩))))
 (.branch 131
 (.branch 129
 (.leaf ⟨(certNat% 56),(certNat% 57)⟩)
 (.branch 130
 (.leaf ⟨(certNat% 58),(certNat% 59)⟩)
 (.leaf ⟨(certNat% 60),(certNat% 61)⟩)))
 (.branch 132
 (.leaf ⟨(certNat% 62),(certNat% 63)⟩)
 (.branch 133
 (.leaf ⟨(certNat% 64),(certNat% 65)⟩)
 (.leaf ⟨(certNat% 66),(certNat% 67)⟩)))))
 (.branch 140
 (.branch 137
 (.branch 135
 (.leaf ⟨(certNat% 68),(certNat% 69)⟩)
 (.branch 136
 (.leaf ⟨(certNat% 70),(certNat% 71)⟩)
 (.leaf ⟨(certNat% 72),(certNat% 73)⟩)))
 (.branch 138
 (.leaf ⟨(certNat% 74),(certNat% 75)⟩)
 (.branch 139
 (.leaf ⟨(certNat% 76),(certNat% 77)⟩)
 (.leaf ⟨(certNat% 78),(certNat% 79)⟩))))
 (.branch 143
 (.branch 141
 (.leaf ⟨(certNat% 80),(certNat% 81)⟩)
 (.branch 142
 (.leaf ⟨(certNat% 82),(certNat% 83)⟩)
 (.leaf ⟨(certNat% 84),(certNat% 85)⟩)))
 (.branch 144
 (.leaf ⟨(certNat% 86),(certNat% 87)⟩)
 (.branch 145
 (.leaf ⟨(certNat% 88),(certNat% 89)⟩)
 (.leaf ⟨(certNat% 90),(certNat% 91)⟩)))))))
def nodeCounters002 : Table Nat :=
(.branch 123
 (.branch 111
 (.branch 105
 (.branch 102
 (.branch 101
 (.leaf (certNat% 92))
 (.leaf (certNat% 93)))
 (.branch 103
 (.leaf (certNat% 94))
 (.branch 104
 (.leaf (certNat% 95))
 (.leaf (certNat% 96)))))
 (.branch 108
 (.branch 106
 (.leaf (certNat% 97))
 (.branch 107
 (.leaf (certNat% 98))
 (.leaf (certNat% 99))))
 (.branch 109
 (.leaf (certNat% 100))
 (.branch 110
 (.leaf (certNat% 101))
 (.leaf (certNat% 102))))))
 (.branch 117
 (.branch 114
 (.branch 112
 (.leaf (certNat% 103))
 (.branch 113
 (.leaf (certNat% 104))
 (.leaf (certNat% 105))))
 (.branch 115
 (.leaf (certNat% 106))
 (.branch 116
 (.leaf (certNat% 107))
 (.leaf (certNat% 108)))))
 (.branch 120
 (.branch 118
 (.leaf (certNat% 109))
 (.branch 119
 (.leaf (certNat% 110))
 (.leaf (certNat% 111))))
 (.branch 121
 (.leaf (certNat% 112))
 (.branch 122
 (.leaf (certNat% 113))
 (.leaf (certNat% 114)))))))
 (.branch 134
 (.branch 128
 (.branch 125
 (.branch 124
 (.leaf (certNat% 115))
 (.leaf (certNat% 116)))
 (.branch 126
 (.leaf (certNat% 117))
 (.branch 127
 (.leaf (certNat% 118))
 (.leaf (certNat% 119)))))
 (.branch 131
 (.branch 129
 (.leaf (certNat% 120))
 (.branch 130
 (.leaf (certNat% 121))
 (.leaf (certNat% 122))))
 (.branch 132
 (.leaf (certNat% 123))
 (.branch 133
 (.leaf (certNat% 124))
 (.leaf (certNat% 125))))))
 (.branch 140
 (.branch 137
 (.branch 135
 (.leaf (certNat% 126))
 (.branch 136
 (.leaf (certNat% 127))
 (.leaf (certNat% 128))))
 (.branch 138
 (.leaf (certNat% 129))
 (.branch 139
 (.leaf (certNat% 130))
 (.leaf (certNat% 131)))))
 (.branch 143
 (.branch 141
 (.leaf (certNat% 132))
 (.branch 142
 (.leaf (certNat% 133))
 (.leaf (certNat% 134))))
 (.branch 144
 (.leaf (certNat% 135))
 (.branch 145
 (.leaf (certNat% 136))
 (.leaf (certNat% 137))))))))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0297
