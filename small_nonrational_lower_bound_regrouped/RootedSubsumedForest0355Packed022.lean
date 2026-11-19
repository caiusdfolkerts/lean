module
prelude
public meta import CertificateNumbers
public import PackedRawNatGrowth

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth

def nodeBlocks022 : Table PackedRawNatGrowth.Block :=
(.branch 1125
 (.branch 1112
 (.branch 1106
 (.branch 1103
 (.branch 1101
 (.leaf ⟨(certNat% 0),(certNat% 1)⟩)
 (.branch 1102
 (.leaf ⟨(certNat% 2),(certNat% 3)⟩)
 (.leaf ⟨(certNat% 4),(certNat% 5)⟩)))
 (.branch 1104
 (.leaf ⟨(certNat% 6),(certNat% 7)⟩)
 (.branch 1105
 (.leaf ⟨(certNat% 8),(certNat% 9)⟩)
 (.leaf ⟨(certNat% 10),(certNat% 11)⟩))))
 (.branch 1109
 (.branch 1107
 (.leaf ⟨(certNat% 12),(certNat% 13)⟩)
 (.branch 1108
 (.leaf ⟨(certNat% 14),(certNat% 15)⟩)
 (.leaf ⟨(certNat% 16),(certNat% 17)⟩)))
 (.branch 1110
 (.leaf ⟨(certNat% 18),(certNat% 19)⟩)
 (.branch 1111
 (.leaf ⟨(certNat% 20),(certNat% 21)⟩)
 (.leaf ⟨(certNat% 22),(certNat% 23)⟩)))))
 (.branch 1118
 (.branch 1115
 (.branch 1113
 (.leaf ⟨(certNat% 24),(certNat% 25)⟩)
 (.branch 1114
 (.leaf ⟨(certNat% 26),(certNat% 27)⟩)
 (.leaf ⟨(certNat% 28),(certNat% 29)⟩)))
 (.branch 1116
 (.leaf ⟨(certNat% 30),(certNat% 31)⟩)
 (.branch 1117
 (.leaf ⟨(certNat% 32),(certNat% 33)⟩)
 (.leaf ⟨(certNat% 34),(certNat% 35)⟩))))
 (.branch 1121
 (.branch 1119
 (.leaf ⟨(certNat% 36),(certNat% 37)⟩)
 (.branch 1120
 (.leaf ⟨(certNat% 38),(certNat% 39)⟩)
 (.leaf ⟨(certNat% 40),(certNat% 41)⟩)))
 (.branch 1123
 (.branch 1122
 (.leaf ⟨(certNat% 42),(certNat% 43)⟩)
 (.leaf ⟨(certNat% 44),(certNat% 45)⟩))
 (.branch 1124
 (.leaf ⟨(certNat% 46),(certNat% 47)⟩)
 (.leaf ⟨(certNat% 48),(certNat% 49)⟩))))))
 (.branch 1137
 (.branch 1131
 (.branch 1128
 (.branch 1126
 (.leaf ⟨(certNat% 50),(certNat% 51)⟩)
 (.branch 1127
 (.leaf ⟨(certNat% 52),(certNat% 53)⟩)
 (.leaf ⟨(certNat% 54),(certNat% 55)⟩)))
 (.branch 1129
 (.leaf ⟨(certNat% 56),(certNat% 57)⟩)
 (.branch 1130
 (.leaf ⟨(certNat% 58),(certNat% 59)⟩)
 (.leaf ⟨(certNat% 60),(certNat% 61)⟩))))
 (.branch 1134
 (.branch 1132
 (.leaf ⟨(certNat% 62),(certNat% 63)⟩)
 (.branch 1133
 (.leaf ⟨(certNat% 64),(certNat% 65)⟩)
 (.leaf ⟨(certNat% 66),(certNat% 67)⟩)))
 (.branch 1135
 (.leaf ⟨(certNat% 68),(certNat% 69)⟩)
 (.branch 1136
 (.leaf ⟨(certNat% 70),(certNat% 71)⟩)
 (.leaf ⟨(certNat% 72),(certNat% 73)⟩)))))
 (.branch 1143
 (.branch 1140
 (.branch 1138
 (.leaf ⟨(certNat% 74),(certNat% 75)⟩)
 (.branch 1139
 (.leaf ⟨(certNat% 76),(certNat% 77)⟩)
 (.leaf ⟨(certNat% 78),(certNat% 79)⟩)))
 (.branch 1141
 (.leaf ⟨(certNat% 80),(certNat% 81)⟩)
 (.branch 1142
 (.leaf ⟨(certNat% 82),(certNat% 83)⟩)
 (.leaf ⟨(certNat% 84),(certNat% 85)⟩))))
 (.branch 1146
 (.branch 1144
 (.leaf ⟨(certNat% 86),(certNat% 87)⟩)
 (.branch 1145
 (.leaf ⟨(certNat% 88),(certNat% 89)⟩)
 (.leaf ⟨(certNat% 90),(certNat% 91)⟩)))
 (.branch 1148
 (.branch 1147
 (.leaf ⟨(certNat% 92),(certNat% 93)⟩)
 (.leaf ⟨(certNat% 94),(certNat% 95)⟩))
 (.branch 1149
 (.leaf ⟨(certNat% 96),(certNat% 97)⟩)
 (.leaf ⟨(certNat% 98),(certNat% 99)⟩)))))))
def nodeCounters022 : Table Nat :=
(.branch 1125
 (.branch 1112
 (.branch 1106
 (.branch 1103
 (.branch 1101
 (.leaf (certNat% 100))
 (.branch 1102
 (.leaf (certNat% 101))
 (.leaf (certNat% 102))))
 (.branch 1104
 (.leaf (certNat% 103))
 (.branch 1105
 (.leaf (certNat% 104))
 (.leaf (certNat% 105)))))
 (.branch 1109
 (.branch 1107
 (.leaf (certNat% 106))
 (.branch 1108
 (.leaf (certNat% 107))
 (.leaf (certNat% 108))))
 (.branch 1110
 (.leaf (certNat% 109))
 (.branch 1111
 (.leaf (certNat% 110))
 (.leaf (certNat% 111))))))
 (.branch 1118
 (.branch 1115
 (.branch 1113
 (.leaf (certNat% 112))
 (.branch 1114
 (.leaf (certNat% 113))
 (.leaf (certNat% 114))))
 (.branch 1116
 (.leaf (certNat% 115))
 (.branch 1117
 (.leaf (certNat% 116))
 (.leaf (certNat% 117)))))
 (.branch 1121
 (.branch 1119
 (.leaf (certNat% 118))
 (.branch 1120
 (.leaf (certNat% 119))
 (.leaf (certNat% 120))))
 (.branch 1123
 (.branch 1122
 (.leaf (certNat% 121))
 (.leaf (certNat% 122)))
 (.branch 1124
 (.leaf (certNat% 123))
 (.leaf (certNat% 124)))))))
 (.branch 1137
 (.branch 1131
 (.branch 1128
 (.branch 1126
 (.leaf (certNat% 125))
 (.branch 1127
 (.leaf (certNat% 126))
 (.leaf (certNat% 127))))
 (.branch 1129
 (.leaf (certNat% 128))
 (.branch 1130
 (.leaf (certNat% 129))
 (.leaf (certNat% 130)))))
 (.branch 1134
 (.branch 1132
 (.leaf (certNat% 131))
 (.branch 1133
 (.leaf (certNat% 132))
 (.leaf (certNat% 133))))
 (.branch 1135
 (.leaf (certNat% 134))
 (.branch 1136
 (.leaf (certNat% 135))
 (.leaf (certNat% 136))))))
 (.branch 1143
 (.branch 1140
 (.branch 1138
 (.leaf (certNat% 137))
 (.branch 1139
 (.leaf (certNat% 138))
 (.leaf (certNat% 139))))
 (.branch 1141
 (.leaf (certNat% 140))
 (.branch 1142
 (.leaf (certNat% 141))
 (.leaf (certNat% 142)))))
 (.branch 1146
 (.branch 1144
 (.leaf (certNat% 143))
 (.branch 1145
 (.leaf (certNat% 144))
 (.leaf (certNat% 145))))
 (.branch 1148
 (.branch 1147
 (.leaf (certNat% 146))
 (.leaf (certNat% 147)))
 (.branch 1149
 (.leaf (certNat% 148))
 (.leaf (certNat% 149))))))))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
