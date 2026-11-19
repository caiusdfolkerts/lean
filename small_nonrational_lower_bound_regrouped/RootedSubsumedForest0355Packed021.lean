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

def nodeBlocks021 : Table PackedRawNatGrowth.Block :=
(.branch 1075
 (.branch 1062
 (.branch 1056
 (.branch 1053
 (.branch 1051
 (.leaf ⟨(certNat% 0),(certNat% 1)⟩)
 (.branch 1052
 (.leaf ⟨(certNat% 2),(certNat% 3)⟩)
 (.leaf ⟨(certNat% 4),(certNat% 5)⟩)))
 (.branch 1054
 (.leaf ⟨(certNat% 6),(certNat% 7)⟩)
 (.branch 1055
 (.leaf ⟨(certNat% 8),(certNat% 9)⟩)
 (.leaf ⟨(certNat% 10),(certNat% 11)⟩))))
 (.branch 1059
 (.branch 1057
 (.leaf ⟨(certNat% 12),(certNat% 13)⟩)
 (.branch 1058
 (.leaf ⟨(certNat% 14),(certNat% 15)⟩)
 (.leaf ⟨(certNat% 16),(certNat% 17)⟩)))
 (.branch 1060
 (.leaf ⟨(certNat% 18),(certNat% 19)⟩)
 (.branch 1061
 (.leaf ⟨(certNat% 20),(certNat% 21)⟩)
 (.leaf ⟨(certNat% 22),(certNat% 23)⟩)))))
 (.branch 1068
 (.branch 1065
 (.branch 1063
 (.leaf ⟨(certNat% 24),(certNat% 25)⟩)
 (.branch 1064
 (.leaf ⟨(certNat% 26),(certNat% 27)⟩)
 (.leaf ⟨(certNat% 28),(certNat% 29)⟩)))
 (.branch 1066
 (.leaf ⟨(certNat% 30),(certNat% 31)⟩)
 (.branch 1067
 (.leaf ⟨(certNat% 32),(certNat% 33)⟩)
 (.leaf ⟨(certNat% 34),(certNat% 35)⟩))))
 (.branch 1071
 (.branch 1069
 (.leaf ⟨(certNat% 36),(certNat% 37)⟩)
 (.branch 1070
 (.leaf ⟨(certNat% 38),(certNat% 39)⟩)
 (.leaf ⟨(certNat% 40),(certNat% 41)⟩)))
 (.branch 1073
 (.branch 1072
 (.leaf ⟨(certNat% 42),(certNat% 43)⟩)
 (.leaf ⟨(certNat% 44),(certNat% 45)⟩))
 (.branch 1074
 (.leaf ⟨(certNat% 46),(certNat% 47)⟩)
 (.leaf ⟨(certNat% 48),(certNat% 49)⟩))))))
 (.branch 1087
 (.branch 1081
 (.branch 1078
 (.branch 1076
 (.leaf ⟨(certNat% 50),(certNat% 51)⟩)
 (.branch 1077
 (.leaf ⟨(certNat% 52),(certNat% 53)⟩)
 (.leaf ⟨(certNat% 54),(certNat% 55)⟩)))
 (.branch 1079
 (.leaf ⟨(certNat% 56),(certNat% 57)⟩)
 (.branch 1080
 (.leaf ⟨(certNat% 58),(certNat% 59)⟩)
 (.leaf ⟨(certNat% 60),(certNat% 61)⟩))))
 (.branch 1084
 (.branch 1082
 (.leaf ⟨(certNat% 62),(certNat% 63)⟩)
 (.branch 1083
 (.leaf ⟨(certNat% 64),(certNat% 65)⟩)
 (.leaf ⟨(certNat% 66),(certNat% 67)⟩)))
 (.branch 1085
 (.leaf ⟨(certNat% 68),(certNat% 69)⟩)
 (.branch 1086
 (.leaf ⟨(certNat% 70),(certNat% 71)⟩)
 (.leaf ⟨(certNat% 72),(certNat% 73)⟩)))))
 (.branch 1093
 (.branch 1090
 (.branch 1088
 (.leaf ⟨(certNat% 74),(certNat% 75)⟩)
 (.branch 1089
 (.leaf ⟨(certNat% 76),(certNat% 77)⟩)
 (.leaf ⟨(certNat% 78),(certNat% 79)⟩)))
 (.branch 1091
 (.leaf ⟨(certNat% 80),(certNat% 81)⟩)
 (.branch 1092
 (.leaf ⟨(certNat% 82),(certNat% 83)⟩)
 (.leaf ⟨(certNat% 84),(certNat% 85)⟩))))
 (.branch 1096
 (.branch 1094
 (.leaf ⟨(certNat% 86),(certNat% 87)⟩)
 (.branch 1095
 (.leaf ⟨(certNat% 88),(certNat% 89)⟩)
 (.leaf ⟨(certNat% 90),(certNat% 91)⟩)))
 (.branch 1098
 (.branch 1097
 (.leaf ⟨(certNat% 92),(certNat% 93)⟩)
 (.leaf ⟨(certNat% 94),(certNat% 95)⟩))
 (.branch 1099
 (.leaf ⟨(certNat% 96),(certNat% 97)⟩)
 (.leaf ⟨(certNat% 98),(certNat% 99)⟩)))))))
def nodeCounters021 : Table Nat :=
(.branch 1075
 (.branch 1062
 (.branch 1056
 (.branch 1053
 (.branch 1051
 (.leaf (certNat% 100))
 (.branch 1052
 (.leaf (certNat% 101))
 (.leaf (certNat% 102))))
 (.branch 1054
 (.leaf (certNat% 103))
 (.branch 1055
 (.leaf (certNat% 104))
 (.leaf (certNat% 105)))))
 (.branch 1059
 (.branch 1057
 (.leaf (certNat% 106))
 (.branch 1058
 (.leaf (certNat% 107))
 (.leaf (certNat% 108))))
 (.branch 1060
 (.leaf (certNat% 109))
 (.branch 1061
 (.leaf (certNat% 110))
 (.leaf (certNat% 111))))))
 (.branch 1068
 (.branch 1065
 (.branch 1063
 (.leaf (certNat% 112))
 (.branch 1064
 (.leaf (certNat% 113))
 (.leaf (certNat% 114))))
 (.branch 1066
 (.leaf (certNat% 115))
 (.branch 1067
 (.leaf (certNat% 116))
 (.leaf (certNat% 117)))))
 (.branch 1071
 (.branch 1069
 (.leaf (certNat% 118))
 (.branch 1070
 (.leaf (certNat% 119))
 (.leaf (certNat% 120))))
 (.branch 1073
 (.branch 1072
 (.leaf (certNat% 121))
 (.leaf (certNat% 122)))
 (.branch 1074
 (.leaf (certNat% 123))
 (.leaf (certNat% 124)))))))
 (.branch 1087
 (.branch 1081
 (.branch 1078
 (.branch 1076
 (.leaf (certNat% 125))
 (.branch 1077
 (.leaf (certNat% 126))
 (.leaf (certNat% 127))))
 (.branch 1079
 (.leaf (certNat% 128))
 (.branch 1080
 (.leaf (certNat% 129))
 (.leaf (certNat% 130)))))
 (.branch 1084
 (.branch 1082
 (.leaf (certNat% 131))
 (.branch 1083
 (.leaf (certNat% 132))
 (.leaf (certNat% 133))))
 (.branch 1085
 (.leaf (certNat% 134))
 (.branch 1086
 (.leaf (certNat% 135))
 (.leaf (certNat% 136))))))
 (.branch 1093
 (.branch 1090
 (.branch 1088
 (.leaf (certNat% 137))
 (.branch 1089
 (.leaf (certNat% 138))
 (.leaf (certNat% 139))))
 (.branch 1091
 (.leaf (certNat% 140))
 (.branch 1092
 (.leaf (certNat% 141))
 (.leaf (certNat% 142)))))
 (.branch 1096
 (.branch 1094
 (.leaf (certNat% 143))
 (.branch 1095
 (.leaf (certNat% 144))
 (.leaf (certNat% 145))))
 (.branch 1098
 (.branch 1097
 (.leaf (certNat% 146))
 (.leaf (certNat% 147)))
 (.branch 1099
 (.leaf (certNat% 148))
 (.leaf (certNat% 149))))))))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
