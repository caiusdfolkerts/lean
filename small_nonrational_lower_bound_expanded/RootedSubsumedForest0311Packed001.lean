module
prelude
public meta import CertificateNumbers
public import PackedRawNatGrowth

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0311
open Papers.RationalityTen ConcreteGrowth

def nodeBlocks001 : Table PackedRawNatGrowth.Block :=
(.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(certNat% 0),(certNat% 1)⟩)
 (.branch 52
 (.leaf ⟨(certNat% 2),(certNat% 3)⟩)
 (.leaf ⟨(certNat% 4),(certNat% 5)⟩)))
 (.branch 54
 (.leaf ⟨(certNat% 6),(certNat% 7)⟩)
 (.branch 55
 (.leaf ⟨(certNat% 8),(certNat% 9)⟩)
 (.leaf ⟨(certNat% 10),(certNat% 11)⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(certNat% 12),(certNat% 13)⟩)
 (.branch 58
 (.leaf ⟨(certNat% 14),(certNat% 15)⟩)
 (.leaf ⟨(certNat% 16),(certNat% 17)⟩)))
 (.branch 60
 (.leaf ⟨(certNat% 18),(certNat% 19)⟩)
 (.branch 61
 (.leaf ⟨(certNat% 20),(certNat% 21)⟩)
 (.leaf ⟨(certNat% 22),(certNat% 23)⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(certNat% 24),(certNat% 25)⟩)
 (.branch 64
 (.leaf ⟨(certNat% 26),(certNat% 27)⟩)
 (.leaf ⟨(certNat% 28),(certNat% 29)⟩)))
 (.branch 66
 (.leaf ⟨(certNat% 30),(certNat% 31)⟩)
 (.branch 67
 (.leaf ⟨(certNat% 32),(certNat% 33)⟩)
 (.leaf ⟨(certNat% 34),(certNat% 35)⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(certNat% 36),(certNat% 37)⟩)
 (.branch 70
 (.leaf ⟨(certNat% 38),(certNat% 39)⟩)
 (.leaf ⟨(certNat% 40),(certNat% 41)⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(certNat% 42),(certNat% 43)⟩)
 (.leaf ⟨(certNat% 44),(certNat% 45)⟩))
 (.branch 74
 (.leaf ⟨(certNat% 46),(certNat% 47)⟩)
 (.leaf ⟨(certNat% 48),(certNat% 49)⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(certNat% 50),(certNat% 51)⟩)
 (.branch 77
 (.leaf ⟨(certNat% 52),(certNat% 53)⟩)
 (.leaf ⟨(certNat% 54),(certNat% 55)⟩)))
 (.branch 79
 (.leaf ⟨(certNat% 56),(certNat% 57)⟩)
 (.branch 80
 (.leaf ⟨(certNat% 58),(certNat% 59)⟩)
 (.leaf ⟨(certNat% 60),(certNat% 61)⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(certNat% 62),(certNat% 63)⟩)
 (.branch 83
 (.leaf ⟨(certNat% 64),(certNat% 65)⟩)
 (.leaf ⟨(certNat% 66),(certNat% 67)⟩)))
 (.branch 85
 (.leaf ⟨(certNat% 68),(certNat% 69)⟩)
 (.branch 86
 (.leaf ⟨(certNat% 70),(certNat% 71)⟩)
 (.leaf ⟨(certNat% 72),(certNat% 73)⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(certNat% 74),(certNat% 75)⟩)
 (.branch 89
 (.leaf ⟨(certNat% 76),(certNat% 77)⟩)
 (.leaf ⟨(certNat% 78),(certNat% 79)⟩)))
 (.branch 91
 (.leaf ⟨(certNat% 80),(certNat% 81)⟩)
 (.branch 92
 (.leaf ⟨(certNat% 82),(certNat% 83)⟩)
 (.leaf ⟨(certNat% 84),(certNat% 85)⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(certNat% 86),(certNat% 87)⟩)
 (.branch 95
 (.leaf ⟨(certNat% 88),(certNat% 89)⟩)
 (.leaf ⟨(certNat% 90),(certNat% 91)⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(certNat% 92),(certNat% 93)⟩)
 (.leaf ⟨(certNat% 94),(certNat% 95)⟩))
 (.branch 99
 (.leaf ⟨(certNat% 96),(certNat% 97)⟩)
 (.leaf ⟨(certNat% 98),(certNat% 99)⟩)))))))
def nodeCounters001 : Table Nat :=
(.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf (certNat% 100))
 (.branch 52
 (.leaf (certNat% 101))
 (.leaf (certNat% 102))))
 (.branch 54
 (.leaf (certNat% 103))
 (.branch 55
 (.leaf (certNat% 104))
 (.leaf (certNat% 105)))))
 (.branch 59
 (.branch 57
 (.leaf (certNat% 106))
 (.branch 58
 (.leaf (certNat% 107))
 (.leaf (certNat% 108))))
 (.branch 60
 (.leaf (certNat% 109))
 (.branch 61
 (.leaf (certNat% 110))
 (.leaf (certNat% 111))))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf (certNat% 112))
 (.branch 64
 (.leaf (certNat% 113))
 (.leaf (certNat% 114))))
 (.branch 66
 (.leaf (certNat% 115))
 (.branch 67
 (.leaf (certNat% 116))
 (.leaf (certNat% 117)))))
 (.branch 71
 (.branch 69
 (.leaf (certNat% 118))
 (.branch 70
 (.leaf (certNat% 119))
 (.leaf (certNat% 120))))
 (.branch 73
 (.branch 72
 (.leaf (certNat% 121))
 (.leaf (certNat% 122)))
 (.branch 74
 (.leaf (certNat% 123))
 (.leaf (certNat% 124)))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf (certNat% 125))
 (.branch 77
 (.leaf (certNat% 126))
 (.leaf (certNat% 127))))
 (.branch 79
 (.leaf (certNat% 128))
 (.branch 80
 (.leaf (certNat% 129))
 (.leaf (certNat% 130)))))
 (.branch 84
 (.branch 82
 (.leaf (certNat% 131))
 (.branch 83
 (.leaf (certNat% 132))
 (.leaf (certNat% 133))))
 (.branch 85
 (.leaf (certNat% 134))
 (.branch 86
 (.leaf (certNat% 135))
 (.leaf (certNat% 136))))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf (certNat% 137))
 (.branch 89
 (.leaf (certNat% 138))
 (.leaf (certNat% 139))))
 (.branch 91
 (.leaf (certNat% 140))
 (.branch 92
 (.leaf (certNat% 141))
 (.leaf (certNat% 142)))))
 (.branch 96
 (.branch 94
 (.leaf (certNat% 143))
 (.branch 95
 (.leaf (certNat% 144))
 (.leaf (certNat% 145))))
 (.branch 98
 (.branch 97
 (.leaf (certNat% 146))
 (.leaf (certNat% 147)))
 (.branch 99
 (.leaf (certNat% 148))
 (.leaf (certNat% 149))))))))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0311
