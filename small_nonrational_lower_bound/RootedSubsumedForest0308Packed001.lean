module
prelude
public meta import CertificateNumbers
public import PackedRawNatGrowth

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0308
open Papers.RationalityTen ConcreteGrowth

def nodeBlocks001 : Table PackedRawNatGrowth.Block :=
(.branch 72
 (.branch 61
 (.branch 55
 (.branch 52
 (.branch 51
 (.leaf ⟨(certNat% 0),(certNat% 1)⟩)
 (.leaf ⟨(certNat% 2),(certNat% 3)⟩))
 (.branch 53
 (.leaf ⟨(certNat% 4),(certNat% 5)⟩)
 (.branch 54
 (.leaf ⟨(certNat% 6),(certNat% 7)⟩)
 (.leaf ⟨(certNat% 8),(certNat% 9)⟩))))
 (.branch 58
 (.branch 56
 (.leaf ⟨(certNat% 10),(certNat% 11)⟩)
 (.branch 57
 (.leaf ⟨(certNat% 12),(certNat% 13)⟩)
 (.leaf ⟨(certNat% 14),(certNat% 15)⟩)))
 (.branch 59
 (.leaf ⟨(certNat% 16),(certNat% 17)⟩)
 (.branch 60
 (.leaf ⟨(certNat% 18),(certNat% 19)⟩)
 (.leaf ⟨(certNat% 20),(certNat% 21)⟩)))))
 (.branch 66
 (.branch 63
 (.branch 62
 (.leaf ⟨(certNat% 22),(certNat% 23)⟩)
 (.leaf ⟨(certNat% 24),(certNat% 25)⟩))
 (.branch 64
 (.leaf ⟨(certNat% 26),(certNat% 27)⟩)
 (.branch 65
 (.leaf ⟨(certNat% 28),(certNat% 29)⟩)
 (.leaf ⟨(certNat% 30),(certNat% 31)⟩))))
 (.branch 69
 (.branch 67
 (.leaf ⟨(certNat% 32),(certNat% 33)⟩)
 (.branch 68
 (.leaf ⟨(certNat% 34),(certNat% 35)⟩)
 (.leaf ⟨(certNat% 36),(certNat% 37)⟩)))
 (.branch 70
 (.leaf ⟨(certNat% 38),(certNat% 39)⟩)
 (.branch 71
 (.leaf ⟨(certNat% 40),(certNat% 41)⟩)
 (.leaf ⟨(certNat% 42),(certNat% 43)⟩))))))
 (.branch 83
 (.branch 77
 (.branch 74
 (.branch 73
 (.leaf ⟨(certNat% 44),(certNat% 45)⟩)
 (.leaf ⟨(certNat% 46),(certNat% 47)⟩))
 (.branch 75
 (.leaf ⟨(certNat% 48),(certNat% 49)⟩)
 (.branch 76
 (.leaf ⟨(certNat% 50),(certNat% 51)⟩)
 (.leaf ⟨(certNat% 52),(certNat% 53)⟩))))
 (.branch 80
 (.branch 78
 (.leaf ⟨(certNat% 54),(certNat% 55)⟩)
 (.branch 79
 (.leaf ⟨(certNat% 56),(certNat% 57)⟩)
 (.leaf ⟨(certNat% 58),(certNat% 59)⟩)))
 (.branch 81
 (.leaf ⟨(certNat% 60),(certNat% 61)⟩)
 (.branch 82
 (.leaf ⟨(certNat% 62),(certNat% 63)⟩)
 (.leaf ⟨(certNat% 64),(certNat% 65)⟩)))))
 (.branch 89
 (.branch 86
 (.branch 84
 (.leaf ⟨(certNat% 66),(certNat% 67)⟩)
 (.branch 85
 (.leaf ⟨(certNat% 68),(certNat% 69)⟩)
 (.leaf ⟨(certNat% 70),(certNat% 71)⟩)))
 (.branch 87
 (.leaf ⟨(certNat% 72),(certNat% 73)⟩)
 (.branch 88
 (.leaf ⟨(certNat% 74),(certNat% 75)⟩)
 (.leaf ⟨(certNat% 76),(certNat% 77)⟩))))
 (.branch 92
 (.branch 90
 (.leaf ⟨(certNat% 78),(certNat% 79)⟩)
 (.branch 91
 (.leaf ⟨(certNat% 80),(certNat% 81)⟩)
 (.leaf ⟨(certNat% 82),(certNat% 83)⟩)))
 (.branch 93
 (.leaf ⟨(certNat% 84),(certNat% 85)⟩)
 (.branch 94
 (.leaf ⟨(certNat% 86),(certNat% 87)⟩)
 (.leaf ⟨(certNat% 88),(certNat% 89)⟩)))))))
def nodeCounters001 : Table Nat :=
(.branch 72
 (.branch 61
 (.branch 55
 (.branch 52
 (.branch 51
 (.leaf (certNat% 90))
 (.leaf (certNat% 91)))
 (.branch 53
 (.leaf (certNat% 92))
 (.branch 54
 (.leaf (certNat% 93))
 (.leaf (certNat% 94)))))
 (.branch 58
 (.branch 56
 (.leaf (certNat% 95))
 (.branch 57
 (.leaf (certNat% 96))
 (.leaf (certNat% 97))))
 (.branch 59
 (.leaf (certNat% 98))
 (.branch 60
 (.leaf (certNat% 99))
 (.leaf (certNat% 100))))))
 (.branch 66
 (.branch 63
 (.branch 62
 (.leaf (certNat% 101))
 (.leaf (certNat% 102)))
 (.branch 64
 (.leaf (certNat% 103))
 (.branch 65
 (.leaf (certNat% 104))
 (.leaf (certNat% 105)))))
 (.branch 69
 (.branch 67
 (.leaf (certNat% 106))
 (.branch 68
 (.leaf (certNat% 107))
 (.leaf (certNat% 108))))
 (.branch 70
 (.leaf (certNat% 109))
 (.branch 71
 (.leaf (certNat% 110))
 (.leaf (certNat% 111)))))))
 (.branch 83
 (.branch 77
 (.branch 74
 (.branch 73
 (.leaf (certNat% 112))
 (.leaf (certNat% 113)))
 (.branch 75
 (.leaf (certNat% 114))
 (.branch 76
 (.leaf (certNat% 115))
 (.leaf (certNat% 116)))))
 (.branch 80
 (.branch 78
 (.leaf (certNat% 117))
 (.branch 79
 (.leaf (certNat% 118))
 (.leaf (certNat% 119))))
 (.branch 81
 (.leaf (certNat% 120))
 (.branch 82
 (.leaf (certNat% 121))
 (.leaf (certNat% 122))))))
 (.branch 89
 (.branch 86
 (.branch 84
 (.leaf (certNat% 123))
 (.branch 85
 (.leaf (certNat% 124))
 (.leaf (certNat% 125))))
 (.branch 87
 (.leaf (certNat% 126))
 (.branch 88
 (.leaf (certNat% 127))
 (.leaf (certNat% 128)))))
 (.branch 92
 (.branch 90
 (.leaf (certNat% 129))
 (.branch 91
 (.leaf (certNat% 130))
 (.leaf (certNat% 131))))
 (.branch 93
 (.leaf (certNat% 132))
 (.branch 94
 (.leaf (certNat% 133))
 (.leaf (certNat% 134))))))))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0308
