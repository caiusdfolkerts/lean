module
prelude
public meta import CertificateNumbers
public import PackedRawNatGrowth

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0707
open Papers.RationalityTen ConcreteGrowth

def nodeBlocks001 : Table PackedRawNatGrowth.Block :=
(.branch 65
 (.branch 57
 (.branch 53
 (.branch 51
 (.leaf ⟨(certNat% 0),(certNat% 1)⟩)
 (.branch 52
 (.leaf ⟨(certNat% 2),(certNat% 3)⟩)
 (.leaf ⟨(certNat% 4),(certNat% 5)⟩)))
 (.branch 55
 (.branch 54
 (.leaf ⟨(certNat% 6),(certNat% 7)⟩)
 (.leaf ⟨(certNat% 8),(certNat% 9)⟩))
 (.branch 56
 (.leaf ⟨(certNat% 10),(certNat% 11)⟩)
 (.leaf ⟨(certNat% 12),(certNat% 13)⟩))))
 (.branch 61
 (.branch 59
 (.branch 58
 (.leaf ⟨(certNat% 14),(certNat% 15)⟩)
 (.leaf ⟨(certNat% 16),(certNat% 17)⟩))
 (.branch 60
 (.leaf ⟨(certNat% 18),(certNat% 19)⟩)
 (.leaf ⟨(certNat% 20),(certNat% 21)⟩)))
 (.branch 63
 (.branch 62
 (.leaf ⟨(certNat% 22),(certNat% 23)⟩)
 (.leaf ⟨(certNat% 24),(certNat% 25)⟩))
 (.branch 64
 (.leaf ⟨(certNat% 26),(certNat% 27)⟩)
 (.leaf ⟨(certNat% 28),(certNat% 29)⟩)))))
 (.branch 72
 (.branch 68
 (.branch 66
 (.leaf ⟨(certNat% 30),(certNat% 31)⟩)
 (.branch 67
 (.leaf ⟨(certNat% 32),(certNat% 33)⟩)
 (.leaf ⟨(certNat% 34),(certNat% 35)⟩)))
 (.branch 70
 (.branch 69
 (.leaf ⟨(certNat% 36),(certNat% 37)⟩)
 (.leaf ⟨(certNat% 38),(certNat% 39)⟩))
 (.branch 71
 (.leaf ⟨(certNat% 40),(certNat% 41)⟩)
 (.leaf ⟨(certNat% 42),(certNat% 43)⟩))))
 (.branch 76
 (.branch 74
 (.branch 73
 (.leaf ⟨(certNat% 44),(certNat% 45)⟩)
 (.leaf ⟨(certNat% 46),(certNat% 47)⟩))
 (.branch 75
 (.leaf ⟨(certNat% 48),(certNat% 49)⟩)
 (.leaf ⟨(certNat% 50),(certNat% 51)⟩)))
 (.branch 78
 (.branch 77
 (.leaf ⟨(certNat% 52),(certNat% 53)⟩)
 (.leaf ⟨(certNat% 54),(certNat% 55)⟩))
 (.branch 79
 (.leaf ⟨(certNat% 56),(certNat% 57)⟩)
 (.leaf ⟨(certNat% 58),(certNat% 59)⟩))))))
def nodeCounters001 : Table Nat :=
(.branch 65
 (.branch 57
 (.branch 53
 (.branch 51
 (.leaf (certNat% 60))
 (.branch 52
 (.leaf (certNat% 61))
 (.leaf (certNat% 62))))
 (.branch 55
 (.branch 54
 (.leaf (certNat% 63))
 (.leaf (certNat% 64)))
 (.branch 56
 (.leaf (certNat% 65))
 (.leaf (certNat% 66)))))
 (.branch 61
 (.branch 59
 (.branch 58
 (.leaf (certNat% 67))
 (.leaf (certNat% 68)))
 (.branch 60
 (.leaf (certNat% 69))
 (.leaf (certNat% 70))))
 (.branch 63
 (.branch 62
 (.leaf (certNat% 71))
 (.leaf (certNat% 72)))
 (.branch 64
 (.leaf (certNat% 73))
 (.leaf (certNat% 74))))))
 (.branch 72
 (.branch 68
 (.branch 66
 (.leaf (certNat% 75))
 (.branch 67
 (.leaf (certNat% 76))
 (.leaf (certNat% 77))))
 (.branch 70
 (.branch 69
 (.leaf (certNat% 78))
 (.leaf (certNat% 79)))
 (.branch 71
 (.leaf (certNat% 80))
 (.leaf (certNat% 81)))))
 (.branch 76
 (.branch 74
 (.branch 73
 (.leaf (certNat% 82))
 (.leaf (certNat% 83)))
 (.branch 75
 (.leaf (certNat% 84))
 (.leaf (certNat% 85))))
 (.branch 78
 (.branch 77
 (.leaf (certNat% 86))
 (.leaf (certNat% 87)))
 (.branch 79
 (.leaf (certNat% 88))
 (.leaf (certNat% 89)))))))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0707
