module
prelude
public meta import CertificateNumbers
public import PackedRawNatGrowth

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest03
open Papers.RationalityTen ConcreteGrowth

def nodeBlocks001 : Table PackedRawNatGrowth.Block :=
(.branch 66
 (.branch 58
 (.branch 54
 (.branch 52
 (.branch 51
 (.leaf ⟨(certNat% 0),(certNat% 1)⟩)
 (.leaf ⟨(certNat% 2),(certNat% 3)⟩))
 (.branch 53
 (.leaf ⟨(certNat% 4),(certNat% 5)⟩)
 (.leaf ⟨(certNat% 6),(certNat% 7)⟩)))
 (.branch 56
 (.branch 55
 (.leaf ⟨(certNat% 8),(certNat% 9)⟩)
 (.leaf ⟨(certNat% 10),(certNat% 11)⟩))
 (.branch 57
 (.leaf ⟨(certNat% 12),(certNat% 13)⟩)
 (.leaf ⟨(certNat% 14),(certNat% 15)⟩))))
 (.branch 62
 (.branch 60
 (.branch 59
 (.leaf ⟨(certNat% 16),(certNat% 17)⟩)
 (.leaf ⟨(certNat% 18),(certNat% 19)⟩))
 (.branch 61
 (.leaf ⟨(certNat% 20),(certNat% 21)⟩)
 (.leaf ⟨(certNat% 22),(certNat% 23)⟩)))
 (.branch 64
 (.branch 63
 (.leaf ⟨(certNat% 24),(certNat% 25)⟩)
 (.leaf ⟨(certNat% 26),(certNat% 27)⟩))
 (.branch 65
 (.leaf ⟨(certNat% 28),(certNat% 29)⟩)
 (.leaf ⟨(certNat% 30),(certNat% 31)⟩)))))
 (.branch 74
 (.branch 70
 (.branch 68
 (.branch 67
 (.leaf ⟨(certNat% 32),(certNat% 33)⟩)
 (.leaf ⟨(certNat% 34),(certNat% 35)⟩))
 (.branch 69
 (.leaf ⟨(certNat% 36),(certNat% 37)⟩)
 (.leaf ⟨(certNat% 38),(certNat% 39)⟩)))
 (.branch 72
 (.branch 71
 (.leaf ⟨(certNat% 40),(certNat% 41)⟩)
 (.leaf ⟨(certNat% 42),(certNat% 43)⟩))
 (.branch 73
 (.leaf ⟨(certNat% 44),(certNat% 45)⟩)
 (.leaf ⟨(certNat% 46),(certNat% 47)⟩))))
 (.branch 78
 (.branch 76
 (.branch 75
 (.leaf ⟨(certNat% 48),(certNat% 49)⟩)
 (.leaf ⟨(certNat% 50),(certNat% 51)⟩))
 (.branch 77
 (.leaf ⟨(certNat% 52),(certNat% 53)⟩)
 (.leaf ⟨(certNat% 54),(certNat% 55)⟩)))
 (.branch 80
 (.branch 79
 (.leaf ⟨(certNat% 56),(certNat% 57)⟩)
 (.leaf ⟨(certNat% 58),(certNat% 59)⟩))
 (.branch 81
 (.leaf ⟨(certNat% 60),(certNat% 61)⟩)
 (.leaf ⟨(certNat% 62),(certNat% 63)⟩))))))
def nodeCounters001 : Table Nat :=
(.branch 66
 (.branch 58
 (.branch 54
 (.branch 52
 (.branch 51
 (.leaf (certNat% 64))
 (.leaf (certNat% 65)))
 (.branch 53
 (.leaf (certNat% 66))
 (.leaf (certNat% 67))))
 (.branch 56
 (.branch 55
 (.leaf (certNat% 68))
 (.leaf (certNat% 69)))
 (.branch 57
 (.leaf (certNat% 70))
 (.leaf (certNat% 71)))))
 (.branch 62
 (.branch 60
 (.branch 59
 (.leaf (certNat% 72))
 (.leaf (certNat% 73)))
 (.branch 61
 (.leaf (certNat% 74))
 (.leaf (certNat% 75))))
 (.branch 64
 (.branch 63
 (.leaf (certNat% 76))
 (.leaf (certNat% 77)))
 (.branch 65
 (.leaf (certNat% 78))
 (.leaf (certNat% 79))))))
 (.branch 74
 (.branch 70
 (.branch 68
 (.branch 67
 (.leaf (certNat% 80))
 (.leaf (certNat% 81)))
 (.branch 69
 (.leaf (certNat% 82))
 (.leaf (certNat% 83))))
 (.branch 72
 (.branch 71
 (.leaf (certNat% 84))
 (.leaf (certNat% 85)))
 (.branch 73
 (.leaf (certNat% 86))
 (.leaf (certNat% 87)))))
 (.branch 78
 (.branch 76
 (.branch 75
 (.leaf (certNat% 88))
 (.leaf (certNat% 89)))
 (.branch 77
 (.leaf (certNat% 90))
 (.leaf (certNat% 91))))
 (.branch 80
 (.branch 79
 (.leaf (certNat% 92))
 (.leaf (certNat% 93)))
 (.branch 81
 (.leaf (certNat% 94))
 (.leaf (certNat% 95)))))))

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest03
