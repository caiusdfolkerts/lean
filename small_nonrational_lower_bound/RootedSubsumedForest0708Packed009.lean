module
prelude
public meta import CertificateNumbers
public import PackedRawNatGrowth

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
open Papers.RationalityTen ConcreteGrowth

def nodeBlocks009 : Table PackedRawNatGrowth.Block :=
(.branch 461
 (.branch 455
 (.branch 452
 (.branch 451
 (.leaf ⟨(certNat% 0),(certNat% 1)⟩)
 (.leaf ⟨(certNat% 2),(certNat% 3)⟩))
 (.branch 453
 (.leaf ⟨(certNat% 4),(certNat% 5)⟩)
 (.branch 454
 (.leaf ⟨(certNat% 6),(certNat% 7)⟩)
 (.leaf ⟨(certNat% 8),(certNat% 9)⟩))))
 (.branch 458
 (.branch 456
 (.leaf ⟨(certNat% 10),(certNat% 11)⟩)
 (.branch 457
 (.leaf ⟨(certNat% 12),(certNat% 13)⟩)
 (.leaf ⟨(certNat% 14),(certNat% 15)⟩)))
 (.branch 459
 (.leaf ⟨(certNat% 16),(certNat% 17)⟩)
 (.branch 460
 (.leaf ⟨(certNat% 18),(certNat% 19)⟩)
 (.leaf ⟨(certNat% 20),(certNat% 21)⟩)))))
 (.branch 466
 (.branch 463
 (.branch 462
 (.leaf ⟨(certNat% 22),(certNat% 23)⟩)
 (.leaf ⟨(certNat% 24),(certNat% 25)⟩))
 (.branch 464
 (.leaf ⟨(certNat% 26),(certNat% 27)⟩)
 (.branch 465
 (.leaf ⟨(certNat% 28),(certNat% 29)⟩)
 (.leaf ⟨(certNat% 30),(certNat% 31)⟩))))
 (.branch 469
 (.branch 467
 (.leaf ⟨(certNat% 32),(certNat% 33)⟩)
 (.branch 468
 (.leaf ⟨(certNat% 34),(certNat% 35)⟩)
 (.leaf ⟨(certNat% 36),(certNat% 37)⟩)))
 (.branch 470
 (.leaf ⟨(certNat% 38),(certNat% 39)⟩)
 (.branch 471
 (.leaf ⟨(certNat% 40),(certNat% 41)⟩)
 (.leaf ⟨(certNat% 42),(certNat% 43)⟩))))))
def nodeCounters009 : Table Nat :=
(.branch 461
 (.branch 455
 (.branch 452
 (.branch 451
 (.leaf (certNat% 44))
 (.leaf (certNat% 45)))
 (.branch 453
 (.leaf (certNat% 46))
 (.branch 454
 (.leaf (certNat% 47))
 (.leaf (certNat% 48)))))
 (.branch 458
 (.branch 456
 (.leaf (certNat% 49))
 (.branch 457
 (.leaf (certNat% 50))
 (.leaf (certNat% 51))))
 (.branch 459
 (.leaf (certNat% 52))
 (.branch 460
 (.leaf (certNat% 53))
 (.leaf (certNat% 54))))))
 (.branch 466
 (.branch 463
 (.branch 462
 (.leaf (certNat% 55))
 (.leaf (certNat% 56)))
 (.branch 464
 (.leaf (certNat% 57))
 (.branch 465
 (.leaf (certNat% 58))
 (.leaf (certNat% 59)))))
 (.branch 469
 (.branch 467
 (.leaf (certNat% 60))
 (.branch 468
 (.leaf (certNat% 61))
 (.leaf (certNat% 62))))
 (.branch 470
 (.leaf (certNat% 63))
 (.branch 471
 (.leaf (certNat% 64))
 (.leaf (certNat% 65)))))))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
