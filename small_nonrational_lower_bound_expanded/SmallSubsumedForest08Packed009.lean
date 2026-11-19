module
prelude
public meta import CertificateNumbers
public import PackedRawNatGrowth

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest08
open Papers.RationalityTen ConcreteGrowth

def nodeBlocks009 : Table PackedRawNatGrowth.Block :=
(.branch 466
 (.branch 458
 (.branch 454
 (.branch 452
 (.branch 451
 (.leaf ⟨(certNat% 0),(certNat% 1)⟩)
 (.leaf ⟨(certNat% 2),(certNat% 3)⟩))
 (.branch 453
 (.leaf ⟨(certNat% 4),(certNat% 5)⟩)
 (.leaf ⟨(certNat% 6),(certNat% 7)⟩)))
 (.branch 456
 (.branch 455
 (.leaf ⟨(certNat% 8),(certNat% 9)⟩)
 (.leaf ⟨(certNat% 10),(certNat% 11)⟩))
 (.branch 457
 (.leaf ⟨(certNat% 12),(certNat% 13)⟩)
 (.leaf ⟨(certNat% 14),(certNat% 15)⟩))))
 (.branch 462
 (.branch 460
 (.branch 459
 (.leaf ⟨(certNat% 16),(certNat% 17)⟩)
 (.leaf ⟨(certNat% 18),(certNat% 19)⟩))
 (.branch 461
 (.leaf ⟨(certNat% 20),(certNat% 21)⟩)
 (.leaf ⟨(certNat% 22),(certNat% 23)⟩)))
 (.branch 464
 (.branch 463
 (.leaf ⟨(certNat% 24),(certNat% 25)⟩)
 (.leaf ⟨(certNat% 26),(certNat% 27)⟩))
 (.branch 465
 (.leaf ⟨(certNat% 28),(certNat% 29)⟩)
 (.leaf ⟨(certNat% 30),(certNat% 31)⟩)))))
 (.branch 474
 (.branch 470
 (.branch 468
 (.branch 467
 (.leaf ⟨(certNat% 32),(certNat% 33)⟩)
 (.leaf ⟨(certNat% 34),(certNat% 35)⟩))
 (.branch 469
 (.leaf ⟨(certNat% 36),(certNat% 37)⟩)
 (.leaf ⟨(certNat% 38),(certNat% 39)⟩)))
 (.branch 472
 (.branch 471
 (.leaf ⟨(certNat% 40),(certNat% 41)⟩)
 (.leaf ⟨(certNat% 42),(certNat% 43)⟩))
 (.branch 473
 (.leaf ⟨(certNat% 44),(certNat% 45)⟩)
 (.leaf ⟨(certNat% 46),(certNat% 47)⟩))))
 (.branch 478
 (.branch 476
 (.branch 475
 (.leaf ⟨(certNat% 48),(certNat% 49)⟩)
 (.leaf ⟨(certNat% 50),(certNat% 51)⟩))
 (.branch 477
 (.leaf ⟨(certNat% 52),(certNat% 53)⟩)
 (.leaf ⟨(certNat% 54),(certNat% 55)⟩)))
 (.branch 480
 (.branch 479
 (.leaf ⟨(certNat% 56),(certNat% 57)⟩)
 (.leaf ⟨(certNat% 58),(certNat% 59)⟩))
 (.branch 481
 (.leaf ⟨(certNat% 60),(certNat% 61)⟩)
 (.branch 482
 (.leaf ⟨(certNat% 62),(certNat% 63)⟩)
 (.leaf ⟨(certNat% 64),(certNat% 65)⟩)))))))
def nodeCounters009 : Table Nat :=
(.branch 466
 (.branch 458
 (.branch 454
 (.branch 452
 (.branch 451
 (.leaf (certNat% 66))
 (.leaf (certNat% 67)))
 (.branch 453
 (.leaf (certNat% 68))
 (.leaf (certNat% 69))))
 (.branch 456
 (.branch 455
 (.leaf (certNat% 70))
 (.leaf (certNat% 71)))
 (.branch 457
 (.leaf (certNat% 72))
 (.leaf (certNat% 73)))))
 (.branch 462
 (.branch 460
 (.branch 459
 (.leaf (certNat% 74))
 (.leaf (certNat% 75)))
 (.branch 461
 (.leaf (certNat% 76))
 (.leaf (certNat% 77))))
 (.branch 464
 (.branch 463
 (.leaf (certNat% 78))
 (.leaf (certNat% 79)))
 (.branch 465
 (.leaf (certNat% 80))
 (.leaf (certNat% 81))))))
 (.branch 474
 (.branch 470
 (.branch 468
 (.branch 467
 (.leaf (certNat% 82))
 (.leaf (certNat% 83)))
 (.branch 469
 (.leaf (certNat% 84))
 (.leaf (certNat% 85))))
 (.branch 472
 (.branch 471
 (.leaf (certNat% 86))
 (.leaf (certNat% 87)))
 (.branch 473
 (.leaf (certNat% 88))
 (.leaf (certNat% 89)))))
 (.branch 478
 (.branch 476
 (.branch 475
 (.leaf (certNat% 90))
 (.leaf (certNat% 91)))
 (.branch 477
 (.leaf (certNat% 92))
 (.leaf (certNat% 93))))
 (.branch 480
 (.branch 479
 (.leaf (certNat% 94))
 (.leaf (certNat% 95)))
 (.branch 481
 (.leaf (certNat% 96))
 (.branch 482
 (.leaf (certNat% 97))
 (.leaf (certNat% 98))))))))

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest08
