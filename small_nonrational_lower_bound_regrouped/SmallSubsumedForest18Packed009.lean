module
prelude
public meta import CertificateNumbers
public import PackedRawNatGrowth

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
open Papers.RationalityTen ConcreteGrowth

def nodeBlocks009 : Table PackedRawNatGrowth.Block :=
(.branch 470
 (.branch 460
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
 (.branch 457
 (.branch 456
 (.leaf ⟨(certNat% 10),(certNat% 11)⟩)
 (.leaf ⟨(certNat% 12),(certNat% 13)⟩))
 (.branch 458
 (.leaf ⟨(certNat% 14),(certNat% 15)⟩)
 (.branch 459
 (.leaf ⟨(certNat% 16),(certNat% 17)⟩)
 (.leaf ⟨(certNat% 18),(certNat% 19)⟩)))))
 (.branch 465
 (.branch 462
 (.branch 461
 (.leaf ⟨(certNat% 20),(certNat% 21)⟩)
 (.leaf ⟨(certNat% 22),(certNat% 23)⟩))
 (.branch 463
 (.leaf ⟨(certNat% 24),(certNat% 25)⟩)
 (.branch 464
 (.leaf ⟨(certNat% 26),(certNat% 27)⟩)
 (.leaf ⟨(certNat% 28),(certNat% 29)⟩))))
 (.branch 467
 (.branch 466
 (.leaf ⟨(certNat% 30),(certNat% 31)⟩)
 (.leaf ⟨(certNat% 32),(certNat% 33)⟩))
 (.branch 468
 (.leaf ⟨(certNat% 34),(certNat% 35)⟩)
 (.branch 469
 (.leaf ⟨(certNat% 36),(certNat% 37)⟩)
 (.leaf ⟨(certNat% 38),(certNat% 39)⟩))))))
 (.branch 480
 (.branch 475
 (.branch 472
 (.branch 471
 (.leaf ⟨(certNat% 40),(certNat% 41)⟩)
 (.leaf ⟨(certNat% 42),(certNat% 43)⟩))
 (.branch 473
 (.leaf ⟨(certNat% 44),(certNat% 45)⟩)
 (.branch 474
 (.leaf ⟨(certNat% 46),(certNat% 47)⟩)
 (.leaf ⟨(certNat% 48),(certNat% 49)⟩))))
 (.branch 477
 (.branch 476
 (.leaf ⟨(certNat% 50),(certNat% 51)⟩)
 (.leaf ⟨(certNat% 52),(certNat% 53)⟩))
 (.branch 478
 (.leaf ⟨(certNat% 54),(certNat% 55)⟩)
 (.branch 479
 (.leaf ⟨(certNat% 56),(certNat% 57)⟩)
 (.leaf ⟨(certNat% 58),(certNat% 59)⟩)))))
 (.branch 485
 (.branch 482
 (.branch 481
 (.leaf ⟨(certNat% 60),(certNat% 61)⟩)
 (.leaf ⟨(certNat% 62),(certNat% 63)⟩))
 (.branch 483
 (.leaf ⟨(certNat% 64),(certNat% 65)⟩)
 (.branch 484
 (.leaf ⟨(certNat% 66),(certNat% 67)⟩)
 (.leaf ⟨(certNat% 68),(certNat% 69)⟩))))
 (.branch 488
 (.branch 486
 (.leaf ⟨(certNat% 70),(certNat% 71)⟩)
 (.branch 487
 (.leaf ⟨(certNat% 72),(certNat% 73)⟩)
 (.leaf ⟨(certNat% 74),(certNat% 75)⟩)))
 (.branch 489
 (.leaf ⟨(certNat% 76),(certNat% 77)⟩)
 (.branch 490
 (.leaf ⟨(certNat% 78),(certNat% 79)⟩)
 (.leaf ⟨(certNat% 80),(certNat% 81)⟩)))))))
def nodeCounters009 : Table Nat :=
(.branch 470
 (.branch 460
 (.branch 455
 (.branch 452
 (.branch 451
 (.leaf (certNat% 82))
 (.leaf (certNat% 83)))
 (.branch 453
 (.leaf (certNat% 84))
 (.branch 454
 (.leaf (certNat% 85))
 (.leaf (certNat% 86)))))
 (.branch 457
 (.branch 456
 (.leaf (certNat% 87))
 (.leaf (certNat% 88)))
 (.branch 458
 (.leaf (certNat% 89))
 (.branch 459
 (.leaf (certNat% 90))
 (.leaf (certNat% 91))))))
 (.branch 465
 (.branch 462
 (.branch 461
 (.leaf (certNat% 92))
 (.leaf (certNat% 93)))
 (.branch 463
 (.leaf (certNat% 94))
 (.branch 464
 (.leaf (certNat% 95))
 (.leaf (certNat% 96)))))
 (.branch 467
 (.branch 466
 (.leaf (certNat% 97))
 (.leaf (certNat% 98)))
 (.branch 468
 (.leaf (certNat% 99))
 (.branch 469
 (.leaf (certNat% 100))
 (.leaf (certNat% 101)))))))
 (.branch 480
 (.branch 475
 (.branch 472
 (.branch 471
 (.leaf (certNat% 102))
 (.leaf (certNat% 103)))
 (.branch 473
 (.leaf (certNat% 104))
 (.branch 474
 (.leaf (certNat% 105))
 (.leaf (certNat% 106)))))
 (.branch 477
 (.branch 476
 (.leaf (certNat% 107))
 (.leaf (certNat% 108)))
 (.branch 478
 (.leaf (certNat% 109))
 (.branch 479
 (.leaf (certNat% 110))
 (.leaf (certNat% 111))))))
 (.branch 485
 (.branch 482
 (.branch 481
 (.leaf (certNat% 112))
 (.leaf (certNat% 113)))
 (.branch 483
 (.leaf (certNat% 114))
 (.branch 484
 (.leaf (certNat% 115))
 (.leaf (certNat% 116)))))
 (.branch 488
 (.branch 486
 (.leaf (certNat% 117))
 (.branch 487
 (.leaf (certNat% 118))
 (.leaf (certNat% 119))))
 (.branch 489
 (.leaf (certNat% 120))
 (.branch 490
 (.leaf (certNat% 121))
 (.leaf (certNat% 122))))))))

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
