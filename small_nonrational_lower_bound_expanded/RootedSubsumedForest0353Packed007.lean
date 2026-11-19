module
prelude
public meta import CertificateNumbers
public import PackedRawNatGrowth

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0353
open Papers.RationalityTen ConcreteGrowth

def nodeBlocks007 : Table PackedRawNatGrowth.Block :=
(.branch 360
 (.branch 355
 (.branch 352
 (.branch 351
 (.leaf ⟨(certNat% 0),(certNat% 1)⟩)
 (.leaf ⟨(certNat% 2),(certNat% 3)⟩))
 (.branch 353
 (.leaf ⟨(certNat% 4),(certNat% 5)⟩)
 (.branch 354
 (.leaf ⟨(certNat% 6),(certNat% 7)⟩)
 (.leaf ⟨(certNat% 8),(certNat% 9)⟩))))
 (.branch 357
 (.branch 356
 (.leaf ⟨(certNat% 10),(certNat% 11)⟩)
 (.leaf ⟨(certNat% 12),(certNat% 13)⟩))
 (.branch 358
 (.leaf ⟨(certNat% 14),(certNat% 15)⟩)
 (.branch 359
 (.leaf ⟨(certNat% 16),(certNat% 17)⟩)
 (.leaf ⟨(certNat% 18),(certNat% 19)⟩)))))
 (.branch 365
 (.branch 362
 (.branch 361
 (.leaf ⟨(certNat% 20),(certNat% 21)⟩)
 (.leaf ⟨(certNat% 22),(certNat% 23)⟩))
 (.branch 363
 (.leaf ⟨(certNat% 24),(certNat% 25)⟩)
 (.branch 364
 (.leaf ⟨(certNat% 26),(certNat% 27)⟩)
 (.leaf ⟨(certNat% 28),(certNat% 29)⟩))))
 (.branch 367
 (.branch 366
 (.leaf ⟨(certNat% 30),(certNat% 31)⟩)
 (.leaf ⟨(certNat% 32),(certNat% 33)⟩))
 (.branch 368
 (.leaf ⟨(certNat% 34),(certNat% 35)⟩)
 (.branch 369
 (.leaf ⟨(certNat% 36),(certNat% 37)⟩)
 (.leaf ⟨(certNat% 38),(certNat% 39)⟩))))))
def nodeCounters007 : Table Nat :=
(.branch 360
 (.branch 355
 (.branch 352
 (.branch 351
 (.leaf (certNat% 40))
 (.leaf (certNat% 41)))
 (.branch 353
 (.leaf (certNat% 42))
 (.branch 354
 (.leaf (certNat% 43))
 (.leaf (certNat% 44)))))
 (.branch 357
 (.branch 356
 (.leaf (certNat% 45))
 (.leaf (certNat% 46)))
 (.branch 358
 (.leaf (certNat% 47))
 (.branch 359
 (.leaf (certNat% 48))
 (.leaf (certNat% 49))))))
 (.branch 365
 (.branch 362
 (.branch 361
 (.leaf (certNat% 50))
 (.leaf (certNat% 51)))
 (.branch 363
 (.leaf (certNat% 52))
 (.branch 364
 (.leaf (certNat% 53))
 (.leaf (certNat% 54)))))
 (.branch 367
 (.branch 366
 (.leaf (certNat% 55))
 (.leaf (certNat% 56)))
 (.branch 368
 (.leaf (certNat% 57))
 (.branch 369
 (.leaf (certNat% 58))
 (.leaf (certNat% 59)))))))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0353
