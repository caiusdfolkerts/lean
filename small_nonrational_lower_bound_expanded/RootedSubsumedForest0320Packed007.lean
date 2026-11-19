module
prelude
public meta import CertificateNumbers
public import PackedRawNatGrowth

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0320
open Papers.RationalityTen ConcreteGrowth

def nodeBlocks007 : Table PackedRawNatGrowth.Block :=
(.branch 359
 (.branch 354
 (.branch 352
 (.branch 351
 (.leaf ⟨(certNat% 0),(certNat% 1)⟩)
 (.leaf ⟨(certNat% 2),(certNat% 3)⟩))
 (.branch 353
 (.leaf ⟨(certNat% 4),(certNat% 5)⟩)
 (.leaf ⟨(certNat% 6),(certNat% 7)⟩)))
 (.branch 356
 (.branch 355
 (.leaf ⟨(certNat% 8),(certNat% 9)⟩)
 (.leaf ⟨(certNat% 10),(certNat% 11)⟩))
 (.branch 357
 (.leaf ⟨(certNat% 12),(certNat% 13)⟩)
 (.branch 358
 (.leaf ⟨(certNat% 14),(certNat% 15)⟩)
 (.leaf ⟨(certNat% 16),(certNat% 17)⟩)))))
 (.branch 364
 (.branch 361
 (.branch 360
 (.leaf ⟨(certNat% 18),(certNat% 19)⟩)
 (.leaf ⟨(certNat% 20),(certNat% 21)⟩))
 (.branch 362
 (.leaf ⟨(certNat% 22),(certNat% 23)⟩)
 (.branch 363
 (.leaf ⟨(certNat% 24),(certNat% 25)⟩)
 (.leaf ⟨(certNat% 26),(certNat% 27)⟩))))
 (.branch 366
 (.branch 365
 (.leaf ⟨(certNat% 28),(certNat% 29)⟩)
 (.leaf ⟨(certNat% 30),(certNat% 31)⟩))
 (.branch 367
 (.leaf ⟨(certNat% 32),(certNat% 33)⟩)
 (.branch 368
 (.leaf ⟨(certNat% 34),(certNat% 35)⟩)
 (.leaf ⟨(certNat% 36),(certNat% 37)⟩))))))
def nodeCounters007 : Table Nat :=
(.branch 359
 (.branch 354
 (.branch 352
 (.branch 351
 (.leaf (certNat% 38))
 (.leaf (certNat% 39)))
 (.branch 353
 (.leaf (certNat% 40))
 (.leaf (certNat% 41))))
 (.branch 356
 (.branch 355
 (.leaf (certNat% 42))
 (.leaf (certNat% 43)))
 (.branch 357
 (.leaf (certNat% 44))
 (.branch 358
 (.leaf (certNat% 45))
 (.leaf (certNat% 46))))))
 (.branch 364
 (.branch 361
 (.branch 360
 (.leaf (certNat% 47))
 (.leaf (certNat% 48)))
 (.branch 362
 (.leaf (certNat% 49))
 (.branch 363
 (.leaf (certNat% 50))
 (.leaf (certNat% 51)))))
 (.branch 366
 (.branch 365
 (.leaf (certNat% 52))
 (.leaf (certNat% 53)))
 (.branch 367
 (.leaf (certNat% 54))
 (.branch 368
 (.leaf (certNat% 55))
 (.leaf (certNat% 56)))))))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0320
