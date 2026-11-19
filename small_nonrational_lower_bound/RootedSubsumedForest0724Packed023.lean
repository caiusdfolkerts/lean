module
prelude
public meta import CertificateNumbers
public import PackedRawNatGrowth

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth

def nodeBlocks023 : Table PackedRawNatGrowth.Block :=
(.branch 1156
 (.branch 1153
 (.branch 1151
 (.leaf ⟨(certNat% 0),(certNat% 1)⟩)
 (.branch 1152
 (.leaf ⟨(certNat% 2),(certNat% 3)⟩)
 (.leaf ⟨(certNat% 4),(certNat% 5)⟩)))
 (.branch 1154
 (.leaf ⟨(certNat% 6),(certNat% 7)⟩)
 (.branch 1155
 (.leaf ⟨(certNat% 8),(certNat% 9)⟩)
 (.leaf ⟨(certNat% 10),(certNat% 11)⟩))))
 (.branch 1159
 (.branch 1157
 (.leaf ⟨(certNat% 12),(certNat% 13)⟩)
 (.branch 1158
 (.leaf ⟨(certNat% 14),(certNat% 15)⟩)
 (.leaf ⟨(certNat% 16),(certNat% 17)⟩)))
 (.branch 1161
 (.branch 1160
 (.leaf ⟨(certNat% 18),(certNat% 19)⟩)
 (.leaf ⟨(certNat% 20),(certNat% 21)⟩))
 (.branch 1162
 (.leaf ⟨(certNat% 22),(certNat% 23)⟩)
 (.leaf ⟨(certNat% 24),(certNat% 25)⟩)))))
def nodeCounters023 : Table Nat :=
(.branch 1156
 (.branch 1153
 (.branch 1151
 (.leaf (certNat% 26))
 (.branch 1152
 (.leaf (certNat% 27))
 (.leaf (certNat% 28))))
 (.branch 1154
 (.leaf (certNat% 29))
 (.branch 1155
 (.leaf (certNat% 30))
 (.leaf (certNat% 31)))))
 (.branch 1159
 (.branch 1157
 (.leaf (certNat% 32))
 (.branch 1158
 (.leaf (certNat% 33))
 (.leaf (certNat% 34))))
 (.branch 1161
 (.branch 1160
 (.leaf (certNat% 35))
 (.leaf (certNat% 36)))
 (.branch 1162
 (.leaf (certNat% 37))
 (.leaf (certNat% 38))))))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
