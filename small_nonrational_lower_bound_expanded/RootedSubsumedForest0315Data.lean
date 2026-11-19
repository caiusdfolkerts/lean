module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public meta import CertificateNumbers
import HexNatLiteral
public import RootedSixBase02GrowthCacheData
public import RootedSixBase02FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0315
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 8084
abbrev nodeCount : Nat := 3170
abbrev leafCount : Nat := 10
cert_widths_3 13 12 6 4
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨((certNat% 0)),(certNat% 1)⟩)
 (.branch 2
 (.leaf ⟨((certNat% 2)),(certNat% 3)⟩)
 (.leaf ⟨((certNat% 4)),(certNat% 5)⟩)))
 (.branch 4
 (.leaf ⟨((certNat% 6)),(certNat% 7)⟩)
 (.branch 5
 (.leaf ⟨((certNat% 8)),(certNat% 9)⟩)
 (.leaf ⟨((certNat% 10)),(certNat% 11)⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨((certNat% 12)),(certNat% 13)⟩)
 (.branch 8
 (.leaf ⟨((certNat% 14)),(certNat% 15)⟩)
 (.leaf ⟨((certNat% 16)),(certNat% 17)⟩)))
 (.branch 10
 (.leaf ⟨((certNat% 18)),(certNat% 19)⟩)
 (.branch 11
 (.leaf ⟨((certNat% 20)),(certNat% 21)⟩)
 (.leaf ⟨((certNat% 22)),(certNat% 23)⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨((certNat% 24)),(certNat% 25)⟩)
 (.branch 14
 (.leaf ⟨((certNat% 26)),(certNat% 27)⟩)
 (.leaf ⟨((certNat% 28)),(certNat% 29)⟩)))
 (.branch 16
 (.leaf ⟨((certNat% 30)),(certNat% 31)⟩)
 (.branch 17
 (.leaf ⟨((certNat% 32)),(certNat% 33)⟩)
 (.leaf ⟨((certNat% 34)),(certNat% 35)⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨((certNat% 36)),(certNat% 37)⟩)
 (.branch 20
 (.leaf ⟨((certNat% 38)),(certNat% 39)⟩)
 (.leaf ⟨((certNat% 40)),(certNat% 41)⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨((certNat% 42)),(certNat% 43)⟩)
 (.leaf ⟨((certNat% 44)),(certNat% 45)⟩))
 (.branch 24
 (.leaf ⟨((certNat% 46)),(certNat% 47)⟩)
 (.leaf ⟨((certNat% 48)),(certNat% 49)⟩))))))
def counterTable : Table Nat :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (certNat% 50))
 (.branch 2
 (.leaf (certNat% 51))
 (.leaf (certNat% 52))))
 (.branch 4
 (.leaf (certNat% 53))
 (.branch 5
 (.leaf (certNat% 54))
 (.leaf (certNat% 55)))))
 (.branch 9
 (.branch 7
 (.leaf (certNat% 56))
 (.branch 8
 (.leaf (certNat% 57))
 (.leaf (certNat% 58))))
 (.branch 10
 (.leaf (certNat% 59))
 (.branch 11
 (.leaf (certNat% 60))
 (.leaf (certNat% 61))))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf (certNat% 62))
 (.branch 14
 (.leaf (certNat% 63))
 (.leaf (certNat% 64))))
 (.branch 16
 (.leaf (certNat% 65))
 (.branch 17
 (.leaf (certNat% 66))
 (.leaf (certNat% 67)))))
 (.branch 21
 (.branch 19
 (.leaf (certNat% 68))
 (.branch 20
 (.leaf (certNat% 69))
 (.leaf (certNat% 70))))
 (.branch 23
 (.branch 22
 (.leaf (certNat% 71))
 (.leaf (certNat% 72)))
 (.branch 24
 (.leaf (certNat% 73))
 (.leaf (certNat% 74)))))))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf [0,6,154,333,482,530,660,854,1051])
 (.leaf [0,56,138,243,528,669,959,1045,7900]))
 (.branch 3
 (.leaf [0,53,163,218,530,617,822,962,1038,1379,7893])
 (.branch 4
 (.leaf [0,6,141,332,483,672,961,1053,8052])
 (.leaf [0,27,108,214,330,462,550,684,938,1017,8056]))))
 (.branch 7
 (.branch 6
 (.leaf [0,21,109,187,331,551,684,959,1041,1235,8056])
 (.leaf [0,41,162,230,529,630,861,960,995,1273,7897]))
 (.branch 8
 (.leaf [0,31,158,234,527,633,861,882,1009,1141,7899])
 (.branch 9
 (.leaf [0,126,224,417,527,645,928,1021,1144,7894])
 (.leaf [0,53,171,186,530,622,841,1060,1165,7902])))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 1 1 0 0 0 0 0 5 4
cert_nodeTest_5 48 02
cert_nodeTest_sound_4 48 02
cert_leafTest_4 02
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0315
