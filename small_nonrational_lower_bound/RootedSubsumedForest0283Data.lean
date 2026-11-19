module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0283
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 8084
abbrev nodeCount : Nat := 4025
abbrev leafCount : Nat := 7
cert_widths_3 13 12 6 3
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨((certNat% 0)),(certNat% 1)⟩)
 (.leaf ⟨((certNat% 2)),(certNat% 3)⟩))
 (.branch 3
 (.leaf ⟨((certNat% 4)),(certNat% 5)⟩)
 (.leaf ⟨((certNat% 6)),(certNat% 7)⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨((certNat% 8)),(certNat% 9)⟩)
 (.leaf ⟨((certNat% 10)),(certNat% 11)⟩))
 (.branch 7
 (.leaf ⟨((certNat% 12)),(certNat% 13)⟩)
 (.leaf ⟨((certNat% 14)),(certNat% 15)⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨((certNat% 16)),(certNat% 17)⟩)
 (.leaf ⟨((certNat% 18)),(certNat% 19)⟩))
 (.branch 11
 (.leaf ⟨((certNat% 20)),(certNat% 21)⟩)
 (.leaf ⟨((certNat% 22)),(certNat% 23)⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨((certNat% 24)),(certNat% 25)⟩)
 (.leaf ⟨((certNat% 26)),(certNat% 27)⟩))
 (.branch 15
 (.leaf ⟨((certNat% 28)),(certNat% 29)⟩)
 (.leaf ⟨((certNat% 30)),(certNat% 31)⟩)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ⟨((certNat% 32)),(certNat% 33)⟩)
 (.leaf ⟨((certNat% 34)),(certNat% 35)⟩))
 (.branch 19
 (.leaf ⟨((certNat% 36)),(certNat% 37)⟩)
 (.leaf ⟨((certNat% 38)),(certNat% 39)⟩)))
 (.branch 22
 (.branch 21
 (.leaf ⟨((certNat% 40)),(certNat% 41)⟩)
 (.leaf ⟨((certNat% 42)),(certNat% 43)⟩))
 (.branch 23
 (.leaf ⟨((certNat% 44)),(certNat% 45)⟩)
 (.leaf ⟨((certNat% 46)),(certNat% 47)⟩))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ⟨((certNat% 48)),(certNat% 49)⟩)
 (.leaf ⟨((certNat% 50)),(certNat% 51)⟩))
 (.branch 27
 (.leaf ⟨((certNat% 52)),(certNat% 53)⟩)
 (.leaf ⟨((certNat% 54)),(certNat% 55)⟩)))
 (.branch 30
 (.branch 29
 (.leaf ⟨((certNat% 56)),(certNat% 57)⟩)
 (.leaf ⟨((certNat% 58)),(certNat% 59)⟩))
 (.branch 31
 (.leaf ⟨((certNat% 60)),(certNat% 61)⟩)
 (.leaf ⟨(certNat% 62),(certNat% 63)⟩))))))
def counterTable : Table Nat :=
(.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (certNat% 64))
 (.leaf (certNat% 65)))
 (.branch 3
 (.leaf (certNat% 66))
 (.leaf (certNat% 67))))
 (.branch 6
 (.branch 5
 (.leaf (certNat% 68))
 (.leaf (certNat% 69)))
 (.branch 7
 (.leaf (certNat% 70))
 (.leaf (certNat% 71)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (certNat% 72))
 (.leaf (certNat% 73)))
 (.branch 11
 (.leaf (certNat% 74))
 (.leaf (certNat% 75))))
 (.branch 14
 (.branch 13
 (.leaf (certNat% 76))
 (.leaf (certNat% 77)))
 (.branch 15
 (.leaf (certNat% 78))
 (.leaf (certNat% 79))))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf (certNat% 80))
 (.leaf (certNat% 81)))
 (.branch 19
 (.leaf (certNat% 82))
 (.leaf (certNat% 83))))
 (.branch 22
 (.branch 21
 (.leaf (certNat% 84))
 (.leaf (certNat% 85)))
 (.branch 23
 (.leaf (certNat% 86))
 (.leaf (certNat% 87)))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf (certNat% 88))
 (.leaf (certNat% 89)))
 (.branch 27
 (.leaf (certNat% 90))
 (.leaf (certNat% 91))))
 (.branch 30
 (.branch 29
 (.leaf (certNat% 92))
 (.leaf (certNat% 93)))
 (.branch 31
 (.leaf (certNat% 94))
 (.leaf (certNat% 95)))))))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 3
 (.branch 1
 (.leaf [0,6,154,333,482,530,660,854,1051])
 (.branch 2
 (.leaf [0,6,141,332,483,672,961,1053,8052])
 (.leaf [0,21,233,330,683,937,1005,1236,5605,8057])))
 (.branch 5
 (.branch 4
 (.leaf [0,41,163,218,530,646,860,962,7236,7893])
 (.leaf [0,5,133,529,591,631,960,1029,5772,7897]))
 (.branch 6
 (.leaf [0,93,126,242,657,863,937,1033,7126,7901])
 (.leaf [0,93,170,198,622,863,998,1118,7139,7903]))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 1 1 0 0 1 0 0 4 3
cert_nodeTest_5 48 02
cert_nodeTest_sound_4 48 02
cert_leafTest_4 02
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0283
