module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public meta import CertificateNumbers
import HexNatLiteral
public import RootedSixBase03GrowthCacheData
public import RootedSixBase03FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0712
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 5238
abbrev nodeCount : Nat := 2298
abbrev leafCount : Nat := 8
cert_widths_3 13 12 7 3
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 9
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
 (.branch 8
 (.leaf ⟨((certNat% 14)),(certNat% 15)⟩)
 (.leaf ⟨((certNat% 16)),(certNat% 17)⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨((certNat% 18)),(certNat% 19)⟩)
 (.leaf ⟨((certNat% 20)),(certNat% 21)⟩))
 (.branch 12
 (.leaf ⟨((certNat% 22)),(certNat% 23)⟩)
 (.leaf ⟨((certNat% 24)),(certNat% 25)⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨((certNat% 26)),(certNat% 27)⟩)
 (.leaf ⟨((certNat% 28)),(certNat% 29)⟩))
 (.branch 16
 (.leaf ⟨((certNat% 30)),(certNat% 31)⟩)
 (.branch 17
 (.leaf ⟨((certNat% 32)),(certNat% 33)⟩)
 (.leaf ⟨((certNat% 34)),(certNat% 35)⟩))))))
def counterTable : Table Nat :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (certNat% 36))
 (.leaf (certNat% 37)))
 (.branch 3
 (.leaf (certNat% 38))
 (.leaf (certNat% 39))))
 (.branch 6
 (.branch 5
 (.leaf (certNat% 40))
 (.leaf (certNat% 41)))
 (.branch 7
 (.leaf (certNat% 42))
 (.branch 8
 (.leaf (certNat% 43))
 (.leaf (certNat% 44))))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf (certNat% 45))
 (.leaf (certNat% 46)))
 (.branch 12
 (.leaf (certNat% 47))
 (.leaf (certNat% 48))))
 (.branch 15
 (.branch 14
 (.leaf (certNat% 49))
 (.leaf (certNat% 50)))
 (.branch 16
 (.leaf (certNat% 51))
 (.branch 17
 (.leaf (certNat% 52))
 (.leaf (certNat% 53)))))))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf [0,1,258,317,347,370,542,711,1012,1289,1608])
 (.leaf [0,1,191,345,350,611,670,724,1001,1229,1609]))
 (.branch 3
 (.leaf [0,1,216,346,396,495,569,745,1020,1114,1268])
 (.leaf [0,15,129,191,345,602,712,1013,1213,1229,1612])))
 (.branch 6
 (.branch 5
 (.leaf [0,31,140,250,346,411,723,1003,1145,1285,1379])
 (.leaf [0,77,116,237,345,557,759,943,1033,1113,1279]))
 (.branch 7
 (.leaf [0,111,164,248,347,543,711,943,1015,1273,1381])
 (.leaf [0,140,236,347,556,736,949,988,1277,1613]))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 1 0 0 0 0 0 0 3 6
cert_nodeTest_5 96 03
cert_nodeTest_sound_4 96 03
cert_leafTest_4 03
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0712
