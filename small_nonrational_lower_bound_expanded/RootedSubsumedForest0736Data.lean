module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public meta import CertificateNumbers
import HexNatLiteral
public import RootedSixBase04GrowthCacheData
public import RootedSixBase04FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0736
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2824
abbrev nodeCount : Nat := 3455
abbrev leafCount : Nat := 5
cert_widths_3 12 12 11 3
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 13
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
 (.branch 11
 (.branch 10
 (.leaf ⟨((certNat% 18)),(certNat% 19)⟩)
 (.leaf ⟨((certNat% 20)),(certNat% 21)⟩))
 (.branch 12
 (.leaf ⟨((certNat% 22)),(certNat% 23)⟩)
 (.leaf ⟨((certNat% 24)),(certNat% 25)⟩)))))
 (.branch 20
 (.branch 16
 (.branch 14
 (.leaf ⟨((certNat% 26)),(certNat% 27)⟩)
 (.branch 15
 (.leaf ⟨((certNat% 28)),(certNat% 29)⟩)
 (.leaf ⟨((certNat% 30)),(certNat% 31)⟩)))
 (.branch 18
 (.branch 17
 (.leaf ⟨((certNat% 32)),(certNat% 33)⟩)
 (.leaf ⟨((certNat% 34)),(certNat% 35)⟩))
 (.branch 19
 (.leaf ⟨((certNat% 36)),(certNat% 37)⟩)
 (.leaf ⟨((certNat% 38)),(certNat% 39)⟩))))
 (.branch 23
 (.branch 21
 (.leaf ⟨((certNat% 40)),(certNat% 41)⟩)
 (.branch 22
 (.leaf ⟨((certNat% 42)),(certNat% 43)⟩)
 (.leaf ⟨((certNat% 44)),(certNat% 45)⟩)))
 (.branch 25
 (.branch 24
 (.leaf ⟨((certNat% 46)),(certNat% 47)⟩)
 (.leaf ⟨((certNat% 48)),(certNat% 49)⟩))
 (.branch 26
 (.leaf ⟨((certNat% 50)),(certNat% 51)⟩)
 (.leaf ⟨((certNat% 52)),(certNat% 53)⟩))))))
def counterTable : Table Nat :=
(.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (certNat% 54))
 (.branch 2
 (.leaf (certNat% 55))
 (.leaf (certNat% 56))))
 (.branch 4
 (.leaf (certNat% 57))
 (.branch 5
 (.leaf (certNat% 58))
 (.leaf (certNat% 59)))))
 (.branch 9
 (.branch 7
 (.leaf (certNat% 60))
 (.branch 8
 (.leaf (certNat% 61))
 (.leaf (certNat% 62))))
 (.branch 11
 (.branch 10
 (.leaf (certNat% 63))
 (.leaf (certNat% 64)))
 (.branch 12
 (.leaf (certNat% 65))
 (.leaf (certNat% 66))))))
 (.branch 20
 (.branch 16
 (.branch 14
 (.leaf (certNat% 67))
 (.branch 15
 (.leaf (certNat% 68))
 (.leaf (certNat% 69))))
 (.branch 18
 (.branch 17
 (.leaf (certNat% 70))
 (.leaf (certNat% 71)))
 (.branch 19
 (.leaf (certNat% 72))
 (.leaf (certNat% 73)))))
 (.branch 23
 (.branch 21
 (.leaf (certNat% 74))
 (.branch 22
 (.leaf (certNat% 75))
 (.leaf (certNat% 76))))
 (.branch 25
 (.branch 24
 (.leaf (certNat% 77))
 (.leaf (certNat% 78)))
 (.branch 26
 (.leaf (certNat% 79))
 (.leaf (certNat% 80)))))))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 2
 (.branch 1
 (.leaf [0,1,6,297,371,516,800,990,1153,1261,1522,1821])
 (.leaf [0,1,26,249,290,391,709,804,949,1248,1504,1848]))
 (.branch 3
 (.leaf [0,1,26,244,321,389,737,794,981,1235,1514,1843])
 (.branch 4
 (.leaf [0,2,36,254,401,543,766,830,959,1247,1478,1851])
 (.leaf [0,1,41,206,377,571,751,782,984,1223,1525,1845]))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 2 0 0 0 0 0 0 4 5
cert_nodeTest_5 1152 04
cert_nodeTest_sound_4 1152 04
cert_leafTest_4 04
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0736
