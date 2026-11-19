module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public meta import CertificateNumbers
import HexNatLiteral
public import RootedSixExtra05GrowthCacheData
public import RootedSixExtra05FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0860
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2170
abbrev nodeCount : Nat := 2729
abbrev leafCount : Nat := 17
cert_widths_3 12 12 9 5
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨((certNat% 0)),(certNat% 1)⟩)
 (.leaf ⟨((certNat% 2)),(certNat% 3)⟩))
 (.branch 3
 (.leaf ⟨((certNat% 4)),(certNat% 5)⟩)
 (.branch 4
 (.leaf ⟨((certNat% 6)),(certNat% 7)⟩)
 (.leaf ⟨((certNat% 8)),(certNat% 9)⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨((certNat% 10)),(certNat% 11)⟩)
 (.branch 7
 (.leaf ⟨((certNat% 12)),(certNat% 13)⟩)
 (.leaf ⟨((certNat% 14)),(certNat% 15)⟩)))
 (.branch 9
 (.leaf ⟨((certNat% 16)),(certNat% 17)⟩)
 (.branch 10
 (.leaf ⟨((certNat% 18)),(certNat% 19)⟩)
 (.leaf ⟨((certNat% 20)),(certNat% 21)⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨((certNat% 22)),(certNat% 23)⟩)
 (.leaf ⟨((certNat% 24)),(certNat% 25)⟩))
 (.branch 14
 (.leaf ⟨((certNat% 26)),(certNat% 27)⟩)
 (.branch 15
 (.leaf ⟨((certNat% 28)),(certNat% 29)⟩)
 (.leaf ⟨((certNat% 30)),(certNat% 31)⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨((certNat% 32)),(certNat% 33)⟩)
 (.branch 18
 (.leaf ⟨((certNat% 34)),(certNat% 35)⟩)
 (.leaf ⟨((certNat% 36)),(certNat% 37)⟩)))
 (.branch 20
 (.leaf ⟨((certNat% 38)),(certNat% 39)⟩)
 (.branch 21
 (.leaf ⟨((certNat% 40)),(certNat% 41)⟩)
 (.leaf ⟨(certNat% 42),(certNat% 43)⟩))))))
def counterTable : Table Nat :=
(.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (certNat% 44))
 (.leaf (certNat% 45)))
 (.branch 3
 (.leaf (certNat% 46))
 (.branch 4
 (.leaf (certNat% 47))
 (.leaf (certNat% 48)))))
 (.branch 8
 (.branch 6
 (.leaf (certNat% 49))
 (.branch 7
 (.leaf (certNat% 50))
 (.leaf (certNat% 51))))
 (.branch 9
 (.leaf (certNat% 52))
 (.branch 10
 (.leaf (certNat% 53))
 (.leaf (certNat% 54))))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf (certNat% 55))
 (.leaf (certNat% 56)))
 (.branch 14
 (.leaf (certNat% 57))
 (.branch 15
 (.leaf (certNat% 58))
 (.leaf (certNat% 59)))))
 (.branch 19
 (.branch 17
 (.leaf (certNat% 60))
 (.branch 18
 (.leaf (certNat% 61))
 (.leaf (certNat% 62))))
 (.branch 20
 (.leaf (certNat% 63))
 (.branch 21
 (.leaf (certNat% 64))
 (.leaf (certNat% 65)))))))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf [0,5,17,116,161,251,379,448,608,630,815,826])
 (.leaf [0,17,152,160,168,251,408,448,579,779,1004]))
 (.branch 3
 (.leaf [0,22,38,152,162,251,448,815])
 (.leaf [0,20,77,129,162,249,446,598,820,986])))
 (.branch 6
 (.branch 5
 (.leaf [0,25,33,105,161,237,248,362,445,631,756])
 (.leaf [0,5,44,137,160,248,254,448,558,716,776,1140]))
 (.branch 7
 (.leaf [0,1,87,161,221,242,248,362,445,538,756])
 (.leaf [0,5,12,131,160,248,423,448,532,558,688,776]))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf [0,5,87,159,161,222,250,339,446,473,710,790])
 (.leaf [0,8,14,137,162,250,448,599,708,812]))
 (.branch 11
 (.leaf [0,25,27,155,162,249,281,339,446,507,536,792])
 (.leaf [0,23,87,128,163,188,250,381,447,599,816])))
 (.branch 14
 (.branch 13
 (.leaf [0,23,39,104,163,192,250,402,447,599,816])
 (.leaf [0,8,140,162,251,402,448,599,815]))
 (.branch 15
 (.leaf [0,1,161,170,251,303,403,448,500,600,803])
 (.branch 16
 (.leaf [0,23,39,104,160,251,326,361,448,523,558,779])
 (.leaf [0,4,56,163,251,448]))))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 2 0 0 0 0 0 0 5 5
cert_nodeTest_4 288 05
cert_nodeTest_sound_3 288 05
cert_leafTest_5 05
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0860
