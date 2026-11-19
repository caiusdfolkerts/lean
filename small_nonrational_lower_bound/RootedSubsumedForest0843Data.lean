module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0843
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2170
abbrev nodeCount : Nat := 1887
abbrev leafCount : Nat := 18
cert_widths_3 12 11 9 5
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨((certNat% 0)),(certNat% 1)⟩)
 (.branch 2
 (.leaf ⟨((certNat% 2)),(certNat% 3)⟩)
 (.leaf ⟨((certNat% 4)),(certNat% 5)⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨((certNat% 6)),(certNat% 7)⟩)
 (.leaf ⟨((certNat% 8)),(certNat% 9)⟩))
 (.branch 6
 (.leaf ⟨((certNat% 10)),(certNat% 11)⟩)
 (.leaf ⟨((certNat% 12)),(certNat% 13)⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨((certNat% 14)),(certNat% 15)⟩)
 (.leaf ⟨((certNat% 16)),(certNat% 17)⟩))
 (.branch 10
 (.leaf ⟨((certNat% 18)),(certNat% 19)⟩)
 (.leaf ⟨((certNat% 20)),(certNat% 21)⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨((certNat% 22)),(certNat% 23)⟩)
 (.leaf ⟨((certNat% 24)),(certNat% 25)⟩))
 (.branch 14
 (.leaf ⟨((certNat% 26)),(certNat% 27)⟩)
 (.leaf ⟨((certNat% 28)),(certNat% 29)⟩)))))
def counterTable : Table Nat :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf (certNat% 30))
 (.branch 2
 (.leaf (certNat% 31))
 (.leaf (certNat% 32))))
 (.branch 5
 (.branch 4
 (.leaf (certNat% 33))
 (.leaf (certNat% 34)))
 (.branch 6
 (.leaf (certNat% 35))
 (.leaf (certNat% 36)))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf (certNat% 37))
 (.leaf (certNat% 38)))
 (.branch 10
 (.leaf (certNat% 39))
 (.leaf (certNat% 40))))
 (.branch 13
 (.branch 12
 (.leaf (certNat% 41))
 (.leaf (certNat% 42)))
 (.branch 14
 (.leaf (certNat% 43))
 (.leaf (certNat% 44))))))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf [0,22,38,152,162,251,448,815])
 (.leaf [0,8,14,137,162,250,448,599,708,812]))
 (.branch 3
 (.leaf [0,8,140,162,251,402,448,599,815])
 (.leaf [0,18,33,89,160,310,446,671,752,965,1508])))
 (.branch 6
 (.branch 5
 (.leaf [0,17,18,157,161,167,448,603,820,826,1508])
 (.leaf [0,18,33,157,160,165,448,603,820,824,1508]))
 (.branch 7
 (.leaf [0,5,57,125,160,291,447,540,713,788,946,1496])
 (.branch 8
 (.leaf [0,22,154,163,250,817,1569])
 (.leaf [0,1,5,242,251,280,447,456,708,821,1413])))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf [0,1,87,221,251,274,447,450,708,821,1413])
 (.leaf [0,4,56,163,251,448]))
 (.branch 12
 (.leaf [0,2,8,249,415,446,612,804,1410])
 (.leaf [0,136,163,251,616,725,811,1558])))
 (.branch 15
 (.branch 14
 (.leaf [0,5,12,131,160,248,423,556,686,776,1099,1560])
 (.leaf [0,1,5,242,248,364,445,540,756,901,1413]))
 (.branch 16
 (.leaf [0,17,18,90,161,310,446,671,753,965,1508])
 (.branch 17
 (.leaf [0,88,161,249,506,562,650,751,1073,1569])
 (.leaf [0,1,87,221,248,358,445,534,756,901,1413]))))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 2 1 0 0 0 0 0 4 4
cert_nodeTest_4 288 05
cert_nodeTest_sound_3 288 05
cert_leafTest_5 05
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0843
