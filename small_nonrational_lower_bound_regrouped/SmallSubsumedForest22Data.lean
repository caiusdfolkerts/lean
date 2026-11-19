module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public meta import CertificateNumbers
public import RootedSmallCacheData
public import RootedSmallGeneratorWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest22
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 3436
abbrev nodeCount : Nat := 1989
abbrev leafCount : Nat := 6
cert_widths_4 11 3
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(certNat% 0),(certNat% 1)⟩)
 (.leaf ⟨(certNat% 2),(certNat% 3)⟩))
 (.branch 3
 (.leaf ⟨(certNat% 4),(certNat% 5)⟩)
 (.leaf ⟨(certNat% 6),(certNat% 7)⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(certNat% 8),(certNat% 9)⟩)
 (.leaf ⟨(certNat% 10),(certNat% 11)⟩))
 (.branch 7
 (.leaf ⟨(certNat% 12),(certNat% 13)⟩)
 (.leaf ⟨(certNat% 14),(certNat% 15)⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(certNat% 16),(certNat% 17)⟩)
 (.leaf ⟨(certNat% 18),(certNat% 19)⟩))
 (.branch 11
 (.leaf ⟨(certNat% 20),(certNat% 21)⟩)
 (.leaf ⟨(certNat% 22),(certNat% 23)⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(certNat% 24),(certNat% 25)⟩)
 (.leaf ⟨(certNat% 26),(certNat% 27)⟩))
 (.branch 15
 (.leaf ⟨(certNat% 28),(certNat% 29)⟩)
 (.leaf ⟨(certNat% 30),(certNat% 31)⟩)))))
def counterTable : Table Nat :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (certNat% 32))
 (.leaf (certNat% 33)))
 (.branch 3
 (.leaf (certNat% 34))
 (.leaf (certNat% 35))))
 (.branch 6
 (.branch 5
 (.leaf (certNat% 36))
 (.leaf (certNat% 37)))
 (.branch 7
 (.leaf (certNat% 38))
 (.leaf (certNat% 39)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (certNat% 40))
 (.leaf (certNat% 41)))
 (.branch 11
 (.leaf (certNat% 42))
 (.leaf (certNat% 43))))
 (.branch 14
 (.branch 13
 (.leaf (certNat% 44))
 (.leaf (certNat% 45)))
 (.branch 15
 (.leaf (certNat% 46))
 (.leaf (certNat% 47))))))
cert_codes_4
cert_counters_4
cert_rawNodes_4
def leafTable : Table (List Nat) :=
(.branch 3
 (.branch 1
 (.leaf [0,192,360,464,704,788,1212,1358,1699,1783,2207,2353])
 (.branch 2
 (.leaf [0,228,336,443,728,812,982,1442,1723,1807,1977,2437])
 (.leaf [0,240,312,464,740,824,1422,1581,1735,1819,2417,2576])))
 (.branch 4
 (.leaf [0,180,312,704,841,1075,1532,1699,1857,2485,2527])
 (.branch 5
 (.leaf [0,180,312,704,848,1510,1619,1699,1843,2557,2582])
 (.leaf [0,228,360,728,860,1607,1723,1855,2602]))))
def rawLeaves := leafTable.get

cert_leaves_4
cert_quota_5 0 8 4
cert_nodeTest_6
cert_nodeTest_sound_5
cert_leafTest_6
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest22
