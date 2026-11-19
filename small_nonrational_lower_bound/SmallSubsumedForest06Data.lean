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
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest06
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 3436
abbrev nodeCount : Nat := 2147
abbrev leafCount : Nat := 7
cert_widths_4 12 3
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
 (.branch 16
 (.leaf ⟨(certNat% 30),(certNat% 31)⟩)
 (.leaf ⟨(certNat% 32),(certNat% 33)⟩))))))
def counterTable : Table Nat :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (certNat% 34))
 (.leaf (certNat% 35)))
 (.branch 3
 (.leaf (certNat% 36))
 (.leaf (certNat% 37))))
 (.branch 6
 (.branch 5
 (.leaf (certNat% 38))
 (.leaf (certNat% 39)))
 (.branch 7
 (.leaf (certNat% 40))
 (.leaf (certNat% 41)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (certNat% 42))
 (.leaf (certNat% 43)))
 (.branch 11
 (.leaf (certNat% 44))
 (.leaf (certNat% 45))))
 (.branch 14
 (.branch 13
 (.leaf (certNat% 46))
 (.leaf (certNat% 47)))
 (.branch 15
 (.leaf (certNat% 48))
 (.branch 16
 (.leaf (certNat% 49))
 (.leaf (certNat% 50)))))))
cert_codes_4
cert_counters_4
def rawNodes (i : Nat) := PackedRawNatGrowth.decodeNode widths (codes i)
def leafTable : Table (List Nat) :=
(.branch 3
 (.branch 1
 (.leaf [0,294,414,662,818,1645,1801,3059,3084,3237,3387])
 (.branch 2
 (.leaf [0,202,356,639,774,1717,1819,2242,3011,3122,3247])
 (.leaf [0,180,309,687,751,1737,1843,2254,2523,2925,3091])))
 (.branch 5
 (.branch 4
 (.leaf [0,176,372,704,854,1638,1834,2490,2523,2673,3116])
 (.leaf [0,177,312,734,848,1164,1692,1843,2049,2523,3216]))
 (.branch 6
 (.leaf [0,202,411,627,786,1572,1681,1858,3074,3155,3163])
 (.leaf [0,248,400,734,850,1692,1757,1898,2523,3118,3211]))))
def rawLeaves := leafTable.get
cert_leaves_4
cert_quota_5 0 4 6
cert_nodeTest_6
cert_nodeTest_sound_5
cert_leafTest_6
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest06
