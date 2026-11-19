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
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest13
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 3436
abbrev nodeCount : Nat := 2215
abbrev leafCount : Nat := 10
cert_widths_4 12 4
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 9
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
 (.branch 8
 (.leaf ⟨(certNat% 14),(certNat% 15)⟩)
 (.leaf ⟨(certNat% 16),(certNat% 17)⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨(certNat% 18),(certNat% 19)⟩)
 (.leaf ⟨(certNat% 20),(certNat% 21)⟩))
 (.branch 12
 (.leaf ⟨(certNat% 22),(certNat% 23)⟩)
 (.leaf ⟨(certNat% 24),(certNat% 25)⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨(certNat% 26),(certNat% 27)⟩)
 (.leaf ⟨(certNat% 28),(certNat% 29)⟩))
 (.branch 16
 (.leaf ⟨(certNat% 30),(certNat% 31)⟩)
 (.branch 17
 (.leaf ⟨(certNat% 32),(certNat% 33)⟩)
 (.leaf ⟨(certNat% 34),(certNat% 35)⟩))))))
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
cert_codes_4
cert_counters_4
cert_rawNodes_4
def leafTable : Table (List Nat) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf [0,284,334,635,759,1138,1681,1847,2067,3042,3262,3312])
 (.leaf [0,294,414,662,818,1645,1801,3059,3084,3237,3387]))
 (.branch 3
 (.leaf [0,212,370,683,807,1243,1634,1774,2406,3040,3238,3387])
 (.branch 4
 (.leaf [0,212,370,683,807,1243,1634,1784,2949,3040,3238,3387])
 (.leaf [0,202,356,639,774,1717,1819,2242,3011,3122,3247]))))
 (.branch 7
 (.branch 6
 (.leaf [0,180,309,687,751,1737,1843,2254,2523,2925,3091])
 (.leaf [0,176,372,704,854,1638,1834,2490,2523,2673,3116]))
 (.branch 8
 (.leaf [0,177,312,734,848,1164,1692,1843,2049,2523,3216])
 (.branch 9
 (.leaf [0,202,411,627,786,1572,1681,1858,3074,3155,3163])
 (.leaf [0,248,400,734,850,1692,1757,1898,2523,3118,3211])))))
def rawLeaves := leafTable.get

cert_leaves_4
cert_quota_5 0 4 7
cert_nodeTest_6
cert_nodeTest_sound_5
cert_leafTest_6
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest13
