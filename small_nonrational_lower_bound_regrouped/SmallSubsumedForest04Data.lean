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
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest04
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 3436
abbrev nodeCount : Nat := 387
abbrev leafCount : Nat := 4
cert_widths_4 9 2
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 2
 (.branch 1
 (.leaf ⟨(certNat% 0),(certNat% 1)⟩)
 (.leaf ⟨(certNat% 2),(certNat% 3)⟩))
 (.branch 3
 (.leaf ⟨(certNat% 4),(certNat% 5)⟩)
 (.leaf ⟨(certNat% 6),(certNat% 7)⟩)))
def counterTable : Table Nat :=
(.branch 2
 (.branch 1
 (.leaf (certNat% 8))
 (.leaf (certNat% 9)))
 (.branch 3
 (.leaf (certNat% 10))
 (.leaf (certNat% 11))))
cert_codes_4
cert_counters_4
def rawNodes (i : Nat) := PackedRawNatGrowth.decodeNode widths (codes i)
def leafTable : Table (List Nat) :=
(.branch 2
 (.branch 1
 (.leaf [0,188,383,712,806,1659,1813,2368,2787,3241,3390])
 (.leaf [0,228,357,727,782,1437,1710,1765,2594,3115,3340]))
 (.branch 3
 (.leaf [0,252,345,738,808,1546,1721,1826,2516,3111,3286])
 (.leaf [0,204,336,690,822,1550,1709,1841,2570,3140])))
def rawLeaves := leafTable.get
cert_leaves_4
cert_quota_5 0 0 10
cert_nodeTest_6
cert_nodeTest_sound_5
cert_leafTest_6
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest04
