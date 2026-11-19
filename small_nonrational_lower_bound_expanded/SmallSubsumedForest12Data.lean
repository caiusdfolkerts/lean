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
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest12
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 3436
abbrev nodeCount : Nat := 1415
abbrev leafCount : Nat := 1
cert_widths_4 11 1
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(certNat% 0),(certNat% 1)⟩)
 (.branch 2
 (.leaf ⟨(certNat% 2),(certNat% 3)⟩)
 (.leaf ⟨(certNat% 4),(certNat% 5)⟩)))
 (.branch 4
 (.leaf ⟨(certNat% 6),(certNat% 7)⟩)
 (.branch 5
 (.leaf ⟨(certNat% 8),(certNat% 9)⟩)
 (.leaf ⟨(certNat% 10),(certNat% 11)⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(certNat% 12),(certNat% 13)⟩)
 (.branch 8
 (.leaf ⟨(certNat% 14),(certNat% 15)⟩)
 (.leaf ⟨(certNat% 16),(certNat% 17)⟩)))
 (.branch 10
 (.leaf ⟨(certNat% 18),(certNat% 19)⟩)
 (.branch 11
 (.leaf ⟨(certNat% 20),(certNat% 21)⟩)
 (.leaf ⟨(certNat% 22),(certNat% 23)⟩)))))
def counterTable : Table Nat :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf (certNat% 24))
 (.branch 2
 (.leaf (certNat% 25))
 (.leaf (certNat% 26))))
 (.branch 4
 (.leaf (certNat% 27))
 (.branch 5
 (.leaf (certNat% 28))
 (.leaf (certNat% 29)))))
 (.branch 9
 (.branch 7
 (.leaf (certNat% 30))
 (.branch 8
 (.leaf (certNat% 31))
 (.leaf (certNat% 32))))
 (.branch 10
 (.leaf (certNat% 33))
 (.branch 11
 (.leaf (certNat% 34))
 (.leaf (certNat% 35))))))
cert_codes_4
cert_counters_4
cert_rawNodes_4
def leafTable : Table (List Nat) :=
(.leaf [0,204,336,690,822,1550,1709,1841,2570,3140])
def rawLeaves := leafTable.get

cert_leaves_4
cert_quota_5 0 2 9
cert_nodeTest_6
cert_nodeTest_sound_5
cert_leafTest_6
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest12
