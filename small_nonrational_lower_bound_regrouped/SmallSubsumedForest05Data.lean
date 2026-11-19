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
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest05
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 3436
abbrev nodeCount : Nat := 1404
abbrev leafCount : Nat := 1
cert_widths_4 11 1
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(certNat% 0),(certNat% 1)⟩)
 (.leaf ⟨(certNat% 2),(certNat% 3)⟩))
 (.branch 3
 (.leaf ⟨(certNat% 4),(certNat% 5)⟩)
 (.branch 4
 (.leaf ⟨(certNat% 6),(certNat% 7)⟩)
 (.leaf ⟨(certNat% 8),(certNat% 9)⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(certNat% 10),(certNat% 11)⟩)
 (.branch 7
 (.leaf ⟨(certNat% 12),(certNat% 13)⟩)
 (.leaf ⟨(certNat% 14),(certNat% 15)⟩)))
 (.branch 9
 (.leaf ⟨(certNat% 16),(certNat% 17)⟩)
 (.branch 10
 (.leaf ⟨(certNat% 18),(certNat% 19)⟩)
 (.leaf ⟨(certNat% 20),(certNat% 21)⟩)))))
def counterTable : Table Nat :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf (certNat% 22))
 (.leaf (certNat% 23)))
 (.branch 3
 (.leaf (certNat% 24))
 (.branch 4
 (.leaf (certNat% 25))
 (.leaf (certNat% 26)))))
 (.branch 8
 (.branch 6
 (.leaf (certNat% 27))
 (.branch 7
 (.leaf (certNat% 28))
 (.leaf (certNat% 29))))
 (.branch 9
 (.leaf (certNat% 30))
 (.branch 10
 (.leaf (certNat% 31))
 (.leaf (certNat% 32))))))
cert_codes_4
cert_counters_4
def rawNodes (i : Nat) := PackedRawNatGrowth.decodeNode widths (codes i)
def leafTable : Table (List Nat) :=
(.leaf [])
def rawLeaves := leafTable.get
cert_leaves_4
cert_quota_5 0 2 8
cert_nodeTest_6
cert_nodeTest_sound_5
cert_leafTest_6
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest05
