module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public meta import CertificateNumbers
public import RootedSevenMixed026GrowthCacheData
public import IdentityRawMaps
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0026
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 556
abbrev nodeCount : Nat := 427
abbrev leafCount : Nat := 1
cert_widths_2 10 9 1
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
cert_codes_2
cert_counters_2
cert_rawNodes_2
cert_leafTable_2
cert_rawLeaves_2
cert_leaves_2
cert_quota_2 0 1 3 5
cert_nodeTest_3 026
cert_nodeTest_sound 026
cert_leafTest_3 026
end Papers.RationalityTen.RootedForests.RootedRawForest0026
