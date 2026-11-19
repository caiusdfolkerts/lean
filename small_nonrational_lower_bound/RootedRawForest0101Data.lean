module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public meta import CertificateNumbers
public import RootedSevenPure067GrowthCacheData
public import IdentityRawMaps
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0101
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 406
abbrev nodeCount : Nat := 274
abbrev leafCount : Nat := 6
cert_widths_2 9 9 3
cert_blocks_3
cert_counterTable_2
cert_codes_2
cert_counters_2
cert_rawNodes_2
def leafTable : Table (List Nat) :=
(.branch 3
 (.branch 1
 (.leaf [0,2,37,74,140,165,186,211,245,314])
 (.branch 2
 (.leaf [0,14,37,62,141,164,185,211,233,315])
 (.leaf [0,1,38,86,139,165,186,212,257,302])))
 (.branch 4
 (.leaf [0,26,38,61,141,163,184,212,234,303])
 (.branch 5
 (.leaf [0,13,39,85,139,164,185,213,258,290])
 (.leaf [0,25,39,73,140,163,184,213,246,291]))))
cert_rawLeaves_2
cert_leaves_2
cert_quota_2 0 0 6 3
cert_nodeTest_2 067
cert_nodeTest_sound_2 067
cert_leafTest_2 067
end Papers.RationalityTen.RootedForests.RootedRawForest0101
