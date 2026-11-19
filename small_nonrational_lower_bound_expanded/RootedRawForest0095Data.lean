module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public meta import CertificateNumbers
public import HexNatLiteral
public import RootedSevenPure061GrowthCacheData
public import IdentityRawMaps
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0095
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 461
abbrev nodeCount : Nat := 655
abbrev leafCount : Nat := 6
cert_widths_2 9 10 3
def blocks : Table PackedRawNatGrowth.Block :=
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
def counterTable : Table Nat :=
(.branch 3
 (.branch 1
 (.leaf (certNat% 12))
 (.branch 2
 (.leaf (certNat% 13))
 (.leaf (certNat% 14))))
 (.branch 4
 (.leaf (certNat% 15))
 (.branch 5
 (.leaf (certNat% 16))
 (.leaf (certNat% 17)))))
cert_codes_2
cert_counters_2
cert_rawNodes_2
def leafTable : Table (List Nat) :=
(.branch 3
 (.branch 1
 (.leaf [0,15,57,92,116,221,299,374])
 (.branch 2
 (.leaf [0,16,69,92,116,233,311,374])
 (.leaf [0,14,56,93,117,220,298,375])))
 (.branch 4
 (.leaf [0,16,81,93,117,245,323,375])
 (.branch 5
 (.leaf [0,14,68,94,118,232,310,376])
 (.leaf [0,15,80,94,118,244,322,376]))))
cert_rawLeaves_2
cert_leaves_2
cert_quota_2 1 0 6 3
cert_nodeTest_2 061
cert_nodeTest_sound_2 061
cert_leafTest_2 061
end Papers.RationalityTen.RootedForests.RootedRawForest0095
