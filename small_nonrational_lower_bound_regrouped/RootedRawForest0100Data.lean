module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public meta import CertificateNumbers
public import HexNatLiteral
public import RootedSevenPure066GrowthCacheData
public import IdentityRawMaps
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0100
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 461
abbrev nodeCount : Nat := 1228
abbrev leafCount : Nat := 12
cert_widths_2 9 11 4
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
 (.branch 7
 (.branch 6
 (.leaf ⟨(certNat% 10),(certNat% 11)⟩)
 (.leaf ⟨(certNat% 12),(certNat% 13)⟩))
 (.branch 8
 (.leaf ⟨(certNat% 14),(certNat% 15)⟩)
 (.branch 9
 (.leaf ⟨(certNat% 16),(certNat% 17)⟩)
 (.leaf ⟨(certNat% 18),(certNat% 19)⟩)))))
def counterTable : Table Nat :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf (certNat% 20))
 (.leaf (certNat% 21)))
 (.branch 3
 (.leaf (certNat% 22))
 (.branch 4
 (.leaf (certNat% 23))
 (.leaf (certNat% 24)))))
 (.branch 7
 (.branch 6
 (.leaf (certNat% 25))
 (.leaf (certNat% 26)))
 (.branch 8
 (.leaf (certNat% 27))
 (.branch 9
 (.leaf (certNat% 28))
 (.leaf (certNat% 29))))))
cert_codes_2
cert_counters_2
cert_rawNodes_2
def leafTable : Table (List Nat) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf [0,1,92,129,195,199,222,325,375,379])
 (.branch 2
 (.leaf [0,39,57,92,129,195,222,325,375,379])
 (.leaf [0,1,92,117,196,198,234,324,376,378])))
 (.branch 4
 (.leaf [0,39,69,92,117,196,234,324,376,378])
 (.branch 5
 (.leaf [0,2,93,141,194,199,223,313,374,379])
 (.leaf [0,39,56,93,141,194,223,313,374,379]))))
 (.branch 9
 (.branch 7
 (.leaf [0,2,93,116,196,197,246,312,376,377])
 (.branch 8
 (.leaf [0,39,81,93,116,196,246,312,376,377])
 (.leaf [0,3,94,140,194,198,235,301,374,378])))
 (.branch 10
 (.leaf [0,39,68,94,140,194,235,301,374,378])
 (.branch 11
 (.leaf [0,3,94,128,195,197,247,300,375,377])
 (.leaf [0,39,80,94,128,195,247,300,375,377])))))
cert_rawLeaves_2
cert_leaves_2
cert_quota_2 1 0 6 3
cert_nodeTest_2 066
cert_nodeTest_sound_2 066
cert_leafTest_2 066
end Papers.RationalityTen.RootedForests.RootedRawForest0100
