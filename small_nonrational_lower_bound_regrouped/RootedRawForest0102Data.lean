module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public meta import CertificateNumbers
public import HexNatLiteral
public import RootedSevenPure068GrowthCacheData
public import IdentityRawMaps
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0102
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 461
abbrev nodeCount : Nat := 1216
abbrev leafCount : Nat := 6
cert_widths_2 9 11 3
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
(.branch 3
 (.branch 1
 (.leaf [0,57,92,129,195,220,241,266,300,369])
 (.branch 2
 (.leaf [0,69,92,117,196,219,240,266,288,370])
 (.leaf [0,56,93,141,194,220,241,267,312,357])))
 (.branch 4
 (.leaf [0,81,93,116,196,218,239,267,289,358])
 (.branch 5
 (.leaf [0,68,94,140,194,219,240,268,313,345])
 (.leaf [0,80,94,128,195,218,239,268,301,346]))))
cert_rawLeaves_2
cert_leaves_2
cert_quota_2 1 0 6 3
cert_nodeTest_2 068
cert_nodeTest_sound_2 068
cert_leafTest_2 068
end Papers.RationalityTen.RootedForests.RootedRawForest0102
