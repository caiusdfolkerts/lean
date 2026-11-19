module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public meta import CertificateNumbers
public import HexNatLiteral
public import RootedSevenPure045GrowthCacheData
public import IdentityRawMaps
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0079
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 560
abbrev nodeCount : Nat := 2017
abbrev leafCount : Nat := 1
cert_widths_2 10 11 1
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
 (.leaf ⟨(certNat% 30),(certNat% 31)⟩)))))
def counterTable : Table Nat :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (certNat% 32))
 (.leaf (certNat% 33)))
 (.branch 3
 (.leaf (certNat% 34))
 (.leaf (certNat% 35))))
 (.branch 6
 (.branch 5
 (.leaf (certNat% 36))
 (.leaf (certNat% 37)))
 (.branch 7
 (.leaf (certNat% 38))
 (.leaf (certNat% 39)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (certNat% 40))
 (.leaf (certNat% 41)))
 (.branch 11
 (.leaf (certNat% 42))
 (.leaf (certNat% 43))))
 (.branch 14
 (.branch 13
 (.leaf (certNat% 44))
 (.leaf (certNat% 45)))
 (.branch 15
 (.leaf (certNat% 46))
 (.leaf (certNat% 47))))))
cert_codes_2
cert_counters_2
cert_rawNodes_2
cert_leafTable_2
cert_rawLeaves_2
cert_leaves_2
cert_quota_2 1 0 5 4
cert_nodeTest_2 045
cert_nodeTest_sound_2 045
cert_leafTest_2 045
end Papers.RationalityTen.RootedForests.RootedRawForest0079
