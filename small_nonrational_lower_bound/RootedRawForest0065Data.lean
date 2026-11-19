module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public meta import CertificateNumbers
public import HexNatLiteral
public import RootedSevenPure031GrowthCacheData
public import IdentityRawMaps
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0065
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 461
abbrev nodeCount : Nat := 1401
abbrev leafCount : Nat := 18
cert_widths_2 9 11 5
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
cert_codes_2
cert_counters_2
cert_rawNodes_2
def leafTable : Table (List Nat) :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf [0,59,92,117,142,161,208,248,305,390])
 (.leaf [0,71,92,118,141,161,207,236,293,391]))
 (.branch 3
 (.leaf [0,57,92,116,162,187,208,246,312,383])
 (.leaf [0,60,92,117,142,162,187,243,315,393])))
 (.branch 6
 (.branch 5
 (.leaf [0,69,92,116,163,186,207,234,313,371])
 (.leaf [0,72,92,118,141,163,186,231,314,392]))
 (.branch 7
 (.leaf [0,61,93,116,142,161,187,255,303,381])
 (.branch 8
 (.leaf [0,56,93,117,161,187,208,258,300,395])
 (.leaf [0,58,93,116,142,162,208,260,317,378])))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf [0,83,93,118,140,162,206,235,292,379])
 (.leaf [0,81,93,117,163,185,206,233,301,370]))
 (.branch 12
 (.leaf [0,84,93,118,140,163,185,232,302,380])
 (.leaf [0,73,94,116,141,161,186,256,291,369])))
 (.branch 15
 (.branch 14
 (.leaf [0,68,94,118,161,186,207,257,288,394])
 (.leaf [0,85,94,117,140,162,185,244,290,368]))
 (.branch 16
 (.leaf [0,80,94,118,162,185,206,245,289,382])
 (.branch 17
 (.leaf [0,70,94,116,141,163,207,259,316,366])
 (.leaf [0,82,94,117,140,163,206,247,304,367]))))))
cert_rawLeaves_2
cert_leaves_2
cert_quota_2 1 0 4 5
cert_nodeTest_2 031
cert_nodeTest_sound_2 031
cert_leafTest_2 031
end Papers.RationalityTen.RootedForests.RootedRawForest0065
