module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public meta import CertificateNumbers
import HexNatLiteral
public import RootedSixBase04GrowthCacheData
public import RootedSixBase04FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0705
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2824
abbrev nodeCount : Nat := 961
abbrev leafCount : Nat := 3
cert_widths_3 12 10 11 2
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨((certNat% 0)),(certNat% 1)⟩)
 (.leaf ⟨((certNat% 2)),(certNat% 3)⟩))
 (.branch 3
 (.leaf ⟨((certNat% 4)),(certNat% 5)⟩)
 (.leaf ⟨((certNat% 6)),(certNat% 7)⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨((certNat% 8)),(certNat% 9)⟩)
 (.leaf ⟨((certNat% 10)),(certNat% 11)⟩))
 (.branch 7
 (.leaf ⟨((certNat% 12)),(certNat% 13)⟩)
 (.leaf ⟨((certNat% 14)),(certNat% 15)⟩))))
cert_counterTable_5
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 1
 (.leaf [0,1,6,331,352,389,569,798,978,2789,2819])
 (.branch 2
 (.leaf [0,1,6,287,389,569,777,798,978,2789,2819])
 (.leaf [0,1,96,331,389,572,798,981,1808,2427,2789])))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 2 2 0 0 0 0 0 6 1
cert_nodeTest_5 1152 04
cert_nodeTest_sound_4 1152 04
cert_leafTest_4 04
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0705
