module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public meta import CertificateNumbers
import HexNatLiteral
public import RootedSixBase02GrowthCacheData
public import RootedSixBase02FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0361
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 8084
abbrev nodeCount : Nat := 958
abbrev leafCount : Nat := 7
cert_widths_3 13 10 6 3
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
 (.leaf ⟨(certNat% 14),(certNat% 15)⟩))))
cert_counterTable_5
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 3
 (.branch 1
 (.leaf [0,63,139,225,333,355,529,655,925,1054,1229])
 (.branch 2
 (.leaf [0,1,189,332,335,530,553,643,946,1053,1230])
 (.leaf [0,21,104,211,330,530,598,679,905,1017,1234])))
 (.branch 5
 (.branch 4
 (.leaf [0,83,153,174,333,482,529,534,631,946,1054])
 (.leaf [0,53,114,210,332,530,556,667,925,1053,1229]))
 (.branch 6
 (.leaf [0,21,163,188,331,337,530,679,947,1041,1235])
 (.leaf [0,1,178,333,362,482,529,538,655,946,1054]))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 1 0 0 0 0 0 0 2 8
cert_nodeTest_5 48 02
cert_nodeTest_sound_4 48 02
cert_leafTest_4 02
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0361
