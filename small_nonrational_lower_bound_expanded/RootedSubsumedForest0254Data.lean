module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0254
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 8084
abbrev nodeCount : Nat := 1579
abbrev leafCount : Nat := 2
cert_widths_3 13 11 6 1
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨((certNat% 0)),(certNat% 1)⟩)
 (.branch 2
 (.leaf ⟨((certNat% 2)),(certNat% 3)⟩)
 (.leaf ⟨((certNat% 4)),(certNat% 5)⟩)))
 (.branch 4
 (.leaf ⟨((certNat% 6)),(certNat% 7)⟩)
 (.branch 5
 (.leaf ⟨((certNat% 8)),(certNat% 9)⟩)
 (.leaf ⟨((certNat% 10)),(certNat% 11)⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨((certNat% 12)),(certNat% 13)⟩)
 (.branch 8
 (.leaf ⟨((certNat% 14)),(certNat% 15)⟩)
 (.leaf ⟨((certNat% 16)),(certNat% 17)⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨((certNat% 18)),(certNat% 19)⟩)
 (.leaf ⟨((certNat% 20)),(certNat% 21)⟩))
 (.branch 12
 (.leaf ⟨((certNat% 22)),(certNat% 23)⟩)
 (.leaf ⟨(certNat% 24),(certNat% 25)⟩)))))
def counterTable : Table Nat :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf (certNat% 26))
 (.branch 2
 (.leaf (certNat% 27))
 (.leaf (certNat% 28))))
 (.branch 4
 (.leaf (certNat% 29))
 (.branch 5
 (.leaf (certNat% 30))
 (.leaf (certNat% 31)))))
 (.branch 9
 (.branch 7
 (.leaf (certNat% 32))
 (.branch 8
 (.leaf (certNat% 33))
 (.leaf (certNat% 34))))
 (.branch 11
 (.branch 10
 (.leaf (certNat% 35))
 (.leaf (certNat% 36)))
 (.branch 12
 (.leaf (certNat% 37))
 (.leaf (certNat% 38))))))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 1
 (.leaf [0,6,141,332,483,672,961,1053,8052])
 (.leaf [0,1,187,330,589,651,902,993,1232,1332,8058]))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 1 1 0 0 0 0 0 3 5
cert_nodeTest_5 48 02
cert_nodeTest_sound_4 48 02
cert_leafTest_4 02
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0254
