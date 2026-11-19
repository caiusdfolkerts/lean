module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public meta import CertificateNumbers
import HexNatLiteral
public import RootedSixBase03GrowthCacheData
public import RootedSixBase03FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0676
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 5238
abbrev nodeCount : Nat := 2557
abbrev leafCount : Nat := 2
cert_widths_3 13 12 7 1
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨((certNat% 0)),(certNat% 1)⟩)
 (.leaf ⟨((certNat% 2)),(certNat% 3)⟩))
 (.branch 3
 (.leaf ⟨((certNat% 4)),(certNat% 5)⟩)
 (.branch 4
 (.leaf ⟨((certNat% 6)),(certNat% 7)⟩)
 (.leaf ⟨((certNat% 8)),(certNat% 9)⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨((certNat% 10)),(certNat% 11)⟩)
 (.leaf ⟨((certNat% 12)),(certNat% 13)⟩))
 (.branch 8
 (.leaf ⟨((certNat% 14)),(certNat% 15)⟩)
 (.branch 9
 (.leaf ⟨((certNat% 16)),(certNat% 17)⟩)
 (.leaf ⟨((certNat% 18)),(certNat% 19)⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨((certNat% 20)),(certNat% 21)⟩)
 (.leaf ⟨((certNat% 22)),(certNat% 23)⟩))
 (.branch 13
 (.leaf ⟨((certNat% 24)),(certNat% 25)⟩)
 (.branch 14
 (.leaf ⟨((certNat% 26)),(certNat% 27)⟩)
 (.leaf ⟨((certNat% 28)),(certNat% 29)⟩))))
 (.branch 17
 (.branch 16
 (.leaf ⟨((certNat% 30)),(certNat% 31)⟩)
 (.leaf ⟨((certNat% 32)),(certNat% 33)⟩))
 (.branch 18
 (.leaf ⟨((certNat% 34)),(certNat% 35)⟩)
 (.branch 19
 (.leaf ⟨((certNat% 36)),(certNat% 37)⟩)
 (.leaf ⟨((certNat% 38)),(certNat% 39)⟩))))))
def counterTable : Table Nat :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (certNat% 40))
 (.leaf (certNat% 41)))
 (.branch 3
 (.leaf (certNat% 42))
 (.branch 4
 (.leaf (certNat% 43))
 (.leaf (certNat% 44)))))
 (.branch 7
 (.branch 6
 (.leaf (certNat% 45))
 (.leaf (certNat% 46)))
 (.branch 8
 (.leaf (certNat% 47))
 (.branch 9
 (.leaf (certNat% 48))
 (.leaf (certNat% 49))))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf (certNat% 50))
 (.leaf (certNat% 51)))
 (.branch 13
 (.leaf (certNat% 52))
 (.branch 14
 (.leaf (certNat% 53))
 (.leaf (certNat% 54)))))
 (.branch 17
 (.branch 16
 (.leaf (certNat% 55))
 (.leaf (certNat% 56)))
 (.branch 18
 (.leaf (certNat% 57))
 (.branch 19
 (.leaf (certNat% 58))
 (.leaf (certNat% 59)))))))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 1
 (.leaf [0,1,197,406,452,544,734,988,1298,1609,4996])
 (.leaf [0,1,195,352,511,554,708,1033,1277,1607,4994]))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 1 1 0 0 0 0 0 4 4
cert_nodeTest_5 96 03
cert_nodeTest_sound_4 96 03
cert_leafTest_4 03
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0676
