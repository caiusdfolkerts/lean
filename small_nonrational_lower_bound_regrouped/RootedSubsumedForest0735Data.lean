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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0735
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2824
abbrev nodeCount : Nat := 2473
abbrev leafCount : Nat := 5
cert_widths_3 12 12 11 3
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
 (.leaf ⟨(certNat% 38),(certNat% 39)⟩))))))
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
(.branch 2
 (.branch 1
 (.leaf [0,1,5,359,527,780,948,1249,1526,1825,1850])
 (.leaf [0,1,9,239,383,516,807,998,1185,1260,1505,1824]))
 (.branch 3
 (.leaf [0,1,26,230,386,661,745,807,995,1260,1505])
 (.branch 4
 (.leaf [0,1,41,206,429,488,554,782,972,1226,1526,1847])
 (.leaf [0,2,97,254,410,574,831,995,1260]))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 2 0 0 0 0 0 0 2 7
cert_nodeTest_5 1152 04
cert_nodeTest_sound_4 1152 04
cert_leafTest_4 04
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0735
