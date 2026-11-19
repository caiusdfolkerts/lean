module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public meta import CertificateNumbers
import HexNatLiteral
public import RootedSixBase01GrowthCacheData
public import RootedSixBase01FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0232
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 15246
abbrev nodeCount : Nat := 2976
abbrev leafCount : Nat := 1
cert_widths_3 14 12 6 1
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 12
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
 (.branch 10
 (.leaf ⟨((certNat% 18)),(certNat% 19)⟩)
 (.branch 11
 (.leaf ⟨((certNat% 20)),(certNat% 21)⟩)
 (.leaf ⟨((certNat% 22)),(certNat% 23)⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨((certNat% 24)),(certNat% 25)⟩)
 (.branch 14
 (.leaf ⟨((certNat% 26)),(certNat% 27)⟩)
 (.leaf ⟨((certNat% 28)),(certNat% 29)⟩)))
 (.branch 16
 (.leaf ⟨((certNat% 30)),(certNat% 31)⟩)
 (.branch 17
 (.leaf ⟨((certNat% 32)),(certNat% 33)⟩)
 (.leaf ⟨((certNat% 34)),(certNat% 35)⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨((certNat% 36)),(certNat% 37)⟩)
 (.branch 20
 (.leaf ⟨((certNat% 38)),(certNat% 39)⟩)
 (.leaf ⟨((certNat% 40)),(certNat% 41)⟩)))
 (.branch 22
 (.leaf ⟨((certNat% 42)),(certNat% 43)⟩)
 (.branch 23
 (.leaf ⟨((certNat% 44)),(certNat% 45)⟩)
 (.leaf ⟨(certNat% 46),(certNat% 47)⟩))))))
def counterTable : Table Nat :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (certNat% 48))
 (.branch 2
 (.leaf (certNat% 49))
 (.leaf (certNat% 50))))
 (.branch 4
 (.leaf (certNat% 51))
 (.branch 5
 (.leaf (certNat% 52))
 (.leaf (certNat% 53)))))
 (.branch 9
 (.branch 7
 (.leaf (certNat% 54))
 (.branch 8
 (.leaf (certNat% 55))
 (.leaf (certNat% 56))))
 (.branch 10
 (.leaf (certNat% 57))
 (.branch 11
 (.leaf (certNat% 58))
 (.leaf (certNat% 59))))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf (certNat% 60))
 (.branch 14
 (.leaf (certNat% 61))
 (.leaf (certNat% 62))))
 (.branch 16
 (.leaf (certNat% 63))
 (.branch 17
 (.leaf (certNat% 64))
 (.leaf (certNat% 65)))))
 (.branch 21
 (.branch 19
 (.leaf (certNat% 66))
 (.branch 20
 (.leaf (certNat% 67))
 (.leaf (certNat% 68))))
 (.branch 22
 (.leaf (certNat% 69))
 (.branch 23
 (.leaf (certNat% 70))
 (.leaf (certNat% 71)))))))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
cert_leafTable_3
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 1 0 0 0 0 1 0 2 6
cert_nodeTest_5 48 01
cert_nodeTest_sound_4 48 01
cert_leafTest_4 01
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0232
