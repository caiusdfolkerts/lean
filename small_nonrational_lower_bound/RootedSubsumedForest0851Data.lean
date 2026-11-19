module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public meta import CertificateNumbers
import HexNatLiteral
public import RootedSixExtra05GrowthCacheData
public import RootedSixExtra05FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0851
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2170
abbrev nodeCount : Nat := 2320
abbrev leafCount : Nat := 13
cert_widths_3 12 12 9 4
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 9
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
 (.branch 8
 (.leaf ⟨((certNat% 14)),(certNat% 15)⟩)
 (.leaf ⟨((certNat% 16)),(certNat% 17)⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨((certNat% 18)),(certNat% 19)⟩)
 (.leaf ⟨((certNat% 20)),(certNat% 21)⟩))
 (.branch 12
 (.leaf ⟨((certNat% 22)),(certNat% 23)⟩)
 (.branch 13
 (.leaf ⟨((certNat% 24)),(certNat% 25)⟩)
 (.leaf ⟨((certNat% 26)),(certNat% 27)⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨((certNat% 28)),(certNat% 29)⟩)
 (.leaf ⟨((certNat% 30)),(certNat% 31)⟩))
 (.branch 17
 (.leaf ⟨((certNat% 32)),(certNat% 33)⟩)
 (.branch 18
 (.leaf ⟨((certNat% 34)),(certNat% 35)⟩)
 (.leaf ⟨(certNat% 36),(certNat% 37)⟩))))))
def counterTable : Table Nat :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (certNat% 38))
 (.leaf (certNat% 39)))
 (.branch 3
 (.leaf (certNat% 40))
 (.leaf (certNat% 41))))
 (.branch 6
 (.branch 5
 (.leaf (certNat% 42))
 (.leaf (certNat% 43)))
 (.branch 7
 (.leaf (certNat% 44))
 (.branch 8
 (.leaf (certNat% 45))
 (.leaf (certNat% 46))))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf (certNat% 47))
 (.leaf (certNat% 48)))
 (.branch 12
 (.leaf (certNat% 49))
 (.branch 13
 (.leaf (certNat% 50))
 (.leaf (certNat% 51)))))
 (.branch 16
 (.branch 15
 (.leaf (certNat% 52))
 (.leaf (certNat% 53)))
 (.branch 17
 (.leaf (certNat% 54))
 (.branch 18
 (.leaf (certNat% 55))
 (.leaf (certNat% 56)))))))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf [0,22,38,152,162,251,448,815])
 (.branch 2
 (.leaf [0,20,77,129,162,249,446,598,820,986])
 (.leaf [0,22,154,163,250,817,1569])))
 (.branch 4
 (.leaf [0,1,162,173,251,282,402,818,1225,1568])
 (.branch 5
 (.leaf [0,4,56,163,251,448])
 (.leaf [0,2,8,249,415,446,612,804,1410]))))
 (.branch 9
 (.branch 7
 (.leaf [0,136,163,251,616,725,811,1558])
 (.branch 8
 (.leaf [0,1,160,248,545,675,752,1095,1225,1568])
 (.leaf [0,1,5,161,282,414,479,611,791,1507,1567])))
 (.branch 11
 (.branch 10
 (.leaf [0,2,8,162,417,614,815,1502,1562])
 (.leaf [0,5,23,107,250,417,467,723,813,1406,1562]))
 (.branch 12
 (.leaf [0,124,446,612,721,799,1410,1506])
 (.leaf [0,17,109,201,447,583,772,860,1408,1492])))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 2 2 0 0 0 0 0 5 2
cert_nodeTest_4 288 05
cert_nodeTest_sound_3 288 05
cert_leafTest_5 05
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0851
