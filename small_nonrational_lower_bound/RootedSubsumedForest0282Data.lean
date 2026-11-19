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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0282
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 8084
abbrev nodeCount : Nat := 3904
abbrev leafCount : Nat := 12
cert_widths_3 13 12 6 4
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨((certNat% 0)),(certNat% 1)⟩)
 (.branch 2
 (.leaf ⟨((certNat% 2)),(certNat% 3)⟩)
 (.leaf ⟨((certNat% 4)),(certNat% 5)⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨((certNat% 6)),(certNat% 7)⟩)
 (.leaf ⟨((certNat% 8)),(certNat% 9)⟩))
 (.branch 6
 (.leaf ⟨((certNat% 10)),(certNat% 11)⟩)
 (.leaf ⟨((certNat% 12)),(certNat% 13)⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨((certNat% 14)),(certNat% 15)⟩)
 (.leaf ⟨((certNat% 16)),(certNat% 17)⟩))
 (.branch 10
 (.leaf ⟨((certNat% 18)),(certNat% 19)⟩)
 (.leaf ⟨((certNat% 20)),(certNat% 21)⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨((certNat% 22)),(certNat% 23)⟩)
 (.leaf ⟨((certNat% 24)),(certNat% 25)⟩))
 (.branch 14
 (.leaf ⟨((certNat% 26)),(certNat% 27)⟩)
 (.leaf ⟨((certNat% 28)),(certNat% 29)⟩)))))
 (.branch 23
 (.branch 19
 (.branch 17
 (.branch 16
 (.leaf ⟨((certNat% 30)),(certNat% 31)⟩)
 (.leaf ⟨((certNat% 32)),(certNat% 33)⟩))
 (.branch 18
 (.leaf ⟨((certNat% 34)),(certNat% 35)⟩)
 (.leaf ⟨((certNat% 36)),(certNat% 37)⟩)))
 (.branch 21
 (.branch 20
 (.leaf ⟨((certNat% 38)),(certNat% 39)⟩)
 (.leaf ⟨((certNat% 40)),(certNat% 41)⟩))
 (.branch 22
 (.leaf ⟨((certNat% 42)),(certNat% 43)⟩)
 (.leaf ⟨((certNat% 44)),(certNat% 45)⟩))))
 (.branch 27
 (.branch 25
 (.branch 24
 (.leaf ⟨((certNat% 46)),(certNat% 47)⟩)
 (.leaf ⟨((certNat% 48)),(certNat% 49)⟩))
 (.branch 26
 (.leaf ⟨((certNat% 50)),(certNat% 51)⟩)
 (.leaf ⟨((certNat% 52)),(certNat% 53)⟩)))
 (.branch 29
 (.branch 28
 (.leaf ⟨((certNat% 54)),(certNat% 55)⟩)
 (.leaf ⟨((certNat% 56)),(certNat% 57)⟩))
 (.branch 30
 (.leaf ⟨((certNat% 58)),(certNat% 59)⟩)
 (.leaf ⟨(certNat% 60),(certNat% 61)⟩))))))
def counterTable : Table Nat :=
(.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf (certNat% 62))
 (.branch 2
 (.leaf (certNat% 63))
 (.leaf (certNat% 64))))
 (.branch 5
 (.branch 4
 (.leaf (certNat% 65))
 (.leaf (certNat% 66)))
 (.branch 6
 (.leaf (certNat% 67))
 (.leaf (certNat% 68)))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf (certNat% 69))
 (.leaf (certNat% 70)))
 (.branch 10
 (.leaf (certNat% 71))
 (.leaf (certNat% 72))))
 (.branch 13
 (.branch 12
 (.leaf (certNat% 73))
 (.leaf (certNat% 74)))
 (.branch 14
 (.leaf (certNat% 75))
 (.leaf (certNat% 76))))))
 (.branch 23
 (.branch 19
 (.branch 17
 (.branch 16
 (.leaf (certNat% 77))
 (.leaf (certNat% 78)))
 (.branch 18
 (.leaf (certNat% 79))
 (.leaf (certNat% 80))))
 (.branch 21
 (.branch 20
 (.leaf (certNat% 81))
 (.leaf (certNat% 82)))
 (.branch 22
 (.leaf (certNat% 83))
 (.leaf (certNat% 84)))))
 (.branch 27
 (.branch 25
 (.branch 24
 (.leaf (certNat% 85))
 (.leaf (certNat% 86)))
 (.branch 26
 (.leaf (certNat% 87))
 (.leaf (certNat% 88))))
 (.branch 29
 (.branch 28
 (.leaf (certNat% 89))
 (.leaf (certNat% 90)))
 (.branch 30
 (.leaf (certNat% 91))
 (.leaf (certNat% 92)))))))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf [0,57,102,211,331,678,865,1032,4786,8025])
 (.branch 2
 (.leaf [0,57,103,187,330,682,861,1076,4818,8080])
 (.leaf [0,1,175,330,535,938,1017,1242,4507,8056])))
 (.branch 4
 (.leaf [0,6,139,331,959,1046,4449,8056])
 (.branch 5
 (.leaf [0,53,103,187,330,917,1017,1244,4506,8052])
 (.leaf [0,6,141,332,483,672,961,1053,8052]))))
 (.branch 9
 (.branch 7
 (.leaf [0,103,202,391,528,669,857,883,5091,7903])
 (.branch 8
 (.leaf [0,1,175,330,654,913,993,1332,2013,8058])
 (.leaf [0,1,178,333,364,482,655,1055,2013,8058])))
 (.branch 10
 (.leaf [0,6,333,493,655,1055,2389,8058])
 (.branch 11
 (.leaf [0,1,177,371,636,942,1054,1236,3721,8040])
 (.leaf [0,1,177,371,589,631,1055,1236,3721,8058])))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 1 1 1 0 0 0 0 3 4
cert_nodeTest_5 48 02
cert_nodeTest_sound_4 48 02
cert_leafTest_4 02
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0282
