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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0862
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2170
abbrev nodeCount : Nat := 5003
abbrev leafCount : Nat := 31
cert_widths_3 12 13 9 5
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 20
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
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf ⟨((certNat% 40)),(certNat% 41)⟩)
 (.leaf ⟨((certNat% 42)),(certNat% 43)⟩))
 (.branch 23
 (.leaf ⟨((certNat% 44)),(certNat% 45)⟩)
 (.branch 24
 (.leaf ⟨((certNat% 46)),(certNat% 47)⟩)
 (.leaf ⟨((certNat% 48)),(certNat% 49)⟩))))
 (.branch 27
 (.branch 26
 (.leaf ⟨((certNat% 50)),(certNat% 51)⟩)
 (.leaf ⟨((certNat% 52)),(certNat% 53)⟩))
 (.branch 28
 (.leaf ⟨((certNat% 54)),(certNat% 55)⟩)
 (.branch 29
 (.leaf ⟨((certNat% 56)),(certNat% 57)⟩)
 (.leaf ⟨((certNat% 58)),(certNat% 59)⟩)))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf ⟨((certNat% 60)),(certNat% 61)⟩)
 (.leaf ⟨((certNat% 62)),(certNat% 63)⟩))
 (.branch 33
 (.leaf ⟨((certNat% 64)),(certNat% 65)⟩)
 (.branch 34
 (.leaf ⟨((certNat% 66)),(certNat% 67)⟩)
 (.leaf ⟨((certNat% 68)),(certNat% 69)⟩))))
 (.branch 37
 (.branch 36
 (.leaf ⟨((certNat% 70)),(certNat% 71)⟩)
 (.leaf ⟨((certNat% 72)),(certNat% 73)⟩))
 (.branch 38
 (.leaf ⟨((certNat% 74)),(certNat% 75)⟩)
 (.branch 39
 (.leaf ⟨((certNat% 76)),(certNat% 77)⟩)
 (.leaf ⟨(certNat% 78),(certNat% 79)⟩)))))))
def counterTable : Table Nat :=
(.branch 20
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (certNat% 80))
 (.leaf (certNat% 81)))
 (.branch 3
 (.leaf (certNat% 82))
 (.branch 4
 (.leaf (certNat% 83))
 (.leaf (certNat% 84)))))
 (.branch 7
 (.branch 6
 (.leaf (certNat% 85))
 (.leaf (certNat% 86)))
 (.branch 8
 (.leaf (certNat% 87))
 (.branch 9
 (.leaf (certNat% 88))
 (.leaf (certNat% 89))))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf (certNat% 90))
 (.leaf (certNat% 91)))
 (.branch 13
 (.leaf (certNat% 92))
 (.branch 14
 (.leaf (certNat% 93))
 (.leaf (certNat% 94)))))
 (.branch 17
 (.branch 16
 (.leaf (certNat% 95))
 (.leaf (certNat% 96)))
 (.branch 18
 (.leaf (certNat% 97))
 (.branch 19
 (.leaf (certNat% 98))
 (.leaf (certNat% 99)))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf (certNat% 100))
 (.leaf (certNat% 101)))
 (.branch 23
 (.leaf (certNat% 102))
 (.branch 24
 (.leaf (certNat% 103))
 (.leaf (certNat% 104)))))
 (.branch 27
 (.branch 26
 (.leaf (certNat% 105))
 (.leaf (certNat% 106)))
 (.branch 28
 (.leaf (certNat% 107))
 (.branch 29
 (.leaf (certNat% 108))
 (.leaf (certNat% 109))))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf (certNat% 110))
 (.leaf (certNat% 111)))
 (.branch 33
 (.leaf (certNat% 112))
 (.branch 34
 (.leaf (certNat% 113))
 (.leaf (certNat% 114)))))
 (.branch 37
 (.branch 36
 (.leaf (certNat% 115))
 (.leaf (certNat% 116)))
 (.branch 38
 (.leaf (certNat% 117))
 (.branch 39
 (.leaf (certNat% 118))
 (.leaf (certNat% 119))))))))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf [0,8,20,66,137,162,249,448,599,706,812])
 (.branch 2
 (.leaf [0,22,38,152,162,251,448,815])
 (.leaf [0,8,21,26,152,161,251,448,600,803])))
 (.branch 5
 (.branch 4
 (.leaf [0,2,8,62,162,249,401,446,598,804])
 (.leaf [0,3,8,9,163,250,402,447,599,816]))
 (.branch 6
 (.leaf [0,8,14,137,162,250,448,599,708,812])
 (.leaf [0,8,140,162,251,402,448,599,815]))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf [0,18,33,89,160,310,446,671,752,965,1508])
 (.leaf [0,8,20,60,157,161,448,603,820,1508]))
 (.branch 10
 (.leaf [0,17,18,157,161,167,448,603,820,826,1508])
 (.leaf [0,18,33,157,160,165,448,603,820,824,1508])))
 (.branch 13
 (.branch 12
 (.leaf [0,19,39,79,109,163,186,447,604,772,845,1492])
 (.leaf [0,5,57,125,160,291,447,540,713,788,946,1496]))
 (.branch 14
 (.leaf [0,22,154,163,250,817,1569])
 (.leaf [0,1,5,242,251,280,447,456,708,821,1413])))))
 (.branch 23
 (.branch 19
 (.branch 17
 (.branch 16
 (.leaf [0,2,8,15,162,251,402,528,818,1568])
 (.leaf [0,2,18,19,162,167,251,276,528,818,992,1568]))
 (.branch 18
 (.leaf [0,1,87,221,251,274,447,450,708,821,1413])
 (.leaf [0,4,56,163,251,448])))
 (.branch 21
 (.branch 20
 (.leaf [0,1,5,11,161,249,456,612,721,800,1566])
 (.leaf [0,2,8,14,162,250,614,723,812,1562]))
 (.branch 22
 (.leaf [0,2,8,249,415,446,612,804,1410])
 (.leaf [0,5,23,39,104,250,417,447,614,816,1406]))))
 (.branch 27
 (.branch 25
 (.branch 24
 (.leaf [0,136,163,251,616,725,811,1558])
 (.leaf [0,5,12,131,160,248,423,556,686,776,1099,1560]))
 (.branch 26
 (.leaf [0,1,5,11,161,249,506,562,650,751,1073,1569])
 (.leaf [0,1,5,242,248,364,445,540,756,901,1413])))
 (.branch 29
 (.branch 28
 (.leaf [0,17,18,90,161,310,446,671,753,965,1508])
 (.leaf [0,17,23,69,103,160,333,445,691,766,988,1504]))
 (.branch 30
 (.leaf [0,88,161,249,506,562,650,751,1073,1569])
 (.leaf [0,1,87,221,248,358,445,534,756,901,1413]))))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 3 1 0 0 0 0 0 4 4
cert_nodeTest_4 288 05
cert_nodeTest_sound_3 288 05
cert_leafTest_5 05
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0862
