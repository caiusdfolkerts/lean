module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0865
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2170
abbrev nodeCount : Nat := 5713
abbrev leafCount : Nat := 36
cert_widths_3 12 13 9 6
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 22
 (.branch 11
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
 (.branch 8
 (.branch 6
 (.leaf ⟨((certNat% 10)),(certNat% 11)⟩)
 (.branch 7
 (.leaf ⟨((certNat% 12)),(certNat% 13)⟩)
 (.leaf ⟨((certNat% 14)),(certNat% 15)⟩)))
 (.branch 9
 (.leaf ⟨((certNat% 16)),(certNat% 17)⟩)
 (.branch 10
 (.leaf ⟨((certNat% 18)),(certNat% 19)⟩)
 (.leaf ⟨((certNat% 20)),(certNat% 21)⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨((certNat% 22)),(certNat% 23)⟩)
 (.leaf ⟨((certNat% 24)),(certNat% 25)⟩))
 (.branch 14
 (.leaf ⟨((certNat% 26)),(certNat% 27)⟩)
 (.branch 15
 (.leaf ⟨((certNat% 28)),(certNat% 29)⟩)
 (.leaf ⟨((certNat% 30)),(certNat% 31)⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨((certNat% 32)),(certNat% 33)⟩)
 (.branch 18
 (.leaf ⟨((certNat% 34)),(certNat% 35)⟩)
 (.leaf ⟨((certNat% 36)),(certNat% 37)⟩)))
 (.branch 20
 (.leaf ⟨((certNat% 38)),(certNat% 39)⟩)
 (.branch 21
 (.leaf ⟨((certNat% 40)),(certNat% 41)⟩)
 (.leaf ⟨((certNat% 42)),(certNat% 43)⟩))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf ⟨((certNat% 44)),(certNat% 45)⟩)
 (.leaf ⟨((certNat% 46)),(certNat% 47)⟩))
 (.branch 25
 (.leaf ⟨((certNat% 48)),(certNat% 49)⟩)
 (.branch 26
 (.leaf ⟨((certNat% 50)),(certNat% 51)⟩)
 (.leaf ⟨((certNat% 52)),(certNat% 53)⟩))))
 (.branch 30
 (.branch 28
 (.leaf ⟨((certNat% 54)),(certNat% 55)⟩)
 (.branch 29
 (.leaf ⟨((certNat% 56)),(certNat% 57)⟩)
 (.leaf ⟨((certNat% 58)),(certNat% 59)⟩)))
 (.branch 31
 (.leaf ⟨((certNat% 60)),(certNat% 61)⟩)
 (.branch 32
 (.leaf ⟨((certNat% 62)),(certNat% 63)⟩)
 (.leaf ⟨((certNat% 64)),(certNat% 65)⟩)))))
 (.branch 39
 (.branch 36
 (.branch 34
 (.leaf ⟨((certNat% 66)),(certNat% 67)⟩)
 (.branch 35
 (.leaf ⟨((certNat% 68)),(certNat% 69)⟩)
 (.leaf ⟨((certNat% 70)),(certNat% 71)⟩)))
 (.branch 37
 (.leaf ⟨((certNat% 72)),(certNat% 73)⟩)
 (.branch 38
 (.leaf ⟨((certNat% 74)),(certNat% 75)⟩)
 (.leaf ⟨((certNat% 76)),(certNat% 77)⟩))))
 (.branch 42
 (.branch 40
 (.leaf ⟨((certNat% 78)),(certNat% 79)⟩)
 (.branch 41
 (.leaf ⟨((certNat% 80)),(certNat% 81)⟩)
 (.leaf ⟨((certNat% 82)),(certNat% 83)⟩)))
 (.branch 43
 (.leaf ⟨((certNat% 84)),(certNat% 85)⟩)
 (.branch 44
 (.leaf ⟨((certNat% 86)),(certNat% 87)⟩)
 (.leaf ⟨((certNat% 88)),(certNat% 89)⟩)))))))
def counterTable : Table Nat :=
(.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (certNat% 90))
 (.leaf (certNat% 91)))
 (.branch 3
 (.leaf (certNat% 92))
 (.branch 4
 (.leaf (certNat% 93))
 (.leaf (certNat% 94)))))
 (.branch 8
 (.branch 6
 (.leaf (certNat% 95))
 (.branch 7
 (.leaf (certNat% 96))
 (.leaf (certNat% 97))))
 (.branch 9
 (.leaf (certNat% 98))
 (.branch 10
 (.leaf (certNat% 99))
 (.leaf (certNat% 100))))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf (certNat% 101))
 (.leaf (certNat% 102)))
 (.branch 14
 (.leaf (certNat% 103))
 (.branch 15
 (.leaf (certNat% 104))
 (.leaf (certNat% 105)))))
 (.branch 19
 (.branch 17
 (.leaf (certNat% 106))
 (.branch 18
 (.leaf (certNat% 107))
 (.leaf (certNat% 108))))
 (.branch 20
 (.leaf (certNat% 109))
 (.branch 21
 (.leaf (certNat% 110))
 (.leaf (certNat% 111)))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf (certNat% 112))
 (.leaf (certNat% 113)))
 (.branch 25
 (.leaf (certNat% 114))
 (.branch 26
 (.leaf (certNat% 115))
 (.leaf (certNat% 116)))))
 (.branch 30
 (.branch 28
 (.leaf (certNat% 117))
 (.branch 29
 (.leaf (certNat% 118))
 (.leaf (certNat% 119))))
 (.branch 31
 (.leaf (certNat% 120))
 (.branch 32
 (.leaf (certNat% 121))
 (.leaf (certNat% 122))))))
 (.branch 39
 (.branch 36
 (.branch 34
 (.leaf (certNat% 123))
 (.branch 35
 (.leaf (certNat% 124))
 (.leaf (certNat% 125))))
 (.branch 37
 (.leaf (certNat% 126))
 (.branch 38
 (.leaf (certNat% 127))
 (.leaf (certNat% 128)))))
 (.branch 42
 (.branch 40
 (.leaf (certNat% 129))
 (.branch 41
 (.leaf (certNat% 130))
 (.leaf (certNat% 131))))
 (.branch 43
 (.leaf (certNat% 132))
 (.branch 44
 (.leaf (certNat% 133))
 (.leaf (certNat% 134))))))))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf [0,8,20,47,137,162,249,448,599,820,986])
 (.leaf [0,22,38,152,162,251,448,815]))
 (.branch 3
 (.leaf [0,20,77,129,162,249,446,598,820,986])
 (.leaf [0,8,20,60,157,161,448,603,820,1508])))
 (.branch 6
 (.branch 5
 (.leaf [0,22,154,163,250,817,1569])
 (.leaf [0,2,8,15,162,251,402,528,818,1568]))
 (.branch 7
 (.leaf [0,3,17,24,160,216,249,325,758,1234,1548])
 (.branch 8
 (.leaf [0,1,162,173,251,282,402,818,1225,1568])
 (.leaf [0,6,15,17,155,160,249,431,758,1248,1548])))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf [0,1,54,87,161,166,249,275,446,507,528])
 (.leaf [0,4,56,163,251,448]))
 (.branch 12
 (.leaf [0,11,41,54,101,161,187,249,446,522,740])
 (.leaf [0,23,39,56,92,163,213,251,324,448,521])))
 (.branch 15
 (.branch 14
 (.leaf [0,26,27,53,154,160,192,248,259,445,527])
 (.leaf [0,25,54,87,154,161,188,249,255,446,527]))
 (.branch 16
 (.leaf [0,1,17,53,160,261,415,445,937,1417,1506])
 (.branch 17
 (.leaf [0,1,5,11,161,249,456,612,721,800,1566])
 (.leaf [0,2,8,14,162,250,614,723,812,1562]))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf [0,2,8,249,415,446,612,804,1410])
 (.leaf [0,5,23,39,104,250,417,447,614,816,1406]))
 (.branch 21
 (.leaf [0,136,163,251,616,725,811,1558])
 (.leaf [0,4,17,34,247,248,277,445,495,944,1074,1404,1588])))
 (.branch 24
 (.branch 23
 (.leaf [0,1,5,53,242,248,366,445,542,1359,1413])
 (.leaf [0,1,160,248,545,675,752,1095,1225,1568]))
 (.branch 25
 (.leaf [0,17,34,52,135,248,275,445,493,944,1074,1404,1588])
 (.branch 26
 (.leaf [0,6,17,59,95,249,394,591,758,1410,1548])
 (.leaf [0,1,5,161,282,414,479,611,791,1507,1567])))))
 (.branch 31
 (.branch 29
 (.branch 28
 (.leaf [0,1,5,11,447,456,614,723,811,1406,1502])
 (.leaf [0,2,8,162,417,614,815,1502,1562]))
 (.branch 30
 (.leaf [0,2,8,14,446,612,721,799,1410,1506])
 (.leaf [0,5,23,39,104,161,415,612,803,1506,1566])))
 (.branch 33
 (.branch 32
 (.leaf [0,5,23,107,250,417,467,723,813,1406,1562])
 (.leaf [0,124,446,612,721,799,1410,1506]))
 (.branch 34
 (.leaf [0,17,18,35,95,222,249,758,881,1412,1548])
 (.branch 35
 (.leaf [0,17,109,201,447,583,772,860,1408,1492])
 (.leaf [0,1,20,53,162,168,289,507,827,944,1074,1504,1568])))))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 3 2 0 0 0 0 0 5 2
cert_nodeTest_4 288 05
cert_nodeTest_sound_3 288 05
cert_leafTest_5 05
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0865
