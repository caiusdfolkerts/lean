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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0864
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2170
abbrev nodeCount : Nat := 3294
abbrev leafCount : Nat := 41
cert_widths_3 12 12 9 6
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 13
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
 (.leaf ⟨((certNat% 24)),(certNat% 25)⟩)))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf ⟨((certNat% 26)),(certNat% 27)⟩)
 (.branch 15
 (.leaf ⟨((certNat% 28)),(certNat% 29)⟩)
 (.leaf ⟨((certNat% 30)),(certNat% 31)⟩)))
 (.branch 17
 (.leaf ⟨((certNat% 32)),(certNat% 33)⟩)
 (.branch 18
 (.leaf ⟨((certNat% 34)),(certNat% 35)⟩)
 (.leaf ⟨((certNat% 36)),(certNat% 37)⟩))))
 (.branch 22
 (.branch 20
 (.leaf ⟨((certNat% 38)),(certNat% 39)⟩)
 (.branch 21
 (.leaf ⟨((certNat% 40)),(certNat% 41)⟩)
 (.leaf ⟨((certNat% 42)),(certNat% 43)⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨((certNat% 44)),(certNat% 45)⟩)
 (.leaf ⟨((certNat% 46)),(certNat% 47)⟩))
 (.branch 25
 (.leaf ⟨((certNat% 48)),(certNat% 49)⟩)
 (.leaf ⟨((certNat% 50)),(certNat% 51)⟩))))))
def counterTable : Table Nat :=
(.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (certNat% 52))
 (.branch 2
 (.leaf (certNat% 53))
 (.leaf (certNat% 54))))
 (.branch 4
 (.leaf (certNat% 55))
 (.branch 5
 (.leaf (certNat% 56))
 (.leaf (certNat% 57)))))
 (.branch 9
 (.branch 7
 (.leaf (certNat% 58))
 (.branch 8
 (.leaf (certNat% 59))
 (.leaf (certNat% 60))))
 (.branch 11
 (.branch 10
 (.leaf (certNat% 61))
 (.leaf (certNat% 62)))
 (.branch 12
 (.leaf (certNat% 63))
 (.leaf (certNat% 64))))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf (certNat% 65))
 (.branch 15
 (.leaf (certNat% 66))
 (.leaf (certNat% 67))))
 (.branch 17
 (.leaf (certNat% 68))
 (.branch 18
 (.leaf (certNat% 69))
 (.leaf (certNat% 70)))))
 (.branch 22
 (.branch 20
 (.leaf (certNat% 71))
 (.branch 21
 (.leaf (certNat% 72))
 (.leaf (certNat% 73))))
 (.branch 24
 (.branch 23
 (.leaf (certNat% 74))
 (.leaf (certNat% 75)))
 (.branch 25
 (.leaf (certNat% 76))
 (.leaf (certNat% 77)))))))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 20
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf [0,5,18,137,160,250,255,448,563,716,770,1529])
 (.leaf [0,5,12,113,161,250,339,448,565,695,794,1531]))
 (.branch 3
 (.leaf [0,5,12,113,161,250,347,448,557,695,808,1465])
 (.branch 4
 (.leaf [0,22,38,152,162,251,448,815])
 (.leaf [0,20,77,129,162,249,446,598,820,986]))))
 (.branch 7
 (.branch 6
 (.leaf [0,25,33,105,161,237,248,362,445,631,756])
 (.leaf [0,6,17,92,162,249,380,446,544,818,939,1519]))
 (.branch 8
 (.leaf [0,1,87,161,221,242,248,362,445,538,756])
 (.branch 9
 (.leaf [0,6,17,126,160,249,423,591,721,758,1057,1566])
 (.leaf [0,5,87,101,161,375,447,536,702,796,990,1494])))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf [0,7,76,136,160,393,446,546,640,720,767,1507])
 (.leaf [0,6,77,124,160,394,446,591,612,721,779,1506]))
 (.branch 13
 (.leaf [0,6,17,126,160,249,423,591,721,784,946,1566])
 (.branch 14
 (.leaf [0,5,87,101,161,375,447,536,702,806,1097,1494])
 (.leaf [0,5,58,137,160,352,448,549,616,725,812,1498]))))
 (.branch 17
 (.branch 16
 (.leaf [0,6,57,149,160,351,448,566,636,724,800,1499])
 (.leaf [0,6,17,126,160,249,423,591,721,810,860,1566]))
 (.branch 18
 (.leaf [0,5,87,101,161,375,447,536,702,821,901,1494])
 (.branch 19
 (.leaf [0,18,33,89,160,310,446,671,752,965,1508])
 (.leaf [0,17,18,157,161,167,448,603,820,826,1508]))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf [0,18,33,157,160,165,448,603,820,824,1508])
 (.leaf [0,7,76,89,163,309,446,551,595,645,819,1509]))
 (.branch 23
 (.leaf [0,7,76,89,163,309,446,565,645,819,1121,1509])
 (.branch 24
 (.leaf [0,9,74,88,163,330,445,587,633,646,819,1509])
 (.leaf [0,6,17,91,162,249,380,507,674,818,939,1568]))))
 (.branch 27
 (.branch 26
 (.leaf [0,5,79,137,160,270,448,561,716,772,1090,1492])
 (.leaf [0,5,18,131,160,250,423,556,784,967,1099,1560]))
 (.branch 28
 (.leaf [0,5,87,121,161,338,448,557,794,967,1099,1496])
 (.branch 29
 (.leaf [0,22,154,163,250,817,1569])
 (.leaf [0,1,5,242,251,280,447,456,708,821,1413])))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf [0,1,87,221,251,274,447,450,708,821,1413])
 (.leaf [0,4,56,163,251,448]))
 (.branch 33
 (.leaf [0,1,72,160,248,445,793,875,938,1512])
 (.branch 34
 (.leaf [0,1,87,160,248,445,838,965,1053,1590])
 (.leaf [0,1,5,251,282,419,448,479,616,815,1402]))))
 (.branch 38
 (.branch 36
 (.leaf [0,2,8,249,415,446,612,804,1410])
 (.branch 37
 (.leaf [0,5,23,131,160,394,445,465,700,778,1506])
 (.leaf [0,136,163,251,616,725,811,1558])))
 (.branch 39
 (.leaf [0,1,5,242,248,364,445,540,756,901,1413])
 (.branch 40
 (.leaf [0,17,18,90,161,310,446,671,753,965,1508])
 (.leaf [0,1,87,221,248,358,445,534,756,901,1413])))))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 2 1 0 0 0 0 0 6 3
cert_nodeTest_4 288 05
cert_nodeTest_sound_3 288 05
cert_leafTest_5 05
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0864
