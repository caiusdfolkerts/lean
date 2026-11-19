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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0857
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2170
abbrev nodeCount : Nat := 3555
abbrev leafCount : Nat := 52
cert_widths_3 12 12 9 6
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 14
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
 (.branch 10
 (.branch 8
 (.leaf ⟨((certNat% 14)),(certNat% 15)⟩)
 (.branch 9
 (.leaf ⟨((certNat% 16)),(certNat% 17)⟩)
 (.leaf ⟨((certNat% 18)),(certNat% 19)⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨((certNat% 20)),(certNat% 21)⟩)
 (.leaf ⟨((certNat% 22)),(certNat% 23)⟩))
 (.branch 13
 (.leaf ⟨((certNat% 24)),(certNat% 25)⟩)
 (.leaf ⟨((certNat% 26)),(certNat% 27)⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨((certNat% 28)),(certNat% 29)⟩)
 (.branch 16
 (.leaf ⟨((certNat% 30)),(certNat% 31)⟩)
 (.leaf ⟨((certNat% 32)),(certNat% 33)⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨((certNat% 34)),(certNat% 35)⟩)
 (.leaf ⟨((certNat% 36)),(certNat% 37)⟩))
 (.branch 20
 (.leaf ⟨((certNat% 38)),(certNat% 39)⟩)
 (.leaf ⟨((certNat% 40)),(certNat% 41)⟩))))
 (.branch 24
 (.branch 22
 (.leaf ⟨((certNat% 42)),(certNat% 43)⟩)
 (.branch 23
 (.leaf ⟨((certNat% 44)),(certNat% 45)⟩)
 (.leaf ⟨((certNat% 46)),(certNat% 47)⟩)))
 (.branch 26
 (.branch 25
 (.leaf ⟨((certNat% 48)),(certNat% 49)⟩)
 (.leaf ⟨((certNat% 50)),(certNat% 51)⟩))
 (.branch 27
 (.leaf ⟨((certNat% 52)),(certNat% 53)⟩)
 (.leaf ⟨((certNat% 54)),(certNat% 55)⟩))))))
def counterTable : Table Nat :=
(.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf (certNat% 56))
 (.branch 2
 (.leaf (certNat% 57))
 (.leaf (certNat% 58))))
 (.branch 5
 (.branch 4
 (.leaf (certNat% 59))
 (.leaf (certNat% 60)))
 (.branch 6
 (.leaf (certNat% 61))
 (.leaf (certNat% 62)))))
 (.branch 10
 (.branch 8
 (.leaf (certNat% 63))
 (.branch 9
 (.leaf (certNat% 64))
 (.leaf (certNat% 65))))
 (.branch 12
 (.branch 11
 (.leaf (certNat% 66))
 (.leaf (certNat% 67)))
 (.branch 13
 (.leaf (certNat% 68))
 (.leaf (certNat% 69))))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf (certNat% 70))
 (.branch 16
 (.leaf (certNat% 71))
 (.leaf (certNat% 72))))
 (.branch 19
 (.branch 18
 (.leaf (certNat% 73))
 (.leaf (certNat% 74)))
 (.branch 20
 (.leaf (certNat% 75))
 (.leaf (certNat% 76)))))
 (.branch 24
 (.branch 22
 (.leaf (certNat% 77))
 (.branch 23
 (.leaf (certNat% 78))
 (.leaf (certNat% 79))))
 (.branch 26
 (.branch 25
 (.leaf (certNat% 80))
 (.leaf (certNat% 81)))
 (.branch 27
 (.leaf (certNat% 82))
 (.leaf (certNat% 83)))))))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 26
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf [0,17,19,36,125,161,251,276,447,713,788,931])
 (.branch 2
 (.leaf [0,17,18,137,162,167,249,448,599,706,812,910])
 (.leaf [0,1,17,34,160,251,280,400,447,450,708,814,827])))
 (.branch 4
 (.leaf [0,5,18,33,137,160,250,255,448,597,708,812,824])
 (.branch 5
 (.leaf [0,17,36,45,113,161,166,248,448,583,776,825])
 (.leaf [0,22,39,84,124,163,206,250,446,557,642,799,949]))))
 (.branch 9
 (.branch 7
 (.leaf [0,5,19,83,125,160,251,276,447,537,713,764,929])
 (.branch 8
 (.leaf [0,5,20,81,113,161,250,256,448,562,687,812,823])
 (.leaf [0,6,19,57,151,160,251,421,447,534,705,788,931])))
 (.branch 11
 (.branch 10
 (.leaf [0,9,17,64,114,161,248,422,448,597,685,812,826])
 (.leaf [0,5,18,57,137,160,250,255,448,561,713,800,910]))
 (.branch 12
 (.leaf [0,6,17,66,149,160,249,255,448,582,712,812,827])
 (.leaf [0,8,20,66,137,162,249,448,599,706,812])))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf [0,17,18,21,140,162,167,251,448,599,815,997])
 (.branch 15
 (.leaf [0,17,18,21,140,162,167,251,448,604,803,826])
 (.leaf [0,17,19,36,116,161,166,251,448,583,779,825])))
 (.branch 17
 (.leaf [0,17,19,39,92,163,207,249,446,600,804,993])
 (.branch 18
 (.leaf [0,17,19,23,129,163,209,249,446,600,804,993])
 (.leaf [0,2,18,87,162,167,249,359,446,598,804,868]))))
 (.branch 22
 (.branch 20
 (.leaf [0,3,17,33,160,171,250,401,447,598,816,851])
 (.branch 21
 (.leaf [0,6,17,30,92,162,249,380,447,620,707,814,931])
 (.leaf [0,7,17,49,91,163,249,379,448,492,712,813,910])))
 (.branch 24
 (.branch 23
 (.leaf [0,5,17,33,116,161,251,379,448,576,815,831])
 (.leaf [0,5,17,81,116,161,251,379,448,562,815,831]))
 (.branch 25
 (.leaf [0,17,23,87,128,161,250,380,447,598,816,847])
 (.leaf [0,17,23,81,128,161,250,380,447,533,816,852]))))))
 (.branch 39
 (.branch 32
 (.branch 29
 (.branch 27
 (.leaf [0,17,23,25,116,160,251,406,448,576,815,827])
 (.branch 28
 (.leaf [0,1,6,21,163,230,248,342,445,582,768,889])
 (.leaf [0,6,17,23,152,160,251,406,448,582,815,827])))
 (.branch 30
 (.leaf [0,17,152,161,167,251,385,448,603,815,826])
 (.branch 31
 (.leaf [0,22,38,152,162,251,448,815])
 (.leaf [0,8,21,26,152,161,251,448,600,803]))))
 (.branch 35
 (.branch 33
 (.leaf [0,19,39,87,101,163,186,248,448,515,688,777])
 (.branch 34
 (.leaf [0,5,7,20,150,161,250,425,446,473,710,790])
 (.leaf [0,2,18,87,162,167,248,275,447,514,689,765])))
 (.branch 37
 (.branch 36
 (.leaf [0,8,18,50,90,162,248,423,447,514,689,765])
 (.leaf [0,1,6,21,163,230,249,258,448,498,709,801]))
 (.branch 38
 (.leaf [0,19,39,49,89,160,251,295,448,519,579,779])
 (.leaf [0,11,34,63,137,160,166,248,448,604,670,800,825])))))
 (.branch 45
 (.branch 42
 (.branch 40
 (.leaf [0,2,8,62,162,249,401,446,598,804])
 (.branch 41
 (.leaf [0,3,8,9,163,250,402,447,599,816])
 (.leaf [0,1,5,23,161,251,301,403,446,451,709,802])))
 (.branch 43
 (.leaf [0,5,6,23,139,162,251,402,447,452,708,814])
 (.branch 44
 (.leaf [0,5,7,14,150,161,249,425,448,557,709,800])
 (.leaf [0,1,5,87,161,251,295,360,446,451,709,802]))))
 (.branch 48
 (.branch 46
 (.leaf [0,13,39,87,101,163,186,251,447,599,687,811])
 (.branch 47
 (.leaf [0,8,14,137,162,250,448,599,708,812])
 (.leaf [0,1,5,8,162,251,280,402,447,456,708,814])))
 (.branch 50
 (.branch 49
 (.leaf [0,23,87,128,163,188,250,381,447,599,816])
 (.leaf [0,23,39,104,163,192,250,402,447,599,816]))
 (.branch 51
 (.leaf [0,8,140,162,251,402,448,599,815])
 (.leaf [0,4,56,163,251,448])))))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 3 0 0 0 0 0 0 3 6
cert_nodeTest_4 288 05
cert_nodeTest_sound_3 288 05
cert_leafTest_5 05
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0857
