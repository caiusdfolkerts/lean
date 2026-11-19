module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0716
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 5238
abbrev nodeCount : Nat := 3766
abbrev leafCount : Nat := 30
cert_widths_3 13 12 7 5
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
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf ⟨((certNat% 30)),(certNat% 31)⟩)
 (.branch 17
 (.leaf ⟨((certNat% 32)),(certNat% 33)⟩)
 (.leaf ⟨((certNat% 34)),(certNat% 35)⟩)))
 (.branch 20
 (.branch 19
 (.leaf ⟨((certNat% 36)),(certNat% 37)⟩)
 (.leaf ⟨((certNat% 38)),(certNat% 39)⟩))
 (.branch 21
 (.leaf ⟨((certNat% 40)),(certNat% 41)⟩)
 (.leaf ⟨((certNat% 42)),(certNat% 43)⟩))))
 (.branch 26
 (.branch 24
 (.branch 23
 (.leaf ⟨((certNat% 44)),(certNat% 45)⟩)
 (.leaf ⟨((certNat% 46)),(certNat% 47)⟩))
 (.branch 25
 (.leaf ⟨((certNat% 48)),(certNat% 49)⟩)
 (.leaf ⟨((certNat% 50)),(certNat% 51)⟩)))
 (.branch 28
 (.branch 27
 (.leaf ⟨((certNat% 52)),(certNat% 53)⟩)
 (.leaf ⟨((certNat% 54)),(certNat% 55)⟩))
 (.branch 29
 (.leaf ⟨((certNat% 56)),(certNat% 57)⟩)
 (.leaf ⟨(certNat% 58),(certNat% 59)⟩))))))
def counterTable : Table Nat :=
(.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf (certNat% 60))
 (.branch 2
 (.leaf (certNat% 61))
 (.leaf (certNat% 62))))
 (.branch 5
 (.branch 4
 (.leaf (certNat% 63))
 (.leaf (certNat% 64)))
 (.branch 6
 (.leaf (certNat% 65))
 (.leaf (certNat% 66)))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf (certNat% 67))
 (.leaf (certNat% 68)))
 (.branch 10
 (.leaf (certNat% 69))
 (.leaf (certNat% 70))))
 (.branch 13
 (.branch 12
 (.leaf (certNat% 71))
 (.leaf (certNat% 72)))
 (.branch 14
 (.leaf (certNat% 73))
 (.leaf (certNat% 74))))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf (certNat% 75))
 (.branch 17
 (.leaf (certNat% 76))
 (.leaf (certNat% 77))))
 (.branch 20
 (.branch 19
 (.leaf (certNat% 78))
 (.leaf (certNat% 79)))
 (.branch 21
 (.leaf (certNat% 80))
 (.leaf (certNat% 81)))))
 (.branch 26
 (.branch 24
 (.branch 23
 (.leaf (certNat% 82))
 (.leaf (certNat% 83)))
 (.branch 25
 (.leaf (certNat% 84))
 (.leaf (certNat% 85))))
 (.branch 28
 (.branch 27
 (.leaf (certNat% 86))
 (.leaf (certNat% 87)))
 (.branch 29
 (.leaf (certNat% 88))
 (.leaf (certNat% 89)))))))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf [0,1,5,347,370,475,542,710,1012,1289,1608])
 (.branch 2
 (.leaf [0,1,97,203,346,392,566,698,1025,1265,1609])
 (.leaf [0,1,62,204,347,394,495,545,738,940,1058,1280])))
 (.branch 5
 (.branch 4
 (.leaf [0,1,62,251,261,347,394,545,738,1058,1280,1467])
 (.leaf [0,1,111,216,346,395,495,544,750,939,976,1265]))
 (.branch 6
 (.leaf [0,1,251,261,347,394,544,735,988,1289,1609])
 (.leaf [0,1,82,239,262,347,373,556,736,991,1320,1494]))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf [0,1,111,250,282,346,395,544,750,976,1265,1467])
 (.leaf [0,1,85,238,303,345,374,556,762,967,1242,1474]))
 (.branch 10
 (.leaf [0,1,97,251,261,347,394,544,738,991,1230,1345])
 (.leaf [0,1,62,216,345,375,496,569,757,1182,1266])))
 (.branch 13
 (.branch 12
 (.leaf [0,1,114,204,347,397,495,557,733,1024,1277])
 (.leaf [0,2,41,225,345,567,680,817,1014,1253,1366]))
 (.branch 14
 (.leaf [0,27,61,121,228,344,476,568,761,945,1254])
 (.leaf [0,4,97,236,347,591,697,1022,1241,1365,1607])))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf [0,1,77,213,344,577,660,759,965,1254,1609])
 (.branch 17
 (.leaf [0,4,57,236,347,555,679,699,1024,1277,1607])
 (.leaf [0,28,66,118,240,344,475,593,757,1025,1209,1243])))
 (.branch 20
 (.branch 19
 (.leaf [0,16,98,117,203,346,590,701,1026,1209,1277,1344])
 (.leaf [0,31,114,128,251,347,411,711,1012,1124,1289]))
 (.branch 21
 (.leaf [0,31,41,116,239,347,412,771,1027,1122,1241,1365])
 (.leaf [0,77,128,251,347,411,542,711,1012,1289,1607]))))
 (.branch 26
 (.branch 24
 (.branch 23
 (.leaf [0,77,112,152,251,347,390,541,738,988,1277,1467])
 (.leaf [0,77,97,116,239,347,412,554,702,1027,1241,1365]))
 (.branch 25
 (.leaf [0,27,120,203,346,413,590,700,1025,1241,1607])
 (.leaf [0,27,108,130,229,344,455,582,746,1011,1039,1255])))
 (.branch 28
 (.branch 27
 (.leaf [0,32,43,164,248,347,922,1012,1289])
 (.leaf [0,58,77,116,237,345,554,723,1001,1278,1610]))
 (.branch 29
 (.leaf [0,57,58,140,236,347,556,736,988,1277,1610])
 (.leaf [0,57,58,153,237,345,555,723,1001,1278,1610]))))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 2 0 0 0 0 0 0 1 8
cert_nodeTest_5 96 03
cert_nodeTest_sound_4 96 03
cert_leafTest_4 03
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0716
