module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0350
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 15246
abbrev nodeCount : Nat := 3295
abbrev leafCount : Nat := 17
cert_widths_3 14 12 6 5
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
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf [0,35,121,243,372,586,767,850,857,1022,1149,1552])
 (.leaf [0,1,248,282,372,616,767,922,1030,1186,1231]))
 (.branch 3
 (.leaf [0,35,126,248,300,396,767,901,1030,1186,1215])
 (.leaf [0,35,150,224,319,406,766,858,988,1119,1455,1614])))
 (.branch 6
 (.branch 5
 (.leaf [0,35,150,225,298,394,767,857,1022,1149,1467,1552])
 (.leaf [0,57,160,249,390,614,768,899,964,1143,1455,1614]))
 (.branch 7
 (.leaf [0,1,216,388,464,582,654,708,768,936,1014,1182])
 (.leaf [0,1,216,392,459,661,694,768,960,1005,1180,1466]))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf [0,39,160,252,368,498,637,768,942,969,1168,1424])
 (.leaf [0,19,142,250,387,589,657,768,988,1117,1124,1532]))
 (.branch 11
 (.leaf [0,1,216,396,429,607,657,724,768,1024,1161,1575])
 (.leaf [0,35,131,216,411,585,768,875,1033,1127,1294,1556])))
 (.branch 14
 (.branch 13
 (.leaf [0,71,154,252,399,584,629,768,914,1021,1279,1514])
 (.leaf [0,35,116,245,401,768,878,1024,1137,1365,1554]))
 (.branch 15
 (.leaf [0,1,247,297,348,630,768,915,1014,1182,1365])
 (.branch 16
 (.leaf [0,1,258,317,372,625,767,1016,1156,1362,1463])
 (.leaf [0,1,245,266,360,581,625,768,919,1031,1187]))))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 1 0 0 0 0 0 0 5 5
cert_nodeTest_5 48 01
cert_nodeTest_sound_4 48 01
cert_leafTest_4 01
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0350
