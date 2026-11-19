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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0245
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 15246
abbrev nodeCount : Nat := 4011
abbrev leafCount : Nat := 10
cert_widths_3 14 12 6 4
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 16
 (.branch 8
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
 (.leaf ⟨((certNat% 14)),(certNat% 15)⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨((certNat% 16)),(certNat% 17)⟩)
 (.leaf ⟨((certNat% 18)),(certNat% 19)⟩))
 (.branch 11
 (.leaf ⟨((certNat% 20)),(certNat% 21)⟩)
 (.leaf ⟨((certNat% 22)),(certNat% 23)⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨((certNat% 24)),(certNat% 25)⟩)
 (.leaf ⟨((certNat% 26)),(certNat% 27)⟩))
 (.branch 15
 (.leaf ⟨((certNat% 28)),(certNat% 29)⟩)
 (.leaf ⟨((certNat% 30)),(certNat% 31)⟩)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ⟨((certNat% 32)),(certNat% 33)⟩)
 (.leaf ⟨((certNat% 34)),(certNat% 35)⟩))
 (.branch 19
 (.leaf ⟨((certNat% 36)),(certNat% 37)⟩)
 (.leaf ⟨((certNat% 38)),(certNat% 39)⟩)))
 (.branch 22
 (.branch 21
 (.leaf ⟨((certNat% 40)),(certNat% 41)⟩)
 (.leaf ⟨((certNat% 42)),(certNat% 43)⟩))
 (.branch 23
 (.leaf ⟨((certNat% 44)),(certNat% 45)⟩)
 (.leaf ⟨((certNat% 46)),(certNat% 47)⟩))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ⟨((certNat% 48)),(certNat% 49)⟩)
 (.leaf ⟨((certNat% 50)),(certNat% 51)⟩))
 (.branch 27
 (.leaf ⟨((certNat% 52)),(certNat% 53)⟩)
 (.leaf ⟨((certNat% 54)),(certNat% 55)⟩)))
 (.branch 30
 (.branch 29
 (.leaf ⟨((certNat% 56)),(certNat% 57)⟩)
 (.leaf ⟨((certNat% 58)),(certNat% 59)⟩))
 (.branch 31
 (.leaf ⟨((certNat% 60)),(certNat% 61)⟩)
 (.leaf ⟨(certNat% 62),(certNat% 63)⟩))))))
def counterTable : Table Nat :=
(.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (certNat% 64))
 (.leaf (certNat% 65)))
 (.branch 3
 (.leaf (certNat% 66))
 (.leaf (certNat% 67))))
 (.branch 6
 (.branch 5
 (.leaf (certNat% 68))
 (.leaf (certNat% 69)))
 (.branch 7
 (.leaf (certNat% 70))
 (.leaf (certNat% 71)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (certNat% 72))
 (.leaf (certNat% 73)))
 (.branch 11
 (.leaf (certNat% 74))
 (.leaf (certNat% 75))))
 (.branch 14
 (.branch 13
 (.leaf (certNat% 76))
 (.leaf (certNat% 77)))
 (.branch 15
 (.leaf (certNat% 78))
 (.leaf (certNat% 79))))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf (certNat% 80))
 (.leaf (certNat% 81)))
 (.branch 19
 (.leaf (certNat% 82))
 (.leaf (certNat% 83))))
 (.branch 22
 (.branch 21
 (.leaf (certNat% 84))
 (.leaf (certNat% 85)))
 (.branch 23
 (.leaf (certNat% 86))
 (.leaf (certNat% 87)))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf (certNat% 88))
 (.leaf (certNat% 89)))
 (.branch 27
 (.leaf (certNat% 90))
 (.leaf (certNat% 91))))
 (.branch 30
 (.branch 29
 (.leaf (certNat% 92))
 (.leaf (certNat% 93)))
 (.branch 31
 (.leaf (certNat% 94))
 (.leaf (certNat% 95)))))))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf [0,35,121,243,372,586,767,850,857,1030,14307])
 (.leaf [0,35,150,224,319,406,766,858,992,1119,13741]))
 (.branch 3
 (.leaf [0,35,150,225,298,394,767,857,1030,1467,14307])
 (.branch 4
 (.leaf [0,57,125,213,355,649,768,898,1005,1179,13757])
 (.leaf [0,35,224,415,766,858,988,1119,1455,1614,12141]))))
 (.branch 7
 (.branch 6
 (.leaf [0,35,224,415,766,858,1010,1149,1467,1531,12141])
 (.leaf [0,35,131,216,411,585,768,875,1033,1575,14195]))
 (.branch 8
 (.leaf [0,1,365,618,768,894,1026,1170,1365,12618])
 (.branch 9
 (.leaf [0,1,377,625,767,1016,1156,1362,1463,12619])
 (.leaf [0,35,121,372,597,767,857,1022,1149,1552,12720])))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 1 0 0 0 1 0 0 4 4
cert_nodeTest_5 48 01
cert_nodeTest_sound_4 48 01
cert_leafTest_4 01
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0245
