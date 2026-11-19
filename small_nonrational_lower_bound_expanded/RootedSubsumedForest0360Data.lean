module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0360
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 8084
abbrev nodeCount : Nat := 4725
abbrev leafCount : Nat := 55
cert_widths_3 13 13 6 6
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 18
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
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨((certNat% 18)),(certNat% 19)⟩)
 (.leaf ⟨((certNat% 20)),(certNat% 21)⟩))
 (.branch 12
 (.leaf ⟨((certNat% 22)),(certNat% 23)⟩)
 (.leaf ⟨((certNat% 24)),(certNat% 25)⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨((certNat% 26)),(certNat% 27)⟩)
 (.leaf ⟨((certNat% 28)),(certNat% 29)⟩))
 (.branch 16
 (.leaf ⟨((certNat% 30)),(certNat% 31)⟩)
 (.branch 17
 (.leaf ⟨((certNat% 32)),(certNat% 33)⟩)
 (.leaf ⟨((certNat% 34)),(certNat% 35)⟩))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf ⟨((certNat% 36)),(certNat% 37)⟩)
 (.leaf ⟨((certNat% 38)),(certNat% 39)⟩))
 (.branch 21
 (.leaf ⟨((certNat% 40)),(certNat% 41)⟩)
 (.leaf ⟨((certNat% 42)),(certNat% 43)⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨((certNat% 44)),(certNat% 45)⟩)
 (.leaf ⟨((certNat% 46)),(certNat% 47)⟩))
 (.branch 25
 (.leaf ⟨((certNat% 48)),(certNat% 49)⟩)
 (.branch 26
 (.leaf ⟨((certNat% 50)),(certNat% 51)⟩)
 (.leaf ⟨((certNat% 52)),(certNat% 53)⟩)))))
 (.branch 32
 (.branch 29
 (.branch 28
 (.leaf ⟨((certNat% 54)),(certNat% 55)⟩)
 (.leaf ⟨((certNat% 56)),(certNat% 57)⟩))
 (.branch 30
 (.leaf ⟨((certNat% 58)),(certNat% 59)⟩)
 (.branch 31
 (.leaf ⟨((certNat% 60)),(certNat% 61)⟩)
 (.leaf ⟨((certNat% 62)),(certNat% 63)⟩))))
 (.branch 34
 (.branch 33
 (.leaf ⟨((certNat% 64)),(certNat% 65)⟩)
 (.leaf ⟨((certNat% 66)),(certNat% 67)⟩))
 (.branch 35
 (.leaf ⟨((certNat% 68)),(certNat% 69)⟩)
 (.branch 36
 (.leaf ⟨((certNat% 70)),(certNat% 71)⟩)
 (.leaf ⟨((certNat% 72)),(certNat% 73)⟩)))))))
def counterTable : Table Nat :=
(.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (certNat% 74))
 (.leaf (certNat% 75)))
 (.branch 3
 (.leaf (certNat% 76))
 (.leaf (certNat% 77))))
 (.branch 6
 (.branch 5
 (.leaf (certNat% 78))
 (.leaf (certNat% 79)))
 (.branch 7
 (.leaf (certNat% 80))
 (.branch 8
 (.leaf (certNat% 81))
 (.leaf (certNat% 82))))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf (certNat% 83))
 (.leaf (certNat% 84)))
 (.branch 12
 (.leaf (certNat% 85))
 (.leaf (certNat% 86))))
 (.branch 15
 (.branch 14
 (.leaf (certNat% 87))
 (.leaf (certNat% 88)))
 (.branch 16
 (.leaf (certNat% 89))
 (.branch 17
 (.leaf (certNat% 90))
 (.leaf (certNat% 91)))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf (certNat% 92))
 (.leaf (certNat% 93)))
 (.branch 21
 (.leaf (certNat% 94))
 (.leaf (certNat% 95))))
 (.branch 24
 (.branch 23
 (.leaf (certNat% 96))
 (.leaf (certNat% 97)))
 (.branch 25
 (.leaf (certNat% 98))
 (.branch 26
 (.leaf (certNat% 99))
 (.leaf (certNat% 100))))))
 (.branch 32
 (.branch 29
 (.branch 28
 (.leaf (certNat% 101))
 (.leaf (certNat% 102)))
 (.branch 30
 (.leaf (certNat% 103))
 (.branch 31
 (.leaf (certNat% 104))
 (.leaf (certNat% 105)))))
 (.branch 34
 (.branch 33
 (.leaf (certNat% 106))
 (.leaf (certNat% 107)))
 (.branch 35
 (.leaf (certNat% 108))
 (.branch 36
 (.leaf (certNat% 109))
 (.leaf (certNat% 110))))))))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 27
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf [0,1,57,201,333,356,527,628,944,1054,1230,1258])
 (.branch 2
 (.leaf [0,2,58,211,331,529,531,676,903,1041,1229,1299])
 (.leaf [0,57,71,163,212,331,334,530,679,926,1017,1237])))
 (.branch 4
 (.leaf [0,57,93,162,224,331,355,529,680,927,1029,1229])
 (.branch 5
 (.leaf [0,1,71,187,330,530,577,679,902,1041,1236])
 (.leaf [0,22,68,150,203,332,379,528,619,857,948,1064]))))
 (.branch 9
 (.branch 7
 (.leaf [0,22,68,164,203,332,503,528,555,619,948,1064])
 (.branch 8
 (.leaf [0,17,93,166,188,330,503,530,678,902,1005,1320])
 (.leaf [0,18,67,106,189,332,505,528,618,945,1105,1280])))
 (.branch 11
 (.branch 10
 (.leaf [0,15,37,131,224,331,504,527,730,882,1006,1129])
 (.leaf [0,17,83,119,237,333,503,527,632,902,994,1128]))
 (.branch 12
 (.leaf [0,1,15,237,250,333,401,527,632,905,1018,1230])
 (.leaf [0,31,85,150,234,333,527,632,862,905,1018])))))
 (.branch 20
 (.branch 16
 (.branch 14
 (.leaf [0,1,31,190,333,380,481,528,656,858,904,1042])
 (.branch 15
 (.leaf [0,1,31,237,247,333,380,528,656,904,1042,1229])
 (.leaf [0,63,139,225,333,355,529,655,925,1054,1229])))
 (.branch 18
 (.branch 17
 (.leaf [0,9,27,141,201,333,379,528,619,947,1042,1231])
 (.leaf [0,9,53,115,225,333,359,529,655,925,1054,1229]))
 (.branch 19
 (.leaf [0,21,83,162,203,331,358,529,631,856,948,1029])
 (.leaf [0,1,189,332,335,530,553,643,946,1053,1230]))))
 (.branch 23
 (.branch 21
 (.leaf [0,21,83,152,203,331,504,529,576,631,948,1029])
 (.branch 22
 (.leaf [0,21,22,164,227,332,509,527,556,620,927,1006])
 (.leaf [0,27,101,117,178,332,483,530,556,667,925,1053])))
 (.branch 25
 (.branch 24
 (.leaf [0,27,28,129,190,333,489,528,536,656,904,1042])
 (.leaf [0,21,104,211,330,530,598,679,905,1017,1234]))
 (.branch 26
 (.leaf [0,83,153,174,333,482,529,534,631,946,1054])
 (.leaf [0,53,114,210,332,530,556,667,925,1053,1229]))))))
 (.branch 41
 (.branch 34
 (.branch 30
 (.branch 28
 (.leaf [0,6,34,153,333,482,529,655,946,1054])
 (.branch 29
 (.leaf [0,18,86,151,213,332,530,667,946,1053])
 (.leaf [0,9,41,139,201,333,358,529,655,946,1054,1234])))
 (.branch 32
 (.branch 31
 (.leaf [0,21,163,188,331,337,530,679,947,1041,1235])
 (.leaf [0,1,178,333,362,482,529,538,655,946,1054]))
 (.branch 33
 (.leaf [0,27,63,117,178,332,483,530,559,667,946,1053])
 (.leaf [0,5,21,151,248,331,530,631,837,944,1050,1064]))))
 (.branch 37
 (.branch 35
 (.leaf [0,6,90,153,333,482,528,652,944,1054])
 (.branch 36
 (.leaf [0,6,48,165,246,333,485,529,617,943,1042,1254])
 (.leaf [0,21,48,162,227,330,359,529,620,862,927,1002])))
 (.branch 39
 (.branch 38
 (.leaf [0,21,53,163,191,331,337,530,619,838,947,1038])
 (.leaf [0,18,91,151,213,332,530,666,951,1030]))
 (.branch 40
 (.leaf [0,5,93,103,330,530,598,678,691,908,1005,1320])
 (.leaf [0,10,38,138,201,333,379,528,693,950,1030,1106])))))
 (.branch 48
 (.branch 44
 (.branch 42
 (.leaf [0,1,83,201,333,356,529,532,631,951,1029,1085])
 (.branch 43
 (.leaf [0,63,83,139,225,333,355,529,655,930,1005,1086])
 (.leaf [0,53,84,138,186,332,530,555,643,951,1041,1064])))
 (.branch 46
 (.branch 45
 (.leaf [0,9,48,115,225,333,359,529,620,930,1002,1086])
 (.leaf [0,1,50,201,333,377,528,537,631,950,1025,1106]))
 (.branch 47
 (.leaf [0,1,67,189,332,335,530,553,642,951,1062,1279])
 (.leaf [0,1,93,189,332,335,530,553,642,951,1006,1279]))))
 (.branch 51
 (.branch 49
 (.leaf [0,63,94,139,225,333,355,529,654,930,1042,1257])
 (.branch 50
 (.leaf [0,5,21,166,253,333,485,530,619,838,1039])
 (.leaf [0,5,30,154,252,333,467,530,631,837,1051])))
 (.branch 53
 (.branch 52
 (.leaf [0,28,48,107,226,330,461,527,680,862,1004])
 (.leaf [0,23,53,130,175,333,530,655,816,1051,1237]))
 (.branch 54
 (.leaf [0,53,83,154,174,333,482,530,631,837,1051])
 (.leaf [0,27,98,143,191,331,441,528,640,776,1040])))))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 2 0 0 0 0 0 0 2 7
cert_nodeTest_5 48 02
cert_nodeTest_sound_4 48 02
cert_leafTest_4 02
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0360
