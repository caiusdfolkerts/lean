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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0248
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 8084
abbrev nodeCount : Nat := 2710
abbrev leafCount : Nat := 17
cert_widths_3 13 12 6 5
def blocks : Table PackedRawNatGrowth.Block :=
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
 (.leaf ⟨(certNat% 42),(certNat% 43)⟩))))))
def counterTable : Table Nat :=
(.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (certNat% 44))
 (.leaf (certNat% 45)))
 (.branch 3
 (.leaf (certNat% 46))
 (.branch 4
 (.leaf (certNat% 47))
 (.leaf (certNat% 48)))))
 (.branch 8
 (.branch 6
 (.leaf (certNat% 49))
 (.branch 7
 (.leaf (certNat% 50))
 (.leaf (certNat% 51))))
 (.branch 9
 (.leaf (certNat% 52))
 (.branch 10
 (.leaf (certNat% 53))
 (.leaf (certNat% 54))))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf (certNat% 55))
 (.leaf (certNat% 56)))
 (.branch 14
 (.leaf (certNat% 57))
 (.branch 15
 (.leaf (certNat% 58))
 (.leaf (certNat% 59)))))
 (.branch 19
 (.branch 17
 (.leaf (certNat% 60))
 (.branch 18
 (.leaf (certNat% 61))
 (.leaf (certNat% 62))))
 (.branch 20
 (.leaf (certNat% 63))
 (.branch 21
 (.leaf (certNat% 64))
 (.leaf (certNat% 65)))))))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf [0,15,143,188,330,505,528,903,1045,1107,6963])
 (.leaf [0,15,131,224,331,504,527,641,882,1312,7339]))
 (.branch 3
 (.leaf [0,126,222,333,527,660,923,1001,1127,6562])
 (.leaf [0,126,234,333,527,629,856,902,1270,7336])))
 (.branch 6
 (.branch 5
 (.leaf [0,21,163,191,331,337,530,624,947,1038,6580])
 (.leaf [0,31,126,234,333,528,657,860,904,7340]))
 (.branch 7
 (.leaf [0,21,163,191,331,337,530,646,856,947,7236])
 (.leaf [0,21,140,191,331,505,530,576,646,947,7236]))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf [0,53,138,186,332,530,555,642,951,1294,7172])
 (.leaf [0,63,102,225,333,398,527,929,1009,1127,6801]))
 (.branch 11
 (.leaf [0,1,201,333,356,529,532,630,951,1273,7226])
 (.leaf [0,63,114,237,333,397,527,629,908,1270,7336])))
 (.branch 14
 (.branch 13
 (.leaf [0,5,154,259,333,530,631,837,1051,5842])
 (.leaf [0,83,154,211,333,439,530,635,1015,6579]))
 (.branch 15
 (.leaf [0,1,175,530,556,660,854,1051,1234,6496])
 (.branch 16
 (.leaf [0,5,109,333,398,443,551,630,1015,1364,7144])
 (.leaf [0,1,183,333,377,459,535,654,1039,1363,7144]))))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 1 0 0 0 1 0 0 3 5
cert_nodeTest_5 48 02
cert_nodeTest_sound_4 48 02
cert_leafTest_4 02
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0248
