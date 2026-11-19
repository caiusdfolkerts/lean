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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0362
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 8084
abbrev nodeCount : Nat := 2597
abbrev leafCount : Nat := 25
cert_widths_3 13 12 6 5
def blocks : Table PackedRawNatGrowth.Block :=
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
 (.branch 18
 (.branch 16
 (.leaf ⟨((certNat% 30)),(certNat% 31)⟩)
 (.branch 17
 (.leaf ⟨((certNat% 32)),(certNat% 33)⟩)
 (.leaf ⟨((certNat% 34)),(certNat% 35)⟩)))
 (.branch 19
 (.leaf ⟨((certNat% 36)),(certNat% 37)⟩)
 (.branch 20
 (.leaf ⟨((certNat% 38)),(certNat% 39)⟩)
 (.leaf ⟨(certNat% 40),(certNat% 41)⟩))))))
def counterTable : Table Nat :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (certNat% 42))
 (.leaf (certNat% 43)))
 (.branch 3
 (.leaf (certNat% 44))
 (.branch 4
 (.leaf (certNat% 45))
 (.leaf (certNat% 46)))))
 (.branch 7
 (.branch 6
 (.leaf (certNat% 47))
 (.leaf (certNat% 48)))
 (.branch 8
 (.leaf (certNat% 49))
 (.branch 9
 (.leaf (certNat% 50))
 (.leaf (certNat% 51))))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf (certNat% 52))
 (.leaf (certNat% 53)))
 (.branch 13
 (.leaf (certNat% 54))
 (.branch 14
 (.leaf (certNat% 55))
 (.leaf (certNat% 56)))))
 (.branch 18
 (.branch 16
 (.leaf (certNat% 57))
 (.branch 17
 (.leaf (certNat% 58))
 (.leaf (certNat% 59))))
 (.branch 19
 (.leaf (certNat% 60))
 (.branch 20
 (.leaf (certNat% 61))
 (.leaf (certNat% 62)))))))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf [0,57,162,224,331,355,529,681,928,1057,1082])
 (.branch 2
 (.leaf [0,15,119,212,331,505,527,629,903,1046,1226,1297])
 (.leaf [0,15,143,188,330,505,528,684,850,903,1037,1107])))
 (.branch 4
 (.leaf [0,31,126,234,333,528,653,860,904,1055,1332])
 (.branch 5
 (.leaf [0,21,140,191,331,505,530,576,642,947,995,1294])
 (.leaf [0,21,163,191,331,337,530,642,856,947,995,1294]))))
 (.branch 9
 (.branch 7
 (.leaf [0,126,222,333,527,617,857,923,1057,1223,1255])
 (.branch 8
 (.leaf [0,93,162,222,333,529,658,855,922,1034,1082])
 (.leaf [0,162,222,333,529,615,844,922,1002,1086,1377])))
 (.branch 10
 (.leaf [0,5,103,330,530,598,679,696,905,1017,1251])
 (.branch 11
 (.leaf [0,41,162,198,333,529,658,860,943,1034,1085])
 (.leaf [0,1,175,330,530,547,614,667,926,1017,1231])))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf [0,21,163,215,330,338,530,615,843,926,1014,1376])
 (.branch 14
 (.leaf [0,63,139,226,333,355,529,681,855,925,1057])
 (.leaf [0,9,139,202,333,358,529,681,860,946,1057])))
 (.branch 16
 (.leaf [0,53,138,186,332,530,555,642,951,1033,1160,1275])
 (.branch 17
 (.leaf [0,63,102,225,333,398,527,660,787,929,1001,1127])
 (.leaf [0,21,162,200,331,358,529,681,949,1057,1085]))))
 (.branch 21
 (.branch 19
 (.leaf [0,1,201,333,356,529,532,630,951,1045,1181,1254])
 (.branch 20
 (.leaf [0,63,102,225,333,398,527,617,929,1057,1223,1255])
 (.leaf [0,5,154,248,333,443,530,630,845,1015,1378])))
 (.branch 23
 (.branch 22
 (.leaf [0,5,142,269,332,425,529,646,842,1027,1184])
 (.leaf [0,5,166,247,333,469,530,619,838,1039,1245]))
 (.branch 24
 (.leaf [0,6,154,333,482,530,660,854,1051])
 (.leaf [0,83,154,211,333,439,530,627,845,1015,1378]))))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 1 0 0 0 0 0 0 4 6
cert_nodeTest_5 48 02
cert_nodeTest_sound_4 48 02
cert_leafTest_4 02
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0362
