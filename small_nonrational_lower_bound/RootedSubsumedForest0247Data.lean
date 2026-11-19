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
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0247
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 8084
abbrev nodeCount : Nat := 2267
abbrev leafCount : Nat := 13
cert_widths_3 13 12 6 4
def blocks : Table PackedRawNatGrowth.Block :=
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
def counterTable : Table Nat :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (certNat% 36))
 (.leaf (certNat% 37)))
 (.branch 3
 (.leaf (certNat% 38))
 (.leaf (certNat% 39))))
 (.branch 6
 (.branch 5
 (.leaf (certNat% 40))
 (.leaf (certNat% 41)))
 (.branch 7
 (.leaf (certNat% 42))
 (.branch 8
 (.leaf (certNat% 43))
 (.leaf (certNat% 44))))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf (certNat% 45))
 (.leaf (certNat% 46)))
 (.branch 12
 (.leaf (certNat% 47))
 (.leaf (certNat% 48))))
 (.branch 15
 (.branch 14
 (.leaf (certNat% 49))
 (.leaf (certNat% 50)))
 (.branch 16
 (.leaf (certNat% 51))
 (.branch 17
 (.leaf (certNat% 52))
 (.leaf (certNat% 53)))))))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf [0,1,178,332,338,483,667,857,940,1053,4795])
 (.branch 2
 (.leaf [0,1,213,269,332,338,667,940,1053,1229,4795])
 (.leaf [0,1,175,530,556,667,942,1053,1236,3660])))
 (.branch 4
 (.leaf [0,83,151,174,331,631,861,958,1029,4842])
 (.branch 5
 (.leaf [0,5,162,268,529,619,839,943,1026,1100,3683])
 (.leaf [0,1,177,331,357,628,944,1029,1232,1313,4782]))))
 (.branch 9
 (.branch 7
 (.leaf [0,5,152,289,331,444,630,901,994,1311,4835])
 (.branch 8
 (.leaf [0,127,175,330,654,860,902,993,1332,4835])
 (.leaf [0,21,104,223,330,675,882,1005,1235,1335,4818])))
 (.branch 11
 (.branch 10
 (.leaf [0,83,165,210,333,460,615,922,1018,1269,4803])
 (.leaf [0,53,102,211,331,676,903,1041,1229,1316,4770]))
 (.branch 12
 (.leaf [0,83,154,174,333,482,631,861,1055,4835])
 (.leaf [0,27,118,178,332,483,667,861,1056,4834])))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 1 0 1 0 0 0 0 2 6
cert_nodeTest_5 48 02
cert_nodeTest_sound_4 48 02
cert_leafTest_4 02
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0247
