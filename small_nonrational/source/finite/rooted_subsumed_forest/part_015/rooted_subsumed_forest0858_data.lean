module
prelude
public import RootedSixExtra06GrowthCacheData
public import RootedSixExtra06FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0858Packed000
public import RootedSubsumedForest0858Packed001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0858
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2300
abbrev nodeCount : Nat := 12137
abbrev leafCount : Nat := 50
def widths : PackedRawNatGrowth.Widths := ⟨12,14,8,6⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 50
 nodeBlocks000
 nodeBlocks001)
def counterTable : Table Nat :=
(.branch 50
 nodeCounters000
 nodeCounters001)
def codes (i : Nat) : Nat :=
  let b := blocks.get (i / 128)
  PackedRawNatGrowth.drop
    (PackedRawNatGrowth.take 32 (PackedRawNatGrowth.drop (32*(i%128)) b.offsets)) b.payload
def counters (i : Nat) : Nat :=
  PackedRawNatGrowth.take 55 (PackedRawNatGrowth.drop (55*(i%128)) (counterTable.get (i/128)))
def rawNodes (i : Nat) := PackedRawNatGrowth.decodeNode widths (codes i)

def leafTable : Table (List Nat) :=
(.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf [0,1,8,11,222,424,555,750,840,971,1082,1390,2297])
 (.branch 2
 (.leaf [0,3,5,21,222,276,591,707,840,1013,1336,1430,2297])
 (.leaf [0,1,8,205,290,484,555,749,860,1018,2298])))
 (.branch 4
 (.leaf [0,1,11,44,214,258,465,531,832,962,1191,2298])
 (.branch 5
 (.leaf [0,2,22,43,236,257,302,579,821,963,1192,2296])
 (.leaf [0,1,23,47,200,275,543,749,861,1019,1432,2299]))))
 (.branch 9
 (.branch 7
 (.leaf [0,5,12,42,155,420,592,773,812,970,1172,2296])
 (.branch 8
 (.leaf [0,7,11,47,107,461,567,728,861,1019,1108,2299])
 (.leaf [0,1,22,32,222,263,625,751,837,995,1434,2298])))
 (.branch 10
 (.leaf [0,1,15,63,182,302,560,743,857,1196,2298])
 (.branch 11
 (.leaf [0,5,23,33,146,326,510,687,859,972,1271,2296])
 (.leaf [0,6,12,88,147,423,576,688,816,1002,1358,2296])))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf [0,6,12,109,421,543,855,1002,1194,1402,2298])
 (.branch 14
 (.leaf [0,7,12,53,110,442,564,707,1017,1183,1279,2299])
 (.leaf [0,5,27,54,122,331,497,588,686,996,1280,2297])))
 (.branch 16
 (.leaf [0,1,14,44,184,383,485,543,859,996,1292,2297])
 (.branch 17
 (.leaf [0,7,12,33,153,194,442,728,856,998,1188,2299])
 (.leaf [0,1,24,182,266,543,855,1002,1194,1402,2298]))))
 (.branch 21
 (.branch 19
 (.leaf [0,5,13,41,177,236,421,556,796,987,1196,2297])
 (.branch 20
 (.leaf [0,16,32,64,142,223,290,750,844,1192,2299])
 (.leaf [0,1,12,53,225,365,486,543,986,1208,2298])))
 (.branch 23
 (.branch 22
 (.leaf [0,1,27,54,203,278,484,555,1010,1189,2299])
 (.leaf [0,1,27,54,203,277,492,555,974,1446,2299]))
 (.branch 24
 (.leaf [0,1,15,53,182,319,499,543,1011,1194,2298])
 (.leaf [0,10,12,32,147,485,750,849,1007,2299]))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf [0,23,27,32,147,223,264,750,849,1007,1433,2299])
 (.branch 27
 (.leaf [0,9,16,51,146,293,506,539,749,981,1259,2299])
 (.leaf [0,1,27,32,227,266,485,604,750,849,1007,2299])))
 (.branch 29
 (.leaf [0,2,11,56,248,340,464,567,725,825,983,2299])
 (.branch 30
 (.leaf [0,1,16,85,184,331,497,543,748,856,996,2297])
 (.leaf [0,1,27,47,206,278,484,543,749,861,1019,2299]))))
 (.branch 34
 (.branch 32
 (.leaf [0,11,27,45,120,249,446,568,849,1007,1109,2299])
 (.branch 33
 (.leaf [0,4,24,44,248,327,592,836,994,2297])
 (.leaf [0,2,22,83,184,302,567,727,856,980,1163,2296])))
 (.branch 35
 (.leaf [0,2,22,57,186,267,532,727,852,978,1381,2298])
 (.branch 36
 (.leaf [0,3,28,81,247,269,382,591,704,821,957,2297])
 (.leaf [0,5,21,53,139,297,587,707,1012,1282,1343,2297])))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf [0,3,55,71,249,303,439,568,704,825,983,2299])
 (.branch 39
 (.leaf [0,1,11,84,233,473,555,746,840,974,1388,2298])
 (.leaf [0,2,12,80,564,859,1001,1292,2297])))
 (.branch 41
 (.leaf [0,5,29,52,121,329,447,531,950,1162,2297])
 (.branch 42
 (.leaf [0,5,27,61,145,279,584,720,821,1197,2296])
 (.leaf [0,28,42,61,156,221,267,592,809,1195,2296]))))
 (.branch 46
 (.branch 44
 (.leaf [0,5,22,51,157,327,513,532,963,1199,2296])
 (.branch 45
 (.leaf [0,5,29,52,121,326,442,531,999,1195,2297])
 (.leaf [0,5,27,51,145,331,476,532,975,1196,2296])))
 (.branch 48
 (.branch 47
 (.leaf [0,6,21,88,170,315,509,575,729,800,958,2296])
 (.leaf [0,5,29,44,134,327,421,592,775,836,994,2297]))
 (.branch 49
 (.leaf [0,7,27,47,110,302,463,567,728,861,1019,2299])
 (.leaf [0,7,87,101,171,298,465,563,730,800,958,2296])))))))
def rawLeaves := leafTable.get

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 3
  | 2 => 6
  | 3 => 2
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 0
  | 10 => 1
  | _ => 0

def nodeTest (i : Nat) : Bool :=
  SubsumedCounterReplay.check widths cellCount 1024 240 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixExtra06.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixExtra06.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixExtra06.kindMasks Papers.RationalityTen.RootedCaches.RootedSixExtra06.keys Papers.RationalityTen.RootedCaches.RootedSixExtra06.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixExtra06.Generators.FastWords.rawMaps rawLeaves codes counters i
theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 240 leafCount nodeCount (rawNodes i) = true ∧
      SubsumedRawGrowth.nodeCheck Papers.RationalityTen.RootedCaches.RootedSixExtra06.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixExtra06.badMasks
        Papers.RationalityTen.RootedCaches.RootedSixExtra06.kindMasks Papers.RationalityTen.RootedCaches.RootedSixExtra06.keys Papers.RationalityTen.RootedCaches.RootedSixExtra06.fastKind quota
        Papers.RationalityTen.FacetUniverses.RootedSixExtra06.Generators.FastWords.rawMaps rawLeaves rawNodes i = true :=
  SubsumedCounterReplay.check_sound widths cellCount 1024 240 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixExtra06.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixExtra06.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixExtra06.kindMasks Papers.RationalityTen.RootedCaches.RootedSixExtra06.keys Papers.RationalityTen.RootedCaches.RootedSixExtra06.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixExtra06.Generators.FastWords.rawMaps rawLeaves codes counters i h
def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.RootedSixExtra06.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0858
