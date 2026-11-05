module
prelude
public import RootedSixBase03GrowthCacheData
public import RootedSixBase03FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0723Packed000
public import RootedSubsumedForest0723Packed001
public import RootedSubsumedForest0723Packed002

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0723
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 5238
abbrev nodeCount : Nat := 16182
abbrev leafCount : Nat := 146
def widths : PackedRawNatGrowth.Widths := ⟨13,14,7,8⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 50
 nodeBlocks000
 (.branch 100
 nodeBlocks001
 nodeBlocks002))
def counterTable : Table Nat :=
(.branch 50
 nodeCounters000
 (.branch 100
 nodeCounters001
 nodeCounters002))
def codes (i : Nat) : Nat :=
  let b := blocks.get (i / 128)
  PackedRawNatGrowth.drop
    (PackedRawNatGrowth.take 32 (PackedRawNatGrowth.drop (32*(i%128)) b.offsets)) b.payload
def counters (i : Nat) : Nat :=
  PackedRawNatGrowth.take 55 (PackedRawNatGrowth.drop (55*(i%128)) (counterTable.get (i/128)))
def rawNodes (i : Nat) := PackedRawNatGrowth.decodeNode widths (codes i)

def leafTable : Table Nat :=
(.branch 73
 (.branch 36
 (.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf 0x64a27e10c47ca2dd11607082b20d10078004000c)
 (.leaf 0x6462670f745ce25a0d686042b00e600a800c000c))
 (.branch 3
 (.leaf 0xc7653126c100c57c22a0d785b02b60ef0048004000d)
 (.leaf 0x5a528112e47f22cc12d071c2b20810078014000c)))
 (.branch 6
 (.branch 5
 (.leaf 0x50b22d8ff47562eb11087b02ba15a06e8004000c)
 (.leaf 0x4e91f00eb059422210185c42b60e90318008000c))
 (.branch 7
 (.leaf 0x64229c93b481e35018008a42b209901e8018000c)
 (.branch 8
 (.leaf 0x4fd2000edc74222d0ec861c2b60c50150004000c)
 (.leaf 0x64227290004ee2340ec06702b60c40148008000c)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf 0x53728292b481e3aa16a89802b008101f0014000c)
 (.leaf 0x53a2770fd85942360b985642280eb0308004000c))
 (.branch 12
 (.leaf 0x60d296101057c22a0c3856c2500f60288004000c)
 (.leaf 0x5c22808fe059421e0b9056c27a10202d8004000c)))
 (.branch 15
 (.branch 14
 (.leaf 0x5bb2808fe05c42210b9056c27a10201c8004000c)
 (.leaf 0x5bc2748f8059426a0b8856c2a410200f8008000c))
 (.branch 16
 (.leaf 0x64227290004ee2340ce056c2540de0148008000c)
 (.branch 17
 (.leaf 0x59028712e480a2c012707702b40830118014000c)
 (.leaf 0x5162428fac64a2f311e05742b40cb0290004000c))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf 0x6432a793b88b63fd10f05742b40cb0148004000c)
 (.leaf 0x5cb2ce93fc8b240911505782b20bf0148004000c))
 (.branch 21
 (.leaf 0x60f2e415789d23ea11505782b20bf0148004000c)
 (.leaf 0x63d2d014cca1e3ea11505782b20bf0148004000c)))
 (.branch 24
 (.branch 23
 (.leaf 0x15989f440312106702b60ef0150008000a)
 (.leaf 0x143880a2f212b06742b40e30320008000a))
 (.branch 25
 (.leaf 0x63a2a413d07ee2c211305c82b60d70308004000c)
 (.branch 26
 (.leaf 0x15548062e612506702b60ef0298008000a)
 (.leaf 0x51628412bc7f62ce11905782b20bf0370004000c)))))
 (.branch 31
 (.branch 29
 (.branch 28
 (.leaf 0x5ba27c12dc8022da11f071c2b20770220014000c)
 (.leaf 0x56527c92d87ee2ce119076c2b608f0250014000c))
 (.branch 30
 (.leaf 0x53c26b0fdc59027412585c82b60d70378004000c)
 (.leaf 0x5cb2ce8f445da2b313185782b00be0288008000c)))
 (.branch 33
 (.branch 32
 (.leaf 0x63d299941c7d42d514f098c2bc15905f8004000c)
 (.leaf 0x50d25d10106222e8110876c2b608f0250014000c))
 (.branch 34
 (.leaf 0x58e28b0fac5b028912b85742b40cb0290004000c)
 (.branch 35
 (.leaf 0x5a327b0fb47622d812e06c82b20780130014000c)
 (.leaf 0x4ff22c90246a030011685782b20c001c8004000c)))))))
 (.branch 54
 (.branch 45
 (.branch 40
 (.branch 38
 (.branch 37
 (.leaf 0x50f22e8fc475c2fb11085c82b60d801b0004000c)
 (.leaf 0x323141c8ba3f116e08782e415b06d8004000b))
 (.branch 39
 (.leaf 0x64127e9000650275126061c2b60db0150004000c)
 (.leaf 0x143480835212286702b60f30158008000a)))
 (.branch 42
 (.branch 41
 (.leaf 0x5562570fe867a2dd116861c2b60db0290004000c)
 (.leaf 0x50c2240f6464c2c611105c42b60f30318008000c))
 (.branch 43
 (.leaf 0x5011fc0ef45c42870f786282b60cc0100004000c)
 (.branch 44
 (.leaf 0x6492a694487b62e810e85842b00e700b0008000c)
 (.leaf 0x58c26e8f505e02380b005682360e30308004000c)))))
 (.branch 49
 (.branch 47
 (.branch 46
 (.leaf 0x50b22d8ff45d62210b185682a61030048004000c)
 (.leaf 0x50d23910105bc2240fb06342b60c000d8004000c))
 (.branch 48
 (.leaf 0x287121c80a2eb11206302b411a07d0004000b)
 (.leaf 0xbf44f42248f8069e2bb0c605682340fe00f8004000d)))
 (.branch 51
 (.branch 50
 (.leaf 0x28710145da2390fa86302b411f0030004000b)
 (.leaf 0x5ce28691888082c60e706702b607700f8014000c))
 (.branch 52
 (.leaf 0x5cf29a92b88703fa16e88b42b00c90290004000c)
 (.branch 53
 (.leaf 0x5b52630fa45f622d0bd856425e0ee0290004000c)
 (.leaf 0x50d26290105c222d0f805e82b60c001c8004000c))))))
 (.branch 63
 (.branch 58
 (.branch 56
 (.branch 55
 (.leaf 0x5cd2808fe05c42210f2856c20a08f027001c000c)
 (.leaf 0x2848f7070a2e10fd856c29e08c00f8018000b))
 (.branch 57
 (.leaf 0x4dc20e8f305782520d485682a20c801c8010000c)
 (.leaf 0x324136878a33a17f8a244ae1580028004000b)))
 (.branch 60
 (.branch 59
 (.leaf 0x3241530a223cf1930bd04401580028004000b)
 (.leaf 0x3241534a2442f1fe8b1843c1580028004000b))
 (.branch 61
 (.leaf 0x1588a243f615a09902b20e10158008000a)
 (.branch 62
 (.leaf 0x324939878a33b18009042b00810268014000b)
 (.leaf 0x63b29893608062b915c09302b60ec0378010000c)))))
 (.branch 68
 (.branch 65
 (.branch 64
 (.leaf 0x5be27a11687f82ba15089002b40c8038000c000c)
 (.leaf 0x2e313687682fa11605601da07901e8054000b))
 (.branch 66
 (.leaf 0x3249534a243db16f08802b00bd0308004000b)
 (.branch 67
 (.leaf 0x306934c84e40415f88a82b20740278018000b)
 (.leaf 0x6422b114488623e516389a82b20e100f8008000c))))
 (.branch 70
 (.branch 69
 (.leaf 0x56228912247ec3bd1638a1c2b20e100f8008000c)
 (.leaf 0x62426d90d47f03bd16f8a1c2b00c90100004000c))
 (.branch 71
 (.leaf 0x56627d13148062bb14188a82b60ec0378010000c)
 (.branch 72
 (.leaf 0x326136878a3b417c09402b00c90118004000b)
 (.leaf 0x268925c7902c8141097c2b20bc01d8008000b))))))))
 (.branch 109
 (.branch 91
 (.branch 82
 (.branch 77
 (.branch 75
 (.branch 74
 (.leaf 0x32493387ba2e014f89902b00bd01c8004000b)
 (.leaf 0x3249534a243db16f88802b00c901c8004000b))
 (.branch 76
 (.leaf 0x54f277116c7fa3ac15e09182b40c8038000c000c)
 (.leaf 0x6382a313ec78c3a417f09a82b00c90100004000c)))
 (.branch 79
 (.branch 78
 (.leaf 0x5bc27390bc7fa3a417f09a82b00c90100004000c)
 (.leaf 0x5c528692f08082bd121056c1ae07502f0044000c))
 (.branch 80
 (.leaf 0x5b826f12e07aa2f012c856017c0a5030803c000c)
 (.branch 81
 (.leaf 0x27491b87c02c8124056c1ae07501c8044000b)
 (.leaf 0x53a27712e47ec38f131056417e081014803c000c)))))
 (.branch 86
 (.branch 84
 (.branch 83
 (.leaf 0x4ec207101c7622d81300560182099036803c000c)
 (.leaf 0x54f27712e880431111b05681ce0740148048000c))
 (.branch 85
 (.leaf 0x50d23090106222e80c3856c1ae0750318080000c)
 (.leaf 0x5772748f805c82290b8856c1de0990310134000c)))
 (.branch 88
 (.branch 87
 (.leaf 0x53c26b0fdc6c82490b9056c1ae08102680a4000c)
 (.leaf 0x50d25c101059c2320f8056c1780a7030808c000c))
 (.branch 89
 (.leaf 0x5a128811307b83bd1438568190098014807c000c)
 (.branch 90
 (.leaf 0x50d23110106a42c70ce056c1e607401c807c000c)
 (.leaf 0x5bb28710145e42560c405681c6076027006c000c))))))
 (.branch 100
 (.branch 95
 (.branch 93
 (.branch 92
 (.leaf 0x54f27711dc8042120d40568196077014807c000c)
 (.leaf 0x58127a8fb043c2130fe85681ae08302680a4000c))
 (.branch 94
 (.leaf 0x53c26b0fdc43c2130d4856c1ae08302680a4000c)
 (.leaf 0x50d26510105922700ed856c1820a70108070000c)))
 (.branch 97
 (.branch 96
 (.leaf 0x50e25c10145e42560f88568180083011806c000c)
 (.leaf 0x4ff2188f945a42740e3856419a09e00f806c000c))
 (.branch 98
 (.leaf 0xbf850b2258f205a42150f3856818209b011807c000d)
 (.branch 99
 (.leaf 0x56627d100c57622a10a06482b60ef03c81bc000c)
 (.leaf 0xc6a55b2718f1c5f22350cb05641c40b900d803c000d)))))
 (.branch 104
 (.branch 102
 (.branch 101
 (.leaf 0xc7a50c2150f9c5d02210ee856c1ce08f00d8024000d)
 (.leaf 0x5011fc0b884422130fe856c19808f02700e4000c))
 (.branch 103
 (.leaf 0x4dd1ea0b584fe2160f405681e009b026807c000c)
 (.leaf 0x6352ad938c78e38f17f05641c207401c807c000c)))
 (.branch 106
 (.branch 105
 (.leaf 0x64c2668fd4590264107856417e0b70098028000c)
 (.leaf 0x64727f0f105ee2330ac85541ee08600d803c000c))
 (.branch 107
 (.leaf 0x6492790f105fe23f0d985641fc09200e803c000c)
 (.branch 108
 (.leaf 0x5be27b0fb45922a10ce056417e0930108070000c)
 (.leaf 0x63d279925c85440616385641c207401c807c000c)))))))
 (.branch 127
 (.branch 118
 (.branch 113
 (.branch 111
 (.branch 110
 (.leaf 0x56627d11207b23ab15d856c1d808c037807c000c)
 (.leaf 0x6432b2141888c3e515d85681c008001c807c000c))
 (.branch 112
 (.leaf 0x4ff2188f9475c2d30ff856420207400f8030000c)
 (.leaf 0x4e72178ff47642eb0b585601aa0a00100028000c)))
 (.branch 115
 (.branch 114
 (.leaf 0x62428091207b23ab15d856c1d808c037807c000c)
 (.leaf 0x62228690cc79a3ae16f856c1f008c019807c000c))
 (.branch 116
 (.leaf 0x60f2b313e87c03ab15d856c1d808c037807c000c)
 (.branch 117
 (.leaf 0x5242708f1c75e22c0ff05642000a9015808c000c)
 (.leaf 0x4ff2188f9475c2d30ff856420209d011807c000c)))))
 (.branch 122
 (.branch 120
 (.branch 119
 (.leaf 0x55127112e480622a0ec056c1880a7014808c000c)
 (.leaf 0x53b26a91b47be3b2123856c1d808c0150090000c))
 (.branch 121
 (.leaf 0x54d28912c47bc3ac124056019207502700ac000c)
 (.leaf 0x5bb27f90c47ca38f17f05641c207401c807c000c)))
 (.branch 124
 (.branch 123
 (.leaf 0x14308ba3f116f856c1f00a401e0080000a)
 (.leaf 0x14047f0246101056c1d00b302800a8000a))
 (.branch 125
 (.leaf 0x4e72178ff45d42460df85601d00820310134000c)
 (.branch 126
 (.leaf 0x4dd25c0f5057225210005681e80b2030811c000c)
 (.leaf 0x56228913089283f616385641c207401c807c000c))))))
 (.branch 136
 (.branch 131
 (.branch 129
 (.branch 128
 (.leaf 0x52227c92a478c2f8156856019207501c8088000c)
 (.leaf 0x56527c8fdc58e21f0d7056c1f60a003780e4000c))
 (.branch 130
 (.leaf 0x50125c0fe057622e101056c1d00b302380e4000c)
 (.leaf 0x5bb2808fe05c42210cc856c1f608802700e4000c)))
 (.branch 133
 (.branch 132
 (.leaf 0x5b528791207b23ab15d856c1d808c037807c000c)
 (.leaf 0x56627d125c80c3ab15d856c1d808c037807c000c))
 (.branch 134
 (.leaf 0x57f28712e480a24e0ee056818e07f0150040000c)
 (.branch 135
 (.leaf 0x2748f8044418e0ad844c1ae0a202680a4000b)
 (.leaf 0x28711dc80a2d30d085682580fa03f007c000b)))))
 (.branch 141
 (.branch 138
 (.branch 137
 (.leaf 0x60f27992fc8aa3e016385641c207401c807c000c)
 (.leaf 0x5bd2688f205ac1a00ac85041dc08a026807c000c))
 (.branch 139
 (.leaf 0xa123f41cd056c1f00a401580800009)
 (.branch 140
 (.leaf 0x27492f87c03b5117056c1a80a40148098000b)
 (.leaf 0x32594247b83b316f856c1f008c019807c000b))))
 (.branch 143
 (.branch 142
 (.leaf 0x5bb28112707f22f611805641c207402700e4000c)
 (.leaf 0x28092f47f03b415d88b82b60ec058011c000b))
 (.branch 144
 (.leaf 0x26912b47923af17609802b00bd0408134000b)
 (.branch 145
 (.leaf 0x2688f207642d611705641da0990310134000b)
 (.leaf 0x50d202056c2040ba01580840008)))))))))
def rawLeaves (i : Nat) : List Nat :=
  let code := leafTable.get i
  (PackedRawNatGrowth.readList 13 (PackedRawNatGrowth.take 5 code)
    (PackedRawNatGrowth.drop 5 code)).1

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 5
  | 3 => 5
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 0
  | 10 => 0
  | _ => 0

def nodeTest (i : Nat) : Bool :=
  SubsumedCounterReplay.check widths cellCount 1024 96 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixBase03.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase03.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase03.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase03.keys Papers.RationalityTen.RootedCaches.RootedSixBase03.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase03.Generators.FastWords.rawMaps rawLeaves codes counters i
theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 96 leafCount nodeCount (rawNodes i) = true ∧
      SubsumedRawGrowth.nodeCheck Papers.RationalityTen.RootedCaches.RootedSixBase03.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase03.badMasks
        Papers.RationalityTen.RootedCaches.RootedSixBase03.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase03.keys Papers.RationalityTen.RootedCaches.RootedSixBase03.fastKind quota
        Papers.RationalityTen.FacetUniverses.RootedSixBase03.Generators.FastWords.rawMaps rawLeaves rawNodes i = true :=
  SubsumedCounterReplay.check_sound widths cellCount 1024 96 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixBase03.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase03.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase03.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase03.keys Papers.RationalityTen.RootedCaches.RootedSixBase03.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase03.Generators.FastWords.rawMaps rawLeaves codes counters i h
def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.RootedSixBase03.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0723
