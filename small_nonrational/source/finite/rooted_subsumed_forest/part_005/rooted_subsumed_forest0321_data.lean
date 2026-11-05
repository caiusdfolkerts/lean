module
prelude
public import RootedSixBase02GrowthCacheData
public import RootedSixBase02FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0321Packed000
public import RootedSubsumedForest0321Packed001
public import RootedSubsumedForest0321Packed002
public import RootedSubsumedForest0321Packed003

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0321
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 8084
abbrev nodeCount : Nat := 22737
abbrev leafCount : Nat := 136
def widths : PackedRawNatGrowth.Widths := ⟨13,15,6,8⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 100
 (.branch 50
 nodeBlocks000
 nodeBlocks001)
 (.branch 150
 nodeBlocks002
 nodeBlocks003))
def counterTable : Table Nat :=
(.branch 100
 (.branch 50
 nodeCounters000
 nodeCounters001)
 (.branch 150
 nodeCounters002
 nodeCounters003))
def codes (i : Nat) : Nat :=
  let b := blocks.get (i / 128)
  PackedRawNatGrowth.drop
    (PackedRawNatGrowth.take 32 (PackedRawNatGrowth.drop (32*(i%128)) b.offsets)) b.payload
def counters (i : Nat) : Nat :=
  PackedRawNatGrowth.take 55 (PackedRawNatGrowth.drop (55*(i%128)) (counterTable.get (i/128)))
def rawNodes (i : Nat) := PackedRawNatGrowth.decodeNode widths (codes i)

def leafTable : Table Nat :=
(.branch 68
 (.branch 34
 (.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf 0x11a4550257108852c1be04501e0008000a)
 (.leaf 0x1014550257108852c1be05601e0008000a))
 (.branch 3
 (.leaf 0x10145502110f4052c14e03c0090020000a)
 (.leaf 0x107851e2110f4053414a03e0060018000a)))
 (.branch 6
 (.branch 5
 (.leaf 0x10185382100a603ac11405601e00e0000a)
 (.leaf 0x10487662f210805341440260110020000a))
 (.branch 7
 (.leaf 0x107476029b109052c12e0560250018000a)
 (.leaf 0x10487662100f2853411a02600a0018000a))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf 0x10747642120a603b013002800f0048000a)
 (.leaf 0x107876428f108878829a0990110018000a))
 (.branch 11
 (.leaf 0x107476429b10905301aa09702b0048000a)
 (.leaf 0x10187602100f1053413204c0130018000a)))
 (.branch 14
 (.branch 13
 (.leaf 0x107876028c108078829a09902d0018000a)
 (.leaf 0x101876e29a10905301aa09702d8048000a))
 (.branch 15
 (.leaf 0x2a7109053414c04600d001c0008)
 (.branch 16
 (.leaf 0x1b00a704201b90a582fc11e044015806c000b)
 (.leaf 0x269906c68a27710905341bc0350148010000b))))))
 (.branch 25
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf 0x1ab8aa04221cf0a6038811c04500e006c000b)
 (.leaf 0x1ae8a9c4241e40a682f813404600d8024000b))
 (.branch 20
 (.leaf 0x1b00a704201a70a5831c11e0540220028000b)
 (.leaf 0x266907066029b10885301a403601a800c000b)))
 (.branch 23
 (.branch 22
 (.leaf 0x103c68c2120f2853414c0260060018000a)
 (.leaf 0x106c51e2120f4053414c0340060018000a))
 (.branch 24
 (.leaf 0x106c68a2120f1053413402c0138018000a)
 (.leaf 0x100c68e2110a6038c14e02600f0060000a))))
 (.branch 29
 (.branch 27
 (.branch 26
 (.leaf 0x106c51e2120f1053413403801a0018000a)
 (.leaf 0x1f792670fb477c2ab114852818e05d01c8004000c))
 (.branch 28
 (.leaf 0x1f782670fe477e2ac0a7852817805e01c800c000c)
 (.leaf 0x1f78269904477e2ac0a7852817804701c800c000c)))
 (.branch 31
 (.branch 30
 (.leaf 0x1f78269904477e2ac10a052817604701c8004000c)
 (.leaf 0x7dd478029f0f0853014804a0220020000a))
 (.branch 32
 (.leaf 0x1f752140f0053e1f70a603201480540220058000c)
 (.branch 33
 (.leaf 0x1f6d1f70eac50e1fd0a6038014805400b0054000c)
 (.leaf 0x1f792028ef85561f80a583201300550298054000c)))))))
 (.branch 51
 (.branch 42
 (.branch 38
 (.branch 36
 (.branch 35
 (.leaf 0x7de08223bf156052c1160560160018000a)
 (.leaf 0x7dd083a3c1150053011a05600c0018000a))
 (.branch 37
 (.leaf 0x7dd083a3c115005301aa0560090008000a)
 (.leaf 0x7de08223bf156052c1a60560110008000a)))
 (.branch 40
 (.branch 39
 (.leaf 0x1f6820f0eb84f81e20b385341620650298004000c)
 (.leaf 0x1f7420e8f045401ce0a602c011a06502a006c000c))
 (.branch 41
 (.leaf 0x1f642090e644e01e90a682f410205300e006c000c)
 (.leaf 0x7dd083a3c1150078c2980120030008000a))))
 (.branch 46
 (.branch 44
 (.branch 43
 (.leaf 0x3ee841d1e08a803c614c04680180009)
 (.leaf 0x1f782088efc5582140f1852c17c01b0078004000c))
 (.branch 45
 (.leaf 0x1f781fc8ea85582170e705281ac01b0048004000c)
 (.leaf 0x1f7420e8f045401e30a602c80ea03f00f806c000c)))
 (.branch 48
 (.branch 47
 (.leaf 0x1f741fc8e545401b90a5035c0ee03500f806c000c)
 (.leaf 0xfba10747822a00f185542980b200f8004000b))
 (.branch 49
 (.leaf 0x1f78269904477e2ac10a052c1760150078004000c)
 (.branch 50
 (.leaf 0x1f7826a8fe47542ac10b85281a60150048004000c)
 (.leaf 0x1f78269904477e2ac0a582ec0d203f0100054000c))))))
 (.branch 59
 (.branch 55
 (.branch 53
 (.branch 52
 (.leaf 0x1f7826a8fe47542ac0a5034c0d60350100054000c)
 (.leaf 0xfbc134c8223bf15605442960bc00a800c000b))
 (.branch 54
 (.leaf 0xfbc134c8223bf156052c17808c00d8054000b)
 (.leaf 0x1f7426990747822a00a7853017a02900f8004000c)))
 (.branch 57
 (.branch 56
 (.leaf 0x1f6c26a90747582880a905301aa0290048004000c)
 (.leaf 0x1f6c26a90747582880a603540d602900d8040000c))
 (.branch 58
 (.leaf 0x1f78269904477e2ac0a582c40e603f015003c000c)
 (.leaf 0xfbc134c8223bf15608582960ae0150008000b))))
 (.branch 63
 (.branch 61
 (.branch 60
 (.leaf 0xfba134c83a3c1150053017408a01a80a4000b)
 (.leaf 0x1ed820c8f0468a283108871c0d40360110014000c))
 (.branch 62
 (.leaf 0x1f79268100c752351116052815e0480130004000c)
 (.leaf 0x1edd2030ef86b226b108076c1040530118014000c)))
 (.branch 65
 (.branch 64
 (.leaf 0x1f78268903c7543520a503480e80490130058000c)
 (.leaf 0x1ed420d0f0c68a27710906c812e0350048014000c))
 (.branch 66
 (.leaf 0x1edc21e8efc6b426b10807701140440050014000c)
 (.branch 67
 (.leaf 0x1ed92028f006b027710887181440530058014000c)
 (.leaf 0x1edd2008ef86b6277108076c12c0320058014000c))))))))
 (.branch 102
 (.branch 85
 (.branch 76
 (.branch 72
 (.branch 70
 (.branch 69
 (.leaf 0x1f75268101072835313b89042940470028004000c)
 (.leaf 0x1f74267106c72a35413b85280ce04901a8014000c))
 (.branch 71
 (.leaf 0xf6e104877e26b10807c411a0150048014000b)
 (.leaf 0xf6e104877e26b10807c40d40150090014000b)))
 (.branch 74
 (.branch 73
 (.leaf 0x3ef040e1df8d4829608b01300180009)
 (.leaf 0xfbc103877e35210d052c1640260078004000b))
 (.branch 75
 (.leaf 0x7dd08343c11aa05301ac0270090008000a)
 (.leaf 0xfbc140877e352133852c1160470218018000b))))
 (.branch 80
 (.branch 78
 (.branch 77
 (.leaf 0xfbc103877e352135852c1160150048014000b)
 (.leaf 0xfbc103877e352135852c0d402200a8014000b))
 (.branch 79
 (.leaf 0x1f7420d0f046a82770d305300d40350090014000c)
 (.leaf 0x1f7420d0f046a82770a8853016603500b0008000c)))
 (.branch 82
 (.branch 81
 (.leaf 0x1f7729b8fa86e432e0fc052819609c012803c000c)
 (.leaf 0x1f7629b0fb473628d0fd052817809d0088030000c))
 (.branch 83
 (.leaf 0x1f7a29a0f8470c28b0fb85281780a90298044000c)
 (.branch 84
 (.leaf 0x1f7329c93387f2387152052817809000d803c000c)
 (.leaf 0x3ef65352678f8452e14f0a5032015003c01c8074000d))))))
 (.branch 93
 (.branch 89
 (.branch 87
 (.branch 86
 (.leaf 0x1f7b26990806e829b130852815e04800f8004000c)
 (.leaf 0x1f7b26a90806e6283126052c16204a0078004000c))
 (.branch 88
 (.leaf 0x1f77269905054e2630a7852817804701c800c000c)
 (.leaf 0x1f7721410505062370a7853017a05401e0004000c)))
 (.branch 91
 (.branch 90
 (.leaf 0x1f7a267107c71227713105280ce04901a8014000c)
 (.leaf 0x1f7b26990806e829b13085280ce0480148014000c))
 (.branch 92
 (.leaf 0x1ed22309018760359135884010e0530118014000c)
 (.leaf 0x1f76268904c73c2640a503480e80490130058000c))))
 (.branch 97
 (.branch 95
 (.branch 94
 (.leaf 0x1ecb21c106873633014788480dc0350108018000c)
 (.leaf 0x1f7b26a90806e6283126052c0d204a00a8014000c))
 (.branch 96
 (.leaf 0x1f7720a0dcc5062370d185300ea0540250014000c)
 (.leaf 0x1f7728590985042370a7853017a04301e0004000c)))
 (.branch 99
 (.branch 98
 (.leaf 0x1f7729b8fb454c2630a7852817805d01c800c000c)
 (.leaf 0xfbd94d47c237714d09842940af00f8004000b))
 (.branch 100
 (.leaf 0xfbd94807c437814109302960b10078004000b)
 (.branch 101
 (.leaf 0xfbd94d47bc37718f89842940670128014000b)
 (.leaf 0x1f7a29a0f7871827613105280ce06101a8014000c)))))))
 (.branch 119
 (.branch 110
 (.branch 106
 (.branch 104
 (.branch 103
 (.leaf 0x1ed2230901876c2b510806281140260050014000c)
 (.leaf 0xfbd94d47c237714d09842940670148014000b))
 (.branch 105
 (.leaf 0x1ed2226100876e26b10885d41160320048014000c)
 (.leaf 0xfbd94807c4378141093029606900a8014000b)))
 (.branch 108
 (.branch 107
 (.leaf 0x1f7729b93387da2a311b852818e05d01c8004000c)
 (.leaf 0xfbd94807c0320126052815e03a0130004000b))
 (.branch 109
 (.leaf 0x1f7a28f934070a273131052c1a60470218008000c)
 (.leaf 0x1ed22260ecc6b426b10806281140440050014000c))))
 (.branch 114
 (.branch 112
 (.branch 111
 (.leaf 0x1f7629b13407da39b14608e02940290028004000c)
 (.leaf 0x1f7a29a0f8470c28b12685281760650298004000c))
 (.branch 113
 (.leaf 0xfbd14d09a03e11c30a2c49a14a05d8004000b)
 (.leaf 0x1f7a29a0f8470c28e126852815e06501a8004000c)))
 (.branch 116
 (.branch 115
 (.leaf 0x1f7a20f853415202700d001c0008)
 (.leaf 0xfbd107c51e1d30a683dc1520530148014000b))
 (.branch 117
 (.leaf 0xfbd107c51e1e80a683f415202900a8014000b)
 (.branch 118
 (.leaf 0x3ef441f14787a029a0a900600180009)
 (.leaf 0xfbd107c4ee1e80a683e815205300a8014000b))))))
 (.branch 127
 (.branch 123
 (.branch 121
 (.branch 120
 (.leaf 0xfbb104c5201e90a682f813a03500d8024000b)
 (.leaf 0xfbb104c4d61e90a682f413a05300d8024000b))
 (.branch 122
 (.leaf 0xfbb104c5201be0a682ec13a05301a8024000b)
 (.leaf 0x7de8a6828b0f0853415204b022001c000a)))
 (.branch 125
 (.branch 124
 (.leaf 0x1ede2aa10904ea22b10906741ec0310038008000c)
 (.leaf 0x1f7a29a10f45161f70a682f0152053022005c000c))
 (.branch 126
 (.leaf 0x1f7a28f90f84ec1fd0a682c415204300c8028000c)
 (.leaf 0x1ede2120d144ee2120d306740d40350118014000c))))
 (.branch 131
 (.branch 129
 (.branch 128
 (.leaf 0x1f6f29113448063430a50378108048013005c000c)
 (.leaf 0x1f7a28f8f806161d00a682bc1520490130028000c))
 (.branch 130
 (.leaf 0xfbd90805362610f185542980b200f8004000b)
 (.leaf 0x7dec84029b130878c2980120030008000a)))
 (.branch 133
 (.branch 132
 (.leaf 0x1f7b26710805062610a8853021a0160028008000c)
 (.leaf 0xfbd934c84029b13085442980b000b0008000b))
 (.branch 134
 (.leaf 0x1f7a20f89dc49a1e20b385341620650298004000c)
 (.branch 135
 (.leaf 0x1f7a20f8a3c49a1e20b3853416406501a8004000c)
 (.leaf 0x1f7b29010a450424c0a9053016204300c0004000c)))))))))
def rawLeaves (i : Nat) : List Nat :=
  let code := leafTable.get i
  (PackedRawNatGrowth.readList 13 (PackedRawNatGrowth.take 5 code)
    (PackedRawNatGrowth.drop 5 code)).1

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 3
  | 2 => 5
  | 3 => 3
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 1
  | 10 => 0
  | _ => 0

def nodeTest (i : Nat) : Bool :=
  SubsumedCounterReplay.check widths cellCount 1024 48 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixBase02.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase02.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase02.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase02.keys Papers.RationalityTen.RootedCaches.RootedSixBase02.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.FastWords.rawMaps rawLeaves codes counters i
theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 48 leafCount nodeCount (rawNodes i) = true ∧
      SubsumedRawGrowth.nodeCheck Papers.RationalityTen.RootedCaches.RootedSixBase02.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase02.badMasks
        Papers.RationalityTen.RootedCaches.RootedSixBase02.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase02.keys Papers.RationalityTen.RootedCaches.RootedSixBase02.fastKind quota
        Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.FastWords.rawMaps rawLeaves rawNodes i = true :=
  SubsumedCounterReplay.check_sound widths cellCount 1024 48 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixBase02.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase02.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase02.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase02.keys Papers.RationalityTen.RootedCaches.RootedSixBase02.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.FastWords.rawMaps rawLeaves codes counters i h
def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.RootedSixBase02.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0321
