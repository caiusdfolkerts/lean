module
prelude
public import RootedSixBase03GrowthCacheData
public import RootedSixBase03FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0695Packed000
public import RootedSubsumedForest0695Packed001
public import RootedSubsumedForest0695Packed002
public import RootedSubsumedForest0695Packed003

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0695
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 5238
abbrev nodeCount : Nat := 19755
abbrev leafCount : Nat := 138
def widths : PackedRawNatGrowth.Widths := ⟨13,15,7,8⟩
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
(.branch 69
 (.branch 34
 (.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf 0x50b99289e041c1ec8bcc4701590078004000b)
 (.leaf 0xb62277100857c2360d686042b40e30048004000c))
 (.branch 3
 (.leaf 0x75894089723f9131071c2b20810078014000b)
 (.leaf 0x81794387562eb11087b02ba15a06e8004000b)))
 (.branch 6
 (.branch 5
 (.leaf 0x7781940a724ed20788a42b209901e8018000b)
 (.leaf 0x5eb139480024a0ec06702b60c40148008000b))
 (.branch 7
 (.leaf 0x678195c9ca4000ec06702b60c40148008000b)
 (.leaf 0x6cd14dca0a40f1dc0b542b008101f0014000b))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf 0x868901457c2360c405682260ea0308004000b)
 (.leaf 0x678195c9ca4000ce056c2540de0148008000b))
 (.branch 11
 (.leaf 0x6dc94408b63fd10f05742b40cb0148004000b)
 (.leaf 0x87619448b63fd10f05742b40cb0148004000b)))
 (.branch 14
 (.branch 13
 (.leaf 0x15989f440312106702b60ef0150008000a)
 (.leaf 0x221240412106702b60ef01500080009))
 (.branch 15
 (.leaf 0x8179738b1050e10f05742b40cb0148004000b)
 (.branch 16
 (.leaf 0x8251938a9e4ee10f05742b40cb0148004000b)
 (.leaf 0x15548062e612506702b60ef0298008000a))))))
 (.branch 25
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf 0x88a92dc80a2da11f071c2b20770220014000b)
 (.leaf 0x88492dc8082c211307182b608f0250014000b))
 (.branch 20
 (.leaf 0x8699010578275126061c2b60d70378004000b)
 (.leaf 0x5ad94447d42d514f098c2bc15905f8004000b)))
 (.branch 23
 (.branch 22
 (.leaf 0x6db8f445e02b313185782b00be0288008000b)
 (.leaf 0x6b4972cb3a3d117905782b00be0288008000b))
 (.branch 24
 (.leaf 0x69998f4a665071f50b682bc15905f8004000b)
 (.leaf 0x71393a49743e012487682b60b3023801c000b))))
 (.branch 29
 (.branch 27
 (.branch 26
 (.leaf 0x73d943897240512b07702b40830118014000b)
 (.leaf 0x81794386a42f411085742b40cc01c8004000b))
 (.branch 28
 (.leaf 0x76994408b63fd11085742b40cc01c8004000b)
 (.leaf 0x678195c9ca40019306702b60f30148008000b)))
 (.branch 31
 (.branch 30
 (.leaf 0x824956c67a2dd116861c2b60db0290004000b)
 (.leaf 0x7fd943464c2c611105c42b60f30318008000b))
 (.branch 32
 (.leaf 0x847926081e3a917809802b209901e8018000b)
 (.branch 33
 (.leaf 0x52b142c8b63fd1dc8bac44215d0ad0004000b)
 (.leaf 0x54693a47c03b716508882e215b0318008000b)))))))
 (.branch 51
 (.branch 42
 (.branch 38
 (.branch 36
 (.branch 35
 (.leaf 0x85d995081e35018008a42b209901e8018000b)
 (.leaf 0x54b17289d23e016509a82e215b00f8008000b))
 (.branch 37
 (.leaf 0x5301734a023f817108842e415b01c8004000b)
 (.leaf 0x81794385d62210b185682a61030048004000b)))
 (.branch 40
 (.branch 39
 (.leaf 0x53a942c8b63fd17a08842c615a0048004000b)
 (.leaf 0x67494348082e60fb06342b60c000d8004000b))
 (.branch 41
 (.leaf 0xfff27991606a22c70bb856425e0f200f8004000c)
 (.leaf 0xa7d30793cc8943e016385dc2b213d00f8004000c))))
 (.branch 46
 (.branch 44
 (.branch 43
 (.leaf 0x76897fca084c621608a42b209901e8018000b)
 (.leaf 0x880953498c42c16489042b008101f0014000b))
 (.branch 45
 (.leaf 0x3d993a47c02ca0ed06902b60e400f8008000b)
 (.leaf 0x7e2940457622e0ca056c2780ec01d000c000b)))
 (.branch 48
 (.branch 47
 (.leaf 0x153050d202091434e15b01580080009)
 (.leaf 0x45d94e49da3c717c88d43f8159027001c000b))
 (.branch 49
 (.leaf 0x49714087f22f911c8564276077027001c000b)
 (.branch 50
 (.leaf 0x577987c9ce33b18009042b008101f0014000b)
 (.leaf 0x49a94348c4404163069c2b607700f8014000b))))))
 (.branch 60
 (.branch 55
 (.branch 53
 (.branch 52
 (.leaf 0x3aa94348082e111687ec2b60c001c8004000b)
 (.leaf 0x57496dca8c50316489042b008101f0014000b))
 (.branch 54
 (.leaf 0x3ab193099a3f516789682b20ce00a800c000b)
 (.leaf 0x205e50e1a90bd02b4098010001c0009)))
 (.branch 57
 (.branch 56
 (.leaf 0x1da651022d8ff42b4098010001c0009)
 (.leaf 0x81816f4a022ba15188d02b60d40378010000b))
 (.branch 58
 (.leaf 0x5ae94487ec2c614609002b20bc0388008000b)
 (.branch 59
 (.leaf 0x6bc98eca624d82030ae42b60ec0378010000b)
 (.leaf 0x7ef1950ac451216389a82b20e100f8008000b)))))
 (.branch 64
 (.branch 62
 (.branch 61
 (.leaf 0x81215449c43ab15e094c2b60d40378010000b)
 (.leaf 0x3ce94e89dc3f616409902b20bc0388008000b))
 (.branch 63
 (.leaf 0x3d99534a244a91ef0b7c2b00c90100004000b)
 (.leaf 0x3d698909b64401fc0b7c2b00c90100004000b)))
 (.branch 66
 (.branch 65
 (.leaf 0x81a936c8863bd16f8a1c2b00c90100004000b)
 (.leaf 0x88292247f23bd1638a1c2b20e100f8008000b))
 (.branch 67
 (.leaf 0x88493148082bb14188a82b60ec0378010000b)
 (.branch 68
 (.leaf 0x89219408623e516389a82b20e100f8008000b)
 (.leaf 0x5a9941478c3a417f09a82b00c90100004000b))))))))
 (.branch 103
 (.branch 86
 (.branch 77
 (.branch 73
 (.branch 71
 (.branch 70
 (.leaf 0x7e196eca0438f17f09a82b20e100f8008000b)
 (.leaf 0x76e98e0a8c5031e309a82b00c90100004000b))
 (.branch 72
 (.leaf 0x77517289ce42f1fe89a82b00c90100004000b)
 (.leaf 0x84d92e47f238f131056417e081014803c000b)))
 (.branch 75
 (.branch 74
 (.leaf 0x77293789703d5130856017c0a5030803c000b)
 (.leaf 0x86892e880a31111b05681ce0740148048000b))
 (.branch 76
 (.leaf 0x778934894e3c90b905601ac0b00310084000b)
 (.leaf 0x86990106ca24a0c3856c1ae07502680a4000b))))
 (.branch 81
 (.branch 79
 (.branch 78
 (.leaf 0x73b93747a823d0ae05681c60a50308138000b)
 (.leaf 0x54c14348c4404163869c2b607401c807c000b))
 (.branch 80
 (.leaf 0x86891dc80a2120d40568196077014807c000b)
 (.leaf 0x86990104542110d3856c1ae07702680a4000b)))
 (.branch 83
 (.branch 82
 (.leaf 0x7fc94385a42750ee056818209f00f806c000b)
 (.leaf 0x3ce94047f02bd0e3056c19a0b70100074000b))
 (.branch 84
 (.leaf 0xfcb285916c5a42150f3856818209b011807c000c)
 (.branch 85
 (.leaf 0x884901057622a10a06482b60ef03c81bc000b)
 (.leaf 0x8a131c15189f63c617c895c2b00ca00d803c000c))))))
 (.branch 94
 (.branch 90
 (.branch 88
 (.branch 87
 (.leaf 0x53b991c9fc3c418008cc2b208600d803c000b)
 (.leaf 0xb6927d100c57a24c0c4856c1ae09f00d8024000c))
 (.branch 89
 (.leaf 0x75398d4ab64eb1e385641c207401c807c000b)
 (.leaf 0xb532828f185f224d0d585601940b900d803c000c)))
 (.branch 92
 (.branch 91
 (.leaf 0x7fc943875a2d310085681ea08000f8030000b)
 (.leaf 0x7fc94387622d30b785681f207c00f8030000b))
 (.branch 93
 (.leaf 0x8338fb076221f0f585681b80b50148098000b)
 (.leaf 0x7e1940875c2d30ff856420209d011807c000b))))
 (.branch 98
 (.branch 96
 (.branch 95
 (.leaf 0x86992e480822a0ec056c1880a7014808c000b)
 (.leaf 0x14308ba3f116f856c1f00a401e0080000a))
 (.branch 97
 (.leaf 0x84e92e47f022e0f6856c1a00b302380a4000b)
 (.leaf 0x4ee9534a244ba1ef09682b00a3015803c000b)))
 (.branch 100
 (.branch 99
 (.leaf 0x75a17349fe4311f285641c207401c807c000b)
 (.leaf 0x6cd94e0a0c3de1db856017a08102780a8000b))
 (.branch 101
 (.leaf 0x7e093a85d42460df85601d00820310134000b)
 (.branch 102
 (.leaf 0x818943458e21f101856c1d20a703780e4000b)
 (.leaf 0x5b493e88062bd12186682b60d704480e4000b)))))))
 (.branch 120
 (.branch 111
 (.branch 107
 (.branch 105
 (.branch 104
 (.leaf 0x62e9590a0c40715d85681c008001c807c000b)
 (.leaf 0x88b10cc79a3ae171856c1f008c019807c000b))
 (.branch 106
 (.leaf 0x891193888c3e515d85681c008001c807c000b)
 (.leaf 0x80a1944ac850615d85681c008001c807c000b)))
 (.branch 109
 (.branch 108
 (.leaf 0xb6026b0fac5ac1a00ad04b01f407e023807c000c)
 (.leaf 0x47193d47d82ee11085681ba08302680e8000b))
 (.branch 110
 (.leaf 0x46f93447902d614a056420209a026807c000b)
 (.leaf 0x5ac93b478e38f17f05641c207401c807c000b))))
 (.branch 115
 (.branch 113
 (.branch 112
 (.leaf 0x86d91307c03bd1438568190098014807c000b)
 (.leaf 0x86991b08082bc138056c1a80b001d8080000b))
 (.branch 114
 (.leaf 0x84e91bc7f03b2117856c1a80a40148098000b)
 (.leaf 0x7fc96eca1c37a17905681c008001c807c000b)))
 (.branch 117
 (.branch 116
 (.leaf 0x206250d16f856c1f00a401e00800009)
 (.leaf 0x88393148fe40515d85681c008001c807c000b))
 (.branch 118
 (.leaf 0x88491c88083ab112056c1d808c02780a8000b)
 (.branch 119
 (.leaf 0x6aa96eca043f917f05641c207402700e4000b)
 (.leaf 0x42b96f49a23c816b06a82b20ee026807c000b))))))
 (.branch 129
 (.branch 124
 (.branch 122
 (.branch 121
 (.leaf 0x43a96f4a043f916a86ac2b20bf011006c000b)
 (.leaf 0x2212404121056c1ec0ae02800a80009))
 (.branch 123
 (.leaf 0x88392e080a2bd12705681a408a030808c000b)
 (.leaf 0x88492e08082bb115056c1ec0ae037808c000b)))
 (.branch 126
 (.branch 125
 (.leaf 0x7fd96eca1a2de10e856c1ec0ae0378138000b)
 (.leaf 0x5db1704a1a40416708c82bc0bf0280004000b))
 (.branch 127
 (.leaf 0x5db1718a1a4bd2020b184440bc0240008000b)
 (.branch 128
 (.leaf 0x5d517109ea4851f60ba44780d50268004000b)
 (.leaf 0x5db16fc9d23e01650ad053e0e100f8008000b)))))
 (.branch 133
 (.branch 131
 (.branch 130
 (.leaf 0x5d9170ca1c40516d099c47c0bc0278008000b)
 (.leaf 0x5dd1718a024bd1fc0af41960750100040000b))
 (.branch 132
 (.leaf 0x5d917109ba3d416b06081dc094026807c000b)
 (.leaf 0x5dd97049ba3d415f099c1ec0ae028007c000b)))
 (.branch 135
 (.branch 134
 (.leaf 0x5de1890a023d01ad85501ec080015007c000b)
 (.leaf 0xbbd30793c47c02bb14508101c60ab037807c000c))
 (.branch 136
 (.leaf 0xbb4314142c9063fb16984f820607700f806c000c)
 (.branch 137
 (.leaf 0xbb931413c08062c411584f41860ba0378070000c)
 (.leaf 0x5d414107c63b217808f01ca085036006c000b)))))))))
def rawLeaves (i : Nat) : List Nat :=
  let code := leafTable.get i
  (PackedRawNatGrowth.readList 13 (PackedRawNatGrowth.take 5 code)
    (PackedRawNatGrowth.drop 5 code)).1

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 4
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 1
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0695
