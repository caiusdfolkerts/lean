module
prelude
public import RootedSixBase01GrowthCacheData
public import RootedSixBase01FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0302Packed000
public import RootedSubsumedForest0302Packed001
public import RootedSubsumedForest0302Packed002
public import RootedSubsumedForest0302Packed003

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 15246
abbrev nodeCount : Nat := 19838
abbrev leafCount : Nat := 133
def widths : PackedRawNatGrowth.Widths := ⟨14,15,6,8⟩
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
(.branch 66
 (.branch 33
 (.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf 0xaa41fb86a019d85fc14502e204080900028000b)
 (.leaf 0xaaa24f07ec1c9862e18004ec0ac800a0008000b))
 (.branch 3
 (.leaf 0xb742a989381f6862e18004fa0ac800a0008000b)
 (.leaf 0xaac1f5860617f04ca116833804780900028000b)))
 (.branch 6
 (.branch 5
 (.leaf 0xb6c2aa0922202860617f02ca03a80480028000b)
 (.leaf 0x7ee1a305fc14b033e05c809000380009))
 (.branch 7
 (.leaf 0xaa820106a8180052a0b401ce03b009400f8000b)
 (.leaf 0xaac1f5860817f04ca0ce0200046009001d8000b))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf 0x480e2b288f41fb07061a0060006880460008000b)
 (.leaf 0x1242878c18485fc132820004a009001d8000a))
 (.branch 11
 (.leaf 0x126f87a619905fa17904e407a808e0010000a)
 (.leaf 0x4b142ac093e1f505fe14102b807080120008000b)))
 (.branch 14
 (.branch 13
 (.leaf 0x55722e589461cb860013882b608301da0008000b)
 (.leaf 0x59482de87c61cb860013a02b608301da0008000b))
 (.branch 15
 (.leaf 0x5a22203873a18004ca0b4020a07c80ae0008000b)
 (.leaf 0x4d0a1e9871017e85300c0028a064008e0010000b)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf 0x551a2da89041cc85fc13882ee09781d80008000b)
 (.leaf 0x5a22203873a18004ca0c0021607c80260008000b))
 (.branch 19
 (.leaf 0x55b824b873018004ca0c1821607c80260008000b)
 (.leaf 0x49f623788881c205fa144829e06a007a0010000b)))
 (.branch 22
 (.branch 21
 (.leaf 0x2dd09361f6872e18001da04c804a0080000a)
 (.leaf 0x5a22203873a18001f204c004800880009))
 (.branch 23
 (.leaf 0x56fa250079c1da05fa149819005880660088000b)
 (.leaf 0x4d1630f8b281f4060014002ca06a80900008000b))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf 0x4fd230f8b281f4060017102ca06a80900008000b)
 (.leaf 0x57a22d8898a1ee05fe1440312070808e0010000b))
 (.branch 27
 (.leaf 0xab0243878c1d985fc151017a046806c0078000b)
 (.leaf 0xb6c2aa092220285fc13282ca05e80c20008000b)))
 (.branch 30
 (.branch 29
 (.leaf 0x14ba8ab2248880a17f04ca0b2817a0008000a)
 (.leaf 0x531c2ef89801fc05fe13802e206480900008000b))
 (.branch 31
 (.leaf 0x59c42f187841d785fa151817805280680080000b)
 (.branch 32
 (.leaf 0xb462ab093a1f085fe144819203a80720078000b)
 (.leaf 0x4f762df09c01e986f417e82fa05e008e0010000b)))))))
 (.branch 49
 (.branch 41
 (.branch 37
 (.branch 35
 (.branch 34
 (.leaf 0x59d62de099420306ac17f82e206480460008000b)
 (.leaf 0x55fe2e4897e251070217f82b206480460008000b))
 (.branch 36
 (.leaf 0x56002e5092e1b6860015582ca06a80480008000b)
 (.leaf 0xab21e3076817f052c0b4817a05880900050000b)))
 (.branch 39
 (.branch 38
 (.leaf 0xaa81e385fa139031a0a9017805d008e01c8000b)
 (.leaf 0x51362d788fe1c186000be01f2040007c0118000b))
 (.branch 40
 (.leaf 0x55702e688fe1b706000be81da03a00ae0118000b)
 (.leaf 0x2d589061cc85fe0c901f0056007c0120000a))))
 (.branch 45
 (.branch 43
 (.branch 42
 (.leaf 0x48f82eb0b561ec875617f04c807601280238000b)
 (.leaf 0x49d02e509561e986de17e81a8056008e0120000b))
 (.branch 44
 (.leaf 0x49402e688c41f586de17f01d804a00ae0118000b)
 (.leaf 0x49422ec8b961e1873217f04da07601700238000b)))
 (.branch 47
 (.branch 46
 (.leaf 0xab21e985fa13304a60cc8196053808e0048000b)
 (.leaf 0x55b424586b017f849c0c781f603c00480050000b))
 (.branch 48
 (.leaf 0x4dfe2d5891a17f849c0c581f603d807c0050000b)
 (.leaf 0xaac1ef85fa133045c0ce818204d808e00f8000b)))))
 (.branch 57
 (.branch 53
 (.branch 51
 (.branch 50
 (.leaf 0xb422ab08f220285fa0c0019603b804600f8000b)
 (.leaf 0x55822d008c217e84940c781ae03b80de0118000b))
 (.branch 52
 (.leaf 0x55a62c588c217e84920cd81ae04180ae0118000b)
 (.leaf 0x55162c688c017f049e0cd81de03b004800a0000b)))
 (.branch 55
 (.branch 54
 (.leaf 0x52e023007a817f04a60cb81de03b004800a0000b)
 (.leaf 0x49d42cb08c21f885fa12a81ae03b80de0118000b))
 (.branch 56
 (.leaf 0x12578bd224f07c81cb05fc12c817c04e00b60128000c)
 (.leaf 0x15420bd2251872c17f04960b5017c04e00b60128000c))))
 (.branch 61
 (.branch 59
 (.branch 58
 (.leaf 0x15670c0224b86d817f84960c1819803c00680120000c)
 (.leaf 0x55ea30e0704180050a0cd81b004200900108000b))
 (.branch 60
 (.leaf 0x127c8c0224908101b605fe12b019803c00680120000c)
 (.leaf 0x38ce2ac090c20185fe13282e8081006c0008000b)))
 (.branch 63
 (.branch 62
 (.leaf 0xaac1ef85fa133033009f81bc04c008e01c8000b)
 (.leaf 0xaa61f505fe15102b80ab81d604700920100000b))
 (.branch 64
 (.leaf 0x10688c0224907fc1b605fe0c881a203c00680120000c)
 (.branch 65
 (.leaf 0x41b026007be1ad05fa0c881a004e808e0120000b)
 (.leaf 0x41ba23707d41c205fe0b0820004880ae0118000b))))))))
 (.branch 99
 (.branch 82
 (.branch 74
 (.branch 70
 (.branch 68
 (.branch 67
 (.leaf 0x41a630107b61cb860013682d807a81380238000b)
 (.leaf 0xb2c2ab08c21f405fa0ca01bc04b00de0118000b))
 (.branch 69
 (.leaf 0xaa8249073018004ca0ce8202040008001c8000b)
 (.leaf 0x497a30b89581fe870c180020204000900118000b)))
 (.branch 72
 (.branch 71
 (.leaf 0x497a30988dc1fe870c180020204000a80118000b)
 (.leaf 0x49b6243073217f8200056007e01200009))
 (.branch 73
 (.leaf 0x49b62ec07a01cc85fe130820005600ae0238000b)
 (.leaf 0x3f962ed0b561e805fc136833c07b008e01b0000b))))
 (.branch 78
 (.branch 76
 (.branch 75
 (.leaf 0x48de2b1090e1cc85fc138825e07a007c0008000b)
 (.leaf 0x43a62a788f420106dc1aa06000b680460008000b))
 (.branch 77
 (.leaf 0x44362a9890c20186a417f84ca0bc806c0008000b)
 (.leaf 0x45022ab090e1e306b017f02f005d005a0128000b)))
 (.branch 80
 (.branch 79
 (.leaf 0x45962ec0aa81e805fe1308338057008e01b0000b)
 (.leaf 0x45962aa08c61e806aa17f833805700cc0120000b))
 (.branch 81
 (.leaf 0x5a862ab08c41f607080ce020004600d60118000b)
 (.leaf 0x16a90c222c609ce23804960b4817c04d807a0120000c)))))
 (.branch 90
 (.branch 86
 (.branch 84
 (.branch 83
 (.leaf 0x16a90bfe2dc097a1ec84960b581c603b008e0120000c)
 (.leaf 0x16b20b8c2ac89421fb04e20ac81920008000a))
 (.branch 85
 (.leaf 0x5ad22a989421ef051210c81ea03b00780078000b)
 (.leaf 0x5a8a2e189101e304e20b9827a08100ae0008000b)))
 (.branch 88
 (.branch 87
 (.leaf 0x5ad02ac09401f5076613e82b807080120008000b)
 (.leaf 0x5ad22ac09421ef07660ae81aa04c804a0048000b))
 (.branch 89
 (.leaf 0x5a322ab08ca1f5833209f81c004b00720118000b)
 (.leaf 0x5ad22a989421ef02ba0ab81ac051804a0100000b))))
 (.branch 94
 (.branch 92
 (.branch 91
 (.leaf 0x5a322ac08ca1f584a40cc81c604780460048000b)
 (.leaf 0x5a722ab08fa201030009f020603b804600f8000b))
 (.branch 93
 (.leaf 0x5a922ab091220184ca0ba027a08100720008000b)
 (.leaf 0x5a522aa08e220183180a9020403a00720118000b)))
 (.branch 96
 (.branch 95
 (.leaf 0x16ac892a201066417702de04480480028000a)
 (.leaf 0x16b489421fb03920b181ac05800c40128000a))
 (.branch 97
 (.leaf 0x5aa82e2092a1ef04ca0b701c004400b001c8000b)
 (.branch 98
 (.leaf 0x5a902ab89101fb84e210d82f2083000c0008000b)
 (.leaf 0x5aca3068b841e786dc0b101da03e008e0118000b)))))))
 (.branch 116
 (.branch 107
 (.branch 103
 (.branch 101
 (.branch 100
 (.leaf 0x5aa82fc8b8825587b60b201d4051008e0120000b)
 (.leaf 0x5aca3110b801f386fc13502b206a80900008000b))
 (.branch 102
 (.leaf 0x5a902f18b1a2ab87c0136831204c808e0030000b)
 (.leaf 0x5aca3110b8026687ce14002b206a80900008000b)))
 (.branch 105
 (.branch 104
 (.leaf 0x5aa82fc8b881ed84c20d882dc071808e0010000b)
 (.leaf 0x5aa82fc8aa61ee04c2121833a04d808e0030000b))
 (.branch 106
 (.leaf 0x5ac83070b861ed84da0ac01d605180ae0238000b)
 (.leaf 0x5ab22fc8aa61ee04c20ce820204c008e01e0000b))))
 (.branch 111
 (.branch 109
 (.branch 108
 (.leaf 0x5aca3068b841e784f80ad825207b808e0008000b)
 (.leaf 0x5aa82fc8b8429a080e13202ca05e808e0008000b))
 (.branch 110
 (.leaf 0x5aa82fc8b881ed84c80b701c0044008e01c8000b)
 (.leaf 0x5aca3068b841e7859e14182b0076808e0010000b)))
 (.branch 113
 (.branch 112
 (.leaf 0x5ac83070b861ed84ee0ad81c4043008e00f8000b)
 (.leaf 0x16b48c4623107e613804b00ae027407700d60008000c))
 (.branch 114
 (.leaf 0x16948c2424907fc136049e0c601f603d80d80050000c)
 (.branch 115
 (.leaf 0x5a9031308f41fe070a0c7028804600460030000b)
 (.leaf 0x16ac8c4a237081213204920cd81b004180d601d0000c))))))
 (.branch 124
 (.branch 120
 (.branch 118
 (.branch 117
 (.leaf 0x16b20c4623107e81ab04b60e0832c06600460008000c)
 (.leaf 0x169c0c1e242078415384a00c0817e05b00de0058000c))
 (.branch 119
 (.leaf 0x5ada2a988f420286dc0c281d203a00780118000b)
 (.leaf 0x5aba2aa893c1fc872613b02b808d800c0008000b)))
 (.branch 122
 (.branch 121
 (.leaf 0x5ae22fe8b8423287e61c782b206480460008000b)
 (.leaf 0x169e0bc82d1091213184900c001f4054807e01d0000c))
 (.branch 123
 (.leaf 0x169e0bc82d1091213184900cb81e004d807e01d0000c)
 (.leaf 0x5a823138aa624488001be02e203a80480028000b))))
 (.branch 128
 (.branch 126
 (.branch 125
 (.leaf 0x16b80bce23207a01d1849c0cb81e003b004800a0000c)
 (.leaf 0x5ae22e0892e1fd874815702b206480480008000b))
 (.branch 127
 (.leaf 0x5ae22e188fe1f1871e0ad81c4042804600f8000b)
 (.leaf 0x5ae02e189161f7871c13102b206a80d60008000b)))
 (.branch 130
 (.branch 129
 (.leaf 0x16b08c041ed874c13684b810b02d204e008e0030000c)
 (.leaf 0x5aa2251080c1d404fa11a02e808f800c0008000b))
 (.branch 131
 (.leaf 0x5ae22e0892e1fd874813282b206480720008000b)
 (.branch 132
 (.leaf 0x16ae0bac2db87b2130849c0b581f4054808e0098000c)
 (.leaf 0x16a60bd62dc87ca13204920bb81f6042808e01c8000c)))))))))
def rawLeaves (i : Nat) : List Nat :=
  let code := leafTable.get i
  (PackedRawNatGrowth.readList 14 (PackedRawNatGrowth.take 5 code)
    (PackedRawNatGrowth.drop 5 code)).1

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 5
  | 3 => 3
  | 4 => 0
  | 5 => 0
  | 6 => 1
  | 7 => 0
  | 8 => 0
  | 9 => 0
  | 10 => 0
  | _ => 0

def nodeTest (i : Nat) : Bool :=
  SubsumedCounterReplay.check widths cellCount 1024 48 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixBase01.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase01.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase01.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase01.keys Papers.RationalityTen.RootedCaches.RootedSixBase01.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.FastWords.rawMaps rawLeaves codes counters i
theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 48 leafCount nodeCount (rawNodes i) = true ∧
      SubsumedRawGrowth.nodeCheck Papers.RationalityTen.RootedCaches.RootedSixBase01.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase01.badMasks
        Papers.RationalityTen.RootedCaches.RootedSixBase01.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase01.keys Papers.RationalityTen.RootedCaches.RootedSixBase01.fastKind quota
        Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.FastWords.rawMaps rawLeaves rawNodes i = true :=
  SubsumedCounterReplay.check_sound widths cellCount 1024 48 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixBase01.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase01.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase01.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase01.keys Papers.RationalityTen.RootedCaches.RootedSixBase01.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.FastWords.rawMaps rawLeaves codes counters i h
def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.RootedSixBase01.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
