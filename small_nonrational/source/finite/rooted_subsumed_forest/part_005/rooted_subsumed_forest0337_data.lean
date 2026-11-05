module
prelude
public import RootedSixBase00GrowthCacheData
public import RootedSixBase00FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0337Packed000
public import RootedSubsumedForest0337Packed001
public import RootedSubsumedForest0337Packed002
public import RootedSubsumedForest0337Packed003
public import RootedSubsumedForest0337Packed004
public import RootedSubsumedForest0337Packed005
public import RootedSubsumedForest0337Packed006

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0337
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 21976
abbrev nodeCount : Nat := 41895
abbrev leafCount : Nat := 145
def widths : PackedRawNatGrowth.Widths := ⟨15,16,7,8⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 150
 (.branch 50
 nodeBlocks000
 (.branch 100
 nodeBlocks001
 nodeBlocks002))
 (.branch 250
 (.branch 200
 nodeBlocks003
 nodeBlocks004)
 (.branch 300
 nodeBlocks005
 nodeBlocks006)))
def counterTable : Table Nat :=
(.branch 150
 (.branch 50
 nodeCounters000
 (.branch 100
 nodeCounters001
 nodeCounters002))
 (.branch 250
 (.branch 200
 nodeCounters003
 nodeCounters004)
 (.branch 300
 nodeCounters005
 nodeCounters006)))
def codes (i : Nat) : Nat :=
  let b := blocks.get (i / 128)
  PackedRawNatGrowth.drop
    (PackedRawNatGrowth.take 32 (PackedRawNatGrowth.drop (32*(i%128)) b.offsets)) b.payload
def counters (i : Nat) : Nat :=
  PackedRawNatGrowth.take 55 (PackedRawNatGrowth.drop (55*(i%128)) (counterTable.get (i/128)))
def rawNodes (i : Nat) := PackedRawNatGrowth.decodeNode widths (codes i)

def leafTable : Table Nat :=
(.branch 72
 (.branch 36
 (.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf 0x1abc2fc84e9089a0fa018d82bc02ce009000280010000c)
 (.leaf 0x1ac42ea84f508b20f4c15d018b019400b401280020000c))
 (.branch 3
 (.leaf 0xe5e17b026b845b061e0ae810c01a90282009000280030000d)
 (.leaf 0x1ac42e9858609ea0d2015b816601de010401280020000c)))
 (.branch 6
 (.branch 5
 (.leaf 0x1abc2fb859d09d2109019e02b90196009000780010000c)
 (.leaf 0x1abc2fe04f308900c6c17c01680228009400280020000c))
 (.branch 7
 (.leaf 0x1ab82fe04f308600ccc17c01c50198009400780020000c)
 (.branch 8
 (.leaf 0x1bf035684f308580c5c17c019701de017c01280020000c)
 (.leaf 0x1c402fd851308740c940f681080134013001180110000c)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf 0xbd4163c266040f07920cd00ed018a01b4010801180010000d)
 (.leaf 0x1abc2fc059d0980113418c01b0019a008c00800010000c))
 (.branch 12
 (.leaf 0xe8617142b5843907ac0ccc0cd81520134012c01180060000d)
 (.leaf 0x1c4c35785f0098011441d48173019600b801180010000c)))
 (.branch 15
 (.branch 14
 (.leaf 0x17f4260045607a40cfc0ec8198025a008c00300010000c)
 (.leaf 0x1ac42fc84d1086a0f4c19981690228008c00300010000c))
 (.branch 16
 (.leaf 0x1ac42fb858809a210f019201b0019a008c00800010000c)
 (.branch 17
 (.leaf 0x1ac42ec04cf08a80c400ed018c022e008c00300010000c)
 (.leaf 0x1bf835885e1099e11401d4817f019600b801180010000c))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf 0x30e85fd0a7a115813881970194013401680020000b)
 (.leaf 0x2ff045706660aec1560173019601bc02700010000b))
 (.branch 21
 (.leaf 0xe2c17e4274844d06d40cc0117018d010c009000f80050000d)
 (.leaf 0x2fe8456067e0b4c1558197019c013400980010000b)))
 (.branch 24
 (.branch 23
 (.leaf 0x2f8853d091a11281a4027f01ae013000780010000b)
 (.leaf 0x2fe853d08ac0cf01398197019c013400980010000b))
 (.branch 25
 (.leaf 0x1ab82fd043c064e0c1415a81680252013400280020000c)
 (.branch 26
 (.leaf 0x1c782eb04b5071a0d4814b016b0228010400280020000c)
 (.leaf 0x1ab82fd054908780c9c15301680252013400280020000c)))))
 (.branch 31
 (.branch 29
 (.branch 28
 (.leaf 0x1c702df04c1067c0c1415a81b00198010400780020000c)
 (.leaf 0x1abc2f7041806960c1c15481af01b0013000780030000c))
 (.branch 30
 (.leaf 0x1ab42f0059008480d0c17102a701c6013000780010000c)
 (.leaf 0x1ac02f7051008300d4015a01da01b0013000780030000c)))
 (.branch 33
 (.branch 32
 (.leaf 0xcde172825984a1069e0b34159817301c6014002100010000d)
 (.leaf 0x1ac02e4845507c00b3c15981970194013401680020000c))
 (.branch 34
 (.leaf 0x1ab42f7043d07f20c9c173029b02e6013000280010000c)
 (.branch 35
 (.leaf 0xe8a1b2c2fc042e066209bc0e181a402ac012c00380020000d)
 (.leaf 0x1abc2df0425068009bc0d701610222012c00880020000c)))))))
 (.branch 54
 (.branch 45
 (.branch 40
 (.branch 38
 (.branch 37
 (.leaf 0x1abc2f7041807ec0d4013981750226013000380010000c)
 (.leaf 0x1abc2f6059b08b20c3c14c01740226013000280030000c))
 (.branch 39
 (.leaf 0x17fc2c70430069a0a5c0e4815201c8013400780020000c)
 (.leaf 0x35a85ac09b21124197827f02fe035c03000010000b)))
 (.branch 42
 (.branch 41
 (.leaf 0x1ab82fd043c07f40c9c14e01680252013400280020000c)
 (.leaf 0x1c4435684f308880cbc13f817f01ae018002e80010000c))
 (.branch 43
 (.leaf 0x1b9c35904e708580c5c14b019701de01e402f80020000c)
 (.branch 44
 (.leaf 0x1ad42f7043d080e0c9c1510174014c013000500050000c)
 (.leaf 0x1ac82e50431066609f80e981a10228012c00300010000c)))))
 (.branch 49
 (.branch 47
 (.branch 46
 (.leaf 0x1c4435785fc088a0c6c1498167011e016c02600050000c)
 (.leaf 0x1ad02fd05ab08480cfc15580cc01660134009800f0000c))
 (.branch 48
 (.leaf 0x2fe847808ac0cfc15580cc01660134009800f0000b)
 (.leaf 0x1ad42f005ac09ca109019d828b01c6016000780010000c)))
 (.branch 51
 (.branch 50
 (.leaf 0x1ac42fc058809b010d419802730196016c00780010000c)
 (.leaf 0x2ff045d08ae0ccc15600cb011e013801e800f0000b))
 (.branch 52
 (.leaf 0x17f82d304e408ae0cc01398173019601f003780010000c)
 (.branch 53
 (.leaf 0x1ac42fc84d1086a0ccc13f0169022801ec00300010000c)
 (.leaf 0x1bf835804cf08a00c600cc00cd013a018401180200000c))))))
 (.branch 63
 (.branch 58
 (.branch 56
 (.branch 55
 (.leaf 0xe5e17b026b845106d609cc0d7814c022200b800880010000d)
 (.leaf 0x1ac02f584d3082a0d2c1470175027c01f800380010000c))
 (.branch 57
 (.leaf 0xe5e18002710439069c0a2c0b5013e01e0017000f80010000d)
 (.leaf 0x1c402fd843a064e0a7c11901ed013c013000880050000c)))
 (.branch 60
 (.branch 59
 (.leaf 0x2ff045706660ab00c600ce0124013801e801f0000b)
 (.leaf 0x2ff045706660ab00ba00cc015401bc027001f0000b))
 (.branch 61
 (.leaf 0x1ab42f6058809a810d4197827f01ae020000780010000c)
 (.branch 62
 (.leaf 0xe6817e026a8437066009cc12101850258015400300010000d)
 (.leaf 0x1ce435985f809aa10b419802730196015400780010000c)))))
 (.branch 67
 (.branch 65
 (.branch 64
 (.leaf 0xe88177c2b604ec06940a2c0b5013e01e0010800f80010000d)
 (.leaf 0xe7a1c2c2e3841706940a7c0e200d801840130010800f0000d))
 (.branch 66
 (.leaf 0xe6c17dc270842b067a09cc0bc81280210015401080010000d)
 (.leaf 0xe6c17e025e844f063209d00ce8127020c015401f80020000d)))
 (.branch 69
 (.branch 68
 (.leaf 0x35205fe09c210601980273019601f000780010000b)
 (.leaf 0x17f82d304e408ae0fa018d8173010600f401200050000c))
 (.branch 70
 (.leaf 0x17f426c045607da0c9c0c00142014c009000c00050000c)
 (.branch 71
 (.leaf 0x171c2c284f4068e0a8c11681c901fc010400780020000c)
 (.leaf 0x1abc2f5859b09ea0d2013f816701ae016c02100010000c))))))))
 (.branch 108
 (.branch 90
 (.branch 81
 (.branch 76
 (.branch 74
 (.branch 73
 (.leaf 0x1abc2fb859d09d2109019e02730196016c00780010000c)
 (.leaf 0x1ac42ef858509e810541a3828b01c601f400780010000c))
 (.branch 75
 (.leaf 0x1bf035885fc085a0ccc13f01690228012c00300010000c)
 (.leaf 0x1ac42fe04f308600ccc13f81690228017400300010000c)))
 (.branch 78
 (.branch 77
 (.leaf 0x1bc02f6843707d809f80c2813d01f4012c01700010000c)
 (.leaf 0x1bf42eb842308040cfc15700cb011e01c0026800f0000c))
 (.branch 79
 (.leaf 0x39086b40bdc12d01a4027e02ce035c02100010000b)
 (.branch 80
 (.leaf 0x17142c2845808060cc41390106013401e402580120000c)
 (.leaf 0x1bec2fd842208040cf41390107011c01e802580110000c)))))
 (.branch 85
 (.branch 83
 (.branch 82
 (.leaf 0x1c7c2e484d8064c0a880e0017d0252010c00280020000c)
 (.leaf 0x1c7c2f084c008e00cf8145016d0252010c00300010000c))
 (.branch 84
 (.leaf 0x1c802f104b4080a0d28145016a01de010800480010000c)
 (.leaf 0x1c8035985d509b01144138818b019401e001680020000c)))
 (.branch 87
 (.branch 86
 (.leaf 0x1c4c35785f0098011441390173019601e401700010000c)
 (.leaf 0xe841b802770420061c0a840d3815101ac017c01e80040000d))
 (.branch 88
 (.leaf 0x1c7c2ed04e408660c6814b01c50228003c00280020000c)
 (.branch 89
 (.leaf 0x1c7c2f904cc08960cc813f01c5019c00f400800010000c)
 (.leaf 0x1c7c2f904cc08960cbc13f016701ae01bc02e00010000c))))))
 (.branch 99
 (.branch 94
 (.branch 92
 (.branch 91
 (.leaf 0x1c7c2f304c0087e0cf8145016a0252016c00300010000c)
 (.leaf 0x1bf035805fc0966111413f016701ae01f801780010000c))
 (.branch 93
 (.leaf 0x1ce435985d409ae1144138818b019401cc01680020000c)
 (.leaf 0x34785be0996115c13901730196017401700010000b)))
 (.branch 96
 (.branch 95
 (.leaf 0xe7e1a202f484b206960a880d9815301b0010400780020000d)
 (.leaf 0xe68179c2658450066a09c80c10128020c01cc02000010000d))
 (.branch 97
 (.leaf 0xe6c17fc2598445069a09f80b5013d01f801d001000010000d)
 (.branch 98
 (.leaf 0x1c7c33d05f209920cc813f01690228010400300010000c)
 (.leaf 0xe5e17e026a844f063009c4116819d025801e400280020000d)))))
 (.branch 103
 (.branch 101
 (.branch 100
 (.leaf 0xe5e17b026a045b061a09f40d4813c01f401e401f00030000d)
 (.leaf 0x1c7c2ef04bd083e0cf8145016d025201f400300010000c))
 (.branch 102
 (.leaf 0x1c7c33d05f209920cc813d8166014e016c02080060000c)
 (.leaf 0x1ac02fb858809a20cf01390173019601e802180010000c)))
 (.branch 105
 (.branch 104
 (.leaf 0x1c4c35785c909ce11401388197019401e401680020000c)
 (.leaf 0x1bf035805bc09e6111013e81a301ac01f801680030000c))
 (.branch 106
 (.leaf 0x1c7c2eb04c1067a0a500d8013901da010400780020000c)
 (.branch 107
 (.leaf 0x1c6c2df04cd08ec0ce415601ef01e8010400800030000c)
 (.leaf 0x18002c7042408020d3815180d70106016c027000f0000c)))))))
 (.branch 126
 (.branch 117
 (.branch 112
 (.branch 110
 (.branch 109
 (.leaf 0x1c7c2e504cd06740a800e2817501ea010400f80020000c)
 (.leaf 0xe5e17a426b8451064a09c00d7814c022201e800880010000d))
 (.branch 111
 (.leaf 0xe6e1748277043806200a200ed012101f001a400880010000d)
 (.leaf 0xe5e17dc270843a064a09c00d7814c022201e800880010000d)))
 (.branch 114
 (.branch 113
 (.leaf 0x1c782dd04d408460cb415581d901d001f400780040000c)
 (.leaf 0x17f82d384e408ae0ef818c0173010601ec01200050000c))
 (.branch 115
 (.leaf 0x1ab82fc058e08600ce014e01c50198013400780020000c)
 (.branch 116
 (.leaf 0xbee15e423b843c06880aa011700ee01200138015000f0000d)
 (.leaf 0x1ac42ef84be082a0d3c15981d901c801f400780040000c)))))
 (.branch 121
 (.branch 119
 (.branch 118
 (.leaf 0x1ac42de04bc08700f8015981a201c401f401680040000c)
 (.leaf 0xe66171c275042f06620a940ee015101b001d800780040000d))
 (.branch 120
 (.leaf 0xe6018002650421069c0a8c10301530108017000780070000d)
 (.leaf 0xe6217d0264841507aa0d0810381530126008c00780060000d)))
 (.branch 123
 (.branch 122
 (.leaf 0xe6617a8269843807d40a380bb013e01dc015801700010000d)
 (.leaf 0xe6217d0264841607aa0d080c78153011c016c01180060000d))
 (.branch 124
 (.leaf 0x1abc2fd84f208480cfc17c80cb011e00f4013000f0000c)
 (.branch 125
 (.leaf 0x1a382fe853d097c0cf40ec80e401640104012000f0000c)
 (.leaf 0x1ab42ec04cf08900c700f780f0011c017401180100000c))))))
 (.branch 135
 (.branch 130
 (.branch 128
 (.branch 127
 (.leaf 0xe2a174c2bc04db07fe0cf40bb80e3014c0104012000a0000d)
 (.leaf 0xe2217f025a04460750095c0d200da013a017001780230000d))
 (.branch 129
 (.leaf 0xe2217f025a04460750095c0c101090126017001780230000d)
 (.leaf 0xe241724273043a07a409680ba00e7016800b401300160000d)))
 (.branch 132
 (.branch 131
 (.leaf 0x1ac82ea84e9089a0ef80c680d9010c00b4012001f0000c)
 (.leaf 0x1c802df05aa099a0cc815600cc014e0104009800f0000c))
 (.branch 133
 (.leaf 0x1ce82f584ed082c10181a4827f01f6020802b00100000c)
 (.branch 134
 (.leaf 0x1a8c2fe84be082a100419f82ae0196023c03e800f0000c)
 (.leaf 0x174c2c304f508060d2414b80e30106016c020800f0000c)))))
 (.branch 140
 (.branch 137
 (.branch 136
 (.leaf 0xe2c17e826e847308820cf011700f10108009000f800f0000d)
 (.leaf 0x17cc259042d08080d0414c00e3011e01f802d800f0000c))
 (.branch 138
 (.leaf 0x1a382fe84be07fe0cf414a80e3011e01f0020800f0000c)
 (.branch 139
 (.leaf 0x39085ca096a10181a502a201ae020c020800f0000b)
 (.leaf 0xe801a242ee84b206980a4c0e200e4017c0178020800f0000d))))
 (.branch 142
 (.branch 141
 (.leaf 0xe6217b0258842d075808c00b10104012600b8011800f0000d)
 (.leaf 0xdfc177c2c604cf063209680cd80f0013a0108011800a0000d))
 (.branch 143
 (.leaf 0x1ac82e9857109d20cf00ba80f101080104012001f0000c)
 (.branch 144
 (.leaf 0xe6217b0259042d053008c00b101040120016c017000f0000d)
 (.leaf 0x1ac82f804e708600cd00e280d80156009000f800f0000c)))))))))
def rawLeaves (i : Nat) : List Nat :=
  let code := leafTable.get i
  (PackedRawNatGrowth.readList 15 (PackedRawNatGrowth.take 5 code)
    (PackedRawNatGrowth.drop 5 code)).1

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 3
  | 2 => 7
  | 3 => 2
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
    Papers.RationalityTen.RootedCaches.RootedSixBase00.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase00.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase00.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase00.keys Papers.RationalityTen.RootedCaches.RootedSixBase00.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.FastWords.rawMaps rawLeaves codes counters i
theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 96 leafCount nodeCount (rawNodes i) = true ∧
      SubsumedRawGrowth.nodeCheck Papers.RationalityTen.RootedCaches.RootedSixBase00.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase00.badMasks
        Papers.RationalityTen.RootedCaches.RootedSixBase00.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase00.keys Papers.RationalityTen.RootedCaches.RootedSixBase00.fastKind quota
        Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.FastWords.rawMaps rawLeaves rawNodes i = true :=
  SubsumedCounterReplay.check_sound widths cellCount 1024 96 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixBase00.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase00.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase00.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase00.keys Papers.RationalityTen.RootedCaches.RootedSixBase00.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.FastWords.rawMaps rawLeaves codes counters i h
def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.RootedSixBase00.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0337
