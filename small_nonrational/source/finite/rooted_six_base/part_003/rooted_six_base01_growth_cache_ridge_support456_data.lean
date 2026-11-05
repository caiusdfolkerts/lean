module
prelude
public import RootedSixBase01GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport456_000 : List Nat := [509,510,511,778,779,780,1043,1044,1045,1395,1396,1397,1489,1490,1491,2868,2869,2870,2871,2872,2873,2964,2965,2966,2967,2968,2969,3060,3061,3062,3063,3064]
def ridgeSupport456_001 : List Nat := [3065,3132,3133,3134,3135,3136,3137,3228,3229,3230,3231,3232,3233,3324,3325,3326,3327,3328,3329,3384,3385,3386,3387,3388,3389,3396,3397,3398,3399,3400,3401,3828]
def ridgeSupport456_002 : List Nat := [3829,3830,3831,3832,3833,3924,3925,3926,3927,3928,3929,4020,4021,4022,4023,4024,4025,4080,4081,4082,4083,4084,4085,4092,4093,4094,4095,4096,4097,5772,5773,5774]
def ridgeSupport456_003 : List Nat := [5775,5776,5777,5820,5821,5822,5823,5824,5825,5964,5965,5966,5967,5968,5969,5994,5995,5996,5997,5998,5999,6024,6025,6026,6027,6028,6029,8182,8183,8188,8189,8194]
def ridgeSupport456_004 : List Nat := [8195,8202,8204,8208,8210,8214,8216,8230,8231,8236,8237,8242,8243,8322,8324,8328,8330,8334,8336,8370,8372,8376,8378,8382,8384,8422,8423,8428,8429,8434,8435,8442]
def ridgeSupport456_005 : List Nat := [8444,8448,8450,8454,8456,8470,8471,8476,8477,8482,8483,8562,8564,8568,8570,8574,8576,8610,8612,8616,8618,8622,8624,8700,8701,8702,8703,8704,8705,8712,8713,8714]
def ridgeSupport456_006 : List Nat := [8715,8716,8717,8950,8951,8956,8957,8962,8963,8970,8972,8976,8978,8982,8984,8998,8999,9004,9005,9010,9011,9090,9092,9096,9098,9102,9104,9138,9140,9144,9146,9150]
def ridgeSupport456_007 : List Nat := [9152,9228,9229,9230,9231,9232,9233,9240,9241,9242,9243,9244,9245,10482,10484,10488,10490,10494,10496,10510,10511,10516,10517,10522,10523,10558,10559,10564,10565,10570,10571,10650]
def ridgeSupport456_008 : List Nat := [10652,10656,10658,10662,10664,10692,10693,10694,10695,10696,10697,10758,10759,10760,10761,10762,10763,10788,10789,10790,10791,10792,10793,12258,12260,12264,12318,12320,12324,12326,12330,12332]
def ridgeSupport456_009 : List Nat := [12390,12392,12396,12450,12452,12456,12458,12462,12464,12552,12553,12554,12555,12556,12557,12738,12740,12744,12798,12800,12804,12806,12810,12812,12900,12901,12902,12903,12904,12905,13686,13688]
def ridgeSupport456_010 : List Nat := [13692,13782,13784,13788,13790,13794,13796,13854,13855,13856,13857,13858,13859,14818,14819,14824,14825,14830,14831,14854,14855,14860,14861,14866,14867,14914,14915,14920,14921,14926,14927,15103]
def ridgeSupport456_011 : List Nat := [15105,15109,15111,15115,15117]
def ridgeSupport456_code : Nat := 0x3b0dec2fb07ec17b01ebffa4fe93ba49e923a43e90ba13e84ba0de833a07e81b9efe7bb9e9e7a39e3e78b623d88b621d88361fd87b5e4d78b5ded7735d8d75b57cd5e3576c9a7268c99f266c997264c83320ac81b204c8031fec7231c4c70b10dc43310bc42b109c4230b0c2bb0aac2a30a4c28b06cc1a3066c0b302ac09b024c08301ebfa2fe4bf8aa29a8a2a27a89aa25a892a0ba82aa09a822a07a81a9c9a7229c7a71a9c5a7129a8a69a9a2a68299ca66a94ba52a945a51293fa4fa91ba46a915a45290fa43a900a3fa8faa3e28f4a3ca41d907241b906a4199062411904240f903a40d90323c08efa3ba8ee23b48eca3908e3a38a8e223848e0a3338cca32d8cb23278c9a3188c5a3128c4230c8c2a3038c0a2fd8bf22f78bda20d883220b882a209882220188021ff87fa1fd87f21b086ba1aa86a21a4868a18085fa17a85e217485ca123848a11d8472117845a108841a10284020fc83ea0f383ca0ed83b20e7839a0c082fa0ba82e20b482ca090823a08a8222084820a03380ca02d80b2027809a018805a012804200c802a0038009ffd7ff1ff77fd978d5e3178b5e297895e2176f5db976d5db176b5da97515d4174f5d3974d5d316c15b016bf5af96bd5af16915a4168f5a3968d5a310014000fff3ff8ffd3ff0ff53fd0ff33fc8ff13fc0fb93ee0fb73ed8fb53ed0f593d60f573d58f553d50ef93be0ef73bd8ef53bd0d493520d473518d453510d3d34f0d3b34e8d3934e0d013400cff33f8cfd33f0ca13280c9f3278c9d3270c413100c3f30f8c3d30f0bf92fe0bf72fd8bf52fd0b992e60b972e58b952e50b392ce0b372cd8b352cd05d317485d115d457415cc41510504130c3030b0c281ff07f81fd
def ridgeSupport456_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport456_code
def ridgeSupport456_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport456_code
def ridgeSupport456_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport456_code
def ridgeSupport456_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport456_code
def ridgeSupport456_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport456_code
def ridgeSupport456_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport456_code
def ridgeSupport456_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport456_code
def ridgeSupport456_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport456_code
def ridgeSupport456_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport456_code
def ridgeSupport456_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport456_code
def ridgeSupport456_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport456_code
def ridgeSupport456_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport456_code
def ridgeSupport456_rest_012 : Nat := PackedRawNatGrowth.drop 4998 ridgeSupport456_code
def ridgeSupport456_suffix_012 : List Nat := []
def ridgeSupport456_suffix_011 : List Nat := ridgeSupport456_011 ++ ridgeSupport456_suffix_012
def ridgeSupport456_suffix_010 : List Nat := ridgeSupport456_010 ++ ridgeSupport456_suffix_011
def ridgeSupport456_suffix_009 : List Nat := ridgeSupport456_009 ++ ridgeSupport456_suffix_010
def ridgeSupport456_suffix_008 : List Nat := ridgeSupport456_008 ++ ridgeSupport456_suffix_009
def ridgeSupport456_suffix_007 : List Nat := ridgeSupport456_007 ++ ridgeSupport456_suffix_008
def ridgeSupport456_suffix_006 : List Nat := ridgeSupport456_006 ++ ridgeSupport456_suffix_007
def ridgeSupport456_suffix_005 : List Nat := ridgeSupport456_005 ++ ridgeSupport456_suffix_006
def ridgeSupport456_suffix_004 : List Nat := ridgeSupport456_004 ++ ridgeSupport456_suffix_005
def ridgeSupport456_suffix_003 : List Nat := ridgeSupport456_003 ++ ridgeSupport456_suffix_004
def ridgeSupport456_suffix_002 : List Nat := ridgeSupport456_002 ++ ridgeSupport456_suffix_003
def ridgeSupport456_suffix_001 : List Nat := ridgeSupport456_001 ++ ridgeSupport456_suffix_002
def ridgeSupport456_suffix_000 : List Nat := ridgeSupport456_000 ++ ridgeSupport456_suffix_001
theorem ridgeSupport456_source : candidateRows 456 =
    (PackedRawNatGrowth.readList 14 357 ridgeSupport456_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
