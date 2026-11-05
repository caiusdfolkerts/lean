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
def ridgeSupport736_000 : List Nat := [1304,1305,1306,1413,1414,1415,1522,1523,1524,1620,1621,1622,5478,5479,5480,5481,5482,5483,5574,5575,5576,5577,5578,5579,5670,5671,5672,5673,5674,5675,5742,5743]
def ridgeSupport736_001 : List Nat := [5744,5745,5746,5747,5838,5839,5840,5841,5842,5843,5934,5935,5936,5937,5938,5939,6108,6109,6110,6111,6112,6113,6120,6121,6122,6123,6124,6125,6438,6439,6440,6441]
def ridgeSupport736_002 : List Nat := [6442,6443,6534,6535,6536,6537,6538,6539,6630,6631,6632,6633,6634,6635,6804,6805,6806,6807,6808,6809,6816,6817,6818,6819,6820,6821,10244,10245,10250,10251,10264,10265]
def ridgeSupport736_003 : List Nat := [10267,10270,10273,10276,10284,10286,10292,10293,10298,10299,10312,10313,10387,10390,10393,10396,10404,10406,10435,10438,10441,10444,10452,10454,10484,10485,10490,10491,10504,10505,10507,10510]
def ridgeSupport736_004 : List Nat := [10513,10516,10524,10526,10532,10533,10538,10539,10552,10553,10627,10630,10633,10636,10644,10646,10675,10678,10681,10684,10692,10694,10836,10837,10838,10839,10840,10841,10848,10849,10850,10851]
def ridgeSupport736_005 : List Nat := [10852,10853,11012,11013,11018,11019,11032,11033,11035,11038,11041,11044,11052,11054,11060,11061,11066,11067,11080,11081,11155,11158,11161,11164,11172,11174,11203,11206,11209,11212,11220,11222]
def ridgeSupport736_006 : List Nat := [11364,11365,11366,11367,11368,11369,11376,11377,11378,11379,11380,11381,13567,13570,13574,13627,13630,13633,13636,13644,13646,13699,13702,13706,13759,13762,13765,13768,13776,13778,13914,13915]
def ridgeSupport736_007 : List Nat := [13916,13917,13918,13919,14047,14050,14054,14107,14110,14113,14116,14124,14126,14262,14263,14264,14265,14266,14267,15068,15069,15074,15075,15088,15089,15104,15105,15110,15111,15124,15125,15164]
def ridgeSupport736_008 : List Nat := [15165,15170,15171,15184,15185]
def ridgeSupport736_code : Nat := 0x3b51ed43b43ed0bb3decf3b15ec53b07ec1bb01ec03af1ebc3ae3eb8baddeb737bbdeeb7b9dee37b7dedb72edcb3724dc8771edc6f6e6db8b6dfd97f65ed97765cd96f65ad74b5d0d7235c5d70b5bfd62b586d60f54ed533544d50753ed4ef506d40b4ffb1d6c74b1cec72b1c6c70b1a6c68b19ec66b196c64af5abd4af32bc9af1abc3ae9aba4ae72b99ae5ab93ad26b48aceeb3aacd6b34acbab2cac92b21ac7ab1bac66b18ac2eb0aac16b04a996a64a98ea62a986a60a966a58a95ea56a956a54a71a9c4a6f29b9a6da9b3a65a994a632989a61a983a4e6938a4ae92aa496924a47a91ca452911a43a90ba426908a3ee8faa3d68f4a35a8d4a3328c9a31a8c3a29a8a4a272899a25a893a126848a0ee83aa0d6834a0ba82ca092821a07a81ba066818a02e80aa0168046a95aa46a8daa26a85aa06a65a986a5da966a55a9467ad9ea67a59e8679d9e6662d98a6625988661d98664ad92a64a5928649d9265fb57ec5fad7ea5fa57e85f857e05f7d7de5f757dc5ccd7325cc57305cbd72e5b4d6d25b456d05b3d6ce59cd67259c567059bd66e58ad62a58a5628589d626572d5ca57255c8571d5c655ad56a55a5568559d566195865519505f417cc5f2161c586161451a1464518
def ridgeSupport736_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport736_code
def ridgeSupport736_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport736_code
def ridgeSupport736_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport736_code
def ridgeSupport736_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport736_code
def ridgeSupport736_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport736_code
def ridgeSupport736_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport736_code
def ridgeSupport736_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport736_code
def ridgeSupport736_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport736_code
def ridgeSupport736_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport736_code
def ridgeSupport736_rest_009 : Nat := PackedRawNatGrowth.drop 3654 ridgeSupport736_code
def ridgeSupport736_suffix_009 : List Nat := []
def ridgeSupport736_suffix_008 : List Nat := ridgeSupport736_008 ++ ridgeSupport736_suffix_009
def ridgeSupport736_suffix_007 : List Nat := ridgeSupport736_007 ++ ridgeSupport736_suffix_008
def ridgeSupport736_suffix_006 : List Nat := ridgeSupport736_006 ++ ridgeSupport736_suffix_007
def ridgeSupport736_suffix_005 : List Nat := ridgeSupport736_005 ++ ridgeSupport736_suffix_006
def ridgeSupport736_suffix_004 : List Nat := ridgeSupport736_004 ++ ridgeSupport736_suffix_005
def ridgeSupport736_suffix_003 : List Nat := ridgeSupport736_003 ++ ridgeSupport736_suffix_004
def ridgeSupport736_suffix_002 : List Nat := ridgeSupport736_002 ++ ridgeSupport736_suffix_003
def ridgeSupport736_suffix_001 : List Nat := ridgeSupport736_001 ++ ridgeSupport736_suffix_002
def ridgeSupport736_suffix_000 : List Nat := ridgeSupport736_000 ++ ridgeSupport736_suffix_001
theorem ridgeSupport736_source : candidateRows 736 =
    (PackedRawNatGrowth.readList 14 261 ridgeSupport736_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
