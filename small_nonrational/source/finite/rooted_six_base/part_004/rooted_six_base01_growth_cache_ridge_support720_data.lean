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
def ridgeSupport720_000 : List Nat := [883,884,885,1220,1221,1222,1525,1526,1527,1595,1596,1597,4518,4519,4520,4521,4522,4523,4614,4615,4616,4617,4618,4619,4710,4711,4712,4713,4714,4715,4782,4783]
def ridgeSupport720_001 : List Nat := [4784,4785,4786,4787,4878,4879,4880,4881,4882,4883,4974,4975,4976,4977,4978,4979,5148,5149,5150,5151,5152,5153,5160,5161,5162,5163,5164,5165,6462,6463,6464,6465]
def ridgeSupport720_002 : List Nat := [6466,6467,6510,6511,6512,6513,6514,6515,6654,6655,6656,6657,6658,6659,6798,6799,6800,6801,6802,6803,6828,6829,6830,6831,6832,6833,9476,9477,9482,9483,9496,9497]
def ridgeSupport720_003 : List Nat := [9499,9502,9505,9508,9516,9518,9524,9525,9530,9531,9544,9545,9619,9622,9625,9628,9636,9638,9667,9670,9673,9676,9684,9686,9716,9717,9722,9723,9736,9737,9739,9742]
def ridgeSupport720_004 : List Nat := [9745,9748,9756,9758,9764,9765,9770,9771,9784,9785,9859,9862,9865,9868,9876,9878,9907,9910,9913,9916,9924,9926,10068,10069,10070,10071,10072,10073,10080,10081,10082,10083]
def ridgeSupport720_005 : List Nat := [10084,10085,11011,11014,11017,11020,11028,11030,11036,11037,11042,11043,11056,11057,11084,11085,11090,11091,11104,11105,11179,11182,11185,11188,11196,11198,11214,11215,11216,11217,11218,11219]
def ridgeSupport720_006 : List Nat := [11358,11359,11360,11361,11362,11363,11388,11389,11390,11391,11392,11393,13087,13090,13094,13147,13150,13153,13156,13164,13166,13219,13222,13226,13279,13282,13285,13288,13296,13298,13434,13435]
def ridgeSupport720_007 : List Nat := [13436,13437,13438,13439,14035,14038,14042,14131,14134,14137,14140,14148,14150,14256,14257,14258,14259,14260,14261,14972,14973,14978,14979,14992,14993,15008,15009,15014,15015,15028,15029,15162]
def ridgeSupport720_008 : List Nat := [15167,15168,15173,15181,15183]
def ridgeSupport720_code : Nat := 0x3b4fed37b45ed03b3fecebab5ead3aa7ea9baa1ea83a91ea43a83ea0ba7de9f37b5ded37b3decb7b1dec3746dd1373cdce7736dccf6dadb5b6d3d1ff47ed1f747cd1ef47acfcb3f0cfa33e5cf8b3dfceab3a6ce8f36ecdb3364cd8735ecd6f326cc8b31fb206c80b1fec7eb1f6c7cb18ec62b186c60b17ec5eaf4ebd2af46bd0af3ebceaefabbcaed2bb1aebababad86b60ad4eb52ad36b4cacc6b30ac8eb22ac76b1cac5ab14ac32b09ac1ab039d967649d8e7629d867609d667589d5e7569d567549b1a6c49af26b99ada6b39a5a6949a326899a1a68398e663898ae62a9896624987a61c9852611983a60b982660897ee5fa97d65f4975a5d497325c9971a5c3969a5a49672599965a593952654894ee53a94d653494ba52c9492521947a51b9466518942e50a94165046ac5ab06abdaae6ab5aac6a4da926a45a906a3da8e680da026805a0067fd9fe65cd97265c597065bd96e650d942650594064fd93e50b542c50ad42a50a54285085420507d41e507541c4dcd3724dc53704dbd36e4c4d3124c453104c3d30e4acd2b24ac52b04abd2ae49ad26a49a5268499d266482d20a4825208481d20646ad1aa46a51a8469d1a618f463c18ec5f717d85f513184c513103750dd0373
def ridgeSupport720_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport720_code
def ridgeSupport720_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport720_code
def ridgeSupport720_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport720_code
def ridgeSupport720_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport720_code
def ridgeSupport720_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport720_code
def ridgeSupport720_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport720_code
def ridgeSupport720_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport720_code
def ridgeSupport720_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport720_code
def ridgeSupport720_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport720_code
def ridgeSupport720_rest_009 : Nat := PackedRawNatGrowth.drop 3654 ridgeSupport720_code
def ridgeSupport720_suffix_009 : List Nat := []
def ridgeSupport720_suffix_008 : List Nat := ridgeSupport720_008 ++ ridgeSupport720_suffix_009
def ridgeSupport720_suffix_007 : List Nat := ridgeSupport720_007 ++ ridgeSupport720_suffix_008
def ridgeSupport720_suffix_006 : List Nat := ridgeSupport720_006 ++ ridgeSupport720_suffix_007
def ridgeSupport720_suffix_005 : List Nat := ridgeSupport720_005 ++ ridgeSupport720_suffix_006
def ridgeSupport720_suffix_004 : List Nat := ridgeSupport720_004 ++ ridgeSupport720_suffix_005
def ridgeSupport720_suffix_003 : List Nat := ridgeSupport720_003 ++ ridgeSupport720_suffix_004
def ridgeSupport720_suffix_002 : List Nat := ridgeSupport720_002 ++ ridgeSupport720_suffix_003
def ridgeSupport720_suffix_001 : List Nat := ridgeSupport720_001 ++ ridgeSupport720_suffix_002
def ridgeSupport720_suffix_000 : List Nat := ridgeSupport720_000 ++ ridgeSupport720_suffix_001
theorem ridgeSupport720_source : candidateRows 720 =
    (PackedRawNatGrowth.readList 14 261 ridgeSupport720_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
