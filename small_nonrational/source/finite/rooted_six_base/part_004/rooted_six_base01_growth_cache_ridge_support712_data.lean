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
def ridgeSupport712_000 : List Nat := [530,531,532,799,800,801,1064,1065,1066,1416,1417,1418,1486,1487,1488,2862,2863,2864,2865,2866,2867,2958,2959,2960,2961,2962,2963,3054,3055,3056,3057,3058]
def ridgeSupport712_001 : List Nat := [3059,3126,3127,3128,3129,3130,3131,3222,3223,3224,3225,3226,3227,3318,3319,3320,3321,3322,3323,3492,3493,3494,3495,3496,3497,3504,3505,3506,3507,3508,3509,3822]
def ridgeSupport712_002 : List Nat := [3823,3824,3825,3826,3827,3918,3919,3920,3921,3922,3923,4014,4015,4016,4017,4018,4019,4188,4189,4190,4191,4192,4193,4200,4201,4202,4203,4204,4205,5766,5767,5768]
def ridgeSupport712_003 : List Nat := [5769,5770,5771,5814,5815,5816,5817,5818,5819,5958,5959,5960,5961,5962,5963,6102,6103,6104,6105,6106,6107,6132,6133,6134,6135,6136,6137,8180,8181,8186,8187,8200]
def ridgeSupport712_004 : List Nat := [8201,8203,8206,8209,8212,8220,8222,8228,8229,8234,8235,8248,8249,8323,8326,8329,8332,8340,8342,8371,8374,8377,8380,8388,8390,8420,8421,8426,8427,8440,8441,8443]
def ridgeSupport712_005 : List Nat := [8446,8449,8452,8460,8462,8468,8469,8474,8475,8488,8489,8563,8566,8569,8572,8580,8582,8611,8614,8617,8620,8628,8630,8772,8773,8774,8775,8776,8777,8784,8785,8786]
def ridgeSupport712_006 : List Nat := [8787,8788,8789,8948,8949,8954,8955,8968,8969,8971,8974,8977,8980,8988,8990,8996,8997,9002,9003,9016,9017,9091,9094,9097,9100,9108,9110,9139,9142,9145,9148,9156]
def ridgeSupport712_007 : List Nat := [9158,9300,9301,9302,9303,9304,9305,9312,9313,9314,9315,9316,9317,10483,10486,10489,10492,10500,10502,10508,10509,10514,10515,10528,10529,10556,10557,10562,10563,10576,10577,10651]
def ridgeSupport712_008 : List Nat := [10654,10657,10660,10668,10670,10686,10687,10688,10689,10690,10691,10830,10831,10832,10833,10834,10835,10860,10861,10862,10863,10864,10865,12259,12262,12266,12319,12322,12325,12328,12336,12338]
def ridgeSupport712_009 : List Nat := [12391,12394,12398,12451,12454,12457,12460,12468,12470,12606,12607,12608,12609,12610,12611,12739,12742,12746,12799,12802,12805,12808,12816,12818,12954,12955,12956,12957,12958,12959,13687,13690]
def ridgeSupport712_010 : List Nat := [13694,13783,13786,13789,13792,13800,13802,13908,13909,13910,13911,13912,13913,14816,14817,14822,14823,14836,14837,14852,14853,14858,14859,14872,14873,14912,14913,14918,14919,14932,14933,15102]
def ridgeSupport712_011 : List Nat := [15107,15108,15113,15121,15123]
def ridgeSupport712_code : Nat := 0x3b13ec47b09ec13b03ebfba55e953a47e91ba41e903a19e863a0be82ba05e8139f5e7d39e7e79b9e1e783659d963657d95b655d9535ead7a35e0d7775dad75f57ed5eb577ca7f29eca7729cca6f29ac84b210c823205c80b1ffc72b1c6c70f143c50b141c50313fc4fb0b6c2d30acc2a70a6c28f06ec1ab067c0cb030c0a3025c08b01fbfaafe6bf8ea71a9c2a6fa9baa6da9b2a53a94aa51a942a4fa93a9c3a70a9c1a7029bfa6fa9aea6b29a4a68699ea66e951a542943a50a93da4f2921a482913a44a90da432906a4128fca3e68f6a3ce4659192463918a46191824599162457915a45591523c68f123bc8ee63b68ece3968e5238c8e263868e0e3398ce232b8caa3258c9231e8c723148c4630e8c2e3098c222fb8bea2f58bd22558952253894a25189422498922247891a24589121b686d21ac86a61a6868e186861217c85e617685ce12984a211b846a115845210e843210484060fe83ee0f983e20eb83aa0e583920c683120bc82e60b682ce096825208c8226086820e03980e202b80aa025809201e8072014804600e802e0098021ffb7fe9ff57fd17f95fe17f75fd97f55fd17db5f697d95f617d75f5974b5d297495d217475d196bb5ae96b95ae16b75ad968b5a296895a216875a1906d41b106b41a906941a1061418105f417905d4170fb33ec8fb13ec0faf3eb8f533d48f513d40f4f3d38ef33bc8ef13bc0eef3bb8db536d0db336c8db136c0da936a0da73698da53690cfb33e8cf933e0cf733d8c9b3268c993260c973258c3b30e8c3930e0c3730d8bf32fc8bf12fc0bef2fb8b932e48b912e40b8f2e38b332cc8b312cc0b2f2cb85d0173c5ce1628589162042a10a44280c843200c7c214084c212
def ridgeSupport712_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport712_code
def ridgeSupport712_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport712_code
def ridgeSupport712_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport712_code
def ridgeSupport712_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport712_code
def ridgeSupport712_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport712_code
def ridgeSupport712_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport712_code
def ridgeSupport712_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport712_code
def ridgeSupport712_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport712_code
def ridgeSupport712_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport712_code
def ridgeSupport712_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport712_code
def ridgeSupport712_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport712_code
def ridgeSupport712_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport712_code
def ridgeSupport712_rest_012 : Nat := PackedRawNatGrowth.drop 4998 ridgeSupport712_code
def ridgeSupport712_suffix_012 : List Nat := []
def ridgeSupport712_suffix_011 : List Nat := ridgeSupport712_011 ++ ridgeSupport712_suffix_012
def ridgeSupport712_suffix_010 : List Nat := ridgeSupport712_010 ++ ridgeSupport712_suffix_011
def ridgeSupport712_suffix_009 : List Nat := ridgeSupport712_009 ++ ridgeSupport712_suffix_010
def ridgeSupport712_suffix_008 : List Nat := ridgeSupport712_008 ++ ridgeSupport712_suffix_009
def ridgeSupport712_suffix_007 : List Nat := ridgeSupport712_007 ++ ridgeSupport712_suffix_008
def ridgeSupport712_suffix_006 : List Nat := ridgeSupport712_006 ++ ridgeSupport712_suffix_007
def ridgeSupport712_suffix_005 : List Nat := ridgeSupport712_005 ++ ridgeSupport712_suffix_006
def ridgeSupport712_suffix_004 : List Nat := ridgeSupport712_004 ++ ridgeSupport712_suffix_005
def ridgeSupport712_suffix_003 : List Nat := ridgeSupport712_003 ++ ridgeSupport712_suffix_004
def ridgeSupport712_suffix_002 : List Nat := ridgeSupport712_002 ++ ridgeSupport712_suffix_003
def ridgeSupport712_suffix_001 : List Nat := ridgeSupport712_001 ++ ridgeSupport712_suffix_002
def ridgeSupport712_suffix_000 : List Nat := ridgeSupport712_000 ++ ridgeSupport712_suffix_001
theorem ridgeSupport712_source : candidateRows 712 =
    (PackedRawNatGrowth.readList 14 357 ridgeSupport712_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
