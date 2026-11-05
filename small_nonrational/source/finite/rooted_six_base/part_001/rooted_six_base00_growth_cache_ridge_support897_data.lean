module
prelude
public import RootedSixBase00GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport897_000 : List Nat := [349,350,351,505,506,507,589,590,591,611,612,613,5920,5921,5922,5923,5924,5925,5968,5969,5970,5971,5972,5973,6112,6113,6114,6115,6116,6117,6184,6185]
def ridgeSupport897_001 : List Nat := [6186,6187,6188,6189,6232,6233,6234,6235,6236,6237,6376,6377,6378,6379,6380,6381,7024,7025,7026,7027,7028,7029,7036,7037,7038,7039,7040,7041,7144,7145,7146,7147]
def ridgeSupport897_002 : List Nat := [7148,7149,7192,7193,7194,7195,7196,7197,7336,7337,7338,7339,7340,7341,7984,7985,7986,7987,7988,7989,7996,7997,7998,7999,8000,8001,8680,8681,8682,8683,8684,8685]
def ridgeSupport897_003 : List Nat := [8692,8693,8694,8695,8696,8697,12529,12531,12535,12537,12541,12543,12550,12551,12556,12557,12562,12563,12598,12599,12604,12605,12610,12611,12697,12699,12703,12705,12709,12711,12712,12713]
def ridgeSupport897_004 : List Nat := [12714,12715,12716,12717,12769,12771,12775,12777,12781,12783,12790,12791,12796,12797,12802,12803,12838,12839,12844,12845,12850,12851,12937,12939,12943,12945,12949,12951,12952,12953,12954,12955]
def ridgeSupport897_005 : List Nat := [12956,12957,13504,13505,13506,13507,13508,13509,13516,13517,13518,13519,13520,13521,13537,13539,13543,13545,13549,13551,13558,13559,13564,13565,13570,13571,13606,13607,13612,13613,13618,13619]
def ridgeSupport897_006 : List Nat := [13705,13707,13711,13713,13717,13719,13720,13721,13722,13723,13724,13725,14272,14273,14274,14275,14276,14277,14284,14285,14286,14287,14288,14289,14800,14801,14802,14803,14804,14805,14812,14813]
def ridgeSupport897_007 : List Nat := [14814,14815,14816,14817,17711,17713,17715,17809,17811,17815,17817,17821,17823,17843,17845,17847,17941,17943,17947,17949,17953,17955,18310,18311,18312,18313,18314,18315,18323,18325,18327,18421]
def ridgeSupport897_008 : List Nat := [18423,18427,18429,18433,18435,18790,18791,18792,18793,18794,18795,19138,19139,19140,19141,19142,19143,21360,21362,21366,21368,21372,21374,21396,21398,21402,21404,21408,21410,21492,21494,21498]
def ridgeSupport897_009 : List Nat := [21500,21504,21506]
def ridgeSupport897_code : Nat := 0x1500aa0053fca7f54fda9fa53a2a7414e729cd5396a7294dfa9be5378a6ed4dca9b84ac7958d2b165624ac3958525ae4b5496992d1259e4b3480390031ff63fdc7f78feb1e5e3cac7938f171e2a3c4c7888f0f1e1a311c6218c3b186e30bc6158b6f16d62d9c59f8b3b16662cbc5938b2314ce298c52f73c2e781cefb9de73bae771ceab9d473a6e749ce8b9d06fa2df41be7b7ce6f9adf31be2b7c46f86df09be0b7c06b3ad671acdb59a6b32d661acbb5956b22d63dac5b5896a66d4c9a96b52c6a4ed499a81b50269fad3f1a7bb4f669ded3b5a74b4e769c6d385a68b4d0699ed339a66b4cc698ad311a61b4c26982d30194eb29c6536ca6994cb298652eca55948b28f6516ca25919b232645ac8b1913b2266406c8098feb1fc63eec7d98f7b1ed63d2c79d8f1b1e1635ac6b18d5b1aa6352c6a18d3b1a56342c67d8cdb1996286c50989eb13c626ec4d9889b112621ac431883b10661fec3f587cb0f761e6c3c50fca1f843ee87d90faa1f443da87b10f5a1ea43d287a0fa09f403e7e7cf8f9e9f3c3e6a7cd0f999f323e627cc0e569cac395672a8e549ca8383a7070e0d9c1a38327060df69bec37d66fa8df49be837026e00dbf9b7e36fa6df0dba9b7436e66dc8db89b7031da63b0c7598ea31d263a0c2e985c30b66168c2c9858305a60b0c15982a305260a0bf297e42fc65f88bf097e02eaa5d50ba997522ea25d40b9297242e465c88b90972004ca0990131824f049c09340fd81fa03f2057c0af015d
def ridgeSupport897_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport897_code
def ridgeSupport897_rest_001 : Nat := PackedRawNatGrowth.drop 480 ridgeSupport897_code
def ridgeSupport897_rest_002 : Nat := PackedRawNatGrowth.drop 960 ridgeSupport897_code
def ridgeSupport897_rest_003 : Nat := PackedRawNatGrowth.drop 1440 ridgeSupport897_code
def ridgeSupport897_rest_004 : Nat := PackedRawNatGrowth.drop 1920 ridgeSupport897_code
def ridgeSupport897_rest_005 : Nat := PackedRawNatGrowth.drop 2400 ridgeSupport897_code
def ridgeSupport897_rest_006 : Nat := PackedRawNatGrowth.drop 2880 ridgeSupport897_code
def ridgeSupport897_rest_007 : Nat := PackedRawNatGrowth.drop 3360 ridgeSupport897_code
def ridgeSupport897_rest_008 : Nat := PackedRawNatGrowth.drop 3840 ridgeSupport897_code
def ridgeSupport897_rest_009 : Nat := PackedRawNatGrowth.drop 4320 ridgeSupport897_code
def ridgeSupport897_rest_010 : Nat := PackedRawNatGrowth.drop 4365 ridgeSupport897_code
def ridgeSupport897_suffix_010 : List Nat := []
def ridgeSupport897_suffix_009 : List Nat := ridgeSupport897_009 ++ ridgeSupport897_suffix_010
def ridgeSupport897_suffix_008 : List Nat := ridgeSupport897_008 ++ ridgeSupport897_suffix_009
def ridgeSupport897_suffix_007 : List Nat := ridgeSupport897_007 ++ ridgeSupport897_suffix_008
def ridgeSupport897_suffix_006 : List Nat := ridgeSupport897_006 ++ ridgeSupport897_suffix_007
def ridgeSupport897_suffix_005 : List Nat := ridgeSupport897_005 ++ ridgeSupport897_suffix_006
def ridgeSupport897_suffix_004 : List Nat := ridgeSupport897_004 ++ ridgeSupport897_suffix_005
def ridgeSupport897_suffix_003 : List Nat := ridgeSupport897_003 ++ ridgeSupport897_suffix_004
def ridgeSupport897_suffix_002 : List Nat := ridgeSupport897_002 ++ ridgeSupport897_suffix_003
def ridgeSupport897_suffix_001 : List Nat := ridgeSupport897_001 ++ ridgeSupport897_suffix_002
def ridgeSupport897_suffix_000 : List Nat := ridgeSupport897_000 ++ ridgeSupport897_suffix_001
theorem ridgeSupport897_source : candidateRows 897 =
    (PackedRawNatGrowth.readList 15 291 ridgeSupport897_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase00
