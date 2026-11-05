module
prelude
public import RootedSixExtra00GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport146_000 : List Nat := [36,46,55,58,59,623,626,627,630,633,660,661,664,665,670,672,673,676,677,682,779,782,783,786,789,816,817,820,821,826,828,829]
def ridgeSupport146_001 : List Nat := [832,833,838,935,937,938,940,941,943,945,946,948,949,952,953,956,958,959,961,962,964,966,967,969,970,973,974,999,1000,1002,1003,1004]
def ridgeSupport146_002 : List Nat := [1005,1007,1008,1010,1011,1013,1014,4168,4169,4174,4175,4176,4177,4178,4179,4182,4183,4188,4189,4192,4193,4198,4199,4200,4201,4202,4203,4206,4207,4212,4213,4222]
def ridgeSupport146_003 : List Nat := [4223,4224,4225,4226,4227,4246,4247,4248,4249,4250,4251,4270,4271,4272,4273,4274,4275,4294,4295,4296,4297,4298,4299,4318,4319,4320,4321,4322,4323,4342,4343,4344]
def ridgeSupport146_004 : List Nat := [4345,4346,4347,4363,4365,4366,4367,4368,4369,4370,4371,4373,4376,4379,4382,4656,4657,4674,4675,4692,4693,4697,4700,4703,4706,4710,4711,4728,4729,4746,4747,4764]
def ridgeSupport146_005 : List Nat := [4765,4769,4772,4775,4778,4782,4783,4870,4871,4888,4889,4906,4907,4915,4917,4921,4923,4924,4925,5184,5185,5202,5203,5220,5221,5225,5228,5231,5234,5238,5239,5256]
def ridgeSupport146_006 : List Nat := [5257,5274,5275,5292,5293,5297,5300,5303,5306,5310,5311,5398,5399,5416,5417,5434,5435,5443,5445,5449,5451,5452,5453,7342,7343,7344,7345,7346,7347,8182,8183,8184]
def ridgeSupport146_007 : List Nat := [8185,8186,8187,8203,8205,8206,8207,8208,8209,8215,8217,8218,8219,8220,8221,8273,8276,8286,8287,8291,8294,8304,8305,8329,8331,8338,8339,8393,8396,8406,8407,8411]
def ridgeSupport146_008 : List Nat := [8414,8424,8425,8449,8451,8458,8459]
def ridgeSupport146_code : Nat := 0x210b842a10384060e983a20de836e0d7835a0cc8326093824a08b822607181c2066818e05f817a054814601d807201b806a019805e011804200f803a00d802dffb7fe9ff97fe1ff77fd9cb372c9cb172c1caf72b954d553154b5525545550d53b54e952954a151754594bf52f94ba52dd4b452c54ad52b149b5269489522147751d947251bd46c51a546551914535149441510133d4cf133b4ce53354ccd32b4ca93194c613074c192af4ab92aa4a9d2a44a8529d4a7128b4a2927949e12674999262497d25c49652554951243490923148c111e446d11844551134449111444110f443910d442d0fb43e90f943e10f743d90e343890e143810df43790cb43290c943210c743190b342c90b142c10af42b909b4269099426109742590834209081420107f41f907541d106f41b906b41a906941a10674199061418105d417105741590534149051414104f413904941203f60fd43f30fc83f00fbc3ed0fb03eb0fa83e80f9c3ce0f343ca0f243c70f183c40f083c10efc3be0ef03b90ee03b50ed03b20ec43af0eb43ac0ea83a90e9c3460d043400cf433c0ce83350cd03310cc03150c4830f0c3830b0aa82a50a902a10a8029e0a642980a5429409e427609cc27209bc03b00e803700b8024
def ridgeSupport146_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport146_code
def ridgeSupport146_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport146_code
def ridgeSupport146_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport146_code
def ridgeSupport146_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport146_code
def ridgeSupport146_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport146_code
def ridgeSupport146_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport146_code
def ridgeSupport146_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport146_code
def ridgeSupport146_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport146_code
def ridgeSupport146_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport146_code
def ridgeSupport146_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport146_code
def ridgeSupport146_suffix_009 : List Nat := []
def ridgeSupport146_suffix_008 : List Nat := ridgeSupport146_008 ++ ridgeSupport146_suffix_009
def ridgeSupport146_suffix_007 : List Nat := ridgeSupport146_007 ++ ridgeSupport146_suffix_008
def ridgeSupport146_suffix_006 : List Nat := ridgeSupport146_006 ++ ridgeSupport146_suffix_007
def ridgeSupport146_suffix_005 : List Nat := ridgeSupport146_005 ++ ridgeSupport146_suffix_006
def ridgeSupport146_suffix_004 : List Nat := ridgeSupport146_004 ++ ridgeSupport146_suffix_005
def ridgeSupport146_suffix_003 : List Nat := ridgeSupport146_003 ++ ridgeSupport146_suffix_004
def ridgeSupport146_suffix_002 : List Nat := ridgeSupport146_002 ++ ridgeSupport146_suffix_003
def ridgeSupport146_suffix_001 : List Nat := ridgeSupport146_001 ++ ridgeSupport146_suffix_002
def ridgeSupport146_suffix_000 : List Nat := ridgeSupport146_000 ++ ridgeSupport146_suffix_001
theorem ridgeSupport146_source : candidateSupports 146 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport146_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
