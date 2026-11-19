module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public meta import CertificateNumbers
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
cert_ridgeSupport_7 146 008 8414 8424 8425 8449 8451 8458 8459
cert_ridgeSupport_code_3 146
cert_ridgeSupport_rest_2 146 000 0
cert_ridgeSupport_rest_2 146 001 448
cert_ridgeSupport_rest_2 146 002 896
cert_ridgeSupport_rest_2 146 003 1344
cert_ridgeSupport_rest_2 146 004 1792
cert_ridgeSupport_rest_2 146 005 2240
cert_ridgeSupport_rest_2 146 006 2688
cert_ridgeSupport_rest_2 146 007 3136
cert_ridgeSupport_rest_2 146 008 3584
cert_ridgeSupport_rest_2 146 009 3682
cert_ridgeSupport_suffix_4 146 009
cert_ridgeSupport_suffix_3 146 008 009
cert_ridgeSupport_suffix_3 146 007 008
cert_ridgeSupport_suffix_3 146 006 007
cert_ridgeSupport_suffix_3 146 005 006
cert_ridgeSupport_suffix_3 146 004 005
cert_ridgeSupport_suffix_3 146 003 004
cert_ridgeSupport_suffix_3 146 002 003
cert_ridgeSupport_suffix_3 146 001 002
cert_ridgeSupport_suffix_3 146 000 001
cert_ridgeSupport_source_3 146 14 263
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
