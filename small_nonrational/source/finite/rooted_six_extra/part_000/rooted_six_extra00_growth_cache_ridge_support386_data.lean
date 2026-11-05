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
def ridgeSupport386_000 : List Nat := [12,42,52,58,61,64,166,167,170,171,174,175,238,239,242,243,246,247,275,276,277,280,281,286,287,292,294,337,338,342,344,345]
def ridgeSupport386_001 : List Nat := [349,351,352,354,661,662,663,664,665,666,695,699,700,701,702,704,705,712,714,760,761,762,765,766,767,769,774,776,817,818,819,820]
def ridgeSupport386_002 : List Nat := [821,822,851,855,856,857,858,860,861,868,870,916,917,918,921,922,923,925,930,932,935,939,940,941,942,944,945,952,954,1000,1001,1002]
def ridgeSupport386_003 : List Nat := [1005,1006,1007,1009,1014,1016,1019,1022,1023,1024,1027,1028,1029,1031,1036,1037,1039,1040,1865,1867,1884,1886,1944,1945,1950,1951,1964,1965,1967,1970,1973,1976]
def ridgeSupport386_004 : List Nat := [1978,1979,1992,1993,1998,1999,2033,2035,2040,2041,2046,2047,2052,2054,2060,2061,2074,2075,2084,2085,2098,2099,2369,2371,2388,2390,2400,2401,2406,2407,2448,2449]
def ridgeSupport386_005 : List Nat := [2454,2455,2468,2469,2471,2474,2477,2480,2482,2483,2489,2491,2496,2497,2502,2503,2508,2510,2544,2545,2550,2551,2568,2569,2574,2575,2586,2588,2616,2618,2626,2627]
def ridgeSupport386_006 : List Nat := [2644,2645,2801,2803,2831,2833,2846,2847,2864,2865,3137,3139,3156,3158,3168,3169,3174,3175,3216,3217,3222,3223,3236,3237,3239,3242,3245,3248,3250,3251,3257,3259]
def ridgeSupport386_007 : List Nat := [3264,3265,3270,3271,3276,3278,3312,3313,3318,3319,3336,3337,3342,3343,3354,3356,3384,3386,3394,3395,3412,3413,3569,3571,3599,3601,3614,3615,3632,3633,4193,4195]
def ridgeSupport386_008 : List Nat := [4212,4214,4224,4225,4230,4231,4272,4273,4278,4279,4292,4293,4295,4298,4301,4304,4306,4307,4313,4315,4320,4321,4326,4327,4332,4334,4368,4369,4374,4375,4392,4393]
def ridgeSupport386_009 : List Nat := [4398,4399,4662,4664,4674,4676,4702,4703,4714,4715,4877,4879,4889,4891,4922,4923,4934,4935,5190,5192,5202,5204,5230,5231,5242,5243,5405,5407,5417,5419,5450,5451]
def ridgeSupport386_010 : List Nat := [5462,5463,7076,7077,7150,7151,7246,7247,7366,7367,7680,7681,7686,7687,7696,7698,7700,7701,7704,7707,7775,7778,7781,7784,7804,7806,7808,7809,7812,7815,7822,7823]
def ridgeSupport386_011 : List Nat := [7825,7827,7876,7878,7880,7881,7943,7946,7949,7952,7972,7974,7976,7977,7980,7983,7990,7991,7993,7995,8044,8046,8048,8049,8183,8186,8189,8192,8212,8214,8216,8217]
def ridgeSupport386_012 : List Nat := [8220,8223,8284,8285,8287,8289,8338,8340,8342,8343,8404,8405,8407,8409,8458,8460,8462,8463]
def ridgeSupport386_code : Nat := 0x843e10e843210a83660d783560d4825e0968252092818605f817605c807e01c8066018805a0148001ffd7fe9ff77dc5f707db9f6c7cedf397cddf367cbdf2c7ca5f287c99f247c41f0d7c29f077b25ec87b19ec47a4de917a3de8e7a1de847a05e8079f9e7c79a1e657989e5f786de187855e147849e10781de067805e00731dcc6713dc4e6fbdbee6e95ba4555d556552d54a54ad529547d51d51ed47a51bd46e515145251214464d1d3464ced33a4c6d3194c3d30d49ad26a497d25e491124248e123644bd12e44a5128445d116444511043b90ec439d0e643850e0436d0d9434d0d243410cd43290c743150c442dd0b642c50b0421d086420508041d9074418d06138c4e30387ce1e3844e0f37ccdf13554d54350cd4234e8d383470d1a343cd0e3424d0833dccf633c4cf03338ccc331ccc63304cc032eccb932cccb232c0cad32a8ca73294ca4325cc963244c90319cc663184c603158c54310cc412cc4b302c7cb1e2c44b0f2bccaf12954a54290ca4228e8a382870a1a283ca0e2824a0827dc9f627c49f027389cc271c9c627049c026ec9b926cc9b226c09ad26a89a726949a4265c9962644990259c96625849602558954250c94120cc8322094824206c81a203480c20188041ffc7fe1fe47f81fcc7f11f3c7ce1f247c81eec7ba1ee07b51ec87af1eb47ac1e7c79e1e647981d7875c1d2c749104040f103440c101c405101040310003ff0ff83fb0fe03f60fc43ef0fb83ed0fa83e90fa03ba0ee03b10ec03ae0eb43ac0eac3a70e903a20e7439b0e683990e583950e503660d9035d0d7035a0d643580d5c3530cd83350cd03330cc83310c203060c042ff0bf82fd0be82f90be02ca0b202c10b002be0af42bc0aec2b70a682990a602970a582950588160057c15d056415805581520544126049011f04781190460115045011303dc0f603cc0f203bc0ee02bc0ae02ac0aa029c0a6010003d00e803400a800c
def ridgeSupport386_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport386_code
def ridgeSupport386_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport386_code
def ridgeSupport386_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport386_code
def ridgeSupport386_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport386_code
def ridgeSupport386_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport386_code
def ridgeSupport386_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport386_code
def ridgeSupport386_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport386_code
def ridgeSupport386_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport386_code
def ridgeSupport386_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport386_code
def ridgeSupport386_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport386_code
def ridgeSupport386_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport386_code
def ridgeSupport386_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport386_code
def ridgeSupport386_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport386_code
def ridgeSupport386_rest_013 : Nat := PackedRawNatGrowth.drop 5628 ridgeSupport386_code
def ridgeSupport386_suffix_013 : List Nat := []
def ridgeSupport386_suffix_012 : List Nat := ridgeSupport386_012 ++ ridgeSupport386_suffix_013
def ridgeSupport386_suffix_011 : List Nat := ridgeSupport386_011 ++ ridgeSupport386_suffix_012
def ridgeSupport386_suffix_010 : List Nat := ridgeSupport386_010 ++ ridgeSupport386_suffix_011
def ridgeSupport386_suffix_009 : List Nat := ridgeSupport386_009 ++ ridgeSupport386_suffix_010
def ridgeSupport386_suffix_008 : List Nat := ridgeSupport386_008 ++ ridgeSupport386_suffix_009
def ridgeSupport386_suffix_007 : List Nat := ridgeSupport386_007 ++ ridgeSupport386_suffix_008
def ridgeSupport386_suffix_006 : List Nat := ridgeSupport386_006 ++ ridgeSupport386_suffix_007
def ridgeSupport386_suffix_005 : List Nat := ridgeSupport386_005 ++ ridgeSupport386_suffix_006
def ridgeSupport386_suffix_004 : List Nat := ridgeSupport386_004 ++ ridgeSupport386_suffix_005
def ridgeSupport386_suffix_003 : List Nat := ridgeSupport386_003 ++ ridgeSupport386_suffix_004
def ridgeSupport386_suffix_002 : List Nat := ridgeSupport386_002 ++ ridgeSupport386_suffix_003
def ridgeSupport386_suffix_001 : List Nat := ridgeSupport386_001 ++ ridgeSupport386_suffix_002
def ridgeSupport386_suffix_000 : List Nat := ridgeSupport386_000 ++ ridgeSupport386_suffix_001
theorem ridgeSupport386_source : candidateSupports 386 =
    (PackedRawNatGrowth.readList 14 402 ridgeSupport386_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
