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
def ridgeSupport836_000 : List Nat := [481,482,483,746,747,748,1170,1171,1172,1326,1327,1328,1410,1411,1412,1456,1457,1458,2104,2105,2118,2119,2124,2125,2131,2133,2141,2144,2147,2150,2152,2153]
def ridgeSupport836_001 : List Nat := [2166,2167,2172,2173,2251,2253,2261,2264,2267,2270,2299,2301,2309,2312,2315,2318,2344,2345,2358,2359,2364,2365,2371,2373,2381,2384,2387,2390,2392,2393,2406,2407]
def ridgeSupport836_002 : List Nat := [2412,2413,2491,2493,2501,2504,2507,2510,2539,2541,2549,2552,2555,2558,2770,2771,2772,2773,2774,2775,2782,2783,2784,2785,2786,2787,3643,3645,3653,3656,3659,3662]
def ridgeSupport836_003 : List Nat := [3664,3665,3678,3679,3684,3685,3712,3713,3726,3727,3732,3733,3811,3813,3821,3824,3827,3830,3838,3839,3840,3841,3842,3843,4060,4061,4062,4063,4064,4065,4090,4091]
def ridgeSupport836_004 : List Nat := [4092,4093,4094,4095,4411,4413,4421,4424,4427,4430,4432,4433,4446,4447,4452,4453,4480,4481,4494,4495,4500,4501,4579,4581,4589,4592,4595,4598,4606,4607,4608,4609]
def ridgeSupport836_005 : List Nat := [4610,4611,4828,4829,4830,4831,4832,4833,4858,4859,4860,4861,4862,4863,5467,5469,5477,5480,5483,5486,5488,5489,5502,5503,5508,5509,5536,5537,5550,5551,5556,5557]
def ridgeSupport836_006 : List Nat := [5635,5637,5645,5648,5651,5654,5662,5663,5664,5665,5666,5667,6136,6137,6138,6139,6140,6141,6148,6149,6150,6151,6152,6153,6664,6665,6666,6667,6668,6669,6676,6677]
def ridgeSupport836_007 : List Nat := [6678,6679,6680,6681,7084,7085,7098,7099,7104,7105,7120,7121,7134,7135,7140,7141,7278,7280,7288,7293,7294,7299,7374,7376,7384,7389,7390,7395,7494,7496,7504,7509]
def ridgeSupport836_008 : List Nat := [7510,7515]
def ridgeSupport836_code : Nat := 0x756dd567555d507521d46738dcde7375cd87341cce720dc7e71f5c7871c1c6e6f95be46f7dbde6f45bd06f05bc06eedbba6eb5bac6865a18685da166855a146835a0c682da0a6825a086025808601d80660158045ff57fc5fed7fa5fe57f8588d6225885620587d61e5859613584160d581560356d55b456bd5ae56855a0561558455fd57e55c557055b956b55a1565557555b4bfd2fe4bf52fc4bed2fa4b852e04b7d2de4b752dc480d202480520047fd1fe47d91f347c11ed47951e34655194463d18e46051804595164457d15e4545150453914b452114544f513b3ffcffe3ff4ffc3fecffa3f84fe03f7cfde3f74fdc3c0cf023c04f003bfcefe3bd8ef33bc0eed3b94ee33a54e943a3ce8e3a04e803994e64397ce5e3944e503938e4b3920e4538f4e3b2b8cae22b84ae02b7cade2b5cad62b54ad42b4cad227f89fb27e09f527b49eb27389cb27209c526f49bb25b496c259c96625649582558953254094d251494324f493c24dc93624a4928243890b242090523f48fb23788db23608d523348cb21f487c21dc87621a48682198863218085d2154853213484c211c84620e483816c85b116c0584160c58214c052f14b8494124c4920bb02eb0ba81e307881e1
def ridgeSupport836_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport836_code
def ridgeSupport836_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport836_code
def ridgeSupport836_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport836_code
def ridgeSupport836_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport836_code
def ridgeSupport836_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport836_code
def ridgeSupport836_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport836_code
def ridgeSupport836_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport836_code
def ridgeSupport836_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport836_code
def ridgeSupport836_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport836_code
def ridgeSupport836_rest_009 : Nat := PackedRawNatGrowth.drop 3612 ridgeSupport836_code
def ridgeSupport836_suffix_009 : List Nat := []
def ridgeSupport836_suffix_008 : List Nat := ridgeSupport836_008 ++ ridgeSupport836_suffix_009
def ridgeSupport836_suffix_007 : List Nat := ridgeSupport836_007 ++ ridgeSupport836_suffix_008
def ridgeSupport836_suffix_006 : List Nat := ridgeSupport836_006 ++ ridgeSupport836_suffix_007
def ridgeSupport836_suffix_005 : List Nat := ridgeSupport836_005 ++ ridgeSupport836_suffix_006
def ridgeSupport836_suffix_004 : List Nat := ridgeSupport836_004 ++ ridgeSupport836_suffix_005
def ridgeSupport836_suffix_003 : List Nat := ridgeSupport836_003 ++ ridgeSupport836_suffix_004
def ridgeSupport836_suffix_002 : List Nat := ridgeSupport836_002 ++ ridgeSupport836_suffix_003
def ridgeSupport836_suffix_001 : List Nat := ridgeSupport836_001 ++ ridgeSupport836_suffix_002
def ridgeSupport836_suffix_000 : List Nat := ridgeSupport836_000 ++ ridgeSupport836_suffix_001
theorem ridgeSupport836_source : candidateSupports 836 =
    (PackedRawNatGrowth.readList 14 258 ridgeSupport836_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
