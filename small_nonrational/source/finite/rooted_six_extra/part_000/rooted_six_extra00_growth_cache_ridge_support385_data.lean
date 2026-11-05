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
def ridgeSupport385_000 : List Nat := [12,22,28,31,34,168,169,170,171,172,173,240,241,242,243,244,245,274,278,279,280,281,283,284,291,293,339,340,341,344,345,346]
def ridgeSupport385_001 : List Nat := [348,353,355,396,397,398,399,400,401,430,434,435,436,437,439,440,447,449,495,496,497,500,501,502,504,509,511,514,518,519,520,521]
def ridgeSupport385_002 : List Nat := [523,524,531,533,579,580,581,584,585,586,588,593,595,598,601,602,603,606,607,608,610,615,616,618,619,1889,1891,1908,1910,1920,1921,1926]
def ridgeSupport385_003 : List Nat := [1927,1968,1969,1974,1975,1988,1989,1991,1994,1997,2000,2002,2003,2009,2011,2016,2017,2022,2023,2028,2030,2064,2065,2070,2071,2088,2089,2094,2095,2129,2131,2148]
def ridgeSupport385_004 : List Nat := [2150,2160,2161,2166,2167,2208,2209,2214,2215,2228,2229,2231,2234,2237,2240,2242,2243,2249,2251,2256,2257,2262,2263,2268,2270,2304,2305,2310,2311,2328,2329,2334]
def ridgeSupport385_005 : List Nat := [2335,2598,2600,2610,2612,2638,2639,2650,2651,2813,2815,2825,2827,2858,2859,2870,2871,2897,2899,2916,2918,2928,2929,2934,2935,2976,2977,2982,2983,2996,2997,2999]
def ridgeSupport385_006 : List Nat := [3002,3005,3008,3010,3011,3017,3019,3024,3025,3030,3031,3036,3038,3072,3073,3078,3079,3096,3097,3102,3103,3366,3368,3378,3380,3406,3407,3418,3419,3581,3583,3593]
def ridgeSupport385_007 : List Nat := [3595,3626,3627,3638,3639,3894,3896,3906,3908,3934,3935,3946,3947,4109,4111,4121,4123,4154,4155,4166,4167,7078,7079,7114,7115,7210,7211,7679,7682,7685,7688,7708]
def ridgeSupport385_008 : List Nat := [7710,7712,7713,7716,7719,7727,7730,7733,7736,7756,7758,7760,7761,7764,7767,7828,7829,7831,7833,7882,7884,7886,7887,7895,7898,7901,7904,7924,7926,7928,7929,7932]
def ridgeSupport385_009 : List Nat := [7935,7996,7997,7999,8001,8050,8052,8054,8055,8116,8117,8119,8121,8170,8172,8174,8175]
def ridgeSupport385_code : Nat := 0x1fef7fb9fec7fa9fb97eddfb57ed1f777dd9f747dc9f417cfdf3d7cf1eff7bf1ef97be1ef67bd1ee07b75eda7b5decf7b39ecc7b29e997a5de957a51e577951e517941e4e7931e3878d5e3278bde277891e217881e1e7871e087815e0277fdc2b70a9bcb6f29ba76e99047411903b40e901b406500f4034f6b3da8f5f3d78f443d08f383cd8e3738d8e2b38a8e0b3824dff37f4d5b3568d4f3538d3434c8d283498c1f3078c193060c073018c013000bde2f70bd72f58bd12f40bcb2f24bc32f08bc02ef4bba2edcbb52ed0ba72e98ba12e80b772dd8b712dc0b662d90b532d44b372cd8b2b2ca8b0b2c24aff2bf4a5b2968a4f2938a3428c8a28289891f24789192460907241890124008de23708d723588d123408cb23248c323088c022f48ba22dc8b522d08a722988a1228087721d887121c08662190853214482f20b882920a0817205881120407ee1fb07e71f987e11f807db1f647d31f487d01f347ca1f1c7c51f107b71ed87b11ec07871e187811e007761dd07631d8426b09a8268099c262098025f097825b09682590958253094424c0928249092024509102430854213083020b0824208081c20608081ff07f41f807d81f507d01f107c01ef07041bf06e01b706d41b406cc1b206b8191064018f063818d0630163058415c0568159056015505501530494123047011b0464118045c11604480f503d00f303c80f103c00ad02b00ab02a80a902a0022007c01c005800c
def ridgeSupport385_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport385_code
def ridgeSupport385_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport385_code
def ridgeSupport385_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport385_code
def ridgeSupport385_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport385_code
def ridgeSupport385_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport385_code
def ridgeSupport385_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport385_code
def ridgeSupport385_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport385_code
def ridgeSupport385_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport385_code
def ridgeSupport385_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport385_code
def ridgeSupport385_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport385_code
def ridgeSupport385_rest_010 : Nat := PackedRawNatGrowth.drop 4270 ridgeSupport385_code
def ridgeSupport385_suffix_010 : List Nat := []
def ridgeSupport385_suffix_009 : List Nat := ridgeSupport385_009 ++ ridgeSupport385_suffix_010
def ridgeSupport385_suffix_008 : List Nat := ridgeSupport385_008 ++ ridgeSupport385_suffix_009
def ridgeSupport385_suffix_007 : List Nat := ridgeSupport385_007 ++ ridgeSupport385_suffix_008
def ridgeSupport385_suffix_006 : List Nat := ridgeSupport385_006 ++ ridgeSupport385_suffix_007
def ridgeSupport385_suffix_005 : List Nat := ridgeSupport385_005 ++ ridgeSupport385_suffix_006
def ridgeSupport385_suffix_004 : List Nat := ridgeSupport385_004 ++ ridgeSupport385_suffix_005
def ridgeSupport385_suffix_003 : List Nat := ridgeSupport385_003 ++ ridgeSupport385_suffix_004
def ridgeSupport385_suffix_002 : List Nat := ridgeSupport385_002 ++ ridgeSupport385_suffix_003
def ridgeSupport385_suffix_001 : List Nat := ridgeSupport385_001 ++ ridgeSupport385_suffix_002
def ridgeSupport385_suffix_000 : List Nat := ridgeSupport385_000 ++ ridgeSupport385_suffix_001
theorem ridgeSupport385_source : candidateSupports 385 =
    (PackedRawNatGrowth.readList 14 305 ridgeSupport385_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
