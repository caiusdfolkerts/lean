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
def ridgeSupport452_000 : List Nat := [439,440,441,704,705,706,1128,1129,1130,1284,1285,1286,1368,1369,1370,1462,1463,1464,2108,2109,2114,2115,2120,2121,2128,2130,2134,2136,2140,2142,2156,2157]
def ridgeSupport452_001 : List Nat := [2162,2163,2168,2169,2248,2250,2254,2256,2260,2262,2296,2298,2302,2304,2308,2310,2348,2349,2354,2355,2360,2361,2368,2370,2374,2376,2380,2382,2396,2397,2402,2403]
def ridgeSupport452_002 : List Nat := [2408,2409,2488,2490,2494,2496,2500,2502,2536,2538,2542,2544,2548,2550,2626,2627,2628,2629,2630,2631,2638,2639,2640,2641,2642,2643,3640,3642,3646,3648,3652,3654]
def ridgeSupport452_003 : List Nat := [3668,3669,3674,3675,3680,3681,3716,3717,3722,3723,3728,3729,3808,3810,3814,3816,3820,3822,3850,3851,3852,3853,3854,3855,3916,3917,3918,3919,3920,3921,3946,3947]
def ridgeSupport452_004 : List Nat := [3948,3949,3950,3951,4408,4410,4414,4416,4420,4422,4436,4437,4442,4443,4448,4449,4484,4485,4490,4491,4496,4497,4576,4578,4582,4584,4588,4590,4618,4619,4620,4621]
def ridgeSupport452_005 : List Nat := [4622,4623,4684,4685,4686,4687,4688,4689,4714,4715,4716,4717,4718,4719,5464,5466,5470,5472,5476,5478,5492,5493,5498,5499,5504,5505,5540,5541,5546,5547,5552,5553]
def ridgeSupport452_006 : List Nat := [5632,5634,5638,5640,5644,5646,5674,5675,5676,5677,5678,5679,5992,5993,5994,5995,5996,5997,6004,6005,6006,6007,6008,6009,6520,6521,6522,6523,6524,6525,6532,6533]
def ridgeSupport452_007 : List Nat := [6534,6535,6536,6537,7088,7089,7094,7095,7100,7101,7124,7125,7130,7131,7136,7137,7277,7279,7283,7285,7289,7291,7373,7375,7379,7381,7385,7387,7493,7495,7499,7501]
def ridgeSupport452_008 : List Nat := [7505,7507]
def ridgeSupport452_code : Nat := 0x754dd517535d4b751dd45736dcd97355cd3733dccd71edc7971d5c7371bdc6d6f85be06f6dbda6f55bd46ef5bbc6eddbb66ec5bb06625988661d986661598465f597c65ed97a65e59785de57785ddd7765dd57745db576c5dad76a5da576858bd62e58b562c58ad62a583960c5821606580960056c55b056ad5aa56955a4560558055ed57a55d55745599564558155e556955849bd26e49b526c49ad26a4945250493d24e493524c483d20e483520c482d20a47b91ec47a11e647891e04645190462d18a46151844585160456d15a45551544519144450113e44e91383dbcf6e3db4f6c3dacf6a3d44f503d3cf4e3d34f4c3c3cf0e3c34f0c3c2cf0a3bb8eec3ba0ee63b88ee03a44e903a2ce8a3a14e843984e60396ce5a3954e543918e443900e3e38e8e38294ca522944a50293ca4e291ca462914a44290ca4227d89f427c09ee27a89e827189c427009be26e89b825a4968258c962257495c253894c2520946250894024e493824cc93224b492c241890424008fe23e88f823588d423408ce23288c821e487821cc87221b486c217885c216085621488502124848210c84220f483c16e05b716d855a15645581418505141046a11a44680b082c10b001b906e01b7
def ridgeSupport452_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport452_code
def ridgeSupport452_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport452_code
def ridgeSupport452_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport452_code
def ridgeSupport452_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport452_code
def ridgeSupport452_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport452_code
def ridgeSupport452_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport452_code
def ridgeSupport452_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport452_code
def ridgeSupport452_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport452_code
def ridgeSupport452_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport452_code
def ridgeSupport452_rest_009 : Nat := PackedRawNatGrowth.drop 3612 ridgeSupport452_code
def ridgeSupport452_suffix_009 : List Nat := []
def ridgeSupport452_suffix_008 : List Nat := ridgeSupport452_008 ++ ridgeSupport452_suffix_009
def ridgeSupport452_suffix_007 : List Nat := ridgeSupport452_007 ++ ridgeSupport452_suffix_008
def ridgeSupport452_suffix_006 : List Nat := ridgeSupport452_006 ++ ridgeSupport452_suffix_007
def ridgeSupport452_suffix_005 : List Nat := ridgeSupport452_005 ++ ridgeSupport452_suffix_006
def ridgeSupport452_suffix_004 : List Nat := ridgeSupport452_004 ++ ridgeSupport452_suffix_005
def ridgeSupport452_suffix_003 : List Nat := ridgeSupport452_003 ++ ridgeSupport452_suffix_004
def ridgeSupport452_suffix_002 : List Nat := ridgeSupport452_002 ++ ridgeSupport452_suffix_003
def ridgeSupport452_suffix_001 : List Nat := ridgeSupport452_001 ++ ridgeSupport452_suffix_002
def ridgeSupport452_suffix_000 : List Nat := ridgeSupport452_000 ++ ridgeSupport452_suffix_001
theorem ridgeSupport452_source : candidateSupports 452 =
    (PackedRawNatGrowth.readList 14 258 ridgeSupport452_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
