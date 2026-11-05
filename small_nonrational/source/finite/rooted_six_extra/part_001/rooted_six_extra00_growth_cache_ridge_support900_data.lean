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
def ridgeSupport900_000 : List Nat := [502,503,504,767,768,769,1191,1192,1193,1347,1348,1349,1431,1432,1433,1453,1454,1455,2110,2111,2116,2117,2122,2123,2137,2139,2143,2145,2149,2151,2158,2159]
def ridgeSupport900_001 : List Nat := [2164,2165,2170,2171,2257,2259,2263,2265,2269,2271,2305,2307,2311,2313,2317,2319,2350,2351,2356,2357,2362,2363,2377,2379,2383,2385,2389,2391,2398,2399,2404,2405]
def ridgeSupport900_002 : List Nat := [2410,2411,2497,2499,2503,2505,2509,2511,2545,2547,2551,2553,2557,2559,2842,2843,2844,2845,2846,2847,2854,2855,2856,2857,2858,2859,3649,3651,3655,3657,3661,3663]
def ridgeSupport900_003 : List Nat := [3670,3671,3676,3677,3682,3683,3718,3719,3724,3725,3730,3731,3817,3819,3823,3825,3829,3831,3832,3833,3834,3835,3836,3837,4132,4133,4134,4135,4136,4137,4162,4163]
def ridgeSupport900_004 : List Nat := [4164,4165,4166,4167,4417,4419,4423,4425,4429,4431,4438,4439,4444,4445,4450,4451,4486,4487,4492,4493,4498,4499,4585,4587,4591,4593,4597,4599,4600,4601,4602,4603]
def ridgeSupport900_005 : List Nat := [4604,4605,4900,4901,4902,4903,4904,4905,4930,4931,4932,4933,4934,4935,5473,5475,5479,5481,5485,5487,5494,5495,5500,5501,5506,5507,5542,5543,5548,5549,5554,5555]
def ridgeSupport900_006 : List Nat := [5641,5643,5647,5649,5653,5655,5656,5657,5658,5659,5660,5661,6208,6209,6210,6211,6212,6213,6220,6221,6222,6223,6224,6225,6736,6737,6738,6739,6740,6741,6748,6749]
def ridgeSupport900_007 : List Nat := [6750,6751,6752,6753,7090,7091,7096,7097,7102,7103,7126,7127,7132,7133,7138,7139,7284,7286,7290,7292,7296,7298,7380,7382,7386,7388,7392,7394,7500,7502,7506,7508]
def ridgeSupport900_008 : List Nat := [7512,7514]
def ridgeSupport900_code : Nat := 0x7569d587551d527539d4c7389ce07371cda7359cd47209c8071f1c7a71d9c746f8dbe26f75bdc6f5dbd66efdbbe6ee5bb86ecdbb26985a60697da5e6975a5c6955a54694da526945a506145850613d84e613584c6115844610d8426105840587561c586d61a5865618585d615584560f582d60956cd5b256b55ac569d5a6560d58255f557c55dd57655bd56d55a5567558d5614d1d3464d153444d0d3424ca53284c9d3264c9532447f51fc47ed1fa47e51f847dd1f547c51ef47ad1e9464d192463518c461d186458d162457515c455d156453d14d4525147450d141411d0464115044410d04240a5028409d02640950243bf4efc3becefa3be4ef83bdcef53bc4eef3bacee93a4ce923a34e8c3a1ce86398ce623974e5c395ce56393ce4d3924e47390ce412cacb2a2ca4b282c9cb262c7cb1e2c74b1c2c6cb1a27fc9fd27e49f727cc9f1273c9cd27249c7270c9c125ac96a2594964257c95e255c955254494f252c94924ec93a24d493424bc92e243c90d2424907240c901237c8dd23648d7234c8d121ec87a21d487421bc86e219c865218485f216c859212c84a211484420fc83e16bc5ae16b459916605971514544150c4a912a04a70c043000bfc1f807dc1f6
def ridgeSupport900_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport900_code
def ridgeSupport900_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport900_code
def ridgeSupport900_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport900_code
def ridgeSupport900_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport900_code
def ridgeSupport900_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport900_code
def ridgeSupport900_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport900_code
def ridgeSupport900_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport900_code
def ridgeSupport900_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport900_code
def ridgeSupport900_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport900_code
def ridgeSupport900_rest_009 : Nat := PackedRawNatGrowth.drop 3612 ridgeSupport900_code
def ridgeSupport900_suffix_009 : List Nat := []
def ridgeSupport900_suffix_008 : List Nat := ridgeSupport900_008 ++ ridgeSupport900_suffix_009
def ridgeSupport900_suffix_007 : List Nat := ridgeSupport900_007 ++ ridgeSupport900_suffix_008
def ridgeSupport900_suffix_006 : List Nat := ridgeSupport900_006 ++ ridgeSupport900_suffix_007
def ridgeSupport900_suffix_005 : List Nat := ridgeSupport900_005 ++ ridgeSupport900_suffix_006
def ridgeSupport900_suffix_004 : List Nat := ridgeSupport900_004 ++ ridgeSupport900_suffix_005
def ridgeSupport900_suffix_003 : List Nat := ridgeSupport900_003 ++ ridgeSupport900_suffix_004
def ridgeSupport900_suffix_002 : List Nat := ridgeSupport900_002 ++ ridgeSupport900_suffix_003
def ridgeSupport900_suffix_001 : List Nat := ridgeSupport900_001 ++ ridgeSupport900_suffix_002
def ridgeSupport900_suffix_000 : List Nat := ridgeSupport900_000 ++ ridgeSupport900_suffix_001
theorem ridgeSupport900_source : candidateSupports 900 =
    (PackedRawNatGrowth.readList 14 258 ridgeSupport900_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
