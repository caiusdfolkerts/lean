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
def ridgeSupport900_000 : List Nat := [502,503,504,767,768,769,1191,1192,1193,1347,1348,1349,1431,1432,1433,1453,1454,1455,2110,2111,2116,2117,2122,2123,2137,2139,2143,2145,2149,2151,2158,2159]
def ridgeSupport900_001 : List Nat := [2164,2165,2170,2171,2257,2259,2263,2265,2269,2271,2305,2307,2311,2313,2317,2319,2350,2351,2356,2357,2362,2363,2377,2379,2383,2385,2389,2391,2398,2399,2404,2405]
def ridgeSupport900_002 : List Nat := [2410,2411,2497,2499,2503,2505,2509,2511,2545,2547,2551,2553,2557,2559,2842,2843,2844,2845,2846,2847,2854,2855,2856,2857,2858,2859,3649,3651,3655,3657,3661,3663]
def ridgeSupport900_003 : List Nat := [3670,3671,3676,3677,3682,3683,3718,3719,3724,3725,3730,3731,3817,3819,3823,3825,3829,3831,3832,3833,3834,3835,3836,3837,4132,4133,4134,4135,4136,4137,4162,4163]
def ridgeSupport900_004 : List Nat := [4164,4165,4166,4167,4417,4419,4423,4425,4429,4431,4438,4439,4444,4445,4450,4451,4486,4487,4492,4493,4498,4499,4585,4587,4591,4593,4597,4599,4600,4601,4602,4603]
def ridgeSupport900_005 : List Nat := [4604,4605,4900,4901,4902,4903,4904,4905,4930,4931,4932,4933,4934,4935,5473,5475,5479,5481,5485,5487,5494,5495,5500,5501,5506,5507,5542,5543,5548,5549,5554,5555]
def ridgeSupport900_006 : List Nat := [5641,5643,5647,5649,5653,5655,5656,5657,5658,5659,5660,5661,6208,6209,6210,6211,6212,6213,6220,6221,6222,6223,6224,6225,6736,6737,6738,6739,6740,6741,6748,6749]
def ridgeSupport900_007 : List Nat := [6750,6751,6752,6753,7090,7091,7096,7097,7102,7103,7126,7127,7132,7133,7138,7139,7284,7286,7290,7292,7296,7298,7380,7382,7386,7388,7392,7394,7500,7502,7506,7508]
def ridgeSupport900_008 : List Nat := [7512,7514]
cert_ridgeSupport_code_3 900
cert_ridgeSupport_rest_2 900 000 0
cert_ridgeSupport_rest_2 900 001 448
cert_ridgeSupport_rest_2 900 002 896
cert_ridgeSupport_rest_2 900 003 1344
cert_ridgeSupport_rest_2 900 004 1792
cert_ridgeSupport_rest_2 900 005 2240
cert_ridgeSupport_rest_2 900 006 2688
cert_ridgeSupport_rest_2 900 007 3136
cert_ridgeSupport_rest_2 900 008 3584
cert_ridgeSupport_rest_2 900 009 3612
cert_ridgeSupport_suffix_4 900 009
cert_ridgeSupport_suffix_3 900 008 009
cert_ridgeSupport_suffix_3 900 007 008
cert_ridgeSupport_suffix_3 900 006 007
cert_ridgeSupport_suffix_3 900 005 006
cert_ridgeSupport_suffix_3 900 004 005
cert_ridgeSupport_suffix_3 900 003 004
cert_ridgeSupport_suffix_3 900 002 003
cert_ridgeSupport_suffix_3 900 001 002
cert_ridgeSupport_suffix_3 900 000 001
cert_ridgeSupport_source_3 900 14 258
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
