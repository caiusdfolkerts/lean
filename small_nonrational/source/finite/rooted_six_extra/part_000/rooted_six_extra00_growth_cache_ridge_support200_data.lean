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
def ridgeSupport200_000 : List Nat := [25,49,69,99,105,111,112,202,203,204,205,212,213,358,359,360,361,368,369,514,515,519,521,522,526,528,529,531,535,536,540,542]
def ridgeSupport200_001 : List Nat := [543,547,549,550,552,779,780,783,784,787,788,851,852,856,858,859,863,865,866,868,872,873,877,879,880,884,886,887,889,1044,1045,1048]
def ridgeSupport200_002 : List Nat := [1049,1052,1053,1116,1117,1121,1123,1124,1128,1130,1131,1133,1137,1138,1142,1144,1145,1149,1151,1152,1154,1467,1468,1469,1470,1471,1472,1539,1540,1541,1544,1545]
def ridgeSupport200_003 : List Nat := [1546,1548,1553,1555,1560,1561,1562,1565,1566,1567,1569,1574,1576,1623,1624,1625,1628,1629,1630,1632,1637,1639,1644,1645,1646,1649,1650,1651,1653,1658,1660,1707]
def ridgeSupport200_004 : List Nat := [1708,1710,1711,1712,1713,1715,1716,1718,1719,1721,1722,2885,2887,2891,2893,2944,2945,2950,2951,2971,2973,2977,2979,2984,2985,2990,2991,2992,2993,2998,2999,3040]
def ridgeSupport200_005 : List Nat := [3041,3046,3047,3053,3055,3059,3061,3080,3081,3086,3087,3104,3105,3110,3111,3125,3127,3131,3133,3184,3185,3190,3191,3211,3213,3217,3219,3224,3225,3230,3231,3232]
def ridgeSupport200_006 : List Nat := [3233,3238,3239,3280,3281,3286,3287,3293,3295,3299,3301,3320,3321,3326,3327,3344,3345,3350,3351,3359,3361,3371,3373,3392,3393,3404,3405,3431,3433,3443,3445,3464]
def ridgeSupport200_007 : List Nat := [3465,3476,3477,3653,3655,3659,3661,3712,3713,3718,3719,3739,3741,3745,3747,3752,3753,3758,3759,3760,3761,3766,3767,3808,3809,3814,3815,3821,3823,3827,3829,3848]
def ridgeSupport200_008 : List Nat := [3849,3854,3855,3872,3873,3878,3879,3887,3889,3899,3901,3920,3921,3932,3933,3959,3961,3971,3973,3992,3993,4004,4005,4973,4975,4979,4981,4984,4985,4990,4991,5032]
def ridgeSupport200_009 : List Nat := [5033,5038,5039,5059,5061,5065,5067,5072,5073,5078,5079,5080,5081,5086,5087,5093,5095,5099,5101,5128,5129,5134,5135,5152,5153,5158,5159,5177,5179,5207,5209,5222]
def ridgeSupport200_010 : List Nat := [5223,5240,5241,5249,5251,5279,5281,5294,5295,5312,5313,5741,5743,5747,5749,5752,5753,5758,5759,5800,5801,5806,5807,5827,5829,5833,5835,5840,5841,5846,5847,5848]
def ridgeSupport200_011 : List Nat := [5849,5854,5855,5861,5863,5867,5869,5896,5897,5902,5903,5920,5921,5926,5927,5945,5947,5975,5977,5990,5991,6008,6009,6017,6019,6047,6049,6062,6063,6080,6081,6773]
def ridgeSupport200_012 : List Nat := [6775,6785,6787,6818,6819,6830,6831,6845,6847,6857,6859,6890,6891,6902,6903,7214,7215,7250,7251,7310,7311,7456,7457,7552,7553,7888,7889,7894,7895,7912,7913,7918]
def ridgeSupport200_013 : List Nat := [7919,7922,7923,7936,7937,7942,7943,7960,7961,7966,7967,7970,7971,7984,7986,7988,7989,8002,8004,8006,8007,8056,8057,8062,8063,8080,8081,8086,8087,8090,8091,8104]
def ridgeSupport200_014 : List Nat := [8106,8108,8109,8122,8124,8126,8127,8347,8349,8353,8355,8380,8381,8386,8387,8390,8391,8398,8400,8402,8403,8416,8418,8420,8421,8515,8517,8521,8523,8548,8549,8554]
def ridgeSupport200_015 : List Nat := [8555,8558,8559,8566,8568,8570,8571,8584,8586,8588,8589,8764,8766,8768,8769,8782,8784,8786,8787]
def ridgeSupport200_code : Nat := 0x2253894a250893a241890223e88f218d863218a862217b85ea17885da16f85ba16b85aa165859214b8526145850e0e583920e283820d3834a0d0833a0c7831a0c3830a0bd82f20a3828609d826dfbf7ef9fbc7ee9fad7eb1faa7ea1f9b7e69f977e59f917e41f7f7df9f797de1f477d19f447d09f357cd1f327cc1f237c89f1f7c79f197c61f077c19f017c01ef37bc9eef7bb9ee97ba1ed77b59ed17b41d817601d217481c8f7239c537149c2f70b9af76bd9aeb6ba9acb6b25abf6af5aaf6ab9aa36a89a836a05a7769d57c15f017af5eb97a15e7d7835e057795de17675d997595d5d73b5ce57275c997215c8170f5c397095c216ed5bad6e75b956df5b796d95b616d75b596d15b416cb5b256c55b0d6af5ab96a95aa167f59f967959e167559cd66f59b54c153014af52b94a1527d483520547951e14675199459515d43b50e54275099421508140f503940950213ed4fad3e74f953df4f793d94f613d74f593d14f413cb4f253c54f0d3af4eb93a94ea137f4df93794de13754dcd36f4db4fa53e90f993e60f853e0cf793ddcf5d3d70f513d40f3d3cecf313cbcf273c98f213c80f0f3c38f093c20ef53bcceef3bb4ee73b98ee13b80eb73ad8eb13ac0eaf3ab8ea93aa0ea33a84e9d3a6ce873a18e813a00e4d392ce473914d953650d893620d7535ccd69359cd4d3530d413500d2d34acd21347cd173458d113440cff33f8cf933e0ce5338ccdf3374cd73358cd13340ca73298ca13280c9f3278c993260c933244c8d322cc7731d8c7131c0c3d30ecc3730d4c273098c213080c0f3038c093020bf52fccbef2fb4be72f98be12f80bb72ed8bb12ec0baf2eb8ba92ea0ba32e84b9d2e6cb872e18b812e00b4d2d2cb472d146ba1ae46b71ad86b41acc6b11ac06af1ab86ac1aac67c19e867519cc67219c466e19b466c199c665198065e197465c1964658195c6281898621187c61e187461a1864618184c611183060a18246081814604180c5c016fc5be16f45bc16ec482120047f11f447911e047611c847111b446b11a84681190463118445d117041d1070419106041510503790ddc3760dd03700dbc36d0da43680d903620d8435f0d6c35a0d603540d4c3140c4c3100c3c30c0c2c2280898225088c21f087821c0860217084c211084020e0828209081c203080817105c016905a016705980d503500cd03300cb032807001bc069018c04500c4019
def ridgeSupport200_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport200_code
def ridgeSupport200_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport200_code
def ridgeSupport200_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport200_code
def ridgeSupport200_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport200_code
def ridgeSupport200_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport200_code
def ridgeSupport200_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport200_code
def ridgeSupport200_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport200_code
def ridgeSupport200_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport200_code
def ridgeSupport200_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport200_code
def ridgeSupport200_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport200_code
def ridgeSupport200_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport200_code
def ridgeSupport200_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport200_code
def ridgeSupport200_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport200_code
def ridgeSupport200_rest_013 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport200_code
def ridgeSupport200_rest_014 : Nat := PackedRawNatGrowth.drop 6272 ridgeSupport200_code
def ridgeSupport200_rest_015 : Nat := PackedRawNatGrowth.drop 6720 ridgeSupport200_code
def ridgeSupport200_rest_016 : Nat := PackedRawNatGrowth.drop 6986 ridgeSupport200_code
def ridgeSupport200_suffix_016 : List Nat := []
def ridgeSupport200_suffix_015 : List Nat := ridgeSupport200_015 ++ ridgeSupport200_suffix_016
def ridgeSupport200_suffix_014 : List Nat := ridgeSupport200_014 ++ ridgeSupport200_suffix_015
def ridgeSupport200_suffix_013 : List Nat := ridgeSupport200_013 ++ ridgeSupport200_suffix_014
def ridgeSupport200_suffix_012 : List Nat := ridgeSupport200_012 ++ ridgeSupport200_suffix_013
def ridgeSupport200_suffix_011 : List Nat := ridgeSupport200_011 ++ ridgeSupport200_suffix_012
def ridgeSupport200_suffix_010 : List Nat := ridgeSupport200_010 ++ ridgeSupport200_suffix_011
def ridgeSupport200_suffix_009 : List Nat := ridgeSupport200_009 ++ ridgeSupport200_suffix_010
def ridgeSupport200_suffix_008 : List Nat := ridgeSupport200_008 ++ ridgeSupport200_suffix_009
def ridgeSupport200_suffix_007 : List Nat := ridgeSupport200_007 ++ ridgeSupport200_suffix_008
def ridgeSupport200_suffix_006 : List Nat := ridgeSupport200_006 ++ ridgeSupport200_suffix_007
def ridgeSupport200_suffix_005 : List Nat := ridgeSupport200_005 ++ ridgeSupport200_suffix_006
def ridgeSupport200_suffix_004 : List Nat := ridgeSupport200_004 ++ ridgeSupport200_suffix_005
def ridgeSupport200_suffix_003 : List Nat := ridgeSupport200_003 ++ ridgeSupport200_suffix_004
def ridgeSupport200_suffix_002 : List Nat := ridgeSupport200_002 ++ ridgeSupport200_suffix_003
def ridgeSupport200_suffix_001 : List Nat := ridgeSupport200_001 ++ ridgeSupport200_suffix_002
def ridgeSupport200_suffix_000 : List Nat := ridgeSupport200_000 ++ ridgeSupport200_suffix_001
theorem ridgeSupport200_source : candidateSupports 200 =
    (PackedRawNatGrowth.readList 14 499 ridgeSupport200_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
