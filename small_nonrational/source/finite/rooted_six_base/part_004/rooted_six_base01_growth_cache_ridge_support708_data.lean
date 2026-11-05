module
prelude
public import RootedSixBase01GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport708_000 : List Nat := [446,447,448,711,712,713,1067,1068,1069,1223,1224,1225,1307,1308,1309,1377,1378,1379,1902,1903,1904,1905,1906,1907,1998,1999,2000,2001,2002,2003,2094,2095]
def ridgeSupport708_001 : List Nat := [2096,2097,2098,2099,2166,2167,2168,2169,2170,2171,2262,2263,2264,2265,2266,2267,2358,2359,2360,2361,2362,2363,2532,2533,2534,2535,2536,2537,2544,2545,2546,2547]
def ridgeSupport708_002 : List Nat := [2548,2549,3846,3847,3848,3849,3850,3851,3894,3895,3896,3897,3898,3899,4038,4039,4040,4041,4042,4043,4182,4183,4184,4185,4186,4187,4212,4213,4214,4215,4216,4217]
def ridgeSupport708_003 : List Nat := [4806,4807,4808,4809,4810,4811,4854,4855,4856,4857,4858,4859,4998,4999,5000,5001,5002,5003,5142,5143,5144,5145,5146,5147,5172,5173,5174,5175,5176,5177,5502,5503]
def ridgeSupport708_004 : List Nat := [5504,5505,5506,5507,5550,5551,5552,5553,5554,5555,5694,5695,5696,5697,5698,5699,6114,6115,6116,6117,6118,6119,6126,6127,6128,6129,6130,6131,6810,6811,6812,6813]
def ridgeSupport708_005 : List Nat := [6814,6815,6822,6823,6824,6825,6826,6827,7412,7413,7418,7419,7432,7433,7435,7438,7441,7444,7452,7454,7460,7461,7466,7467,7480,7481,7555,7558,7561,7564,7572,7574]
def ridgeSupport708_006 : List Nat := [7603,7606,7609,7612,7620,7622,7652,7653,7658,7659,7672,7673,7675,7678,7681,7684,7692,7694,7700,7701,7706,7707,7720,7721,7795,7798,7801,7804,7812,7814,7843,7846]
def ridgeSupport708_007 : List Nat := [7849,7852,7860,7862,8004,8005,8006,8007,8008,8009,8016,8017,8018,8019,8020,8021,8947,8950,8953,8956,8964,8966,8972,8973,8978,8979,8992,8993,9020,9021,9026,9027]
def ridgeSupport708_008 : List Nat := [9040,9041,9115,9118,9121,9124,9132,9134,9150,9151,9152,9153,9154,9155,9294,9295,9296,9297,9298,9299,9324,9325,9326,9327,9328,9329,9715,9718,9721,9724,9732,9734]
def ridgeSupport708_009 : List Nat := [9740,9741,9746,9747,9760,9761,9788,9789,9794,9795,9808,9809,9883,9886,9889,9892,9900,9902,9918,9919,9920,9921,9922,9923,10062,10063,10064,10065,10066,10067,10092,10093]
def ridgeSupport708_010 : List Nat := [10094,10095,10096,10097,10243,10246,10249,10252,10260,10262,10268,10269,10274,10275,10288,10289,10316,10317,10322,10323,10336,10337,10411,10414,10417,10420,10428,10430,10446,10447,10448,10449]
def ridgeSupport708_011 : List Nat := [10450,10451,10842,10843,10844,10845,10846,10847,10854,10855,10856,10857,10858,10859,11370,11371,11372,11373,11374,11375,11382,11383,11384,11385,11386,11387,11779,11782,11786,11839,11842,11845]
def ridgeSupport708_012 : List Nat := [11848,11856,11858,11911,11914,11918,11971,11974,11977,11980,11988,11990,12126,12127,12128,12129,12130,12131,12727,12730,12734,12823,12826,12829,12832,12840,12842,12948,12949,12950,12951,12952]
def ridgeSupport708_013 : List Nat := [12953,13207,13210,13214,13303,13306,13309,13312,13320,13322,13428,13429,13430,13431,13432,13433,13555,13558,13562,13651,13654,13657,13660,13668,13670,13920,13921,13922,13923,13924,13925,14268]
def ridgeSupport708_014 : List Nat := [14269,14270,14271,14272,14273,14720,14721,14726,14727,14740,14741,14756,14757,14762,14763,14776,14777,14910,14915,14916,14921,14929,14931,15006,15011,15012,15017,15025,15027,15066,15071,15072]
def ridgeSupport708_015 : List Nat := [15077,15085,15087]
def ridgeSupport708_code : Nat := 0x3aefebb7ae5eb83adfeb6bab3eac7aa9ea93aa3ea7ba53e947a49e913a43e8fb9b9e6e39abe6ab9a5e693995e653987e61b981e6037c1df037bfdefb7bddef3665d993663d98b661d983566d59355cd567556d54f4fad3db4f3d1e7478d1df476d1d7474d02b408d0033fdcfeb3f7ce7b39ace5f299ca63297ca5b295ca5322ac8a3220c87721ac85f1bec6eb1b7bd8ef62bd86f60bd7ef5ebb5aed4bb32ec9bb1aec3ba3ae8aba1ee52b942e48b916e42b8fee0ab81ae03b1eec7ab1e6c78b1dec76b1bec6eb1b6c6cb1aec6aa9aea6aa9a6a68a99ea66a97ea5ea976a5ca96ea5aa34e8d2a3468d0a33e8cea2fa8bca2d28b1a2ba8aba186860a14e852a13684ca0c6830a08e822a07681ca05a814a032809a01a8039dc67709dbe76e9db676c9d4e7529d467509d3e74e9b0e6c29b066c09afe6be9aba6ac9a926a19a7a69b9946650990e64298f663c9886620984e612983660c981a60497f25f997da5f391c647091be46e91b646c914e4529146450913e44e8f0e3c28f063c08efe3be8eba3ac8e923a18e7a39b8d463508d0e3428cf633c8c863208c4e3128c3630c8c1a3048bf22f98bda2f37d55f547d4df527d45f507d25f487d1df467d15f447ad9eb47ab1ea97a99ea37a19e8479f1e7979d9e7378a5e28786de1a7855e147839e0c7811e0177f9dfb77e5df877addea7795de47719dc476f1db976d9db37659d947631d897619d8374e5d3874add2a7495d247479d1c7451d117439d0b7425d0873edcfa73d5cf46aadaaa6aa5aa86a9daa66a7da9e6a75a9c6a6da9a5fcd7f25fc57f05fbd7ee5f9d7e65f957e45f8d7e2590d642590564058fd63e56cd5b256c55b056bd5ae560d582560558055fd57e50e543850dd43650d5434506d41a5065418505d4164e2d38a4e253884e1d3864bed2fa4be52f84bdd2f64b2d2ca4b252c84b1d2c641e507841dd07641d5074416d05a4165058415d0563f2cfca3f24fc83f1cfc63cecf3a3ce4f383cdcf363c2cf0a3c24f083c1cf0627d49f427cc9f227c49f027a49e8279c9e627949e424ec93a24e493824dc936236c8da23648d8235c8d621ec87a21e487821dc87620cc83220c483020bc82e1f4c7d21f447d01f3c7ce1dcc7721dc47701dbc76e158c562158451d147051b13244c8131c42d10b042b0b242c80b1c1c006fc1be
def ridgeSupport708_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport708_code
def ridgeSupport708_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport708_code
def ridgeSupport708_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport708_code
def ridgeSupport708_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport708_code
def ridgeSupport708_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport708_code
def ridgeSupport708_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport708_code
def ridgeSupport708_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport708_code
def ridgeSupport708_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport708_code
def ridgeSupport708_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport708_code
def ridgeSupport708_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport708_code
def ridgeSupport708_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport708_code
def ridgeSupport708_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport708_code
def ridgeSupport708_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport708_code
def ridgeSupport708_rest_013 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport708_code
def ridgeSupport708_rest_014 : Nat := PackedRawNatGrowth.drop 6272 ridgeSupport708_code
def ridgeSupport708_rest_015 : Nat := PackedRawNatGrowth.drop 6720 ridgeSupport708_code
def ridgeSupport708_rest_016 : Nat := PackedRawNatGrowth.drop 6762 ridgeSupport708_code
def ridgeSupport708_suffix_016 : List Nat := []
def ridgeSupport708_suffix_015 : List Nat := ridgeSupport708_015 ++ ridgeSupport708_suffix_016
def ridgeSupport708_suffix_014 : List Nat := ridgeSupport708_014 ++ ridgeSupport708_suffix_015
def ridgeSupport708_suffix_013 : List Nat := ridgeSupport708_013 ++ ridgeSupport708_suffix_014
def ridgeSupport708_suffix_012 : List Nat := ridgeSupport708_012 ++ ridgeSupport708_suffix_013
def ridgeSupport708_suffix_011 : List Nat := ridgeSupport708_011 ++ ridgeSupport708_suffix_012
def ridgeSupport708_suffix_010 : List Nat := ridgeSupport708_010 ++ ridgeSupport708_suffix_011
def ridgeSupport708_suffix_009 : List Nat := ridgeSupport708_009 ++ ridgeSupport708_suffix_010
def ridgeSupport708_suffix_008 : List Nat := ridgeSupport708_008 ++ ridgeSupport708_suffix_009
def ridgeSupport708_suffix_007 : List Nat := ridgeSupport708_007 ++ ridgeSupport708_suffix_008
def ridgeSupport708_suffix_006 : List Nat := ridgeSupport708_006 ++ ridgeSupport708_suffix_007
def ridgeSupport708_suffix_005 : List Nat := ridgeSupport708_005 ++ ridgeSupport708_suffix_006
def ridgeSupport708_suffix_004 : List Nat := ridgeSupport708_004 ++ ridgeSupport708_suffix_005
def ridgeSupport708_suffix_003 : List Nat := ridgeSupport708_003 ++ ridgeSupport708_suffix_004
def ridgeSupport708_suffix_002 : List Nat := ridgeSupport708_002 ++ ridgeSupport708_suffix_003
def ridgeSupport708_suffix_001 : List Nat := ridgeSupport708_001 ++ ridgeSupport708_suffix_002
def ridgeSupport708_suffix_000 : List Nat := ridgeSupport708_000 ++ ridgeSupport708_suffix_001
theorem ridgeSupport708_source : candidateRows 708 =
    (PackedRawNatGrowth.readList 14 483 ridgeSupport708_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
