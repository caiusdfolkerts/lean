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
def ridgeSupport450_000 : List Nat := [269,270,271,693,694,695,781,782,783,865,866,867,959,960,961,1644,1645,1646,1647,1648,1649,1740,1741,1742,1743,1744,1745,1836,1837,1838,1839,1840]
def ridgeSupport450_001 : List Nat := [1841,2196,2197,2198,2199,2200,2201,2244,2245,2246,2247,2248,2249,2388,2389,2390,2391,2392,2393,2418,2419,2420,2421,2422,2423,2448,2449,2450,2451,2452,2453,3156]
def ridgeSupport450_002 : List Nat := [3157,3158,3159,3160,3161,3204,3205,3206,3207,3208,3209,3348,3349,3350,3351,3352,3353,3378,3379,3380,3381,3382,3383,3408,3409,3410,3411,3412,3413,4548,4549,4550]
def ridgeSupport450_003 : List Nat := [4551,4552,4553,4596,4597,4598,4599,4600,4601,4740,4741,4742,4743,4744,4745,5046,5047,5048,5049,5050,5051,5058,5059,5060,5061,5062,5063,7174,7175,7180,7181,7186]
def ridgeSupport450_004 : List Nat := [7187,7194,7196,7200,7202,7206,7208,7222,7223,7228,7229,7234,7235,7314,7316,7320,7322,7326,7328,7362,7364,7368,7370,7374,7376,7650,7652,7656,7658,7662,7664,7678]
def ridgeSupport450_005 : List Nat := [7679,7684,7685,7690,7691,7726,7727,7732,7733,7738,7739,7818,7820,7824,7826,7830,7832,7860,7861,7862,7863,7864,7865,7926,7927,7928,7929,7930,7931,7956,7957,7958]
def ridgeSupport450_006 : List Nat := [7959,7960,7961,8418,8420,8424,8426,8430,8432,8446,8447,8452,8453,8458,8459,8494,8495,8500,8501,8506,8507,8586,8588,8592,8594,8598,8600,8628,8629,8630,8631,8632]
def ridgeSupport450_007 : List Nat := [8633,8694,8695,8696,8697,8698,8699,8724,8725,8726,8727,8728,8729,9474,9476,9480,9482,9486,9488,9502,9503,9508,9509,9514,9515,9550,9551,9556,9557,9562,9563,9642]
def ridgeSupport450_008 : List Nat := [9644,9648,9650,9654,9656,9684,9685,9686,9687,9688,9689,10002,10003,10004,10005,10006,10007,10014,10015,10016,10017,10018,10019,11646,11648,11652,11706,11708,11712,11714,11718,11720]
def ridgeSupport450_009 : List Nat := [11898,11900,11904,11994,11996,12000,12002,12006,12008,12066,12067,12068,12069,12070,12071,12378,12380,12384,12474,12476,12480,12482,12486,12488,12546,12547,12548,12549,12550,12551,13074,13076]
def ridgeSupport450_010 : List Nat := [13080,13170,13172,13176,13178,13182,13184,13386,13387,13388,13389,13390,13391,14686,14687,14692,14693,14698,14699,14755,14757,14761,14763,14767,14769,14851,14853,14857,14859,14863,14865,14971]
def ridgeSupport450_011 : List Nat := [14973,14977,14979,14983,14985]
def ridgeSupport450_code : Nat := 0x3a89ea1fa83ea07a7de9efa11e83fa0be827a05e80f9b1e6bf9abe6a79a5e68f96be5ab965e59395fe57b44fd13b44dd13344bd12b380cdfb37acde3374cdcb318cc53312c41f106c417104c40f102c3230c6c30b0c0c2f30bac18305cc16af27bc9af25bc92f23bc8aee8bb9aee2bb82edcbb6ae80b9f2e7ab722dc6b70adc0b6f2dbab612d80b5fa7239c8a7219c8271f9c7a7179c5a7159c527139c4a5d997625d7975a5d597525b896da5b296c25ac96aa55b956a555955254f953a52b94aa525949251f947a510943a50a9422504940a2198862217885a21588521fb87ea1f987e21f787da1b986e21b786da1b586d2198865a192864218c862a13b84ea13584d212f84ba10b842a10584120ff83fa0f083ba0ea83a20e48389f197c61f177c59f157c51efb7be9ef97be1ef77bd9eb97ae1eb77ad9eb57ad1e987a59e927a41e8c7a29e3b78e9e3578d1e2f78b9e0b7829e057811dff77f9df077b9dea77a1de47789cd07339cca7321cc47309ca07279c9a7261c947249c437109c3d70f1c3770d9c287099c227081c1c7069c137049c0d7031c0770193c74f193c54f113c34f093bb4ee93b94ee13b74ed92894a212874a192854a111f947e11f747d91f547d11c947211c747191c54710d553550d533548d513540d3734d8d3534d0d3334c8d193460d173458d153450c893220c873218c853210c593160c573158c55315099526509932648991264097725d897525d097325c89592560957255895525508c923208c723188c523108992260897225889522507311cc072f1cb872d1cb06d11b406cf1b386cd1b3067119c066f19b866d19b03c10f003bf0d8c3620d8430f0c3830d0adc2b60ad410f043810d
def ridgeSupport450_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport450_code
def ridgeSupport450_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport450_code
def ridgeSupport450_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport450_code
def ridgeSupport450_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport450_code
def ridgeSupport450_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport450_code
def ridgeSupport450_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport450_code
def ridgeSupport450_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport450_code
def ridgeSupport450_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport450_code
def ridgeSupport450_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport450_code
def ridgeSupport450_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport450_code
def ridgeSupport450_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport450_code
def ridgeSupport450_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport450_code
def ridgeSupport450_rest_012 : Nat := PackedRawNatGrowth.drop 4998 ridgeSupport450_code
def ridgeSupport450_suffix_012 : List Nat := []
def ridgeSupport450_suffix_011 : List Nat := ridgeSupport450_011 ++ ridgeSupport450_suffix_012
def ridgeSupport450_suffix_010 : List Nat := ridgeSupport450_010 ++ ridgeSupport450_suffix_011
def ridgeSupport450_suffix_009 : List Nat := ridgeSupport450_009 ++ ridgeSupport450_suffix_010
def ridgeSupport450_suffix_008 : List Nat := ridgeSupport450_008 ++ ridgeSupport450_suffix_009
def ridgeSupport450_suffix_007 : List Nat := ridgeSupport450_007 ++ ridgeSupport450_suffix_008
def ridgeSupport450_suffix_006 : List Nat := ridgeSupport450_006 ++ ridgeSupport450_suffix_007
def ridgeSupport450_suffix_005 : List Nat := ridgeSupport450_005 ++ ridgeSupport450_suffix_006
def ridgeSupport450_suffix_004 : List Nat := ridgeSupport450_004 ++ ridgeSupport450_suffix_005
def ridgeSupport450_suffix_003 : List Nat := ridgeSupport450_003 ++ ridgeSupport450_suffix_004
def ridgeSupport450_suffix_002 : List Nat := ridgeSupport450_002 ++ ridgeSupport450_suffix_003
def ridgeSupport450_suffix_001 : List Nat := ridgeSupport450_001 ++ ridgeSupport450_suffix_002
def ridgeSupport450_suffix_000 : List Nat := ridgeSupport450_000 ++ ridgeSupport450_suffix_001
theorem ridgeSupport450_source : candidateRows 450 =
    (PackedRawNatGrowth.readList 14 357 ridgeSupport450_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
