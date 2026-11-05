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
def ridgeSupport900_000 : List Nat := [488,489,490,753,754,755,1109,1110,1111,1265,1266,1267,1349,1350,1351,1371,1372,1373,1890,1891,1892,1893,1894,1895,1986,1987,1988,1989,1990,1991,2082,2083]
def ridgeSupport900_001 : List Nat := [2084,2085,2086,2087,2154,2155,2156,2157,2158,2159,2250,2251,2252,2253,2254,2255,2346,2347,2348,2349,2350,2351,2748,2749,2750,2751,2752,2753,2760,2761,2762,2763]
def ridgeSupport900_002 : List Nat := [2764,2765,3834,3835,3836,3837,3838,3839,3882,3883,3884,3885,3886,3887,4026,4027,4028,4029,4030,4031,4398,4399,4400,4401,4402,4403,4428,4429,4430,4431,4432,4433]
def ridgeSupport900_003 : List Nat := [4794,4795,4796,4797,4798,4799,4842,4843,4844,4845,4846,4847,4986,4987,4988,4989,4990,4991,5358,5359,5360,5361,5362,5363,5388,5389,5390,5391,5392,5393,5490,5491]
def ridgeSupport900_004 : List Nat := [5492,5493,5494,5495,5538,5539,5540,5541,5542,5543,5682,5683,5684,5685,5686,5687,6330,6331,6332,6333,6334,6335,6342,6343,6344,6345,6346,6347,7026,7027,7028,7029]
def ridgeSupport900_005 : List Nat := [7030,7031,7038,7039,7040,7041,7042,7043,7416,7417,7422,7423,7428,7429,7443,7445,7449,7451,7455,7457,7464,7465,7470,7471,7476,7477,7563,7565,7569,7571,7575,7577]
def ridgeSupport900_006 : List Nat := [7611,7613,7617,7619,7623,7625,7656,7657,7662,7663,7668,7669,7683,7685,7689,7691,7695,7697,7704,7705,7710,7711,7716,7717,7803,7805,7809,7811,7815,7817,7851,7853]
def ridgeSupport900_007 : List Nat := [7857,7859,7863,7865,8148,8149,8150,8151,8152,8153,8160,8161,8162,8163,8164,8165,8955,8957,8961,8963,8967,8969,8976,8977,8982,8983,8988,8989,9024,9025,9030,9031]
def ridgeSupport900_008 : List Nat := [9036,9037,9123,9125,9129,9131,9135,9137,9138,9139,9140,9141,9142,9143,9438,9439,9440,9441,9442,9443,9468,9469,9470,9471,9472,9473,9723,9725,9729,9731,9735,9737]
def ridgeSupport900_009 : List Nat := [9744,9745,9750,9751,9756,9757,9792,9793,9798,9799,9804,9805,9891,9893,9897,9899,9903,9905,9906,9907,9908,9909,9910,9911,10206,10207,10208,10209,10210,10211,10236,10237]
def ridgeSupport900_010 : List Nat := [10238,10239,10240,10241,10251,10253,10257,10259,10263,10265,10272,10273,10278,10279,10284,10285,10320,10321,10326,10327,10332,10333,10419,10421,10425,10427,10431,10433,10434,10435,10436,10437]
def ridgeSupport900_011 : List Nat := [10438,10439,10986,10987,10988,10989,10990,10991,10998,10999,11000,11001,11002,11003,11514,11515,11516,11517,11518,11519,11526,11527,11528,11529,11530,11531,11785,11787,11789,11847,11849,11853]
def ridgeSupport900_012 : List Nat := [11855,11859,11861,11917,11919,11921,11979,11981,11985,11987,11991,11993,12234,12235,12236,12237,12238,12239,12733,12735,12737,12831,12833,12837,12839,12843,12845,13056,13057,13058,13059,13060]
def ridgeSupport900_013 : List Nat := [13061,13213,13215,13217,13311,13313,13317,13319,13323,13325,13536,13537,13538,13539,13540,13541,13561,13563,13565,13659,13661,13665,13667,13671,13673,14028,14029,14030,14031,14032,14033,14376]
def ridgeSupport900_014 : List Nat := [14377,14378,14379,14380,14381,14724,14725,14730,14731,14736,14737,14760,14761,14766,14767,14772,14773,14918,14920,14924,14926,14930,14932,15014,15016,15020,15022,15026,15028,15074,15076,15080]
def ridgeSupport900_015 : List Nat := [15082,15086,15088]
def ridgeSupport900_code : Nat := 0x3af0ebbbaeaeba3ae4eb8bab4eacbaaeeab3aa8ea9ba54e94ba4ee933a48e91b9b5e6d39afe6bb9a9e6a3991e64398be62b985e61382de0b382be0ab829e0a36d1db436cfdb3b6cddb33569d59f563d58755dd56f4fdd3ef4f9d3974e4d38f4e2d3874e0d03740bd01f405d0073ffce8739fce77305cc13303cc0b301cc0322dc8af227c897221c87f1c1c6ff1bdbf3efcebf36fccbf2efcabb66ed7bb4eed1bb36ecbba46e8fba36e55b94ee4fb936e49b91ee0db82ee09b42ed0ab426d08b41ed06b3fecfeb3f6cfcb3eecfaabeeafaabe6af8abdeaf6abbeaeeabb6aecabaeaeaa31e8c6a3168c4a30e8c2a3068bfa2ee8b9a2d68b3a17685ca15e856a146850a0b682ca09e826a086820a066817a04e811a03680ba0068009ffe7fe9ff67fc9f8e7e29f867e09f7e7de9ade6b69ad66b49ace6b29ac66af9aae6a99a966a3993664c991e6469906640987661c985e61698466109826607980e60197f65fb940650093fe4fe93f64fc938e4e293864e0937e4de8ede3b68ed63b48ece3b28ec63af8eae3a98e963a38d3634c8d1e3468d063408c7631c8c5e3168c463108c263078c0e3018bf62fb7f95fe47f8dfe27f85fe07f65fd87f5dfd67f55fd47ae5eb77acdeb17ab5eab7a25e877a0de8179f5e7b7895e24787de1e7865e187845e0f782de097815e0377d5df477bddee77a5de87725dc7770ddc176f5dbb7665d97764dd917635d8b74d5d3474bdd2e74a5d287485d1f746dd197455d137415d0473fdcfe73e5cf86e0db826e05b806dfdb7e6dddb766dd5b746dcdb72632d8ca63258c8631d8c662fd8be62f58bc62ed8ba58dd63658d563458cd632569d5a656955a4568d5a255dd57655d557455cd5725445510543d50e543550c53cd4f253c54f053bd4ee4dfd37e4df537c4ded37a4bbd2ee4bb52ec4bad2ea4afd2be4af52bc4aed2ba4545150453d14e453514c44cd13244c513044bd12e3efcfbe3ef4fbc3eecfba3cbcf2e3cb4f2c3cacf2a3bfcefe3bf4efc3becefa2b34acc2b2caca2b24ac82b04ac02afcabe2af4abc24bc92e24b492c24ac92a233c8ce23348cc232c8ca21bc86e21b486c21ac86a209c8262094824208c8221f1c7c61f147c41f0c7c21d9c7661d947641d8c762157455c156c547151854513cc4f213c445711584550bcc2f20bc41ea07a41e8
def ridgeSupport900_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport900_code
def ridgeSupport900_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport900_code
def ridgeSupport900_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport900_code
def ridgeSupport900_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport900_code
def ridgeSupport900_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport900_code
def ridgeSupport900_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport900_code
def ridgeSupport900_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport900_code
def ridgeSupport900_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport900_code
def ridgeSupport900_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport900_code
def ridgeSupport900_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport900_code
def ridgeSupport900_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport900_code
def ridgeSupport900_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport900_code
def ridgeSupport900_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport900_code
def ridgeSupport900_rest_013 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport900_code
def ridgeSupport900_rest_014 : Nat := PackedRawNatGrowth.drop 6272 ridgeSupport900_code
def ridgeSupport900_rest_015 : Nat := PackedRawNatGrowth.drop 6720 ridgeSupport900_code
def ridgeSupport900_rest_016 : Nat := PackedRawNatGrowth.drop 6762 ridgeSupport900_code
def ridgeSupport900_suffix_016 : List Nat := []
def ridgeSupport900_suffix_015 : List Nat := ridgeSupport900_015 ++ ridgeSupport900_suffix_016
def ridgeSupport900_suffix_014 : List Nat := ridgeSupport900_014 ++ ridgeSupport900_suffix_015
def ridgeSupport900_suffix_013 : List Nat := ridgeSupport900_013 ++ ridgeSupport900_suffix_014
def ridgeSupport900_suffix_012 : List Nat := ridgeSupport900_012 ++ ridgeSupport900_suffix_013
def ridgeSupport900_suffix_011 : List Nat := ridgeSupport900_011 ++ ridgeSupport900_suffix_012
def ridgeSupport900_suffix_010 : List Nat := ridgeSupport900_010 ++ ridgeSupport900_suffix_011
def ridgeSupport900_suffix_009 : List Nat := ridgeSupport900_009 ++ ridgeSupport900_suffix_010
def ridgeSupport900_suffix_008 : List Nat := ridgeSupport900_008 ++ ridgeSupport900_suffix_009
def ridgeSupport900_suffix_007 : List Nat := ridgeSupport900_007 ++ ridgeSupport900_suffix_008
def ridgeSupport900_suffix_006 : List Nat := ridgeSupport900_006 ++ ridgeSupport900_suffix_007
def ridgeSupport900_suffix_005 : List Nat := ridgeSupport900_005 ++ ridgeSupport900_suffix_006
def ridgeSupport900_suffix_004 : List Nat := ridgeSupport900_004 ++ ridgeSupport900_suffix_005
def ridgeSupport900_suffix_003 : List Nat := ridgeSupport900_003 ++ ridgeSupport900_suffix_004
def ridgeSupport900_suffix_002 : List Nat := ridgeSupport900_002 ++ ridgeSupport900_suffix_003
def ridgeSupport900_suffix_001 : List Nat := ridgeSupport900_001 ++ ridgeSupport900_suffix_002
def ridgeSupport900_suffix_000 : List Nat := ridgeSupport900_000 ++ ridgeSupport900_suffix_001
theorem ridgeSupport900_source : candidateRows 900 =
    (PackedRawNatGrowth.readList 14 483 ridgeSupport900_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
