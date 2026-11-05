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
def ridgeSupport452_000 : List Nat := [425,426,427,690,691,692,1046,1047,1048,1202,1203,1204,1286,1287,1288,1380,1381,1382,1908,1909,1910,1911,1912,1913,2004,2005,2006,2007,2008,2009,2100,2101]
def ridgeSupport452_001 : List Nat := [2102,2103,2104,2105,2172,2173,2174,2175,2176,2177,2268,2269,2270,2271,2272,2273,2364,2365,2366,2367,2368,2369,2424,2425,2426,2427,2428,2429,2436,2437,2438,2439]
def ridgeSupport452_002 : List Nat := [2440,2441,3852,3853,3854,3855,3856,3857,3900,3901,3902,3903,3904,3905,4044,4045,4046,4047,4048,4049,4074,4075,4076,4077,4078,4079,4104,4105,4106,4107,4108,4109]
def ridgeSupport452_003 : List Nat := [4812,4813,4814,4815,4816,4817,4860,4861,4862,4863,4864,4865,5004,5005,5006,5007,5008,5009,5034,5035,5036,5037,5038,5039,5064,5065,5066,5067,5068,5069,5508,5509]
def ridgeSupport452_004 : List Nat := [5510,5511,5512,5513,5556,5557,5558,5559,5560,5561,5700,5701,5702,5703,5704,5705,6006,6007,6008,6009,6010,6011,6018,6019,6020,6021,6022,6023,6702,6703,6704,6705]
def ridgeSupport452_005 : List Nat := [6706,6707,6714,6715,6716,6717,6718,6719,7414,7415,7420,7421,7426,7427,7434,7436,7440,7442,7446,7448,7462,7463,7468,7469,7474,7475,7554,7556,7560,7562,7566,7568]
def ridgeSupport452_006 : List Nat := [7602,7604,7608,7610,7614,7616,7654,7655,7660,7661,7666,7667,7674,7676,7680,7682,7686,7688,7702,7703,7708,7709,7714,7715,7794,7796,7800,7802,7806,7808,7842,7844]
def ridgeSupport452_007 : List Nat := [7848,7850,7854,7856,7932,7933,7934,7935,7936,7937,7944,7945,7946,7947,7948,7949,8946,8948,8952,8954,8958,8960,8974,8975,8980,8981,8986,8987,9022,9023,9028,9029]
def ridgeSupport452_008 : List Nat := [9034,9035,9114,9116,9120,9122,9126,9128,9156,9157,9158,9159,9160,9161,9222,9223,9224,9225,9226,9227,9252,9253,9254,9255,9256,9257,9714,9716,9720,9722,9726,9728]
def ridgeSupport452_009 : List Nat := [9742,9743,9748,9749,9754,9755,9790,9791,9796,9797,9802,9803,9882,9884,9888,9890,9894,9896,9924,9925,9926,9927,9928,9929,9990,9991,9992,9993,9994,9995,10020,10021]
def ridgeSupport452_010 : List Nat := [10022,10023,10024,10025,10242,10244,10248,10250,10254,10256,10270,10271,10276,10277,10282,10283,10318,10319,10324,10325,10330,10331,10410,10412,10416,10418,10422,10424,10452,10453,10454,10455]
def ridgeSupport452_011 : List Nat := [10456,10457,10770,10771,10772,10773,10774,10775,10782,10783,10784,10785,10786,10787,11298,11299,11300,11301,11302,11303,11310,11311,11312,11313,11314,11315,11778,11780,11784,11838,11840,11844]
def ridgeSupport452_012 : List Nat := [11846,11850,11852,11910,11912,11916,11970,11972,11976,11978,11982,11984,12072,12073,12074,12075,12076,12077,12726,12728,12732,12822,12824,12828,12830,12834,12836,12894,12895,12896,12897,12898]
def ridgeSupport452_013 : List Nat := [12899,13206,13208,13212,13302,13304,13308,13310,13314,13316,13374,13375,13376,13377,13378,13379,13554,13556,13560,13650,13652,13656,13658,13662,13664,13866,13867,13868,13869,13870,13871,14214]
def ridgeSupport452_014 : List Nat := [14215,14216,14217,14218,14219,14722,14723,14728,14729,14734,14735,14758,14759,14764,14765,14770,14771,14911,14913,14917,14919,14923,14925,15007,15009,15013,15015,15019,15021,15067,15069,15073]
def ridgeSupport452_015 : List Nat := [15075,15079,15081]
def ridgeSupport452_code : Nat := 0x3ae9eb9fae3eb87addeb6faadeaafaa7ea97aa1ea7fa4de92fa47e917a41e8ff9b3e6cb9ade6b39a7e69b98fe63b989e623983e60b78bde2b789de23787de1b62fd8bb62dd8b362bd8ab560d57b55ad563554d54b4f8d3d34f2d10f442d107440d0ff43ed013402cffb3fccfe33f6ce73398ce5b263c98b261c98325fc97b224c88b21ec873218c85b1bcc6e31b6bcb6f2cbcaef2abca6f28bb42ecebb2aec8bb12ec2ba32e88ba1ae4cb92ae46b912e40b8fae08b812e02b0cec32b0c6c30b0bec2eb09ec26b096c24b08ec22a88ea22a886a20a87ea1ea85ea16a856a14a84ea12a3668d8a35e8d6a3568d4a2e28b6a2ca8b0a2b28aaa16e85aa156854a13e84ea0ae82aa096824a07e81ea04280ea02a808a0128029ca67289c9e7269c967249c2e70a9c267089c1e7069b266c89b1e6c69b166c49aa26a69a8a6a09a7269a992e64a991664498fe63e986e61a9856614983e60e98025fe97ea5f897d25f290a6428909e4269096424902e40a9026408901e4068f263c88f1e3c68f163c48ea23a68e8a3a08e7239a8d2e34a8d163448cfe33e8c6e31a8c563148c3e30e8c022fe8bea2f88bd22f27c35f0c7c2df0a7c25f087c05f007bfdefe7bf5efc7ac1eae7aa9ea87a91ea27a01e7e79e9e7879d1e72788de227875e1c785de167821e067809e0077f1dfa77cddf277b5dec779dde67701dbe76e9db876d1db27641d8e7629d887611d8274cdd3274b5d2c749dd267461d167449d107431d0a740dd0273f5cfc73ddcf668fda3e68f5a3c68eda3a68cda3268c5a3068bda2e5e1d7865e157845e0d7825ded77a5de57785ddd7765925648591d646591564456e55b856dd5b656d55b45625588561d58656155844f353cc4f2d3ca4f253c84ebd3ae4eb53ac4ead3aa4e453904e3d38e4e3538c4c053004bfd2fe4bf52fc4b452d04b3d2ce4b352cc403500c402d00a40250083fbcfee3fb4fec3facfea3f44fd03f3cfce3f34fcc3d04f403cfcf3e3cf4f3c3c44f103c3cf0e3c34f0c2624988261c986261498425f497c25ec97a25e4978250494024fc93e24f493c23848e0237c8de23748dc220488021fc87e21f487c20e483820dc83620d48341f647d81f5c7d61f547d41de47781ddc7761dd477415985651590508141c50612d04b312c8418105c4160ad02b30ac81ab06a81a9
def ridgeSupport452_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport452_code
def ridgeSupport452_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport452_code
def ridgeSupport452_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport452_code
def ridgeSupport452_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport452_code
def ridgeSupport452_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport452_code
def ridgeSupport452_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport452_code
def ridgeSupport452_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport452_code
def ridgeSupport452_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport452_code
def ridgeSupport452_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport452_code
def ridgeSupport452_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport452_code
def ridgeSupport452_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport452_code
def ridgeSupport452_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport452_code
def ridgeSupport452_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport452_code
def ridgeSupport452_rest_013 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport452_code
def ridgeSupport452_rest_014 : Nat := PackedRawNatGrowth.drop 6272 ridgeSupport452_code
def ridgeSupport452_rest_015 : Nat := PackedRawNatGrowth.drop 6720 ridgeSupport452_code
def ridgeSupport452_rest_016 : Nat := PackedRawNatGrowth.drop 6762 ridgeSupport452_code
def ridgeSupport452_suffix_016 : List Nat := []
def ridgeSupport452_suffix_015 : List Nat := ridgeSupport452_015 ++ ridgeSupport452_suffix_016
def ridgeSupport452_suffix_014 : List Nat := ridgeSupport452_014 ++ ridgeSupport452_suffix_015
def ridgeSupport452_suffix_013 : List Nat := ridgeSupport452_013 ++ ridgeSupport452_suffix_014
def ridgeSupport452_suffix_012 : List Nat := ridgeSupport452_012 ++ ridgeSupport452_suffix_013
def ridgeSupport452_suffix_011 : List Nat := ridgeSupport452_011 ++ ridgeSupport452_suffix_012
def ridgeSupport452_suffix_010 : List Nat := ridgeSupport452_010 ++ ridgeSupport452_suffix_011
def ridgeSupport452_suffix_009 : List Nat := ridgeSupport452_009 ++ ridgeSupport452_suffix_010
def ridgeSupport452_suffix_008 : List Nat := ridgeSupport452_008 ++ ridgeSupport452_suffix_009
def ridgeSupport452_suffix_007 : List Nat := ridgeSupport452_007 ++ ridgeSupport452_suffix_008
def ridgeSupport452_suffix_006 : List Nat := ridgeSupport452_006 ++ ridgeSupport452_suffix_007
def ridgeSupport452_suffix_005 : List Nat := ridgeSupport452_005 ++ ridgeSupport452_suffix_006
def ridgeSupport452_suffix_004 : List Nat := ridgeSupport452_004 ++ ridgeSupport452_suffix_005
def ridgeSupport452_suffix_003 : List Nat := ridgeSupport452_003 ++ ridgeSupport452_suffix_004
def ridgeSupport452_suffix_002 : List Nat := ridgeSupport452_002 ++ ridgeSupport452_suffix_003
def ridgeSupport452_suffix_001 : List Nat := ridgeSupport452_001 ++ ridgeSupport452_suffix_002
def ridgeSupport452_suffix_000 : List Nat := ridgeSupport452_000 ++ ridgeSupport452_suffix_001
theorem ridgeSupport452_source : candidateRows 452 =
    (PackedRawNatGrowth.readList 14 483 ridgeSupport452_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
