module
prelude
public import RootedSixBase00GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport898_000 : List Nat := [346,347,348,770,771,772,926,927,928,1010,1011,1012,1032,1033,1034,5896,5897,5898,5899,5900,5901,5992,5993,5994,5995,5996,5997,6088,6089,6090,6091,6092]
def ridgeSupport898_001 : List Nat := [6093,6448,6449,6450,6451,6452,6453,6496,6497,6498,6499,6500,6501,6640,6641,6642,6643,6644,6645,7012,7013,7014,7015,7016,7017,7042,7043,7044,7045,7046,7047,7408]
def ridgeSupport898_002 : List Nat := [7409,7410,7411,7412,7413,7456,7457,7458,7459,7460,7461,7600,7601,7602,7603,7604,7605,7972,7973,7974,7975,7976,7977,8002,8003,8004,8005,8006,8007,8800,8801,8802]
def ridgeSupport898_003 : List Nat := [8803,8804,8805,8848,8849,8850,8851,8852,8853,8992,8993,8994,8995,8996,8997,9640,9641,9642,9643,9644,9645,9652,9653,9654,9655,9656,9657,10336,10337,10338,10339,10340]
def ridgeSupport898_004 : List Nat := [10341,10348,10349,10350,10351,10352,10353,12526,12527,12532,12533,12538,12539,12553,12555,12559,12561,12565,12567,12574,12575,12580,12581,12586,12587,12673,12675,12679,12681,12685,12687,12721]
def ridgeSupport898_005 : List Nat := [12723,12727,12729,12733,12735,13009,13011,13015,13017,13021,13023,13030,13031,13036,13037,13042,13043,13078,13079,13084,13085,13090,13091,13177,13179,13183,13185,13189,13191,13192,13193,13194]
def ridgeSupport898_006 : List Nat := [13195,13196,13197,13492,13493,13494,13495,13496,13497,13522,13523,13524,13525,13526,13527,13777,13779,13783,13785,13789,13791,13798,13799,13804,13805,13810,13811,13846,13847,13852,13853,13858]
def ridgeSupport898_007 : List Nat := [13859,13945,13947,13951,13953,13957,13959,13960,13961,13962,13963,13964,13965,14260,14261,14262,14263,14264,14265,14290,14291,14292,14293,14294,14295,14833,14835,14839,14841,14845,14847,14854]
def ridgeSupport898_008 : List Nat := [14855,14860,14861,14866,14867,14902,14903,14908,14909,14914,14915,15001,15003,15007,15009,15013,15015,15016,15017,15018,15019,15020,15021,15568,15569,15570,15571,15572,15573,15580,15581,15582]
def ridgeSupport898_009 : List Nat := [15583,15584,15585,16096,16097,16098,16099,16100,16101,16108,16109,16110,16111,16112,16113,17723,17725,17727,17785,17787,17791,17793,17797,17799,17975,17977,17979,18073,18075,18079,18081,18085]
def ridgeSupport898_010 : List Nat := [18087,18298,18299,18300,18301,18302,18303,18455,18457,18459,18553,18555,18559,18561,18565,18567,18778,18779,18780,18781,18782,18783,19151,19153,19155,19249,19251,19255,19257,19261,19263,19618]
def ridgeSupport898_011 : List Nat := [19619,19620,19621,19622,19623,19966,19967,19968,19969,19970,19971,21358,21359,21364,21365,21370,21371,21432,21434,21438,21440,21444,21446,21528,21530,21534,21536,21540,21542,21648,21650,21654]
def ridgeSupport898_012 : List Nat := [21656,21660,21662]
def ridgeSupport898_code : Nat := 0x1527aa4e5498a92d524aa485426a8495082a0f541aa8314f1a9e253c0a77d4eea9dc537ba6f54dd69ba536fa6dd380e7014e019c0137fe6ff4ca7994d32966524ca399452cfe59ecb39966f2cce598cad395a32b3e4afc95e92bb25724adc95a910f2216440c87f90f721e640dc819902f1dfe3bf477d8ef91dee3bd46a78d4b1a8634fc69b8d3318ee31cc6378b0f16162c0c57f8af715e629fc53d8a76fbc5f783eef7ddcfbb5f763ee57dc8fb8df713ee17dc0f385e703cdf79bcf375e6e3cd579a8f34de693cd179a0eab5d563aab7554eaa5d543aa7754aea85d4fba9b7532e90dd213a3d7478e8ddd1b3a137424e835d063a07740ce7fdcfeb9f973eee7cdcf8b7d76facdf55bea37d36fa4dee5bdc37b76f6cded5bda368d6d18da2db4536896d10da1db42b6816cfed9edb3cb6236c44d875b0e36176c2cd7cdaf935ed6bd8d79daf335df6bbad765aebb5d36ba2d35da6b34d569a8d34da6934b96970d2dda5b34b56968ce359c6338b6714ce259c43387670ace059bfb37b66f2cc8d991331d6638cc5d98b32f365e4cbb597632e765cccb7d96eb2d965aecb4d968b1bf637ac6e58dbb1b36362c63d8c6b189630ec60d8c0b12b6254c495892311f623cc45d88ab111621ec42d884b0fb61f4c3d587a30ef61dca1c5438286f50dca1b5436286550c8a18d431286150c096e52dc25b74b6c96d52da25ad4b5896ad2d525a94b508c95192232346448c85190229545288a4d149229145208995132226344c489851301f473e8c7d14fa21f433e847ca4f941f273e4c7c94f921db53b6876cced91db13b607494e921d233a447484e901cf539e873cce791cf139e06e1cdc31b8537086e0cdc11b6936d06d9cdb31b6536c867d4cfa19f333e467c4cf8196532c8658ccb1196132c064d4c9a1933326464c4c9817cd2f985f2cbe517c92f905db4bb6176b2ed45da4bb4170d2e185c2cb8517092e101028204840807e80fcc1f903a0073e0e781820303060405700ad815a
def ridgeSupport898_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport898_code
def ridgeSupport898_rest_001 : Nat := PackedRawNatGrowth.drop 480 ridgeSupport898_code
def ridgeSupport898_rest_002 : Nat := PackedRawNatGrowth.drop 960 ridgeSupport898_code
def ridgeSupport898_rest_003 : Nat := PackedRawNatGrowth.drop 1440 ridgeSupport898_code
def ridgeSupport898_rest_004 : Nat := PackedRawNatGrowth.drop 1920 ridgeSupport898_code
def ridgeSupport898_rest_005 : Nat := PackedRawNatGrowth.drop 2400 ridgeSupport898_code
def ridgeSupport898_rest_006 : Nat := PackedRawNatGrowth.drop 2880 ridgeSupport898_code
def ridgeSupport898_rest_007 : Nat := PackedRawNatGrowth.drop 3360 ridgeSupport898_code
def ridgeSupport898_rest_008 : Nat := PackedRawNatGrowth.drop 3840 ridgeSupport898_code
def ridgeSupport898_rest_009 : Nat := PackedRawNatGrowth.drop 4320 ridgeSupport898_code
def ridgeSupport898_rest_010 : Nat := PackedRawNatGrowth.drop 4800 ridgeSupport898_code
def ridgeSupport898_rest_011 : Nat := PackedRawNatGrowth.drop 5280 ridgeSupport898_code
def ridgeSupport898_rest_012 : Nat := PackedRawNatGrowth.drop 5760 ridgeSupport898_code
def ridgeSupport898_rest_013 : Nat := PackedRawNatGrowth.drop 5805 ridgeSupport898_code
def ridgeSupport898_suffix_013 : List Nat := []
def ridgeSupport898_suffix_012 : List Nat := ridgeSupport898_012 ++ ridgeSupport898_suffix_013
def ridgeSupport898_suffix_011 : List Nat := ridgeSupport898_011 ++ ridgeSupport898_suffix_012
def ridgeSupport898_suffix_010 : List Nat := ridgeSupport898_010 ++ ridgeSupport898_suffix_011
def ridgeSupport898_suffix_009 : List Nat := ridgeSupport898_009 ++ ridgeSupport898_suffix_010
def ridgeSupport898_suffix_008 : List Nat := ridgeSupport898_008 ++ ridgeSupport898_suffix_009
def ridgeSupport898_suffix_007 : List Nat := ridgeSupport898_007 ++ ridgeSupport898_suffix_008
def ridgeSupport898_suffix_006 : List Nat := ridgeSupport898_006 ++ ridgeSupport898_suffix_007
def ridgeSupport898_suffix_005 : List Nat := ridgeSupport898_005 ++ ridgeSupport898_suffix_006
def ridgeSupport898_suffix_004 : List Nat := ridgeSupport898_004 ++ ridgeSupport898_suffix_005
def ridgeSupport898_suffix_003 : List Nat := ridgeSupport898_003 ++ ridgeSupport898_suffix_004
def ridgeSupport898_suffix_002 : List Nat := ridgeSupport898_002 ++ ridgeSupport898_suffix_003
def ridgeSupport898_suffix_001 : List Nat := ridgeSupport898_001 ++ ridgeSupport898_suffix_002
def ridgeSupport898_suffix_000 : List Nat := ridgeSupport898_000 ++ ridgeSupport898_suffix_001
theorem ridgeSupport898_source : candidateRows 898 =
    (PackedRawNatGrowth.readList 15 387 ridgeSupport898_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase00
