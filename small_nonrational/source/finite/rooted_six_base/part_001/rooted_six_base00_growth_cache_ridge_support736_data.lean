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
def ridgeSupport736_000 : List Nat := [1386,1387,1388,1651,1652,1653,1760,1761,1762,1858,1859,1860,10444,10445,10446,10447,10448,10449,10540,10541,10542,10543,10544,10545,10636,10637,10638,10639,10640,10641,10708,10709]
def ridgeSupport736_001 : List Nat := [10710,10711,10712,10713,10804,10805,10806,10807,10808,10809,10900,10901,10902,10903,10904,10905,11074,11075,11076,11077,11078,11079,11086,11087,11088,11089,11090,11091,11404,11405,11406,11407]
def ridgeSupport736_002 : List Nat := [11408,11409,11500,11501,11502,11503,11504,11505,11596,11597,11598,11599,11600,11601,11770,11771,11772,11773,11774,11775,11782,11783,11784,11785,11786,11787,12202,12203,12204,12205,12206,12207]
def ridgeSupport736_003 : List Nat := [12214,12215,12216,12217,12218,12219,16122,16123,16128,16129,16142,16143,16145,16148,16151,16154,16162,16164,16170,16171,16176,16177,16190,16191,16265,16268,16271,16274,16282,16284,16313,16316]
def ridgeSupport736_004 : List Nat := [16319,16322,16330,16332,16362,16363,16368,16369,16382,16383,16385,16388,16391,16394,16402,16404,16410,16411,16416,16417,16430,16431,16505,16508,16511,16514,16522,16524,16553,16556,16559,16562]
def ridgeSupport736_005 : List Nat := [16570,16572,16714,16715,16716,16717,16718,16719,16726,16727,16728,16729,16730,16731,16890,16891,16896,16897,16910,16911,16913,16916,16919,16922,16930,16932,16938,16939,16944,16945,16958,16959]
def ridgeSupport736_006 : List Nat := [17033,17036,17039,17042,17050,17052,17081,17084,17087,17090,17098,17100,17242,17243,17244,17245,17246,17247,17254,17255,17256,17257,17258,17259,17530,17531,17532,17533,17534,17535,17542,17543]
def ridgeSupport736_007 : List Nat := [17544,17545,17546,17547,19985,19988,19992,20045,20048,20051,20054,20062,20064,20117,20120,20124,20177,20180,20183,20186,20194,20196,20332,20333,20334,20335,20336,20337,20465,20468,20472,20525]
def ridgeSupport736_008 : List Nat := [20528,20531,20534,20542,20544,20680,20681,20682,20683,20684,20685,20896,20897,20898,20899,20900,20901,21798,21799,21804,21805,21818,21819,21834,21835,21840,21841,21854,21855,21894,21895,21900]
def ridgeSupport736_009 : List Nat := [21901,21914,21915]
def ridgeSupport736_code : Nat := 0x1566eacd558dab19561eac3555faabd5546aa8554baa9554eea9d552daa59549ea9351a5a349468e8d151a1a341433686650cba19543268645040a07d40da819d030a05b3fe27fa4ff19ee33dc27b7cf6e9edb3db27724ee29db53b5e76a4ed19d393a6274ace609cbd395a729ce509c9b386270a4e118917122a244c488890f121a23fc47e88fb11f223dc47a86d70daa1b4c36886cf0d9a1afc35e86bb0d721adc35a85990b2a16142bf85790ae614e429a85250a3e1464289847f08fa118c230845708aa11242228435085e10a4211841f083a100c20083f707ea0adc15a82b305620abc156829f053a0a6c14c8297052a05e40ba816502be05640a98119022a041407f80f901e6017c02e8043008200dc01a8029004a005400780090005fffbffe7fe2ffc1ff5bfea7f98ff29fe13fbf7f78fee5fce3f9a7f24fe3dfc63f897e7efcf9f98bf307e56fca9f923f227e34fc5df8a3f117e1efc39f80bf007df6fbe97ddafba5f72bee17dbafb65f5ebeb97d6afac5f56bea9705ae0a5c12b821703ae065bfeb7f96feadfc5bf6b7e96a8ad505a9eb5396a6ad4c59e2b3c1677acee59dab3b1648ac90591eb239646ac8c56a6ad495a8ab50569ead395a3ab46568aad115a1ab425532aa6154baa96552aaa5151caa38546ea8d951aaa3453b2a7614eba9d653aaa7514c8a990531ea6394c6a98c5262a4c1497a92e525aa4b1468a8d0519ea339466a8cc0e881d0c3a106e20dc21b8033a86740ce615b02b5856a
def ridgeSupport736_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport736_code
def ridgeSupport736_rest_001 : Nat := PackedRawNatGrowth.drop 480 ridgeSupport736_code
def ridgeSupport736_rest_002 : Nat := PackedRawNatGrowth.drop 960 ridgeSupport736_code
def ridgeSupport736_rest_003 : Nat := PackedRawNatGrowth.drop 1440 ridgeSupport736_code
def ridgeSupport736_rest_004 : Nat := PackedRawNatGrowth.drop 1920 ridgeSupport736_code
def ridgeSupport736_rest_005 : Nat := PackedRawNatGrowth.drop 2400 ridgeSupport736_code
def ridgeSupport736_rest_006 : Nat := PackedRawNatGrowth.drop 2880 ridgeSupport736_code
def ridgeSupport736_rest_007 : Nat := PackedRawNatGrowth.drop 3360 ridgeSupport736_code
def ridgeSupport736_rest_008 : Nat := PackedRawNatGrowth.drop 3840 ridgeSupport736_code
def ridgeSupport736_rest_009 : Nat := PackedRawNatGrowth.drop 4320 ridgeSupport736_code
def ridgeSupport736_rest_010 : Nat := PackedRawNatGrowth.drop 4365 ridgeSupport736_code
def ridgeSupport736_suffix_010 : List Nat := []
def ridgeSupport736_suffix_009 : List Nat := ridgeSupport736_009 ++ ridgeSupport736_suffix_010
def ridgeSupport736_suffix_008 : List Nat := ridgeSupport736_008 ++ ridgeSupport736_suffix_009
def ridgeSupport736_suffix_007 : List Nat := ridgeSupport736_007 ++ ridgeSupport736_suffix_008
def ridgeSupport736_suffix_006 : List Nat := ridgeSupport736_006 ++ ridgeSupport736_suffix_007
def ridgeSupport736_suffix_005 : List Nat := ridgeSupport736_005 ++ ridgeSupport736_suffix_006
def ridgeSupport736_suffix_004 : List Nat := ridgeSupport736_004 ++ ridgeSupport736_suffix_005
def ridgeSupport736_suffix_003 : List Nat := ridgeSupport736_003 ++ ridgeSupport736_suffix_004
def ridgeSupport736_suffix_002 : List Nat := ridgeSupport736_002 ++ ridgeSupport736_suffix_003
def ridgeSupport736_suffix_001 : List Nat := ridgeSupport736_001 ++ ridgeSupport736_suffix_002
def ridgeSupport736_suffix_000 : List Nat := ridgeSupport736_000 ++ ridgeSupport736_suffix_001
theorem ridgeSupport736_source : candidateRows 736 =
    (PackedRawNatGrowth.readList 15 291 ridgeSupport736_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase00
