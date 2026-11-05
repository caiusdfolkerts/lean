module
prelude
public import RootedSevenTwoSix13GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport704_000 : List Nat := [184,185,186,187,194,195,241,242,243,244,251,252,286,288,290,292,294,299,300,302,305,319,320,321,322,329,330,364,366,368,370,372]
def ridgeSupport704_001 : List Nat := [377,378,380,383,385,387,389,391,393,398,399,401,404,478,480,481,483,485,488,490,492,493,495,497,500,515,516,517,518,521,522,523]
def ridgeSupport704_002 : List Nat := [524,534,535,539,540,541,542,546,547,550,552,553,555,557,560,562,564,565,567,569,572,587,588,589,590,593,594,595,596,606,607,611]
def ridgeSupport704_003 : List Nat := [612,613,614,618,619,622,624,625,627,629,632,634,636,637,639,641,644,659,660,661,662,665,666,667,668,678,679,683,684,685,686,690]
def ridgeSupport704_004 : List Nat := [691,874,876,877,879,894,895,899,900,901,902,906,907,911,912,913,914,952,953,956,957,958,959,962,963,970,975,976,981,982,984,985]
def ridgeSupport704_005 : List Nat := [987,1002,1003,1007,1008,1009,1010,1014,1015,1019,1020,1021,1022,1060,1061,1064,1065,1066,1067,1070,1071,1078,1083,1084,1089,1090,1092,1093,1095,1110,1111,1115]
def ridgeSupport704_006 : List Nat := [1116,1117,1118,1122,1123,1127,1128,1129,1130,1168,1169,1172,1173,1174,1175,1178,1179,1186,1191,1192,1197,1206,1207,1212,1213,1218,1219,1314,1315,1318,1323,1326]
def ridgeSupport704_007 : List Nat := [1327,1330,1335,1350,1351,1356,1357,1368,1369,1372,1377,1380,1381,1384,1389,1404,1405,1410,1411,1422,1423,1426,1431,1434,1435,1438,1443,1458,1459,1464,1465,1493]
def ridgeSupport704_008 : List Nat := [1494,1495,1496,1511,1512,1513,1514,1529,1530,1531,1532,1764,1765,1776,1777,1800,1801,1812,1813,1836,1837,1848,1849,1872,1873,1884,1885,1908,1909,1920,1921,1944]
def ridgeSupport704_009 : List Nat := [1945,1956,1957]
def ridgeSupport704_code : Nat := 0x1e97d2799f31e07c0775ee9d77ae751ea1ce79c72de59c578a709e11bc7786e5dc97f2fddfabf37aaf4de8bcf762ebdd6bab6e6dc5b3b6568ecf59bb3565ec958fb1d60ec157daf95b6b4565ac9586ae559ab1536a6547a8d4de9952fa5d4ae93523a4530e614bd9792de5b4ad95129e5149b93525e4b4959292464846a8d31a233c638c517a2ec5c8b715e2b44788b112214418790ee1b42f85d0ae15429851096123fe7faff1fdbf77ecfc9f8bf07defadf53db7b2f61eb3d57a0f3de53c3784efddf3bd778ee5dc392722e41c7b8b714e19c2b84706dfdbf36f6dadb1b52b3564ab956aac556a9d5329c536a694ca9652aa5149a845029fd3ea7c4f49e13aa734e29c13726b4d499932a644c697d2f2544a694928a4e49a93125a3c4728dd1aa344648c116a2b4528a1132234448790ea1c43685d0b20c41682904a0640a811019f43e27bcf69ec3d47a0f29e33c2780ef19432263cc718930e614c19812fe5f0bd1792e85c8b816e2d8528a49422825009f93125c4b0959262484889011e1f83ec7a0f31e43c4618c21762e85c8b8
def ridgeSupport704_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport704_code
def ridgeSupport704_rest_001 : Nat := PackedRawNatGrowth.drop 352 ridgeSupport704_code
def ridgeSupport704_rest_002 : Nat := PackedRawNatGrowth.drop 704 ridgeSupport704_code
def ridgeSupport704_rest_003 : Nat := PackedRawNatGrowth.drop 1056 ridgeSupport704_code
def ridgeSupport704_rest_004 : Nat := PackedRawNatGrowth.drop 1408 ridgeSupport704_code
def ridgeSupport704_rest_005 : Nat := PackedRawNatGrowth.drop 1760 ridgeSupport704_code
def ridgeSupport704_rest_006 : Nat := PackedRawNatGrowth.drop 2112 ridgeSupport704_code
def ridgeSupport704_rest_007 : Nat := PackedRawNatGrowth.drop 2464 ridgeSupport704_code
def ridgeSupport704_rest_008 : Nat := PackedRawNatGrowth.drop 2816 ridgeSupport704_code
def ridgeSupport704_rest_009 : Nat := PackedRawNatGrowth.drop 3168 ridgeSupport704_code
def ridgeSupport704_rest_010 : Nat := PackedRawNatGrowth.drop 3201 ridgeSupport704_code
def ridgeSupport704_suffix_010 : List Nat := []
def ridgeSupport704_suffix_009 : List Nat := ridgeSupport704_009 ++ ridgeSupport704_suffix_010
def ridgeSupport704_suffix_008 : List Nat := ridgeSupport704_008 ++ ridgeSupport704_suffix_009
def ridgeSupport704_suffix_007 : List Nat := ridgeSupport704_007 ++ ridgeSupport704_suffix_008
def ridgeSupport704_suffix_006 : List Nat := ridgeSupport704_006 ++ ridgeSupport704_suffix_007
def ridgeSupport704_suffix_005 : List Nat := ridgeSupport704_005 ++ ridgeSupport704_suffix_006
def ridgeSupport704_suffix_004 : List Nat := ridgeSupport704_004 ++ ridgeSupport704_suffix_005
def ridgeSupport704_suffix_003 : List Nat := ridgeSupport704_003 ++ ridgeSupport704_suffix_004
def ridgeSupport704_suffix_002 : List Nat := ridgeSupport704_002 ++ ridgeSupport704_suffix_003
def ridgeSupport704_suffix_001 : List Nat := ridgeSupport704_001 ++ ridgeSupport704_suffix_002
def ridgeSupport704_suffix_000 : List Nat := ridgeSupport704_000 ++ ridgeSupport704_suffix_001
theorem ridgeSupport704_source : candidateRows 704 =
    (PackedRawNatGrowth.readList 11 291 ridgeSupport704_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
