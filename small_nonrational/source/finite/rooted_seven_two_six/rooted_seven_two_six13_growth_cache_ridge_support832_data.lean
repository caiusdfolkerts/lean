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
def ridgeSupport832_000 : List Nat := [196,197,198,199,206,207,253,254,255,256,263,264,287,288,289,292,293,298,299,304,306,331,332,333,334,341,342,365,366,367,370,371]
def ridgeSupport832_001 : List Nat := [376,377,382,384,386,387,388,391,392,397,398,403,405,478,479,480,482,487,489,490,491,492,494,499,501,514,515,517,519,520,521,523]
def ridgeSupport832_002 : List Nat := [525,532,533,538,539,541,543,544,545,550,551,552,554,559,561,562,563,564,566,571,573,586,587,589,591,592,593,595,597,604,605,610]
def ridgeSupport832_003 : List Nat := [611,613,615,616,617,622,623,624,626,631,633,634,635,636,638,643,645,658,659,661,663,664,665,667,669,676,677,682,683,685,687,688]
def ridgeSupport832_004 : List Nat := [689,874,875,876,878,892,893,898,899,901,903,904,905,910,911,913,915,954,955,956,957,960,961,962,963,972,974,978,980,982,983,984]
def ridgeSupport832_005 : List Nat := [986,1000,1001,1006,1007,1009,1011,1012,1013,1018,1019,1021,1023,1062,1063,1064,1065,1068,1069,1070,1071,1080,1082,1086,1088,1090,1091,1092,1094,1108,1109,1114]
def ridgeSupport832_006 : List Nat := [1115,1117,1119,1120,1121,1126,1127,1129,1131,1170,1171,1172,1173,1176,1177,1178,1179,1188,1190,1194,1196,1204,1205,1210,1211,1216,1217,1312,1313,1320,1322,1324]
def ridgeSupport832_007 : List Nat := [1325,1332,1334,1348,1349,1354,1355,1366,1367,1374,1376,1378,1379,1386,1388,1402,1403,1408,1409,1420,1421,1428,1430,1432,1433,1440,1442,1456,1457,1462,1463,1492]
def ridgeSupport832_008 : List Nat := [1493,1495,1497,1510,1511,1513,1515,1528,1529,1531,1533,1762,1763,1774,1775,1798,1799,1810,1811,1834,1835,1846,1847,1870,1871,1882,1883,1906,1907,1918,1919,1942]
def ridgeSupport832_009 : List Nat := [1943,1954,1955]
def ridgeSupport832_code : Nat := 0x1e8fd1797f2ddffbf773ee5d6fad74fe9dcdf9b72be55c4f89707e0dbbf776e3dc57f6fddf9bf17aef4de7bcd766ebdd5ba96dedb5b1b6168ad0599b3165aca58db19606c057baf55b2b5563ac5582af557aad52ea5545a894da9a52da594aa94521a41306604bb9752d65a4ac95529a5249b9352664c49592924e4946b8d319e334618c117e2ec5b8b51562a44688910e2144087d0ea1c42f85d0b61642985109e133ff7fafedfd3f57e8fcdf8bef7dcfa5f43da7b0f5deb3d47a4f39e63c3784f05e03bd778eeddd393722e3dc7389710e1dc2b83704df5be36e6d8dadb52b1560abd56aab554a955229d536a654c29752aa4d492855069f93e27b4f49e53ba724e09bd372694d099d32a634c49752e2554a69452824f49a92d2523d4768d91a2334648c517a2a45089d1322144087d0ea1b4348550a20d4168250420740a80d011f53e67b8f61eb3d47a4f39e23c077cef195326638c698830e610c19823005f8bc9782e65c8b796e2da558aa94e29a530a59322604ac951252484849011f21041c800ff1fc3f4678ce18e318628c4
def ridgeSupport832_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport832_code
def ridgeSupport832_rest_001 : Nat := PackedRawNatGrowth.drop 352 ridgeSupport832_code
def ridgeSupport832_rest_002 : Nat := PackedRawNatGrowth.drop 704 ridgeSupport832_code
def ridgeSupport832_rest_003 : Nat := PackedRawNatGrowth.drop 1056 ridgeSupport832_code
def ridgeSupport832_rest_004 : Nat := PackedRawNatGrowth.drop 1408 ridgeSupport832_code
def ridgeSupport832_rest_005 : Nat := PackedRawNatGrowth.drop 1760 ridgeSupport832_code
def ridgeSupport832_rest_006 : Nat := PackedRawNatGrowth.drop 2112 ridgeSupport832_code
def ridgeSupport832_rest_007 : Nat := PackedRawNatGrowth.drop 2464 ridgeSupport832_code
def ridgeSupport832_rest_008 : Nat := PackedRawNatGrowth.drop 2816 ridgeSupport832_code
def ridgeSupport832_rest_009 : Nat := PackedRawNatGrowth.drop 3168 ridgeSupport832_code
def ridgeSupport832_rest_010 : Nat := PackedRawNatGrowth.drop 3201 ridgeSupport832_code
def ridgeSupport832_suffix_010 : List Nat := []
def ridgeSupport832_suffix_009 : List Nat := ridgeSupport832_009 ++ ridgeSupport832_suffix_010
def ridgeSupport832_suffix_008 : List Nat := ridgeSupport832_008 ++ ridgeSupport832_suffix_009
def ridgeSupport832_suffix_007 : List Nat := ridgeSupport832_007 ++ ridgeSupport832_suffix_008
def ridgeSupport832_suffix_006 : List Nat := ridgeSupport832_006 ++ ridgeSupport832_suffix_007
def ridgeSupport832_suffix_005 : List Nat := ridgeSupport832_005 ++ ridgeSupport832_suffix_006
def ridgeSupport832_suffix_004 : List Nat := ridgeSupport832_004 ++ ridgeSupport832_suffix_005
def ridgeSupport832_suffix_003 : List Nat := ridgeSupport832_003 ++ ridgeSupport832_suffix_004
def ridgeSupport832_suffix_002 : List Nat := ridgeSupport832_002 ++ ridgeSupport832_suffix_003
def ridgeSupport832_suffix_001 : List Nat := ridgeSupport832_001 ++ ridgeSupport832_suffix_002
def ridgeSupport832_suffix_000 : List Nat := ridgeSupport832_000 ++ ridgeSupport832_suffix_001
theorem ridgeSupport832_source : candidateRows 832 =
    (PackedRawNatGrowth.readList 11 291 ridgeSupport832_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
