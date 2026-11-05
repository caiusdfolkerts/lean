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
def ridgeSupport833_000 : List Nat := [314,315,316,470,471,472,554,555,556,600,601,602,1656,1657,1658,1659,1660,1661,1704,1705,1706,1707,1708,1709,1848,1849,1850,1851,1852,1853,1920,1921]
def ridgeSupport833_001 : List Nat := [1922,1923,1924,1925,1968,1969,1970,1971,1972,1973,2112,2113,2114,2115,2116,2117,2646,2647,2648,2649,2650,2651,2658,2659,2660,2661,2662,2663,2880,2881,2882,2883]
def ridgeSupport833_002 : List Nat := [2884,2885,2928,2929,2930,2931,2932,2933,3072,3073,3074,3075,3076,3077,3606,3607,3608,3609,3610,3611,3618,3619,3620,3621,3622,3623,4302,4303,4304,4305,4306,4307]
def ridgeSupport833_003 : List Nat := [4314,4315,4316,4317,4318,4319,7173,7175,7183,7186,7189,7192,7194,7195,7208,7209,7214,7215,7242,7243,7256,7257,7262,7263,7341,7343,7351,7354,7357,7360,7368,7369]
def ridgeSupport833_004 : List Nat := [7370,7371,7372,7373,7413,7415,7423,7426,7429,7432,7434,7435,7448,7449,7454,7455,7482,7483,7496,7497,7502,7503,7581,7583,7591,7594,7597,7600,7608,7609,7610,7611]
def ridgeSupport833_005 : List Nat := [7612,7613,8082,8083,8084,8085,8086,8087,8094,8095,8096,8097,8098,8099,8181,8183,8191,8194,8197,8200,8202,8203,8216,8217,8222,8223,8250,8251,8264,8265,8270,8271]
def ridgeSupport833_006 : List Nat := [8349,8351,8359,8362,8365,8368,8376,8377,8378,8379,8380,8381,8850,8851,8852,8853,8854,8855,8862,8863,8864,8865,8866,8867,9378,9379,9380,9381,9382,9383,9390,9391]
def ridgeSupport833_007 : List Nat := [9392,9393,9394,9395,11637,11639,11644,11733,11735,11743,11746,11749,11752,11769,11771,11776,11865,11867,11875,11878,11881,11884,12186,12187,12188,12189,12190,12191,12249,12251,12256,12345]
def ridgeSupport833_008 : List Nat := [12347,12355,12358,12361,12364,12666,12667,12668,12669,12670,12671,13014,13015,13016,13017,13018,13019,14684,14686,14694,14699,14700,14705,14720,14722,14730,14735,14736,14741,14816,14818,14826]
def ridgeSupport833_009 : List Nat := [14831,14832,14837]
def ridgeSupport833_code : Nat := 0x39f5e7c39efe7ab9e2e783995e64398fe62b982e603971e5b396be59b95ee5732dbcb6b2d9cb632d7cb5b17fc5fb17dc5f317bc5eb04cc127046c10f03bc0e6fe0bf6efd9be7ef9ebe76f9cbe6ef9ab9b2e69b99ae63b96ee59b802dfbb7e6de8b796de2b77edd7b756d7cb5ded7592ce4b292c64b092be4ae929e4a692964a4928e4a28a8e2a28a862a08a7e29e8a5e2968a562948a4e29282f60bc82ee0ba82e60b882c20ad82aa0a7827e09d813e04e812604880ee03a807e01e8066018802e00a80220058009fff7fddff57e8dfa27e85fa07e7df9e7e5df967e55f947e4df9276f5dbc76eddba76e5db876c1dad76a9da7767dd9d753dd4e7525d4874edd3a747dd1e7465d18742dd0a7421d057409cff73ddcf57335ccc732dcca7325cc87301cbd72e9cb772bdcad717dc5e7165c58712dc4a70bdc2e70a5c28706dc1a7061c157049c0f701dc05437d0de43750dc436d0da434d0d243450d0433d0ce389ce263894e24388ce22386ce1a3864e18385ce163014c04300cc023004c002dd4b742dccb722dc4b702d14b442d0cb422d04b40299ca662994a64298ca62296ca5a2964a58295ca562114844210c84221048401ed47b41ecc7b21ec47b01e147841e0c7821e047801cf473c1cec73a1ce47381ab46ac1aac6aa1aa46a819f467c19ec67a19e46780968259096022c08ac22a07601d7075813c04ec13a
def ridgeSupport833_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport833_code
def ridgeSupport833_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport833_code
def ridgeSupport833_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport833_code
def ridgeSupport833_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport833_code
def ridgeSupport833_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport833_code
def ridgeSupport833_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport833_code
def ridgeSupport833_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport833_code
def ridgeSupport833_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport833_code
def ridgeSupport833_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport833_code
def ridgeSupport833_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport833_code
def ridgeSupport833_rest_010 : Nat := PackedRawNatGrowth.drop 4074 ridgeSupport833_code
def ridgeSupport833_suffix_010 : List Nat := []
def ridgeSupport833_suffix_009 : List Nat := ridgeSupport833_009 ++ ridgeSupport833_suffix_010
def ridgeSupport833_suffix_008 : List Nat := ridgeSupport833_008 ++ ridgeSupport833_suffix_009
def ridgeSupport833_suffix_007 : List Nat := ridgeSupport833_007 ++ ridgeSupport833_suffix_008
def ridgeSupport833_suffix_006 : List Nat := ridgeSupport833_006 ++ ridgeSupport833_suffix_007
def ridgeSupport833_suffix_005 : List Nat := ridgeSupport833_005 ++ ridgeSupport833_suffix_006
def ridgeSupport833_suffix_004 : List Nat := ridgeSupport833_004 ++ ridgeSupport833_suffix_005
def ridgeSupport833_suffix_003 : List Nat := ridgeSupport833_003 ++ ridgeSupport833_suffix_004
def ridgeSupport833_suffix_002 : List Nat := ridgeSupport833_002 ++ ridgeSupport833_suffix_003
def ridgeSupport833_suffix_001 : List Nat := ridgeSupport833_001 ++ ridgeSupport833_suffix_002
def ridgeSupport833_suffix_000 : List Nat := ridgeSupport833_000 ++ ridgeSupport833_suffix_001
theorem ridgeSupport833_source : candidateRows 833 =
    (PackedRawNatGrowth.readList 14 291 ridgeSupport833_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
