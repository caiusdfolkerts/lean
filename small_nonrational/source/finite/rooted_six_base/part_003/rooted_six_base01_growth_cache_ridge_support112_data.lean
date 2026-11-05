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
def ridgeSupport112_000 : List Nat := [71,101,102,103,765,1118,1121,1123,1126,1128,1130,1133,1135,1138,1140,1142,1145,1147,1150,1152,1493,1494,1496,1497,1498,1499,1501,1502,1504,1505,1507,1508]
def ridgeSupport112_001 : List Nat := [1514,1515,1517,1518,1519,1520,1522,1523,1525,1526,1528,1529,1535,1536,1538,1539,1540,1541,1543,1544,1546,1547,1549,1550,6426,6427,6428,6429,6430,6431,6432,6433]
def ridgeSupport112_002 : List Nat := [6438,6439,6444,6445,6450,6451,6452,6453,6454,6455,6456,6457,6462,6463,6468,6469,6474,6475,6476,6477,6478,6479,6486,6487,6488,6489,6490,6491,6498,6499,6500,6501]
def ridgeSupport112_003 : List Nat := [6502,6503,6506,6508,6512,6514,6518,6520,6522,6523,6524,6525,6526,6527,6530,6532,6536,6538,6542,6544,6546,6547,6548,6549,6550,6551,6576,6577,6582,6583,6588,6589]
def ridgeSupport112_004 : List Nat := [6600,6601,6606,6607,6612,6613,6624,6625,6627,6629,6630,6631,6633,6635,6636,6637,6639,6641,6648,6649,6651,6653,6654,6655,6657,6659,6660,6661,6663,6665,6674,6676]
def ridgeSupport112_005 : List Nat := [6680,6682,6686,6688,6692,6694,6698,6700,6702,6703,6708,6709,6714,6715,6720,6721,6732,6733,6738,6739,6747,6749,6753,6755,6762,6763,6774,6775,6789,6791,6795,6797]
def ridgeSupport112_006 : List Nat := [6800,6802,6806,6808,6810,6811,6816,6817,6822,6823,6828,6829,6840,6841,6846,6847,6855,6857,6861,6863,6870,6871,6882,6883,6897,6899,6903,6905,6908,6910,6914,6916]
def ridgeSupport112_007 : List Nat := [6918,6919,6924,6925,6930,6931,6936,6937,6948,6949,6954,6955,6963,6965,6969,6971,6978,6979,6990,6991,7005,7007,7011,7013,7123,7125,7127,7128,7131,7133,7135,7136]
def ridgeSupport112_008 : List Nat := [7139,7141,7143,7144,11010,11011,11012,11013,11014,11015,11016,11017,11022,11023,11028,11029,11034,11035,11036,11037,11038,11039,11040,11041,11046,11047,11052,11053,11058,11059,11060,11061]
def ridgeSupport112_009 : List Nat := [11062,11063,11082,11083,11084,11085,11086,11087,11106,11107,11108,11109,11110,11111,11130,11131,11132,11133,11134,11135,11154,11155,11156,11157,11158,11159,11178,11179,11180,11181,11182,11183]
def ridgeSupport112_010 : List Nat := [11202,11203,11204,11205,11206,11207,11211,11213,11217,11219,11223,11225,11268,11269,11280,11281,11289,11291,11295,11297,11304,11305,11316,11317,11340,11341,11352,11353,11361,11363,11367,11369]
def ridgeSupport112_011 : List Nat := [11376,11377,11388,11389,11412,11413,11424,11425,11433,11435,11439,11441,11448,11449,11460,11461,11539,11543,11546,11548,11550,11552,11555,11559,11562,11564,11566,11568,11571,11575,11578,11580]
def ridgeSupport112_012 : List Nat := [11582,11584,14034,14035,14036,14037,14038,14039,14046,14047,14048,14049,14050,14051,14058,14059,14060,14061,14062,14063,14082,14083,14084,14085,14086,14087,14106,14107,14108,14109,14110,14111]
def ridgeSupport112_013 : List Nat := [14115,14117,14121,14123,14127,14129,14130,14131,14132,14133,14134,14135,14139,14141,14145,14147,14151,14153,14157,14158,14160,14161,14163,14164,14169,14171,14175,14177,14184,14185,14196,14197]
def ridgeSupport112_014 : List Nat := [14205,14207,14211,14213,14216,14218,14223,14225,14229,14231,14238,14239,14250,14251,14259,14261,14265,14267,14270,14272,14277,14279,14283,14285,14292,14293,14304,14305,14313,14315,14319,14321]
def ridgeSupport112_015 : List Nat := [14324,14326,14383,14385,14387,14389,14391,14393,14646,14647,14648,14649,14650,14651,14661,14663,14667,14669,14673,14675,15162,15163,15164,15165,15166,15167,15223,15227,15231]
def ridgeSupport112_code : Nat := 0x3b7fedefb77ecffb3eecf7b3cecefb3ae54f951e53794be51f945e4ef93ae4e7938e4df936e0e7837e0d7833e0c782fdfdb7f4dfc77efdfaf7e9df877e0df577d4df377cbdf1f7c5df037bedeef7b9ded77b3deaf7aade7f79ede5f795de4778fde2b788de17783ddff77dddd7774dda7768dd8775fdd6f759dd53753dd47750dd3b74ddd27747dd0f741dcf773bdcdf736dcd7734dccf732dcc772fdcaf729dc97723dc7f71edc7771cdc6f71adc1f706dc17704dc0f702dbbf6eedbb76ecdbaf6eadb8f6e2db876e0db7f6dedb5f6d6db576d4db4f6d2b502d3eb4f2d3ab4ded33b4c2d2eb4b2d2ab49ed23b482d1eb472d1ab45ed13b316cc4b2e6cb8b2c6cafb2aeca9b286ca0b256c94b1f6c7cb1c6c70b1a6c67b18ec61b166c58b136c4cb0d6c34b0a6c28b086c1fb06ec19b046c10b016c04af66bd7af4ebd1af36bcbaf1ebc6af16bc4af0ebc2aebebaeaeb6bacaeaebaaae5eb96ae56b94ae4eb92adfeb7eadf6b7cadeeb7aad9eb66ad96b64ad8eb62ad3eb4ead36b4cad2eb4aacdeb36acd6b34acceb32acb6b2cac9eb26ac86b20ac7eb1eac76b1cac6eb1aac56b14ac3eb0eac26b08ac1eb06ac16b04ac0eb026fa1be76f95be36f81bdf6f75bdb6f61bd76f55bd36d95b636d7db5d6d3db4e6d0db426cedb396cd5b336cadb2a6c95b246c65b186c4db126c35b0c6c1db066c11b026bf9afc6be5af76bcdaf16b8dae26b5dad66b3dacd6b25ac76afdabe6ae5ab86ab5aac6a9daa66a85aa06a6da9a6a61a966a49a906a35a8b6a1da8569dda7669ada6a698da616975a5b694da526935a4c6905a4068eda3a68d5a3468bda2e68b1a2a6899a246881a1e6869a186851a126825a076815a04680da0167fd9fe67f59fb67e59f867c59ef67b59ec67ad9e9679d9e667959e367859e067559d4673d9ce67259c866f59bc66dd9b666c59b0665d9966655994664d992664198e6629988661198265fd97e65f597c65ed97a65e197665c997065b196a659d9666595964658d962656d95a6565958655d956653d94e653594c652d94a651594464fd93e64e593864dd93664d593464cd93264b592c649d9266485920647d91e647591c646d91a183860d182c60a18206071814604180c60218005ff17e45f817d85f517cc5f217c05ef17b85ed17ac5ea17905e317845e017785dd176c5da17645d817585d5120047e11ec47911d847411c846f11b446a11a0466118c46111782fd019c0660194047
def ridgeSupport112_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport112_code
def ridgeSupport112_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport112_code
def ridgeSupport112_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport112_code
def ridgeSupport112_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport112_code
def ridgeSupport112_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport112_code
def ridgeSupport112_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport112_code
def ridgeSupport112_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport112_code
def ridgeSupport112_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport112_code
def ridgeSupport112_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport112_code
def ridgeSupport112_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport112_code
def ridgeSupport112_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport112_code
def ridgeSupport112_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport112_code
def ridgeSupport112_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport112_code
def ridgeSupport112_rest_013 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport112_code
def ridgeSupport112_rest_014 : Nat := PackedRawNatGrowth.drop 6272 ridgeSupport112_code
def ridgeSupport112_rest_015 : Nat := PackedRawNatGrowth.drop 6720 ridgeSupport112_code
def ridgeSupport112_rest_016 : Nat := PackedRawNatGrowth.drop 7126 ridgeSupport112_code
def ridgeSupport112_suffix_016 : List Nat := []
def ridgeSupport112_suffix_015 : List Nat := ridgeSupport112_015 ++ ridgeSupport112_suffix_016
def ridgeSupport112_suffix_014 : List Nat := ridgeSupport112_014 ++ ridgeSupport112_suffix_015
def ridgeSupport112_suffix_013 : List Nat := ridgeSupport112_013 ++ ridgeSupport112_suffix_014
def ridgeSupport112_suffix_012 : List Nat := ridgeSupport112_012 ++ ridgeSupport112_suffix_013
def ridgeSupport112_suffix_011 : List Nat := ridgeSupport112_011 ++ ridgeSupport112_suffix_012
def ridgeSupport112_suffix_010 : List Nat := ridgeSupport112_010 ++ ridgeSupport112_suffix_011
def ridgeSupport112_suffix_009 : List Nat := ridgeSupport112_009 ++ ridgeSupport112_suffix_010
def ridgeSupport112_suffix_008 : List Nat := ridgeSupport112_008 ++ ridgeSupport112_suffix_009
def ridgeSupport112_suffix_007 : List Nat := ridgeSupport112_007 ++ ridgeSupport112_suffix_008
def ridgeSupport112_suffix_006 : List Nat := ridgeSupport112_006 ++ ridgeSupport112_suffix_007
def ridgeSupport112_suffix_005 : List Nat := ridgeSupport112_005 ++ ridgeSupport112_suffix_006
def ridgeSupport112_suffix_004 : List Nat := ridgeSupport112_004 ++ ridgeSupport112_suffix_005
def ridgeSupport112_suffix_003 : List Nat := ridgeSupport112_003 ++ ridgeSupport112_suffix_004
def ridgeSupport112_suffix_002 : List Nat := ridgeSupport112_002 ++ ridgeSupport112_suffix_003
def ridgeSupport112_suffix_001 : List Nat := ridgeSupport112_001 ++ ridgeSupport112_suffix_002
def ridgeSupport112_suffix_000 : List Nat := ridgeSupport112_000 ++ ridgeSupport112_suffix_001
theorem ridgeSupport112_source : candidateRows 112 =
    (PackedRawNatGrowth.readList 14 509 ridgeSupport112_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
