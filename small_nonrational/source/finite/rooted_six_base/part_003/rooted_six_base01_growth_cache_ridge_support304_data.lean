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
def ridgeSupport304_000 : List Nat := [73,102,104,106,767,1131,1132,1134,1139,1141,1155,1156,1158,1163,1165,1178,1181,1183,1186,1188,1492,1493,1495,1496,1499,1500,1501,1503,1504,1506,1511,1512]
def ridgeSupport304_001 : List Nat := [1534,1536,1537,1539,1540,1542,1544,1545,1547,1548,1551,1552,1555,1557,1558,1560,1561,1563,1565,1566,1568,1569,1572,1573,6428,6429,6434,6435,6438,6439,6440,6441]
def ridgeSupport304_002 : List Nat := [6442,6443,6448,6449,6452,6453,6458,6459,6462,6463,6464,6465,6466,6467,6472,6473,6476,6477,6480,6481,6484,6485,6488,6489,6492,6493,6496,6497,6498,6503,6504,6509]
def ridgeSupport304_003 : List Nat := [6510,6511,6512,6513,6514,6515,6517,6519,6522,6527,6528,6533,6534,6535,6536,6537,6538,6539,6541,6543,6558,6559,6560,6561,6562,6563,6572,6573,6578,6579,6592,6593]
def ridgeSupport304_004 : List Nat := [6596,6597,6602,6603,6616,6617,6619,6620,6621,6622,6625,6626,6627,6628,6636,6638,6640,6641,6643,6644,6645,6646,6649,6650,6651,6652,6660,6662,6664,6665,6666,6671]
def ridgeSupport304_005 : List Nat := [6672,6677,6685,6687,6691,6693,6697,6699,6706,6707,6712,6713,6718,6719,6724,6725,6736,6737,6742,6743,6744,6746,6750,6752,6766,6767,6778,6779,6786,6788,6792,6794]
def ridgeSupport304_006 : List Nat := [6906,6911,6912,6917,6920,6921,6926,6927,6932,6933,6938,6939,6950,6951,6956,6957,6961,6964,6967,6970,6980,6981,6992,6993,7003,7006,7009,7012,7014,7019,7020,7025]
def ridgeSupport304_007 : List Nat := [7028,7029,7034,7035,7040,7041,7046,7047,7058,7059,7064,7065,7069,7072,7075,7078,7088,7089,7100,7101,7111,7114,7117,7120,7130,7132,7134,7137,7146,7148,7150,7153]
def ridgeSupport304_008 : List Nat := [7163,7165,7167,7168,11012,11013,11018,11019,11022,11023,11024,11025,11026,11027,11032,11033,11036,11037,11042,11043,11046,11047,11048,11049,11050,11051,11056,11057,11070,11071,11072,11073]
def ridgeSupport304_009 : List Nat := [11074,11075,11094,11095,11096,11097,11098,11099,11118,11119,11120,11121,11122,11123,11142,11143,11144,11145,11146,11147,11166,11167,11168,11169,11170,11171,11190,11191,11192,11193,11194,11195]
def ridgeSupport304_010 : List Nat := [11203,11206,11209,11212,11214,11215,11216,11217,11218,11219,11220,11222,11272,11273,11284,11285,11286,11288,11292,11294,11308,11309,11320,11321,11414,11415,11426,11427,11431,11434,11437,11440]
def ridgeSupport304_011 : List Nat := [11450,11451,11462,11463,11486,11487,11498,11499,11503,11506,11509,11512,11522,11523,11534,11535,11554,11558,11563,11565,11567,11569,11586,11590,11595,11597,11599,11601,11619,11623,11626,11628]
def ridgeSupport304_012 : List Nat := [11630,11632,14036,14037,14040,14041,14044,14045,14048,14049,14052,14053,14056,14057,14070,14071,14072,14073,14074,14075,14094,14095,14096,14097,14098,14099,14107,14110,14113,14116,14118,14119]
def ridgeSupport304_013 : List Nat := [14120,14121,14122,14123,14124,14126,14131,14134,14137,14140,14142,14143,14144,14145,14146,14147,14148,14150,14154,14156,14157,14159,14164,14165,14166,14168,14172,14174,14188,14189,14200,14201]
def ridgeSupport304_014 : List Nat := [14202,14204,14208,14210,14215,14217,14275,14278,14281,14284,14294,14295,14306,14307,14311,14314,14317,14320,14322,14327,14329,14332,14335,14338,14348,14349,14360,14361,14365,14368,14371,14374]
def ridgeSupport304_015 : List Nat := [14376,14381,14386,14388,14394,14396,14403,14405,14648,14649,14652,14653,14656,14657,14658,14660,14671,14674,14677,14680,15174,15175,15176,15177,15178,15179,15226,15234,15243]
def ridgeSupport304_code : Nat := 0x3b8bee0bb7aed2fb4aed27b48ed1fb46e563955e54b94fe513942e507940e4f793ce4e7938e117843e0f383ae0d3832e0b7828e09b823e08381de067818e03780ce00b7ffdff37f9dfdf7f2dfc37eddfab7e7df8f7e2df5f7d6df337c9df1b7c3de27787de0b780ddf377adde7778ddb776cdd7b75cdd63756dd57754dd3f74ddd3374add1b744dd0f742dd07740dcff73edcf3739dcdb733dcbb72cdcaf72adca7728dc9f726dc93721dc7b71bdc4f712dc47710dc3f70edbef6fadbe76f8dbdf6f6dba76e8db976e4db876e0db776dcdb676d8db576d4b5c2d6eb5b2d6ab59ed63b546d4fb536d4bb51ad42b4c6d2fb4b6d2bb49ad22b43ed0eb40ed02b3e2cf5b3cacefb3aeceab37ecdeb31ecc6b2eecbab2c2cadb2aaca7b28eca2b25ec96b0e6c38b0b6c2cb07ac1cb062c16b056c14b026c08af5abd4af4ebd2af46bd0af3ebceaf32bc9af1abc3aeeebbaaee6bb8aedebb6ae8eba2ae86ba0ae7eb9eae2eb8aae26b88ae1eb86adceb72adc6b70adbeb6ead6eb5aad66b58ad5eb56ad0eb42ad06b40acfeb3eacc6b30acaeb2aaca6b28ac9eb26ac8eb22ac76b1cac66b18ac4eb12ac46b10ac3eb0eac2eb0aac16b047001bff6ff5bfb6fc5bee6fb1bea6f85bde6f71bda6f41bcd6f29bc76ef5bbc6ec5bb06e99ba36e81b9d6e65b986e4db926e1db866e05b806dedb7a6dd5b746dc5b6c6dadb666d91b616d79b5b6d45b506d15b446ce9b376cd1b316cb5b2c6c9db266c6db1a6c55b146c3db0e6c25b086c15b006bfdafa6a29a886a11a8269eda7a69bda6e6981a5e6969a58695da566945a506915a4468fda3e68e5a3868cda3268ada296895a23687da1d6855a10683da0a6825a086819a0467f19fb67e99f967d99f567d19f367c59f067b99ec67919e367899e167799dd67719db67659d8672d9ca67159c467059c066cd9b266b59ac668d9a266859a0667d99e663d98d662d98a6625988661d986661598065fd97a65dd97565cd97265c597065bd96e65b5968659d9626585960657595c656595865559546545950653594c6525948650d942650594064fd93e64ed93a64d593464c593064ad92a64a5928649d926648d922647591c18946241884620187861d186c61918606161854613184060f183060b18246081818604180c60118005fe17a05e717885e0177c5dd17705db17605d717545d412904a2127c49d126848d122c486121048311d447311b846c11ac2ff01a80680198049
def ridgeSupport304_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport304_code
def ridgeSupport304_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport304_code
def ridgeSupport304_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport304_code
def ridgeSupport304_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport304_code
def ridgeSupport304_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport304_code
def ridgeSupport304_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport304_code
def ridgeSupport304_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport304_code
def ridgeSupport304_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport304_code
def ridgeSupport304_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport304_code
def ridgeSupport304_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport304_code
def ridgeSupport304_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport304_code
def ridgeSupport304_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport304_code
def ridgeSupport304_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport304_code
def ridgeSupport304_rest_013 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport304_code
def ridgeSupport304_rest_014 : Nat := PackedRawNatGrowth.drop 6272 ridgeSupport304_code
def ridgeSupport304_rest_015 : Nat := PackedRawNatGrowth.drop 6720 ridgeSupport304_code
def ridgeSupport304_rest_016 : Nat := PackedRawNatGrowth.drop 7126 ridgeSupport304_code
def ridgeSupport304_suffix_016 : List Nat := []
def ridgeSupport304_suffix_015 : List Nat := ridgeSupport304_015 ++ ridgeSupport304_suffix_016
def ridgeSupport304_suffix_014 : List Nat := ridgeSupport304_014 ++ ridgeSupport304_suffix_015
def ridgeSupport304_suffix_013 : List Nat := ridgeSupport304_013 ++ ridgeSupport304_suffix_014
def ridgeSupport304_suffix_012 : List Nat := ridgeSupport304_012 ++ ridgeSupport304_suffix_013
def ridgeSupport304_suffix_011 : List Nat := ridgeSupport304_011 ++ ridgeSupport304_suffix_012
def ridgeSupport304_suffix_010 : List Nat := ridgeSupport304_010 ++ ridgeSupport304_suffix_011
def ridgeSupport304_suffix_009 : List Nat := ridgeSupport304_009 ++ ridgeSupport304_suffix_010
def ridgeSupport304_suffix_008 : List Nat := ridgeSupport304_008 ++ ridgeSupport304_suffix_009
def ridgeSupport304_suffix_007 : List Nat := ridgeSupport304_007 ++ ridgeSupport304_suffix_008
def ridgeSupport304_suffix_006 : List Nat := ridgeSupport304_006 ++ ridgeSupport304_suffix_007
def ridgeSupport304_suffix_005 : List Nat := ridgeSupport304_005 ++ ridgeSupport304_suffix_006
def ridgeSupport304_suffix_004 : List Nat := ridgeSupport304_004 ++ ridgeSupport304_suffix_005
def ridgeSupport304_suffix_003 : List Nat := ridgeSupport304_003 ++ ridgeSupport304_suffix_004
def ridgeSupport304_suffix_002 : List Nat := ridgeSupport304_002 ++ ridgeSupport304_suffix_003
def ridgeSupport304_suffix_001 : List Nat := ridgeSupport304_001 ++ ridgeSupport304_suffix_002
def ridgeSupport304_suffix_000 : List Nat := ridgeSupport304_000 ++ ridgeSupport304_suffix_001
theorem ridgeSupport304_source : candidateRows 304 =
    (PackedRawNatGrowth.readList 14 509 ridgeSupport304_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
