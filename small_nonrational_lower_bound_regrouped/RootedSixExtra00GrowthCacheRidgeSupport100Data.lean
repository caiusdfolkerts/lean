module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public meta import CertificateNumbers
public import RootedSixExtra00GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport100_000 : List Nat := [65,75,85,86,87,1045,1046,1049,1050,1055,1057,1058,1061,1062,1067,1069,1070,1073,1074,1079,1201,1202,1205,1206,1211,1213,1214,1217,1218,1223,1225,1226]
def ridgeSupport100_001 : List Nat := [1229,1230,1235,1357,1358,1360,1361,1362,1363,1365,1366,1368,1369,1371,1372,1378,1379,1381,1382,1383,1384,1386,1387,1389,1390,1392,1393,1399,1400,1402,1403,1404]
def ridgeSupport100_002 : List Nat := [1405,1407,1408,1410,1411,1413,1414,5464,5465,5466,5467,5468,5469,5470,5471,5476,5477,5482,5483,5488,5489,5490,5491,5492,5493,5494,5495,5500,5501,5506,5507,5512]
def ridgeSupport100_003 : List Nat := [5513,5514,5515,5516,5517,5536,5537,5538,5539,5540,5541,5560,5561,5562,5563,5564,5565,5584,5585,5586,5587,5588,5589,5608,5609,5610,5611,5612,5613,5632,5633,5634]
def ridgeSupport100_004 : List Nat := [5635,5636,5637,5656,5657,5658,5659,5660,5661,5665,5667,5671,5673,5677,5679,5950,5951,5968,5969,5986,5987,5995,5997,6001,6003,6004,6005,6022,6023,6040,6041,6058]
def ridgeSupport100_005 : List Nat := [6059,6067,6069,6073,6075,6076,6077,6094,6095,6112,6113,6130,6131,6139,6141,6145,6147,6148,6149,6478,6479,6496,6497,6514,6515,6523,6525,6529,6531,6532,6533,6550]
def ridgeSupport100_006 : List Nat := [6551,6568,6569,6586,6587,6595,6597,6601,6603,6604,6605,6622,6623,6640,6641,6658,6659,6667,6669,6673,6675,6676,6677,7492,7493,7494,7495,7496,7497,8464,8465,8466]
def ridgeSupport100_007 : List Nat := [8467,8468,8469,8488,8489,8490,8491,8492,8493,8500,8501,8502,8503,8504,8505,8563,8565,8572,8573,8581,8583,8590,8591,8599,8601,8608,8609,8683,8685,8692,8693,8701]
cert_ridgeSupport_7 100 008 8703 8710 8711 8719 8721 8728 8729
cert_ridgeSupport_code_3 100
cert_ridgeSupport_rest_2 100 000 0
cert_ridgeSupport_rest_2 100 001 448
cert_ridgeSupport_rest_2 100 002 896
cert_ridgeSupport_rest_2 100 003 1344
cert_ridgeSupport_rest_2 100 004 1792
cert_ridgeSupport_rest_2 100 005 2240
cert_ridgeSupport_rest_2 100 006 2688
cert_ridgeSupport_rest_2 100 007 3136
cert_ridgeSupport_rest_2 100 008 3584
cert_ridgeSupport_rest_2 100 009 3682
cert_ridgeSupport_suffix_4 100 009
cert_ridgeSupport_suffix_3 100 008 009
cert_ridgeSupport_suffix_3 100 007 008
cert_ridgeSupport_suffix_3 100 006 007
cert_ridgeSupport_suffix_3 100 005 006
cert_ridgeSupport_suffix_3 100 004 005
cert_ridgeSupport_suffix_3 100 003 004
cert_ridgeSupport_suffix_3 100 002 003
cert_ridgeSupport_suffix_3 100 001 002
cert_ridgeSupport_suffix_3 100 000 001
cert_ridgeSupport_source_3 100 14 263
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
