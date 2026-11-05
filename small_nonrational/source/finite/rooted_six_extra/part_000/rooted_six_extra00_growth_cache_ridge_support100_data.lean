module
prelude
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
def ridgeSupport100_008 : List Nat := [8703,8710,8711,8719,8721,8728,8729]
def ridgeSupport100_code : Nat := 0x22198862211883e207881a1ff87f61f587d21ed87ae1a18682199865e18f863a187861617d85f217585ce13984e213784da13584d212d84b212b84aa12984a21158452113844a1118441d497521d477519d457511a156851a136845a0d682da0368099f167c19df67799cd67319cb67259c5670d9bb66e99a966a199766599856611983660597d65ed97365c9961658194f6539805601180360057fd5fed7f35fc97e15f817cf5f397bd5ef17bb5ee57b55ecd7ab5ea97995e617875e197755dd17735dc576d5dad7635d897515d4173f5cf962f58b5629589d623588561d587161b586961958616055811603580960158015ed57b15eb57a95e957a15d557515d357495d157415bd56f15bb56e95b956e15a556915a356895a1568158d563158b56295895621583560957d55f157755d957555d157355c957155c156b55a9565559155f557955d557155b556955955605861614583160858015fc57d15f057b15e857815dc57115c056e15b456b15a8568159c5661594563158855c156c559156055615545531548551154054e15344d313384cd13284c9131c4c213044be12f44bb12d84b512c84b110dc43210c442e10b442b10984251088421107c41a106441610540570158055012c041
def ridgeSupport100_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport100_code
def ridgeSupport100_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport100_code
def ridgeSupport100_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport100_code
def ridgeSupport100_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport100_code
def ridgeSupport100_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport100_code
def ridgeSupport100_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport100_code
def ridgeSupport100_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport100_code
def ridgeSupport100_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport100_code
def ridgeSupport100_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport100_code
def ridgeSupport100_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport100_code
def ridgeSupport100_suffix_009 : List Nat := []
def ridgeSupport100_suffix_008 : List Nat := ridgeSupport100_008 ++ ridgeSupport100_suffix_009
def ridgeSupport100_suffix_007 : List Nat := ridgeSupport100_007 ++ ridgeSupport100_suffix_008
def ridgeSupport100_suffix_006 : List Nat := ridgeSupport100_006 ++ ridgeSupport100_suffix_007
def ridgeSupport100_suffix_005 : List Nat := ridgeSupport100_005 ++ ridgeSupport100_suffix_006
def ridgeSupport100_suffix_004 : List Nat := ridgeSupport100_004 ++ ridgeSupport100_suffix_005
def ridgeSupport100_suffix_003 : List Nat := ridgeSupport100_003 ++ ridgeSupport100_suffix_004
def ridgeSupport100_suffix_002 : List Nat := ridgeSupport100_002 ++ ridgeSupport100_suffix_003
def ridgeSupport100_suffix_001 : List Nat := ridgeSupport100_001 ++ ridgeSupport100_suffix_002
def ridgeSupport100_suffix_000 : List Nat := ridgeSupport100_000 ++ ridgeSupport100_suffix_001
theorem ridgeSupport100_source : candidateSupports 100 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport100_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
