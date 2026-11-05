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
def ridgeSupport833_000 : List Nat := [328,329,330,484,485,486,568,569,570,614,615,616,5926,5927,5928,5929,5930,5931,5974,5975,5976,5977,5978,5979,6118,6119,6120,6121,6122,6123,6190,6191]
def ridgeSupport833_001 : List Nat := [6192,6193,6194,6195,6238,6239,6240,6241,6242,6243,6382,6383,6384,6385,6386,6387,6916,6917,6918,6919,6920,6921,6928,6929,6930,6931,6932,6933,7150,7151,7152,7153]
def ridgeSupport833_002 : List Nat := [7154,7155,7198,7199,7200,7201,7202,7203,7342,7343,7344,7345,7346,7347,7876,7877,7878,7879,7880,7881,7888,7889,7890,7891,7892,7893,8572,8573,8574,8575,8576,8577]
def ridgeSupport833_003 : List Nat := [8584,8585,8586,8587,8588,8589,12523,12525,12533,12536,12539,12542,12544,12545,12558,12559,12564,12565,12592,12593,12606,12607,12612,12613,12691,12693,12701,12704,12707,12710,12718,12719]
def ridgeSupport833_004 : List Nat := [12720,12721,12722,12723,12763,12765,12773,12776,12779,12782,12784,12785,12798,12799,12804,12805,12832,12833,12846,12847,12852,12853,12931,12933,12941,12944,12947,12950,12958,12959,12960,12961]
def ridgeSupport833_005 : List Nat := [12962,12963,13432,13433,13434,13435,13436,13437,13444,13445,13446,13447,13448,13449,13531,13533,13541,13544,13547,13550,13552,13553,13566,13567,13572,13573,13600,13601,13614,13615,13620,13621]
def ridgeSupport833_006 : List Nat := [13699,13701,13709,13712,13715,13718,13726,13727,13728,13729,13730,13731,14200,14201,14202,14203,14204,14205,14212,14213,14214,14215,14216,14217,14728,14729,14730,14731,14732,14733,14740,14741]
def ridgeSupport833_007 : List Nat := [14742,14743,14744,14745,17707,17709,17714,17803,17805,17813,17816,17819,17822,17839,17841,17846,17935,17937,17945,17948,17951,17954,18256,18257,18258,18259,18260,18261,18319,18321,18326,18415]
def ridgeSupport833_008 : List Nat := [18417,18425,18428,18431,18434,18736,18737,18738,18739,18740,18741,19084,19085,19086,19087,19088,19089,21354,21356,21364,21369,21370,21375,21390,21392,21400,21405,21406,21411,21486,21488,21496]
def ridgeSupport833_009 : List Nat := [21501,21502,21507]
def ridgeSupport833_code : Nat := 0x1500e9ff53fda7f14fc29f753a3a73d4e769cc5390a71d4dfe9bd5379a6e94db29b54a9195212a3e5474a8d951924d649a4933926524c649848028fff1ff23fcc7f18fdf1e5a3c8c78f8eab1d523a9c7528ea31d42311461f8c391866308c60f8b6d16c62d7c59e8b3716622cac58d8b1714ca296c52b7332e661ccbb996732ae651cc6b98c7316e629cc4b9886f12de21bc3b7866f0ade11bbeb77c6ef6dde9bbcb7786b46d689ad0b5a06b3ed679acb35936b20d635ac2b5836a6ad4d1a97b52e6a42d481a82b50469fed3f9a78b4f069dcd3ada7434e569bad36da44b488690ed219a42b48468fad1f1a3db47a68f2d1e1951b2a26542ca8194fb29e652cca4d948328d650aca0d91ab234645ec8b9910b220640ac8118ffb1fe63e2c7c18f731eb63d0c7958eeb1db6366c6c98d8b1b0635ec6b98d331a36340c6758cab193628ac51189fb13e6262c4c188ab114621ec439880b10061fcc3ed87c30f561dac3ad0c6a18c431686290c4a188430286010bfa17e42fa85f0f6a9ed43da67b48f689ed03d927b20f639ec63d8a7b10e599cb2396272c0e579cae38467088e109c20383e7078df99bf237e26fc0df79bee362a6c50d899b1236226c40d849b08360e6c18d829b0431e663c8c7898f031de63b8c31986230c26180c2f985e306660c8c189830305e60b8bf597ea2fd25fa0bf397e62eb65d68bac97582eae5d58b95972a2e525ca0b93972604d0099c133023a047208e00f301e503c805280a48148
def ridgeSupport833_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport833_code
def ridgeSupport833_rest_001 : Nat := PackedRawNatGrowth.drop 480 ridgeSupport833_code
def ridgeSupport833_rest_002 : Nat := PackedRawNatGrowth.drop 960 ridgeSupport833_code
def ridgeSupport833_rest_003 : Nat := PackedRawNatGrowth.drop 1440 ridgeSupport833_code
def ridgeSupport833_rest_004 : Nat := PackedRawNatGrowth.drop 1920 ridgeSupport833_code
def ridgeSupport833_rest_005 : Nat := PackedRawNatGrowth.drop 2400 ridgeSupport833_code
def ridgeSupport833_rest_006 : Nat := PackedRawNatGrowth.drop 2880 ridgeSupport833_code
def ridgeSupport833_rest_007 : Nat := PackedRawNatGrowth.drop 3360 ridgeSupport833_code
def ridgeSupport833_rest_008 : Nat := PackedRawNatGrowth.drop 3840 ridgeSupport833_code
def ridgeSupport833_rest_009 : Nat := PackedRawNatGrowth.drop 4320 ridgeSupport833_code
def ridgeSupport833_rest_010 : Nat := PackedRawNatGrowth.drop 4365 ridgeSupport833_code
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
    (PackedRawNatGrowth.readList 15 291 ridgeSupport833_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase00
