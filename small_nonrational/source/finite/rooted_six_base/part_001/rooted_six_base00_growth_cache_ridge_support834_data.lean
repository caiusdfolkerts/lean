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
def ridgeSupport834_000 : List Nat := [325,326,327,749,750,751,905,906,907,989,990,991,1035,1036,1037,5902,5903,5904,5905,5906,5907,5998,5999,6000,6001,6002,6003,6094,6095,6096,6097,6098]
def ridgeSupport834_001 : List Nat := [6099,6454,6455,6456,6457,6458,6459,6502,6503,6504,6505,6506,6507,6646,6647,6648,6649,6650,6651,6904,6905,6906,6907,6908,6909,6934,6935,6936,6937,6938,6939,7414]
def ridgeSupport834_002 : List Nat := [7415,7416,7417,7418,7419,7462,7463,7464,7465,7466,7467,7606,7607,7608,7609,7610,7611,7864,7865,7866,7867,7868,7869,7894,7895,7896,7897,7898,7899,8806,8807,8808]
def ridgeSupport834_003 : List Nat := [8809,8810,8811,8854,8855,8856,8857,8858,8859,8998,8999,9000,9001,9002,9003,9532,9533,9534,9535,9536,9537,9544,9545,9546,9547,9548,9549,10228,10229,10230,10231,10232]
def ridgeSupport834_004 : List Nat := [10233,10240,10241,10242,10243,10244,10245,12520,12521,12534,12535,12540,12541,12547,12549,12557,12560,12563,12566,12568,12569,12582,12583,12588,12589,12667,12669,12677,12680,12683,12686,12715]
def ridgeSupport834_005 : List Nat := [12717,12725,12728,12731,12734,13003,13005,13013,13016,13019,13022,13024,13025,13038,13039,13044,13045,13072,13073,13086,13087,13092,13093,13171,13173,13181,13184,13187,13190,13198,13199,13200]
def ridgeSupport834_006 : List Nat := [13201,13202,13203,13420,13421,13422,13423,13424,13425,13450,13451,13452,13453,13454,13455,13771,13773,13781,13784,13787,13790,13792,13793,13806,13807,13812,13813,13840,13841,13854,13855,13860]
def ridgeSupport834_007 : List Nat := [13861,13939,13941,13949,13952,13955,13958,13966,13967,13968,13969,13970,13971,14188,14189,14190,14191,14192,14193,14218,14219,14220,14221,14222,14223,14827,14829,14837,14840,14843,14846,14848]
def ridgeSupport834_008 : List Nat := [14849,14862,14863,14868,14869,14896,14897,14910,14911,14916,14917,14995,14997,15005,15008,15011,15014,15022,15023,15024,15025,15026,15027,15496,15497,15498,15499,15500,15501,15508,15509,15510]
def ridgeSupport834_009 : List Nat := [15511,15512,15513,16024,16025,16026,16027,16028,16029,16036,16037,16038,16039,16040,16041,17719,17721,17726,17779,17781,17789,17792,17795,17798,17971,17973,17978,18067,18069,18077,18080,18083]
def ridgeSupport834_010 : List Nat := [18086,18244,18245,18246,18247,18248,18249,18451,18453,18458,18547,18549,18557,18560,18563,18566,18724,18725,18726,18727,18728,18729,19147,19149,19154,19243,19245,19253,19256,19259,19262,19564]
def ridgeSupport834_011 : List Nat := [19565,19566,19567,19568,19569,19912,19913,19914,19915,19916,19917,21352,21353,21366,21367,21372,21373,21426,21428,21436,21441,21442,21447,21522,21524,21532,21537,21538,21543,21642,21644,21652]
def ridgeSupport834_012 : List Nat := [21657,21658,21663]
def ridgeSupport834_code : Nat := 0x1527ea4d5499a9295232a455427a8455086a0e5414a8254f1e9e153c1a7794ed29d9537da6f94dde9bb5369a6d137366e64dcb9b9537266e44c7198e131be6374c6d98d92cfa59dcb38966b2cb6595cad2959b2b2e494c928924f249a492c924910d220e440487d90eb21ce40d481590271d263a447478e8d1d163a246a68d471a8234ec6958d2718ea31ac6338b0d160e2c0457d8aeb15ce29f45398a6efaa5f543ea77d4cfa95f523e9d7d38fa6df4d3e997d30f265e4c3c97792cf255e4a3c8d7918f22de453c897910eacdd593ab17560eabdd573aa67546ea81d4eba957526e915d223a3f747ce8c5d183a157428e83dd073a017400e7f9cfdb9f873eae7b5cf5b78f6f1cde35bc6378b6f14ddc5bb8376f6edcddb5bb636936d24da45b48368f6d1cda19b41b6806cfad9d5b39b6256c48d87db0f36116c20d7d5afa35ef6bdcd785af035de6bb6d761aeab5cd6b96d23da47348d6918d22da45347168e0d1bda37346d68d8ce4d9c933916720ce3d9c733866706ce019beb37566e6cc95992331f663ccc4598832f565e8cbbd97732e165c0cb7996db2d865aacb35965b1be6376c6e18dab1ad6356c6398c5b188630ac5f58bdb12d6258c49d89331196230c459889b110621ac415881b0fd61f8c3dd87b30e961d0a01540228035004a00540027f94ff09fdd3fb27f54fe895352a6254b4a9495252a425414a8094fd29f253d4a788cad195232946508c9d193229b45348a6514c2297452c89ad135226944d0899d1331edb3db47b64f6c1ed73dac7af4f5e1ebb3d747ae4f5c1dbb3b7476e4edc1db73b6c74ace951d293a50749ce931cfb39f473e4e7c1cf739ec6c6cd8d1b1936306c5cd8b1afd35f86becd7d1af935f067eccfd19f933f067dccfb196b32d465a4cb4196732cc64ecc9d1939327064dcc9b17d32fa45f44be817cf2f9c5dccbb917712ee05dbcbb717132e245c44b88170f2e1c1034206040b07be0f781ee838b07140e2417782ee05da051c0a30145
def ridgeSupport834_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport834_code
def ridgeSupport834_rest_001 : Nat := PackedRawNatGrowth.drop 480 ridgeSupport834_code
def ridgeSupport834_rest_002 : Nat := PackedRawNatGrowth.drop 960 ridgeSupport834_code
def ridgeSupport834_rest_003 : Nat := PackedRawNatGrowth.drop 1440 ridgeSupport834_code
def ridgeSupport834_rest_004 : Nat := PackedRawNatGrowth.drop 1920 ridgeSupport834_code
def ridgeSupport834_rest_005 : Nat := PackedRawNatGrowth.drop 2400 ridgeSupport834_code
def ridgeSupport834_rest_006 : Nat := PackedRawNatGrowth.drop 2880 ridgeSupport834_code
def ridgeSupport834_rest_007 : Nat := PackedRawNatGrowth.drop 3360 ridgeSupport834_code
def ridgeSupport834_rest_008 : Nat := PackedRawNatGrowth.drop 3840 ridgeSupport834_code
def ridgeSupport834_rest_009 : Nat := PackedRawNatGrowth.drop 4320 ridgeSupport834_code
def ridgeSupport834_rest_010 : Nat := PackedRawNatGrowth.drop 4800 ridgeSupport834_code
def ridgeSupport834_rest_011 : Nat := PackedRawNatGrowth.drop 5280 ridgeSupport834_code
def ridgeSupport834_rest_012 : Nat := PackedRawNatGrowth.drop 5760 ridgeSupport834_code
def ridgeSupport834_rest_013 : Nat := PackedRawNatGrowth.drop 5805 ridgeSupport834_code
def ridgeSupport834_suffix_013 : List Nat := []
def ridgeSupport834_suffix_012 : List Nat := ridgeSupport834_012 ++ ridgeSupport834_suffix_013
def ridgeSupport834_suffix_011 : List Nat := ridgeSupport834_011 ++ ridgeSupport834_suffix_012
def ridgeSupport834_suffix_010 : List Nat := ridgeSupport834_010 ++ ridgeSupport834_suffix_011
def ridgeSupport834_suffix_009 : List Nat := ridgeSupport834_009 ++ ridgeSupport834_suffix_010
def ridgeSupport834_suffix_008 : List Nat := ridgeSupport834_008 ++ ridgeSupport834_suffix_009
def ridgeSupport834_suffix_007 : List Nat := ridgeSupport834_007 ++ ridgeSupport834_suffix_008
def ridgeSupport834_suffix_006 : List Nat := ridgeSupport834_006 ++ ridgeSupport834_suffix_007
def ridgeSupport834_suffix_005 : List Nat := ridgeSupport834_005 ++ ridgeSupport834_suffix_006
def ridgeSupport834_suffix_004 : List Nat := ridgeSupport834_004 ++ ridgeSupport834_suffix_005
def ridgeSupport834_suffix_003 : List Nat := ridgeSupport834_003 ++ ridgeSupport834_suffix_004
def ridgeSupport834_suffix_002 : List Nat := ridgeSupport834_002 ++ ridgeSupport834_suffix_003
def ridgeSupport834_suffix_001 : List Nat := ridgeSupport834_001 ++ ridgeSupport834_suffix_002
def ridgeSupport834_suffix_000 : List Nat := ridgeSupport834_000 ++ ridgeSupport834_suffix_001
theorem ridgeSupport834_source : candidateRows 834 =
    (PackedRawNatGrowth.readList 15 387 ridgeSupport834_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase00
