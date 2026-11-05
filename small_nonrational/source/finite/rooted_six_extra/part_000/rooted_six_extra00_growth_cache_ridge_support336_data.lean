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
def ridgeSupport336_000 : List Nat := [56,80,100,116,121,123,635,636,637,638,645,646,791,792,793,794,801,802,935,937,939,941,943,948,949,951,954,977,978,982,984,985]
def ridgeSupport336_001 : List Nat := [989,991,992,994,1212,1213,1216,1217,1220,1221,1272,1274,1276,1278,1280,1285,1286,1288,1291,1314,1315,1319,1321,1322,1326,1328,1329,1331,1477,1478,1481,1482]
def ridgeSupport336_002 : List Nat := [1485,1486,1537,1539,1541,1543,1545,1550,1551,1553,1556,1579,1580,1584,1586,1587,1591,1593,1594,1596,1731,1733,1735,1736,1738,1740,1741,1745,1750,1774,1775,1776]
def ridgeSupport336_003 : List Nat := [1779,1780,1781,1783,1788,1790,1815,1817,1818,1820,1821,1823,1825,1826,1828,1829,1833,1834,4175,4177,4186,4191,4242,4243,4252,4253,4265,4268,4274,4275,4279,4281]
def ridgeSupport336_004 : List Nat := [4284,4285,4290,4291,4300,4301,4338,4339,4343,4345,4348,4349,4354,4359,4370,4371,4380,4381,4394,4395,4404,4405,4415,4417,4426,4431,4482,4483,4492,4493,4505,4508]
def ridgeSupport336_005 : List Nat := [4514,4515,4519,4521,4524,4525,4530,4531,4540,4541,4578,4579,4583,4585,4588,4589,4594,4599,4610,4611,4620,4621,4634,4635,4644,4645,4654,4659,4666,4671,4686,4687]
def ridgeSupport336_006 : List Nat := [4698,4699,4799,4801,4811,4813,4832,4833,4844,4845,4943,4945,4954,4959,5010,5011,5020,5021,5033,5036,5042,5043,5047,5049,5052,5053,5058,5059,5068,5069,5106,5107]
def ridgeSupport336_007 : List Nat := [5111,5113,5116,5117,5122,5127,5138,5139,5148,5149,5162,5163,5172,5173,5182,5187,5194,5199,5214,5215,5226,5227,5327,5329,5339,5341,5360,5361,5372,5373,6263,6265]
def ridgeSupport336_008 : List Nat := [6274,6279,6282,6283,6292,6293,6330,6331,6340,6341,6353,6356,6362,6363,6367,6369,6372,6373,6378,6379,6383,6385,6388,6389,6394,6399,6426,6427,6436,6437,6450,6451]
def ridgeSupport336_009 : List Nat := [6460,6461,6472,6477,6502,6507,6516,6517,6534,6535,6617,6619,6647,6649,6662,6663,6680,6681,6760,6765,6790,6795,6804,6805,6822,6823,6905,6907,6935,6937,6950,6951]
def ridgeSupport336_010 : List Nat := [6968,6969,7368,7369,7404,7405,7464,7465,7614,7615,8178,8179,8188,8189,8202,8203,8206,8208,8209,8210,8226,8227,8236,8237,8250,8251,8254,8256,8257,8258,8273,8274]
def ridgeSupport336_011 : List Nat := [8275,8276,8308,8310,8312,8313,8346,8347,8356,8357,8370,8371,8374,8376,8377,8378,8393,8394,8395,8396,8428,8430,8432,8433,8633,8636,8647,8649,8670,8671,8674,8676]
def ridgeSupport336_012 : List Nat := [8677,8678,8687,8688,8689,8690,8722,8724,8726,8727,8759,8760,8761,8762,8794,8796,8798,8799]
def ridgeSupport336_code : Nat := 0x897e25e897225a88ea23988e2237885e216885221287ca1f187c21ef879a1e587921e2877e1de87261c786f21b983c60f083ba0ec83320cb832a0c982ea0b982e20b682ce0b282960a4826e09a81e607881da0748152053814a051810a041810203e80ee03a80b602c808e022804a011804200e802e00a7ff5ffc7fcdff276fddbe74a5d2873b5cec7325cc86ce5b386c9db266c65b176bedaf96a9daa66a55a946a2da8669b5a686865a18681da0667e59f7676d9d9661d98665d597465ad966653594864f593c64cd9326495924646d91a63fd8fa63d58f463c58ef63ad8ea63958e463858df636d8da63518d163158c462ed8ba6255894622d88a621d88261e587753f54fc53c54f053754db53454cf51ad46a517d45e513d44a510d43e50d543450ad42a507541c504d412501d4024ff53fc4fe53f74fcd3f24f353cc4f0d3c24ef53bc4ee53b74ecd3b24eb13a94e7539c4e4d3924d7d35a4d4534f4bb52ec4b852e04b352cb4b052bf496d25a493d24e48fd23a48cd22e4895224486d21a483520c480d20247dd1f247b51ec47a51e7478d1e246f51bc46cd1b246b51ac46a51a7468d1a24671199463518c460d182453d14a450513f44d513444ad12a447511c444d112441d10243f50fc43e50f743cd0f243350cc430d0c242f50bc42e50b742cd0b242b10a9427509c424d092417d05a414504f1ca87291c947241c887211c7c71d1c7071a1c647171bf86fc1bdc6f51bd06f31bc06ef1bb86d61b446cd1b306ca1b206c71b146c318f063a18e463718cc63218c062c18ac614184460f1838609181c605180c60117385cd17285c917185c514cc53114c052e14a8529149c523148850b1420506141450013f84fc13e84f813144c413044c012f44bc0f883e00f7c3dd0f643d80f583d20f443ba0edc3b50ed03af0eb43ab0ea43a70c883210c683190c603170a1828509f827d09f027b01ec07901d00640140038
def ridgeSupport336_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport336_code
def ridgeSupport336_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport336_code
def ridgeSupport336_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport336_code
def ridgeSupport336_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport336_code
def ridgeSupport336_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport336_code
def ridgeSupport336_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport336_code
def ridgeSupport336_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport336_code
def ridgeSupport336_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport336_code
def ridgeSupport336_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport336_code
def ridgeSupport336_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport336_code
def ridgeSupport336_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport336_code
def ridgeSupport336_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport336_code
def ridgeSupport336_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport336_code
def ridgeSupport336_rest_013 : Nat := PackedRawNatGrowth.drop 5628 ridgeSupport336_code
def ridgeSupport336_suffix_013 : List Nat := []
def ridgeSupport336_suffix_012 : List Nat := ridgeSupport336_012 ++ ridgeSupport336_suffix_013
def ridgeSupport336_suffix_011 : List Nat := ridgeSupport336_011 ++ ridgeSupport336_suffix_012
def ridgeSupport336_suffix_010 : List Nat := ridgeSupport336_010 ++ ridgeSupport336_suffix_011
def ridgeSupport336_suffix_009 : List Nat := ridgeSupport336_009 ++ ridgeSupport336_suffix_010
def ridgeSupport336_suffix_008 : List Nat := ridgeSupport336_008 ++ ridgeSupport336_suffix_009
def ridgeSupport336_suffix_007 : List Nat := ridgeSupport336_007 ++ ridgeSupport336_suffix_008
def ridgeSupport336_suffix_006 : List Nat := ridgeSupport336_006 ++ ridgeSupport336_suffix_007
def ridgeSupport336_suffix_005 : List Nat := ridgeSupport336_005 ++ ridgeSupport336_suffix_006
def ridgeSupport336_suffix_004 : List Nat := ridgeSupport336_004 ++ ridgeSupport336_suffix_005
def ridgeSupport336_suffix_003 : List Nat := ridgeSupport336_003 ++ ridgeSupport336_suffix_004
def ridgeSupport336_suffix_002 : List Nat := ridgeSupport336_002 ++ ridgeSupport336_suffix_003
def ridgeSupport336_suffix_001 : List Nat := ridgeSupport336_001 ++ ridgeSupport336_suffix_002
def ridgeSupport336_suffix_000 : List Nat := ridgeSupport336_000 ++ ridgeSupport336_suffix_001
theorem ridgeSupport336_source : candidateSupports 336 =
    (PackedRawNatGrowth.readList 14 402 ridgeSupport336_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
