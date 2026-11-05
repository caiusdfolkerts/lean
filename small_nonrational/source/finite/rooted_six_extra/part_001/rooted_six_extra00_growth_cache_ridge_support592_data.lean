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
def ridgeSupport592_000 : List Nat := [57,81,101,117,122,123,647,648,649,650,657,658,803,804,805,806,813,814,956,958,960,962,964,969,970,972,975,977,979,981,983,985]
def ridgeSupport592_001 : List Nat := [990,991,993,996,1224,1225,1228,1229,1232,1233,1293,1295,1297,1299,1301,1306,1307,1309,1312,1314,1316,1318,1320,1322,1327,1328,1330,1333,1489,1490,1493,1494]
def ridgeSupport592_002 : List Nat := [1497,1498,1558,1560,1562,1564,1566,1571,1572,1574,1577,1579,1581,1583,1585,1587,1592,1593,1595,1598,1752,1754,1756,1757,1759,1761,1762,1766,1771,1773,1775,1777]
def ridgeSupport592_003 : List Nat := [1778,1780,1782,1783,1787,1792,1815,1816,1818,1819,1822,1823,1824,1826,1827,1829,1836,1837,4174,4179,4180,4185,4244,4245,4258,4259,4264,4266,4272,4273,4278,4279]
def ridgeSupport592_004 : List Nat := [4285,4287,4292,4293,4306,4307,4340,4341,4342,4347,4348,4353,4354,4355,4368,4369,4374,4375,4392,4393,4398,4399,4414,4419,4420,4425,4484,4485,4498,4499,4504,4506]
def ridgeSupport592_005 : List Nat := [4512,4513,4518,4519,4525,4527,4532,4533,4546,4547,4580,4581,4582,4587,4588,4593,4594,4595,4608,4609,4614,4615,4632,4633,4638,4639,4726,4731,4738,4743,4758,4759]
def ridgeSupport592_006 : List Nat := [4770,4771,4798,4803,4810,4815,4830,4831,4842,4843,4942,4947,4948,4953,5012,5013,5026,5027,5032,5034,5040,5041,5046,5047,5053,5055,5060,5061,5074,5075,5108,5109]
def ridgeSupport592_007 : List Nat := [5110,5115,5116,5121,5122,5123,5136,5137,5142,5143,5160,5161,5166,5167,5254,5259,5266,5271,5286,5287,5298,5299,5326,5331,5338,5343,5358,5359,5370,5371,6262,6267]
def ridgeSupport592_008 : List Nat := [6268,6273,6284,6285,6298,6299,6332,6333,6346,6347,6352,6354,6360,6361,6366,6367,6373,6375,6380,6381,6382,6387,6388,6393,6394,6395,6428,6429,6442,6443,6452,6453]
def ridgeSupport592_009 : List Nat := [6466,6467,6544,6549,6574,6579,6588,6589,6606,6607,6616,6621,6646,6651,6660,6661,6678,6679,6832,6837,6862,6867,6876,6877,6894,6895,6904,6909,6934,6939,6948,6949]
def ridgeSupport592_010 : List Nat := [6966,6967,7366,7367,7402,7403,7462,7463,7616,7617,8180,8181,8194,8195,8204,8205,8207,8208,8209,8211,8228,8229,8242,8243,8252,8253,8255,8256,8257,8259,8291,8292]
def ridgeSupport592_011 : List Nat := [8293,8294,8309,8310,8311,8312,8348,8349,8362,8363,8372,8373,8375,8376,8377,8379,8411,8412,8413,8414,8429,8430,8431,8432,8632,8634,8653,8655,8672,8673,8675,8676]
def ridgeSupport592_012 : List Nat := [8677,8679,8705,8706,8707,8708,8723,8724,8725,8726,8777,8778,8779,8780,8795,8796,8797,8798]
def ridgeSupport592_code : Nat := 0x897a25d897225b893224b892a249885a21588522138812203880a201879e1e587921e387861e0873e1cd86ea1b883c20ef83ba0ed837a0dd83720db82ee0b982e20b782d60b482ae0aa827609c81e207781da075819a0658192063810e041810203f80f603c80ce0328096024804e011804200f803600c800e0027fd5ff47705dc0749dd2673adcea731dcc66cddb366c95b246c6db166bf5af86bbdaee6b75adc6b4dace6ad5ab0685da166815a0467ed9f667759d8673d9ce66f59bc66cd9ae6655990650d94264d593464ad92a647591c63ed8fa63e58f463cd8ee63b58ec639d8e5637d8de63658d863498d0632d8ca62f58bc626d89a623588c620587c61ed87653ed4fa53bd4ee537d4da534d4ce52cd4b2529d4a6525d492522d48650bd42e50a5428505d4165045410500d40250053fc4fed3f64fd53f44f4d3d24f153c44efd3bd4edd3b64ec53b04ea93a84e8d3a24e553944d653544d4d34e4bad2ea4b7d2de4b3d2ca4b0d2be4a8d2a24a5d2964a1d28249ed276487d21e4865218481d206480520047cd1f247c51ec47ad1e647951e4470d1c246d51b446bd1ad469d1a646851a04669198464d19246151844525144450d13e44bd12e44a5128445d1164445110440d10244050fc43ed0f643d50f4434d0d243150c442fd0bd42dd0b642c50b042a90a8428d0a242550944165054414d04e1cb472c1c947231c887201c7c71e1c6c71a1c607171c006fb1bdc6f61bd06f21bc46ef1bb46eb1b986e21b846df1b746dc1b686d818f863b18e463818cc63118bc62d18ac6291898624188c61e187061a186061617685d917585d517485d114d453214c052f14a852814985241488520147451b1468515144c511143c50d13444d013344cc13244c80f903e10f7c3de0f643d70f543d30f443cf0f303ca0f243c40f083c00ef83bc0cb832d0c983250c903230a482910a282890a2028701ec07a01d40650144039
def ridgeSupport592_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport592_code
def ridgeSupport592_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport592_code
def ridgeSupport592_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport592_code
def ridgeSupport592_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport592_code
def ridgeSupport592_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport592_code
def ridgeSupport592_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport592_code
def ridgeSupport592_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport592_code
def ridgeSupport592_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport592_code
def ridgeSupport592_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport592_code
def ridgeSupport592_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport592_code
def ridgeSupport592_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport592_code
def ridgeSupport592_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport592_code
def ridgeSupport592_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport592_code
def ridgeSupport592_rest_013 : Nat := PackedRawNatGrowth.drop 5628 ridgeSupport592_code
def ridgeSupport592_suffix_013 : List Nat := []
def ridgeSupport592_suffix_012 : List Nat := ridgeSupport592_012 ++ ridgeSupport592_suffix_013
def ridgeSupport592_suffix_011 : List Nat := ridgeSupport592_011 ++ ridgeSupport592_suffix_012
def ridgeSupport592_suffix_010 : List Nat := ridgeSupport592_010 ++ ridgeSupport592_suffix_011
def ridgeSupport592_suffix_009 : List Nat := ridgeSupport592_009 ++ ridgeSupport592_suffix_010
def ridgeSupport592_suffix_008 : List Nat := ridgeSupport592_008 ++ ridgeSupport592_suffix_009
def ridgeSupport592_suffix_007 : List Nat := ridgeSupport592_007 ++ ridgeSupport592_suffix_008
def ridgeSupport592_suffix_006 : List Nat := ridgeSupport592_006 ++ ridgeSupport592_suffix_007
def ridgeSupport592_suffix_005 : List Nat := ridgeSupport592_005 ++ ridgeSupport592_suffix_006
def ridgeSupport592_suffix_004 : List Nat := ridgeSupport592_004 ++ ridgeSupport592_suffix_005
def ridgeSupport592_suffix_003 : List Nat := ridgeSupport592_003 ++ ridgeSupport592_suffix_004
def ridgeSupport592_suffix_002 : List Nat := ridgeSupport592_002 ++ ridgeSupport592_suffix_003
def ridgeSupport592_suffix_001 : List Nat := ridgeSupport592_001 ++ ridgeSupport592_suffix_002
def ridgeSupport592_suffix_000 : List Nat := ridgeSupport592_000 ++ ridgeSupport592_suffix_001
theorem ridgeSupport592_source : candidateSupports 592 =
    (PackedRawNatGrowth.readList 14 402 ridgeSupport592_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
