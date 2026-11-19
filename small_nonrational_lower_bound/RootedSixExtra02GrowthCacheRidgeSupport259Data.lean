module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public meta import CertificateNumbers
public import RootedSixExtra02GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport259_000 : List Nat := [3,7,10,12,14,114,116,119,120,122,138,140,143,144,146,163,165,166,169,171,186,188,191,192,194,210,212,215,216,218,235,237]
def ridgeSupport259_001 : List Nat := [238,241,243,246,247,249,250,253,254,255,257,258,260,265,266,288,290,291,293,294,296,298,299,301,302,305,306,309,311,312,314,315]
def ridgeSupport259_002 : List Nat := [317,319,320,322,323,326,327,1390,1391,1396,1397,1400,1401,1402,1403,1404,1405,1410,1411,1414,1415,1420,1421,1424,1425,1426,1427,1428,1429,1434,1435,1448]
def ridgeSupport259_003 : List Nat := [1449,1450,1451,1452,1453,1472,1473,1474,1475,1476,1477,1496,1497,1498,1499,1500,1501,1520,1521,1522,1523,1524,1525,1544,1545,1546,1547,1548,1549,1568,1569,1570]
def ridgeSupport259_004 : List Nat := [1571,1572,1573,1581,1584,1587,1590,1592,1593,1594,1595,1596,1597,1598,1600,2112,2113,2124,2125,2148,2149,2160,2161,2168,2170,2174,2176,2254,2255,2266,2267,2290]
def ridgeSupport259_005 : List Nat := [2291,2302,2303,2313,2316,2319,2322,2326,2327,2338,2339,2362,2363,2374,2375,2385,2388,2391,2394,2880,2881,2892,2893,2916,2917,2928,2929,2936,2938,2942,2944,3022]
def ridgeSupport259_006 : List Nat := [3023,3034,3035,3058,3059,3070,3071,3081,3084,3087,3090,3094,3095,3106,3107,3130,3131,3142,3143,3153,3156,3159,3162,5134,5135,5138,5139,5142,5143,5172,5173,5182]
def ridgeSupport259_007 : List Nat := [5183,5188,5189,5220,5221,5230,5231,5236,5237,5360,5361,5362,5363,5364,5365,5864,5865,5866,5867,5868,5869,5877,5880,5883,5885,5886,5887,5889,5892,5895,5897,5898]
def ridgeSupport259_008 : List Nat := [5899,6002,6004,6008,6010,6039,6042,6045,6048,6057,6060,6063,6066,6170,6172,6176,6178,6207,6210,6213,6216,6225,6228,6231,6234]
cert_ridgeSupport_code_3 259
cert_ridgeSupport_rest_2 259 000 0
cert_ridgeSupport_rest_2 259 001 416
cert_ridgeSupport_rest_2 259 002 832
cert_ridgeSupport_rest_2 259 003 1248
cert_ridgeSupport_rest_2 259 004 1664
cert_ridgeSupport_rest_2 259 005 2080
cert_ridgeSupport_rest_2 259 006 2496
cert_ridgeSupport_rest_2 259 007 2912
cert_ridgeSupport_rest_2 259 008 3328
cert_ridgeSupport_rest_2 259 009 3653
cert_ridgeSupport_suffix_4 259 009
cert_ridgeSupport_suffix_3 259 008 009
cert_ridgeSupport_suffix_3 259 007 008
cert_ridgeSupport_suffix_3 259 006 007
cert_ridgeSupport_suffix_3 259 005 006
cert_ridgeSupport_suffix_3 259 004 005
cert_ridgeSupport_suffix_3 259 003 004
cert_ridgeSupport_suffix_3 259 002 003
cert_ridgeSupport_suffix_3 259 001 002
cert_ridgeSupport_suffix_3 259 000 001
cert_ridgeSupport_source_3 259 13 281
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
