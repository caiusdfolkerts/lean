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
def kindSupport8_000 : List Nat := [21016,21017,21018,21019,21020,21021,21022,21023,21024,21025,21026,21027,21028,21029,21030,21031,21032,21033,21034,21035,21036,21037,21038,21039,21040,21041,21042,21043,21044,21045,21046,21047]
def kindSupport8_001 : List Nat := [21048,21049,21050,21051,21052,21053,21054,21055,21056,21057,21058,21059,21060,21061,21062,21063,21064,21065,21066,21067,21068,21069,21070,21071,21072,21073,21074,21075,21076,21077,21078,21079]
def kindSupport8_002 : List Nat := [21080,21081,21082,21083,21084,21085,21086,21087,21088,21089,21090,21091,21092,21093,21094,21095,21096,21097,21098,21099,21100,21101,21102,21103,21104,21105,21106,21107,21108,21109,21110,21111]
def kindSupport8_003 : List Nat := [21112,21113,21114,21115,21116,21117,21118,21119,21120,21121,21122,21123,21124,21125,21126,21127,21128,21129,21130,21131,21132,21133,21134,21135,21136,21137,21138,21139,21140,21141,21142,21143]
def kindSupport8_004 : List Nat := [21144,21145,21146,21147,21148,21149,21150,21151,21152,21153,21154,21155,21156,21157,21158,21159,21160,21161,21162,21163,21164,21165,21166,21167,21168,21169,21170,21171,21172,21173,21174,21175]
def kindSupport8_005 : List Nat := [21176,21177,21178,21179,21180,21181,21182,21183,21184,21185,21186,21187,21188,21189,21190,21191,21192,21193,21194,21195,21196,21197,21198,21199,21200,21201,21202,21203,21204,21205,21206,21207]
def kindSupport8_006 : List Nat := [21208,21209,21210,21211,21212,21213,21214,21215,21216,21217,21218,21219,21220,21221,21222,21223,21224,21225,21226,21227,21228,21229,21230,21231,21232,21233,21234,21235,21236,21237,21238,21239]
def kindSupport8_007 : List Nat := [21240,21241,21242,21243,21244,21245,21246,21247,21248,21249,21250,21251,21252,21253,21254,21255,21256,21257,21258,21259,21260,21261,21262,21263,21264,21265,21266,21267,21268,21269,21270,21271]
def kindSupport8_008 : List Nat := [21272,21273,21274,21275,21276,21277,21278,21279,21280,21281,21282,21283,21284,21285,21286,21287,21288,21289,21290,21291,21292,21293,21294,21295,21296,21297,21298,21299,21300,21301,21302,21303]
def kindSupport8_009 : List Nat := [21304,21305,21306,21307,21308,21309,21310,21311,21312,21313,21314,21315,21316,21317,21318,21319,21320,21321,21322,21323,21324,21325,21326,21327,21328,21329,21330,21331,21332,21333,21334,21335]
def kindSupport8_010 : List Nat := [21336,21337,21338,21339,21340,21341,21342,21343,21344,21345,21346,21347,21348,21349,21350,21351]
def kindSupport8_code : Nat := 0xa6cf4d9a9b2d364a6c74d8a9b0d360a6bf4d7a9aed35ca6b74d6a9acd358a6af4d5a9aad354a6a74d4a9a8d350a69f4d3a9a6d34ca6974d2a9a4d348a68f4d1a9a2d344a6874d0a9a0d340a67f4cfa99ed33ca6774cea99cd338a66f4cda99ad334a6674cca998d330a65f4cba996d32ca6574caa994d328a64f4c9a992d324a6474c8a990d320a63f4c7a98ed31ca6374c6a98cd318a62f4c5a98ad314a6274c4a988d310a61f4c3a986d30ca6174c2a984d308a60f4c1a982d304a6074c0a980d300a5ff4bfa97ed2fca5f74bea97cd2f8a5ef4bda97ad2f4a5e74bca978d2f0a5df4bba976d2eca5d74baa974d2e8a5cf4b9a972d2e4a5c74b8a970d2e0a5bf4b7a96ed2dca5b74b6a96cd2d8a5af4b5a96ad2d4a5a74b4a968d2d0a59f4b3a966d2cca5974b2a964d2c8a58f4b1a962d2c4a5874b0a960d2c0a57f4afa95ed2bca5774aea95cd2b8a56f4ada95ad2b4a5674aca958d2b0a55f4aba956d2aca5574aaa954d2a8a54f4a9a952d2a4a5474a8a950d2a0a53f4a7a94ed29ca5374a6a94cd298a52f4a5a94ad294a5274a4a948d290a51f4a3a946d28ca5174a2a944d288a50f4a1a942d284a5074a0a940d280a4ff49fa93ed27ca4f749ea93cd278a4ef49da93ad274a4e749ca938d270a4df49ba936d26ca4d749aa934d268a4cf499a932d264a4c7498a930d260a4bf497a92ed25ca4b7496a92cd258a4af495a92ad254a4a7494a928d250a49f493a926d24ca497492a924d248a48f491a922d244a487490a920d240a47f48fa91ed23ca47748ea91cd238a46f48da91ad234a46748ca918d230a45f48ba916d22ca45748aa914d228a44f489a912d224a447488a910d220a43f487a90ed21ca437486a90cd218
def kindSupport8_rest_000 : Nat := PackedRawNatGrowth.drop 0 kindSupport8_code
def kindSupport8_rest_001 : Nat := PackedRawNatGrowth.drop 480 kindSupport8_code
def kindSupport8_rest_002 : Nat := PackedRawNatGrowth.drop 960 kindSupport8_code
def kindSupport8_rest_003 : Nat := PackedRawNatGrowth.drop 1440 kindSupport8_code
def kindSupport8_rest_004 : Nat := PackedRawNatGrowth.drop 1920 kindSupport8_code
def kindSupport8_rest_005 : Nat := PackedRawNatGrowth.drop 2400 kindSupport8_code
def kindSupport8_rest_006 : Nat := PackedRawNatGrowth.drop 2880 kindSupport8_code
def kindSupport8_rest_007 : Nat := PackedRawNatGrowth.drop 3360 kindSupport8_code
def kindSupport8_rest_008 : Nat := PackedRawNatGrowth.drop 3840 kindSupport8_code
def kindSupport8_rest_009 : Nat := PackedRawNatGrowth.drop 4320 kindSupport8_code
def kindSupport8_rest_010 : Nat := PackedRawNatGrowth.drop 4800 kindSupport8_code
def kindSupport8_rest_011 : Nat := PackedRawNatGrowth.drop 5040 kindSupport8_code
def kindSupport8_suffix_011 : List Nat := []
def kindSupport8_suffix_010 : List Nat := kindSupport8_010 ++ kindSupport8_suffix_011
def kindSupport8_suffix_009 : List Nat := kindSupport8_009 ++ kindSupport8_suffix_010
def kindSupport8_suffix_008 : List Nat := kindSupport8_008 ++ kindSupport8_suffix_009
def kindSupport8_suffix_007 : List Nat := kindSupport8_007 ++ kindSupport8_suffix_008
def kindSupport8_suffix_006 : List Nat := kindSupport8_006 ++ kindSupport8_suffix_007
def kindSupport8_suffix_005 : List Nat := kindSupport8_005 ++ kindSupport8_suffix_006
def kindSupport8_suffix_004 : List Nat := kindSupport8_004 ++ kindSupport8_suffix_005
def kindSupport8_suffix_003 : List Nat := kindSupport8_003 ++ kindSupport8_suffix_004
def kindSupport8_suffix_002 : List Nat := kindSupport8_002 ++ kindSupport8_suffix_003
def kindSupport8_suffix_001 : List Nat := kindSupport8_001 ++ kindSupport8_suffix_002
def kindSupport8_suffix_000 : List Nat := kindSupport8_000 ++ kindSupport8_suffix_001
theorem kindSupport8_source : kindRows 8 =
    (PackedRawNatGrowth.readList 15 336 kindSupport8_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase00
