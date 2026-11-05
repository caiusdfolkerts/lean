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
def kindSupport9_000 : List Nat := [7048,7049,7050,7051,7052,7053,7054,7055,7056,7057,7058,7059,7060,7061,7062,7063,7064,7065,7066,7067,7068,7069,7070,7071,7072,7073,7074,7075,7076,7077,7078,7079]
def kindSupport9_001 : List Nat := [7080,7081,7082,7083,7084,7085,7086,7087,7088,7089,7090,7091,7092,7093,7094,7095,7096,7097,7098,7099,7100,7101,7102,7103,7104,7105,7106,7107,7108,7109,7110,7111]
def kindSupport9_002 : List Nat := [7112,7113,7114,7115,7116,7117,7118,7119,7120,7121,7122,7123,7124,7125,7126,7127,7128,7129,7130,7131,7132,7133,7134,7135,7136,7137,7138,7139,7140,7141,7142,7143]
def kindSupport9_003 : List Nat := [7144,7145,7146,7147,7148,7149,7150,7151,7152,7153,7154,7155,7156,7157,7158,7159,7160,7161,7162,7163,7164,7165,7166,7167,7168,7169,7170,7171,7172,7173,7174,7175]
def kindSupport9_004 : List Nat := [7176,7177,7178,7179,7180,7181,7182,7183,7184,7185,7186,7187,7188,7189,7190,7191,7192,7193,7194,7195,7196,7197,7198,7199,7200,7201,7202,7203,7204,7205,7206,7207]
def kindSupport9_005 : List Nat := [7208,7209,7210,7211,7212,7213,7214,7215,7216,7217,7218,7219,7220,7221,7222,7223,7224,7225,7226,7227,7228,7229,7230,7231,7232,7233,7234,7235,7236,7237,7238,7239]
def kindSupport9_006 : List Nat := [7240,7241,7242,7243,7244,7245,7246,7247,7248,7249,7250,7251,7252,7253,7254,7255,7256,7257,7258,7259,7260,7261,7262,7263,7264,7265,7266,7267,7268,7269,7270,7271]
def kindSupport9_007 : List Nat := [7272,7273,7274,7275,7276,7277,7278,7279,7280,7281,7282,7283,7284,7285,7286,7287,7288,7289,7290,7291,7292,7293,7294,7295,7296,7297,7298,7299,7300,7301,7302,7303]
def kindSupport9_008 : List Nat := [7304,7305,7306,7307,7308,7309,7310,7311,7312,7313,7314,7315,7316,7317,7318,7319,7320,7321,7322,7323,7324,7325,7326,7327,7328,7329,7330,7331,7332,7333,7334,7335]
def kindSupport9_009 : List Nat := [7336,7337,7338,7339,7340,7341,7342,7343,7344,7345,7346,7347,7348,7349,7350,7351,7352,7353,7354,7355,7356,7357,7358,7359,7360,7361,7362,7363,7364,7365,7366,7367]
def kindSupport9_010 : List Nat := [7368,7369,7370,7371,7372,7373,7374,7375,7376,7377,7378,7379,7380,7381,7382,7383,7384,7385,7386,7387,7388,7389,7390,7391,7392,7393,7394,7395,7396,7397,7398,7399]
def kindSupport9_011 : List Nat := [7400,7401,7402,7403,7404,7405,7406,7407,7408,7409,7410,7411,7412,7413,7414,7415,7416,7417,7418,7419,7420,7421,7422,7423,7424,7425,7426,7427,7428,7429,7430,7431]
def kindSupport9_012 : List Nat := [7432,7433,7434,7435,7436,7437,7438,7439,7440,7441,7442,7443,7444,7445,7446,7447,7448,7449,7450,7451,7452,7453,7454,7455,7456,7457,7458,7459,7460,7461,7462,7463]
def kindSupport9_013 : List Nat := [7464,7465,7466,7467,7468,7469,7470,7471,7472,7473,7474,7475,7476,7477,7478,7479,7480,7481,7482,7483,7484,7485,7486,7487,7488,7489,7490,7491,7492,7493,7494,7495]
def kindSupport9_014 : List Nat := [7496,7497,7498,7499,7500,7501,7502,7503,7504,7505,7506,7507,7508,7509,7510,7511,7512,7513,7514,7515,7516,7517,7518,7519,7520,7521,7522,7523,7524,7525,7526,7527]
def kindSupport9_015 : List Nat := [7528,7529,7530,7531,7532,7533,7534,7535,7536,7537,7538,7539,7540,7541,7542,7543,7544,7545,7546,7547,7548,7549,7550,7551,7552,7553,7554,7555,7556,7557,7558,7559]
def kindSupport9_016 : List Nat := [7560,7561,7562,7563,7564,7565,7566,7567,7568,7569,7570,7571,7572,7573,7574,7575,7576,7577,7578,7579,7580,7581,7582,7583,7584,7585,7586,7587,7588,7589,7590,7591]
def kindSupport9_017 : List Nat := [7592,7593,7594,7595,7596,7597,7598,7599,7600,7601,7602,7603,7604,7605,7606,7607,7608,7609,7610,7611,7612,7613,7614,7615,7616,7617,7618,7619,7620,7621,7622,7623]
def kindSupport9_018 : List Nat := [7624,7625,7626,7627,7628,7629,7630,7631,7632,7633,7634,7635,7636,7637,7638,7639,7640,7641,7642,7643,7644,7645,7646,7647,7648,7649,7650,7651,7652,7653,7654,7655]
def kindSupport9_019 : List Nat := [7656,7657,7658,7659,7660,7661,7662,7663,7664,7665,7666,7667,7668,7669,7670,7671]
def kindSupport9_code : Nat := 0x77dddf677d5df477cddf277c5df077bddee77b5dec77addea77a5de8779dde67795de4778dde27785de0777ddde7775ddc776ddda7765dd8775ddd67755dd4774ddd27745dd0773ddce7735dcc772ddca7725dc8771ddc67715dc4770ddc27705dc076fddbe76f5dbc76eddba76e5db876dddb676d5db476cddb276c5db076bddae76b5dac76addaa76a5da8769dda67695da4768dda27685da0767dd9e7675d9c766dd9a7665d98765dd967655d94764dd927645d90763dd8e7635d8c762dd8a7625d88761dd867615d84760dd827605d8075fdd7e75f5d7c75edd7a75e5d7875ddd7675d5d7475cdd7275c5d7075bdd6e75b5d6c75add6a75a5d68759dd667595d64758dd627585d60757dd5e7575d5c756dd5a7565d58755dd567555d54754dd527545d50753dd4e7535d4c752dd4a7525d48751dd467515d44750dd427505d4074fdd3e74f5d3c74edd3a74e5d3874ddd3674d5d3474cdd3274c5d3074bdd2e74b5d2c74add2a74a5d28749dd267495d24748dd227485d20747dd1e7475d1c746dd1a7465d18745dd167455d14744dd127445d10743dd0e7435d0c742dd0a7425d08741dd067415d04740dd027405d0073fdcfe73f5cfc73edcfa73e5cf873ddcf673d5cf473cdcf273c5cf073bdcee73b5cec73adcea73a5ce8739dce67395ce4738dce27385ce0737dcde7375cdc736dcda7365cd8735dcd67355cd4734dcd27345cd0733dcce7335ccc732dcca7325cc8731dcc67315cc4730dcc27305cc072fdcbe72f5cbc72edcba72e5cb872ddcb672d5cb472cdcb272c5cb072bdcae72b5cac72adcaa72a5ca8729dca67295ca4728dca27285ca0727dc9e7275c9c726dc9a7265c98725dc967255c94724dc927245c90723dc8e7235c8c722dc8a7225c88721dc867215c84720dc827205c8071fdc7e71f5c7c71edc7a71e5c7871ddc7671d5c7471cdc7271c5c7071bdc6e71b5c6c71adc6a71a5c68719dc667195c64718dc627185c60717dc5e7175c5c716dc5a7165c58715dc567155c54714dc527145c50713dc4e7135c4c712dc4a7125c48711dc467115c44710dc427105c4070fdc3e70f5c3c70edc3a70e5c3870ddc3670d5c3470cdc3270c5c3070bdc2e70b5c2c70adc2a70a5c28709dc267095c24708dc227085c20707dc1e7075c1c706dc1a7065c18705dc167055c14704dc127045c10703dc0e7035c0c702dc0a7025c08701dc067015c04700dc027005c006ffdbfe6ff5bfc6fedbfa6fe5bf86fddbf66fd5bf46fcdbf26fc5bf06fbdbee6fb5bec6fadbea6fa5be86f9dbe66f95be46f8dbe26f85be06f7dbde6f75bdc6f6dbda6f65bd86f5dbd66f55bd46f4dbd26f45bd06f3dbce6f35bcc6f2dbca6f25bc86f1dbc66f15bc46f0dbc26f05bc06efdbbe6ef5bbc6eedbba6ee5bb86eddbb66ed5bb46ecdbb26ec5bb06ebdbae6eb5bac6eadbaa6ea5ba86e9dba66e95ba46e8dba26e85ba06e7db9e6e75b9c6e6db9a6e65b986e5db966e55b946e4db926e45b906e3db8e6e35b8c6e2db8a6e25b88
def kindSupport9_rest_000 : Nat := PackedRawNatGrowth.drop 0 kindSupport9_code
def kindSupport9_rest_001 : Nat := PackedRawNatGrowth.drop 448 kindSupport9_code
def kindSupport9_rest_002 : Nat := PackedRawNatGrowth.drop 896 kindSupport9_code
def kindSupport9_rest_003 : Nat := PackedRawNatGrowth.drop 1344 kindSupport9_code
def kindSupport9_rest_004 : Nat := PackedRawNatGrowth.drop 1792 kindSupport9_code
def kindSupport9_rest_005 : Nat := PackedRawNatGrowth.drop 2240 kindSupport9_code
def kindSupport9_rest_006 : Nat := PackedRawNatGrowth.drop 2688 kindSupport9_code
def kindSupport9_rest_007 : Nat := PackedRawNatGrowth.drop 3136 kindSupport9_code
def kindSupport9_rest_008 : Nat := PackedRawNatGrowth.drop 3584 kindSupport9_code
def kindSupport9_rest_009 : Nat := PackedRawNatGrowth.drop 4032 kindSupport9_code
def kindSupport9_rest_010 : Nat := PackedRawNatGrowth.drop 4480 kindSupport9_code
def kindSupport9_rest_011 : Nat := PackedRawNatGrowth.drop 4928 kindSupport9_code
def kindSupport9_rest_012 : Nat := PackedRawNatGrowth.drop 5376 kindSupport9_code
def kindSupport9_rest_013 : Nat := PackedRawNatGrowth.drop 5824 kindSupport9_code
def kindSupport9_rest_014 : Nat := PackedRawNatGrowth.drop 6272 kindSupport9_code
def kindSupport9_rest_015 : Nat := PackedRawNatGrowth.drop 6720 kindSupport9_code
def kindSupport9_rest_016 : Nat := PackedRawNatGrowth.drop 7168 kindSupport9_code
def kindSupport9_rest_017 : Nat := PackedRawNatGrowth.drop 7616 kindSupport9_code
def kindSupport9_rest_018 : Nat := PackedRawNatGrowth.drop 8064 kindSupport9_code
def kindSupport9_rest_019 : Nat := PackedRawNatGrowth.drop 8512 kindSupport9_code
def kindSupport9_rest_020 : Nat := PackedRawNatGrowth.drop 8736 kindSupport9_code
def kindSupport9_suffix_020 : List Nat := []
def kindSupport9_suffix_019 : List Nat := kindSupport9_019 ++ kindSupport9_suffix_020
def kindSupport9_suffix_018 : List Nat := kindSupport9_018 ++ kindSupport9_suffix_019
def kindSupport9_suffix_017 : List Nat := kindSupport9_017 ++ kindSupport9_suffix_018
def kindSupport9_suffix_016 : List Nat := kindSupport9_016 ++ kindSupport9_suffix_017
def kindSupport9_suffix_015 : List Nat := kindSupport9_015 ++ kindSupport9_suffix_016
def kindSupport9_suffix_014 : List Nat := kindSupport9_014 ++ kindSupport9_suffix_015
def kindSupport9_suffix_013 : List Nat := kindSupport9_013 ++ kindSupport9_suffix_014
def kindSupport9_suffix_012 : List Nat := kindSupport9_012 ++ kindSupport9_suffix_013
def kindSupport9_suffix_011 : List Nat := kindSupport9_011 ++ kindSupport9_suffix_012
def kindSupport9_suffix_010 : List Nat := kindSupport9_010 ++ kindSupport9_suffix_011
def kindSupport9_suffix_009 : List Nat := kindSupport9_009 ++ kindSupport9_suffix_010
def kindSupport9_suffix_008 : List Nat := kindSupport9_008 ++ kindSupport9_suffix_009
def kindSupport9_suffix_007 : List Nat := kindSupport9_007 ++ kindSupport9_suffix_008
def kindSupport9_suffix_006 : List Nat := kindSupport9_006 ++ kindSupport9_suffix_007
def kindSupport9_suffix_005 : List Nat := kindSupport9_005 ++ kindSupport9_suffix_006
def kindSupport9_suffix_004 : List Nat := kindSupport9_004 ++ kindSupport9_suffix_005
def kindSupport9_suffix_003 : List Nat := kindSupport9_003 ++ kindSupport9_suffix_004
def kindSupport9_suffix_002 : List Nat := kindSupport9_002 ++ kindSupport9_suffix_003
def kindSupport9_suffix_001 : List Nat := kindSupport9_001 ++ kindSupport9_suffix_002
def kindSupport9_suffix_000 : List Nat := kindSupport9_000 ++ kindSupport9_suffix_001
theorem kindSupport9_source : kindSupports 9 =
    (PackedRawNatGrowth.readList 14 624 kindSupport9_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
