module
prelude
public import RootedSixBase02GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport9_000 : List Nat := [7580,7581,7582,7583,7584,7585,7586,7587,7588,7589,7590,7591,7592,7593,7594,7595,7596,7597,7598,7599,7600,7601,7602,7603,7604,7605,7606,7607,7608,7609,7610,7611]
def kindSupport9_001 : List Nat := [7612,7613,7614,7615,7616,7617,7618,7619,7620,7621,7622,7623,7624,7625,7626,7627,7628,7629,7630,7631,7632,7633,7634,7635,7636,7637,7638,7639,7640,7641,7642,7643]
def kindSupport9_002 : List Nat := [7644,7645,7646,7647,7648,7649,7650,7651,7652,7653,7654,7655,7656,7657,7658,7659,7660,7661,7662,7663,7664,7665,7666,7667,7668,7669,7670,7671,7672,7673,7674,7675]
def kindSupport9_003 : List Nat := [7676,7677,7678,7679,7680,7681,7682,7683,7684,7685,7686,7687,7688,7689,7690,7691,7692,7693,7694,7695,7696,7697,7698,7699,7700,7701,7702,7703,7704,7705,7706,7707]
def kindSupport9_004 : List Nat := [7708,7709,7710,7711,7712,7713,7714,7715,7716,7717,7718,7719,7720,7721,7722,7723,7724,7725,7726,7727,7728,7729,7730,7731,7732,7733,7734,7735,7736,7737,7738,7739]
def kindSupport9_005 : List Nat := [7740,7741,7742,7743,7744,7745,7746,7747,7748,7749,7750,7751,7752,7753,7754,7755,7756,7757,7758,7759,7760,7761,7762,7763,7764,7765,7766,7767,7768,7769,7770,7771]
def kindSupport9_006 : List Nat := [7772,7773,7774,7775,7776,7777,7778,7779,7780,7781,7782,7783,7784,7785,7786,7787,7788,7789,7790,7791,7792,7793,7794,7795,7796,7797,7798,7799,7800,7801,7802,7803]
def kindSupport9_007 : List Nat := [7804,7805,7806,7807,7808,7809,7810,7811,7812,7813,7814,7815,7816,7817,7818,7819,7820,7821,7822,7823,7824,7825,7826,7827,7828,7829,7830,7831,7832,7833,7834,7835]
def kindSupport9_008 : List Nat := [7836,7837,7838,7839,7840,7841,7842,7843,7844,7845,7846,7847,7848,7849,7850,7851,7852,7853,7854,7855,7856,7857,7858,7859,7860,7861,7862,7863,7864,7865,7866,7867]
def kindSupport9_009 : List Nat := [7868,7869,7870,7871,7872,7873,7874,7875,7876,7877,7878,7879,7880,7881,7882,7883,7884,7885,7886,7887,7888,7889,7890,7891,7892,7893,7894,7895,7896,7897,7898,7899]
def kindSupport9_010 : List Nat := [7900,7901,7902,7903,7904,7905,7906,7907,7908,7909,7910,7911,7912,7913,7914,7915,7916,7917,7918,7919,7920,7921,7922,7923,7924,7925,7926,7927,7928,7929,7930,7931]
def kindSupport9_011 : List Nat := [7932,7933,7934,7935,7936,7937,7938,7939,7940,7941,7942,7943,7944,7945,7946,7947,7948,7949,7950,7951,7952,7953,7954,7955,7956,7957,7958,7959,7960,7961,7962,7963]
def kindSupport9_012 : List Nat := [7964,7965,7966,7967,7968,7969,7970,7971,7972,7973,7974,7975,7976,7977,7978,7979,7980,7981,7982,7983,7984,7985,7986,7987,7988,7989,7990,7991,7992,7993,7994,7995]
def kindSupport9_013 : List Nat := [7996,7997,7998,7999,8000,8001,8002,8003,8004,8005,8006,8007,8008,8009,8010,8011,8012,8013,8014,8015,8016,8017,8018,8019,8020,8021,8022,8023,8024,8025,8026,8027]
def kindSupport9_014 : List Nat := [8028,8029,8030,8031,8032,8033,8034,8035,8036,8037,8038,8039,8040,8041,8042,8043,8044,8045,8046,8047,8048,8049,8050,8051,8052,8053,8054,8055,8056,8057,8058,8059]
def kindSupport9_015 : List Nat := [8060,8061,8062,8063,8064,8065,8066,8067,8068,8069,8070,8071,8072,8073,8074,8075,8076,8077,8078,8079,8080,8081,8082,8083]
def kindSupport9_code : Nat := 0xfc9fe4bf23f90fc7fe3bf1bf8cfc5fe2bf13f88fc3fe1bf0bf84fc1fe0bf03f80fbffdfbefbf7cfbdfdebef3f78fbbfddbeebf74fb9fdcbee3f70fb7fdbbedbf6cfb5fdabed3f68fb3fd9becbf64fb1fd8bec3f60faffd7bebbf5cfadfd6beb3f58fabfd5beabf54fa9fd4bea3f50fa7fd3be9bf4cfa5fd2be93f48fa3fd1be8bf44fa1fd0be83f40f9ffcfbe7bf3cf9dfcebe73f38f9bfcdbe6bf34f99fccbe63f30f97fcbbe5bf2cf95fcabe53f28f93fc9be4bf24f91fc8be43f20f8ffc7be3bf1cf8dfc6be33f18f8bfc5be2bf14f89fc4be23f10f87fc3be1bf0cf85fc2be13f08f83fc1be0bf04f81fc0be03f00f7ffbfbdfbefcf7dfbebdf3ef8f7bfbdbdebef4f79fbcbde3ef0f77fbbbddbeecf75fbabdd3ee8f73fb9bdcbee4f71fb8bdc3ee0f6ffb7bdbbedcf6dfb6bdb3ed8f6bfb5bdabed4f69fb4bda3ed0f67fb3bd9beccf65fb2bd93ec8f63fb1bd8bec4f61fb0bd83ec0f5ffafbd7bebcf5dfaebd73eb8f5bfadbd6beb4f59facbd63eb0f57fabbd5beacf55faabd53ea8f53fa9bd4bea4f51fa8bd43ea0f4ffa7bd3be9cf4dfa6bd33e98f4bfa5bd2be94f49fa4bd23e90f47fa3bd1be8cf45fa2bd13e88f43fa1bd0be84f41fa0bd03e80f3ff9fbcfbe7cf3df9ebcf3e78f3bf9dbcebe74f39f9cbce3e70f37f9bbcdbe6cf35f9abcd3e68f33f99bccbe64f31f98bcc3e60f2ff97bcbbe5cf2df96bcb3e58f2bf95bcabe54f29f94bca3e50f27f93bc9be4cf25f92bc93e48f23f91bc8be44f21f90bc83e40f1ff8fbc7be3cf1df8ebc73e38f1bf8dbc6be34f19f8cbc63e30f17f8bbc5be2cf15f8abc53e28f13f89bc4be24f11f88bc43e20f0ff87bc3be1cf0df86bc33e18f0bf85bc2be14f09f84bc23e10f07f83bc1be0cf05f82bc13e08f03f81bc0be04f01f80bc03e00efff7fbbfbdfcefdf7ebbf3df8efbf7dbbebdf4ef9f7cbbe3df0ef7f7bbbdbdecef5f7abbd3de8ef3f79bbcbde4ef1f78bbc3de0eeff77bbbbddceedf76bbb3dd8eebf75bbabdd4ee9f74bba3dd0ee7f73bb9bdccee5f72bb93dc8ee3f71bb8bdc4ee1f70bb83dc0edff6fbb7bdbceddf6ebb73db8edbf6dbb6bdb4ed9f6cbb63db0ed7f6bbb5bdaced5f6abb53da8ed3f69bb4bda4ed1f68bb43da0ecff67bb3bd9c
def kindSupport9_rest_000 : Nat := PackedRawNatGrowth.drop 0 kindSupport9_code
def kindSupport9_rest_001 : Nat := PackedRawNatGrowth.drop 416 kindSupport9_code
def kindSupport9_rest_002 : Nat := PackedRawNatGrowth.drop 832 kindSupport9_code
def kindSupport9_rest_003 : Nat := PackedRawNatGrowth.drop 1248 kindSupport9_code
def kindSupport9_rest_004 : Nat := PackedRawNatGrowth.drop 1664 kindSupport9_code
def kindSupport9_rest_005 : Nat := PackedRawNatGrowth.drop 2080 kindSupport9_code
def kindSupport9_rest_006 : Nat := PackedRawNatGrowth.drop 2496 kindSupport9_code
def kindSupport9_rest_007 : Nat := PackedRawNatGrowth.drop 2912 kindSupport9_code
def kindSupport9_rest_008 : Nat := PackedRawNatGrowth.drop 3328 kindSupport9_code
def kindSupport9_rest_009 : Nat := PackedRawNatGrowth.drop 3744 kindSupport9_code
def kindSupport9_rest_010 : Nat := PackedRawNatGrowth.drop 4160 kindSupport9_code
def kindSupport9_rest_011 : Nat := PackedRawNatGrowth.drop 4576 kindSupport9_code
def kindSupport9_rest_012 : Nat := PackedRawNatGrowth.drop 4992 kindSupport9_code
def kindSupport9_rest_013 : Nat := PackedRawNatGrowth.drop 5408 kindSupport9_code
def kindSupport9_rest_014 : Nat := PackedRawNatGrowth.drop 5824 kindSupport9_code
def kindSupport9_rest_015 : Nat := PackedRawNatGrowth.drop 6240 kindSupport9_code
def kindSupport9_rest_016 : Nat := PackedRawNatGrowth.drop 6552 kindSupport9_code
def kindSupport9_suffix_016 : List Nat := []
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
    (PackedRawNatGrowth.readList 13 504 kindSupport9_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
