module
prelude
public import RootedSixBase00CanonicalT0Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 6 (raw i) template root
      FacetUniverses.RootedSixBase00.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 208 := i.isLt
  by_cases h_0_208 : i.val < 104
  · by_cases h_0_104 : i.val < 52
    · by_cases h_0_52 : i.val < 26
      · by_cases h_0_26 : i.val < 13
        · by_cases h_0_13 : i.val < 6
          · by_cases h_0_6 : i.val < 3
            · by_cases h_0_3 : i.val < 1
              · have heq : i = Fin.ofNat 208 0 := Fin.ext (by change i.val = 0; omega)
                subst i
                exact block_0000
              · by_cases h_1_3 : i.val < 2
                · have heq : i = Fin.ofNat 208 1 := Fin.ext (by change i.val = 1; omega)
                  subst i
                  exact block_0001
                · have heq : i = Fin.ofNat 208 2 := Fin.ext (by change i.val = 2; omega)
                  subst i
                  exact block_0002
            · by_cases h_3_6 : i.val < 4
              · have heq : i = Fin.ofNat 208 3 := Fin.ext (by change i.val = 3; omega)
                subst i
                exact block_0003
              · by_cases h_4_6 : i.val < 5
                · have heq : i = Fin.ofNat 208 4 := Fin.ext (by change i.val = 4; omega)
                  subst i
                  exact block_0004
                · have heq : i = Fin.ofNat 208 5 := Fin.ext (by change i.val = 5; omega)
                  subst i
                  exact block_0005
          · by_cases h_6_13 : i.val < 9
            · by_cases h_6_9 : i.val < 7
              · have heq : i = Fin.ofNat 208 6 := Fin.ext (by change i.val = 6; omega)
                subst i
                exact block_0006
              · by_cases h_7_9 : i.val < 8
                · have heq : i = Fin.ofNat 208 7 := Fin.ext (by change i.val = 7; omega)
                  subst i
                  exact block_0007
                · have heq : i = Fin.ofNat 208 8 := Fin.ext (by change i.val = 8; omega)
                  subst i
                  exact block_0008
            · by_cases h_9_13 : i.val < 11
              · by_cases h_9_11 : i.val < 10
                · have heq : i = Fin.ofNat 208 9 := Fin.ext (by change i.val = 9; omega)
                  subst i
                  exact block_0009
                · have heq : i = Fin.ofNat 208 10 := Fin.ext (by change i.val = 10; omega)
                  subst i
                  exact block_0010
              · by_cases h_11_13 : i.val < 12
                · have heq : i = Fin.ofNat 208 11 := Fin.ext (by change i.val = 11; omega)
                  subst i
                  exact block_0011
                · have heq : i = Fin.ofNat 208 12 := Fin.ext (by change i.val = 12; omega)
                  subst i
                  exact block_0012
        · by_cases h_13_26 : i.val < 19
          · by_cases h_13_19 : i.val < 16
            · by_cases h_13_16 : i.val < 14
              · have heq : i = Fin.ofNat 208 13 := Fin.ext (by change i.val = 13; omega)
                subst i
                exact block_0013
              · by_cases h_14_16 : i.val < 15
                · have heq : i = Fin.ofNat 208 14 := Fin.ext (by change i.val = 14; omega)
                  subst i
                  exact block_0014
                · have heq : i = Fin.ofNat 208 15 := Fin.ext (by change i.val = 15; omega)
                  subst i
                  exact block_0015
            · by_cases h_16_19 : i.val < 17
              · have heq : i = Fin.ofNat 208 16 := Fin.ext (by change i.val = 16; omega)
                subst i
                exact block_0016
              · by_cases h_17_19 : i.val < 18
                · have heq : i = Fin.ofNat 208 17 := Fin.ext (by change i.val = 17; omega)
                  subst i
                  exact block_0017
                · have heq : i = Fin.ofNat 208 18 := Fin.ext (by change i.val = 18; omega)
                  subst i
                  exact block_0018
          · by_cases h_19_26 : i.val < 22
            · by_cases h_19_22 : i.val < 20
              · have heq : i = Fin.ofNat 208 19 := Fin.ext (by change i.val = 19; omega)
                subst i
                exact block_0019
              · by_cases h_20_22 : i.val < 21
                · have heq : i = Fin.ofNat 208 20 := Fin.ext (by change i.val = 20; omega)
                  subst i
                  exact block_0020
                · have heq : i = Fin.ofNat 208 21 := Fin.ext (by change i.val = 21; omega)
                  subst i
                  exact block_0021
            · by_cases h_22_26 : i.val < 24
              · by_cases h_22_24 : i.val < 23
                · have heq : i = Fin.ofNat 208 22 := Fin.ext (by change i.val = 22; omega)
                  subst i
                  exact block_0022
                · have heq : i = Fin.ofNat 208 23 := Fin.ext (by change i.val = 23; omega)
                  subst i
                  exact block_0023
              · by_cases h_24_26 : i.val < 25
                · have heq : i = Fin.ofNat 208 24 := Fin.ext (by change i.val = 24; omega)
                  subst i
                  exact block_0024
                · have heq : i = Fin.ofNat 208 25 := Fin.ext (by change i.val = 25; omega)
                  subst i
                  exact block_0025
      · by_cases h_26_52 : i.val < 39
        · by_cases h_26_39 : i.val < 32
          · by_cases h_26_32 : i.val < 29
            · by_cases h_26_29 : i.val < 27
              · have heq : i = Fin.ofNat 208 26 := Fin.ext (by change i.val = 26; omega)
                subst i
                exact block_0026
              · by_cases h_27_29 : i.val < 28
                · have heq : i = Fin.ofNat 208 27 := Fin.ext (by change i.val = 27; omega)
                  subst i
                  exact block_0027
                · have heq : i = Fin.ofNat 208 28 := Fin.ext (by change i.val = 28; omega)
                  subst i
                  exact block_0028
            · by_cases h_29_32 : i.val < 30
              · have heq : i = Fin.ofNat 208 29 := Fin.ext (by change i.val = 29; omega)
                subst i
                exact block_0029
              · by_cases h_30_32 : i.val < 31
                · have heq : i = Fin.ofNat 208 30 := Fin.ext (by change i.val = 30; omega)
                  subst i
                  exact block_0030
                · have heq : i = Fin.ofNat 208 31 := Fin.ext (by change i.val = 31; omega)
                  subst i
                  exact block_0031
          · by_cases h_32_39 : i.val < 35
            · by_cases h_32_35 : i.val < 33
              · have heq : i = Fin.ofNat 208 32 := Fin.ext (by change i.val = 32; omega)
                subst i
                exact block_0032
              · by_cases h_33_35 : i.val < 34
                · have heq : i = Fin.ofNat 208 33 := Fin.ext (by change i.val = 33; omega)
                  subst i
                  exact block_0033
                · have heq : i = Fin.ofNat 208 34 := Fin.ext (by change i.val = 34; omega)
                  subst i
                  exact block_0034
            · by_cases h_35_39 : i.val < 37
              · by_cases h_35_37 : i.val < 36
                · have heq : i = Fin.ofNat 208 35 := Fin.ext (by change i.val = 35; omega)
                  subst i
                  exact block_0035
                · have heq : i = Fin.ofNat 208 36 := Fin.ext (by change i.val = 36; omega)
                  subst i
                  exact block_0036
              · by_cases h_37_39 : i.val < 38
                · have heq : i = Fin.ofNat 208 37 := Fin.ext (by change i.val = 37; omega)
                  subst i
                  exact block_0037
                · have heq : i = Fin.ofNat 208 38 := Fin.ext (by change i.val = 38; omega)
                  subst i
                  exact block_0038
        · by_cases h_39_52 : i.val < 45
          · by_cases h_39_45 : i.val < 42
            · by_cases h_39_42 : i.val < 40
              · have heq : i = Fin.ofNat 208 39 := Fin.ext (by change i.val = 39; omega)
                subst i
                exact block_0039
              · by_cases h_40_42 : i.val < 41
                · have heq : i = Fin.ofNat 208 40 := Fin.ext (by change i.val = 40; omega)
                  subst i
                  exact block_0040
                · have heq : i = Fin.ofNat 208 41 := Fin.ext (by change i.val = 41; omega)
                  subst i
                  exact block_0041
            · by_cases h_42_45 : i.val < 43
              · have heq : i = Fin.ofNat 208 42 := Fin.ext (by change i.val = 42; omega)
                subst i
                exact block_0042
              · by_cases h_43_45 : i.val < 44
                · have heq : i = Fin.ofNat 208 43 := Fin.ext (by change i.val = 43; omega)
                  subst i
                  exact block_0043
                · have heq : i = Fin.ofNat 208 44 := Fin.ext (by change i.val = 44; omega)
                  subst i
                  exact block_0044
          · by_cases h_45_52 : i.val < 48
            · by_cases h_45_48 : i.val < 46
              · have heq : i = Fin.ofNat 208 45 := Fin.ext (by change i.val = 45; omega)
                subst i
                exact block_0045
              · by_cases h_46_48 : i.val < 47
                · have heq : i = Fin.ofNat 208 46 := Fin.ext (by change i.val = 46; omega)
                  subst i
                  exact block_0046
                · have heq : i = Fin.ofNat 208 47 := Fin.ext (by change i.val = 47; omega)
                  subst i
                  exact block_0047
            · by_cases h_48_52 : i.val < 50
              · by_cases h_48_50 : i.val < 49
                · have heq : i = Fin.ofNat 208 48 := Fin.ext (by change i.val = 48; omega)
                  subst i
                  exact block_0048
                · have heq : i = Fin.ofNat 208 49 := Fin.ext (by change i.val = 49; omega)
                  subst i
                  exact block_0049
              · by_cases h_50_52 : i.val < 51
                · have heq : i = Fin.ofNat 208 50 := Fin.ext (by change i.val = 50; omega)
                  subst i
                  exact block_0050
                · have heq : i = Fin.ofNat 208 51 := Fin.ext (by change i.val = 51; omega)
                  subst i
                  exact block_0051
    · by_cases h_52_104 : i.val < 78
      · by_cases h_52_78 : i.val < 65
        · by_cases h_52_65 : i.val < 58
          · by_cases h_52_58 : i.val < 55
            · by_cases h_52_55 : i.val < 53
              · have heq : i = Fin.ofNat 208 52 := Fin.ext (by change i.val = 52; omega)
                subst i
                exact block_0052
              · by_cases h_53_55 : i.val < 54
                · have heq : i = Fin.ofNat 208 53 := Fin.ext (by change i.val = 53; omega)
                  subst i
                  exact block_0053
                · have heq : i = Fin.ofNat 208 54 := Fin.ext (by change i.val = 54; omega)
                  subst i
                  exact block_0054
            · by_cases h_55_58 : i.val < 56
              · have heq : i = Fin.ofNat 208 55 := Fin.ext (by change i.val = 55; omega)
                subst i
                exact block_0055
              · by_cases h_56_58 : i.val < 57
                · have heq : i = Fin.ofNat 208 56 := Fin.ext (by change i.val = 56; omega)
                  subst i
                  exact block_0056
                · have heq : i = Fin.ofNat 208 57 := Fin.ext (by change i.val = 57; omega)
                  subst i
                  exact block_0057
          · by_cases h_58_65 : i.val < 61
            · by_cases h_58_61 : i.val < 59
              · have heq : i = Fin.ofNat 208 58 := Fin.ext (by change i.val = 58; omega)
                subst i
                exact block_0058
              · by_cases h_59_61 : i.val < 60
                · have heq : i = Fin.ofNat 208 59 := Fin.ext (by change i.val = 59; omega)
                  subst i
                  exact block_0059
                · have heq : i = Fin.ofNat 208 60 := Fin.ext (by change i.val = 60; omega)
                  subst i
                  exact block_0060
            · by_cases h_61_65 : i.val < 63
              · by_cases h_61_63 : i.val < 62
                · have heq : i = Fin.ofNat 208 61 := Fin.ext (by change i.val = 61; omega)
                  subst i
                  exact block_0061
                · have heq : i = Fin.ofNat 208 62 := Fin.ext (by change i.val = 62; omega)
                  subst i
                  exact block_0062
              · by_cases h_63_65 : i.val < 64
                · have heq : i = Fin.ofNat 208 63 := Fin.ext (by change i.val = 63; omega)
                  subst i
                  exact block_0063
                · have heq : i = Fin.ofNat 208 64 := Fin.ext (by change i.val = 64; omega)
                  subst i
                  exact block_0064
        · by_cases h_65_78 : i.val < 71
          · by_cases h_65_71 : i.val < 68
            · by_cases h_65_68 : i.val < 66
              · have heq : i = Fin.ofNat 208 65 := Fin.ext (by change i.val = 65; omega)
                subst i
                exact block_0065
              · by_cases h_66_68 : i.val < 67
                · have heq : i = Fin.ofNat 208 66 := Fin.ext (by change i.val = 66; omega)
                  subst i
                  exact block_0066
                · have heq : i = Fin.ofNat 208 67 := Fin.ext (by change i.val = 67; omega)
                  subst i
                  exact block_0067
            · by_cases h_68_71 : i.val < 69
              · have heq : i = Fin.ofNat 208 68 := Fin.ext (by change i.val = 68; omega)
                subst i
                exact block_0068
              · by_cases h_69_71 : i.val < 70
                · have heq : i = Fin.ofNat 208 69 := Fin.ext (by change i.val = 69; omega)
                  subst i
                  exact block_0069
                · have heq : i = Fin.ofNat 208 70 := Fin.ext (by change i.val = 70; omega)
                  subst i
                  exact block_0070
          · by_cases h_71_78 : i.val < 74
            · by_cases h_71_74 : i.val < 72
              · have heq : i = Fin.ofNat 208 71 := Fin.ext (by change i.val = 71; omega)
                subst i
                exact block_0071
              · by_cases h_72_74 : i.val < 73
                · have heq : i = Fin.ofNat 208 72 := Fin.ext (by change i.val = 72; omega)
                  subst i
                  exact block_0072
                · have heq : i = Fin.ofNat 208 73 := Fin.ext (by change i.val = 73; omega)
                  subst i
                  exact block_0073
            · by_cases h_74_78 : i.val < 76
              · by_cases h_74_76 : i.val < 75
                · have heq : i = Fin.ofNat 208 74 := Fin.ext (by change i.val = 74; omega)
                  subst i
                  exact block_0074
                · have heq : i = Fin.ofNat 208 75 := Fin.ext (by change i.val = 75; omega)
                  subst i
                  exact block_0075
              · by_cases h_76_78 : i.val < 77
                · have heq : i = Fin.ofNat 208 76 := Fin.ext (by change i.val = 76; omega)
                  subst i
                  exact block_0076
                · have heq : i = Fin.ofNat 208 77 := Fin.ext (by change i.val = 77; omega)
                  subst i
                  exact block_0077
      · by_cases h_78_104 : i.val < 91
        · by_cases h_78_91 : i.val < 84
          · by_cases h_78_84 : i.val < 81
            · by_cases h_78_81 : i.val < 79
              · have heq : i = Fin.ofNat 208 78 := Fin.ext (by change i.val = 78; omega)
                subst i
                exact block_0078
              · by_cases h_79_81 : i.val < 80
                · have heq : i = Fin.ofNat 208 79 := Fin.ext (by change i.val = 79; omega)
                  subst i
                  exact block_0079
                · have heq : i = Fin.ofNat 208 80 := Fin.ext (by change i.val = 80; omega)
                  subst i
                  exact block_0080
            · by_cases h_81_84 : i.val < 82
              · have heq : i = Fin.ofNat 208 81 := Fin.ext (by change i.val = 81; omega)
                subst i
                exact block_0081
              · by_cases h_82_84 : i.val < 83
                · have heq : i = Fin.ofNat 208 82 := Fin.ext (by change i.val = 82; omega)
                  subst i
                  exact block_0082
                · have heq : i = Fin.ofNat 208 83 := Fin.ext (by change i.val = 83; omega)
                  subst i
                  exact block_0083
          · by_cases h_84_91 : i.val < 87
            · by_cases h_84_87 : i.val < 85
              · have heq : i = Fin.ofNat 208 84 := Fin.ext (by change i.val = 84; omega)
                subst i
                exact block_0084
              · by_cases h_85_87 : i.val < 86
                · have heq : i = Fin.ofNat 208 85 := Fin.ext (by change i.val = 85; omega)
                  subst i
                  exact block_0085
                · have heq : i = Fin.ofNat 208 86 := Fin.ext (by change i.val = 86; omega)
                  subst i
                  exact block_0086
            · by_cases h_87_91 : i.val < 89
              · by_cases h_87_89 : i.val < 88
                · have heq : i = Fin.ofNat 208 87 := Fin.ext (by change i.val = 87; omega)
                  subst i
                  exact block_0087
                · have heq : i = Fin.ofNat 208 88 := Fin.ext (by change i.val = 88; omega)
                  subst i
                  exact block_0088
              · by_cases h_89_91 : i.val < 90
                · have heq : i = Fin.ofNat 208 89 := Fin.ext (by change i.val = 89; omega)
                  subst i
                  exact block_0089
                · have heq : i = Fin.ofNat 208 90 := Fin.ext (by change i.val = 90; omega)
                  subst i
                  exact block_0090
        · by_cases h_91_104 : i.val < 97
          · by_cases h_91_97 : i.val < 94
            · by_cases h_91_94 : i.val < 92
              · have heq : i = Fin.ofNat 208 91 := Fin.ext (by change i.val = 91; omega)
                subst i
                exact block_0091
              · by_cases h_92_94 : i.val < 93
                · have heq : i = Fin.ofNat 208 92 := Fin.ext (by change i.val = 92; omega)
                  subst i
                  exact block_0092
                · have heq : i = Fin.ofNat 208 93 := Fin.ext (by change i.val = 93; omega)
                  subst i
                  exact block_0093
            · by_cases h_94_97 : i.val < 95
              · have heq : i = Fin.ofNat 208 94 := Fin.ext (by change i.val = 94; omega)
                subst i
                exact block_0094
              · by_cases h_95_97 : i.val < 96
                · have heq : i = Fin.ofNat 208 95 := Fin.ext (by change i.val = 95; omega)
                  subst i
                  exact block_0095
                · have heq : i = Fin.ofNat 208 96 := Fin.ext (by change i.val = 96; omega)
                  subst i
                  exact block_0096
          · by_cases h_97_104 : i.val < 100
            · by_cases h_97_100 : i.val < 98
              · have heq : i = Fin.ofNat 208 97 := Fin.ext (by change i.val = 97; omega)
                subst i
                exact block_0097
              · by_cases h_98_100 : i.val < 99
                · have heq : i = Fin.ofNat 208 98 := Fin.ext (by change i.val = 98; omega)
                  subst i
                  exact block_0098
                · have heq : i = Fin.ofNat 208 99 := Fin.ext (by change i.val = 99; omega)
                  subst i
                  exact block_0099
            · by_cases h_100_104 : i.val < 102
              · by_cases h_100_102 : i.val < 101
                · have heq : i = Fin.ofNat 208 100 := Fin.ext (by change i.val = 100; omega)
                  subst i
                  exact block_0100
                · have heq : i = Fin.ofNat 208 101 := Fin.ext (by change i.val = 101; omega)
                  subst i
                  exact block_0101
              · by_cases h_102_104 : i.val < 103
                · have heq : i = Fin.ofNat 208 102 := Fin.ext (by change i.val = 102; omega)
                  subst i
                  exact block_0102
                · have heq : i = Fin.ofNat 208 103 := Fin.ext (by change i.val = 103; omega)
                  subst i
                  exact block_0103
  · by_cases h_104_208 : i.val < 156
    · by_cases h_104_156 : i.val < 130
      · by_cases h_104_130 : i.val < 117
        · by_cases h_104_117 : i.val < 110
          · by_cases h_104_110 : i.val < 107
            · by_cases h_104_107 : i.val < 105
              · have heq : i = Fin.ofNat 208 104 := Fin.ext (by change i.val = 104; omega)
                subst i
                exact block_0104
              · by_cases h_105_107 : i.val < 106
                · have heq : i = Fin.ofNat 208 105 := Fin.ext (by change i.val = 105; omega)
                  subst i
                  exact block_0105
                · have heq : i = Fin.ofNat 208 106 := Fin.ext (by change i.val = 106; omega)
                  subst i
                  exact block_0106
            · by_cases h_107_110 : i.val < 108
              · have heq : i = Fin.ofNat 208 107 := Fin.ext (by change i.val = 107; omega)
                subst i
                exact block_0107
              · by_cases h_108_110 : i.val < 109
                · have heq : i = Fin.ofNat 208 108 := Fin.ext (by change i.val = 108; omega)
                  subst i
                  exact block_0108
                · have heq : i = Fin.ofNat 208 109 := Fin.ext (by change i.val = 109; omega)
                  subst i
                  exact block_0109
          · by_cases h_110_117 : i.val < 113
            · by_cases h_110_113 : i.val < 111
              · have heq : i = Fin.ofNat 208 110 := Fin.ext (by change i.val = 110; omega)
                subst i
                exact block_0110
              · by_cases h_111_113 : i.val < 112
                · have heq : i = Fin.ofNat 208 111 := Fin.ext (by change i.val = 111; omega)
                  subst i
                  exact block_0111
                · have heq : i = Fin.ofNat 208 112 := Fin.ext (by change i.val = 112; omega)
                  subst i
                  exact block_0112
            · by_cases h_113_117 : i.val < 115
              · by_cases h_113_115 : i.val < 114
                · have heq : i = Fin.ofNat 208 113 := Fin.ext (by change i.val = 113; omega)
                  subst i
                  exact block_0113
                · have heq : i = Fin.ofNat 208 114 := Fin.ext (by change i.val = 114; omega)
                  subst i
                  exact block_0114
              · by_cases h_115_117 : i.val < 116
                · have heq : i = Fin.ofNat 208 115 := Fin.ext (by change i.val = 115; omega)
                  subst i
                  exact block_0115
                · have heq : i = Fin.ofNat 208 116 := Fin.ext (by change i.val = 116; omega)
                  subst i
                  exact block_0116
        · by_cases h_117_130 : i.val < 123
          · by_cases h_117_123 : i.val < 120
            · by_cases h_117_120 : i.val < 118
              · have heq : i = Fin.ofNat 208 117 := Fin.ext (by change i.val = 117; omega)
                subst i
                exact block_0117
              · by_cases h_118_120 : i.val < 119
                · have heq : i = Fin.ofNat 208 118 := Fin.ext (by change i.val = 118; omega)
                  subst i
                  exact block_0118
                · have heq : i = Fin.ofNat 208 119 := Fin.ext (by change i.val = 119; omega)
                  subst i
                  exact block_0119
            · by_cases h_120_123 : i.val < 121
              · have heq : i = Fin.ofNat 208 120 := Fin.ext (by change i.val = 120; omega)
                subst i
                exact block_0120
              · by_cases h_121_123 : i.val < 122
                · have heq : i = Fin.ofNat 208 121 := Fin.ext (by change i.val = 121; omega)
                  subst i
                  exact block_0121
                · have heq : i = Fin.ofNat 208 122 := Fin.ext (by change i.val = 122; omega)
                  subst i
                  exact block_0122
          · by_cases h_123_130 : i.val < 126
            · by_cases h_123_126 : i.val < 124
              · have heq : i = Fin.ofNat 208 123 := Fin.ext (by change i.val = 123; omega)
                subst i
                exact block_0123
              · by_cases h_124_126 : i.val < 125
                · have heq : i = Fin.ofNat 208 124 := Fin.ext (by change i.val = 124; omega)
                  subst i
                  exact block_0124
                · have heq : i = Fin.ofNat 208 125 := Fin.ext (by change i.val = 125; omega)
                  subst i
                  exact block_0125
            · by_cases h_126_130 : i.val < 128
              · by_cases h_126_128 : i.val < 127
                · have heq : i = Fin.ofNat 208 126 := Fin.ext (by change i.val = 126; omega)
                  subst i
                  exact block_0126
                · have heq : i = Fin.ofNat 208 127 := Fin.ext (by change i.val = 127; omega)
                  subst i
                  exact block_0127
              · by_cases h_128_130 : i.val < 129
                · have heq : i = Fin.ofNat 208 128 := Fin.ext (by change i.val = 128; omega)
                  subst i
                  exact block_0128
                · have heq : i = Fin.ofNat 208 129 := Fin.ext (by change i.val = 129; omega)
                  subst i
                  exact block_0129
      · by_cases h_130_156 : i.val < 143
        · by_cases h_130_143 : i.val < 136
          · by_cases h_130_136 : i.val < 133
            · by_cases h_130_133 : i.val < 131
              · have heq : i = Fin.ofNat 208 130 := Fin.ext (by change i.val = 130; omega)
                subst i
                exact block_0130
              · by_cases h_131_133 : i.val < 132
                · have heq : i = Fin.ofNat 208 131 := Fin.ext (by change i.val = 131; omega)
                  subst i
                  exact block_0131
                · have heq : i = Fin.ofNat 208 132 := Fin.ext (by change i.val = 132; omega)
                  subst i
                  exact block_0132
            · by_cases h_133_136 : i.val < 134
              · have heq : i = Fin.ofNat 208 133 := Fin.ext (by change i.val = 133; omega)
                subst i
                exact block_0133
              · by_cases h_134_136 : i.val < 135
                · have heq : i = Fin.ofNat 208 134 := Fin.ext (by change i.val = 134; omega)
                  subst i
                  exact block_0134
                · have heq : i = Fin.ofNat 208 135 := Fin.ext (by change i.val = 135; omega)
                  subst i
                  exact block_0135
          · by_cases h_136_143 : i.val < 139
            · by_cases h_136_139 : i.val < 137
              · have heq : i = Fin.ofNat 208 136 := Fin.ext (by change i.val = 136; omega)
                subst i
                exact block_0136
              · by_cases h_137_139 : i.val < 138
                · have heq : i = Fin.ofNat 208 137 := Fin.ext (by change i.val = 137; omega)
                  subst i
                  exact block_0137
                · have heq : i = Fin.ofNat 208 138 := Fin.ext (by change i.val = 138; omega)
                  subst i
                  exact block_0138
            · by_cases h_139_143 : i.val < 141
              · by_cases h_139_141 : i.val < 140
                · have heq : i = Fin.ofNat 208 139 := Fin.ext (by change i.val = 139; omega)
                  subst i
                  exact block_0139
                · have heq : i = Fin.ofNat 208 140 := Fin.ext (by change i.val = 140; omega)
                  subst i
                  exact block_0140
              · by_cases h_141_143 : i.val < 142
                · have heq : i = Fin.ofNat 208 141 := Fin.ext (by change i.val = 141; omega)
                  subst i
                  exact block_0141
                · have heq : i = Fin.ofNat 208 142 := Fin.ext (by change i.val = 142; omega)
                  subst i
                  exact block_0142
        · by_cases h_143_156 : i.val < 149
          · by_cases h_143_149 : i.val < 146
            · by_cases h_143_146 : i.val < 144
              · have heq : i = Fin.ofNat 208 143 := Fin.ext (by change i.val = 143; omega)
                subst i
                exact block_0143
              · by_cases h_144_146 : i.val < 145
                · have heq : i = Fin.ofNat 208 144 := Fin.ext (by change i.val = 144; omega)
                  subst i
                  exact block_0144
                · have heq : i = Fin.ofNat 208 145 := Fin.ext (by change i.val = 145; omega)
                  subst i
                  exact block_0145
            · by_cases h_146_149 : i.val < 147
              · have heq : i = Fin.ofNat 208 146 := Fin.ext (by change i.val = 146; omega)
                subst i
                exact block_0146
              · by_cases h_147_149 : i.val < 148
                · have heq : i = Fin.ofNat 208 147 := Fin.ext (by change i.val = 147; omega)
                  subst i
                  exact block_0147
                · have heq : i = Fin.ofNat 208 148 := Fin.ext (by change i.val = 148; omega)
                  subst i
                  exact block_0148
          · by_cases h_149_156 : i.val < 152
            · by_cases h_149_152 : i.val < 150
              · have heq : i = Fin.ofNat 208 149 := Fin.ext (by change i.val = 149; omega)
                subst i
                exact block_0149
              · by_cases h_150_152 : i.val < 151
                · have heq : i = Fin.ofNat 208 150 := Fin.ext (by change i.val = 150; omega)
                  subst i
                  exact block_0150
                · have heq : i = Fin.ofNat 208 151 := Fin.ext (by change i.val = 151; omega)
                  subst i
                  exact block_0151
            · by_cases h_152_156 : i.val < 154
              · by_cases h_152_154 : i.val < 153
                · have heq : i = Fin.ofNat 208 152 := Fin.ext (by change i.val = 152; omega)
                  subst i
                  exact block_0152
                · have heq : i = Fin.ofNat 208 153 := Fin.ext (by change i.val = 153; omega)
                  subst i
                  exact block_0153
              · by_cases h_154_156 : i.val < 155
                · have heq : i = Fin.ofNat 208 154 := Fin.ext (by change i.val = 154; omega)
                  subst i
                  exact block_0154
                · have heq : i = Fin.ofNat 208 155 := Fin.ext (by change i.val = 155; omega)
                  subst i
                  exact block_0155
    · by_cases h_156_208 : i.val < 182
      · by_cases h_156_182 : i.val < 169
        · by_cases h_156_169 : i.val < 162
          · by_cases h_156_162 : i.val < 159
            · by_cases h_156_159 : i.val < 157
              · have heq : i = Fin.ofNat 208 156 := Fin.ext (by change i.val = 156; omega)
                subst i
                exact block_0156
              · by_cases h_157_159 : i.val < 158
                · have heq : i = Fin.ofNat 208 157 := Fin.ext (by change i.val = 157; omega)
                  subst i
                  exact block_0157
                · have heq : i = Fin.ofNat 208 158 := Fin.ext (by change i.val = 158; omega)
                  subst i
                  exact block_0158
            · by_cases h_159_162 : i.val < 160
              · have heq : i = Fin.ofNat 208 159 := Fin.ext (by change i.val = 159; omega)
                subst i
                exact block_0159
              · by_cases h_160_162 : i.val < 161
                · have heq : i = Fin.ofNat 208 160 := Fin.ext (by change i.val = 160; omega)
                  subst i
                  exact block_0160
                · have heq : i = Fin.ofNat 208 161 := Fin.ext (by change i.val = 161; omega)
                  subst i
                  exact block_0161
          · by_cases h_162_169 : i.val < 165
            · by_cases h_162_165 : i.val < 163
              · have heq : i = Fin.ofNat 208 162 := Fin.ext (by change i.val = 162; omega)
                subst i
                exact block_0162
              · by_cases h_163_165 : i.val < 164
                · have heq : i = Fin.ofNat 208 163 := Fin.ext (by change i.val = 163; omega)
                  subst i
                  exact block_0163
                · have heq : i = Fin.ofNat 208 164 := Fin.ext (by change i.val = 164; omega)
                  subst i
                  exact block_0164
            · by_cases h_165_169 : i.val < 167
              · by_cases h_165_167 : i.val < 166
                · have heq : i = Fin.ofNat 208 165 := Fin.ext (by change i.val = 165; omega)
                  subst i
                  exact block_0165
                · have heq : i = Fin.ofNat 208 166 := Fin.ext (by change i.val = 166; omega)
                  subst i
                  exact block_0166
              · by_cases h_167_169 : i.val < 168
                · have heq : i = Fin.ofNat 208 167 := Fin.ext (by change i.val = 167; omega)
                  subst i
                  exact block_0167
                · have heq : i = Fin.ofNat 208 168 := Fin.ext (by change i.val = 168; omega)
                  subst i
                  exact block_0168
        · by_cases h_169_182 : i.val < 175
          · by_cases h_169_175 : i.val < 172
            · by_cases h_169_172 : i.val < 170
              · have heq : i = Fin.ofNat 208 169 := Fin.ext (by change i.val = 169; omega)
                subst i
                exact block_0169
              · by_cases h_170_172 : i.val < 171
                · have heq : i = Fin.ofNat 208 170 := Fin.ext (by change i.val = 170; omega)
                  subst i
                  exact block_0170
                · have heq : i = Fin.ofNat 208 171 := Fin.ext (by change i.val = 171; omega)
                  subst i
                  exact block_0171
            · by_cases h_172_175 : i.val < 173
              · have heq : i = Fin.ofNat 208 172 := Fin.ext (by change i.val = 172; omega)
                subst i
                exact block_0172
              · by_cases h_173_175 : i.val < 174
                · have heq : i = Fin.ofNat 208 173 := Fin.ext (by change i.val = 173; omega)
                  subst i
                  exact block_0173
                · have heq : i = Fin.ofNat 208 174 := Fin.ext (by change i.val = 174; omega)
                  subst i
                  exact block_0174
          · by_cases h_175_182 : i.val < 178
            · by_cases h_175_178 : i.val < 176
              · have heq : i = Fin.ofNat 208 175 := Fin.ext (by change i.val = 175; omega)
                subst i
                exact block_0175
              · by_cases h_176_178 : i.val < 177
                · have heq : i = Fin.ofNat 208 176 := Fin.ext (by change i.val = 176; omega)
                  subst i
                  exact block_0176
                · have heq : i = Fin.ofNat 208 177 := Fin.ext (by change i.val = 177; omega)
                  subst i
                  exact block_0177
            · by_cases h_178_182 : i.val < 180
              · by_cases h_178_180 : i.val < 179
                · have heq : i = Fin.ofNat 208 178 := Fin.ext (by change i.val = 178; omega)
                  subst i
                  exact block_0178
                · have heq : i = Fin.ofNat 208 179 := Fin.ext (by change i.val = 179; omega)
                  subst i
                  exact block_0179
              · by_cases h_180_182 : i.val < 181
                · have heq : i = Fin.ofNat 208 180 := Fin.ext (by change i.val = 180; omega)
                  subst i
                  exact block_0180
                · have heq : i = Fin.ofNat 208 181 := Fin.ext (by change i.val = 181; omega)
                  subst i
                  exact block_0181
      · by_cases h_182_208 : i.val < 195
        · by_cases h_182_195 : i.val < 188
          · by_cases h_182_188 : i.val < 185
            · by_cases h_182_185 : i.val < 183
              · have heq : i = Fin.ofNat 208 182 := Fin.ext (by change i.val = 182; omega)
                subst i
                exact block_0182
              · by_cases h_183_185 : i.val < 184
                · have heq : i = Fin.ofNat 208 183 := Fin.ext (by change i.val = 183; omega)
                  subst i
                  exact block_0183
                · have heq : i = Fin.ofNat 208 184 := Fin.ext (by change i.val = 184; omega)
                  subst i
                  exact block_0184
            · by_cases h_185_188 : i.val < 186
              · have heq : i = Fin.ofNat 208 185 := Fin.ext (by change i.val = 185; omega)
                subst i
                exact block_0185
              · by_cases h_186_188 : i.val < 187
                · have heq : i = Fin.ofNat 208 186 := Fin.ext (by change i.val = 186; omega)
                  subst i
                  exact block_0186
                · have heq : i = Fin.ofNat 208 187 := Fin.ext (by change i.val = 187; omega)
                  subst i
                  exact block_0187
          · by_cases h_188_195 : i.val < 191
            · by_cases h_188_191 : i.val < 189
              · have heq : i = Fin.ofNat 208 188 := Fin.ext (by change i.val = 188; omega)
                subst i
                exact block_0188
              · by_cases h_189_191 : i.val < 190
                · have heq : i = Fin.ofNat 208 189 := Fin.ext (by change i.val = 189; omega)
                  subst i
                  exact block_0189
                · have heq : i = Fin.ofNat 208 190 := Fin.ext (by change i.val = 190; omega)
                  subst i
                  exact block_0190
            · by_cases h_191_195 : i.val < 193
              · by_cases h_191_193 : i.val < 192
                · have heq : i = Fin.ofNat 208 191 := Fin.ext (by change i.val = 191; omega)
                  subst i
                  exact block_0191
                · have heq : i = Fin.ofNat 208 192 := Fin.ext (by change i.val = 192; omega)
                  subst i
                  exact block_0192
              · by_cases h_193_195 : i.val < 194
                · have heq : i = Fin.ofNat 208 193 := Fin.ext (by change i.val = 193; omega)
                  subst i
                  exact block_0193
                · have heq : i = Fin.ofNat 208 194 := Fin.ext (by change i.val = 194; omega)
                  subst i
                  exact block_0194
        · by_cases h_195_208 : i.val < 201
          · by_cases h_195_201 : i.val < 198
            · by_cases h_195_198 : i.val < 196
              · have heq : i = Fin.ofNat 208 195 := Fin.ext (by change i.val = 195; omega)
                subst i
                exact block_0195
              · by_cases h_196_198 : i.val < 197
                · have heq : i = Fin.ofNat 208 196 := Fin.ext (by change i.val = 196; omega)
                  subst i
                  exact block_0196
                · have heq : i = Fin.ofNat 208 197 := Fin.ext (by change i.val = 197; omega)
                  subst i
                  exact block_0197
            · by_cases h_198_201 : i.val < 199
              · have heq : i = Fin.ofNat 208 198 := Fin.ext (by change i.val = 198; omega)
                subst i
                exact block_0198
              · by_cases h_199_201 : i.val < 200
                · have heq : i = Fin.ofNat 208 199 := Fin.ext (by change i.val = 199; omega)
                  subst i
                  exact block_0199
                · have heq : i = Fin.ofNat 208 200 := Fin.ext (by change i.val = 200; omega)
                  subst i
                  exact block_0200
          · by_cases h_201_208 : i.val < 204
            · by_cases h_201_204 : i.val < 202
              · have heq : i = Fin.ofNat 208 201 := Fin.ext (by change i.val = 201; omega)
                subst i
                exact block_0201
              · by_cases h_202_204 : i.val < 203
                · have heq : i = Fin.ofNat 208 202 := Fin.ext (by change i.val = 202; omega)
                  subst i
                  exact block_0202
                · have heq : i = Fin.ofNat 208 203 := Fin.ext (by change i.val = 203; omega)
                  subst i
                  exact block_0203
            · by_cases h_204_208 : i.val < 206
              · by_cases h_204_206 : i.val < 205
                · have heq : i = Fin.ofNat 208 204 := Fin.ext (by change i.val = 204; omega)
                  subst i
                  exact block_0204
                · have heq : i = Fin.ofNat 208 205 := Fin.ext (by change i.val = 205; omega)
                  subst i
                  exact block_0205
              · by_cases h_206_208 : i.val < 207
                · have heq : i = Fin.ofNat 208 206 := Fin.ext (by change i.val = 206; omega)
                  subst i
                  exact block_0206
                · have heq : i = Fin.ofNat 208 207 := Fin.ext (by change i.val = 207; omega)
                  subst i
                  exact block_0207
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.T0
