module
prelude
public import RootedSixExtra03CanonicalS5T0Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra03.S5T0
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 5 (raw i) template root
      FacetUniverses.RootedSixExtra03.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 165 := i.isLt
  by_cases h_0_165 : i.val < 82
  · by_cases h_0_82 : i.val < 41
    · by_cases h_0_41 : i.val < 20
      · by_cases h_0_20 : i.val < 10
        · by_cases h_0_10 : i.val < 5
          · by_cases h_0_5 : i.val < 2
            · by_cases h_0_2 : i.val < 1
              · have heq : i = Fin.ofNat 165 0 := Fin.ext (by change i.val = 0; omega)
                subst i
                exact block_0000
              · have heq : i = Fin.ofNat 165 1 := Fin.ext (by change i.val = 1; omega)
                subst i
                exact block_0001
            · by_cases h_2_5 : i.val < 3
              · have heq : i = Fin.ofNat 165 2 := Fin.ext (by change i.val = 2; omega)
                subst i
                exact block_0002
              · by_cases h_3_5 : i.val < 4
                · have heq : i = Fin.ofNat 165 3 := Fin.ext (by change i.val = 3; omega)
                  subst i
                  exact block_0003
                · have heq : i = Fin.ofNat 165 4 := Fin.ext (by change i.val = 4; omega)
                  subst i
                  exact block_0004
          · by_cases h_5_10 : i.val < 7
            · by_cases h_5_7 : i.val < 6
              · have heq : i = Fin.ofNat 165 5 := Fin.ext (by change i.val = 5; omega)
                subst i
                exact block_0005
              · have heq : i = Fin.ofNat 165 6 := Fin.ext (by change i.val = 6; omega)
                subst i
                exact block_0006
            · by_cases h_7_10 : i.val < 8
              · have heq : i = Fin.ofNat 165 7 := Fin.ext (by change i.val = 7; omega)
                subst i
                exact block_0007
              · by_cases h_8_10 : i.val < 9
                · have heq : i = Fin.ofNat 165 8 := Fin.ext (by change i.val = 8; omega)
                  subst i
                  exact block_0008
                · have heq : i = Fin.ofNat 165 9 := Fin.ext (by change i.val = 9; omega)
                  subst i
                  exact block_0009
        · by_cases h_10_20 : i.val < 15
          · by_cases h_10_15 : i.val < 12
            · by_cases h_10_12 : i.val < 11
              · have heq : i = Fin.ofNat 165 10 := Fin.ext (by change i.val = 10; omega)
                subst i
                exact block_0010
              · have heq : i = Fin.ofNat 165 11 := Fin.ext (by change i.val = 11; omega)
                subst i
                exact block_0011
            · by_cases h_12_15 : i.val < 13
              · have heq : i = Fin.ofNat 165 12 := Fin.ext (by change i.val = 12; omega)
                subst i
                exact block_0012
              · by_cases h_13_15 : i.val < 14
                · have heq : i = Fin.ofNat 165 13 := Fin.ext (by change i.val = 13; omega)
                  subst i
                  exact block_0013
                · have heq : i = Fin.ofNat 165 14 := Fin.ext (by change i.val = 14; omega)
                  subst i
                  exact block_0014
          · by_cases h_15_20 : i.val < 17
            · by_cases h_15_17 : i.val < 16
              · have heq : i = Fin.ofNat 165 15 := Fin.ext (by change i.val = 15; omega)
                subst i
                exact block_0015
              · have heq : i = Fin.ofNat 165 16 := Fin.ext (by change i.val = 16; omega)
                subst i
                exact block_0016
            · by_cases h_17_20 : i.val < 18
              · have heq : i = Fin.ofNat 165 17 := Fin.ext (by change i.val = 17; omega)
                subst i
                exact block_0017
              · by_cases h_18_20 : i.val < 19
                · have heq : i = Fin.ofNat 165 18 := Fin.ext (by change i.val = 18; omega)
                  subst i
                  exact block_0018
                · have heq : i = Fin.ofNat 165 19 := Fin.ext (by change i.val = 19; omega)
                  subst i
                  exact block_0019
      · by_cases h_20_41 : i.val < 30
        · by_cases h_20_30 : i.val < 25
          · by_cases h_20_25 : i.val < 22
            · by_cases h_20_22 : i.val < 21
              · have heq : i = Fin.ofNat 165 20 := Fin.ext (by change i.val = 20; omega)
                subst i
                exact block_0020
              · have heq : i = Fin.ofNat 165 21 := Fin.ext (by change i.val = 21; omega)
                subst i
                exact block_0021
            · by_cases h_22_25 : i.val < 23
              · have heq : i = Fin.ofNat 165 22 := Fin.ext (by change i.val = 22; omega)
                subst i
                exact block_0022
              · by_cases h_23_25 : i.val < 24
                · have heq : i = Fin.ofNat 165 23 := Fin.ext (by change i.val = 23; omega)
                  subst i
                  exact block_0023
                · have heq : i = Fin.ofNat 165 24 := Fin.ext (by change i.val = 24; omega)
                  subst i
                  exact block_0024
          · by_cases h_25_30 : i.val < 27
            · by_cases h_25_27 : i.val < 26
              · have heq : i = Fin.ofNat 165 25 := Fin.ext (by change i.val = 25; omega)
                subst i
                exact block_0025
              · have heq : i = Fin.ofNat 165 26 := Fin.ext (by change i.val = 26; omega)
                subst i
                exact block_0026
            · by_cases h_27_30 : i.val < 28
              · have heq : i = Fin.ofNat 165 27 := Fin.ext (by change i.val = 27; omega)
                subst i
                exact block_0027
              · by_cases h_28_30 : i.val < 29
                · have heq : i = Fin.ofNat 165 28 := Fin.ext (by change i.val = 28; omega)
                  subst i
                  exact block_0028
                · have heq : i = Fin.ofNat 165 29 := Fin.ext (by change i.val = 29; omega)
                  subst i
                  exact block_0029
        · by_cases h_30_41 : i.val < 35
          · by_cases h_30_35 : i.val < 32
            · by_cases h_30_32 : i.val < 31
              · have heq : i = Fin.ofNat 165 30 := Fin.ext (by change i.val = 30; omega)
                subst i
                exact block_0030
              · have heq : i = Fin.ofNat 165 31 := Fin.ext (by change i.val = 31; omega)
                subst i
                exact block_0031
            · by_cases h_32_35 : i.val < 33
              · have heq : i = Fin.ofNat 165 32 := Fin.ext (by change i.val = 32; omega)
                subst i
                exact block_0032
              · by_cases h_33_35 : i.val < 34
                · have heq : i = Fin.ofNat 165 33 := Fin.ext (by change i.val = 33; omega)
                  subst i
                  exact block_0033
                · have heq : i = Fin.ofNat 165 34 := Fin.ext (by change i.val = 34; omega)
                  subst i
                  exact block_0034
          · by_cases h_35_41 : i.val < 38
            · by_cases h_35_38 : i.val < 36
              · have heq : i = Fin.ofNat 165 35 := Fin.ext (by change i.val = 35; omega)
                subst i
                exact block_0035
              · by_cases h_36_38 : i.val < 37
                · have heq : i = Fin.ofNat 165 36 := Fin.ext (by change i.val = 36; omega)
                  subst i
                  exact block_0036
                · have heq : i = Fin.ofNat 165 37 := Fin.ext (by change i.val = 37; omega)
                  subst i
                  exact block_0037
            · by_cases h_38_41 : i.val < 39
              · have heq : i = Fin.ofNat 165 38 := Fin.ext (by change i.val = 38; omega)
                subst i
                exact block_0038
              · by_cases h_39_41 : i.val < 40
                · have heq : i = Fin.ofNat 165 39 := Fin.ext (by change i.val = 39; omega)
                  subst i
                  exact block_0039
                · have heq : i = Fin.ofNat 165 40 := Fin.ext (by change i.val = 40; omega)
                  subst i
                  exact block_0040
    · by_cases h_41_82 : i.val < 61
      · by_cases h_41_61 : i.val < 51
        · by_cases h_41_51 : i.val < 46
          · by_cases h_41_46 : i.val < 43
            · by_cases h_41_43 : i.val < 42
              · have heq : i = Fin.ofNat 165 41 := Fin.ext (by change i.val = 41; omega)
                subst i
                exact block_0041
              · have heq : i = Fin.ofNat 165 42 := Fin.ext (by change i.val = 42; omega)
                subst i
                exact block_0042
            · by_cases h_43_46 : i.val < 44
              · have heq : i = Fin.ofNat 165 43 := Fin.ext (by change i.val = 43; omega)
                subst i
                exact block_0043
              · by_cases h_44_46 : i.val < 45
                · have heq : i = Fin.ofNat 165 44 := Fin.ext (by change i.val = 44; omega)
                  subst i
                  exact block_0044
                · have heq : i = Fin.ofNat 165 45 := Fin.ext (by change i.val = 45; omega)
                  subst i
                  exact block_0045
          · by_cases h_46_51 : i.val < 48
            · by_cases h_46_48 : i.val < 47
              · have heq : i = Fin.ofNat 165 46 := Fin.ext (by change i.val = 46; omega)
                subst i
                exact block_0046
              · have heq : i = Fin.ofNat 165 47 := Fin.ext (by change i.val = 47; omega)
                subst i
                exact block_0047
            · by_cases h_48_51 : i.val < 49
              · have heq : i = Fin.ofNat 165 48 := Fin.ext (by change i.val = 48; omega)
                subst i
                exact block_0048
              · by_cases h_49_51 : i.val < 50
                · have heq : i = Fin.ofNat 165 49 := Fin.ext (by change i.val = 49; omega)
                  subst i
                  exact block_0049
                · have heq : i = Fin.ofNat 165 50 := Fin.ext (by change i.val = 50; omega)
                  subst i
                  exact block_0050
        · by_cases h_51_61 : i.val < 56
          · by_cases h_51_56 : i.val < 53
            · by_cases h_51_53 : i.val < 52
              · have heq : i = Fin.ofNat 165 51 := Fin.ext (by change i.val = 51; omega)
                subst i
                exact block_0051
              · have heq : i = Fin.ofNat 165 52 := Fin.ext (by change i.val = 52; omega)
                subst i
                exact block_0052
            · by_cases h_53_56 : i.val < 54
              · have heq : i = Fin.ofNat 165 53 := Fin.ext (by change i.val = 53; omega)
                subst i
                exact block_0053
              · by_cases h_54_56 : i.val < 55
                · have heq : i = Fin.ofNat 165 54 := Fin.ext (by change i.val = 54; omega)
                  subst i
                  exact block_0054
                · have heq : i = Fin.ofNat 165 55 := Fin.ext (by change i.val = 55; omega)
                  subst i
                  exact block_0055
          · by_cases h_56_61 : i.val < 58
            · by_cases h_56_58 : i.val < 57
              · have heq : i = Fin.ofNat 165 56 := Fin.ext (by change i.val = 56; omega)
                subst i
                exact block_0056
              · have heq : i = Fin.ofNat 165 57 := Fin.ext (by change i.val = 57; omega)
                subst i
                exact block_0057
            · by_cases h_58_61 : i.val < 59
              · have heq : i = Fin.ofNat 165 58 := Fin.ext (by change i.val = 58; omega)
                subst i
                exact block_0058
              · by_cases h_59_61 : i.val < 60
                · have heq : i = Fin.ofNat 165 59 := Fin.ext (by change i.val = 59; omega)
                  subst i
                  exact block_0059
                · have heq : i = Fin.ofNat 165 60 := Fin.ext (by change i.val = 60; omega)
                  subst i
                  exact block_0060
      · by_cases h_61_82 : i.val < 71
        · by_cases h_61_71 : i.val < 66
          · by_cases h_61_66 : i.val < 63
            · by_cases h_61_63 : i.val < 62
              · have heq : i = Fin.ofNat 165 61 := Fin.ext (by change i.val = 61; omega)
                subst i
                exact block_0061
              · have heq : i = Fin.ofNat 165 62 := Fin.ext (by change i.val = 62; omega)
                subst i
                exact block_0062
            · by_cases h_63_66 : i.val < 64
              · have heq : i = Fin.ofNat 165 63 := Fin.ext (by change i.val = 63; omega)
                subst i
                exact block_0063
              · by_cases h_64_66 : i.val < 65
                · have heq : i = Fin.ofNat 165 64 := Fin.ext (by change i.val = 64; omega)
                  subst i
                  exact block_0064
                · have heq : i = Fin.ofNat 165 65 := Fin.ext (by change i.val = 65; omega)
                  subst i
                  exact block_0065
          · by_cases h_66_71 : i.val < 68
            · by_cases h_66_68 : i.val < 67
              · have heq : i = Fin.ofNat 165 66 := Fin.ext (by change i.val = 66; omega)
                subst i
                exact block_0066
              · have heq : i = Fin.ofNat 165 67 := Fin.ext (by change i.val = 67; omega)
                subst i
                exact block_0067
            · by_cases h_68_71 : i.val < 69
              · have heq : i = Fin.ofNat 165 68 := Fin.ext (by change i.val = 68; omega)
                subst i
                exact block_0068
              · by_cases h_69_71 : i.val < 70
                · have heq : i = Fin.ofNat 165 69 := Fin.ext (by change i.val = 69; omega)
                  subst i
                  exact block_0069
                · have heq : i = Fin.ofNat 165 70 := Fin.ext (by change i.val = 70; omega)
                  subst i
                  exact block_0070
        · by_cases h_71_82 : i.val < 76
          · by_cases h_71_76 : i.val < 73
            · by_cases h_71_73 : i.val < 72
              · have heq : i = Fin.ofNat 165 71 := Fin.ext (by change i.val = 71; omega)
                subst i
                exact block_0071
              · have heq : i = Fin.ofNat 165 72 := Fin.ext (by change i.val = 72; omega)
                subst i
                exact block_0072
            · by_cases h_73_76 : i.val < 74
              · have heq : i = Fin.ofNat 165 73 := Fin.ext (by change i.val = 73; omega)
                subst i
                exact block_0073
              · by_cases h_74_76 : i.val < 75
                · have heq : i = Fin.ofNat 165 74 := Fin.ext (by change i.val = 74; omega)
                  subst i
                  exact block_0074
                · have heq : i = Fin.ofNat 165 75 := Fin.ext (by change i.val = 75; omega)
                  subst i
                  exact block_0075
          · by_cases h_76_82 : i.val < 79
            · by_cases h_76_79 : i.val < 77
              · have heq : i = Fin.ofNat 165 76 := Fin.ext (by change i.val = 76; omega)
                subst i
                exact block_0076
              · by_cases h_77_79 : i.val < 78
                · have heq : i = Fin.ofNat 165 77 := Fin.ext (by change i.val = 77; omega)
                  subst i
                  exact block_0077
                · have heq : i = Fin.ofNat 165 78 := Fin.ext (by change i.val = 78; omega)
                  subst i
                  exact block_0078
            · by_cases h_79_82 : i.val < 80
              · have heq : i = Fin.ofNat 165 79 := Fin.ext (by change i.val = 79; omega)
                subst i
                exact block_0079
              · by_cases h_80_82 : i.val < 81
                · have heq : i = Fin.ofNat 165 80 := Fin.ext (by change i.val = 80; omega)
                  subst i
                  exact block_0080
                · have heq : i = Fin.ofNat 165 81 := Fin.ext (by change i.val = 81; omega)
                  subst i
                  exact block_0081
  · by_cases h_82_165 : i.val < 123
    · by_cases h_82_123 : i.val < 102
      · by_cases h_82_102 : i.val < 92
        · by_cases h_82_92 : i.val < 87
          · by_cases h_82_87 : i.val < 84
            · by_cases h_82_84 : i.val < 83
              · have heq : i = Fin.ofNat 165 82 := Fin.ext (by change i.val = 82; omega)
                subst i
                exact block_0082
              · have heq : i = Fin.ofNat 165 83 := Fin.ext (by change i.val = 83; omega)
                subst i
                exact block_0083
            · by_cases h_84_87 : i.val < 85
              · have heq : i = Fin.ofNat 165 84 := Fin.ext (by change i.val = 84; omega)
                subst i
                exact block_0084
              · by_cases h_85_87 : i.val < 86
                · have heq : i = Fin.ofNat 165 85 := Fin.ext (by change i.val = 85; omega)
                  subst i
                  exact block_0085
                · have heq : i = Fin.ofNat 165 86 := Fin.ext (by change i.val = 86; omega)
                  subst i
                  exact block_0086
          · by_cases h_87_92 : i.val < 89
            · by_cases h_87_89 : i.val < 88
              · have heq : i = Fin.ofNat 165 87 := Fin.ext (by change i.val = 87; omega)
                subst i
                exact block_0087
              · have heq : i = Fin.ofNat 165 88 := Fin.ext (by change i.val = 88; omega)
                subst i
                exact block_0088
            · by_cases h_89_92 : i.val < 90
              · have heq : i = Fin.ofNat 165 89 := Fin.ext (by change i.val = 89; omega)
                subst i
                exact block_0089
              · by_cases h_90_92 : i.val < 91
                · have heq : i = Fin.ofNat 165 90 := Fin.ext (by change i.val = 90; omega)
                  subst i
                  exact block_0090
                · have heq : i = Fin.ofNat 165 91 := Fin.ext (by change i.val = 91; omega)
                  subst i
                  exact block_0091
        · by_cases h_92_102 : i.val < 97
          · by_cases h_92_97 : i.val < 94
            · by_cases h_92_94 : i.val < 93
              · have heq : i = Fin.ofNat 165 92 := Fin.ext (by change i.val = 92; omega)
                subst i
                exact block_0092
              · have heq : i = Fin.ofNat 165 93 := Fin.ext (by change i.val = 93; omega)
                subst i
                exact block_0093
            · by_cases h_94_97 : i.val < 95
              · have heq : i = Fin.ofNat 165 94 := Fin.ext (by change i.val = 94; omega)
                subst i
                exact block_0094
              · by_cases h_95_97 : i.val < 96
                · have heq : i = Fin.ofNat 165 95 := Fin.ext (by change i.val = 95; omega)
                  subst i
                  exact block_0095
                · have heq : i = Fin.ofNat 165 96 := Fin.ext (by change i.val = 96; omega)
                  subst i
                  exact block_0096
          · by_cases h_97_102 : i.val < 99
            · by_cases h_97_99 : i.val < 98
              · have heq : i = Fin.ofNat 165 97 := Fin.ext (by change i.val = 97; omega)
                subst i
                exact block_0097
              · have heq : i = Fin.ofNat 165 98 := Fin.ext (by change i.val = 98; omega)
                subst i
                exact block_0098
            · by_cases h_99_102 : i.val < 100
              · have heq : i = Fin.ofNat 165 99 := Fin.ext (by change i.val = 99; omega)
                subst i
                exact block_0099
              · by_cases h_100_102 : i.val < 101
                · have heq : i = Fin.ofNat 165 100 := Fin.ext (by change i.val = 100; omega)
                  subst i
                  exact block_0100
                · have heq : i = Fin.ofNat 165 101 := Fin.ext (by change i.val = 101; omega)
                  subst i
                  exact block_0101
      · by_cases h_102_123 : i.val < 112
        · by_cases h_102_112 : i.val < 107
          · by_cases h_102_107 : i.val < 104
            · by_cases h_102_104 : i.val < 103
              · have heq : i = Fin.ofNat 165 102 := Fin.ext (by change i.val = 102; omega)
                subst i
                exact block_0102
              · have heq : i = Fin.ofNat 165 103 := Fin.ext (by change i.val = 103; omega)
                subst i
                exact block_0103
            · by_cases h_104_107 : i.val < 105
              · have heq : i = Fin.ofNat 165 104 := Fin.ext (by change i.val = 104; omega)
                subst i
                exact block_0104
              · by_cases h_105_107 : i.val < 106
                · have heq : i = Fin.ofNat 165 105 := Fin.ext (by change i.val = 105; omega)
                  subst i
                  exact block_0105
                · have heq : i = Fin.ofNat 165 106 := Fin.ext (by change i.val = 106; omega)
                  subst i
                  exact block_0106
          · by_cases h_107_112 : i.val < 109
            · by_cases h_107_109 : i.val < 108
              · have heq : i = Fin.ofNat 165 107 := Fin.ext (by change i.val = 107; omega)
                subst i
                exact block_0107
              · have heq : i = Fin.ofNat 165 108 := Fin.ext (by change i.val = 108; omega)
                subst i
                exact block_0108
            · by_cases h_109_112 : i.val < 110
              · have heq : i = Fin.ofNat 165 109 := Fin.ext (by change i.val = 109; omega)
                subst i
                exact block_0109
              · by_cases h_110_112 : i.val < 111
                · have heq : i = Fin.ofNat 165 110 := Fin.ext (by change i.val = 110; omega)
                  subst i
                  exact block_0110
                · have heq : i = Fin.ofNat 165 111 := Fin.ext (by change i.val = 111; omega)
                  subst i
                  exact block_0111
        · by_cases h_112_123 : i.val < 117
          · by_cases h_112_117 : i.val < 114
            · by_cases h_112_114 : i.val < 113
              · have heq : i = Fin.ofNat 165 112 := Fin.ext (by change i.val = 112; omega)
                subst i
                exact block_0112
              · have heq : i = Fin.ofNat 165 113 := Fin.ext (by change i.val = 113; omega)
                subst i
                exact block_0113
            · by_cases h_114_117 : i.val < 115
              · have heq : i = Fin.ofNat 165 114 := Fin.ext (by change i.val = 114; omega)
                subst i
                exact block_0114
              · by_cases h_115_117 : i.val < 116
                · have heq : i = Fin.ofNat 165 115 := Fin.ext (by change i.val = 115; omega)
                  subst i
                  exact block_0115
                · have heq : i = Fin.ofNat 165 116 := Fin.ext (by change i.val = 116; omega)
                  subst i
                  exact block_0116
          · by_cases h_117_123 : i.val < 120
            · by_cases h_117_120 : i.val < 118
              · have heq : i = Fin.ofNat 165 117 := Fin.ext (by change i.val = 117; omega)
                subst i
                exact block_0117
              · by_cases h_118_120 : i.val < 119
                · have heq : i = Fin.ofNat 165 118 := Fin.ext (by change i.val = 118; omega)
                  subst i
                  exact block_0118
                · have heq : i = Fin.ofNat 165 119 := Fin.ext (by change i.val = 119; omega)
                  subst i
                  exact block_0119
            · by_cases h_120_123 : i.val < 121
              · have heq : i = Fin.ofNat 165 120 := Fin.ext (by change i.val = 120; omega)
                subst i
                exact block_0120
              · by_cases h_121_123 : i.val < 122
                · have heq : i = Fin.ofNat 165 121 := Fin.ext (by change i.val = 121; omega)
                  subst i
                  exact block_0121
                · have heq : i = Fin.ofNat 165 122 := Fin.ext (by change i.val = 122; omega)
                  subst i
                  exact block_0122
    · by_cases h_123_165 : i.val < 144
      · by_cases h_123_144 : i.val < 133
        · by_cases h_123_133 : i.val < 128
          · by_cases h_123_128 : i.val < 125
            · by_cases h_123_125 : i.val < 124
              · have heq : i = Fin.ofNat 165 123 := Fin.ext (by change i.val = 123; omega)
                subst i
                exact block_0123
              · have heq : i = Fin.ofNat 165 124 := Fin.ext (by change i.val = 124; omega)
                subst i
                exact block_0124
            · by_cases h_125_128 : i.val < 126
              · have heq : i = Fin.ofNat 165 125 := Fin.ext (by change i.val = 125; omega)
                subst i
                exact block_0125
              · by_cases h_126_128 : i.val < 127
                · have heq : i = Fin.ofNat 165 126 := Fin.ext (by change i.val = 126; omega)
                  subst i
                  exact block_0126
                · have heq : i = Fin.ofNat 165 127 := Fin.ext (by change i.val = 127; omega)
                  subst i
                  exact block_0127
          · by_cases h_128_133 : i.val < 130
            · by_cases h_128_130 : i.val < 129
              · have heq : i = Fin.ofNat 165 128 := Fin.ext (by change i.val = 128; omega)
                subst i
                exact block_0128
              · have heq : i = Fin.ofNat 165 129 := Fin.ext (by change i.val = 129; omega)
                subst i
                exact block_0129
            · by_cases h_130_133 : i.val < 131
              · have heq : i = Fin.ofNat 165 130 := Fin.ext (by change i.val = 130; omega)
                subst i
                exact block_0130
              · by_cases h_131_133 : i.val < 132
                · have heq : i = Fin.ofNat 165 131 := Fin.ext (by change i.val = 131; omega)
                  subst i
                  exact block_0131
                · have heq : i = Fin.ofNat 165 132 := Fin.ext (by change i.val = 132; omega)
                  subst i
                  exact block_0132
        · by_cases h_133_144 : i.val < 138
          · by_cases h_133_138 : i.val < 135
            · by_cases h_133_135 : i.val < 134
              · have heq : i = Fin.ofNat 165 133 := Fin.ext (by change i.val = 133; omega)
                subst i
                exact block_0133
              · have heq : i = Fin.ofNat 165 134 := Fin.ext (by change i.val = 134; omega)
                subst i
                exact block_0134
            · by_cases h_135_138 : i.val < 136
              · have heq : i = Fin.ofNat 165 135 := Fin.ext (by change i.val = 135; omega)
                subst i
                exact block_0135
              · by_cases h_136_138 : i.val < 137
                · have heq : i = Fin.ofNat 165 136 := Fin.ext (by change i.val = 136; omega)
                  subst i
                  exact block_0136
                · have heq : i = Fin.ofNat 165 137 := Fin.ext (by change i.val = 137; omega)
                  subst i
                  exact block_0137
          · by_cases h_138_144 : i.val < 141
            · by_cases h_138_141 : i.val < 139
              · have heq : i = Fin.ofNat 165 138 := Fin.ext (by change i.val = 138; omega)
                subst i
                exact block_0138
              · by_cases h_139_141 : i.val < 140
                · have heq : i = Fin.ofNat 165 139 := Fin.ext (by change i.val = 139; omega)
                  subst i
                  exact block_0139
                · have heq : i = Fin.ofNat 165 140 := Fin.ext (by change i.val = 140; omega)
                  subst i
                  exact block_0140
            · by_cases h_141_144 : i.val < 142
              · have heq : i = Fin.ofNat 165 141 := Fin.ext (by change i.val = 141; omega)
                subst i
                exact block_0141
              · by_cases h_142_144 : i.val < 143
                · have heq : i = Fin.ofNat 165 142 := Fin.ext (by change i.val = 142; omega)
                  subst i
                  exact block_0142
                · have heq : i = Fin.ofNat 165 143 := Fin.ext (by change i.val = 143; omega)
                  subst i
                  exact block_0143
      · by_cases h_144_165 : i.val < 154
        · by_cases h_144_154 : i.val < 149
          · by_cases h_144_149 : i.val < 146
            · by_cases h_144_146 : i.val < 145
              · have heq : i = Fin.ofNat 165 144 := Fin.ext (by change i.val = 144; omega)
                subst i
                exact block_0144
              · have heq : i = Fin.ofNat 165 145 := Fin.ext (by change i.val = 145; omega)
                subst i
                exact block_0145
            · by_cases h_146_149 : i.val < 147
              · have heq : i = Fin.ofNat 165 146 := Fin.ext (by change i.val = 146; omega)
                subst i
                exact block_0146
              · by_cases h_147_149 : i.val < 148
                · have heq : i = Fin.ofNat 165 147 := Fin.ext (by change i.val = 147; omega)
                  subst i
                  exact block_0147
                · have heq : i = Fin.ofNat 165 148 := Fin.ext (by change i.val = 148; omega)
                  subst i
                  exact block_0148
          · by_cases h_149_154 : i.val < 151
            · by_cases h_149_151 : i.val < 150
              · have heq : i = Fin.ofNat 165 149 := Fin.ext (by change i.val = 149; omega)
                subst i
                exact block_0149
              · have heq : i = Fin.ofNat 165 150 := Fin.ext (by change i.val = 150; omega)
                subst i
                exact block_0150
            · by_cases h_151_154 : i.val < 152
              · have heq : i = Fin.ofNat 165 151 := Fin.ext (by change i.val = 151; omega)
                subst i
                exact block_0151
              · by_cases h_152_154 : i.val < 153
                · have heq : i = Fin.ofNat 165 152 := Fin.ext (by change i.val = 152; omega)
                  subst i
                  exact block_0152
                · have heq : i = Fin.ofNat 165 153 := Fin.ext (by change i.val = 153; omega)
                  subst i
                  exact block_0153
        · by_cases h_154_165 : i.val < 159
          · by_cases h_154_159 : i.val < 156
            · by_cases h_154_156 : i.val < 155
              · have heq : i = Fin.ofNat 165 154 := Fin.ext (by change i.val = 154; omega)
                subst i
                exact block_0154
              · have heq : i = Fin.ofNat 165 155 := Fin.ext (by change i.val = 155; omega)
                subst i
                exact block_0155
            · by_cases h_156_159 : i.val < 157
              · have heq : i = Fin.ofNat 165 156 := Fin.ext (by change i.val = 156; omega)
                subst i
                exact block_0156
              · by_cases h_157_159 : i.val < 158
                · have heq : i = Fin.ofNat 165 157 := Fin.ext (by change i.val = 157; omega)
                  subst i
                  exact block_0157
                · have heq : i = Fin.ofNat 165 158 := Fin.ext (by change i.val = 158; omega)
                  subst i
                  exact block_0158
          · by_cases h_159_165 : i.val < 162
            · by_cases h_159_162 : i.val < 160
              · have heq : i = Fin.ofNat 165 159 := Fin.ext (by change i.val = 159; omega)
                subst i
                exact block_0159
              · by_cases h_160_162 : i.val < 161
                · have heq : i = Fin.ofNat 165 160 := Fin.ext (by change i.val = 160; omega)
                  subst i
                  exact block_0160
                · have heq : i = Fin.ofNat 165 161 := Fin.ext (by change i.val = 161; omega)
                  subst i
                  exact block_0161
            · by_cases h_162_165 : i.val < 163
              · have heq : i = Fin.ofNat 165 162 := Fin.ext (by change i.val = 162; omega)
                subst i
                exact block_0162
              · by_cases h_163_165 : i.val < 164
                · have heq : i = Fin.ofNat 165 163 := Fin.ext (by change i.val = 163; omega)
                  subst i
                  exact block_0163
                · have heq : i = Fin.ofNat 165 164 := Fin.ext (by change i.val = 164; omega)
                  subst i
                  exact block_0164
end Papers.RationalityTen.RootedCanonical.RootedSixExtra03.S5T0
