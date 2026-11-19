module
prelude
public import RootedSixExtra03CanonicalS5T1Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra03.S5T1
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 5 (raw i) template root
      FacetUniverses.RootedSixExtra03.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 143 := i.isLt
  by_cases h_0_143 : i.val < 71
  · by_cases h_0_71 : i.val < 35
    · by_cases h_0_35 : i.val < 17
      · by_cases h_0_17 : i.val < 8
        · by_cases h_0_8 : i.val < 4
          · by_cases h_0_4 : i.val < 2
            · by_cases h_0_2 : i.val < 1
              · have heq : i = Fin.ofNat 143 0 := Fin.ext (by change i.val = 0; omega)
                subst i
                exact block_0000
              · have heq : i = Fin.ofNat 143 1 := Fin.ext (by change i.val = 1; omega)
                subst i
                exact block_0001
            · by_cases h_2_4 : i.val < 3
              · have heq : i = Fin.ofNat 143 2 := Fin.ext (by change i.val = 2; omega)
                subst i
                exact block_0002
              · have heq : i = Fin.ofNat 143 3 := Fin.ext (by change i.val = 3; omega)
                subst i
                exact block_0003
          · by_cases h_4_8 : i.val < 6
            · by_cases h_4_6 : i.val < 5
              · have heq : i = Fin.ofNat 143 4 := Fin.ext (by change i.val = 4; omega)
                subst i
                exact block_0004
              · have heq : i = Fin.ofNat 143 5 := Fin.ext (by change i.val = 5; omega)
                subst i
                exact block_0005
            · by_cases h_6_8 : i.val < 7
              · have heq : i = Fin.ofNat 143 6 := Fin.ext (by change i.val = 6; omega)
                subst i
                exact block_0006
              · have heq : i = Fin.ofNat 143 7 := Fin.ext (by change i.val = 7; omega)
                subst i
                exact block_0007
        · by_cases h_8_17 : i.val < 12
          · by_cases h_8_12 : i.val < 10
            · by_cases h_8_10 : i.val < 9
              · have heq : i = Fin.ofNat 143 8 := Fin.ext (by change i.val = 8; omega)
                subst i
                exact block_0008
              · have heq : i = Fin.ofNat 143 9 := Fin.ext (by change i.val = 9; omega)
                subst i
                exact block_0009
            · by_cases h_10_12 : i.val < 11
              · have heq : i = Fin.ofNat 143 10 := Fin.ext (by change i.val = 10; omega)
                subst i
                exact block_0010
              · have heq : i = Fin.ofNat 143 11 := Fin.ext (by change i.val = 11; omega)
                subst i
                exact block_0011
          · by_cases h_12_17 : i.val < 14
            · by_cases h_12_14 : i.val < 13
              · have heq : i = Fin.ofNat 143 12 := Fin.ext (by change i.val = 12; omega)
                subst i
                exact block_0012
              · have heq : i = Fin.ofNat 143 13 := Fin.ext (by change i.val = 13; omega)
                subst i
                exact block_0013
            · by_cases h_14_17 : i.val < 15
              · have heq : i = Fin.ofNat 143 14 := Fin.ext (by change i.val = 14; omega)
                subst i
                exact block_0014
              · by_cases h_15_17 : i.val < 16
                · have heq : i = Fin.ofNat 143 15 := Fin.ext (by change i.val = 15; omega)
                  subst i
                  exact block_0015
                · have heq : i = Fin.ofNat 143 16 := Fin.ext (by change i.val = 16; omega)
                  subst i
                  exact block_0016
      · by_cases h_17_35 : i.val < 26
        · by_cases h_17_26 : i.val < 21
          · by_cases h_17_21 : i.val < 19
            · by_cases h_17_19 : i.val < 18
              · have heq : i = Fin.ofNat 143 17 := Fin.ext (by change i.val = 17; omega)
                subst i
                exact block_0017
              · have heq : i = Fin.ofNat 143 18 := Fin.ext (by change i.val = 18; omega)
                subst i
                exact block_0018
            · by_cases h_19_21 : i.val < 20
              · have heq : i = Fin.ofNat 143 19 := Fin.ext (by change i.val = 19; omega)
                subst i
                exact block_0019
              · have heq : i = Fin.ofNat 143 20 := Fin.ext (by change i.val = 20; omega)
                subst i
                exact block_0020
          · by_cases h_21_26 : i.val < 23
            · by_cases h_21_23 : i.val < 22
              · have heq : i = Fin.ofNat 143 21 := Fin.ext (by change i.val = 21; omega)
                subst i
                exact block_0021
              · have heq : i = Fin.ofNat 143 22 := Fin.ext (by change i.val = 22; omega)
                subst i
                exact block_0022
            · by_cases h_23_26 : i.val < 24
              · have heq : i = Fin.ofNat 143 23 := Fin.ext (by change i.val = 23; omega)
                subst i
                exact block_0023
              · by_cases h_24_26 : i.val < 25
                · have heq : i = Fin.ofNat 143 24 := Fin.ext (by change i.val = 24; omega)
                  subst i
                  exact block_0024
                · have heq : i = Fin.ofNat 143 25 := Fin.ext (by change i.val = 25; omega)
                  subst i
                  exact block_0025
        · by_cases h_26_35 : i.val < 30
          · by_cases h_26_30 : i.val < 28
            · by_cases h_26_28 : i.val < 27
              · have heq : i = Fin.ofNat 143 26 := Fin.ext (by change i.val = 26; omega)
                subst i
                exact block_0026
              · have heq : i = Fin.ofNat 143 27 := Fin.ext (by change i.val = 27; omega)
                subst i
                exact block_0027
            · by_cases h_28_30 : i.val < 29
              · have heq : i = Fin.ofNat 143 28 := Fin.ext (by change i.val = 28; omega)
                subst i
                exact block_0028
              · have heq : i = Fin.ofNat 143 29 := Fin.ext (by change i.val = 29; omega)
                subst i
                exact block_0029
          · by_cases h_30_35 : i.val < 32
            · by_cases h_30_32 : i.val < 31
              · have heq : i = Fin.ofNat 143 30 := Fin.ext (by change i.val = 30; omega)
                subst i
                exact block_0030
              · have heq : i = Fin.ofNat 143 31 := Fin.ext (by change i.val = 31; omega)
                subst i
                exact block_0031
            · by_cases h_32_35 : i.val < 33
              · have heq : i = Fin.ofNat 143 32 := Fin.ext (by change i.val = 32; omega)
                subst i
                exact block_0032
              · by_cases h_33_35 : i.val < 34
                · have heq : i = Fin.ofNat 143 33 := Fin.ext (by change i.val = 33; omega)
                  subst i
                  exact block_0033
                · have heq : i = Fin.ofNat 143 34 := Fin.ext (by change i.val = 34; omega)
                  subst i
                  exact block_0034
    · by_cases h_35_71 : i.val < 53
      · by_cases h_35_53 : i.val < 44
        · by_cases h_35_44 : i.val < 39
          · by_cases h_35_39 : i.val < 37
            · by_cases h_35_37 : i.val < 36
              · have heq : i = Fin.ofNat 143 35 := Fin.ext (by change i.val = 35; omega)
                subst i
                exact block_0035
              · have heq : i = Fin.ofNat 143 36 := Fin.ext (by change i.val = 36; omega)
                subst i
                exact block_0036
            · by_cases h_37_39 : i.val < 38
              · have heq : i = Fin.ofNat 143 37 := Fin.ext (by change i.val = 37; omega)
                subst i
                exact block_0037
              · have heq : i = Fin.ofNat 143 38 := Fin.ext (by change i.val = 38; omega)
                subst i
                exact block_0038
          · by_cases h_39_44 : i.val < 41
            · by_cases h_39_41 : i.val < 40
              · have heq : i = Fin.ofNat 143 39 := Fin.ext (by change i.val = 39; omega)
                subst i
                exact block_0039
              · have heq : i = Fin.ofNat 143 40 := Fin.ext (by change i.val = 40; omega)
                subst i
                exact block_0040
            · by_cases h_41_44 : i.val < 42
              · have heq : i = Fin.ofNat 143 41 := Fin.ext (by change i.val = 41; omega)
                subst i
                exact block_0041
              · by_cases h_42_44 : i.val < 43
                · have heq : i = Fin.ofNat 143 42 := Fin.ext (by change i.val = 42; omega)
                  subst i
                  exact block_0042
                · have heq : i = Fin.ofNat 143 43 := Fin.ext (by change i.val = 43; omega)
                  subst i
                  exact block_0043
        · by_cases h_44_53 : i.val < 48
          · by_cases h_44_48 : i.val < 46
            · by_cases h_44_46 : i.val < 45
              · have heq : i = Fin.ofNat 143 44 := Fin.ext (by change i.val = 44; omega)
                subst i
                exact block_0044
              · have heq : i = Fin.ofNat 143 45 := Fin.ext (by change i.val = 45; omega)
                subst i
                exact block_0045
            · by_cases h_46_48 : i.val < 47
              · have heq : i = Fin.ofNat 143 46 := Fin.ext (by change i.val = 46; omega)
                subst i
                exact block_0046
              · have heq : i = Fin.ofNat 143 47 := Fin.ext (by change i.val = 47; omega)
                subst i
                exact block_0047
          · by_cases h_48_53 : i.val < 50
            · by_cases h_48_50 : i.val < 49
              · have heq : i = Fin.ofNat 143 48 := Fin.ext (by change i.val = 48; omega)
                subst i
                exact block_0048
              · have heq : i = Fin.ofNat 143 49 := Fin.ext (by change i.val = 49; omega)
                subst i
                exact block_0049
            · by_cases h_50_53 : i.val < 51
              · have heq : i = Fin.ofNat 143 50 := Fin.ext (by change i.val = 50; omega)
                subst i
                exact block_0050
              · by_cases h_51_53 : i.val < 52
                · have heq : i = Fin.ofNat 143 51 := Fin.ext (by change i.val = 51; omega)
                  subst i
                  exact block_0051
                · have heq : i = Fin.ofNat 143 52 := Fin.ext (by change i.val = 52; omega)
                  subst i
                  exact block_0052
      · by_cases h_53_71 : i.val < 62
        · by_cases h_53_62 : i.val < 57
          · by_cases h_53_57 : i.val < 55
            · by_cases h_53_55 : i.val < 54
              · have heq : i = Fin.ofNat 143 53 := Fin.ext (by change i.val = 53; omega)
                subst i
                exact block_0053
              · have heq : i = Fin.ofNat 143 54 := Fin.ext (by change i.val = 54; omega)
                subst i
                exact block_0054
            · by_cases h_55_57 : i.val < 56
              · have heq : i = Fin.ofNat 143 55 := Fin.ext (by change i.val = 55; omega)
                subst i
                exact block_0055
              · have heq : i = Fin.ofNat 143 56 := Fin.ext (by change i.val = 56; omega)
                subst i
                exact block_0056
          · by_cases h_57_62 : i.val < 59
            · by_cases h_57_59 : i.val < 58
              · have heq : i = Fin.ofNat 143 57 := Fin.ext (by change i.val = 57; omega)
                subst i
                exact block_0057
              · have heq : i = Fin.ofNat 143 58 := Fin.ext (by change i.val = 58; omega)
                subst i
                exact block_0058
            · by_cases h_59_62 : i.val < 60
              · have heq : i = Fin.ofNat 143 59 := Fin.ext (by change i.val = 59; omega)
                subst i
                exact block_0059
              · by_cases h_60_62 : i.val < 61
                · have heq : i = Fin.ofNat 143 60 := Fin.ext (by change i.val = 60; omega)
                  subst i
                  exact block_0060
                · have heq : i = Fin.ofNat 143 61 := Fin.ext (by change i.val = 61; omega)
                  subst i
                  exact block_0061
        · by_cases h_62_71 : i.val < 66
          · by_cases h_62_66 : i.val < 64
            · by_cases h_62_64 : i.val < 63
              · have heq : i = Fin.ofNat 143 62 := Fin.ext (by change i.val = 62; omega)
                subst i
                exact block_0062
              · have heq : i = Fin.ofNat 143 63 := Fin.ext (by change i.val = 63; omega)
                subst i
                exact block_0063
            · by_cases h_64_66 : i.val < 65
              · have heq : i = Fin.ofNat 143 64 := Fin.ext (by change i.val = 64; omega)
                subst i
                exact block_0064
              · have heq : i = Fin.ofNat 143 65 := Fin.ext (by change i.val = 65; omega)
                subst i
                exact block_0065
          · by_cases h_66_71 : i.val < 68
            · by_cases h_66_68 : i.val < 67
              · have heq : i = Fin.ofNat 143 66 := Fin.ext (by change i.val = 66; omega)
                subst i
                exact block_0066
              · have heq : i = Fin.ofNat 143 67 := Fin.ext (by change i.val = 67; omega)
                subst i
                exact block_0067
            · by_cases h_68_71 : i.val < 69
              · have heq : i = Fin.ofNat 143 68 := Fin.ext (by change i.val = 68; omega)
                subst i
                exact block_0068
              · by_cases h_69_71 : i.val < 70
                · have heq : i = Fin.ofNat 143 69 := Fin.ext (by change i.val = 69; omega)
                  subst i
                  exact block_0069
                · have heq : i = Fin.ofNat 143 70 := Fin.ext (by change i.val = 70; omega)
                  subst i
                  exact block_0070
  · by_cases h_71_143 : i.val < 107
    · by_cases h_71_107 : i.val < 89
      · by_cases h_71_89 : i.val < 80
        · by_cases h_71_80 : i.val < 75
          · by_cases h_71_75 : i.val < 73
            · by_cases h_71_73 : i.val < 72
              · have heq : i = Fin.ofNat 143 71 := Fin.ext (by change i.val = 71; omega)
                subst i
                exact block_0071
              · have heq : i = Fin.ofNat 143 72 := Fin.ext (by change i.val = 72; omega)
                subst i
                exact block_0072
            · by_cases h_73_75 : i.val < 74
              · have heq : i = Fin.ofNat 143 73 := Fin.ext (by change i.val = 73; omega)
                subst i
                exact block_0073
              · have heq : i = Fin.ofNat 143 74 := Fin.ext (by change i.val = 74; omega)
                subst i
                exact block_0074
          · by_cases h_75_80 : i.val < 77
            · by_cases h_75_77 : i.val < 76
              · have heq : i = Fin.ofNat 143 75 := Fin.ext (by change i.val = 75; omega)
                subst i
                exact block_0075
              · have heq : i = Fin.ofNat 143 76 := Fin.ext (by change i.val = 76; omega)
                subst i
                exact block_0076
            · by_cases h_77_80 : i.val < 78
              · have heq : i = Fin.ofNat 143 77 := Fin.ext (by change i.val = 77; omega)
                subst i
                exact block_0077
              · by_cases h_78_80 : i.val < 79
                · have heq : i = Fin.ofNat 143 78 := Fin.ext (by change i.val = 78; omega)
                  subst i
                  exact block_0078
                · have heq : i = Fin.ofNat 143 79 := Fin.ext (by change i.val = 79; omega)
                  subst i
                  exact block_0079
        · by_cases h_80_89 : i.val < 84
          · by_cases h_80_84 : i.val < 82
            · by_cases h_80_82 : i.val < 81
              · have heq : i = Fin.ofNat 143 80 := Fin.ext (by change i.val = 80; omega)
                subst i
                exact block_0080
              · have heq : i = Fin.ofNat 143 81 := Fin.ext (by change i.val = 81; omega)
                subst i
                exact block_0081
            · by_cases h_82_84 : i.val < 83
              · have heq : i = Fin.ofNat 143 82 := Fin.ext (by change i.val = 82; omega)
                subst i
                exact block_0082
              · have heq : i = Fin.ofNat 143 83 := Fin.ext (by change i.val = 83; omega)
                subst i
                exact block_0083
          · by_cases h_84_89 : i.val < 86
            · by_cases h_84_86 : i.val < 85
              · have heq : i = Fin.ofNat 143 84 := Fin.ext (by change i.val = 84; omega)
                subst i
                exact block_0084
              · have heq : i = Fin.ofNat 143 85 := Fin.ext (by change i.val = 85; omega)
                subst i
                exact block_0085
            · by_cases h_86_89 : i.val < 87
              · have heq : i = Fin.ofNat 143 86 := Fin.ext (by change i.val = 86; omega)
                subst i
                exact block_0086
              · by_cases h_87_89 : i.val < 88
                · have heq : i = Fin.ofNat 143 87 := Fin.ext (by change i.val = 87; omega)
                  subst i
                  exact block_0087
                · have heq : i = Fin.ofNat 143 88 := Fin.ext (by change i.val = 88; omega)
                  subst i
                  exact block_0088
      · by_cases h_89_107 : i.val < 98
        · by_cases h_89_98 : i.val < 93
          · by_cases h_89_93 : i.val < 91
            · by_cases h_89_91 : i.val < 90
              · have heq : i = Fin.ofNat 143 89 := Fin.ext (by change i.val = 89; omega)
                subst i
                exact block_0089
              · have heq : i = Fin.ofNat 143 90 := Fin.ext (by change i.val = 90; omega)
                subst i
                exact block_0090
            · by_cases h_91_93 : i.val < 92
              · have heq : i = Fin.ofNat 143 91 := Fin.ext (by change i.val = 91; omega)
                subst i
                exact block_0091
              · have heq : i = Fin.ofNat 143 92 := Fin.ext (by change i.val = 92; omega)
                subst i
                exact block_0092
          · by_cases h_93_98 : i.val < 95
            · by_cases h_93_95 : i.val < 94
              · have heq : i = Fin.ofNat 143 93 := Fin.ext (by change i.val = 93; omega)
                subst i
                exact block_0093
              · have heq : i = Fin.ofNat 143 94 := Fin.ext (by change i.val = 94; omega)
                subst i
                exact block_0094
            · by_cases h_95_98 : i.val < 96
              · have heq : i = Fin.ofNat 143 95 := Fin.ext (by change i.val = 95; omega)
                subst i
                exact block_0095
              · by_cases h_96_98 : i.val < 97
                · have heq : i = Fin.ofNat 143 96 := Fin.ext (by change i.val = 96; omega)
                  subst i
                  exact block_0096
                · have heq : i = Fin.ofNat 143 97 := Fin.ext (by change i.val = 97; omega)
                  subst i
                  exact block_0097
        · by_cases h_98_107 : i.val < 102
          · by_cases h_98_102 : i.val < 100
            · by_cases h_98_100 : i.val < 99
              · have heq : i = Fin.ofNat 143 98 := Fin.ext (by change i.val = 98; omega)
                subst i
                exact block_0098
              · have heq : i = Fin.ofNat 143 99 := Fin.ext (by change i.val = 99; omega)
                subst i
                exact block_0099
            · by_cases h_100_102 : i.val < 101
              · have heq : i = Fin.ofNat 143 100 := Fin.ext (by change i.val = 100; omega)
                subst i
                exact block_0100
              · have heq : i = Fin.ofNat 143 101 := Fin.ext (by change i.val = 101; omega)
                subst i
                exact block_0101
          · by_cases h_102_107 : i.val < 104
            · by_cases h_102_104 : i.val < 103
              · have heq : i = Fin.ofNat 143 102 := Fin.ext (by change i.val = 102; omega)
                subst i
                exact block_0102
              · have heq : i = Fin.ofNat 143 103 := Fin.ext (by change i.val = 103; omega)
                subst i
                exact block_0103
            · by_cases h_104_107 : i.val < 105
              · have heq : i = Fin.ofNat 143 104 := Fin.ext (by change i.val = 104; omega)
                subst i
                exact block_0104
              · by_cases h_105_107 : i.val < 106
                · have heq : i = Fin.ofNat 143 105 := Fin.ext (by change i.val = 105; omega)
                  subst i
                  exact block_0105
                · have heq : i = Fin.ofNat 143 106 := Fin.ext (by change i.val = 106; omega)
                  subst i
                  exact block_0106
    · by_cases h_107_143 : i.val < 125
      · by_cases h_107_125 : i.val < 116
        · by_cases h_107_116 : i.val < 111
          · by_cases h_107_111 : i.val < 109
            · by_cases h_107_109 : i.val < 108
              · have heq : i = Fin.ofNat 143 107 := Fin.ext (by change i.val = 107; omega)
                subst i
                exact block_0107
              · have heq : i = Fin.ofNat 143 108 := Fin.ext (by change i.val = 108; omega)
                subst i
                exact block_0108
            · by_cases h_109_111 : i.val < 110
              · have heq : i = Fin.ofNat 143 109 := Fin.ext (by change i.val = 109; omega)
                subst i
                exact block_0109
              · have heq : i = Fin.ofNat 143 110 := Fin.ext (by change i.val = 110; omega)
                subst i
                exact block_0110
          · by_cases h_111_116 : i.val < 113
            · by_cases h_111_113 : i.val < 112
              · have heq : i = Fin.ofNat 143 111 := Fin.ext (by change i.val = 111; omega)
                subst i
                exact block_0111
              · have heq : i = Fin.ofNat 143 112 := Fin.ext (by change i.val = 112; omega)
                subst i
                exact block_0112
            · by_cases h_113_116 : i.val < 114
              · have heq : i = Fin.ofNat 143 113 := Fin.ext (by change i.val = 113; omega)
                subst i
                exact block_0113
              · by_cases h_114_116 : i.val < 115
                · have heq : i = Fin.ofNat 143 114 := Fin.ext (by change i.val = 114; omega)
                  subst i
                  exact block_0114
                · have heq : i = Fin.ofNat 143 115 := Fin.ext (by change i.val = 115; omega)
                  subst i
                  exact block_0115
        · by_cases h_116_125 : i.val < 120
          · by_cases h_116_120 : i.val < 118
            · by_cases h_116_118 : i.val < 117
              · have heq : i = Fin.ofNat 143 116 := Fin.ext (by change i.val = 116; omega)
                subst i
                exact block_0116
              · have heq : i = Fin.ofNat 143 117 := Fin.ext (by change i.val = 117; omega)
                subst i
                exact block_0117
            · by_cases h_118_120 : i.val < 119
              · have heq : i = Fin.ofNat 143 118 := Fin.ext (by change i.val = 118; omega)
                subst i
                exact block_0118
              · have heq : i = Fin.ofNat 143 119 := Fin.ext (by change i.val = 119; omega)
                subst i
                exact block_0119
          · by_cases h_120_125 : i.val < 122
            · by_cases h_120_122 : i.val < 121
              · have heq : i = Fin.ofNat 143 120 := Fin.ext (by change i.val = 120; omega)
                subst i
                exact block_0120
              · have heq : i = Fin.ofNat 143 121 := Fin.ext (by change i.val = 121; omega)
                subst i
                exact block_0121
            · by_cases h_122_125 : i.val < 123
              · have heq : i = Fin.ofNat 143 122 := Fin.ext (by change i.val = 122; omega)
                subst i
                exact block_0122
              · by_cases h_123_125 : i.val < 124
                · have heq : i = Fin.ofNat 143 123 := Fin.ext (by change i.val = 123; omega)
                  subst i
                  exact block_0123
                · have heq : i = Fin.ofNat 143 124 := Fin.ext (by change i.val = 124; omega)
                  subst i
                  exact block_0124
      · by_cases h_125_143 : i.val < 134
        · by_cases h_125_134 : i.val < 129
          · by_cases h_125_129 : i.val < 127
            · by_cases h_125_127 : i.val < 126
              · have heq : i = Fin.ofNat 143 125 := Fin.ext (by change i.val = 125; omega)
                subst i
                exact block_0125
              · have heq : i = Fin.ofNat 143 126 := Fin.ext (by change i.val = 126; omega)
                subst i
                exact block_0126
            · by_cases h_127_129 : i.val < 128
              · have heq : i = Fin.ofNat 143 127 := Fin.ext (by change i.val = 127; omega)
                subst i
                exact block_0127
              · have heq : i = Fin.ofNat 143 128 := Fin.ext (by change i.val = 128; omega)
                subst i
                exact block_0128
          · by_cases h_129_134 : i.val < 131
            · by_cases h_129_131 : i.val < 130
              · have heq : i = Fin.ofNat 143 129 := Fin.ext (by change i.val = 129; omega)
                subst i
                exact block_0129
              · have heq : i = Fin.ofNat 143 130 := Fin.ext (by change i.val = 130; omega)
                subst i
                exact block_0130
            · by_cases h_131_134 : i.val < 132
              · have heq : i = Fin.ofNat 143 131 := Fin.ext (by change i.val = 131; omega)
                subst i
                exact block_0131
              · by_cases h_132_134 : i.val < 133
                · have heq : i = Fin.ofNat 143 132 := Fin.ext (by change i.val = 132; omega)
                  subst i
                  exact block_0132
                · have heq : i = Fin.ofNat 143 133 := Fin.ext (by change i.val = 133; omega)
                  subst i
                  exact block_0133
        · by_cases h_134_143 : i.val < 138
          · by_cases h_134_138 : i.val < 136
            · by_cases h_134_136 : i.val < 135
              · have heq : i = Fin.ofNat 143 134 := Fin.ext (by change i.val = 134; omega)
                subst i
                exact block_0134
              · have heq : i = Fin.ofNat 143 135 := Fin.ext (by change i.val = 135; omega)
                subst i
                exact block_0135
            · by_cases h_136_138 : i.val < 137
              · have heq : i = Fin.ofNat 143 136 := Fin.ext (by change i.val = 136; omega)
                subst i
                exact block_0136
              · have heq : i = Fin.ofNat 143 137 := Fin.ext (by change i.val = 137; omega)
                subst i
                exact block_0137
          · by_cases h_138_143 : i.val < 140
            · by_cases h_138_140 : i.val < 139
              · have heq : i = Fin.ofNat 143 138 := Fin.ext (by change i.val = 138; omega)
                subst i
                exact block_0138
              · have heq : i = Fin.ofNat 143 139 := Fin.ext (by change i.val = 139; omega)
                subst i
                exact block_0139
            · by_cases h_140_143 : i.val < 141
              · have heq : i = Fin.ofNat 143 140 := Fin.ext (by change i.val = 140; omega)
                subst i
                exact block_0140
              · by_cases h_141_143 : i.val < 142
                · have heq : i = Fin.ofNat 143 141 := Fin.ext (by change i.val = 141; omega)
                  subst i
                  exact block_0141
                · have heq : i = Fin.ofNat 143 142 := Fin.ext (by change i.val = 142; omega)
                  subst i
                  exact block_0142
end Papers.RationalityTen.RootedCanonical.RootedSixExtra03.S5T1
