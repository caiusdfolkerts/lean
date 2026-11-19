module
prelude
public import RootedSixExtra03CanonicalT4Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra03.T4
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 6 (raw i) template root
      FacetUniverses.RootedSixExtra03.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 140 := i.isLt
  by_cases h_0_140 : i.val < 70
  · by_cases h_0_70 : i.val < 35
    · by_cases h_0_35 : i.val < 17
      · by_cases h_0_17 : i.val < 8
        · by_cases h_0_8 : i.val < 4
          · by_cases h_0_4 : i.val < 2
            · by_cases h_0_2 : i.val < 1
              · have heq : i = Fin.ofNat 140 0 := Fin.ext (by change i.val = 0; omega)
                subst i
                exact block_0000
              · have heq : i = Fin.ofNat 140 1 := Fin.ext (by change i.val = 1; omega)
                subst i
                exact block_0001
            · by_cases h_2_4 : i.val < 3
              · have heq : i = Fin.ofNat 140 2 := Fin.ext (by change i.val = 2; omega)
                subst i
                exact block_0002
              · have heq : i = Fin.ofNat 140 3 := Fin.ext (by change i.val = 3; omega)
                subst i
                exact block_0003
          · by_cases h_4_8 : i.val < 6
            · by_cases h_4_6 : i.val < 5
              · have heq : i = Fin.ofNat 140 4 := Fin.ext (by change i.val = 4; omega)
                subst i
                exact block_0004
              · have heq : i = Fin.ofNat 140 5 := Fin.ext (by change i.val = 5; omega)
                subst i
                exact block_0005
            · by_cases h_6_8 : i.val < 7
              · have heq : i = Fin.ofNat 140 6 := Fin.ext (by change i.val = 6; omega)
                subst i
                exact block_0006
              · have heq : i = Fin.ofNat 140 7 := Fin.ext (by change i.val = 7; omega)
                subst i
                exact block_0007
        · by_cases h_8_17 : i.val < 12
          · by_cases h_8_12 : i.val < 10
            · by_cases h_8_10 : i.val < 9
              · have heq : i = Fin.ofNat 140 8 := Fin.ext (by change i.val = 8; omega)
                subst i
                exact block_0008
              · have heq : i = Fin.ofNat 140 9 := Fin.ext (by change i.val = 9; omega)
                subst i
                exact block_0009
            · by_cases h_10_12 : i.val < 11
              · have heq : i = Fin.ofNat 140 10 := Fin.ext (by change i.val = 10; omega)
                subst i
                exact block_0010
              · have heq : i = Fin.ofNat 140 11 := Fin.ext (by change i.val = 11; omega)
                subst i
                exact block_0011
          · by_cases h_12_17 : i.val < 14
            · by_cases h_12_14 : i.val < 13
              · have heq : i = Fin.ofNat 140 12 := Fin.ext (by change i.val = 12; omega)
                subst i
                exact block_0012
              · have heq : i = Fin.ofNat 140 13 := Fin.ext (by change i.val = 13; omega)
                subst i
                exact block_0013
            · by_cases h_14_17 : i.val < 15
              · have heq : i = Fin.ofNat 140 14 := Fin.ext (by change i.val = 14; omega)
                subst i
                exact block_0014
              · by_cases h_15_17 : i.val < 16
                · have heq : i = Fin.ofNat 140 15 := Fin.ext (by change i.val = 15; omega)
                  subst i
                  exact block_0015
                · have heq : i = Fin.ofNat 140 16 := Fin.ext (by change i.val = 16; omega)
                  subst i
                  exact block_0016
      · by_cases h_17_35 : i.val < 26
        · by_cases h_17_26 : i.val < 21
          · by_cases h_17_21 : i.val < 19
            · by_cases h_17_19 : i.val < 18
              · have heq : i = Fin.ofNat 140 17 := Fin.ext (by change i.val = 17; omega)
                subst i
                exact block_0017
              · have heq : i = Fin.ofNat 140 18 := Fin.ext (by change i.val = 18; omega)
                subst i
                exact block_0018
            · by_cases h_19_21 : i.val < 20
              · have heq : i = Fin.ofNat 140 19 := Fin.ext (by change i.val = 19; omega)
                subst i
                exact block_0019
              · have heq : i = Fin.ofNat 140 20 := Fin.ext (by change i.val = 20; omega)
                subst i
                exact block_0020
          · by_cases h_21_26 : i.val < 23
            · by_cases h_21_23 : i.val < 22
              · have heq : i = Fin.ofNat 140 21 := Fin.ext (by change i.val = 21; omega)
                subst i
                exact block_0021
              · have heq : i = Fin.ofNat 140 22 := Fin.ext (by change i.val = 22; omega)
                subst i
                exact block_0022
            · by_cases h_23_26 : i.val < 24
              · have heq : i = Fin.ofNat 140 23 := Fin.ext (by change i.val = 23; omega)
                subst i
                exact block_0023
              · by_cases h_24_26 : i.val < 25
                · have heq : i = Fin.ofNat 140 24 := Fin.ext (by change i.val = 24; omega)
                  subst i
                  exact block_0024
                · have heq : i = Fin.ofNat 140 25 := Fin.ext (by change i.val = 25; omega)
                  subst i
                  exact block_0025
        · by_cases h_26_35 : i.val < 30
          · by_cases h_26_30 : i.val < 28
            · by_cases h_26_28 : i.val < 27
              · have heq : i = Fin.ofNat 140 26 := Fin.ext (by change i.val = 26; omega)
                subst i
                exact block_0026
              · have heq : i = Fin.ofNat 140 27 := Fin.ext (by change i.val = 27; omega)
                subst i
                exact block_0027
            · by_cases h_28_30 : i.val < 29
              · have heq : i = Fin.ofNat 140 28 := Fin.ext (by change i.val = 28; omega)
                subst i
                exact block_0028
              · have heq : i = Fin.ofNat 140 29 := Fin.ext (by change i.val = 29; omega)
                subst i
                exact block_0029
          · by_cases h_30_35 : i.val < 32
            · by_cases h_30_32 : i.val < 31
              · have heq : i = Fin.ofNat 140 30 := Fin.ext (by change i.val = 30; omega)
                subst i
                exact block_0030
              · have heq : i = Fin.ofNat 140 31 := Fin.ext (by change i.val = 31; omega)
                subst i
                exact block_0031
            · by_cases h_32_35 : i.val < 33
              · have heq : i = Fin.ofNat 140 32 := Fin.ext (by change i.val = 32; omega)
                subst i
                exact block_0032
              · by_cases h_33_35 : i.val < 34
                · have heq : i = Fin.ofNat 140 33 := Fin.ext (by change i.val = 33; omega)
                  subst i
                  exact block_0033
                · have heq : i = Fin.ofNat 140 34 := Fin.ext (by change i.val = 34; omega)
                  subst i
                  exact block_0034
    · by_cases h_35_70 : i.val < 52
      · by_cases h_35_52 : i.val < 43
        · by_cases h_35_43 : i.val < 39
          · by_cases h_35_39 : i.val < 37
            · by_cases h_35_37 : i.val < 36
              · have heq : i = Fin.ofNat 140 35 := Fin.ext (by change i.val = 35; omega)
                subst i
                exact block_0035
              · have heq : i = Fin.ofNat 140 36 := Fin.ext (by change i.val = 36; omega)
                subst i
                exact block_0036
            · by_cases h_37_39 : i.val < 38
              · have heq : i = Fin.ofNat 140 37 := Fin.ext (by change i.val = 37; omega)
                subst i
                exact block_0037
              · have heq : i = Fin.ofNat 140 38 := Fin.ext (by change i.val = 38; omega)
                subst i
                exact block_0038
          · by_cases h_39_43 : i.val < 41
            · by_cases h_39_41 : i.val < 40
              · have heq : i = Fin.ofNat 140 39 := Fin.ext (by change i.val = 39; omega)
                subst i
                exact block_0039
              · have heq : i = Fin.ofNat 140 40 := Fin.ext (by change i.val = 40; omega)
                subst i
                exact block_0040
            · by_cases h_41_43 : i.val < 42
              · have heq : i = Fin.ofNat 140 41 := Fin.ext (by change i.val = 41; omega)
                subst i
                exact block_0041
              · have heq : i = Fin.ofNat 140 42 := Fin.ext (by change i.val = 42; omega)
                subst i
                exact block_0042
        · by_cases h_43_52 : i.val < 47
          · by_cases h_43_47 : i.val < 45
            · by_cases h_43_45 : i.val < 44
              · have heq : i = Fin.ofNat 140 43 := Fin.ext (by change i.val = 43; omega)
                subst i
                exact block_0043
              · have heq : i = Fin.ofNat 140 44 := Fin.ext (by change i.val = 44; omega)
                subst i
                exact block_0044
            · by_cases h_45_47 : i.val < 46
              · have heq : i = Fin.ofNat 140 45 := Fin.ext (by change i.val = 45; omega)
                subst i
                exact block_0045
              · have heq : i = Fin.ofNat 140 46 := Fin.ext (by change i.val = 46; omega)
                subst i
                exact block_0046
          · by_cases h_47_52 : i.val < 49
            · by_cases h_47_49 : i.val < 48
              · have heq : i = Fin.ofNat 140 47 := Fin.ext (by change i.val = 47; omega)
                subst i
                exact block_0047
              · have heq : i = Fin.ofNat 140 48 := Fin.ext (by change i.val = 48; omega)
                subst i
                exact block_0048
            · by_cases h_49_52 : i.val < 50
              · have heq : i = Fin.ofNat 140 49 := Fin.ext (by change i.val = 49; omega)
                subst i
                exact block_0049
              · by_cases h_50_52 : i.val < 51
                · have heq : i = Fin.ofNat 140 50 := Fin.ext (by change i.val = 50; omega)
                  subst i
                  exact block_0050
                · have heq : i = Fin.ofNat 140 51 := Fin.ext (by change i.val = 51; omega)
                  subst i
                  exact block_0051
      · by_cases h_52_70 : i.val < 61
        · by_cases h_52_61 : i.val < 56
          · by_cases h_52_56 : i.val < 54
            · by_cases h_52_54 : i.val < 53
              · have heq : i = Fin.ofNat 140 52 := Fin.ext (by change i.val = 52; omega)
                subst i
                exact block_0052
              · have heq : i = Fin.ofNat 140 53 := Fin.ext (by change i.val = 53; omega)
                subst i
                exact block_0053
            · by_cases h_54_56 : i.val < 55
              · have heq : i = Fin.ofNat 140 54 := Fin.ext (by change i.val = 54; omega)
                subst i
                exact block_0054
              · have heq : i = Fin.ofNat 140 55 := Fin.ext (by change i.val = 55; omega)
                subst i
                exact block_0055
          · by_cases h_56_61 : i.val < 58
            · by_cases h_56_58 : i.val < 57
              · have heq : i = Fin.ofNat 140 56 := Fin.ext (by change i.val = 56; omega)
                subst i
                exact block_0056
              · have heq : i = Fin.ofNat 140 57 := Fin.ext (by change i.val = 57; omega)
                subst i
                exact block_0057
            · by_cases h_58_61 : i.val < 59
              · have heq : i = Fin.ofNat 140 58 := Fin.ext (by change i.val = 58; omega)
                subst i
                exact block_0058
              · by_cases h_59_61 : i.val < 60
                · have heq : i = Fin.ofNat 140 59 := Fin.ext (by change i.val = 59; omega)
                  subst i
                  exact block_0059
                · have heq : i = Fin.ofNat 140 60 := Fin.ext (by change i.val = 60; omega)
                  subst i
                  exact block_0060
        · by_cases h_61_70 : i.val < 65
          · by_cases h_61_65 : i.val < 63
            · by_cases h_61_63 : i.val < 62
              · have heq : i = Fin.ofNat 140 61 := Fin.ext (by change i.val = 61; omega)
                subst i
                exact block_0061
              · have heq : i = Fin.ofNat 140 62 := Fin.ext (by change i.val = 62; omega)
                subst i
                exact block_0062
            · by_cases h_63_65 : i.val < 64
              · have heq : i = Fin.ofNat 140 63 := Fin.ext (by change i.val = 63; omega)
                subst i
                exact block_0063
              · have heq : i = Fin.ofNat 140 64 := Fin.ext (by change i.val = 64; omega)
                subst i
                exact block_0064
          · by_cases h_65_70 : i.val < 67
            · by_cases h_65_67 : i.val < 66
              · have heq : i = Fin.ofNat 140 65 := Fin.ext (by change i.val = 65; omega)
                subst i
                exact block_0065
              · have heq : i = Fin.ofNat 140 66 := Fin.ext (by change i.val = 66; omega)
                subst i
                exact block_0066
            · by_cases h_67_70 : i.val < 68
              · have heq : i = Fin.ofNat 140 67 := Fin.ext (by change i.val = 67; omega)
                subst i
                exact block_0067
              · by_cases h_68_70 : i.val < 69
                · have heq : i = Fin.ofNat 140 68 := Fin.ext (by change i.val = 68; omega)
                  subst i
                  exact block_0068
                · have heq : i = Fin.ofNat 140 69 := Fin.ext (by change i.val = 69; omega)
                  subst i
                  exact block_0069
  · by_cases h_70_140 : i.val < 105
    · by_cases h_70_105 : i.val < 87
      · by_cases h_70_87 : i.val < 78
        · by_cases h_70_78 : i.val < 74
          · by_cases h_70_74 : i.val < 72
            · by_cases h_70_72 : i.val < 71
              · have heq : i = Fin.ofNat 140 70 := Fin.ext (by change i.val = 70; omega)
                subst i
                exact block_0070
              · have heq : i = Fin.ofNat 140 71 := Fin.ext (by change i.val = 71; omega)
                subst i
                exact block_0071
            · by_cases h_72_74 : i.val < 73
              · have heq : i = Fin.ofNat 140 72 := Fin.ext (by change i.val = 72; omega)
                subst i
                exact block_0072
              · have heq : i = Fin.ofNat 140 73 := Fin.ext (by change i.val = 73; omega)
                subst i
                exact block_0073
          · by_cases h_74_78 : i.val < 76
            · by_cases h_74_76 : i.val < 75
              · have heq : i = Fin.ofNat 140 74 := Fin.ext (by change i.val = 74; omega)
                subst i
                exact block_0074
              · have heq : i = Fin.ofNat 140 75 := Fin.ext (by change i.val = 75; omega)
                subst i
                exact block_0075
            · by_cases h_76_78 : i.val < 77
              · have heq : i = Fin.ofNat 140 76 := Fin.ext (by change i.val = 76; omega)
                subst i
                exact block_0076
              · have heq : i = Fin.ofNat 140 77 := Fin.ext (by change i.val = 77; omega)
                subst i
                exact block_0077
        · by_cases h_78_87 : i.val < 82
          · by_cases h_78_82 : i.val < 80
            · by_cases h_78_80 : i.val < 79
              · have heq : i = Fin.ofNat 140 78 := Fin.ext (by change i.val = 78; omega)
                subst i
                exact block_0078
              · have heq : i = Fin.ofNat 140 79 := Fin.ext (by change i.val = 79; omega)
                subst i
                exact block_0079
            · by_cases h_80_82 : i.val < 81
              · have heq : i = Fin.ofNat 140 80 := Fin.ext (by change i.val = 80; omega)
                subst i
                exact block_0080
              · have heq : i = Fin.ofNat 140 81 := Fin.ext (by change i.val = 81; omega)
                subst i
                exact block_0081
          · by_cases h_82_87 : i.val < 84
            · by_cases h_82_84 : i.val < 83
              · have heq : i = Fin.ofNat 140 82 := Fin.ext (by change i.val = 82; omega)
                subst i
                exact block_0082
              · have heq : i = Fin.ofNat 140 83 := Fin.ext (by change i.val = 83; omega)
                subst i
                exact block_0083
            · by_cases h_84_87 : i.val < 85
              · have heq : i = Fin.ofNat 140 84 := Fin.ext (by change i.val = 84; omega)
                subst i
                exact block_0084
              · by_cases h_85_87 : i.val < 86
                · have heq : i = Fin.ofNat 140 85 := Fin.ext (by change i.val = 85; omega)
                  subst i
                  exact block_0085
                · have heq : i = Fin.ofNat 140 86 := Fin.ext (by change i.val = 86; omega)
                  subst i
                  exact block_0086
      · by_cases h_87_105 : i.val < 96
        · by_cases h_87_96 : i.val < 91
          · by_cases h_87_91 : i.val < 89
            · by_cases h_87_89 : i.val < 88
              · have heq : i = Fin.ofNat 140 87 := Fin.ext (by change i.val = 87; omega)
                subst i
                exact block_0087
              · have heq : i = Fin.ofNat 140 88 := Fin.ext (by change i.val = 88; omega)
                subst i
                exact block_0088
            · by_cases h_89_91 : i.val < 90
              · have heq : i = Fin.ofNat 140 89 := Fin.ext (by change i.val = 89; omega)
                subst i
                exact block_0089
              · have heq : i = Fin.ofNat 140 90 := Fin.ext (by change i.val = 90; omega)
                subst i
                exact block_0090
          · by_cases h_91_96 : i.val < 93
            · by_cases h_91_93 : i.val < 92
              · have heq : i = Fin.ofNat 140 91 := Fin.ext (by change i.val = 91; omega)
                subst i
                exact block_0091
              · have heq : i = Fin.ofNat 140 92 := Fin.ext (by change i.val = 92; omega)
                subst i
                exact block_0092
            · by_cases h_93_96 : i.val < 94
              · have heq : i = Fin.ofNat 140 93 := Fin.ext (by change i.val = 93; omega)
                subst i
                exact block_0093
              · by_cases h_94_96 : i.val < 95
                · have heq : i = Fin.ofNat 140 94 := Fin.ext (by change i.val = 94; omega)
                  subst i
                  exact block_0094
                · have heq : i = Fin.ofNat 140 95 := Fin.ext (by change i.val = 95; omega)
                  subst i
                  exact block_0095
        · by_cases h_96_105 : i.val < 100
          · by_cases h_96_100 : i.val < 98
            · by_cases h_96_98 : i.val < 97
              · have heq : i = Fin.ofNat 140 96 := Fin.ext (by change i.val = 96; omega)
                subst i
                exact block_0096
              · have heq : i = Fin.ofNat 140 97 := Fin.ext (by change i.val = 97; omega)
                subst i
                exact block_0097
            · by_cases h_98_100 : i.val < 99
              · have heq : i = Fin.ofNat 140 98 := Fin.ext (by change i.val = 98; omega)
                subst i
                exact block_0098
              · have heq : i = Fin.ofNat 140 99 := Fin.ext (by change i.val = 99; omega)
                subst i
                exact block_0099
          · by_cases h_100_105 : i.val < 102
            · by_cases h_100_102 : i.val < 101
              · have heq : i = Fin.ofNat 140 100 := Fin.ext (by change i.val = 100; omega)
                subst i
                exact block_0100
              · have heq : i = Fin.ofNat 140 101 := Fin.ext (by change i.val = 101; omega)
                subst i
                exact block_0101
            · by_cases h_102_105 : i.val < 103
              · have heq : i = Fin.ofNat 140 102 := Fin.ext (by change i.val = 102; omega)
                subst i
                exact block_0102
              · by_cases h_103_105 : i.val < 104
                · have heq : i = Fin.ofNat 140 103 := Fin.ext (by change i.val = 103; omega)
                  subst i
                  exact block_0103
                · have heq : i = Fin.ofNat 140 104 := Fin.ext (by change i.val = 104; omega)
                  subst i
                  exact block_0104
    · by_cases h_105_140 : i.val < 122
      · by_cases h_105_122 : i.val < 113
        · by_cases h_105_113 : i.val < 109
          · by_cases h_105_109 : i.val < 107
            · by_cases h_105_107 : i.val < 106
              · have heq : i = Fin.ofNat 140 105 := Fin.ext (by change i.val = 105; omega)
                subst i
                exact block_0105
              · have heq : i = Fin.ofNat 140 106 := Fin.ext (by change i.val = 106; omega)
                subst i
                exact block_0106
            · by_cases h_107_109 : i.val < 108
              · have heq : i = Fin.ofNat 140 107 := Fin.ext (by change i.val = 107; omega)
                subst i
                exact block_0107
              · have heq : i = Fin.ofNat 140 108 := Fin.ext (by change i.val = 108; omega)
                subst i
                exact block_0108
          · by_cases h_109_113 : i.val < 111
            · by_cases h_109_111 : i.val < 110
              · have heq : i = Fin.ofNat 140 109 := Fin.ext (by change i.val = 109; omega)
                subst i
                exact block_0109
              · have heq : i = Fin.ofNat 140 110 := Fin.ext (by change i.val = 110; omega)
                subst i
                exact block_0110
            · by_cases h_111_113 : i.val < 112
              · have heq : i = Fin.ofNat 140 111 := Fin.ext (by change i.val = 111; omega)
                subst i
                exact block_0111
              · have heq : i = Fin.ofNat 140 112 := Fin.ext (by change i.val = 112; omega)
                subst i
                exact block_0112
        · by_cases h_113_122 : i.val < 117
          · by_cases h_113_117 : i.val < 115
            · by_cases h_113_115 : i.val < 114
              · have heq : i = Fin.ofNat 140 113 := Fin.ext (by change i.val = 113; omega)
                subst i
                exact block_0113
              · have heq : i = Fin.ofNat 140 114 := Fin.ext (by change i.val = 114; omega)
                subst i
                exact block_0114
            · by_cases h_115_117 : i.val < 116
              · have heq : i = Fin.ofNat 140 115 := Fin.ext (by change i.val = 115; omega)
                subst i
                exact block_0115
              · have heq : i = Fin.ofNat 140 116 := Fin.ext (by change i.val = 116; omega)
                subst i
                exact block_0116
          · by_cases h_117_122 : i.val < 119
            · by_cases h_117_119 : i.val < 118
              · have heq : i = Fin.ofNat 140 117 := Fin.ext (by change i.val = 117; omega)
                subst i
                exact block_0117
              · have heq : i = Fin.ofNat 140 118 := Fin.ext (by change i.val = 118; omega)
                subst i
                exact block_0118
            · by_cases h_119_122 : i.val < 120
              · have heq : i = Fin.ofNat 140 119 := Fin.ext (by change i.val = 119; omega)
                subst i
                exact block_0119
              · by_cases h_120_122 : i.val < 121
                · have heq : i = Fin.ofNat 140 120 := Fin.ext (by change i.val = 120; omega)
                  subst i
                  exact block_0120
                · have heq : i = Fin.ofNat 140 121 := Fin.ext (by change i.val = 121; omega)
                  subst i
                  exact block_0121
      · by_cases h_122_140 : i.val < 131
        · by_cases h_122_131 : i.val < 126
          · by_cases h_122_126 : i.val < 124
            · by_cases h_122_124 : i.val < 123
              · have heq : i = Fin.ofNat 140 122 := Fin.ext (by change i.val = 122; omega)
                subst i
                exact block_0122
              · have heq : i = Fin.ofNat 140 123 := Fin.ext (by change i.val = 123; omega)
                subst i
                exact block_0123
            · by_cases h_124_126 : i.val < 125
              · have heq : i = Fin.ofNat 140 124 := Fin.ext (by change i.val = 124; omega)
                subst i
                exact block_0124
              · have heq : i = Fin.ofNat 140 125 := Fin.ext (by change i.val = 125; omega)
                subst i
                exact block_0125
          · by_cases h_126_131 : i.val < 128
            · by_cases h_126_128 : i.val < 127
              · have heq : i = Fin.ofNat 140 126 := Fin.ext (by change i.val = 126; omega)
                subst i
                exact block_0126
              · have heq : i = Fin.ofNat 140 127 := Fin.ext (by change i.val = 127; omega)
                subst i
                exact block_0127
            · by_cases h_128_131 : i.val < 129
              · have heq : i = Fin.ofNat 140 128 := Fin.ext (by change i.val = 128; omega)
                subst i
                exact block_0128
              · by_cases h_129_131 : i.val < 130
                · have heq : i = Fin.ofNat 140 129 := Fin.ext (by change i.val = 129; omega)
                  subst i
                  exact block_0129
                · have heq : i = Fin.ofNat 140 130 := Fin.ext (by change i.val = 130; omega)
                  subst i
                  exact block_0130
        · by_cases h_131_140 : i.val < 135
          · by_cases h_131_135 : i.val < 133
            · by_cases h_131_133 : i.val < 132
              · have heq : i = Fin.ofNat 140 131 := Fin.ext (by change i.val = 131; omega)
                subst i
                exact block_0131
              · have heq : i = Fin.ofNat 140 132 := Fin.ext (by change i.val = 132; omega)
                subst i
                exact block_0132
            · by_cases h_133_135 : i.val < 134
              · have heq : i = Fin.ofNat 140 133 := Fin.ext (by change i.val = 133; omega)
                subst i
                exact block_0133
              · have heq : i = Fin.ofNat 140 134 := Fin.ext (by change i.val = 134; omega)
                subst i
                exact block_0134
          · by_cases h_135_140 : i.val < 137
            · by_cases h_135_137 : i.val < 136
              · have heq : i = Fin.ofNat 140 135 := Fin.ext (by change i.val = 135; omega)
                subst i
                exact block_0135
              · have heq : i = Fin.ofNat 140 136 := Fin.ext (by change i.val = 136; omega)
                subst i
                exact block_0136
            · by_cases h_137_140 : i.val < 138
              · have heq : i = Fin.ofNat 140 137 := Fin.ext (by change i.val = 137; omega)
                subst i
                exact block_0137
              · by_cases h_138_140 : i.val < 139
                · have heq : i = Fin.ofNat 140 138 := Fin.ext (by change i.val = 138; omega)
                  subst i
                  exact block_0138
                · have heq : i = Fin.ofNat 140 139 := Fin.ext (by change i.val = 139; omega)
                  subst i
                  exact block_0139
end Papers.RationalityTen.RootedCanonical.RootedSixExtra03.T4
