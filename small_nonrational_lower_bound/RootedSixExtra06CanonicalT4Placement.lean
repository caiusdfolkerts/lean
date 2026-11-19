module
prelude
public import RootedSixExtra06CanonicalT4Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra06.T4
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 6 (raw i) template root
      FacetUniverses.RootedSixExtra06.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 126 := i.isLt
  by_cases h_0_126 : i.val < 63
  · by_cases h_0_63 : i.val < 31
    · by_cases h_0_31 : i.val < 15
      · by_cases h_0_15 : i.val < 7
        · by_cases h_0_7 : i.val < 3
          · by_cases h_0_3 : i.val < 1
            · have heq : i = Fin.ofNat 126 0 := Fin.ext (by change i.val = 0; omega)
              subst i
              exact block_0000
            · by_cases h_1_3 : i.val < 2
              · have heq : i = Fin.ofNat 126 1 := Fin.ext (by change i.val = 1; omega)
                subst i
                exact block_0001
              · have heq : i = Fin.ofNat 126 2 := Fin.ext (by change i.val = 2; omega)
                subst i
                exact block_0002
          · by_cases h_3_7 : i.val < 5
            · by_cases h_3_5 : i.val < 4
              · have heq : i = Fin.ofNat 126 3 := Fin.ext (by change i.val = 3; omega)
                subst i
                exact block_0003
              · have heq : i = Fin.ofNat 126 4 := Fin.ext (by change i.val = 4; omega)
                subst i
                exact block_0004
            · by_cases h_5_7 : i.val < 6
              · have heq : i = Fin.ofNat 126 5 := Fin.ext (by change i.val = 5; omega)
                subst i
                exact block_0005
              · have heq : i = Fin.ofNat 126 6 := Fin.ext (by change i.val = 6; omega)
                subst i
                exact block_0006
        · by_cases h_7_15 : i.val < 11
          · by_cases h_7_11 : i.val < 9
            · by_cases h_7_9 : i.val < 8
              · have heq : i = Fin.ofNat 126 7 := Fin.ext (by change i.val = 7; omega)
                subst i
                exact block_0007
              · have heq : i = Fin.ofNat 126 8 := Fin.ext (by change i.val = 8; omega)
                subst i
                exact block_0008
            · by_cases h_9_11 : i.val < 10
              · have heq : i = Fin.ofNat 126 9 := Fin.ext (by change i.val = 9; omega)
                subst i
                exact block_0009
              · have heq : i = Fin.ofNat 126 10 := Fin.ext (by change i.val = 10; omega)
                subst i
                exact block_0010
          · by_cases h_11_15 : i.val < 13
            · by_cases h_11_13 : i.val < 12
              · have heq : i = Fin.ofNat 126 11 := Fin.ext (by change i.val = 11; omega)
                subst i
                exact block_0011
              · have heq : i = Fin.ofNat 126 12 := Fin.ext (by change i.val = 12; omega)
                subst i
                exact block_0012
            · by_cases h_13_15 : i.val < 14
              · have heq : i = Fin.ofNat 126 13 := Fin.ext (by change i.val = 13; omega)
                subst i
                exact block_0013
              · have heq : i = Fin.ofNat 126 14 := Fin.ext (by change i.val = 14; omega)
                subst i
                exact block_0014
      · by_cases h_15_31 : i.val < 23
        · by_cases h_15_23 : i.val < 19
          · by_cases h_15_19 : i.val < 17
            · by_cases h_15_17 : i.val < 16
              · have heq : i = Fin.ofNat 126 15 := Fin.ext (by change i.val = 15; omega)
                subst i
                exact block_0015
              · have heq : i = Fin.ofNat 126 16 := Fin.ext (by change i.val = 16; omega)
                subst i
                exact block_0016
            · by_cases h_17_19 : i.val < 18
              · have heq : i = Fin.ofNat 126 17 := Fin.ext (by change i.val = 17; omega)
                subst i
                exact block_0017
              · have heq : i = Fin.ofNat 126 18 := Fin.ext (by change i.val = 18; omega)
                subst i
                exact block_0018
          · by_cases h_19_23 : i.val < 21
            · by_cases h_19_21 : i.val < 20
              · have heq : i = Fin.ofNat 126 19 := Fin.ext (by change i.val = 19; omega)
                subst i
                exact block_0019
              · have heq : i = Fin.ofNat 126 20 := Fin.ext (by change i.val = 20; omega)
                subst i
                exact block_0020
            · by_cases h_21_23 : i.val < 22
              · have heq : i = Fin.ofNat 126 21 := Fin.ext (by change i.val = 21; omega)
                subst i
                exact block_0021
              · have heq : i = Fin.ofNat 126 22 := Fin.ext (by change i.val = 22; omega)
                subst i
                exact block_0022
        · by_cases h_23_31 : i.val < 27
          · by_cases h_23_27 : i.val < 25
            · by_cases h_23_25 : i.val < 24
              · have heq : i = Fin.ofNat 126 23 := Fin.ext (by change i.val = 23; omega)
                subst i
                exact block_0023
              · have heq : i = Fin.ofNat 126 24 := Fin.ext (by change i.val = 24; omega)
                subst i
                exact block_0024
            · by_cases h_25_27 : i.val < 26
              · have heq : i = Fin.ofNat 126 25 := Fin.ext (by change i.val = 25; omega)
                subst i
                exact block_0025
              · have heq : i = Fin.ofNat 126 26 := Fin.ext (by change i.val = 26; omega)
                subst i
                exact block_0026
          · by_cases h_27_31 : i.val < 29
            · by_cases h_27_29 : i.val < 28
              · have heq : i = Fin.ofNat 126 27 := Fin.ext (by change i.val = 27; omega)
                subst i
                exact block_0027
              · have heq : i = Fin.ofNat 126 28 := Fin.ext (by change i.val = 28; omega)
                subst i
                exact block_0028
            · by_cases h_29_31 : i.val < 30
              · have heq : i = Fin.ofNat 126 29 := Fin.ext (by change i.val = 29; omega)
                subst i
                exact block_0029
              · have heq : i = Fin.ofNat 126 30 := Fin.ext (by change i.val = 30; omega)
                subst i
                exact block_0030
    · by_cases h_31_63 : i.val < 47
      · by_cases h_31_47 : i.val < 39
        · by_cases h_31_39 : i.val < 35
          · by_cases h_31_35 : i.val < 33
            · by_cases h_31_33 : i.val < 32
              · have heq : i = Fin.ofNat 126 31 := Fin.ext (by change i.val = 31; omega)
                subst i
                exact block_0031
              · have heq : i = Fin.ofNat 126 32 := Fin.ext (by change i.val = 32; omega)
                subst i
                exact block_0032
            · by_cases h_33_35 : i.val < 34
              · have heq : i = Fin.ofNat 126 33 := Fin.ext (by change i.val = 33; omega)
                subst i
                exact block_0033
              · have heq : i = Fin.ofNat 126 34 := Fin.ext (by change i.val = 34; omega)
                subst i
                exact block_0034
          · by_cases h_35_39 : i.val < 37
            · by_cases h_35_37 : i.val < 36
              · have heq : i = Fin.ofNat 126 35 := Fin.ext (by change i.val = 35; omega)
                subst i
                exact block_0035
              · have heq : i = Fin.ofNat 126 36 := Fin.ext (by change i.val = 36; omega)
                subst i
                exact block_0036
            · by_cases h_37_39 : i.val < 38
              · have heq : i = Fin.ofNat 126 37 := Fin.ext (by change i.val = 37; omega)
                subst i
                exact block_0037
              · have heq : i = Fin.ofNat 126 38 := Fin.ext (by change i.val = 38; omega)
                subst i
                exact block_0038
        · by_cases h_39_47 : i.val < 43
          · by_cases h_39_43 : i.val < 41
            · by_cases h_39_41 : i.val < 40
              · have heq : i = Fin.ofNat 126 39 := Fin.ext (by change i.val = 39; omega)
                subst i
                exact block_0039
              · have heq : i = Fin.ofNat 126 40 := Fin.ext (by change i.val = 40; omega)
                subst i
                exact block_0040
            · by_cases h_41_43 : i.val < 42
              · have heq : i = Fin.ofNat 126 41 := Fin.ext (by change i.val = 41; omega)
                subst i
                exact block_0041
              · have heq : i = Fin.ofNat 126 42 := Fin.ext (by change i.val = 42; omega)
                subst i
                exact block_0042
          · by_cases h_43_47 : i.val < 45
            · by_cases h_43_45 : i.val < 44
              · have heq : i = Fin.ofNat 126 43 := Fin.ext (by change i.val = 43; omega)
                subst i
                exact block_0043
              · have heq : i = Fin.ofNat 126 44 := Fin.ext (by change i.val = 44; omega)
                subst i
                exact block_0044
            · by_cases h_45_47 : i.val < 46
              · have heq : i = Fin.ofNat 126 45 := Fin.ext (by change i.val = 45; omega)
                subst i
                exact block_0045
              · have heq : i = Fin.ofNat 126 46 := Fin.ext (by change i.val = 46; omega)
                subst i
                exact block_0046
      · by_cases h_47_63 : i.val < 55
        · by_cases h_47_55 : i.val < 51
          · by_cases h_47_51 : i.val < 49
            · by_cases h_47_49 : i.val < 48
              · have heq : i = Fin.ofNat 126 47 := Fin.ext (by change i.val = 47; omega)
                subst i
                exact block_0047
              · have heq : i = Fin.ofNat 126 48 := Fin.ext (by change i.val = 48; omega)
                subst i
                exact block_0048
            · by_cases h_49_51 : i.val < 50
              · have heq : i = Fin.ofNat 126 49 := Fin.ext (by change i.val = 49; omega)
                subst i
                exact block_0049
              · have heq : i = Fin.ofNat 126 50 := Fin.ext (by change i.val = 50; omega)
                subst i
                exact block_0050
          · by_cases h_51_55 : i.val < 53
            · by_cases h_51_53 : i.val < 52
              · have heq : i = Fin.ofNat 126 51 := Fin.ext (by change i.val = 51; omega)
                subst i
                exact block_0051
              · have heq : i = Fin.ofNat 126 52 := Fin.ext (by change i.val = 52; omega)
                subst i
                exact block_0052
            · by_cases h_53_55 : i.val < 54
              · have heq : i = Fin.ofNat 126 53 := Fin.ext (by change i.val = 53; omega)
                subst i
                exact block_0053
              · have heq : i = Fin.ofNat 126 54 := Fin.ext (by change i.val = 54; omega)
                subst i
                exact block_0054
        · by_cases h_55_63 : i.val < 59
          · by_cases h_55_59 : i.val < 57
            · by_cases h_55_57 : i.val < 56
              · have heq : i = Fin.ofNat 126 55 := Fin.ext (by change i.val = 55; omega)
                subst i
                exact block_0055
              · have heq : i = Fin.ofNat 126 56 := Fin.ext (by change i.val = 56; omega)
                subst i
                exact block_0056
            · by_cases h_57_59 : i.val < 58
              · have heq : i = Fin.ofNat 126 57 := Fin.ext (by change i.val = 57; omega)
                subst i
                exact block_0057
              · have heq : i = Fin.ofNat 126 58 := Fin.ext (by change i.val = 58; omega)
                subst i
                exact block_0058
          · by_cases h_59_63 : i.val < 61
            · by_cases h_59_61 : i.val < 60
              · have heq : i = Fin.ofNat 126 59 := Fin.ext (by change i.val = 59; omega)
                subst i
                exact block_0059
              · have heq : i = Fin.ofNat 126 60 := Fin.ext (by change i.val = 60; omega)
                subst i
                exact block_0060
            · by_cases h_61_63 : i.val < 62
              · have heq : i = Fin.ofNat 126 61 := Fin.ext (by change i.val = 61; omega)
                subst i
                exact block_0061
              · have heq : i = Fin.ofNat 126 62 := Fin.ext (by change i.val = 62; omega)
                subst i
                exact block_0062
  · by_cases h_63_126 : i.val < 94
    · by_cases h_63_94 : i.val < 78
      · by_cases h_63_78 : i.val < 70
        · by_cases h_63_70 : i.val < 66
          · by_cases h_63_66 : i.val < 64
            · have heq : i = Fin.ofNat 126 63 := Fin.ext (by change i.val = 63; omega)
              subst i
              exact block_0063
            · by_cases h_64_66 : i.val < 65
              · have heq : i = Fin.ofNat 126 64 := Fin.ext (by change i.val = 64; omega)
                subst i
                exact block_0064
              · have heq : i = Fin.ofNat 126 65 := Fin.ext (by change i.val = 65; omega)
                subst i
                exact block_0065
          · by_cases h_66_70 : i.val < 68
            · by_cases h_66_68 : i.val < 67
              · have heq : i = Fin.ofNat 126 66 := Fin.ext (by change i.val = 66; omega)
                subst i
                exact block_0066
              · have heq : i = Fin.ofNat 126 67 := Fin.ext (by change i.val = 67; omega)
                subst i
                exact block_0067
            · by_cases h_68_70 : i.val < 69
              · have heq : i = Fin.ofNat 126 68 := Fin.ext (by change i.val = 68; omega)
                subst i
                exact block_0068
              · have heq : i = Fin.ofNat 126 69 := Fin.ext (by change i.val = 69; omega)
                subst i
                exact block_0069
        · by_cases h_70_78 : i.val < 74
          · by_cases h_70_74 : i.val < 72
            · by_cases h_70_72 : i.val < 71
              · have heq : i = Fin.ofNat 126 70 := Fin.ext (by change i.val = 70; omega)
                subst i
                exact block_0070
              · have heq : i = Fin.ofNat 126 71 := Fin.ext (by change i.val = 71; omega)
                subst i
                exact block_0071
            · by_cases h_72_74 : i.val < 73
              · have heq : i = Fin.ofNat 126 72 := Fin.ext (by change i.val = 72; omega)
                subst i
                exact block_0072
              · have heq : i = Fin.ofNat 126 73 := Fin.ext (by change i.val = 73; omega)
                subst i
                exact block_0073
          · by_cases h_74_78 : i.val < 76
            · by_cases h_74_76 : i.val < 75
              · have heq : i = Fin.ofNat 126 74 := Fin.ext (by change i.val = 74; omega)
                subst i
                exact block_0074
              · have heq : i = Fin.ofNat 126 75 := Fin.ext (by change i.val = 75; omega)
                subst i
                exact block_0075
            · by_cases h_76_78 : i.val < 77
              · have heq : i = Fin.ofNat 126 76 := Fin.ext (by change i.val = 76; omega)
                subst i
                exact block_0076
              · have heq : i = Fin.ofNat 126 77 := Fin.ext (by change i.val = 77; omega)
                subst i
                exact block_0077
      · by_cases h_78_94 : i.val < 86
        · by_cases h_78_86 : i.val < 82
          · by_cases h_78_82 : i.val < 80
            · by_cases h_78_80 : i.val < 79
              · have heq : i = Fin.ofNat 126 78 := Fin.ext (by change i.val = 78; omega)
                subst i
                exact block_0078
              · have heq : i = Fin.ofNat 126 79 := Fin.ext (by change i.val = 79; omega)
                subst i
                exact block_0079
            · by_cases h_80_82 : i.val < 81
              · have heq : i = Fin.ofNat 126 80 := Fin.ext (by change i.val = 80; omega)
                subst i
                exact block_0080
              · have heq : i = Fin.ofNat 126 81 := Fin.ext (by change i.val = 81; omega)
                subst i
                exact block_0081
          · by_cases h_82_86 : i.val < 84
            · by_cases h_82_84 : i.val < 83
              · have heq : i = Fin.ofNat 126 82 := Fin.ext (by change i.val = 82; omega)
                subst i
                exact block_0082
              · have heq : i = Fin.ofNat 126 83 := Fin.ext (by change i.val = 83; omega)
                subst i
                exact block_0083
            · by_cases h_84_86 : i.val < 85
              · have heq : i = Fin.ofNat 126 84 := Fin.ext (by change i.val = 84; omega)
                subst i
                exact block_0084
              · have heq : i = Fin.ofNat 126 85 := Fin.ext (by change i.val = 85; omega)
                subst i
                exact block_0085
        · by_cases h_86_94 : i.val < 90
          · by_cases h_86_90 : i.val < 88
            · by_cases h_86_88 : i.val < 87
              · have heq : i = Fin.ofNat 126 86 := Fin.ext (by change i.val = 86; omega)
                subst i
                exact block_0086
              · have heq : i = Fin.ofNat 126 87 := Fin.ext (by change i.val = 87; omega)
                subst i
                exact block_0087
            · by_cases h_88_90 : i.val < 89
              · have heq : i = Fin.ofNat 126 88 := Fin.ext (by change i.val = 88; omega)
                subst i
                exact block_0088
              · have heq : i = Fin.ofNat 126 89 := Fin.ext (by change i.val = 89; omega)
                subst i
                exact block_0089
          · by_cases h_90_94 : i.val < 92
            · by_cases h_90_92 : i.val < 91
              · have heq : i = Fin.ofNat 126 90 := Fin.ext (by change i.val = 90; omega)
                subst i
                exact block_0090
              · have heq : i = Fin.ofNat 126 91 := Fin.ext (by change i.val = 91; omega)
                subst i
                exact block_0091
            · by_cases h_92_94 : i.val < 93
              · have heq : i = Fin.ofNat 126 92 := Fin.ext (by change i.val = 92; omega)
                subst i
                exact block_0092
              · have heq : i = Fin.ofNat 126 93 := Fin.ext (by change i.val = 93; omega)
                subst i
                exact block_0093
    · by_cases h_94_126 : i.val < 110
      · by_cases h_94_110 : i.val < 102
        · by_cases h_94_102 : i.val < 98
          · by_cases h_94_98 : i.val < 96
            · by_cases h_94_96 : i.val < 95
              · have heq : i = Fin.ofNat 126 94 := Fin.ext (by change i.val = 94; omega)
                subst i
                exact block_0094
              · have heq : i = Fin.ofNat 126 95 := Fin.ext (by change i.val = 95; omega)
                subst i
                exact block_0095
            · by_cases h_96_98 : i.val < 97
              · have heq : i = Fin.ofNat 126 96 := Fin.ext (by change i.val = 96; omega)
                subst i
                exact block_0096
              · have heq : i = Fin.ofNat 126 97 := Fin.ext (by change i.val = 97; omega)
                subst i
                exact block_0097
          · by_cases h_98_102 : i.val < 100
            · by_cases h_98_100 : i.val < 99
              · have heq : i = Fin.ofNat 126 98 := Fin.ext (by change i.val = 98; omega)
                subst i
                exact block_0098
              · have heq : i = Fin.ofNat 126 99 := Fin.ext (by change i.val = 99; omega)
                subst i
                exact block_0099
            · by_cases h_100_102 : i.val < 101
              · have heq : i = Fin.ofNat 126 100 := Fin.ext (by change i.val = 100; omega)
                subst i
                exact block_0100
              · have heq : i = Fin.ofNat 126 101 := Fin.ext (by change i.val = 101; omega)
                subst i
                exact block_0101
        · by_cases h_102_110 : i.val < 106
          · by_cases h_102_106 : i.val < 104
            · by_cases h_102_104 : i.val < 103
              · have heq : i = Fin.ofNat 126 102 := Fin.ext (by change i.val = 102; omega)
                subst i
                exact block_0102
              · have heq : i = Fin.ofNat 126 103 := Fin.ext (by change i.val = 103; omega)
                subst i
                exact block_0103
            · by_cases h_104_106 : i.val < 105
              · have heq : i = Fin.ofNat 126 104 := Fin.ext (by change i.val = 104; omega)
                subst i
                exact block_0104
              · have heq : i = Fin.ofNat 126 105 := Fin.ext (by change i.val = 105; omega)
                subst i
                exact block_0105
          · by_cases h_106_110 : i.val < 108
            · by_cases h_106_108 : i.val < 107
              · have heq : i = Fin.ofNat 126 106 := Fin.ext (by change i.val = 106; omega)
                subst i
                exact block_0106
              · have heq : i = Fin.ofNat 126 107 := Fin.ext (by change i.val = 107; omega)
                subst i
                exact block_0107
            · by_cases h_108_110 : i.val < 109
              · have heq : i = Fin.ofNat 126 108 := Fin.ext (by change i.val = 108; omega)
                subst i
                exact block_0108
              · have heq : i = Fin.ofNat 126 109 := Fin.ext (by change i.val = 109; omega)
                subst i
                exact block_0109
      · by_cases h_110_126 : i.val < 118
        · by_cases h_110_118 : i.val < 114
          · by_cases h_110_114 : i.val < 112
            · by_cases h_110_112 : i.val < 111
              · have heq : i = Fin.ofNat 126 110 := Fin.ext (by change i.val = 110; omega)
                subst i
                exact block_0110
              · have heq : i = Fin.ofNat 126 111 := Fin.ext (by change i.val = 111; omega)
                subst i
                exact block_0111
            · by_cases h_112_114 : i.val < 113
              · have heq : i = Fin.ofNat 126 112 := Fin.ext (by change i.val = 112; omega)
                subst i
                exact block_0112
              · have heq : i = Fin.ofNat 126 113 := Fin.ext (by change i.val = 113; omega)
                subst i
                exact block_0113
          · by_cases h_114_118 : i.val < 116
            · by_cases h_114_116 : i.val < 115
              · have heq : i = Fin.ofNat 126 114 := Fin.ext (by change i.val = 114; omega)
                subst i
                exact block_0114
              · have heq : i = Fin.ofNat 126 115 := Fin.ext (by change i.val = 115; omega)
                subst i
                exact block_0115
            · by_cases h_116_118 : i.val < 117
              · have heq : i = Fin.ofNat 126 116 := Fin.ext (by change i.val = 116; omega)
                subst i
                exact block_0116
              · have heq : i = Fin.ofNat 126 117 := Fin.ext (by change i.val = 117; omega)
                subst i
                exact block_0117
        · by_cases h_118_126 : i.val < 122
          · by_cases h_118_122 : i.val < 120
            · by_cases h_118_120 : i.val < 119
              · have heq : i = Fin.ofNat 126 118 := Fin.ext (by change i.val = 118; omega)
                subst i
                exact block_0118
              · have heq : i = Fin.ofNat 126 119 := Fin.ext (by change i.val = 119; omega)
                subst i
                exact block_0119
            · by_cases h_120_122 : i.val < 121
              · have heq : i = Fin.ofNat 126 120 := Fin.ext (by change i.val = 120; omega)
                subst i
                exact block_0120
              · have heq : i = Fin.ofNat 126 121 := Fin.ext (by change i.val = 121; omega)
                subst i
                exact block_0121
          · by_cases h_122_126 : i.val < 124
            · by_cases h_122_124 : i.val < 123
              · have heq : i = Fin.ofNat 126 122 := Fin.ext (by change i.val = 122; omega)
                subst i
                exact block_0122
              · have heq : i = Fin.ofNat 126 123 := Fin.ext (by change i.val = 123; omega)
                subst i
                exact block_0123
            · by_cases h_124_126 : i.val < 125
              · have heq : i = Fin.ofNat 126 124 := Fin.ext (by change i.val = 124; omega)
                subst i
                exact block_0124
              · have heq : i = Fin.ofNat 126 125 := Fin.ext (by change i.val = 125; omega)
                subst i
                exact block_0125
end Papers.RationalityTen.RootedCanonical.RootedSixExtra06.T4
