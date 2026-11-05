module
prelude
public import RootedSixExtra05CanonicalS5T0Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S5T0
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 5 (raw i) template root
      FacetUniverses.RootedSixExtra05.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 123 := i.isLt
  by_cases h_0_123 : i.val < 61
  · by_cases h_0_61 : i.val < 30
    · by_cases h_0_30 : i.val < 15
      · by_cases h_0_15 : i.val < 7
        · by_cases h_0_7 : i.val < 3
          · by_cases h_0_3 : i.val < 1
            · have heq : i = Fin.ofNat 123 0 := Fin.ext (by change i.val = 0; omega)
              subst i
              exact block_0000
            · by_cases h_1_3 : i.val < 2
              · have heq : i = Fin.ofNat 123 1 := Fin.ext (by change i.val = 1; omega)
                subst i
                exact block_0001
              · have heq : i = Fin.ofNat 123 2 := Fin.ext (by change i.val = 2; omega)
                subst i
                exact block_0002
          · by_cases h_3_7 : i.val < 5
            · by_cases h_3_5 : i.val < 4
              · have heq : i = Fin.ofNat 123 3 := Fin.ext (by change i.val = 3; omega)
                subst i
                exact block_0003
              · have heq : i = Fin.ofNat 123 4 := Fin.ext (by change i.val = 4; omega)
                subst i
                exact block_0004
            · by_cases h_5_7 : i.val < 6
              · have heq : i = Fin.ofNat 123 5 := Fin.ext (by change i.val = 5; omega)
                subst i
                exact block_0005
              · have heq : i = Fin.ofNat 123 6 := Fin.ext (by change i.val = 6; omega)
                subst i
                exact block_0006
        · by_cases h_7_15 : i.val < 11
          · by_cases h_7_11 : i.val < 9
            · by_cases h_7_9 : i.val < 8
              · have heq : i = Fin.ofNat 123 7 := Fin.ext (by change i.val = 7; omega)
                subst i
                exact block_0007
              · have heq : i = Fin.ofNat 123 8 := Fin.ext (by change i.val = 8; omega)
                subst i
                exact block_0008
            · by_cases h_9_11 : i.val < 10
              · have heq : i = Fin.ofNat 123 9 := Fin.ext (by change i.val = 9; omega)
                subst i
                exact block_0009
              · have heq : i = Fin.ofNat 123 10 := Fin.ext (by change i.val = 10; omega)
                subst i
                exact block_0010
          · by_cases h_11_15 : i.val < 13
            · by_cases h_11_13 : i.val < 12
              · have heq : i = Fin.ofNat 123 11 := Fin.ext (by change i.val = 11; omega)
                subst i
                exact block_0011
              · have heq : i = Fin.ofNat 123 12 := Fin.ext (by change i.val = 12; omega)
                subst i
                exact block_0012
            · by_cases h_13_15 : i.val < 14
              · have heq : i = Fin.ofNat 123 13 := Fin.ext (by change i.val = 13; omega)
                subst i
                exact block_0013
              · have heq : i = Fin.ofNat 123 14 := Fin.ext (by change i.val = 14; omega)
                subst i
                exact block_0014
      · by_cases h_15_30 : i.val < 22
        · by_cases h_15_22 : i.val < 18
          · by_cases h_15_18 : i.val < 16
            · have heq : i = Fin.ofNat 123 15 := Fin.ext (by change i.val = 15; omega)
              subst i
              exact block_0015
            · by_cases h_16_18 : i.val < 17
              · have heq : i = Fin.ofNat 123 16 := Fin.ext (by change i.val = 16; omega)
                subst i
                exact block_0016
              · have heq : i = Fin.ofNat 123 17 := Fin.ext (by change i.val = 17; omega)
                subst i
                exact block_0017
          · by_cases h_18_22 : i.val < 20
            · by_cases h_18_20 : i.val < 19
              · have heq : i = Fin.ofNat 123 18 := Fin.ext (by change i.val = 18; omega)
                subst i
                exact block_0018
              · have heq : i = Fin.ofNat 123 19 := Fin.ext (by change i.val = 19; omega)
                subst i
                exact block_0019
            · by_cases h_20_22 : i.val < 21
              · have heq : i = Fin.ofNat 123 20 := Fin.ext (by change i.val = 20; omega)
                subst i
                exact block_0020
              · have heq : i = Fin.ofNat 123 21 := Fin.ext (by change i.val = 21; omega)
                subst i
                exact block_0021
        · by_cases h_22_30 : i.val < 26
          · by_cases h_22_26 : i.val < 24
            · by_cases h_22_24 : i.val < 23
              · have heq : i = Fin.ofNat 123 22 := Fin.ext (by change i.val = 22; omega)
                subst i
                exact block_0022
              · have heq : i = Fin.ofNat 123 23 := Fin.ext (by change i.val = 23; omega)
                subst i
                exact block_0023
            · by_cases h_24_26 : i.val < 25
              · have heq : i = Fin.ofNat 123 24 := Fin.ext (by change i.val = 24; omega)
                subst i
                exact block_0024
              · have heq : i = Fin.ofNat 123 25 := Fin.ext (by change i.val = 25; omega)
                subst i
                exact block_0025
          · by_cases h_26_30 : i.val < 28
            · by_cases h_26_28 : i.val < 27
              · have heq : i = Fin.ofNat 123 26 := Fin.ext (by change i.val = 26; omega)
                subst i
                exact block_0026
              · have heq : i = Fin.ofNat 123 27 := Fin.ext (by change i.val = 27; omega)
                subst i
                exact block_0027
            · by_cases h_28_30 : i.val < 29
              · have heq : i = Fin.ofNat 123 28 := Fin.ext (by change i.val = 28; omega)
                subst i
                exact block_0028
              · have heq : i = Fin.ofNat 123 29 := Fin.ext (by change i.val = 29; omega)
                subst i
                exact block_0029
    · by_cases h_30_61 : i.val < 45
      · by_cases h_30_45 : i.val < 37
        · by_cases h_30_37 : i.val < 33
          · by_cases h_30_33 : i.val < 31
            · have heq : i = Fin.ofNat 123 30 := Fin.ext (by change i.val = 30; omega)
              subst i
              exact block_0030
            · by_cases h_31_33 : i.val < 32
              · have heq : i = Fin.ofNat 123 31 := Fin.ext (by change i.val = 31; omega)
                subst i
                exact block_0031
              · have heq : i = Fin.ofNat 123 32 := Fin.ext (by change i.val = 32; omega)
                subst i
                exact block_0032
          · by_cases h_33_37 : i.val < 35
            · by_cases h_33_35 : i.val < 34
              · have heq : i = Fin.ofNat 123 33 := Fin.ext (by change i.val = 33; omega)
                subst i
                exact block_0033
              · have heq : i = Fin.ofNat 123 34 := Fin.ext (by change i.val = 34; omega)
                subst i
                exact block_0034
            · by_cases h_35_37 : i.val < 36
              · have heq : i = Fin.ofNat 123 35 := Fin.ext (by change i.val = 35; omega)
                subst i
                exact block_0035
              · have heq : i = Fin.ofNat 123 36 := Fin.ext (by change i.val = 36; omega)
                subst i
                exact block_0036
        · by_cases h_37_45 : i.val < 41
          · by_cases h_37_41 : i.val < 39
            · by_cases h_37_39 : i.val < 38
              · have heq : i = Fin.ofNat 123 37 := Fin.ext (by change i.val = 37; omega)
                subst i
                exact block_0037
              · have heq : i = Fin.ofNat 123 38 := Fin.ext (by change i.val = 38; omega)
                subst i
                exact block_0038
            · by_cases h_39_41 : i.val < 40
              · have heq : i = Fin.ofNat 123 39 := Fin.ext (by change i.val = 39; omega)
                subst i
                exact block_0039
              · have heq : i = Fin.ofNat 123 40 := Fin.ext (by change i.val = 40; omega)
                subst i
                exact block_0040
          · by_cases h_41_45 : i.val < 43
            · by_cases h_41_43 : i.val < 42
              · have heq : i = Fin.ofNat 123 41 := Fin.ext (by change i.val = 41; omega)
                subst i
                exact block_0041
              · have heq : i = Fin.ofNat 123 42 := Fin.ext (by change i.val = 42; omega)
                subst i
                exact block_0042
            · by_cases h_43_45 : i.val < 44
              · have heq : i = Fin.ofNat 123 43 := Fin.ext (by change i.val = 43; omega)
                subst i
                exact block_0043
              · have heq : i = Fin.ofNat 123 44 := Fin.ext (by change i.val = 44; omega)
                subst i
                exact block_0044
      · by_cases h_45_61 : i.val < 53
        · by_cases h_45_53 : i.val < 49
          · by_cases h_45_49 : i.val < 47
            · by_cases h_45_47 : i.val < 46
              · have heq : i = Fin.ofNat 123 45 := Fin.ext (by change i.val = 45; omega)
                subst i
                exact block_0045
              · have heq : i = Fin.ofNat 123 46 := Fin.ext (by change i.val = 46; omega)
                subst i
                exact block_0046
            · by_cases h_47_49 : i.val < 48
              · have heq : i = Fin.ofNat 123 47 := Fin.ext (by change i.val = 47; omega)
                subst i
                exact block_0047
              · have heq : i = Fin.ofNat 123 48 := Fin.ext (by change i.val = 48; omega)
                subst i
                exact block_0048
          · by_cases h_49_53 : i.val < 51
            · by_cases h_49_51 : i.val < 50
              · have heq : i = Fin.ofNat 123 49 := Fin.ext (by change i.val = 49; omega)
                subst i
                exact block_0049
              · have heq : i = Fin.ofNat 123 50 := Fin.ext (by change i.val = 50; omega)
                subst i
                exact block_0050
            · by_cases h_51_53 : i.val < 52
              · have heq : i = Fin.ofNat 123 51 := Fin.ext (by change i.val = 51; omega)
                subst i
                exact block_0051
              · have heq : i = Fin.ofNat 123 52 := Fin.ext (by change i.val = 52; omega)
                subst i
                exact block_0052
        · by_cases h_53_61 : i.val < 57
          · by_cases h_53_57 : i.val < 55
            · by_cases h_53_55 : i.val < 54
              · have heq : i = Fin.ofNat 123 53 := Fin.ext (by change i.val = 53; omega)
                subst i
                exact block_0053
              · have heq : i = Fin.ofNat 123 54 := Fin.ext (by change i.val = 54; omega)
                subst i
                exact block_0054
            · by_cases h_55_57 : i.val < 56
              · have heq : i = Fin.ofNat 123 55 := Fin.ext (by change i.val = 55; omega)
                subst i
                exact block_0055
              · have heq : i = Fin.ofNat 123 56 := Fin.ext (by change i.val = 56; omega)
                subst i
                exact block_0056
          · by_cases h_57_61 : i.val < 59
            · by_cases h_57_59 : i.val < 58
              · have heq : i = Fin.ofNat 123 57 := Fin.ext (by change i.val = 57; omega)
                subst i
                exact block_0057
              · have heq : i = Fin.ofNat 123 58 := Fin.ext (by change i.val = 58; omega)
                subst i
                exact block_0058
            · by_cases h_59_61 : i.val < 60
              · have heq : i = Fin.ofNat 123 59 := Fin.ext (by change i.val = 59; omega)
                subst i
                exact block_0059
              · have heq : i = Fin.ofNat 123 60 := Fin.ext (by change i.val = 60; omega)
                subst i
                exact block_0060
  · by_cases h_61_123 : i.val < 92
    · by_cases h_61_92 : i.val < 76
      · by_cases h_61_76 : i.val < 68
        · by_cases h_61_68 : i.val < 64
          · by_cases h_61_64 : i.val < 62
            · have heq : i = Fin.ofNat 123 61 := Fin.ext (by change i.val = 61; omega)
              subst i
              exact block_0061
            · by_cases h_62_64 : i.val < 63
              · have heq : i = Fin.ofNat 123 62 := Fin.ext (by change i.val = 62; omega)
                subst i
                exact block_0062
              · have heq : i = Fin.ofNat 123 63 := Fin.ext (by change i.val = 63; omega)
                subst i
                exact block_0063
          · by_cases h_64_68 : i.val < 66
            · by_cases h_64_66 : i.val < 65
              · have heq : i = Fin.ofNat 123 64 := Fin.ext (by change i.val = 64; omega)
                subst i
                exact block_0064
              · have heq : i = Fin.ofNat 123 65 := Fin.ext (by change i.val = 65; omega)
                subst i
                exact block_0065
            · by_cases h_66_68 : i.val < 67
              · have heq : i = Fin.ofNat 123 66 := Fin.ext (by change i.val = 66; omega)
                subst i
                exact block_0066
              · have heq : i = Fin.ofNat 123 67 := Fin.ext (by change i.val = 67; omega)
                subst i
                exact block_0067
        · by_cases h_68_76 : i.val < 72
          · by_cases h_68_72 : i.val < 70
            · by_cases h_68_70 : i.val < 69
              · have heq : i = Fin.ofNat 123 68 := Fin.ext (by change i.val = 68; omega)
                subst i
                exact block_0068
              · have heq : i = Fin.ofNat 123 69 := Fin.ext (by change i.val = 69; omega)
                subst i
                exact block_0069
            · by_cases h_70_72 : i.val < 71
              · have heq : i = Fin.ofNat 123 70 := Fin.ext (by change i.val = 70; omega)
                subst i
                exact block_0070
              · have heq : i = Fin.ofNat 123 71 := Fin.ext (by change i.val = 71; omega)
                subst i
                exact block_0071
          · by_cases h_72_76 : i.val < 74
            · by_cases h_72_74 : i.val < 73
              · have heq : i = Fin.ofNat 123 72 := Fin.ext (by change i.val = 72; omega)
                subst i
                exact block_0072
              · have heq : i = Fin.ofNat 123 73 := Fin.ext (by change i.val = 73; omega)
                subst i
                exact block_0073
            · by_cases h_74_76 : i.val < 75
              · have heq : i = Fin.ofNat 123 74 := Fin.ext (by change i.val = 74; omega)
                subst i
                exact block_0074
              · have heq : i = Fin.ofNat 123 75 := Fin.ext (by change i.val = 75; omega)
                subst i
                exact block_0075
      · by_cases h_76_92 : i.val < 84
        · by_cases h_76_84 : i.val < 80
          · by_cases h_76_80 : i.val < 78
            · by_cases h_76_78 : i.val < 77
              · have heq : i = Fin.ofNat 123 76 := Fin.ext (by change i.val = 76; omega)
                subst i
                exact block_0076
              · have heq : i = Fin.ofNat 123 77 := Fin.ext (by change i.val = 77; omega)
                subst i
                exact block_0077
            · by_cases h_78_80 : i.val < 79
              · have heq : i = Fin.ofNat 123 78 := Fin.ext (by change i.val = 78; omega)
                subst i
                exact block_0078
              · have heq : i = Fin.ofNat 123 79 := Fin.ext (by change i.val = 79; omega)
                subst i
                exact block_0079
          · by_cases h_80_84 : i.val < 82
            · by_cases h_80_82 : i.val < 81
              · have heq : i = Fin.ofNat 123 80 := Fin.ext (by change i.val = 80; omega)
                subst i
                exact block_0080
              · have heq : i = Fin.ofNat 123 81 := Fin.ext (by change i.val = 81; omega)
                subst i
                exact block_0081
            · by_cases h_82_84 : i.val < 83
              · have heq : i = Fin.ofNat 123 82 := Fin.ext (by change i.val = 82; omega)
                subst i
                exact block_0082
              · have heq : i = Fin.ofNat 123 83 := Fin.ext (by change i.val = 83; omega)
                subst i
                exact block_0083
        · by_cases h_84_92 : i.val < 88
          · by_cases h_84_88 : i.val < 86
            · by_cases h_84_86 : i.val < 85
              · have heq : i = Fin.ofNat 123 84 := Fin.ext (by change i.val = 84; omega)
                subst i
                exact block_0084
              · have heq : i = Fin.ofNat 123 85 := Fin.ext (by change i.val = 85; omega)
                subst i
                exact block_0085
            · by_cases h_86_88 : i.val < 87
              · have heq : i = Fin.ofNat 123 86 := Fin.ext (by change i.val = 86; omega)
                subst i
                exact block_0086
              · have heq : i = Fin.ofNat 123 87 := Fin.ext (by change i.val = 87; omega)
                subst i
                exact block_0087
          · by_cases h_88_92 : i.val < 90
            · by_cases h_88_90 : i.val < 89
              · have heq : i = Fin.ofNat 123 88 := Fin.ext (by change i.val = 88; omega)
                subst i
                exact block_0088
              · have heq : i = Fin.ofNat 123 89 := Fin.ext (by change i.val = 89; omega)
                subst i
                exact block_0089
            · by_cases h_90_92 : i.val < 91
              · have heq : i = Fin.ofNat 123 90 := Fin.ext (by change i.val = 90; omega)
                subst i
                exact block_0090
              · have heq : i = Fin.ofNat 123 91 := Fin.ext (by change i.val = 91; omega)
                subst i
                exact block_0091
    · by_cases h_92_123 : i.val < 107
      · by_cases h_92_107 : i.val < 99
        · by_cases h_92_99 : i.val < 95
          · by_cases h_92_95 : i.val < 93
            · have heq : i = Fin.ofNat 123 92 := Fin.ext (by change i.val = 92; omega)
              subst i
              exact block_0092
            · by_cases h_93_95 : i.val < 94
              · have heq : i = Fin.ofNat 123 93 := Fin.ext (by change i.val = 93; omega)
                subst i
                exact block_0093
              · have heq : i = Fin.ofNat 123 94 := Fin.ext (by change i.val = 94; omega)
                subst i
                exact block_0094
          · by_cases h_95_99 : i.val < 97
            · by_cases h_95_97 : i.val < 96
              · have heq : i = Fin.ofNat 123 95 := Fin.ext (by change i.val = 95; omega)
                subst i
                exact block_0095
              · have heq : i = Fin.ofNat 123 96 := Fin.ext (by change i.val = 96; omega)
                subst i
                exact block_0096
            · by_cases h_97_99 : i.val < 98
              · have heq : i = Fin.ofNat 123 97 := Fin.ext (by change i.val = 97; omega)
                subst i
                exact block_0097
              · have heq : i = Fin.ofNat 123 98 := Fin.ext (by change i.val = 98; omega)
                subst i
                exact block_0098
        · by_cases h_99_107 : i.val < 103
          · by_cases h_99_103 : i.val < 101
            · by_cases h_99_101 : i.val < 100
              · have heq : i = Fin.ofNat 123 99 := Fin.ext (by change i.val = 99; omega)
                subst i
                exact block_0099
              · have heq : i = Fin.ofNat 123 100 := Fin.ext (by change i.val = 100; omega)
                subst i
                exact block_0100
            · by_cases h_101_103 : i.val < 102
              · have heq : i = Fin.ofNat 123 101 := Fin.ext (by change i.val = 101; omega)
                subst i
                exact block_0101
              · have heq : i = Fin.ofNat 123 102 := Fin.ext (by change i.val = 102; omega)
                subst i
                exact block_0102
          · by_cases h_103_107 : i.val < 105
            · by_cases h_103_105 : i.val < 104
              · have heq : i = Fin.ofNat 123 103 := Fin.ext (by change i.val = 103; omega)
                subst i
                exact block_0103
              · have heq : i = Fin.ofNat 123 104 := Fin.ext (by change i.val = 104; omega)
                subst i
                exact block_0104
            · by_cases h_105_107 : i.val < 106
              · have heq : i = Fin.ofNat 123 105 := Fin.ext (by change i.val = 105; omega)
                subst i
                exact block_0105
              · have heq : i = Fin.ofNat 123 106 := Fin.ext (by change i.val = 106; omega)
                subst i
                exact block_0106
      · by_cases h_107_123 : i.val < 115
        · by_cases h_107_115 : i.val < 111
          · by_cases h_107_111 : i.val < 109
            · by_cases h_107_109 : i.val < 108
              · have heq : i = Fin.ofNat 123 107 := Fin.ext (by change i.val = 107; omega)
                subst i
                exact block_0107
              · have heq : i = Fin.ofNat 123 108 := Fin.ext (by change i.val = 108; omega)
                subst i
                exact block_0108
            · by_cases h_109_111 : i.val < 110
              · have heq : i = Fin.ofNat 123 109 := Fin.ext (by change i.val = 109; omega)
                subst i
                exact block_0109
              · have heq : i = Fin.ofNat 123 110 := Fin.ext (by change i.val = 110; omega)
                subst i
                exact block_0110
          · by_cases h_111_115 : i.val < 113
            · by_cases h_111_113 : i.val < 112
              · have heq : i = Fin.ofNat 123 111 := Fin.ext (by change i.val = 111; omega)
                subst i
                exact block_0111
              · have heq : i = Fin.ofNat 123 112 := Fin.ext (by change i.val = 112; omega)
                subst i
                exact block_0112
            · by_cases h_113_115 : i.val < 114
              · have heq : i = Fin.ofNat 123 113 := Fin.ext (by change i.val = 113; omega)
                subst i
                exact block_0113
              · have heq : i = Fin.ofNat 123 114 := Fin.ext (by change i.val = 114; omega)
                subst i
                exact block_0114
        · by_cases h_115_123 : i.val < 119
          · by_cases h_115_119 : i.val < 117
            · by_cases h_115_117 : i.val < 116
              · have heq : i = Fin.ofNat 123 115 := Fin.ext (by change i.val = 115; omega)
                subst i
                exact block_0115
              · have heq : i = Fin.ofNat 123 116 := Fin.ext (by change i.val = 116; omega)
                subst i
                exact block_0116
            · by_cases h_117_119 : i.val < 118
              · have heq : i = Fin.ofNat 123 117 := Fin.ext (by change i.val = 117; omega)
                subst i
                exact block_0117
              · have heq : i = Fin.ofNat 123 118 := Fin.ext (by change i.val = 118; omega)
                subst i
                exact block_0118
          · by_cases h_119_123 : i.val < 121
            · by_cases h_119_121 : i.val < 120
              · have heq : i = Fin.ofNat 123 119 := Fin.ext (by change i.val = 119; omega)
                subst i
                exact block_0119
              · have heq : i = Fin.ofNat 123 120 := Fin.ext (by change i.val = 120; omega)
                subst i
                exact block_0120
            · by_cases h_121_123 : i.val < 122
              · have heq : i = Fin.ofNat 123 121 := Fin.ext (by change i.val = 121; omega)
                subst i
                exact block_0121
              · have heq : i = Fin.ofNat 123 122 := Fin.ext (by change i.val = 122; omega)
                subst i
                exact block_0122
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S5T0
