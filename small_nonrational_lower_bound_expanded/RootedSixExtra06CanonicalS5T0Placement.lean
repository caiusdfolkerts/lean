module
prelude
public import RootedSixExtra06CanonicalS5T0Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S5T0
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 5 (raw i) template root
      FacetUniverses.RootedSixExtra06.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 150 := i.isLt
  by_cases h_0_150 : i.val < 75
  · by_cases h_0_75 : i.val < 37
    · by_cases h_0_37 : i.val < 18
      · by_cases h_0_18 : i.val < 9
        · by_cases h_0_9 : i.val < 4
          · by_cases h_0_4 : i.val < 2
            · by_cases h_0_2 : i.val < 1
              · have heq : i = Fin.ofNat 150 0 := Fin.ext (by change i.val = 0; omega)
                subst i
                exact block_0000
              · have heq : i = Fin.ofNat 150 1 := Fin.ext (by change i.val = 1; omega)
                subst i
                exact block_0001
            · by_cases h_2_4 : i.val < 3
              · have heq : i = Fin.ofNat 150 2 := Fin.ext (by change i.val = 2; omega)
                subst i
                exact block_0002
              · have heq : i = Fin.ofNat 150 3 := Fin.ext (by change i.val = 3; omega)
                subst i
                exact block_0003
          · by_cases h_4_9 : i.val < 6
            · by_cases h_4_6 : i.val < 5
              · have heq : i = Fin.ofNat 150 4 := Fin.ext (by change i.val = 4; omega)
                subst i
                exact block_0004
              · have heq : i = Fin.ofNat 150 5 := Fin.ext (by change i.val = 5; omega)
                subst i
                exact block_0005
            · by_cases h_6_9 : i.val < 7
              · have heq : i = Fin.ofNat 150 6 := Fin.ext (by change i.val = 6; omega)
                subst i
                exact block_0006
              · by_cases h_7_9 : i.val < 8
                · have heq : i = Fin.ofNat 150 7 := Fin.ext (by change i.val = 7; omega)
                  subst i
                  exact block_0007
                · have heq : i = Fin.ofNat 150 8 := Fin.ext (by change i.val = 8; omega)
                  subst i
                  exact block_0008
        · by_cases h_9_18 : i.val < 13
          · by_cases h_9_13 : i.val < 11
            · by_cases h_9_11 : i.val < 10
              · have heq : i = Fin.ofNat 150 9 := Fin.ext (by change i.val = 9; omega)
                subst i
                exact block_0009
              · have heq : i = Fin.ofNat 150 10 := Fin.ext (by change i.val = 10; omega)
                subst i
                exact block_0010
            · by_cases h_11_13 : i.val < 12
              · have heq : i = Fin.ofNat 150 11 := Fin.ext (by change i.val = 11; omega)
                subst i
                exact block_0011
              · have heq : i = Fin.ofNat 150 12 := Fin.ext (by change i.val = 12; omega)
                subst i
                exact block_0012
          · by_cases h_13_18 : i.val < 15
            · by_cases h_13_15 : i.val < 14
              · have heq : i = Fin.ofNat 150 13 := Fin.ext (by change i.val = 13; omega)
                subst i
                exact block_0013
              · have heq : i = Fin.ofNat 150 14 := Fin.ext (by change i.val = 14; omega)
                subst i
                exact block_0014
            · by_cases h_15_18 : i.val < 16
              · have heq : i = Fin.ofNat 150 15 := Fin.ext (by change i.val = 15; omega)
                subst i
                exact block_0015
              · by_cases h_16_18 : i.val < 17
                · have heq : i = Fin.ofNat 150 16 := Fin.ext (by change i.val = 16; omega)
                  subst i
                  exact block_0016
                · have heq : i = Fin.ofNat 150 17 := Fin.ext (by change i.val = 17; omega)
                  subst i
                  exact block_0017
      · by_cases h_18_37 : i.val < 27
        · by_cases h_18_27 : i.val < 22
          · by_cases h_18_22 : i.val < 20
            · by_cases h_18_20 : i.val < 19
              · have heq : i = Fin.ofNat 150 18 := Fin.ext (by change i.val = 18; omega)
                subst i
                exact block_0018
              · have heq : i = Fin.ofNat 150 19 := Fin.ext (by change i.val = 19; omega)
                subst i
                exact block_0019
            · by_cases h_20_22 : i.val < 21
              · have heq : i = Fin.ofNat 150 20 := Fin.ext (by change i.val = 20; omega)
                subst i
                exact block_0020
              · have heq : i = Fin.ofNat 150 21 := Fin.ext (by change i.val = 21; omega)
                subst i
                exact block_0021
          · by_cases h_22_27 : i.val < 24
            · by_cases h_22_24 : i.val < 23
              · have heq : i = Fin.ofNat 150 22 := Fin.ext (by change i.val = 22; omega)
                subst i
                exact block_0022
              · have heq : i = Fin.ofNat 150 23 := Fin.ext (by change i.val = 23; omega)
                subst i
                exact block_0023
            · by_cases h_24_27 : i.val < 25
              · have heq : i = Fin.ofNat 150 24 := Fin.ext (by change i.val = 24; omega)
                subst i
                exact block_0024
              · by_cases h_25_27 : i.val < 26
                · have heq : i = Fin.ofNat 150 25 := Fin.ext (by change i.val = 25; omega)
                  subst i
                  exact block_0025
                · have heq : i = Fin.ofNat 150 26 := Fin.ext (by change i.val = 26; omega)
                  subst i
                  exact block_0026
        · by_cases h_27_37 : i.val < 32
          · by_cases h_27_32 : i.val < 29
            · by_cases h_27_29 : i.val < 28
              · have heq : i = Fin.ofNat 150 27 := Fin.ext (by change i.val = 27; omega)
                subst i
                exact block_0027
              · have heq : i = Fin.ofNat 150 28 := Fin.ext (by change i.val = 28; omega)
                subst i
                exact block_0028
            · by_cases h_29_32 : i.val < 30
              · have heq : i = Fin.ofNat 150 29 := Fin.ext (by change i.val = 29; omega)
                subst i
                exact block_0029
              · by_cases h_30_32 : i.val < 31
                · have heq : i = Fin.ofNat 150 30 := Fin.ext (by change i.val = 30; omega)
                  subst i
                  exact block_0030
                · have heq : i = Fin.ofNat 150 31 := Fin.ext (by change i.val = 31; omega)
                  subst i
                  exact block_0031
          · by_cases h_32_37 : i.val < 34
            · by_cases h_32_34 : i.val < 33
              · have heq : i = Fin.ofNat 150 32 := Fin.ext (by change i.val = 32; omega)
                subst i
                exact block_0032
              · have heq : i = Fin.ofNat 150 33 := Fin.ext (by change i.val = 33; omega)
                subst i
                exact block_0033
            · by_cases h_34_37 : i.val < 35
              · have heq : i = Fin.ofNat 150 34 := Fin.ext (by change i.val = 34; omega)
                subst i
                exact block_0034
              · by_cases h_35_37 : i.val < 36
                · have heq : i = Fin.ofNat 150 35 := Fin.ext (by change i.val = 35; omega)
                  subst i
                  exact block_0035
                · have heq : i = Fin.ofNat 150 36 := Fin.ext (by change i.val = 36; omega)
                  subst i
                  exact block_0036
    · by_cases h_37_75 : i.val < 56
      · by_cases h_37_56 : i.val < 46
        · by_cases h_37_46 : i.val < 41
          · by_cases h_37_41 : i.val < 39
            · by_cases h_37_39 : i.val < 38
              · have heq : i = Fin.ofNat 150 37 := Fin.ext (by change i.val = 37; omega)
                subst i
                exact block_0037
              · have heq : i = Fin.ofNat 150 38 := Fin.ext (by change i.val = 38; omega)
                subst i
                exact block_0038
            · by_cases h_39_41 : i.val < 40
              · have heq : i = Fin.ofNat 150 39 := Fin.ext (by change i.val = 39; omega)
                subst i
                exact block_0039
              · have heq : i = Fin.ofNat 150 40 := Fin.ext (by change i.val = 40; omega)
                subst i
                exact block_0040
          · by_cases h_41_46 : i.val < 43
            · by_cases h_41_43 : i.val < 42
              · have heq : i = Fin.ofNat 150 41 := Fin.ext (by change i.val = 41; omega)
                subst i
                exact block_0041
              · have heq : i = Fin.ofNat 150 42 := Fin.ext (by change i.val = 42; omega)
                subst i
                exact block_0042
            · by_cases h_43_46 : i.val < 44
              · have heq : i = Fin.ofNat 150 43 := Fin.ext (by change i.val = 43; omega)
                subst i
                exact block_0043
              · by_cases h_44_46 : i.val < 45
                · have heq : i = Fin.ofNat 150 44 := Fin.ext (by change i.val = 44; omega)
                  subst i
                  exact block_0044
                · have heq : i = Fin.ofNat 150 45 := Fin.ext (by change i.val = 45; omega)
                  subst i
                  exact block_0045
        · by_cases h_46_56 : i.val < 51
          · by_cases h_46_51 : i.val < 48
            · by_cases h_46_48 : i.val < 47
              · have heq : i = Fin.ofNat 150 46 := Fin.ext (by change i.val = 46; omega)
                subst i
                exact block_0046
              · have heq : i = Fin.ofNat 150 47 := Fin.ext (by change i.val = 47; omega)
                subst i
                exact block_0047
            · by_cases h_48_51 : i.val < 49
              · have heq : i = Fin.ofNat 150 48 := Fin.ext (by change i.val = 48; omega)
                subst i
                exact block_0048
              · by_cases h_49_51 : i.val < 50
                · have heq : i = Fin.ofNat 150 49 := Fin.ext (by change i.val = 49; omega)
                  subst i
                  exact block_0049
                · have heq : i = Fin.ofNat 150 50 := Fin.ext (by change i.val = 50; omega)
                  subst i
                  exact block_0050
          · by_cases h_51_56 : i.val < 53
            · by_cases h_51_53 : i.val < 52
              · have heq : i = Fin.ofNat 150 51 := Fin.ext (by change i.val = 51; omega)
                subst i
                exact block_0051
              · have heq : i = Fin.ofNat 150 52 := Fin.ext (by change i.val = 52; omega)
                subst i
                exact block_0052
            · by_cases h_53_56 : i.val < 54
              · have heq : i = Fin.ofNat 150 53 := Fin.ext (by change i.val = 53; omega)
                subst i
                exact block_0053
              · by_cases h_54_56 : i.val < 55
                · have heq : i = Fin.ofNat 150 54 := Fin.ext (by change i.val = 54; omega)
                  subst i
                  exact block_0054
                · have heq : i = Fin.ofNat 150 55 := Fin.ext (by change i.val = 55; omega)
                  subst i
                  exact block_0055
      · by_cases h_56_75 : i.val < 65
        · by_cases h_56_65 : i.val < 60
          · by_cases h_56_60 : i.val < 58
            · by_cases h_56_58 : i.val < 57
              · have heq : i = Fin.ofNat 150 56 := Fin.ext (by change i.val = 56; omega)
                subst i
                exact block_0056
              · have heq : i = Fin.ofNat 150 57 := Fin.ext (by change i.val = 57; omega)
                subst i
                exact block_0057
            · by_cases h_58_60 : i.val < 59
              · have heq : i = Fin.ofNat 150 58 := Fin.ext (by change i.val = 58; omega)
                subst i
                exact block_0058
              · have heq : i = Fin.ofNat 150 59 := Fin.ext (by change i.val = 59; omega)
                subst i
                exact block_0059
          · by_cases h_60_65 : i.val < 62
            · by_cases h_60_62 : i.val < 61
              · have heq : i = Fin.ofNat 150 60 := Fin.ext (by change i.val = 60; omega)
                subst i
                exact block_0060
              · have heq : i = Fin.ofNat 150 61 := Fin.ext (by change i.val = 61; omega)
                subst i
                exact block_0061
            · by_cases h_62_65 : i.val < 63
              · have heq : i = Fin.ofNat 150 62 := Fin.ext (by change i.val = 62; omega)
                subst i
                exact block_0062
              · by_cases h_63_65 : i.val < 64
                · have heq : i = Fin.ofNat 150 63 := Fin.ext (by change i.val = 63; omega)
                  subst i
                  exact block_0063
                · have heq : i = Fin.ofNat 150 64 := Fin.ext (by change i.val = 64; omega)
                  subst i
                  exact block_0064
        · by_cases h_65_75 : i.val < 70
          · by_cases h_65_70 : i.val < 67
            · by_cases h_65_67 : i.val < 66
              · have heq : i = Fin.ofNat 150 65 := Fin.ext (by change i.val = 65; omega)
                subst i
                exact block_0065
              · have heq : i = Fin.ofNat 150 66 := Fin.ext (by change i.val = 66; omega)
                subst i
                exact block_0066
            · by_cases h_67_70 : i.val < 68
              · have heq : i = Fin.ofNat 150 67 := Fin.ext (by change i.val = 67; omega)
                subst i
                exact block_0067
              · by_cases h_68_70 : i.val < 69
                · have heq : i = Fin.ofNat 150 68 := Fin.ext (by change i.val = 68; omega)
                  subst i
                  exact block_0068
                · have heq : i = Fin.ofNat 150 69 := Fin.ext (by change i.val = 69; omega)
                  subst i
                  exact block_0069
          · by_cases h_70_75 : i.val < 72
            · by_cases h_70_72 : i.val < 71
              · have heq : i = Fin.ofNat 150 70 := Fin.ext (by change i.val = 70; omega)
                subst i
                exact block_0070
              · have heq : i = Fin.ofNat 150 71 := Fin.ext (by change i.val = 71; omega)
                subst i
                exact block_0071
            · by_cases h_72_75 : i.val < 73
              · have heq : i = Fin.ofNat 150 72 := Fin.ext (by change i.val = 72; omega)
                subst i
                exact block_0072
              · by_cases h_73_75 : i.val < 74
                · have heq : i = Fin.ofNat 150 73 := Fin.ext (by change i.val = 73; omega)
                  subst i
                  exact block_0073
                · have heq : i = Fin.ofNat 150 74 := Fin.ext (by change i.val = 74; omega)
                  subst i
                  exact block_0074
  · by_cases h_75_150 : i.val < 112
    · by_cases h_75_112 : i.val < 93
      · by_cases h_75_93 : i.val < 84
        · by_cases h_75_84 : i.val < 79
          · by_cases h_75_79 : i.val < 77
            · by_cases h_75_77 : i.val < 76
              · have heq : i = Fin.ofNat 150 75 := Fin.ext (by change i.val = 75; omega)
                subst i
                exact block_0075
              · have heq : i = Fin.ofNat 150 76 := Fin.ext (by change i.val = 76; omega)
                subst i
                exact block_0076
            · by_cases h_77_79 : i.val < 78
              · have heq : i = Fin.ofNat 150 77 := Fin.ext (by change i.val = 77; omega)
                subst i
                exact block_0077
              · have heq : i = Fin.ofNat 150 78 := Fin.ext (by change i.val = 78; omega)
                subst i
                exact block_0078
          · by_cases h_79_84 : i.val < 81
            · by_cases h_79_81 : i.val < 80
              · have heq : i = Fin.ofNat 150 79 := Fin.ext (by change i.val = 79; omega)
                subst i
                exact block_0079
              · have heq : i = Fin.ofNat 150 80 := Fin.ext (by change i.val = 80; omega)
                subst i
                exact block_0080
            · by_cases h_81_84 : i.val < 82
              · have heq : i = Fin.ofNat 150 81 := Fin.ext (by change i.val = 81; omega)
                subst i
                exact block_0081
              · by_cases h_82_84 : i.val < 83
                · have heq : i = Fin.ofNat 150 82 := Fin.ext (by change i.val = 82; omega)
                  subst i
                  exact block_0082
                · have heq : i = Fin.ofNat 150 83 := Fin.ext (by change i.val = 83; omega)
                  subst i
                  exact block_0083
        · by_cases h_84_93 : i.val < 88
          · by_cases h_84_88 : i.val < 86
            · by_cases h_84_86 : i.val < 85
              · have heq : i = Fin.ofNat 150 84 := Fin.ext (by change i.val = 84; omega)
                subst i
                exact block_0084
              · have heq : i = Fin.ofNat 150 85 := Fin.ext (by change i.val = 85; omega)
                subst i
                exact block_0085
            · by_cases h_86_88 : i.val < 87
              · have heq : i = Fin.ofNat 150 86 := Fin.ext (by change i.val = 86; omega)
                subst i
                exact block_0086
              · have heq : i = Fin.ofNat 150 87 := Fin.ext (by change i.val = 87; omega)
                subst i
                exact block_0087
          · by_cases h_88_93 : i.val < 90
            · by_cases h_88_90 : i.val < 89
              · have heq : i = Fin.ofNat 150 88 := Fin.ext (by change i.val = 88; omega)
                subst i
                exact block_0088
              · have heq : i = Fin.ofNat 150 89 := Fin.ext (by change i.val = 89; omega)
                subst i
                exact block_0089
            · by_cases h_90_93 : i.val < 91
              · have heq : i = Fin.ofNat 150 90 := Fin.ext (by change i.val = 90; omega)
                subst i
                exact block_0090
              · by_cases h_91_93 : i.val < 92
                · have heq : i = Fin.ofNat 150 91 := Fin.ext (by change i.val = 91; omega)
                  subst i
                  exact block_0091
                · have heq : i = Fin.ofNat 150 92 := Fin.ext (by change i.val = 92; omega)
                  subst i
                  exact block_0092
      · by_cases h_93_112 : i.val < 102
        · by_cases h_93_102 : i.val < 97
          · by_cases h_93_97 : i.val < 95
            · by_cases h_93_95 : i.val < 94
              · have heq : i = Fin.ofNat 150 93 := Fin.ext (by change i.val = 93; omega)
                subst i
                exact block_0093
              · have heq : i = Fin.ofNat 150 94 := Fin.ext (by change i.val = 94; omega)
                subst i
                exact block_0094
            · by_cases h_95_97 : i.val < 96
              · have heq : i = Fin.ofNat 150 95 := Fin.ext (by change i.val = 95; omega)
                subst i
                exact block_0095
              · have heq : i = Fin.ofNat 150 96 := Fin.ext (by change i.val = 96; omega)
                subst i
                exact block_0096
          · by_cases h_97_102 : i.val < 99
            · by_cases h_97_99 : i.val < 98
              · have heq : i = Fin.ofNat 150 97 := Fin.ext (by change i.val = 97; omega)
                subst i
                exact block_0097
              · have heq : i = Fin.ofNat 150 98 := Fin.ext (by change i.val = 98; omega)
                subst i
                exact block_0098
            · by_cases h_99_102 : i.val < 100
              · have heq : i = Fin.ofNat 150 99 := Fin.ext (by change i.val = 99; omega)
                subst i
                exact block_0099
              · by_cases h_100_102 : i.val < 101
                · have heq : i = Fin.ofNat 150 100 := Fin.ext (by change i.val = 100; omega)
                  subst i
                  exact block_0100
                · have heq : i = Fin.ofNat 150 101 := Fin.ext (by change i.val = 101; omega)
                  subst i
                  exact block_0101
        · by_cases h_102_112 : i.val < 107
          · by_cases h_102_107 : i.val < 104
            · by_cases h_102_104 : i.val < 103
              · have heq : i = Fin.ofNat 150 102 := Fin.ext (by change i.val = 102; omega)
                subst i
                exact block_0102
              · have heq : i = Fin.ofNat 150 103 := Fin.ext (by change i.val = 103; omega)
                subst i
                exact block_0103
            · by_cases h_104_107 : i.val < 105
              · have heq : i = Fin.ofNat 150 104 := Fin.ext (by change i.val = 104; omega)
                subst i
                exact block_0104
              · by_cases h_105_107 : i.val < 106
                · have heq : i = Fin.ofNat 150 105 := Fin.ext (by change i.val = 105; omega)
                  subst i
                  exact block_0105
                · have heq : i = Fin.ofNat 150 106 := Fin.ext (by change i.val = 106; omega)
                  subst i
                  exact block_0106
          · by_cases h_107_112 : i.val < 109
            · by_cases h_107_109 : i.val < 108
              · have heq : i = Fin.ofNat 150 107 := Fin.ext (by change i.val = 107; omega)
                subst i
                exact block_0107
              · have heq : i = Fin.ofNat 150 108 := Fin.ext (by change i.val = 108; omega)
                subst i
                exact block_0108
            · by_cases h_109_112 : i.val < 110
              · have heq : i = Fin.ofNat 150 109 := Fin.ext (by change i.val = 109; omega)
                subst i
                exact block_0109
              · by_cases h_110_112 : i.val < 111
                · have heq : i = Fin.ofNat 150 110 := Fin.ext (by change i.val = 110; omega)
                  subst i
                  exact block_0110
                · have heq : i = Fin.ofNat 150 111 := Fin.ext (by change i.val = 111; omega)
                  subst i
                  exact block_0111
    · by_cases h_112_150 : i.val < 131
      · by_cases h_112_131 : i.val < 121
        · by_cases h_112_121 : i.val < 116
          · by_cases h_112_116 : i.val < 114
            · by_cases h_112_114 : i.val < 113
              · have heq : i = Fin.ofNat 150 112 := Fin.ext (by change i.val = 112; omega)
                subst i
                exact block_0112
              · have heq : i = Fin.ofNat 150 113 := Fin.ext (by change i.val = 113; omega)
                subst i
                exact block_0113
            · by_cases h_114_116 : i.val < 115
              · have heq : i = Fin.ofNat 150 114 := Fin.ext (by change i.val = 114; omega)
                subst i
                exact block_0114
              · have heq : i = Fin.ofNat 150 115 := Fin.ext (by change i.val = 115; omega)
                subst i
                exact block_0115
          · by_cases h_116_121 : i.val < 118
            · by_cases h_116_118 : i.val < 117
              · have heq : i = Fin.ofNat 150 116 := Fin.ext (by change i.val = 116; omega)
                subst i
                exact block_0116
              · have heq : i = Fin.ofNat 150 117 := Fin.ext (by change i.val = 117; omega)
                subst i
                exact block_0117
            · by_cases h_118_121 : i.val < 119
              · have heq : i = Fin.ofNat 150 118 := Fin.ext (by change i.val = 118; omega)
                subst i
                exact block_0118
              · by_cases h_119_121 : i.val < 120
                · have heq : i = Fin.ofNat 150 119 := Fin.ext (by change i.val = 119; omega)
                  subst i
                  exact block_0119
                · have heq : i = Fin.ofNat 150 120 := Fin.ext (by change i.val = 120; omega)
                  subst i
                  exact block_0120
        · by_cases h_121_131 : i.val < 126
          · by_cases h_121_126 : i.val < 123
            · by_cases h_121_123 : i.val < 122
              · have heq : i = Fin.ofNat 150 121 := Fin.ext (by change i.val = 121; omega)
                subst i
                exact block_0121
              · have heq : i = Fin.ofNat 150 122 := Fin.ext (by change i.val = 122; omega)
                subst i
                exact block_0122
            · by_cases h_123_126 : i.val < 124
              · have heq : i = Fin.ofNat 150 123 := Fin.ext (by change i.val = 123; omega)
                subst i
                exact block_0123
              · by_cases h_124_126 : i.val < 125
                · have heq : i = Fin.ofNat 150 124 := Fin.ext (by change i.val = 124; omega)
                  subst i
                  exact block_0124
                · have heq : i = Fin.ofNat 150 125 := Fin.ext (by change i.val = 125; omega)
                  subst i
                  exact block_0125
          · by_cases h_126_131 : i.val < 128
            · by_cases h_126_128 : i.val < 127
              · have heq : i = Fin.ofNat 150 126 := Fin.ext (by change i.val = 126; omega)
                subst i
                exact block_0126
              · have heq : i = Fin.ofNat 150 127 := Fin.ext (by change i.val = 127; omega)
                subst i
                exact block_0127
            · by_cases h_128_131 : i.val < 129
              · have heq : i = Fin.ofNat 150 128 := Fin.ext (by change i.val = 128; omega)
                subst i
                exact block_0128
              · by_cases h_129_131 : i.val < 130
                · have heq : i = Fin.ofNat 150 129 := Fin.ext (by change i.val = 129; omega)
                  subst i
                  exact block_0129
                · have heq : i = Fin.ofNat 150 130 := Fin.ext (by change i.val = 130; omega)
                  subst i
                  exact block_0130
      · by_cases h_131_150 : i.val < 140
        · by_cases h_131_140 : i.val < 135
          · by_cases h_131_135 : i.val < 133
            · by_cases h_131_133 : i.val < 132
              · have heq : i = Fin.ofNat 150 131 := Fin.ext (by change i.val = 131; omega)
                subst i
                exact block_0131
              · have heq : i = Fin.ofNat 150 132 := Fin.ext (by change i.val = 132; omega)
                subst i
                exact block_0132
            · by_cases h_133_135 : i.val < 134
              · have heq : i = Fin.ofNat 150 133 := Fin.ext (by change i.val = 133; omega)
                subst i
                exact block_0133
              · have heq : i = Fin.ofNat 150 134 := Fin.ext (by change i.val = 134; omega)
                subst i
                exact block_0134
          · by_cases h_135_140 : i.val < 137
            · by_cases h_135_137 : i.val < 136
              · have heq : i = Fin.ofNat 150 135 := Fin.ext (by change i.val = 135; omega)
                subst i
                exact block_0135
              · have heq : i = Fin.ofNat 150 136 := Fin.ext (by change i.val = 136; omega)
                subst i
                exact block_0136
            · by_cases h_137_140 : i.val < 138
              · have heq : i = Fin.ofNat 150 137 := Fin.ext (by change i.val = 137; omega)
                subst i
                exact block_0137
              · by_cases h_138_140 : i.val < 139
                · have heq : i = Fin.ofNat 150 138 := Fin.ext (by change i.val = 138; omega)
                  subst i
                  exact block_0138
                · have heq : i = Fin.ofNat 150 139 := Fin.ext (by change i.val = 139; omega)
                  subst i
                  exact block_0139
        · by_cases h_140_150 : i.val < 145
          · by_cases h_140_145 : i.val < 142
            · by_cases h_140_142 : i.val < 141
              · have heq : i = Fin.ofNat 150 140 := Fin.ext (by change i.val = 140; omega)
                subst i
                exact block_0140
              · have heq : i = Fin.ofNat 150 141 := Fin.ext (by change i.val = 141; omega)
                subst i
                exact block_0141
            · by_cases h_142_145 : i.val < 143
              · have heq : i = Fin.ofNat 150 142 := Fin.ext (by change i.val = 142; omega)
                subst i
                exact block_0142
              · by_cases h_143_145 : i.val < 144
                · have heq : i = Fin.ofNat 150 143 := Fin.ext (by change i.val = 143; omega)
                  subst i
                  exact block_0143
                · have heq : i = Fin.ofNat 150 144 := Fin.ext (by change i.val = 144; omega)
                  subst i
                  exact block_0144
          · by_cases h_145_150 : i.val < 147
            · by_cases h_145_147 : i.val < 146
              · have heq : i = Fin.ofNat 150 145 := Fin.ext (by change i.val = 145; omega)
                subst i
                exact block_0145
              · have heq : i = Fin.ofNat 150 146 := Fin.ext (by change i.val = 146; omega)
                subst i
                exact block_0146
            · by_cases h_147_150 : i.val < 148
              · have heq : i = Fin.ofNat 150 147 := Fin.ext (by change i.val = 147; omega)
                subst i
                exact block_0147
              · by_cases h_148_150 : i.val < 149
                · have heq : i = Fin.ofNat 150 148 := Fin.ext (by change i.val = 148; omega)
                  subst i
                  exact block_0148
                · have heq : i = Fin.ofNat 150 149 := Fin.ext (by change i.val = 149; omega)
                  subst i
                  exact block_0149
end Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S5T0
