module
prelude
public import RootedSevenPure042CanonicalS5T1Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenPure042.S5T1
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 5 (raw i) template root
      FacetUniverses.RootedSevenPure042.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 130 := i.isLt
  by_cases h_0_130 : i.val < 65
  · by_cases h_0_65 : i.val < 32
    · by_cases h_0_32 : i.val < 16
      · by_cases h_0_16 : i.val < 8
        · by_cases h_0_8 : i.val < 4
          · by_cases h_0_4 : i.val < 2
            · by_cases h_0_2 : i.val < 1
              · have heq : i = Fin.ofNat 130 0 := Fin.ext (by change i.val = 0; omega)
                subst i
                exact block_0000
              · have heq : i = Fin.ofNat 130 1 := Fin.ext (by change i.val = 1; omega)
                subst i
                exact block_0001
            · by_cases h_2_4 : i.val < 3
              · have heq : i = Fin.ofNat 130 2 := Fin.ext (by change i.val = 2; omega)
                subst i
                exact block_0002
              · have heq : i = Fin.ofNat 130 3 := Fin.ext (by change i.val = 3; omega)
                subst i
                exact block_0003
          · by_cases h_4_8 : i.val < 6
            · by_cases h_4_6 : i.val < 5
              · have heq : i = Fin.ofNat 130 4 := Fin.ext (by change i.val = 4; omega)
                subst i
                exact block_0004
              · have heq : i = Fin.ofNat 130 5 := Fin.ext (by change i.val = 5; omega)
                subst i
                exact block_0005
            · by_cases h_6_8 : i.val < 7
              · have heq : i = Fin.ofNat 130 6 := Fin.ext (by change i.val = 6; omega)
                subst i
                exact block_0006
              · have heq : i = Fin.ofNat 130 7 := Fin.ext (by change i.val = 7; omega)
                subst i
                exact block_0007
        · by_cases h_8_16 : i.val < 12
          · by_cases h_8_12 : i.val < 10
            · by_cases h_8_10 : i.val < 9
              · have heq : i = Fin.ofNat 130 8 := Fin.ext (by change i.val = 8; omega)
                subst i
                exact block_0008
              · have heq : i = Fin.ofNat 130 9 := Fin.ext (by change i.val = 9; omega)
                subst i
                exact block_0009
            · by_cases h_10_12 : i.val < 11
              · have heq : i = Fin.ofNat 130 10 := Fin.ext (by change i.val = 10; omega)
                subst i
                exact block_0010
              · have heq : i = Fin.ofNat 130 11 := Fin.ext (by change i.val = 11; omega)
                subst i
                exact block_0011
          · by_cases h_12_16 : i.val < 14
            · by_cases h_12_14 : i.val < 13
              · have heq : i = Fin.ofNat 130 12 := Fin.ext (by change i.val = 12; omega)
                subst i
                exact block_0012
              · have heq : i = Fin.ofNat 130 13 := Fin.ext (by change i.val = 13; omega)
                subst i
                exact block_0013
            · by_cases h_14_16 : i.val < 15
              · have heq : i = Fin.ofNat 130 14 := Fin.ext (by change i.val = 14; omega)
                subst i
                exact block_0014
              · have heq : i = Fin.ofNat 130 15 := Fin.ext (by change i.val = 15; omega)
                subst i
                exact block_0015
      · by_cases h_16_32 : i.val < 24
        · by_cases h_16_24 : i.val < 20
          · by_cases h_16_20 : i.val < 18
            · by_cases h_16_18 : i.val < 17
              · have heq : i = Fin.ofNat 130 16 := Fin.ext (by change i.val = 16; omega)
                subst i
                exact block_0016
              · have heq : i = Fin.ofNat 130 17 := Fin.ext (by change i.val = 17; omega)
                subst i
                exact block_0017
            · by_cases h_18_20 : i.val < 19
              · have heq : i = Fin.ofNat 130 18 := Fin.ext (by change i.val = 18; omega)
                subst i
                exact block_0018
              · have heq : i = Fin.ofNat 130 19 := Fin.ext (by change i.val = 19; omega)
                subst i
                exact block_0019
          · by_cases h_20_24 : i.val < 22
            · by_cases h_20_22 : i.val < 21
              · have heq : i = Fin.ofNat 130 20 := Fin.ext (by change i.val = 20; omega)
                subst i
                exact block_0020
              · have heq : i = Fin.ofNat 130 21 := Fin.ext (by change i.val = 21; omega)
                subst i
                exact block_0021
            · by_cases h_22_24 : i.val < 23
              · have heq : i = Fin.ofNat 130 22 := Fin.ext (by change i.val = 22; omega)
                subst i
                exact block_0022
              · have heq : i = Fin.ofNat 130 23 := Fin.ext (by change i.val = 23; omega)
                subst i
                exact block_0023
        · by_cases h_24_32 : i.val < 28
          · by_cases h_24_28 : i.val < 26
            · by_cases h_24_26 : i.val < 25
              · have heq : i = Fin.ofNat 130 24 := Fin.ext (by change i.val = 24; omega)
                subst i
                exact block_0024
              · have heq : i = Fin.ofNat 130 25 := Fin.ext (by change i.val = 25; omega)
                subst i
                exact block_0025
            · by_cases h_26_28 : i.val < 27
              · have heq : i = Fin.ofNat 130 26 := Fin.ext (by change i.val = 26; omega)
                subst i
                exact block_0026
              · have heq : i = Fin.ofNat 130 27 := Fin.ext (by change i.val = 27; omega)
                subst i
                exact block_0027
          · by_cases h_28_32 : i.val < 30
            · by_cases h_28_30 : i.val < 29
              · have heq : i = Fin.ofNat 130 28 := Fin.ext (by change i.val = 28; omega)
                subst i
                exact block_0028
              · have heq : i = Fin.ofNat 130 29 := Fin.ext (by change i.val = 29; omega)
                subst i
                exact block_0029
            · by_cases h_30_32 : i.val < 31
              · have heq : i = Fin.ofNat 130 30 := Fin.ext (by change i.val = 30; omega)
                subst i
                exact block_0030
              · have heq : i = Fin.ofNat 130 31 := Fin.ext (by change i.val = 31; omega)
                subst i
                exact block_0031
    · by_cases h_32_65 : i.val < 48
      · by_cases h_32_48 : i.val < 40
        · by_cases h_32_40 : i.val < 36
          · by_cases h_32_36 : i.val < 34
            · by_cases h_32_34 : i.val < 33
              · have heq : i = Fin.ofNat 130 32 := Fin.ext (by change i.val = 32; omega)
                subst i
                exact block_0032
              · have heq : i = Fin.ofNat 130 33 := Fin.ext (by change i.val = 33; omega)
                subst i
                exact block_0033
            · by_cases h_34_36 : i.val < 35
              · have heq : i = Fin.ofNat 130 34 := Fin.ext (by change i.val = 34; omega)
                subst i
                exact block_0034
              · have heq : i = Fin.ofNat 130 35 := Fin.ext (by change i.val = 35; omega)
                subst i
                exact block_0035
          · by_cases h_36_40 : i.val < 38
            · by_cases h_36_38 : i.val < 37
              · have heq : i = Fin.ofNat 130 36 := Fin.ext (by change i.val = 36; omega)
                subst i
                exact block_0036
              · have heq : i = Fin.ofNat 130 37 := Fin.ext (by change i.val = 37; omega)
                subst i
                exact block_0037
            · by_cases h_38_40 : i.val < 39
              · have heq : i = Fin.ofNat 130 38 := Fin.ext (by change i.val = 38; omega)
                subst i
                exact block_0038
              · have heq : i = Fin.ofNat 130 39 := Fin.ext (by change i.val = 39; omega)
                subst i
                exact block_0039
        · by_cases h_40_48 : i.val < 44
          · by_cases h_40_44 : i.val < 42
            · by_cases h_40_42 : i.val < 41
              · have heq : i = Fin.ofNat 130 40 := Fin.ext (by change i.val = 40; omega)
                subst i
                exact block_0040
              · have heq : i = Fin.ofNat 130 41 := Fin.ext (by change i.val = 41; omega)
                subst i
                exact block_0041
            · by_cases h_42_44 : i.val < 43
              · have heq : i = Fin.ofNat 130 42 := Fin.ext (by change i.val = 42; omega)
                subst i
                exact block_0042
              · have heq : i = Fin.ofNat 130 43 := Fin.ext (by change i.val = 43; omega)
                subst i
                exact block_0043
          · by_cases h_44_48 : i.val < 46
            · by_cases h_44_46 : i.val < 45
              · have heq : i = Fin.ofNat 130 44 := Fin.ext (by change i.val = 44; omega)
                subst i
                exact block_0044
              · have heq : i = Fin.ofNat 130 45 := Fin.ext (by change i.val = 45; omega)
                subst i
                exact block_0045
            · by_cases h_46_48 : i.val < 47
              · have heq : i = Fin.ofNat 130 46 := Fin.ext (by change i.val = 46; omega)
                subst i
                exact block_0046
              · have heq : i = Fin.ofNat 130 47 := Fin.ext (by change i.val = 47; omega)
                subst i
                exact block_0047
      · by_cases h_48_65 : i.val < 56
        · by_cases h_48_56 : i.val < 52
          · by_cases h_48_52 : i.val < 50
            · by_cases h_48_50 : i.val < 49
              · have heq : i = Fin.ofNat 130 48 := Fin.ext (by change i.val = 48; omega)
                subst i
                exact block_0048
              · have heq : i = Fin.ofNat 130 49 := Fin.ext (by change i.val = 49; omega)
                subst i
                exact block_0049
            · by_cases h_50_52 : i.val < 51
              · have heq : i = Fin.ofNat 130 50 := Fin.ext (by change i.val = 50; omega)
                subst i
                exact block_0050
              · have heq : i = Fin.ofNat 130 51 := Fin.ext (by change i.val = 51; omega)
                subst i
                exact block_0051
          · by_cases h_52_56 : i.val < 54
            · by_cases h_52_54 : i.val < 53
              · have heq : i = Fin.ofNat 130 52 := Fin.ext (by change i.val = 52; omega)
                subst i
                exact block_0052
              · have heq : i = Fin.ofNat 130 53 := Fin.ext (by change i.val = 53; omega)
                subst i
                exact block_0053
            · by_cases h_54_56 : i.val < 55
              · have heq : i = Fin.ofNat 130 54 := Fin.ext (by change i.val = 54; omega)
                subst i
                exact block_0054
              · have heq : i = Fin.ofNat 130 55 := Fin.ext (by change i.val = 55; omega)
                subst i
                exact block_0055
        · by_cases h_56_65 : i.val < 60
          · by_cases h_56_60 : i.val < 58
            · by_cases h_56_58 : i.val < 57
              · have heq : i = Fin.ofNat 130 56 := Fin.ext (by change i.val = 56; omega)
                subst i
                exact block_0056
              · have heq : i = Fin.ofNat 130 57 := Fin.ext (by change i.val = 57; omega)
                subst i
                exact block_0057
            · by_cases h_58_60 : i.val < 59
              · have heq : i = Fin.ofNat 130 58 := Fin.ext (by change i.val = 58; omega)
                subst i
                exact block_0058
              · have heq : i = Fin.ofNat 130 59 := Fin.ext (by change i.val = 59; omega)
                subst i
                exact block_0059
          · by_cases h_60_65 : i.val < 62
            · by_cases h_60_62 : i.val < 61
              · have heq : i = Fin.ofNat 130 60 := Fin.ext (by change i.val = 60; omega)
                subst i
                exact block_0060
              · have heq : i = Fin.ofNat 130 61 := Fin.ext (by change i.val = 61; omega)
                subst i
                exact block_0061
            · by_cases h_62_65 : i.val < 63
              · have heq : i = Fin.ofNat 130 62 := Fin.ext (by change i.val = 62; omega)
                subst i
                exact block_0062
              · by_cases h_63_65 : i.val < 64
                · have heq : i = Fin.ofNat 130 63 := Fin.ext (by change i.val = 63; omega)
                  subst i
                  exact block_0063
                · have heq : i = Fin.ofNat 130 64 := Fin.ext (by change i.val = 64; omega)
                  subst i
                  exact block_0064
  · by_cases h_65_130 : i.val < 97
    · by_cases h_65_97 : i.val < 81
      · by_cases h_65_81 : i.val < 73
        · by_cases h_65_73 : i.val < 69
          · by_cases h_65_69 : i.val < 67
            · by_cases h_65_67 : i.val < 66
              · have heq : i = Fin.ofNat 130 65 := Fin.ext (by change i.val = 65; omega)
                subst i
                exact block_0065
              · have heq : i = Fin.ofNat 130 66 := Fin.ext (by change i.val = 66; omega)
                subst i
                exact block_0066
            · by_cases h_67_69 : i.val < 68
              · have heq : i = Fin.ofNat 130 67 := Fin.ext (by change i.val = 67; omega)
                subst i
                exact block_0067
              · have heq : i = Fin.ofNat 130 68 := Fin.ext (by change i.val = 68; omega)
                subst i
                exact block_0068
          · by_cases h_69_73 : i.val < 71
            · by_cases h_69_71 : i.val < 70
              · have heq : i = Fin.ofNat 130 69 := Fin.ext (by change i.val = 69; omega)
                subst i
                exact block_0069
              · have heq : i = Fin.ofNat 130 70 := Fin.ext (by change i.val = 70; omega)
                subst i
                exact block_0070
            · by_cases h_71_73 : i.val < 72
              · have heq : i = Fin.ofNat 130 71 := Fin.ext (by change i.val = 71; omega)
                subst i
                exact block_0071
              · have heq : i = Fin.ofNat 130 72 := Fin.ext (by change i.val = 72; omega)
                subst i
                exact block_0072
        · by_cases h_73_81 : i.val < 77
          · by_cases h_73_77 : i.val < 75
            · by_cases h_73_75 : i.val < 74
              · have heq : i = Fin.ofNat 130 73 := Fin.ext (by change i.val = 73; omega)
                subst i
                exact block_0073
              · have heq : i = Fin.ofNat 130 74 := Fin.ext (by change i.val = 74; omega)
                subst i
                exact block_0074
            · by_cases h_75_77 : i.val < 76
              · have heq : i = Fin.ofNat 130 75 := Fin.ext (by change i.val = 75; omega)
                subst i
                exact block_0075
              · have heq : i = Fin.ofNat 130 76 := Fin.ext (by change i.val = 76; omega)
                subst i
                exact block_0076
          · by_cases h_77_81 : i.val < 79
            · by_cases h_77_79 : i.val < 78
              · have heq : i = Fin.ofNat 130 77 := Fin.ext (by change i.val = 77; omega)
                subst i
                exact block_0077
              · have heq : i = Fin.ofNat 130 78 := Fin.ext (by change i.val = 78; omega)
                subst i
                exact block_0078
            · by_cases h_79_81 : i.val < 80
              · have heq : i = Fin.ofNat 130 79 := Fin.ext (by change i.val = 79; omega)
                subst i
                exact block_0079
              · have heq : i = Fin.ofNat 130 80 := Fin.ext (by change i.val = 80; omega)
                subst i
                exact block_0080
      · by_cases h_81_97 : i.val < 89
        · by_cases h_81_89 : i.val < 85
          · by_cases h_81_85 : i.val < 83
            · by_cases h_81_83 : i.val < 82
              · have heq : i = Fin.ofNat 130 81 := Fin.ext (by change i.val = 81; omega)
                subst i
                exact block_0081
              · have heq : i = Fin.ofNat 130 82 := Fin.ext (by change i.val = 82; omega)
                subst i
                exact block_0082
            · by_cases h_83_85 : i.val < 84
              · have heq : i = Fin.ofNat 130 83 := Fin.ext (by change i.val = 83; omega)
                subst i
                exact block_0083
              · have heq : i = Fin.ofNat 130 84 := Fin.ext (by change i.val = 84; omega)
                subst i
                exact block_0084
          · by_cases h_85_89 : i.val < 87
            · by_cases h_85_87 : i.val < 86
              · have heq : i = Fin.ofNat 130 85 := Fin.ext (by change i.val = 85; omega)
                subst i
                exact block_0085
              · have heq : i = Fin.ofNat 130 86 := Fin.ext (by change i.val = 86; omega)
                subst i
                exact block_0086
            · by_cases h_87_89 : i.val < 88
              · have heq : i = Fin.ofNat 130 87 := Fin.ext (by change i.val = 87; omega)
                subst i
                exact block_0087
              · have heq : i = Fin.ofNat 130 88 := Fin.ext (by change i.val = 88; omega)
                subst i
                exact block_0088
        · by_cases h_89_97 : i.val < 93
          · by_cases h_89_93 : i.val < 91
            · by_cases h_89_91 : i.val < 90
              · have heq : i = Fin.ofNat 130 89 := Fin.ext (by change i.val = 89; omega)
                subst i
                exact block_0089
              · have heq : i = Fin.ofNat 130 90 := Fin.ext (by change i.val = 90; omega)
                subst i
                exact block_0090
            · by_cases h_91_93 : i.val < 92
              · have heq : i = Fin.ofNat 130 91 := Fin.ext (by change i.val = 91; omega)
                subst i
                exact block_0091
              · have heq : i = Fin.ofNat 130 92 := Fin.ext (by change i.val = 92; omega)
                subst i
                exact block_0092
          · by_cases h_93_97 : i.val < 95
            · by_cases h_93_95 : i.val < 94
              · have heq : i = Fin.ofNat 130 93 := Fin.ext (by change i.val = 93; omega)
                subst i
                exact block_0093
              · have heq : i = Fin.ofNat 130 94 := Fin.ext (by change i.val = 94; omega)
                subst i
                exact block_0094
            · by_cases h_95_97 : i.val < 96
              · have heq : i = Fin.ofNat 130 95 := Fin.ext (by change i.val = 95; omega)
                subst i
                exact block_0095
              · have heq : i = Fin.ofNat 130 96 := Fin.ext (by change i.val = 96; omega)
                subst i
                exact block_0096
    · by_cases h_97_130 : i.val < 113
      · by_cases h_97_113 : i.val < 105
        · by_cases h_97_105 : i.val < 101
          · by_cases h_97_101 : i.val < 99
            · by_cases h_97_99 : i.val < 98
              · have heq : i = Fin.ofNat 130 97 := Fin.ext (by change i.val = 97; omega)
                subst i
                exact block_0097
              · have heq : i = Fin.ofNat 130 98 := Fin.ext (by change i.val = 98; omega)
                subst i
                exact block_0098
            · by_cases h_99_101 : i.val < 100
              · have heq : i = Fin.ofNat 130 99 := Fin.ext (by change i.val = 99; omega)
                subst i
                exact block_0099
              · have heq : i = Fin.ofNat 130 100 := Fin.ext (by change i.val = 100; omega)
                subst i
                exact block_0100
          · by_cases h_101_105 : i.val < 103
            · by_cases h_101_103 : i.val < 102
              · have heq : i = Fin.ofNat 130 101 := Fin.ext (by change i.val = 101; omega)
                subst i
                exact block_0101
              · have heq : i = Fin.ofNat 130 102 := Fin.ext (by change i.val = 102; omega)
                subst i
                exact block_0102
            · by_cases h_103_105 : i.val < 104
              · have heq : i = Fin.ofNat 130 103 := Fin.ext (by change i.val = 103; omega)
                subst i
                exact block_0103
              · have heq : i = Fin.ofNat 130 104 := Fin.ext (by change i.val = 104; omega)
                subst i
                exact block_0104
        · by_cases h_105_113 : i.val < 109
          · by_cases h_105_109 : i.val < 107
            · by_cases h_105_107 : i.val < 106
              · have heq : i = Fin.ofNat 130 105 := Fin.ext (by change i.val = 105; omega)
                subst i
                exact block_0105
              · have heq : i = Fin.ofNat 130 106 := Fin.ext (by change i.val = 106; omega)
                subst i
                exact block_0106
            · by_cases h_107_109 : i.val < 108
              · have heq : i = Fin.ofNat 130 107 := Fin.ext (by change i.val = 107; omega)
                subst i
                exact block_0107
              · have heq : i = Fin.ofNat 130 108 := Fin.ext (by change i.val = 108; omega)
                subst i
                exact block_0108
          · by_cases h_109_113 : i.val < 111
            · by_cases h_109_111 : i.val < 110
              · have heq : i = Fin.ofNat 130 109 := Fin.ext (by change i.val = 109; omega)
                subst i
                exact block_0109
              · have heq : i = Fin.ofNat 130 110 := Fin.ext (by change i.val = 110; omega)
                subst i
                exact block_0110
            · by_cases h_111_113 : i.val < 112
              · have heq : i = Fin.ofNat 130 111 := Fin.ext (by change i.val = 111; omega)
                subst i
                exact block_0111
              · have heq : i = Fin.ofNat 130 112 := Fin.ext (by change i.val = 112; omega)
                subst i
                exact block_0112
      · by_cases h_113_130 : i.val < 121
        · by_cases h_113_121 : i.val < 117
          · by_cases h_113_117 : i.val < 115
            · by_cases h_113_115 : i.val < 114
              · have heq : i = Fin.ofNat 130 113 := Fin.ext (by change i.val = 113; omega)
                subst i
                exact block_0113
              · have heq : i = Fin.ofNat 130 114 := Fin.ext (by change i.val = 114; omega)
                subst i
                exact block_0114
            · by_cases h_115_117 : i.val < 116
              · have heq : i = Fin.ofNat 130 115 := Fin.ext (by change i.val = 115; omega)
                subst i
                exact block_0115
              · have heq : i = Fin.ofNat 130 116 := Fin.ext (by change i.val = 116; omega)
                subst i
                exact block_0116
          · by_cases h_117_121 : i.val < 119
            · by_cases h_117_119 : i.val < 118
              · have heq : i = Fin.ofNat 130 117 := Fin.ext (by change i.val = 117; omega)
                subst i
                exact block_0117
              · have heq : i = Fin.ofNat 130 118 := Fin.ext (by change i.val = 118; omega)
                subst i
                exact block_0118
            · by_cases h_119_121 : i.val < 120
              · have heq : i = Fin.ofNat 130 119 := Fin.ext (by change i.val = 119; omega)
                subst i
                exact block_0119
              · have heq : i = Fin.ofNat 130 120 := Fin.ext (by change i.val = 120; omega)
                subst i
                exact block_0120
        · by_cases h_121_130 : i.val < 125
          · by_cases h_121_125 : i.val < 123
            · by_cases h_121_123 : i.val < 122
              · have heq : i = Fin.ofNat 130 121 := Fin.ext (by change i.val = 121; omega)
                subst i
                exact block_0121
              · have heq : i = Fin.ofNat 130 122 := Fin.ext (by change i.val = 122; omega)
                subst i
                exact block_0122
            · by_cases h_123_125 : i.val < 124
              · have heq : i = Fin.ofNat 130 123 := Fin.ext (by change i.val = 123; omega)
                subst i
                exact block_0123
              · have heq : i = Fin.ofNat 130 124 := Fin.ext (by change i.val = 124; omega)
                subst i
                exact block_0124
          · by_cases h_125_130 : i.val < 127
            · by_cases h_125_127 : i.val < 126
              · have heq : i = Fin.ofNat 130 125 := Fin.ext (by change i.val = 125; omega)
                subst i
                exact block_0125
              · have heq : i = Fin.ofNat 130 126 := Fin.ext (by change i.val = 126; omega)
                subst i
                exact block_0126
            · by_cases h_127_130 : i.val < 128
              · have heq : i = Fin.ofNat 130 127 := Fin.ext (by change i.val = 127; omega)
                subst i
                exact block_0127
              · by_cases h_128_130 : i.val < 129
                · have heq : i = Fin.ofNat 130 128 := Fin.ext (by change i.val = 128; omega)
                  subst i
                  exact block_0128
                · have heq : i = Fin.ofNat 130 129 := Fin.ext (by change i.val = 129; omega)
                  subst i
                  exact block_0129
end Papers.RationalityTen.RootedCanonical.RootedSevenPure042.S5T1
