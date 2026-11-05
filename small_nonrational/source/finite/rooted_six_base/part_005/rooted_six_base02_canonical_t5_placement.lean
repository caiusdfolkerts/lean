module
prelude
public import RootedSixBase02CanonicalT5Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase02.T5
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 6 (raw i) template root
      FacetUniverses.RootedSixBase02.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 120 := i.isLt
  by_cases h_0_120 : i.val < 60
  · by_cases h_0_60 : i.val < 30
    · by_cases h_0_30 : i.val < 15
      · by_cases h_0_15 : i.val < 7
        · by_cases h_0_7 : i.val < 3
          · by_cases h_0_3 : i.val < 1
            · have heq : i = Fin.ofNat 120 0 := Fin.ext (by change i.val = 0; omega)
              subst i
              exact block_0000
            · by_cases h_1_3 : i.val < 2
              · have heq : i = Fin.ofNat 120 1 := Fin.ext (by change i.val = 1; omega)
                subst i
                exact block_0001
              · have heq : i = Fin.ofNat 120 2 := Fin.ext (by change i.val = 2; omega)
                subst i
                exact block_0002
          · by_cases h_3_7 : i.val < 5
            · by_cases h_3_5 : i.val < 4
              · have heq : i = Fin.ofNat 120 3 := Fin.ext (by change i.val = 3; omega)
                subst i
                exact block_0003
              · have heq : i = Fin.ofNat 120 4 := Fin.ext (by change i.val = 4; omega)
                subst i
                exact block_0004
            · by_cases h_5_7 : i.val < 6
              · have heq : i = Fin.ofNat 120 5 := Fin.ext (by change i.val = 5; omega)
                subst i
                exact block_0005
              · have heq : i = Fin.ofNat 120 6 := Fin.ext (by change i.val = 6; omega)
                subst i
                exact block_0006
        · by_cases h_7_15 : i.val < 11
          · by_cases h_7_11 : i.val < 9
            · by_cases h_7_9 : i.val < 8
              · have heq : i = Fin.ofNat 120 7 := Fin.ext (by change i.val = 7; omega)
                subst i
                exact block_0007
              · have heq : i = Fin.ofNat 120 8 := Fin.ext (by change i.val = 8; omega)
                subst i
                exact block_0008
            · by_cases h_9_11 : i.val < 10
              · have heq : i = Fin.ofNat 120 9 := Fin.ext (by change i.val = 9; omega)
                subst i
                exact block_0009
              · have heq : i = Fin.ofNat 120 10 := Fin.ext (by change i.val = 10; omega)
                subst i
                exact block_0010
          · by_cases h_11_15 : i.val < 13
            · by_cases h_11_13 : i.val < 12
              · have heq : i = Fin.ofNat 120 11 := Fin.ext (by change i.val = 11; omega)
                subst i
                exact block_0011
              · have heq : i = Fin.ofNat 120 12 := Fin.ext (by change i.val = 12; omega)
                subst i
                exact block_0012
            · by_cases h_13_15 : i.val < 14
              · have heq : i = Fin.ofNat 120 13 := Fin.ext (by change i.val = 13; omega)
                subst i
                exact block_0013
              · have heq : i = Fin.ofNat 120 14 := Fin.ext (by change i.val = 14; omega)
                subst i
                exact block_0014
      · by_cases h_15_30 : i.val < 22
        · by_cases h_15_22 : i.val < 18
          · by_cases h_15_18 : i.val < 16
            · have heq : i = Fin.ofNat 120 15 := Fin.ext (by change i.val = 15; omega)
              subst i
              exact block_0015
            · by_cases h_16_18 : i.val < 17
              · have heq : i = Fin.ofNat 120 16 := Fin.ext (by change i.val = 16; omega)
                subst i
                exact block_0016
              · have heq : i = Fin.ofNat 120 17 := Fin.ext (by change i.val = 17; omega)
                subst i
                exact block_0017
          · by_cases h_18_22 : i.val < 20
            · by_cases h_18_20 : i.val < 19
              · have heq : i = Fin.ofNat 120 18 := Fin.ext (by change i.val = 18; omega)
                subst i
                exact block_0018
              · have heq : i = Fin.ofNat 120 19 := Fin.ext (by change i.val = 19; omega)
                subst i
                exact block_0019
            · by_cases h_20_22 : i.val < 21
              · have heq : i = Fin.ofNat 120 20 := Fin.ext (by change i.val = 20; omega)
                subst i
                exact block_0020
              · have heq : i = Fin.ofNat 120 21 := Fin.ext (by change i.val = 21; omega)
                subst i
                exact block_0021
        · by_cases h_22_30 : i.val < 26
          · by_cases h_22_26 : i.val < 24
            · by_cases h_22_24 : i.val < 23
              · have heq : i = Fin.ofNat 120 22 := Fin.ext (by change i.val = 22; omega)
                subst i
                exact block_0022
              · have heq : i = Fin.ofNat 120 23 := Fin.ext (by change i.val = 23; omega)
                subst i
                exact block_0023
            · by_cases h_24_26 : i.val < 25
              · have heq : i = Fin.ofNat 120 24 := Fin.ext (by change i.val = 24; omega)
                subst i
                exact block_0024
              · have heq : i = Fin.ofNat 120 25 := Fin.ext (by change i.val = 25; omega)
                subst i
                exact block_0025
          · by_cases h_26_30 : i.val < 28
            · by_cases h_26_28 : i.val < 27
              · have heq : i = Fin.ofNat 120 26 := Fin.ext (by change i.val = 26; omega)
                subst i
                exact block_0026
              · have heq : i = Fin.ofNat 120 27 := Fin.ext (by change i.val = 27; omega)
                subst i
                exact block_0027
            · by_cases h_28_30 : i.val < 29
              · have heq : i = Fin.ofNat 120 28 := Fin.ext (by change i.val = 28; omega)
                subst i
                exact block_0028
              · have heq : i = Fin.ofNat 120 29 := Fin.ext (by change i.val = 29; omega)
                subst i
                exact block_0029
    · by_cases h_30_60 : i.val < 45
      · by_cases h_30_45 : i.val < 37
        · by_cases h_30_37 : i.val < 33
          · by_cases h_30_33 : i.val < 31
            · have heq : i = Fin.ofNat 120 30 := Fin.ext (by change i.val = 30; omega)
              subst i
              exact block_0030
            · by_cases h_31_33 : i.val < 32
              · have heq : i = Fin.ofNat 120 31 := Fin.ext (by change i.val = 31; omega)
                subst i
                exact block_0031
              · have heq : i = Fin.ofNat 120 32 := Fin.ext (by change i.val = 32; omega)
                subst i
                exact block_0032
          · by_cases h_33_37 : i.val < 35
            · by_cases h_33_35 : i.val < 34
              · have heq : i = Fin.ofNat 120 33 := Fin.ext (by change i.val = 33; omega)
                subst i
                exact block_0033
              · have heq : i = Fin.ofNat 120 34 := Fin.ext (by change i.val = 34; omega)
                subst i
                exact block_0034
            · by_cases h_35_37 : i.val < 36
              · have heq : i = Fin.ofNat 120 35 := Fin.ext (by change i.val = 35; omega)
                subst i
                exact block_0035
              · have heq : i = Fin.ofNat 120 36 := Fin.ext (by change i.val = 36; omega)
                subst i
                exact block_0036
        · by_cases h_37_45 : i.val < 41
          · by_cases h_37_41 : i.val < 39
            · by_cases h_37_39 : i.val < 38
              · have heq : i = Fin.ofNat 120 37 := Fin.ext (by change i.val = 37; omega)
                subst i
                exact block_0037
              · have heq : i = Fin.ofNat 120 38 := Fin.ext (by change i.val = 38; omega)
                subst i
                exact block_0038
            · by_cases h_39_41 : i.val < 40
              · have heq : i = Fin.ofNat 120 39 := Fin.ext (by change i.val = 39; omega)
                subst i
                exact block_0039
              · have heq : i = Fin.ofNat 120 40 := Fin.ext (by change i.val = 40; omega)
                subst i
                exact block_0040
          · by_cases h_41_45 : i.val < 43
            · by_cases h_41_43 : i.val < 42
              · have heq : i = Fin.ofNat 120 41 := Fin.ext (by change i.val = 41; omega)
                subst i
                exact block_0041
              · have heq : i = Fin.ofNat 120 42 := Fin.ext (by change i.val = 42; omega)
                subst i
                exact block_0042
            · by_cases h_43_45 : i.val < 44
              · have heq : i = Fin.ofNat 120 43 := Fin.ext (by change i.val = 43; omega)
                subst i
                exact block_0043
              · have heq : i = Fin.ofNat 120 44 := Fin.ext (by change i.val = 44; omega)
                subst i
                exact block_0044
      · by_cases h_45_60 : i.val < 52
        · by_cases h_45_52 : i.val < 48
          · by_cases h_45_48 : i.val < 46
            · have heq : i = Fin.ofNat 120 45 := Fin.ext (by change i.val = 45; omega)
              subst i
              exact block_0045
            · by_cases h_46_48 : i.val < 47
              · have heq : i = Fin.ofNat 120 46 := Fin.ext (by change i.val = 46; omega)
                subst i
                exact block_0046
              · have heq : i = Fin.ofNat 120 47 := Fin.ext (by change i.val = 47; omega)
                subst i
                exact block_0047
          · by_cases h_48_52 : i.val < 50
            · by_cases h_48_50 : i.val < 49
              · have heq : i = Fin.ofNat 120 48 := Fin.ext (by change i.val = 48; omega)
                subst i
                exact block_0048
              · have heq : i = Fin.ofNat 120 49 := Fin.ext (by change i.val = 49; omega)
                subst i
                exact block_0049
            · by_cases h_50_52 : i.val < 51
              · have heq : i = Fin.ofNat 120 50 := Fin.ext (by change i.val = 50; omega)
                subst i
                exact block_0050
              · have heq : i = Fin.ofNat 120 51 := Fin.ext (by change i.val = 51; omega)
                subst i
                exact block_0051
        · by_cases h_52_60 : i.val < 56
          · by_cases h_52_56 : i.val < 54
            · by_cases h_52_54 : i.val < 53
              · have heq : i = Fin.ofNat 120 52 := Fin.ext (by change i.val = 52; omega)
                subst i
                exact block_0052
              · have heq : i = Fin.ofNat 120 53 := Fin.ext (by change i.val = 53; omega)
                subst i
                exact block_0053
            · by_cases h_54_56 : i.val < 55
              · have heq : i = Fin.ofNat 120 54 := Fin.ext (by change i.val = 54; omega)
                subst i
                exact block_0054
              · have heq : i = Fin.ofNat 120 55 := Fin.ext (by change i.val = 55; omega)
                subst i
                exact block_0055
          · by_cases h_56_60 : i.val < 58
            · by_cases h_56_58 : i.val < 57
              · have heq : i = Fin.ofNat 120 56 := Fin.ext (by change i.val = 56; omega)
                subst i
                exact block_0056
              · have heq : i = Fin.ofNat 120 57 := Fin.ext (by change i.val = 57; omega)
                subst i
                exact block_0057
            · by_cases h_58_60 : i.val < 59
              · have heq : i = Fin.ofNat 120 58 := Fin.ext (by change i.val = 58; omega)
                subst i
                exact block_0058
              · have heq : i = Fin.ofNat 120 59 := Fin.ext (by change i.val = 59; omega)
                subst i
                exact block_0059
  · by_cases h_60_120 : i.val < 90
    · by_cases h_60_90 : i.val < 75
      · by_cases h_60_75 : i.val < 67
        · by_cases h_60_67 : i.val < 63
          · by_cases h_60_63 : i.val < 61
            · have heq : i = Fin.ofNat 120 60 := Fin.ext (by change i.val = 60; omega)
              subst i
              exact block_0060
            · by_cases h_61_63 : i.val < 62
              · have heq : i = Fin.ofNat 120 61 := Fin.ext (by change i.val = 61; omega)
                subst i
                exact block_0061
              · have heq : i = Fin.ofNat 120 62 := Fin.ext (by change i.val = 62; omega)
                subst i
                exact block_0062
          · by_cases h_63_67 : i.val < 65
            · by_cases h_63_65 : i.val < 64
              · have heq : i = Fin.ofNat 120 63 := Fin.ext (by change i.val = 63; omega)
                subst i
                exact block_0063
              · have heq : i = Fin.ofNat 120 64 := Fin.ext (by change i.val = 64; omega)
                subst i
                exact block_0064
            · by_cases h_65_67 : i.val < 66
              · have heq : i = Fin.ofNat 120 65 := Fin.ext (by change i.val = 65; omega)
                subst i
                exact block_0065
              · have heq : i = Fin.ofNat 120 66 := Fin.ext (by change i.val = 66; omega)
                subst i
                exact block_0066
        · by_cases h_67_75 : i.val < 71
          · by_cases h_67_71 : i.val < 69
            · by_cases h_67_69 : i.val < 68
              · have heq : i = Fin.ofNat 120 67 := Fin.ext (by change i.val = 67; omega)
                subst i
                exact block_0067
              · have heq : i = Fin.ofNat 120 68 := Fin.ext (by change i.val = 68; omega)
                subst i
                exact block_0068
            · by_cases h_69_71 : i.val < 70
              · have heq : i = Fin.ofNat 120 69 := Fin.ext (by change i.val = 69; omega)
                subst i
                exact block_0069
              · have heq : i = Fin.ofNat 120 70 := Fin.ext (by change i.val = 70; omega)
                subst i
                exact block_0070
          · by_cases h_71_75 : i.val < 73
            · by_cases h_71_73 : i.val < 72
              · have heq : i = Fin.ofNat 120 71 := Fin.ext (by change i.val = 71; omega)
                subst i
                exact block_0071
              · have heq : i = Fin.ofNat 120 72 := Fin.ext (by change i.val = 72; omega)
                subst i
                exact block_0072
            · by_cases h_73_75 : i.val < 74
              · have heq : i = Fin.ofNat 120 73 := Fin.ext (by change i.val = 73; omega)
                subst i
                exact block_0073
              · have heq : i = Fin.ofNat 120 74 := Fin.ext (by change i.val = 74; omega)
                subst i
                exact block_0074
      · by_cases h_75_90 : i.val < 82
        · by_cases h_75_82 : i.val < 78
          · by_cases h_75_78 : i.val < 76
            · have heq : i = Fin.ofNat 120 75 := Fin.ext (by change i.val = 75; omega)
              subst i
              exact block_0075
            · by_cases h_76_78 : i.val < 77
              · have heq : i = Fin.ofNat 120 76 := Fin.ext (by change i.val = 76; omega)
                subst i
                exact block_0076
              · have heq : i = Fin.ofNat 120 77 := Fin.ext (by change i.val = 77; omega)
                subst i
                exact block_0077
          · by_cases h_78_82 : i.val < 80
            · by_cases h_78_80 : i.val < 79
              · have heq : i = Fin.ofNat 120 78 := Fin.ext (by change i.val = 78; omega)
                subst i
                exact block_0078
              · have heq : i = Fin.ofNat 120 79 := Fin.ext (by change i.val = 79; omega)
                subst i
                exact block_0079
            · by_cases h_80_82 : i.val < 81
              · have heq : i = Fin.ofNat 120 80 := Fin.ext (by change i.val = 80; omega)
                subst i
                exact block_0080
              · have heq : i = Fin.ofNat 120 81 := Fin.ext (by change i.val = 81; omega)
                subst i
                exact block_0081
        · by_cases h_82_90 : i.val < 86
          · by_cases h_82_86 : i.val < 84
            · by_cases h_82_84 : i.val < 83
              · have heq : i = Fin.ofNat 120 82 := Fin.ext (by change i.val = 82; omega)
                subst i
                exact block_0082
              · have heq : i = Fin.ofNat 120 83 := Fin.ext (by change i.val = 83; omega)
                subst i
                exact block_0083
            · by_cases h_84_86 : i.val < 85
              · have heq : i = Fin.ofNat 120 84 := Fin.ext (by change i.val = 84; omega)
                subst i
                exact block_0084
              · have heq : i = Fin.ofNat 120 85 := Fin.ext (by change i.val = 85; omega)
                subst i
                exact block_0085
          · by_cases h_86_90 : i.val < 88
            · by_cases h_86_88 : i.val < 87
              · have heq : i = Fin.ofNat 120 86 := Fin.ext (by change i.val = 86; omega)
                subst i
                exact block_0086
              · have heq : i = Fin.ofNat 120 87 := Fin.ext (by change i.val = 87; omega)
                subst i
                exact block_0087
            · by_cases h_88_90 : i.val < 89
              · have heq : i = Fin.ofNat 120 88 := Fin.ext (by change i.val = 88; omega)
                subst i
                exact block_0088
              · have heq : i = Fin.ofNat 120 89 := Fin.ext (by change i.val = 89; omega)
                subst i
                exact block_0089
    · by_cases h_90_120 : i.val < 105
      · by_cases h_90_105 : i.val < 97
        · by_cases h_90_97 : i.val < 93
          · by_cases h_90_93 : i.val < 91
            · have heq : i = Fin.ofNat 120 90 := Fin.ext (by change i.val = 90; omega)
              subst i
              exact block_0090
            · by_cases h_91_93 : i.val < 92
              · have heq : i = Fin.ofNat 120 91 := Fin.ext (by change i.val = 91; omega)
                subst i
                exact block_0091
              · have heq : i = Fin.ofNat 120 92 := Fin.ext (by change i.val = 92; omega)
                subst i
                exact block_0092
          · by_cases h_93_97 : i.val < 95
            · by_cases h_93_95 : i.val < 94
              · have heq : i = Fin.ofNat 120 93 := Fin.ext (by change i.val = 93; omega)
                subst i
                exact block_0093
              · have heq : i = Fin.ofNat 120 94 := Fin.ext (by change i.val = 94; omega)
                subst i
                exact block_0094
            · by_cases h_95_97 : i.val < 96
              · have heq : i = Fin.ofNat 120 95 := Fin.ext (by change i.val = 95; omega)
                subst i
                exact block_0095
              · have heq : i = Fin.ofNat 120 96 := Fin.ext (by change i.val = 96; omega)
                subst i
                exact block_0096
        · by_cases h_97_105 : i.val < 101
          · by_cases h_97_101 : i.val < 99
            · by_cases h_97_99 : i.val < 98
              · have heq : i = Fin.ofNat 120 97 := Fin.ext (by change i.val = 97; omega)
                subst i
                exact block_0097
              · have heq : i = Fin.ofNat 120 98 := Fin.ext (by change i.val = 98; omega)
                subst i
                exact block_0098
            · by_cases h_99_101 : i.val < 100
              · have heq : i = Fin.ofNat 120 99 := Fin.ext (by change i.val = 99; omega)
                subst i
                exact block_0099
              · have heq : i = Fin.ofNat 120 100 := Fin.ext (by change i.val = 100; omega)
                subst i
                exact block_0100
          · by_cases h_101_105 : i.val < 103
            · by_cases h_101_103 : i.val < 102
              · have heq : i = Fin.ofNat 120 101 := Fin.ext (by change i.val = 101; omega)
                subst i
                exact block_0101
              · have heq : i = Fin.ofNat 120 102 := Fin.ext (by change i.val = 102; omega)
                subst i
                exact block_0102
            · by_cases h_103_105 : i.val < 104
              · have heq : i = Fin.ofNat 120 103 := Fin.ext (by change i.val = 103; omega)
                subst i
                exact block_0103
              · have heq : i = Fin.ofNat 120 104 := Fin.ext (by change i.val = 104; omega)
                subst i
                exact block_0104
      · by_cases h_105_120 : i.val < 112
        · by_cases h_105_112 : i.val < 108
          · by_cases h_105_108 : i.val < 106
            · have heq : i = Fin.ofNat 120 105 := Fin.ext (by change i.val = 105; omega)
              subst i
              exact block_0105
            · by_cases h_106_108 : i.val < 107
              · have heq : i = Fin.ofNat 120 106 := Fin.ext (by change i.val = 106; omega)
                subst i
                exact block_0106
              · have heq : i = Fin.ofNat 120 107 := Fin.ext (by change i.val = 107; omega)
                subst i
                exact block_0107
          · by_cases h_108_112 : i.val < 110
            · by_cases h_108_110 : i.val < 109
              · have heq : i = Fin.ofNat 120 108 := Fin.ext (by change i.val = 108; omega)
                subst i
                exact block_0108
              · have heq : i = Fin.ofNat 120 109 := Fin.ext (by change i.val = 109; omega)
                subst i
                exact block_0109
            · by_cases h_110_112 : i.val < 111
              · have heq : i = Fin.ofNat 120 110 := Fin.ext (by change i.val = 110; omega)
                subst i
                exact block_0110
              · have heq : i = Fin.ofNat 120 111 := Fin.ext (by change i.val = 111; omega)
                subst i
                exact block_0111
        · by_cases h_112_120 : i.val < 116
          · by_cases h_112_116 : i.val < 114
            · by_cases h_112_114 : i.val < 113
              · have heq : i = Fin.ofNat 120 112 := Fin.ext (by change i.val = 112; omega)
                subst i
                exact block_0112
              · have heq : i = Fin.ofNat 120 113 := Fin.ext (by change i.val = 113; omega)
                subst i
                exact block_0113
            · by_cases h_114_116 : i.val < 115
              · have heq : i = Fin.ofNat 120 114 := Fin.ext (by change i.val = 114; omega)
                subst i
                exact block_0114
              · have heq : i = Fin.ofNat 120 115 := Fin.ext (by change i.val = 115; omega)
                subst i
                exact block_0115
          · by_cases h_116_120 : i.val < 118
            · by_cases h_116_118 : i.val < 117
              · have heq : i = Fin.ofNat 120 116 := Fin.ext (by change i.val = 116; omega)
                subst i
                exact block_0116
              · have heq : i = Fin.ofNat 120 117 := Fin.ext (by change i.val = 117; omega)
                subst i
                exact block_0117
            · by_cases h_118_120 : i.val < 119
              · have heq : i = Fin.ofNat 120 118 := Fin.ext (by change i.val = 118; omega)
                subst i
                exact block_0118
              · have heq : i = Fin.ofNat 120 119 := Fin.ext (by change i.val = 119; omega)
                subst i
                exact block_0119
end Papers.RationalityTen.RootedCanonical.RootedSixBase02.T5
