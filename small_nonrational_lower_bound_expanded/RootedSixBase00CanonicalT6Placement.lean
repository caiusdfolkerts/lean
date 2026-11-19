module
prelude
public import RootedSixBase00CanonicalT6Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.T6
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 6 (raw i) template root
      FacetUniverses.RootedSixBase00.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 124 := i.isLt
  by_cases h_0_124 : i.val < 62
  · by_cases h_0_62 : i.val < 31
    · by_cases h_0_31 : i.val < 15
      · by_cases h_0_15 : i.val < 7
        · by_cases h_0_7 : i.val < 3
          · by_cases h_0_3 : i.val < 1
            · have heq : i = Fin.ofNat 124 0 := Fin.ext (by change i.val = 0; omega)
              subst i
              exact block_0000
            · by_cases h_1_3 : i.val < 2
              · have heq : i = Fin.ofNat 124 1 := Fin.ext (by change i.val = 1; omega)
                subst i
                exact block_0001
              · have heq : i = Fin.ofNat 124 2 := Fin.ext (by change i.val = 2; omega)
                subst i
                exact block_0002
          · by_cases h_3_7 : i.val < 5
            · by_cases h_3_5 : i.val < 4
              · have heq : i = Fin.ofNat 124 3 := Fin.ext (by change i.val = 3; omega)
                subst i
                exact block_0003
              · have heq : i = Fin.ofNat 124 4 := Fin.ext (by change i.val = 4; omega)
                subst i
                exact block_0004
            · by_cases h_5_7 : i.val < 6
              · have heq : i = Fin.ofNat 124 5 := Fin.ext (by change i.val = 5; omega)
                subst i
                exact block_0005
              · have heq : i = Fin.ofNat 124 6 := Fin.ext (by change i.val = 6; omega)
                subst i
                exact block_0006
        · by_cases h_7_15 : i.val < 11
          · by_cases h_7_11 : i.val < 9
            · by_cases h_7_9 : i.val < 8
              · have heq : i = Fin.ofNat 124 7 := Fin.ext (by change i.val = 7; omega)
                subst i
                exact block_0007
              · have heq : i = Fin.ofNat 124 8 := Fin.ext (by change i.val = 8; omega)
                subst i
                exact block_0008
            · by_cases h_9_11 : i.val < 10
              · have heq : i = Fin.ofNat 124 9 := Fin.ext (by change i.val = 9; omega)
                subst i
                exact block_0009
              · have heq : i = Fin.ofNat 124 10 := Fin.ext (by change i.val = 10; omega)
                subst i
                exact block_0010
          · by_cases h_11_15 : i.val < 13
            · by_cases h_11_13 : i.val < 12
              · have heq : i = Fin.ofNat 124 11 := Fin.ext (by change i.val = 11; omega)
                subst i
                exact block_0011
              · have heq : i = Fin.ofNat 124 12 := Fin.ext (by change i.val = 12; omega)
                subst i
                exact block_0012
            · by_cases h_13_15 : i.val < 14
              · have heq : i = Fin.ofNat 124 13 := Fin.ext (by change i.val = 13; omega)
                subst i
                exact block_0013
              · have heq : i = Fin.ofNat 124 14 := Fin.ext (by change i.val = 14; omega)
                subst i
                exact block_0014
      · by_cases h_15_31 : i.val < 23
        · by_cases h_15_23 : i.val < 19
          · by_cases h_15_19 : i.val < 17
            · by_cases h_15_17 : i.val < 16
              · have heq : i = Fin.ofNat 124 15 := Fin.ext (by change i.val = 15; omega)
                subst i
                exact block_0015
              · have heq : i = Fin.ofNat 124 16 := Fin.ext (by change i.val = 16; omega)
                subst i
                exact block_0016
            · by_cases h_17_19 : i.val < 18
              · have heq : i = Fin.ofNat 124 17 := Fin.ext (by change i.val = 17; omega)
                subst i
                exact block_0017
              · have heq : i = Fin.ofNat 124 18 := Fin.ext (by change i.val = 18; omega)
                subst i
                exact block_0018
          · by_cases h_19_23 : i.val < 21
            · by_cases h_19_21 : i.val < 20
              · have heq : i = Fin.ofNat 124 19 := Fin.ext (by change i.val = 19; omega)
                subst i
                exact block_0019
              · have heq : i = Fin.ofNat 124 20 := Fin.ext (by change i.val = 20; omega)
                subst i
                exact block_0020
            · by_cases h_21_23 : i.val < 22
              · have heq : i = Fin.ofNat 124 21 := Fin.ext (by change i.val = 21; omega)
                subst i
                exact block_0021
              · have heq : i = Fin.ofNat 124 22 := Fin.ext (by change i.val = 22; omega)
                subst i
                exact block_0022
        · by_cases h_23_31 : i.val < 27
          · by_cases h_23_27 : i.val < 25
            · by_cases h_23_25 : i.val < 24
              · have heq : i = Fin.ofNat 124 23 := Fin.ext (by change i.val = 23; omega)
                subst i
                exact block_0023
              · have heq : i = Fin.ofNat 124 24 := Fin.ext (by change i.val = 24; omega)
                subst i
                exact block_0024
            · by_cases h_25_27 : i.val < 26
              · have heq : i = Fin.ofNat 124 25 := Fin.ext (by change i.val = 25; omega)
                subst i
                exact block_0025
              · have heq : i = Fin.ofNat 124 26 := Fin.ext (by change i.val = 26; omega)
                subst i
                exact block_0026
          · by_cases h_27_31 : i.val < 29
            · by_cases h_27_29 : i.val < 28
              · have heq : i = Fin.ofNat 124 27 := Fin.ext (by change i.val = 27; omega)
                subst i
                exact block_0027
              · have heq : i = Fin.ofNat 124 28 := Fin.ext (by change i.val = 28; omega)
                subst i
                exact block_0028
            · by_cases h_29_31 : i.val < 30
              · have heq : i = Fin.ofNat 124 29 := Fin.ext (by change i.val = 29; omega)
                subst i
                exact block_0029
              · have heq : i = Fin.ofNat 124 30 := Fin.ext (by change i.val = 30; omega)
                subst i
                exact block_0030
    · by_cases h_31_62 : i.val < 46
      · by_cases h_31_46 : i.val < 38
        · by_cases h_31_38 : i.val < 34
          · by_cases h_31_34 : i.val < 32
            · have heq : i = Fin.ofNat 124 31 := Fin.ext (by change i.val = 31; omega)
              subst i
              exact block_0031
            · by_cases h_32_34 : i.val < 33
              · have heq : i = Fin.ofNat 124 32 := Fin.ext (by change i.val = 32; omega)
                subst i
                exact block_0032
              · have heq : i = Fin.ofNat 124 33 := Fin.ext (by change i.val = 33; omega)
                subst i
                exact block_0033
          · by_cases h_34_38 : i.val < 36
            · by_cases h_34_36 : i.val < 35
              · have heq : i = Fin.ofNat 124 34 := Fin.ext (by change i.val = 34; omega)
                subst i
                exact block_0034
              · have heq : i = Fin.ofNat 124 35 := Fin.ext (by change i.val = 35; omega)
                subst i
                exact block_0035
            · by_cases h_36_38 : i.val < 37
              · have heq : i = Fin.ofNat 124 36 := Fin.ext (by change i.val = 36; omega)
                subst i
                exact block_0036
              · have heq : i = Fin.ofNat 124 37 := Fin.ext (by change i.val = 37; omega)
                subst i
                exact block_0037
        · by_cases h_38_46 : i.val < 42
          · by_cases h_38_42 : i.val < 40
            · by_cases h_38_40 : i.val < 39
              · have heq : i = Fin.ofNat 124 38 := Fin.ext (by change i.val = 38; omega)
                subst i
                exact block_0038
              · have heq : i = Fin.ofNat 124 39 := Fin.ext (by change i.val = 39; omega)
                subst i
                exact block_0039
            · by_cases h_40_42 : i.val < 41
              · have heq : i = Fin.ofNat 124 40 := Fin.ext (by change i.val = 40; omega)
                subst i
                exact block_0040
              · have heq : i = Fin.ofNat 124 41 := Fin.ext (by change i.val = 41; omega)
                subst i
                exact block_0041
          · by_cases h_42_46 : i.val < 44
            · by_cases h_42_44 : i.val < 43
              · have heq : i = Fin.ofNat 124 42 := Fin.ext (by change i.val = 42; omega)
                subst i
                exact block_0042
              · have heq : i = Fin.ofNat 124 43 := Fin.ext (by change i.val = 43; omega)
                subst i
                exact block_0043
            · by_cases h_44_46 : i.val < 45
              · have heq : i = Fin.ofNat 124 44 := Fin.ext (by change i.val = 44; omega)
                subst i
                exact block_0044
              · have heq : i = Fin.ofNat 124 45 := Fin.ext (by change i.val = 45; omega)
                subst i
                exact block_0045
      · by_cases h_46_62 : i.val < 54
        · by_cases h_46_54 : i.val < 50
          · by_cases h_46_50 : i.val < 48
            · by_cases h_46_48 : i.val < 47
              · have heq : i = Fin.ofNat 124 46 := Fin.ext (by change i.val = 46; omega)
                subst i
                exact block_0046
              · have heq : i = Fin.ofNat 124 47 := Fin.ext (by change i.val = 47; omega)
                subst i
                exact block_0047
            · by_cases h_48_50 : i.val < 49
              · have heq : i = Fin.ofNat 124 48 := Fin.ext (by change i.val = 48; omega)
                subst i
                exact block_0048
              · have heq : i = Fin.ofNat 124 49 := Fin.ext (by change i.val = 49; omega)
                subst i
                exact block_0049
          · by_cases h_50_54 : i.val < 52
            · by_cases h_50_52 : i.val < 51
              · have heq : i = Fin.ofNat 124 50 := Fin.ext (by change i.val = 50; omega)
                subst i
                exact block_0050
              · have heq : i = Fin.ofNat 124 51 := Fin.ext (by change i.val = 51; omega)
                subst i
                exact block_0051
            · by_cases h_52_54 : i.val < 53
              · have heq : i = Fin.ofNat 124 52 := Fin.ext (by change i.val = 52; omega)
                subst i
                exact block_0052
              · have heq : i = Fin.ofNat 124 53 := Fin.ext (by change i.val = 53; omega)
                subst i
                exact block_0053
        · by_cases h_54_62 : i.val < 58
          · by_cases h_54_58 : i.val < 56
            · by_cases h_54_56 : i.val < 55
              · have heq : i = Fin.ofNat 124 54 := Fin.ext (by change i.val = 54; omega)
                subst i
                exact block_0054
              · have heq : i = Fin.ofNat 124 55 := Fin.ext (by change i.val = 55; omega)
                subst i
                exact block_0055
            · by_cases h_56_58 : i.val < 57
              · have heq : i = Fin.ofNat 124 56 := Fin.ext (by change i.val = 56; omega)
                subst i
                exact block_0056
              · have heq : i = Fin.ofNat 124 57 := Fin.ext (by change i.val = 57; omega)
                subst i
                exact block_0057
          · by_cases h_58_62 : i.val < 60
            · by_cases h_58_60 : i.val < 59
              · have heq : i = Fin.ofNat 124 58 := Fin.ext (by change i.val = 58; omega)
                subst i
                exact block_0058
              · have heq : i = Fin.ofNat 124 59 := Fin.ext (by change i.val = 59; omega)
                subst i
                exact block_0059
            · by_cases h_60_62 : i.val < 61
              · have heq : i = Fin.ofNat 124 60 := Fin.ext (by change i.val = 60; omega)
                subst i
                exact block_0060
              · have heq : i = Fin.ofNat 124 61 := Fin.ext (by change i.val = 61; omega)
                subst i
                exact block_0061
  · by_cases h_62_124 : i.val < 93
    · by_cases h_62_93 : i.val < 77
      · by_cases h_62_77 : i.val < 69
        · by_cases h_62_69 : i.val < 65
          · by_cases h_62_65 : i.val < 63
            · have heq : i = Fin.ofNat 124 62 := Fin.ext (by change i.val = 62; omega)
              subst i
              exact block_0062
            · by_cases h_63_65 : i.val < 64
              · have heq : i = Fin.ofNat 124 63 := Fin.ext (by change i.val = 63; omega)
                subst i
                exact block_0063
              · have heq : i = Fin.ofNat 124 64 := Fin.ext (by change i.val = 64; omega)
                subst i
                exact block_0064
          · by_cases h_65_69 : i.val < 67
            · by_cases h_65_67 : i.val < 66
              · have heq : i = Fin.ofNat 124 65 := Fin.ext (by change i.val = 65; omega)
                subst i
                exact block_0065
              · have heq : i = Fin.ofNat 124 66 := Fin.ext (by change i.val = 66; omega)
                subst i
                exact block_0066
            · by_cases h_67_69 : i.val < 68
              · have heq : i = Fin.ofNat 124 67 := Fin.ext (by change i.val = 67; omega)
                subst i
                exact block_0067
              · have heq : i = Fin.ofNat 124 68 := Fin.ext (by change i.val = 68; omega)
                subst i
                exact block_0068
        · by_cases h_69_77 : i.val < 73
          · by_cases h_69_73 : i.val < 71
            · by_cases h_69_71 : i.val < 70
              · have heq : i = Fin.ofNat 124 69 := Fin.ext (by change i.val = 69; omega)
                subst i
                exact block_0069
              · have heq : i = Fin.ofNat 124 70 := Fin.ext (by change i.val = 70; omega)
                subst i
                exact block_0070
            · by_cases h_71_73 : i.val < 72
              · have heq : i = Fin.ofNat 124 71 := Fin.ext (by change i.val = 71; omega)
                subst i
                exact block_0071
              · have heq : i = Fin.ofNat 124 72 := Fin.ext (by change i.val = 72; omega)
                subst i
                exact block_0072
          · by_cases h_73_77 : i.val < 75
            · by_cases h_73_75 : i.val < 74
              · have heq : i = Fin.ofNat 124 73 := Fin.ext (by change i.val = 73; omega)
                subst i
                exact block_0073
              · have heq : i = Fin.ofNat 124 74 := Fin.ext (by change i.val = 74; omega)
                subst i
                exact block_0074
            · by_cases h_75_77 : i.val < 76
              · have heq : i = Fin.ofNat 124 75 := Fin.ext (by change i.val = 75; omega)
                subst i
                exact block_0075
              · have heq : i = Fin.ofNat 124 76 := Fin.ext (by change i.val = 76; omega)
                subst i
                exact block_0076
      · by_cases h_77_93 : i.val < 85
        · by_cases h_77_85 : i.val < 81
          · by_cases h_77_81 : i.val < 79
            · by_cases h_77_79 : i.val < 78
              · have heq : i = Fin.ofNat 124 77 := Fin.ext (by change i.val = 77; omega)
                subst i
                exact block_0077
              · have heq : i = Fin.ofNat 124 78 := Fin.ext (by change i.val = 78; omega)
                subst i
                exact block_0078
            · by_cases h_79_81 : i.val < 80
              · have heq : i = Fin.ofNat 124 79 := Fin.ext (by change i.val = 79; omega)
                subst i
                exact block_0079
              · have heq : i = Fin.ofNat 124 80 := Fin.ext (by change i.val = 80; omega)
                subst i
                exact block_0080
          · by_cases h_81_85 : i.val < 83
            · by_cases h_81_83 : i.val < 82
              · have heq : i = Fin.ofNat 124 81 := Fin.ext (by change i.val = 81; omega)
                subst i
                exact block_0081
              · have heq : i = Fin.ofNat 124 82 := Fin.ext (by change i.val = 82; omega)
                subst i
                exact block_0082
            · by_cases h_83_85 : i.val < 84
              · have heq : i = Fin.ofNat 124 83 := Fin.ext (by change i.val = 83; omega)
                subst i
                exact block_0083
              · have heq : i = Fin.ofNat 124 84 := Fin.ext (by change i.val = 84; omega)
                subst i
                exact block_0084
        · by_cases h_85_93 : i.val < 89
          · by_cases h_85_89 : i.val < 87
            · by_cases h_85_87 : i.val < 86
              · have heq : i = Fin.ofNat 124 85 := Fin.ext (by change i.val = 85; omega)
                subst i
                exact block_0085
              · have heq : i = Fin.ofNat 124 86 := Fin.ext (by change i.val = 86; omega)
                subst i
                exact block_0086
            · by_cases h_87_89 : i.val < 88
              · have heq : i = Fin.ofNat 124 87 := Fin.ext (by change i.val = 87; omega)
                subst i
                exact block_0087
              · have heq : i = Fin.ofNat 124 88 := Fin.ext (by change i.val = 88; omega)
                subst i
                exact block_0088
          · by_cases h_89_93 : i.val < 91
            · by_cases h_89_91 : i.val < 90
              · have heq : i = Fin.ofNat 124 89 := Fin.ext (by change i.val = 89; omega)
                subst i
                exact block_0089
              · have heq : i = Fin.ofNat 124 90 := Fin.ext (by change i.val = 90; omega)
                subst i
                exact block_0090
            · by_cases h_91_93 : i.val < 92
              · have heq : i = Fin.ofNat 124 91 := Fin.ext (by change i.val = 91; omega)
                subst i
                exact block_0091
              · have heq : i = Fin.ofNat 124 92 := Fin.ext (by change i.val = 92; omega)
                subst i
                exact block_0092
    · by_cases h_93_124 : i.val < 108
      · by_cases h_93_108 : i.val < 100
        · by_cases h_93_100 : i.val < 96
          · by_cases h_93_96 : i.val < 94
            · have heq : i = Fin.ofNat 124 93 := Fin.ext (by change i.val = 93; omega)
              subst i
              exact block_0093
            · by_cases h_94_96 : i.val < 95
              · have heq : i = Fin.ofNat 124 94 := Fin.ext (by change i.val = 94; omega)
                subst i
                exact block_0094
              · have heq : i = Fin.ofNat 124 95 := Fin.ext (by change i.val = 95; omega)
                subst i
                exact block_0095
          · by_cases h_96_100 : i.val < 98
            · by_cases h_96_98 : i.val < 97
              · have heq : i = Fin.ofNat 124 96 := Fin.ext (by change i.val = 96; omega)
                subst i
                exact block_0096
              · have heq : i = Fin.ofNat 124 97 := Fin.ext (by change i.val = 97; omega)
                subst i
                exact block_0097
            · by_cases h_98_100 : i.val < 99
              · have heq : i = Fin.ofNat 124 98 := Fin.ext (by change i.val = 98; omega)
                subst i
                exact block_0098
              · have heq : i = Fin.ofNat 124 99 := Fin.ext (by change i.val = 99; omega)
                subst i
                exact block_0099
        · by_cases h_100_108 : i.val < 104
          · by_cases h_100_104 : i.val < 102
            · by_cases h_100_102 : i.val < 101
              · have heq : i = Fin.ofNat 124 100 := Fin.ext (by change i.val = 100; omega)
                subst i
                exact block_0100
              · have heq : i = Fin.ofNat 124 101 := Fin.ext (by change i.val = 101; omega)
                subst i
                exact block_0101
            · by_cases h_102_104 : i.val < 103
              · have heq : i = Fin.ofNat 124 102 := Fin.ext (by change i.val = 102; omega)
                subst i
                exact block_0102
              · have heq : i = Fin.ofNat 124 103 := Fin.ext (by change i.val = 103; omega)
                subst i
                exact block_0103
          · by_cases h_104_108 : i.val < 106
            · by_cases h_104_106 : i.val < 105
              · have heq : i = Fin.ofNat 124 104 := Fin.ext (by change i.val = 104; omega)
                subst i
                exact block_0104
              · have heq : i = Fin.ofNat 124 105 := Fin.ext (by change i.val = 105; omega)
                subst i
                exact block_0105
            · by_cases h_106_108 : i.val < 107
              · have heq : i = Fin.ofNat 124 106 := Fin.ext (by change i.val = 106; omega)
                subst i
                exact block_0106
              · have heq : i = Fin.ofNat 124 107 := Fin.ext (by change i.val = 107; omega)
                subst i
                exact block_0107
      · by_cases h_108_124 : i.val < 116
        · by_cases h_108_116 : i.val < 112
          · by_cases h_108_112 : i.val < 110
            · by_cases h_108_110 : i.val < 109
              · have heq : i = Fin.ofNat 124 108 := Fin.ext (by change i.val = 108; omega)
                subst i
                exact block_0108
              · have heq : i = Fin.ofNat 124 109 := Fin.ext (by change i.val = 109; omega)
                subst i
                exact block_0109
            · by_cases h_110_112 : i.val < 111
              · have heq : i = Fin.ofNat 124 110 := Fin.ext (by change i.val = 110; omega)
                subst i
                exact block_0110
              · have heq : i = Fin.ofNat 124 111 := Fin.ext (by change i.val = 111; omega)
                subst i
                exact block_0111
          · by_cases h_112_116 : i.val < 114
            · by_cases h_112_114 : i.val < 113
              · have heq : i = Fin.ofNat 124 112 := Fin.ext (by change i.val = 112; omega)
                subst i
                exact block_0112
              · have heq : i = Fin.ofNat 124 113 := Fin.ext (by change i.val = 113; omega)
                subst i
                exact block_0113
            · by_cases h_114_116 : i.val < 115
              · have heq : i = Fin.ofNat 124 114 := Fin.ext (by change i.val = 114; omega)
                subst i
                exact block_0114
              · have heq : i = Fin.ofNat 124 115 := Fin.ext (by change i.val = 115; omega)
                subst i
                exact block_0115
        · by_cases h_116_124 : i.val < 120
          · by_cases h_116_120 : i.val < 118
            · by_cases h_116_118 : i.val < 117
              · have heq : i = Fin.ofNat 124 116 := Fin.ext (by change i.val = 116; omega)
                subst i
                exact block_0116
              · have heq : i = Fin.ofNat 124 117 := Fin.ext (by change i.val = 117; omega)
                subst i
                exact block_0117
            · by_cases h_118_120 : i.val < 119
              · have heq : i = Fin.ofNat 124 118 := Fin.ext (by change i.val = 118; omega)
                subst i
                exact block_0118
              · have heq : i = Fin.ofNat 124 119 := Fin.ext (by change i.val = 119; omega)
                subst i
                exact block_0119
          · by_cases h_120_124 : i.val < 122
            · by_cases h_120_122 : i.val < 121
              · have heq : i = Fin.ofNat 124 120 := Fin.ext (by change i.val = 120; omega)
                subst i
                exact block_0120
              · have heq : i = Fin.ofNat 124 121 := Fin.ext (by change i.val = 121; omega)
                subst i
                exact block_0121
            · by_cases h_122_124 : i.val < 123
              · have heq : i = Fin.ofNat 124 122 := Fin.ext (by change i.val = 122; omega)
                subst i
                exact block_0122
              · have heq : i = Fin.ofNat 124 123 := Fin.ext (by change i.val = 123; omega)
                subst i
                exact block_0123
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.T6
