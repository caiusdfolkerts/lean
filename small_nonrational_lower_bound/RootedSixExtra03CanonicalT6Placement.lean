module
prelude
public import RootedSixExtra03CanonicalT6Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra03.T6
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 6 (raw i) template root
      FacetUniverses.RootedSixExtra03.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 114 := i.isLt
  by_cases h_0_114 : i.val < 57
  · by_cases h_0_57 : i.val < 28
    · by_cases h_0_28 : i.val < 14
      · by_cases h_0_14 : i.val < 7
        · by_cases h_0_7 : i.val < 3
          · by_cases h_0_3 : i.val < 1
            · have heq : i = Fin.ofNat 114 0 := Fin.ext (by change i.val = 0; omega)
              subst i
              exact block_0000
            · by_cases h_1_3 : i.val < 2
              · have heq : i = Fin.ofNat 114 1 := Fin.ext (by change i.val = 1; omega)
                subst i
                exact block_0001
              · have heq : i = Fin.ofNat 114 2 := Fin.ext (by change i.val = 2; omega)
                subst i
                exact block_0002
          · by_cases h_3_7 : i.val < 5
            · by_cases h_3_5 : i.val < 4
              · have heq : i = Fin.ofNat 114 3 := Fin.ext (by change i.val = 3; omega)
                subst i
                exact block_0003
              · have heq : i = Fin.ofNat 114 4 := Fin.ext (by change i.val = 4; omega)
                subst i
                exact block_0004
            · by_cases h_5_7 : i.val < 6
              · have heq : i = Fin.ofNat 114 5 := Fin.ext (by change i.val = 5; omega)
                subst i
                exact block_0005
              · have heq : i = Fin.ofNat 114 6 := Fin.ext (by change i.val = 6; omega)
                subst i
                exact block_0006
        · by_cases h_7_14 : i.val < 10
          · by_cases h_7_10 : i.val < 8
            · have heq : i = Fin.ofNat 114 7 := Fin.ext (by change i.val = 7; omega)
              subst i
              exact block_0007
            · by_cases h_8_10 : i.val < 9
              · have heq : i = Fin.ofNat 114 8 := Fin.ext (by change i.val = 8; omega)
                subst i
                exact block_0008
              · have heq : i = Fin.ofNat 114 9 := Fin.ext (by change i.val = 9; omega)
                subst i
                exact block_0009
          · by_cases h_10_14 : i.val < 12
            · by_cases h_10_12 : i.val < 11
              · have heq : i = Fin.ofNat 114 10 := Fin.ext (by change i.val = 10; omega)
                subst i
                exact block_0010
              · have heq : i = Fin.ofNat 114 11 := Fin.ext (by change i.val = 11; omega)
                subst i
                exact block_0011
            · by_cases h_12_14 : i.val < 13
              · have heq : i = Fin.ofNat 114 12 := Fin.ext (by change i.val = 12; omega)
                subst i
                exact block_0012
              · have heq : i = Fin.ofNat 114 13 := Fin.ext (by change i.val = 13; omega)
                subst i
                exact block_0013
      · by_cases h_14_28 : i.val < 21
        · by_cases h_14_21 : i.val < 17
          · by_cases h_14_17 : i.val < 15
            · have heq : i = Fin.ofNat 114 14 := Fin.ext (by change i.val = 14; omega)
              subst i
              exact block_0014
            · by_cases h_15_17 : i.val < 16
              · have heq : i = Fin.ofNat 114 15 := Fin.ext (by change i.val = 15; omega)
                subst i
                exact block_0015
              · have heq : i = Fin.ofNat 114 16 := Fin.ext (by change i.val = 16; omega)
                subst i
                exact block_0016
          · by_cases h_17_21 : i.val < 19
            · by_cases h_17_19 : i.val < 18
              · have heq : i = Fin.ofNat 114 17 := Fin.ext (by change i.val = 17; omega)
                subst i
                exact block_0017
              · have heq : i = Fin.ofNat 114 18 := Fin.ext (by change i.val = 18; omega)
                subst i
                exact block_0018
            · by_cases h_19_21 : i.val < 20
              · have heq : i = Fin.ofNat 114 19 := Fin.ext (by change i.val = 19; omega)
                subst i
                exact block_0019
              · have heq : i = Fin.ofNat 114 20 := Fin.ext (by change i.val = 20; omega)
                subst i
                exact block_0020
        · by_cases h_21_28 : i.val < 24
          · by_cases h_21_24 : i.val < 22
            · have heq : i = Fin.ofNat 114 21 := Fin.ext (by change i.val = 21; omega)
              subst i
              exact block_0021
            · by_cases h_22_24 : i.val < 23
              · have heq : i = Fin.ofNat 114 22 := Fin.ext (by change i.val = 22; omega)
                subst i
                exact block_0022
              · have heq : i = Fin.ofNat 114 23 := Fin.ext (by change i.val = 23; omega)
                subst i
                exact block_0023
          · by_cases h_24_28 : i.val < 26
            · by_cases h_24_26 : i.val < 25
              · have heq : i = Fin.ofNat 114 24 := Fin.ext (by change i.val = 24; omega)
                subst i
                exact block_0024
              · have heq : i = Fin.ofNat 114 25 := Fin.ext (by change i.val = 25; omega)
                subst i
                exact block_0025
            · by_cases h_26_28 : i.val < 27
              · have heq : i = Fin.ofNat 114 26 := Fin.ext (by change i.val = 26; omega)
                subst i
                exact block_0026
              · have heq : i = Fin.ofNat 114 27 := Fin.ext (by change i.val = 27; omega)
                subst i
                exact block_0027
    · by_cases h_28_57 : i.val < 42
      · by_cases h_28_42 : i.val < 35
        · by_cases h_28_35 : i.val < 31
          · by_cases h_28_31 : i.val < 29
            · have heq : i = Fin.ofNat 114 28 := Fin.ext (by change i.val = 28; omega)
              subst i
              exact block_0028
            · by_cases h_29_31 : i.val < 30
              · have heq : i = Fin.ofNat 114 29 := Fin.ext (by change i.val = 29; omega)
                subst i
                exact block_0029
              · have heq : i = Fin.ofNat 114 30 := Fin.ext (by change i.val = 30; omega)
                subst i
                exact block_0030
          · by_cases h_31_35 : i.val < 33
            · by_cases h_31_33 : i.val < 32
              · have heq : i = Fin.ofNat 114 31 := Fin.ext (by change i.val = 31; omega)
                subst i
                exact block_0031
              · have heq : i = Fin.ofNat 114 32 := Fin.ext (by change i.val = 32; omega)
                subst i
                exact block_0032
            · by_cases h_33_35 : i.val < 34
              · have heq : i = Fin.ofNat 114 33 := Fin.ext (by change i.val = 33; omega)
                subst i
                exact block_0033
              · have heq : i = Fin.ofNat 114 34 := Fin.ext (by change i.val = 34; omega)
                subst i
                exact block_0034
        · by_cases h_35_42 : i.val < 38
          · by_cases h_35_38 : i.val < 36
            · have heq : i = Fin.ofNat 114 35 := Fin.ext (by change i.val = 35; omega)
              subst i
              exact block_0035
            · by_cases h_36_38 : i.val < 37
              · have heq : i = Fin.ofNat 114 36 := Fin.ext (by change i.val = 36; omega)
                subst i
                exact block_0036
              · have heq : i = Fin.ofNat 114 37 := Fin.ext (by change i.val = 37; omega)
                subst i
                exact block_0037
          · by_cases h_38_42 : i.val < 40
            · by_cases h_38_40 : i.val < 39
              · have heq : i = Fin.ofNat 114 38 := Fin.ext (by change i.val = 38; omega)
                subst i
                exact block_0038
              · have heq : i = Fin.ofNat 114 39 := Fin.ext (by change i.val = 39; omega)
                subst i
                exact block_0039
            · by_cases h_40_42 : i.val < 41
              · have heq : i = Fin.ofNat 114 40 := Fin.ext (by change i.val = 40; omega)
                subst i
                exact block_0040
              · have heq : i = Fin.ofNat 114 41 := Fin.ext (by change i.val = 41; omega)
                subst i
                exact block_0041
      · by_cases h_42_57 : i.val < 49
        · by_cases h_42_49 : i.val < 45
          · by_cases h_42_45 : i.val < 43
            · have heq : i = Fin.ofNat 114 42 := Fin.ext (by change i.val = 42; omega)
              subst i
              exact block_0042
            · by_cases h_43_45 : i.val < 44
              · have heq : i = Fin.ofNat 114 43 := Fin.ext (by change i.val = 43; omega)
                subst i
                exact block_0043
              · have heq : i = Fin.ofNat 114 44 := Fin.ext (by change i.val = 44; omega)
                subst i
                exact block_0044
          · by_cases h_45_49 : i.val < 47
            · by_cases h_45_47 : i.val < 46
              · have heq : i = Fin.ofNat 114 45 := Fin.ext (by change i.val = 45; omega)
                subst i
                exact block_0045
              · have heq : i = Fin.ofNat 114 46 := Fin.ext (by change i.val = 46; omega)
                subst i
                exact block_0046
            · by_cases h_47_49 : i.val < 48
              · have heq : i = Fin.ofNat 114 47 := Fin.ext (by change i.val = 47; omega)
                subst i
                exact block_0047
              · have heq : i = Fin.ofNat 114 48 := Fin.ext (by change i.val = 48; omega)
                subst i
                exact block_0048
        · by_cases h_49_57 : i.val < 53
          · by_cases h_49_53 : i.val < 51
            · by_cases h_49_51 : i.val < 50
              · have heq : i = Fin.ofNat 114 49 := Fin.ext (by change i.val = 49; omega)
                subst i
                exact block_0049
              · have heq : i = Fin.ofNat 114 50 := Fin.ext (by change i.val = 50; omega)
                subst i
                exact block_0050
            · by_cases h_51_53 : i.val < 52
              · have heq : i = Fin.ofNat 114 51 := Fin.ext (by change i.val = 51; omega)
                subst i
                exact block_0051
              · have heq : i = Fin.ofNat 114 52 := Fin.ext (by change i.val = 52; omega)
                subst i
                exact block_0052
          · by_cases h_53_57 : i.val < 55
            · by_cases h_53_55 : i.val < 54
              · have heq : i = Fin.ofNat 114 53 := Fin.ext (by change i.val = 53; omega)
                subst i
                exact block_0053
              · have heq : i = Fin.ofNat 114 54 := Fin.ext (by change i.val = 54; omega)
                subst i
                exact block_0054
            · by_cases h_55_57 : i.val < 56
              · have heq : i = Fin.ofNat 114 55 := Fin.ext (by change i.val = 55; omega)
                subst i
                exact block_0055
              · have heq : i = Fin.ofNat 114 56 := Fin.ext (by change i.val = 56; omega)
                subst i
                exact block_0056
  · by_cases h_57_114 : i.val < 85
    · by_cases h_57_85 : i.val < 71
      · by_cases h_57_71 : i.val < 64
        · by_cases h_57_64 : i.val < 60
          · by_cases h_57_60 : i.val < 58
            · have heq : i = Fin.ofNat 114 57 := Fin.ext (by change i.val = 57; omega)
              subst i
              exact block_0057
            · by_cases h_58_60 : i.val < 59
              · have heq : i = Fin.ofNat 114 58 := Fin.ext (by change i.val = 58; omega)
                subst i
                exact block_0058
              · have heq : i = Fin.ofNat 114 59 := Fin.ext (by change i.val = 59; omega)
                subst i
                exact block_0059
          · by_cases h_60_64 : i.val < 62
            · by_cases h_60_62 : i.val < 61
              · have heq : i = Fin.ofNat 114 60 := Fin.ext (by change i.val = 60; omega)
                subst i
                exact block_0060
              · have heq : i = Fin.ofNat 114 61 := Fin.ext (by change i.val = 61; omega)
                subst i
                exact block_0061
            · by_cases h_62_64 : i.val < 63
              · have heq : i = Fin.ofNat 114 62 := Fin.ext (by change i.val = 62; omega)
                subst i
                exact block_0062
              · have heq : i = Fin.ofNat 114 63 := Fin.ext (by change i.val = 63; omega)
                subst i
                exact block_0063
        · by_cases h_64_71 : i.val < 67
          · by_cases h_64_67 : i.val < 65
            · have heq : i = Fin.ofNat 114 64 := Fin.ext (by change i.val = 64; omega)
              subst i
              exact block_0064
            · by_cases h_65_67 : i.val < 66
              · have heq : i = Fin.ofNat 114 65 := Fin.ext (by change i.val = 65; omega)
                subst i
                exact block_0065
              · have heq : i = Fin.ofNat 114 66 := Fin.ext (by change i.val = 66; omega)
                subst i
                exact block_0066
          · by_cases h_67_71 : i.val < 69
            · by_cases h_67_69 : i.val < 68
              · have heq : i = Fin.ofNat 114 67 := Fin.ext (by change i.val = 67; omega)
                subst i
                exact block_0067
              · have heq : i = Fin.ofNat 114 68 := Fin.ext (by change i.val = 68; omega)
                subst i
                exact block_0068
            · by_cases h_69_71 : i.val < 70
              · have heq : i = Fin.ofNat 114 69 := Fin.ext (by change i.val = 69; omega)
                subst i
                exact block_0069
              · have heq : i = Fin.ofNat 114 70 := Fin.ext (by change i.val = 70; omega)
                subst i
                exact block_0070
      · by_cases h_71_85 : i.val < 78
        · by_cases h_71_78 : i.val < 74
          · by_cases h_71_74 : i.val < 72
            · have heq : i = Fin.ofNat 114 71 := Fin.ext (by change i.val = 71; omega)
              subst i
              exact block_0071
            · by_cases h_72_74 : i.val < 73
              · have heq : i = Fin.ofNat 114 72 := Fin.ext (by change i.val = 72; omega)
                subst i
                exact block_0072
              · have heq : i = Fin.ofNat 114 73 := Fin.ext (by change i.val = 73; omega)
                subst i
                exact block_0073
          · by_cases h_74_78 : i.val < 76
            · by_cases h_74_76 : i.val < 75
              · have heq : i = Fin.ofNat 114 74 := Fin.ext (by change i.val = 74; omega)
                subst i
                exact block_0074
              · have heq : i = Fin.ofNat 114 75 := Fin.ext (by change i.val = 75; omega)
                subst i
                exact block_0075
            · by_cases h_76_78 : i.val < 77
              · have heq : i = Fin.ofNat 114 76 := Fin.ext (by change i.val = 76; omega)
                subst i
                exact block_0076
              · have heq : i = Fin.ofNat 114 77 := Fin.ext (by change i.val = 77; omega)
                subst i
                exact block_0077
        · by_cases h_78_85 : i.val < 81
          · by_cases h_78_81 : i.val < 79
            · have heq : i = Fin.ofNat 114 78 := Fin.ext (by change i.val = 78; omega)
              subst i
              exact block_0078
            · by_cases h_79_81 : i.val < 80
              · have heq : i = Fin.ofNat 114 79 := Fin.ext (by change i.val = 79; omega)
                subst i
                exact block_0079
              · have heq : i = Fin.ofNat 114 80 := Fin.ext (by change i.val = 80; omega)
                subst i
                exact block_0080
          · by_cases h_81_85 : i.val < 83
            · by_cases h_81_83 : i.val < 82
              · have heq : i = Fin.ofNat 114 81 := Fin.ext (by change i.val = 81; omega)
                subst i
                exact block_0081
              · have heq : i = Fin.ofNat 114 82 := Fin.ext (by change i.val = 82; omega)
                subst i
                exact block_0082
            · by_cases h_83_85 : i.val < 84
              · have heq : i = Fin.ofNat 114 83 := Fin.ext (by change i.val = 83; omega)
                subst i
                exact block_0083
              · have heq : i = Fin.ofNat 114 84 := Fin.ext (by change i.val = 84; omega)
                subst i
                exact block_0084
    · by_cases h_85_114 : i.val < 99
      · by_cases h_85_99 : i.val < 92
        · by_cases h_85_92 : i.val < 88
          · by_cases h_85_88 : i.val < 86
            · have heq : i = Fin.ofNat 114 85 := Fin.ext (by change i.val = 85; omega)
              subst i
              exact block_0085
            · by_cases h_86_88 : i.val < 87
              · have heq : i = Fin.ofNat 114 86 := Fin.ext (by change i.val = 86; omega)
                subst i
                exact block_0086
              · have heq : i = Fin.ofNat 114 87 := Fin.ext (by change i.val = 87; omega)
                subst i
                exact block_0087
          · by_cases h_88_92 : i.val < 90
            · by_cases h_88_90 : i.val < 89
              · have heq : i = Fin.ofNat 114 88 := Fin.ext (by change i.val = 88; omega)
                subst i
                exact block_0088
              · have heq : i = Fin.ofNat 114 89 := Fin.ext (by change i.val = 89; omega)
                subst i
                exact block_0089
            · by_cases h_90_92 : i.val < 91
              · have heq : i = Fin.ofNat 114 90 := Fin.ext (by change i.val = 90; omega)
                subst i
                exact block_0090
              · have heq : i = Fin.ofNat 114 91 := Fin.ext (by change i.val = 91; omega)
                subst i
                exact block_0091
        · by_cases h_92_99 : i.val < 95
          · by_cases h_92_95 : i.val < 93
            · have heq : i = Fin.ofNat 114 92 := Fin.ext (by change i.val = 92; omega)
              subst i
              exact block_0092
            · by_cases h_93_95 : i.val < 94
              · have heq : i = Fin.ofNat 114 93 := Fin.ext (by change i.val = 93; omega)
                subst i
                exact block_0093
              · have heq : i = Fin.ofNat 114 94 := Fin.ext (by change i.val = 94; omega)
                subst i
                exact block_0094
          · by_cases h_95_99 : i.val < 97
            · by_cases h_95_97 : i.val < 96
              · have heq : i = Fin.ofNat 114 95 := Fin.ext (by change i.val = 95; omega)
                subst i
                exact block_0095
              · have heq : i = Fin.ofNat 114 96 := Fin.ext (by change i.val = 96; omega)
                subst i
                exact block_0096
            · by_cases h_97_99 : i.val < 98
              · have heq : i = Fin.ofNat 114 97 := Fin.ext (by change i.val = 97; omega)
                subst i
                exact block_0097
              · have heq : i = Fin.ofNat 114 98 := Fin.ext (by change i.val = 98; omega)
                subst i
                exact block_0098
      · by_cases h_99_114 : i.val < 106
        · by_cases h_99_106 : i.val < 102
          · by_cases h_99_102 : i.val < 100
            · have heq : i = Fin.ofNat 114 99 := Fin.ext (by change i.val = 99; omega)
              subst i
              exact block_0099
            · by_cases h_100_102 : i.val < 101
              · have heq : i = Fin.ofNat 114 100 := Fin.ext (by change i.val = 100; omega)
                subst i
                exact block_0100
              · have heq : i = Fin.ofNat 114 101 := Fin.ext (by change i.val = 101; omega)
                subst i
                exact block_0101
          · by_cases h_102_106 : i.val < 104
            · by_cases h_102_104 : i.val < 103
              · have heq : i = Fin.ofNat 114 102 := Fin.ext (by change i.val = 102; omega)
                subst i
                exact block_0102
              · have heq : i = Fin.ofNat 114 103 := Fin.ext (by change i.val = 103; omega)
                subst i
                exact block_0103
            · by_cases h_104_106 : i.val < 105
              · have heq : i = Fin.ofNat 114 104 := Fin.ext (by change i.val = 104; omega)
                subst i
                exact block_0104
              · have heq : i = Fin.ofNat 114 105 := Fin.ext (by change i.val = 105; omega)
                subst i
                exact block_0105
        · by_cases h_106_114 : i.val < 110
          · by_cases h_106_110 : i.val < 108
            · by_cases h_106_108 : i.val < 107
              · have heq : i = Fin.ofNat 114 106 := Fin.ext (by change i.val = 106; omega)
                subst i
                exact block_0106
              · have heq : i = Fin.ofNat 114 107 := Fin.ext (by change i.val = 107; omega)
                subst i
                exact block_0107
            · by_cases h_108_110 : i.val < 109
              · have heq : i = Fin.ofNat 114 108 := Fin.ext (by change i.val = 108; omega)
                subst i
                exact block_0108
              · have heq : i = Fin.ofNat 114 109 := Fin.ext (by change i.val = 109; omega)
                subst i
                exact block_0109
          · by_cases h_110_114 : i.val < 112
            · by_cases h_110_112 : i.val < 111
              · have heq : i = Fin.ofNat 114 110 := Fin.ext (by change i.val = 110; omega)
                subst i
                exact block_0110
              · have heq : i = Fin.ofNat 114 111 := Fin.ext (by change i.val = 111; omega)
                subst i
                exact block_0111
            · by_cases h_112_114 : i.val < 113
              · have heq : i = Fin.ofNat 114 112 := Fin.ext (by change i.val = 112; omega)
                subst i
                exact block_0112
              · have heq : i = Fin.ofNat 114 113 := Fin.ext (by change i.val = 113; omega)
                subst i
                exact block_0113
end Papers.RationalityTen.RootedCanonical.RootedSixExtra03.T6
