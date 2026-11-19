module
prelude
public import RootedSevenPure052CanonicalS5T0Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenPure052.S5T0
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 5 (raw i) template root
      FacetUniverses.RootedSevenPure052.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 153 := i.isLt
  by_cases h_0_153 : i.val < 76
  · by_cases h_0_76 : i.val < 38
    · by_cases h_0_38 : i.val < 19
      · by_cases h_0_19 : i.val < 9
        · by_cases h_0_9 : i.val < 4
          · by_cases h_0_4 : i.val < 2
            · by_cases h_0_2 : i.val < 1
              · have heq : i = Fin.ofNat 153 0 := Fin.ext (by change i.val = 0; omega)
                subst i
                exact block_0000
              · have heq : i = Fin.ofNat 153 1 := Fin.ext (by change i.val = 1; omega)
                subst i
                exact block_0001
            · by_cases h_2_4 : i.val < 3
              · have heq : i = Fin.ofNat 153 2 := Fin.ext (by change i.val = 2; omega)
                subst i
                exact block_0002
              · have heq : i = Fin.ofNat 153 3 := Fin.ext (by change i.val = 3; omega)
                subst i
                exact block_0003
          · by_cases h_4_9 : i.val < 6
            · by_cases h_4_6 : i.val < 5
              · have heq : i = Fin.ofNat 153 4 := Fin.ext (by change i.val = 4; omega)
                subst i
                exact block_0004
              · have heq : i = Fin.ofNat 153 5 := Fin.ext (by change i.val = 5; omega)
                subst i
                exact block_0005
            · by_cases h_6_9 : i.val < 7
              · have heq : i = Fin.ofNat 153 6 := Fin.ext (by change i.val = 6; omega)
                subst i
                exact block_0006
              · by_cases h_7_9 : i.val < 8
                · have heq : i = Fin.ofNat 153 7 := Fin.ext (by change i.val = 7; omega)
                  subst i
                  exact block_0007
                · have heq : i = Fin.ofNat 153 8 := Fin.ext (by change i.val = 8; omega)
                  subst i
                  exact block_0008
        · by_cases h_9_19 : i.val < 14
          · by_cases h_9_14 : i.val < 11
            · by_cases h_9_11 : i.val < 10
              · have heq : i = Fin.ofNat 153 9 := Fin.ext (by change i.val = 9; omega)
                subst i
                exact block_0009
              · have heq : i = Fin.ofNat 153 10 := Fin.ext (by change i.val = 10; omega)
                subst i
                exact block_0010
            · by_cases h_11_14 : i.val < 12
              · have heq : i = Fin.ofNat 153 11 := Fin.ext (by change i.val = 11; omega)
                subst i
                exact block_0011
              · by_cases h_12_14 : i.val < 13
                · have heq : i = Fin.ofNat 153 12 := Fin.ext (by change i.val = 12; omega)
                  subst i
                  exact block_0012
                · have heq : i = Fin.ofNat 153 13 := Fin.ext (by change i.val = 13; omega)
                  subst i
                  exact block_0013
          · by_cases h_14_19 : i.val < 16
            · by_cases h_14_16 : i.val < 15
              · have heq : i = Fin.ofNat 153 14 := Fin.ext (by change i.val = 14; omega)
                subst i
                exact block_0014
              · have heq : i = Fin.ofNat 153 15 := Fin.ext (by change i.val = 15; omega)
                subst i
                exact block_0015
            · by_cases h_16_19 : i.val < 17
              · have heq : i = Fin.ofNat 153 16 := Fin.ext (by change i.val = 16; omega)
                subst i
                exact block_0016
              · by_cases h_17_19 : i.val < 18
                · have heq : i = Fin.ofNat 153 17 := Fin.ext (by change i.val = 17; omega)
                  subst i
                  exact block_0017
                · have heq : i = Fin.ofNat 153 18 := Fin.ext (by change i.val = 18; omega)
                  subst i
                  exact block_0018
      · by_cases h_19_38 : i.val < 28
        · by_cases h_19_28 : i.val < 23
          · by_cases h_19_23 : i.val < 21
            · by_cases h_19_21 : i.val < 20
              · have heq : i = Fin.ofNat 153 19 := Fin.ext (by change i.val = 19; omega)
                subst i
                exact block_0019
              · have heq : i = Fin.ofNat 153 20 := Fin.ext (by change i.val = 20; omega)
                subst i
                exact block_0020
            · by_cases h_21_23 : i.val < 22
              · have heq : i = Fin.ofNat 153 21 := Fin.ext (by change i.val = 21; omega)
                subst i
                exact block_0021
              · have heq : i = Fin.ofNat 153 22 := Fin.ext (by change i.val = 22; omega)
                subst i
                exact block_0022
          · by_cases h_23_28 : i.val < 25
            · by_cases h_23_25 : i.val < 24
              · have heq : i = Fin.ofNat 153 23 := Fin.ext (by change i.val = 23; omega)
                subst i
                exact block_0023
              · have heq : i = Fin.ofNat 153 24 := Fin.ext (by change i.val = 24; omega)
                subst i
                exact block_0024
            · by_cases h_25_28 : i.val < 26
              · have heq : i = Fin.ofNat 153 25 := Fin.ext (by change i.val = 25; omega)
                subst i
                exact block_0025
              · by_cases h_26_28 : i.val < 27
                · have heq : i = Fin.ofNat 153 26 := Fin.ext (by change i.val = 26; omega)
                  subst i
                  exact block_0026
                · have heq : i = Fin.ofNat 153 27 := Fin.ext (by change i.val = 27; omega)
                  subst i
                  exact block_0027
        · by_cases h_28_38 : i.val < 33
          · by_cases h_28_33 : i.val < 30
            · by_cases h_28_30 : i.val < 29
              · have heq : i = Fin.ofNat 153 28 := Fin.ext (by change i.val = 28; omega)
                subst i
                exact block_0028
              · have heq : i = Fin.ofNat 153 29 := Fin.ext (by change i.val = 29; omega)
                subst i
                exact block_0029
            · by_cases h_30_33 : i.val < 31
              · have heq : i = Fin.ofNat 153 30 := Fin.ext (by change i.val = 30; omega)
                subst i
                exact block_0030
              · by_cases h_31_33 : i.val < 32
                · have heq : i = Fin.ofNat 153 31 := Fin.ext (by change i.val = 31; omega)
                  subst i
                  exact block_0031
                · have heq : i = Fin.ofNat 153 32 := Fin.ext (by change i.val = 32; omega)
                  subst i
                  exact block_0032
          · by_cases h_33_38 : i.val < 35
            · by_cases h_33_35 : i.val < 34
              · have heq : i = Fin.ofNat 153 33 := Fin.ext (by change i.val = 33; omega)
                subst i
                exact block_0033
              · have heq : i = Fin.ofNat 153 34 := Fin.ext (by change i.val = 34; omega)
                subst i
                exact block_0034
            · by_cases h_35_38 : i.val < 36
              · have heq : i = Fin.ofNat 153 35 := Fin.ext (by change i.val = 35; omega)
                subst i
                exact block_0035
              · by_cases h_36_38 : i.val < 37
                · have heq : i = Fin.ofNat 153 36 := Fin.ext (by change i.val = 36; omega)
                  subst i
                  exact block_0036
                · have heq : i = Fin.ofNat 153 37 := Fin.ext (by change i.val = 37; omega)
                  subst i
                  exact block_0037
    · by_cases h_38_76 : i.val < 57
      · by_cases h_38_57 : i.val < 47
        · by_cases h_38_47 : i.val < 42
          · by_cases h_38_42 : i.val < 40
            · by_cases h_38_40 : i.val < 39
              · have heq : i = Fin.ofNat 153 38 := Fin.ext (by change i.val = 38; omega)
                subst i
                exact block_0038
              · have heq : i = Fin.ofNat 153 39 := Fin.ext (by change i.val = 39; omega)
                subst i
                exact block_0039
            · by_cases h_40_42 : i.val < 41
              · have heq : i = Fin.ofNat 153 40 := Fin.ext (by change i.val = 40; omega)
                subst i
                exact block_0040
              · have heq : i = Fin.ofNat 153 41 := Fin.ext (by change i.val = 41; omega)
                subst i
                exact block_0041
          · by_cases h_42_47 : i.val < 44
            · by_cases h_42_44 : i.val < 43
              · have heq : i = Fin.ofNat 153 42 := Fin.ext (by change i.val = 42; omega)
                subst i
                exact block_0042
              · have heq : i = Fin.ofNat 153 43 := Fin.ext (by change i.val = 43; omega)
                subst i
                exact block_0043
            · by_cases h_44_47 : i.val < 45
              · have heq : i = Fin.ofNat 153 44 := Fin.ext (by change i.val = 44; omega)
                subst i
                exact block_0044
              · by_cases h_45_47 : i.val < 46
                · have heq : i = Fin.ofNat 153 45 := Fin.ext (by change i.val = 45; omega)
                  subst i
                  exact block_0045
                · have heq : i = Fin.ofNat 153 46 := Fin.ext (by change i.val = 46; omega)
                  subst i
                  exact block_0046
        · by_cases h_47_57 : i.val < 52
          · by_cases h_47_52 : i.val < 49
            · by_cases h_47_49 : i.val < 48
              · have heq : i = Fin.ofNat 153 47 := Fin.ext (by change i.val = 47; omega)
                subst i
                exact block_0047
              · have heq : i = Fin.ofNat 153 48 := Fin.ext (by change i.val = 48; omega)
                subst i
                exact block_0048
            · by_cases h_49_52 : i.val < 50
              · have heq : i = Fin.ofNat 153 49 := Fin.ext (by change i.val = 49; omega)
                subst i
                exact block_0049
              · by_cases h_50_52 : i.val < 51
                · have heq : i = Fin.ofNat 153 50 := Fin.ext (by change i.val = 50; omega)
                  subst i
                  exact block_0050
                · have heq : i = Fin.ofNat 153 51 := Fin.ext (by change i.val = 51; omega)
                  subst i
                  exact block_0051
          · by_cases h_52_57 : i.val < 54
            · by_cases h_52_54 : i.val < 53
              · have heq : i = Fin.ofNat 153 52 := Fin.ext (by change i.val = 52; omega)
                subst i
                exact block_0052
              · have heq : i = Fin.ofNat 153 53 := Fin.ext (by change i.val = 53; omega)
                subst i
                exact block_0053
            · by_cases h_54_57 : i.val < 55
              · have heq : i = Fin.ofNat 153 54 := Fin.ext (by change i.val = 54; omega)
                subst i
                exact block_0054
              · by_cases h_55_57 : i.val < 56
                · have heq : i = Fin.ofNat 153 55 := Fin.ext (by change i.val = 55; omega)
                  subst i
                  exact block_0055
                · have heq : i = Fin.ofNat 153 56 := Fin.ext (by change i.val = 56; omega)
                  subst i
                  exact block_0056
      · by_cases h_57_76 : i.val < 66
        · by_cases h_57_66 : i.val < 61
          · by_cases h_57_61 : i.val < 59
            · by_cases h_57_59 : i.val < 58
              · have heq : i = Fin.ofNat 153 57 := Fin.ext (by change i.val = 57; omega)
                subst i
                exact block_0057
              · have heq : i = Fin.ofNat 153 58 := Fin.ext (by change i.val = 58; omega)
                subst i
                exact block_0058
            · by_cases h_59_61 : i.val < 60
              · have heq : i = Fin.ofNat 153 59 := Fin.ext (by change i.val = 59; omega)
                subst i
                exact block_0059
              · have heq : i = Fin.ofNat 153 60 := Fin.ext (by change i.val = 60; omega)
                subst i
                exact block_0060
          · by_cases h_61_66 : i.val < 63
            · by_cases h_61_63 : i.val < 62
              · have heq : i = Fin.ofNat 153 61 := Fin.ext (by change i.val = 61; omega)
                subst i
                exact block_0061
              · have heq : i = Fin.ofNat 153 62 := Fin.ext (by change i.val = 62; omega)
                subst i
                exact block_0062
            · by_cases h_63_66 : i.val < 64
              · have heq : i = Fin.ofNat 153 63 := Fin.ext (by change i.val = 63; omega)
                subst i
                exact block_0063
              · by_cases h_64_66 : i.val < 65
                · have heq : i = Fin.ofNat 153 64 := Fin.ext (by change i.val = 64; omega)
                  subst i
                  exact block_0064
                · have heq : i = Fin.ofNat 153 65 := Fin.ext (by change i.val = 65; omega)
                  subst i
                  exact block_0065
        · by_cases h_66_76 : i.val < 71
          · by_cases h_66_71 : i.val < 68
            · by_cases h_66_68 : i.val < 67
              · have heq : i = Fin.ofNat 153 66 := Fin.ext (by change i.val = 66; omega)
                subst i
                exact block_0066
              · have heq : i = Fin.ofNat 153 67 := Fin.ext (by change i.val = 67; omega)
                subst i
                exact block_0067
            · by_cases h_68_71 : i.val < 69
              · have heq : i = Fin.ofNat 153 68 := Fin.ext (by change i.val = 68; omega)
                subst i
                exact block_0068
              · by_cases h_69_71 : i.val < 70
                · have heq : i = Fin.ofNat 153 69 := Fin.ext (by change i.val = 69; omega)
                  subst i
                  exact block_0069
                · have heq : i = Fin.ofNat 153 70 := Fin.ext (by change i.val = 70; omega)
                  subst i
                  exact block_0070
          · by_cases h_71_76 : i.val < 73
            · by_cases h_71_73 : i.val < 72
              · have heq : i = Fin.ofNat 153 71 := Fin.ext (by change i.val = 71; omega)
                subst i
                exact block_0071
              · have heq : i = Fin.ofNat 153 72 := Fin.ext (by change i.val = 72; omega)
                subst i
                exact block_0072
            · by_cases h_73_76 : i.val < 74
              · have heq : i = Fin.ofNat 153 73 := Fin.ext (by change i.val = 73; omega)
                subst i
                exact block_0073
              · by_cases h_74_76 : i.val < 75
                · have heq : i = Fin.ofNat 153 74 := Fin.ext (by change i.val = 74; omega)
                  subst i
                  exact block_0074
                · have heq : i = Fin.ofNat 153 75 := Fin.ext (by change i.val = 75; omega)
                  subst i
                  exact block_0075
  · by_cases h_76_153 : i.val < 114
    · by_cases h_76_114 : i.val < 95
      · by_cases h_76_95 : i.val < 85
        · by_cases h_76_85 : i.val < 80
          · by_cases h_76_80 : i.val < 78
            · by_cases h_76_78 : i.val < 77
              · have heq : i = Fin.ofNat 153 76 := Fin.ext (by change i.val = 76; omega)
                subst i
                exact block_0076
              · have heq : i = Fin.ofNat 153 77 := Fin.ext (by change i.val = 77; omega)
                subst i
                exact block_0077
            · by_cases h_78_80 : i.val < 79
              · have heq : i = Fin.ofNat 153 78 := Fin.ext (by change i.val = 78; omega)
                subst i
                exact block_0078
              · have heq : i = Fin.ofNat 153 79 := Fin.ext (by change i.val = 79; omega)
                subst i
                exact block_0079
          · by_cases h_80_85 : i.val < 82
            · by_cases h_80_82 : i.val < 81
              · have heq : i = Fin.ofNat 153 80 := Fin.ext (by change i.val = 80; omega)
                subst i
                exact block_0080
              · have heq : i = Fin.ofNat 153 81 := Fin.ext (by change i.val = 81; omega)
                subst i
                exact block_0081
            · by_cases h_82_85 : i.val < 83
              · have heq : i = Fin.ofNat 153 82 := Fin.ext (by change i.val = 82; omega)
                subst i
                exact block_0082
              · by_cases h_83_85 : i.val < 84
                · have heq : i = Fin.ofNat 153 83 := Fin.ext (by change i.val = 83; omega)
                  subst i
                  exact block_0083
                · have heq : i = Fin.ofNat 153 84 := Fin.ext (by change i.val = 84; omega)
                  subst i
                  exact block_0084
        · by_cases h_85_95 : i.val < 90
          · by_cases h_85_90 : i.val < 87
            · by_cases h_85_87 : i.val < 86
              · have heq : i = Fin.ofNat 153 85 := Fin.ext (by change i.val = 85; omega)
                subst i
                exact block_0085
              · have heq : i = Fin.ofNat 153 86 := Fin.ext (by change i.val = 86; omega)
                subst i
                exact block_0086
            · by_cases h_87_90 : i.val < 88
              · have heq : i = Fin.ofNat 153 87 := Fin.ext (by change i.val = 87; omega)
                subst i
                exact block_0087
              · by_cases h_88_90 : i.val < 89
                · have heq : i = Fin.ofNat 153 88 := Fin.ext (by change i.val = 88; omega)
                  subst i
                  exact block_0088
                · have heq : i = Fin.ofNat 153 89 := Fin.ext (by change i.val = 89; omega)
                  subst i
                  exact block_0089
          · by_cases h_90_95 : i.val < 92
            · by_cases h_90_92 : i.val < 91
              · have heq : i = Fin.ofNat 153 90 := Fin.ext (by change i.val = 90; omega)
                subst i
                exact block_0090
              · have heq : i = Fin.ofNat 153 91 := Fin.ext (by change i.val = 91; omega)
                subst i
                exact block_0091
            · by_cases h_92_95 : i.val < 93
              · have heq : i = Fin.ofNat 153 92 := Fin.ext (by change i.val = 92; omega)
                subst i
                exact block_0092
              · by_cases h_93_95 : i.val < 94
                · have heq : i = Fin.ofNat 153 93 := Fin.ext (by change i.val = 93; omega)
                  subst i
                  exact block_0093
                · have heq : i = Fin.ofNat 153 94 := Fin.ext (by change i.val = 94; omega)
                  subst i
                  exact block_0094
      · by_cases h_95_114 : i.val < 104
        · by_cases h_95_104 : i.val < 99
          · by_cases h_95_99 : i.val < 97
            · by_cases h_95_97 : i.val < 96
              · have heq : i = Fin.ofNat 153 95 := Fin.ext (by change i.val = 95; omega)
                subst i
                exact block_0095
              · have heq : i = Fin.ofNat 153 96 := Fin.ext (by change i.val = 96; omega)
                subst i
                exact block_0096
            · by_cases h_97_99 : i.val < 98
              · have heq : i = Fin.ofNat 153 97 := Fin.ext (by change i.val = 97; omega)
                subst i
                exact block_0097
              · have heq : i = Fin.ofNat 153 98 := Fin.ext (by change i.val = 98; omega)
                subst i
                exact block_0098
          · by_cases h_99_104 : i.val < 101
            · by_cases h_99_101 : i.val < 100
              · have heq : i = Fin.ofNat 153 99 := Fin.ext (by change i.val = 99; omega)
                subst i
                exact block_0099
              · have heq : i = Fin.ofNat 153 100 := Fin.ext (by change i.val = 100; omega)
                subst i
                exact block_0100
            · by_cases h_101_104 : i.val < 102
              · have heq : i = Fin.ofNat 153 101 := Fin.ext (by change i.val = 101; omega)
                subst i
                exact block_0101
              · by_cases h_102_104 : i.val < 103
                · have heq : i = Fin.ofNat 153 102 := Fin.ext (by change i.val = 102; omega)
                  subst i
                  exact block_0102
                · have heq : i = Fin.ofNat 153 103 := Fin.ext (by change i.val = 103; omega)
                  subst i
                  exact block_0103
        · by_cases h_104_114 : i.val < 109
          · by_cases h_104_109 : i.val < 106
            · by_cases h_104_106 : i.val < 105
              · have heq : i = Fin.ofNat 153 104 := Fin.ext (by change i.val = 104; omega)
                subst i
                exact block_0104
              · have heq : i = Fin.ofNat 153 105 := Fin.ext (by change i.val = 105; omega)
                subst i
                exact block_0105
            · by_cases h_106_109 : i.val < 107
              · have heq : i = Fin.ofNat 153 106 := Fin.ext (by change i.val = 106; omega)
                subst i
                exact block_0106
              · by_cases h_107_109 : i.val < 108
                · have heq : i = Fin.ofNat 153 107 := Fin.ext (by change i.val = 107; omega)
                  subst i
                  exact block_0107
                · have heq : i = Fin.ofNat 153 108 := Fin.ext (by change i.val = 108; omega)
                  subst i
                  exact block_0108
          · by_cases h_109_114 : i.val < 111
            · by_cases h_109_111 : i.val < 110
              · have heq : i = Fin.ofNat 153 109 := Fin.ext (by change i.val = 109; omega)
                subst i
                exact block_0109
              · have heq : i = Fin.ofNat 153 110 := Fin.ext (by change i.val = 110; omega)
                subst i
                exact block_0110
            · by_cases h_111_114 : i.val < 112
              · have heq : i = Fin.ofNat 153 111 := Fin.ext (by change i.val = 111; omega)
                subst i
                exact block_0111
              · by_cases h_112_114 : i.val < 113
                · have heq : i = Fin.ofNat 153 112 := Fin.ext (by change i.val = 112; omega)
                  subst i
                  exact block_0112
                · have heq : i = Fin.ofNat 153 113 := Fin.ext (by change i.val = 113; omega)
                  subst i
                  exact block_0113
    · by_cases h_114_153 : i.val < 133
      · by_cases h_114_133 : i.val < 123
        · by_cases h_114_123 : i.val < 118
          · by_cases h_114_118 : i.val < 116
            · by_cases h_114_116 : i.val < 115
              · have heq : i = Fin.ofNat 153 114 := Fin.ext (by change i.val = 114; omega)
                subst i
                exact block_0114
              · have heq : i = Fin.ofNat 153 115 := Fin.ext (by change i.val = 115; omega)
                subst i
                exact block_0115
            · by_cases h_116_118 : i.val < 117
              · have heq : i = Fin.ofNat 153 116 := Fin.ext (by change i.val = 116; omega)
                subst i
                exact block_0116
              · have heq : i = Fin.ofNat 153 117 := Fin.ext (by change i.val = 117; omega)
                subst i
                exact block_0117
          · by_cases h_118_123 : i.val < 120
            · by_cases h_118_120 : i.val < 119
              · have heq : i = Fin.ofNat 153 118 := Fin.ext (by change i.val = 118; omega)
                subst i
                exact block_0118
              · have heq : i = Fin.ofNat 153 119 := Fin.ext (by change i.val = 119; omega)
                subst i
                exact block_0119
            · by_cases h_120_123 : i.val < 121
              · have heq : i = Fin.ofNat 153 120 := Fin.ext (by change i.val = 120; omega)
                subst i
                exact block_0120
              · by_cases h_121_123 : i.val < 122
                · have heq : i = Fin.ofNat 153 121 := Fin.ext (by change i.val = 121; omega)
                  subst i
                  exact block_0121
                · have heq : i = Fin.ofNat 153 122 := Fin.ext (by change i.val = 122; omega)
                  subst i
                  exact block_0122
        · by_cases h_123_133 : i.val < 128
          · by_cases h_123_128 : i.val < 125
            · by_cases h_123_125 : i.val < 124
              · have heq : i = Fin.ofNat 153 123 := Fin.ext (by change i.val = 123; omega)
                subst i
                exact block_0123
              · have heq : i = Fin.ofNat 153 124 := Fin.ext (by change i.val = 124; omega)
                subst i
                exact block_0124
            · by_cases h_125_128 : i.val < 126
              · have heq : i = Fin.ofNat 153 125 := Fin.ext (by change i.val = 125; omega)
                subst i
                exact block_0125
              · by_cases h_126_128 : i.val < 127
                · have heq : i = Fin.ofNat 153 126 := Fin.ext (by change i.val = 126; omega)
                  subst i
                  exact block_0126
                · have heq : i = Fin.ofNat 153 127 := Fin.ext (by change i.val = 127; omega)
                  subst i
                  exact block_0127
          · by_cases h_128_133 : i.val < 130
            · by_cases h_128_130 : i.val < 129
              · have heq : i = Fin.ofNat 153 128 := Fin.ext (by change i.val = 128; omega)
                subst i
                exact block_0128
              · have heq : i = Fin.ofNat 153 129 := Fin.ext (by change i.val = 129; omega)
                subst i
                exact block_0129
            · by_cases h_130_133 : i.val < 131
              · have heq : i = Fin.ofNat 153 130 := Fin.ext (by change i.val = 130; omega)
                subst i
                exact block_0130
              · by_cases h_131_133 : i.val < 132
                · have heq : i = Fin.ofNat 153 131 := Fin.ext (by change i.val = 131; omega)
                  subst i
                  exact block_0131
                · have heq : i = Fin.ofNat 153 132 := Fin.ext (by change i.val = 132; omega)
                  subst i
                  exact block_0132
      · by_cases h_133_153 : i.val < 143
        · by_cases h_133_143 : i.val < 138
          · by_cases h_133_138 : i.val < 135
            · by_cases h_133_135 : i.val < 134
              · have heq : i = Fin.ofNat 153 133 := Fin.ext (by change i.val = 133; omega)
                subst i
                exact block_0133
              · have heq : i = Fin.ofNat 153 134 := Fin.ext (by change i.val = 134; omega)
                subst i
                exact block_0134
            · by_cases h_135_138 : i.val < 136
              · have heq : i = Fin.ofNat 153 135 := Fin.ext (by change i.val = 135; omega)
                subst i
                exact block_0135
              · by_cases h_136_138 : i.val < 137
                · have heq : i = Fin.ofNat 153 136 := Fin.ext (by change i.val = 136; omega)
                  subst i
                  exact block_0136
                · have heq : i = Fin.ofNat 153 137 := Fin.ext (by change i.val = 137; omega)
                  subst i
                  exact block_0137
          · by_cases h_138_143 : i.val < 140
            · by_cases h_138_140 : i.val < 139
              · have heq : i = Fin.ofNat 153 138 := Fin.ext (by change i.val = 138; omega)
                subst i
                exact block_0138
              · have heq : i = Fin.ofNat 153 139 := Fin.ext (by change i.val = 139; omega)
                subst i
                exact block_0139
            · by_cases h_140_143 : i.val < 141
              · have heq : i = Fin.ofNat 153 140 := Fin.ext (by change i.val = 140; omega)
                subst i
                exact block_0140
              · by_cases h_141_143 : i.val < 142
                · have heq : i = Fin.ofNat 153 141 := Fin.ext (by change i.val = 141; omega)
                  subst i
                  exact block_0141
                · have heq : i = Fin.ofNat 153 142 := Fin.ext (by change i.val = 142; omega)
                  subst i
                  exact block_0142
        · by_cases h_143_153 : i.val < 148
          · by_cases h_143_148 : i.val < 145
            · by_cases h_143_145 : i.val < 144
              · have heq : i = Fin.ofNat 153 143 := Fin.ext (by change i.val = 143; omega)
                subst i
                exact block_0143
              · have heq : i = Fin.ofNat 153 144 := Fin.ext (by change i.val = 144; omega)
                subst i
                exact block_0144
            · by_cases h_145_148 : i.val < 146
              · have heq : i = Fin.ofNat 153 145 := Fin.ext (by change i.val = 145; omega)
                subst i
                exact block_0145
              · by_cases h_146_148 : i.val < 147
                · have heq : i = Fin.ofNat 153 146 := Fin.ext (by change i.val = 146; omega)
                  subst i
                  exact block_0146
                · have heq : i = Fin.ofNat 153 147 := Fin.ext (by change i.val = 147; omega)
                  subst i
                  exact block_0147
          · by_cases h_148_153 : i.val < 150
            · by_cases h_148_150 : i.val < 149
              · have heq : i = Fin.ofNat 153 148 := Fin.ext (by change i.val = 148; omega)
                subst i
                exact block_0148
              · have heq : i = Fin.ofNat 153 149 := Fin.ext (by change i.val = 149; omega)
                subst i
                exact block_0149
            · by_cases h_150_153 : i.val < 151
              · have heq : i = Fin.ofNat 153 150 := Fin.ext (by change i.val = 150; omega)
                subst i
                exact block_0150
              · by_cases h_151_153 : i.val < 152
                · have heq : i = Fin.ofNat 153 151 := Fin.ext (by change i.val = 151; omega)
                  subst i
                  exact block_0151
                · have heq : i = Fin.ofNat 153 152 := Fin.ext (by change i.val = 152; omega)
                  subst i
                  exact block_0152
end Papers.RationalityTen.RootedCanonical.RootedSevenPure052.S5T0
