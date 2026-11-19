module
prelude
public import RootedSixBase01CanonicalT5Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase01.T5
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 6 (raw i) template root
      FacetUniverses.RootedSixBase01.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 136 := i.isLt
  by_cases h_0_136 : i.val < 68
  · by_cases h_0_68 : i.val < 34
    · by_cases h_0_34 : i.val < 17
      · by_cases h_0_17 : i.val < 8
        · by_cases h_0_8 : i.val < 4
          · by_cases h_0_4 : i.val < 2
            · by_cases h_0_2 : i.val < 1
              · have heq : i = Fin.ofNat 136 0 := Fin.ext (by change i.val = 0; omega)
                subst i
                exact block_0000
              · have heq : i = Fin.ofNat 136 1 := Fin.ext (by change i.val = 1; omega)
                subst i
                exact block_0001
            · by_cases h_2_4 : i.val < 3
              · have heq : i = Fin.ofNat 136 2 := Fin.ext (by change i.val = 2; omega)
                subst i
                exact block_0002
              · have heq : i = Fin.ofNat 136 3 := Fin.ext (by change i.val = 3; omega)
                subst i
                exact block_0003
          · by_cases h_4_8 : i.val < 6
            · by_cases h_4_6 : i.val < 5
              · have heq : i = Fin.ofNat 136 4 := Fin.ext (by change i.val = 4; omega)
                subst i
                exact block_0004
              · have heq : i = Fin.ofNat 136 5 := Fin.ext (by change i.val = 5; omega)
                subst i
                exact block_0005
            · by_cases h_6_8 : i.val < 7
              · have heq : i = Fin.ofNat 136 6 := Fin.ext (by change i.val = 6; omega)
                subst i
                exact block_0006
              · have heq : i = Fin.ofNat 136 7 := Fin.ext (by change i.val = 7; omega)
                subst i
                exact block_0007
        · by_cases h_8_17 : i.val < 12
          · by_cases h_8_12 : i.val < 10
            · by_cases h_8_10 : i.val < 9
              · have heq : i = Fin.ofNat 136 8 := Fin.ext (by change i.val = 8; omega)
                subst i
                exact block_0008
              · have heq : i = Fin.ofNat 136 9 := Fin.ext (by change i.val = 9; omega)
                subst i
                exact block_0009
            · by_cases h_10_12 : i.val < 11
              · have heq : i = Fin.ofNat 136 10 := Fin.ext (by change i.val = 10; omega)
                subst i
                exact block_0010
              · have heq : i = Fin.ofNat 136 11 := Fin.ext (by change i.val = 11; omega)
                subst i
                exact block_0011
          · by_cases h_12_17 : i.val < 14
            · by_cases h_12_14 : i.val < 13
              · have heq : i = Fin.ofNat 136 12 := Fin.ext (by change i.val = 12; omega)
                subst i
                exact block_0012
              · have heq : i = Fin.ofNat 136 13 := Fin.ext (by change i.val = 13; omega)
                subst i
                exact block_0013
            · by_cases h_14_17 : i.val < 15
              · have heq : i = Fin.ofNat 136 14 := Fin.ext (by change i.val = 14; omega)
                subst i
                exact block_0014
              · by_cases h_15_17 : i.val < 16
                · have heq : i = Fin.ofNat 136 15 := Fin.ext (by change i.val = 15; omega)
                  subst i
                  exact block_0015
                · have heq : i = Fin.ofNat 136 16 := Fin.ext (by change i.val = 16; omega)
                  subst i
                  exact block_0016
      · by_cases h_17_34 : i.val < 25
        · by_cases h_17_25 : i.val < 21
          · by_cases h_17_21 : i.val < 19
            · by_cases h_17_19 : i.val < 18
              · have heq : i = Fin.ofNat 136 17 := Fin.ext (by change i.val = 17; omega)
                subst i
                exact block_0017
              · have heq : i = Fin.ofNat 136 18 := Fin.ext (by change i.val = 18; omega)
                subst i
                exact block_0018
            · by_cases h_19_21 : i.val < 20
              · have heq : i = Fin.ofNat 136 19 := Fin.ext (by change i.val = 19; omega)
                subst i
                exact block_0019
              · have heq : i = Fin.ofNat 136 20 := Fin.ext (by change i.val = 20; omega)
                subst i
                exact block_0020
          · by_cases h_21_25 : i.val < 23
            · by_cases h_21_23 : i.val < 22
              · have heq : i = Fin.ofNat 136 21 := Fin.ext (by change i.val = 21; omega)
                subst i
                exact block_0021
              · have heq : i = Fin.ofNat 136 22 := Fin.ext (by change i.val = 22; omega)
                subst i
                exact block_0022
            · by_cases h_23_25 : i.val < 24
              · have heq : i = Fin.ofNat 136 23 := Fin.ext (by change i.val = 23; omega)
                subst i
                exact block_0023
              · have heq : i = Fin.ofNat 136 24 := Fin.ext (by change i.val = 24; omega)
                subst i
                exact block_0024
        · by_cases h_25_34 : i.val < 29
          · by_cases h_25_29 : i.val < 27
            · by_cases h_25_27 : i.val < 26
              · have heq : i = Fin.ofNat 136 25 := Fin.ext (by change i.val = 25; omega)
                subst i
                exact block_0025
              · have heq : i = Fin.ofNat 136 26 := Fin.ext (by change i.val = 26; omega)
                subst i
                exact block_0026
            · by_cases h_27_29 : i.val < 28
              · have heq : i = Fin.ofNat 136 27 := Fin.ext (by change i.val = 27; omega)
                subst i
                exact block_0027
              · have heq : i = Fin.ofNat 136 28 := Fin.ext (by change i.val = 28; omega)
                subst i
                exact block_0028
          · by_cases h_29_34 : i.val < 31
            · by_cases h_29_31 : i.val < 30
              · have heq : i = Fin.ofNat 136 29 := Fin.ext (by change i.val = 29; omega)
                subst i
                exact block_0029
              · have heq : i = Fin.ofNat 136 30 := Fin.ext (by change i.val = 30; omega)
                subst i
                exact block_0030
            · by_cases h_31_34 : i.val < 32
              · have heq : i = Fin.ofNat 136 31 := Fin.ext (by change i.val = 31; omega)
                subst i
                exact block_0031
              · by_cases h_32_34 : i.val < 33
                · have heq : i = Fin.ofNat 136 32 := Fin.ext (by change i.val = 32; omega)
                  subst i
                  exact block_0032
                · have heq : i = Fin.ofNat 136 33 := Fin.ext (by change i.val = 33; omega)
                  subst i
                  exact block_0033
    · by_cases h_34_68 : i.val < 51
      · by_cases h_34_51 : i.val < 42
        · by_cases h_34_42 : i.val < 38
          · by_cases h_34_38 : i.val < 36
            · by_cases h_34_36 : i.val < 35
              · have heq : i = Fin.ofNat 136 34 := Fin.ext (by change i.val = 34; omega)
                subst i
                exact block_0034
              · have heq : i = Fin.ofNat 136 35 := Fin.ext (by change i.val = 35; omega)
                subst i
                exact block_0035
            · by_cases h_36_38 : i.val < 37
              · have heq : i = Fin.ofNat 136 36 := Fin.ext (by change i.val = 36; omega)
                subst i
                exact block_0036
              · have heq : i = Fin.ofNat 136 37 := Fin.ext (by change i.val = 37; omega)
                subst i
                exact block_0037
          · by_cases h_38_42 : i.val < 40
            · by_cases h_38_40 : i.val < 39
              · have heq : i = Fin.ofNat 136 38 := Fin.ext (by change i.val = 38; omega)
                subst i
                exact block_0038
              · have heq : i = Fin.ofNat 136 39 := Fin.ext (by change i.val = 39; omega)
                subst i
                exact block_0039
            · by_cases h_40_42 : i.val < 41
              · have heq : i = Fin.ofNat 136 40 := Fin.ext (by change i.val = 40; omega)
                subst i
                exact block_0040
              · have heq : i = Fin.ofNat 136 41 := Fin.ext (by change i.val = 41; omega)
                subst i
                exact block_0041
        · by_cases h_42_51 : i.val < 46
          · by_cases h_42_46 : i.val < 44
            · by_cases h_42_44 : i.val < 43
              · have heq : i = Fin.ofNat 136 42 := Fin.ext (by change i.val = 42; omega)
                subst i
                exact block_0042
              · have heq : i = Fin.ofNat 136 43 := Fin.ext (by change i.val = 43; omega)
                subst i
                exact block_0043
            · by_cases h_44_46 : i.val < 45
              · have heq : i = Fin.ofNat 136 44 := Fin.ext (by change i.val = 44; omega)
                subst i
                exact block_0044
              · have heq : i = Fin.ofNat 136 45 := Fin.ext (by change i.val = 45; omega)
                subst i
                exact block_0045
          · by_cases h_46_51 : i.val < 48
            · by_cases h_46_48 : i.val < 47
              · have heq : i = Fin.ofNat 136 46 := Fin.ext (by change i.val = 46; omega)
                subst i
                exact block_0046
              · have heq : i = Fin.ofNat 136 47 := Fin.ext (by change i.val = 47; omega)
                subst i
                exact block_0047
            · by_cases h_48_51 : i.val < 49
              · have heq : i = Fin.ofNat 136 48 := Fin.ext (by change i.val = 48; omega)
                subst i
                exact block_0048
              · by_cases h_49_51 : i.val < 50
                · have heq : i = Fin.ofNat 136 49 := Fin.ext (by change i.val = 49; omega)
                  subst i
                  exact block_0049
                · have heq : i = Fin.ofNat 136 50 := Fin.ext (by change i.val = 50; omega)
                  subst i
                  exact block_0050
      · by_cases h_51_68 : i.val < 59
        · by_cases h_51_59 : i.val < 55
          · by_cases h_51_55 : i.val < 53
            · by_cases h_51_53 : i.val < 52
              · have heq : i = Fin.ofNat 136 51 := Fin.ext (by change i.val = 51; omega)
                subst i
                exact block_0051
              · have heq : i = Fin.ofNat 136 52 := Fin.ext (by change i.val = 52; omega)
                subst i
                exact block_0052
            · by_cases h_53_55 : i.val < 54
              · have heq : i = Fin.ofNat 136 53 := Fin.ext (by change i.val = 53; omega)
                subst i
                exact block_0053
              · have heq : i = Fin.ofNat 136 54 := Fin.ext (by change i.val = 54; omega)
                subst i
                exact block_0054
          · by_cases h_55_59 : i.val < 57
            · by_cases h_55_57 : i.val < 56
              · have heq : i = Fin.ofNat 136 55 := Fin.ext (by change i.val = 55; omega)
                subst i
                exact block_0055
              · have heq : i = Fin.ofNat 136 56 := Fin.ext (by change i.val = 56; omega)
                subst i
                exact block_0056
            · by_cases h_57_59 : i.val < 58
              · have heq : i = Fin.ofNat 136 57 := Fin.ext (by change i.val = 57; omega)
                subst i
                exact block_0057
              · have heq : i = Fin.ofNat 136 58 := Fin.ext (by change i.val = 58; omega)
                subst i
                exact block_0058
        · by_cases h_59_68 : i.val < 63
          · by_cases h_59_63 : i.val < 61
            · by_cases h_59_61 : i.val < 60
              · have heq : i = Fin.ofNat 136 59 := Fin.ext (by change i.val = 59; omega)
                subst i
                exact block_0059
              · have heq : i = Fin.ofNat 136 60 := Fin.ext (by change i.val = 60; omega)
                subst i
                exact block_0060
            · by_cases h_61_63 : i.val < 62
              · have heq : i = Fin.ofNat 136 61 := Fin.ext (by change i.val = 61; omega)
                subst i
                exact block_0061
              · have heq : i = Fin.ofNat 136 62 := Fin.ext (by change i.val = 62; omega)
                subst i
                exact block_0062
          · by_cases h_63_68 : i.val < 65
            · by_cases h_63_65 : i.val < 64
              · have heq : i = Fin.ofNat 136 63 := Fin.ext (by change i.val = 63; omega)
                subst i
                exact block_0063
              · have heq : i = Fin.ofNat 136 64 := Fin.ext (by change i.val = 64; omega)
                subst i
                exact block_0064
            · by_cases h_65_68 : i.val < 66
              · have heq : i = Fin.ofNat 136 65 := Fin.ext (by change i.val = 65; omega)
                subst i
                exact block_0065
              · by_cases h_66_68 : i.val < 67
                · have heq : i = Fin.ofNat 136 66 := Fin.ext (by change i.val = 66; omega)
                  subst i
                  exact block_0066
                · have heq : i = Fin.ofNat 136 67 := Fin.ext (by change i.val = 67; omega)
                  subst i
                  exact block_0067
  · by_cases h_68_136 : i.val < 102
    · by_cases h_68_102 : i.val < 85
      · by_cases h_68_85 : i.val < 76
        · by_cases h_68_76 : i.val < 72
          · by_cases h_68_72 : i.val < 70
            · by_cases h_68_70 : i.val < 69
              · have heq : i = Fin.ofNat 136 68 := Fin.ext (by change i.val = 68; omega)
                subst i
                exact block_0068
              · have heq : i = Fin.ofNat 136 69 := Fin.ext (by change i.val = 69; omega)
                subst i
                exact block_0069
            · by_cases h_70_72 : i.val < 71
              · have heq : i = Fin.ofNat 136 70 := Fin.ext (by change i.val = 70; omega)
                subst i
                exact block_0070
              · have heq : i = Fin.ofNat 136 71 := Fin.ext (by change i.val = 71; omega)
                subst i
                exact block_0071
          · by_cases h_72_76 : i.val < 74
            · by_cases h_72_74 : i.val < 73
              · have heq : i = Fin.ofNat 136 72 := Fin.ext (by change i.val = 72; omega)
                subst i
                exact block_0072
              · have heq : i = Fin.ofNat 136 73 := Fin.ext (by change i.val = 73; omega)
                subst i
                exact block_0073
            · by_cases h_74_76 : i.val < 75
              · have heq : i = Fin.ofNat 136 74 := Fin.ext (by change i.val = 74; omega)
                subst i
                exact block_0074
              · have heq : i = Fin.ofNat 136 75 := Fin.ext (by change i.val = 75; omega)
                subst i
                exact block_0075
        · by_cases h_76_85 : i.val < 80
          · by_cases h_76_80 : i.val < 78
            · by_cases h_76_78 : i.val < 77
              · have heq : i = Fin.ofNat 136 76 := Fin.ext (by change i.val = 76; omega)
                subst i
                exact block_0076
              · have heq : i = Fin.ofNat 136 77 := Fin.ext (by change i.val = 77; omega)
                subst i
                exact block_0077
            · by_cases h_78_80 : i.val < 79
              · have heq : i = Fin.ofNat 136 78 := Fin.ext (by change i.val = 78; omega)
                subst i
                exact block_0078
              · have heq : i = Fin.ofNat 136 79 := Fin.ext (by change i.val = 79; omega)
                subst i
                exact block_0079
          · by_cases h_80_85 : i.val < 82
            · by_cases h_80_82 : i.val < 81
              · have heq : i = Fin.ofNat 136 80 := Fin.ext (by change i.val = 80; omega)
                subst i
                exact block_0080
              · have heq : i = Fin.ofNat 136 81 := Fin.ext (by change i.val = 81; omega)
                subst i
                exact block_0081
            · by_cases h_82_85 : i.val < 83
              · have heq : i = Fin.ofNat 136 82 := Fin.ext (by change i.val = 82; omega)
                subst i
                exact block_0082
              · by_cases h_83_85 : i.val < 84
                · have heq : i = Fin.ofNat 136 83 := Fin.ext (by change i.val = 83; omega)
                  subst i
                  exact block_0083
                · have heq : i = Fin.ofNat 136 84 := Fin.ext (by change i.val = 84; omega)
                  subst i
                  exact block_0084
      · by_cases h_85_102 : i.val < 93
        · by_cases h_85_93 : i.val < 89
          · by_cases h_85_89 : i.val < 87
            · by_cases h_85_87 : i.val < 86
              · have heq : i = Fin.ofNat 136 85 := Fin.ext (by change i.val = 85; omega)
                subst i
                exact block_0085
              · have heq : i = Fin.ofNat 136 86 := Fin.ext (by change i.val = 86; omega)
                subst i
                exact block_0086
            · by_cases h_87_89 : i.val < 88
              · have heq : i = Fin.ofNat 136 87 := Fin.ext (by change i.val = 87; omega)
                subst i
                exact block_0087
              · have heq : i = Fin.ofNat 136 88 := Fin.ext (by change i.val = 88; omega)
                subst i
                exact block_0088
          · by_cases h_89_93 : i.val < 91
            · by_cases h_89_91 : i.val < 90
              · have heq : i = Fin.ofNat 136 89 := Fin.ext (by change i.val = 89; omega)
                subst i
                exact block_0089
              · have heq : i = Fin.ofNat 136 90 := Fin.ext (by change i.val = 90; omega)
                subst i
                exact block_0090
            · by_cases h_91_93 : i.val < 92
              · have heq : i = Fin.ofNat 136 91 := Fin.ext (by change i.val = 91; omega)
                subst i
                exact block_0091
              · have heq : i = Fin.ofNat 136 92 := Fin.ext (by change i.val = 92; omega)
                subst i
                exact block_0092
        · by_cases h_93_102 : i.val < 97
          · by_cases h_93_97 : i.val < 95
            · by_cases h_93_95 : i.val < 94
              · have heq : i = Fin.ofNat 136 93 := Fin.ext (by change i.val = 93; omega)
                subst i
                exact block_0093
              · have heq : i = Fin.ofNat 136 94 := Fin.ext (by change i.val = 94; omega)
                subst i
                exact block_0094
            · by_cases h_95_97 : i.val < 96
              · have heq : i = Fin.ofNat 136 95 := Fin.ext (by change i.val = 95; omega)
                subst i
                exact block_0095
              · have heq : i = Fin.ofNat 136 96 := Fin.ext (by change i.val = 96; omega)
                subst i
                exact block_0096
          · by_cases h_97_102 : i.val < 99
            · by_cases h_97_99 : i.val < 98
              · have heq : i = Fin.ofNat 136 97 := Fin.ext (by change i.val = 97; omega)
                subst i
                exact block_0097
              · have heq : i = Fin.ofNat 136 98 := Fin.ext (by change i.val = 98; omega)
                subst i
                exact block_0098
            · by_cases h_99_102 : i.val < 100
              · have heq : i = Fin.ofNat 136 99 := Fin.ext (by change i.val = 99; omega)
                subst i
                exact block_0099
              · by_cases h_100_102 : i.val < 101
                · have heq : i = Fin.ofNat 136 100 := Fin.ext (by change i.val = 100; omega)
                  subst i
                  exact block_0100
                · have heq : i = Fin.ofNat 136 101 := Fin.ext (by change i.val = 101; omega)
                  subst i
                  exact block_0101
    · by_cases h_102_136 : i.val < 119
      · by_cases h_102_119 : i.val < 110
        · by_cases h_102_110 : i.val < 106
          · by_cases h_102_106 : i.val < 104
            · by_cases h_102_104 : i.val < 103
              · have heq : i = Fin.ofNat 136 102 := Fin.ext (by change i.val = 102; omega)
                subst i
                exact block_0102
              · have heq : i = Fin.ofNat 136 103 := Fin.ext (by change i.val = 103; omega)
                subst i
                exact block_0103
            · by_cases h_104_106 : i.val < 105
              · have heq : i = Fin.ofNat 136 104 := Fin.ext (by change i.val = 104; omega)
                subst i
                exact block_0104
              · have heq : i = Fin.ofNat 136 105 := Fin.ext (by change i.val = 105; omega)
                subst i
                exact block_0105
          · by_cases h_106_110 : i.val < 108
            · by_cases h_106_108 : i.val < 107
              · have heq : i = Fin.ofNat 136 106 := Fin.ext (by change i.val = 106; omega)
                subst i
                exact block_0106
              · have heq : i = Fin.ofNat 136 107 := Fin.ext (by change i.val = 107; omega)
                subst i
                exact block_0107
            · by_cases h_108_110 : i.val < 109
              · have heq : i = Fin.ofNat 136 108 := Fin.ext (by change i.val = 108; omega)
                subst i
                exact block_0108
              · have heq : i = Fin.ofNat 136 109 := Fin.ext (by change i.val = 109; omega)
                subst i
                exact block_0109
        · by_cases h_110_119 : i.val < 114
          · by_cases h_110_114 : i.val < 112
            · by_cases h_110_112 : i.val < 111
              · have heq : i = Fin.ofNat 136 110 := Fin.ext (by change i.val = 110; omega)
                subst i
                exact block_0110
              · have heq : i = Fin.ofNat 136 111 := Fin.ext (by change i.val = 111; omega)
                subst i
                exact block_0111
            · by_cases h_112_114 : i.val < 113
              · have heq : i = Fin.ofNat 136 112 := Fin.ext (by change i.val = 112; omega)
                subst i
                exact block_0112
              · have heq : i = Fin.ofNat 136 113 := Fin.ext (by change i.val = 113; omega)
                subst i
                exact block_0113
          · by_cases h_114_119 : i.val < 116
            · by_cases h_114_116 : i.val < 115
              · have heq : i = Fin.ofNat 136 114 := Fin.ext (by change i.val = 114; omega)
                subst i
                exact block_0114
              · have heq : i = Fin.ofNat 136 115 := Fin.ext (by change i.val = 115; omega)
                subst i
                exact block_0115
            · by_cases h_116_119 : i.val < 117
              · have heq : i = Fin.ofNat 136 116 := Fin.ext (by change i.val = 116; omega)
                subst i
                exact block_0116
              · by_cases h_117_119 : i.val < 118
                · have heq : i = Fin.ofNat 136 117 := Fin.ext (by change i.val = 117; omega)
                  subst i
                  exact block_0117
                · have heq : i = Fin.ofNat 136 118 := Fin.ext (by change i.val = 118; omega)
                  subst i
                  exact block_0118
      · by_cases h_119_136 : i.val < 127
        · by_cases h_119_127 : i.val < 123
          · by_cases h_119_123 : i.val < 121
            · by_cases h_119_121 : i.val < 120
              · have heq : i = Fin.ofNat 136 119 := Fin.ext (by change i.val = 119; omega)
                subst i
                exact block_0119
              · have heq : i = Fin.ofNat 136 120 := Fin.ext (by change i.val = 120; omega)
                subst i
                exact block_0120
            · by_cases h_121_123 : i.val < 122
              · have heq : i = Fin.ofNat 136 121 := Fin.ext (by change i.val = 121; omega)
                subst i
                exact block_0121
              · have heq : i = Fin.ofNat 136 122 := Fin.ext (by change i.val = 122; omega)
                subst i
                exact block_0122
          · by_cases h_123_127 : i.val < 125
            · by_cases h_123_125 : i.val < 124
              · have heq : i = Fin.ofNat 136 123 := Fin.ext (by change i.val = 123; omega)
                subst i
                exact block_0123
              · have heq : i = Fin.ofNat 136 124 := Fin.ext (by change i.val = 124; omega)
                subst i
                exact block_0124
            · by_cases h_125_127 : i.val < 126
              · have heq : i = Fin.ofNat 136 125 := Fin.ext (by change i.val = 125; omega)
                subst i
                exact block_0125
              · have heq : i = Fin.ofNat 136 126 := Fin.ext (by change i.val = 126; omega)
                subst i
                exact block_0126
        · by_cases h_127_136 : i.val < 131
          · by_cases h_127_131 : i.val < 129
            · by_cases h_127_129 : i.val < 128
              · have heq : i = Fin.ofNat 136 127 := Fin.ext (by change i.val = 127; omega)
                subst i
                exact block_0127
              · have heq : i = Fin.ofNat 136 128 := Fin.ext (by change i.val = 128; omega)
                subst i
                exact block_0128
            · by_cases h_129_131 : i.val < 130
              · have heq : i = Fin.ofNat 136 129 := Fin.ext (by change i.val = 129; omega)
                subst i
                exact block_0129
              · have heq : i = Fin.ofNat 136 130 := Fin.ext (by change i.val = 130; omega)
                subst i
                exact block_0130
          · by_cases h_131_136 : i.val < 133
            · by_cases h_131_133 : i.val < 132
              · have heq : i = Fin.ofNat 136 131 := Fin.ext (by change i.val = 131; omega)
                subst i
                exact block_0131
              · have heq : i = Fin.ofNat 136 132 := Fin.ext (by change i.val = 132; omega)
                subst i
                exact block_0132
            · by_cases h_133_136 : i.val < 134
              · have heq : i = Fin.ofNat 136 133 := Fin.ext (by change i.val = 133; omega)
                subst i
                exact block_0133
              · by_cases h_134_136 : i.val < 135
                · have heq : i = Fin.ofNat 136 134 := Fin.ext (by change i.val = 134; omega)
                  subst i
                  exact block_0134
                · have heq : i = Fin.ofNat 136 135 := Fin.ext (by change i.val = 135; omega)
                  subst i
                  exact block_0135
end Papers.RationalityTen.RootedCanonical.RootedSixBase01.T5
