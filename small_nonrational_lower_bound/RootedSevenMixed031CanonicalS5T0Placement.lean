module
prelude
public import RootedSevenMixed031CanonicalS5T0Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed031.S5T0
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 5 (raw i) template root
      FacetUniverses.RootedSevenMixed031.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 159 := i.isLt
  by_cases h_0_159 : i.val < 79
  · by_cases h_0_79 : i.val < 39
    · by_cases h_0_39 : i.val < 19
      · by_cases h_0_19 : i.val < 9
        · by_cases h_0_9 : i.val < 4
          · by_cases h_0_4 : i.val < 2
            · by_cases h_0_2 : i.val < 1
              · have heq : i = Fin.ofNat 159 0 := Fin.ext (by change i.val = 0; omega)
                subst i
                exact block_0000
              · have heq : i = Fin.ofNat 159 1 := Fin.ext (by change i.val = 1; omega)
                subst i
                exact block_0001
            · by_cases h_2_4 : i.val < 3
              · have heq : i = Fin.ofNat 159 2 := Fin.ext (by change i.val = 2; omega)
                subst i
                exact block_0002
              · have heq : i = Fin.ofNat 159 3 := Fin.ext (by change i.val = 3; omega)
                subst i
                exact block_0003
          · by_cases h_4_9 : i.val < 6
            · by_cases h_4_6 : i.val < 5
              · have heq : i = Fin.ofNat 159 4 := Fin.ext (by change i.val = 4; omega)
                subst i
                exact block_0004
              · have heq : i = Fin.ofNat 159 5 := Fin.ext (by change i.val = 5; omega)
                subst i
                exact block_0005
            · by_cases h_6_9 : i.val < 7
              · have heq : i = Fin.ofNat 159 6 := Fin.ext (by change i.val = 6; omega)
                subst i
                exact block_0006
              · by_cases h_7_9 : i.val < 8
                · have heq : i = Fin.ofNat 159 7 := Fin.ext (by change i.val = 7; omega)
                  subst i
                  exact block_0007
                · have heq : i = Fin.ofNat 159 8 := Fin.ext (by change i.val = 8; omega)
                  subst i
                  exact block_0008
        · by_cases h_9_19 : i.val < 14
          · by_cases h_9_14 : i.val < 11
            · by_cases h_9_11 : i.val < 10
              · have heq : i = Fin.ofNat 159 9 := Fin.ext (by change i.val = 9; omega)
                subst i
                exact block_0009
              · have heq : i = Fin.ofNat 159 10 := Fin.ext (by change i.val = 10; omega)
                subst i
                exact block_0010
            · by_cases h_11_14 : i.val < 12
              · have heq : i = Fin.ofNat 159 11 := Fin.ext (by change i.val = 11; omega)
                subst i
                exact block_0011
              · by_cases h_12_14 : i.val < 13
                · have heq : i = Fin.ofNat 159 12 := Fin.ext (by change i.val = 12; omega)
                  subst i
                  exact block_0012
                · have heq : i = Fin.ofNat 159 13 := Fin.ext (by change i.val = 13; omega)
                  subst i
                  exact block_0013
          · by_cases h_14_19 : i.val < 16
            · by_cases h_14_16 : i.val < 15
              · have heq : i = Fin.ofNat 159 14 := Fin.ext (by change i.val = 14; omega)
                subst i
                exact block_0014
              · have heq : i = Fin.ofNat 159 15 := Fin.ext (by change i.val = 15; omega)
                subst i
                exact block_0015
            · by_cases h_16_19 : i.val < 17
              · have heq : i = Fin.ofNat 159 16 := Fin.ext (by change i.val = 16; omega)
                subst i
                exact block_0016
              · by_cases h_17_19 : i.val < 18
                · have heq : i = Fin.ofNat 159 17 := Fin.ext (by change i.val = 17; omega)
                  subst i
                  exact block_0017
                · have heq : i = Fin.ofNat 159 18 := Fin.ext (by change i.val = 18; omega)
                  subst i
                  exact block_0018
      · by_cases h_19_39 : i.val < 29
        · by_cases h_19_29 : i.val < 24
          · by_cases h_19_24 : i.val < 21
            · by_cases h_19_21 : i.val < 20
              · have heq : i = Fin.ofNat 159 19 := Fin.ext (by change i.val = 19; omega)
                subst i
                exact block_0019
              · have heq : i = Fin.ofNat 159 20 := Fin.ext (by change i.val = 20; omega)
                subst i
                exact block_0020
            · by_cases h_21_24 : i.val < 22
              · have heq : i = Fin.ofNat 159 21 := Fin.ext (by change i.val = 21; omega)
                subst i
                exact block_0021
              · by_cases h_22_24 : i.val < 23
                · have heq : i = Fin.ofNat 159 22 := Fin.ext (by change i.val = 22; omega)
                  subst i
                  exact block_0022
                · have heq : i = Fin.ofNat 159 23 := Fin.ext (by change i.val = 23; omega)
                  subst i
                  exact block_0023
          · by_cases h_24_29 : i.val < 26
            · by_cases h_24_26 : i.val < 25
              · have heq : i = Fin.ofNat 159 24 := Fin.ext (by change i.val = 24; omega)
                subst i
                exact block_0024
              · have heq : i = Fin.ofNat 159 25 := Fin.ext (by change i.val = 25; omega)
                subst i
                exact block_0025
            · by_cases h_26_29 : i.val < 27
              · have heq : i = Fin.ofNat 159 26 := Fin.ext (by change i.val = 26; omega)
                subst i
                exact block_0026
              · by_cases h_27_29 : i.val < 28
                · have heq : i = Fin.ofNat 159 27 := Fin.ext (by change i.val = 27; omega)
                  subst i
                  exact block_0027
                · have heq : i = Fin.ofNat 159 28 := Fin.ext (by change i.val = 28; omega)
                  subst i
                  exact block_0028
        · by_cases h_29_39 : i.val < 34
          · by_cases h_29_34 : i.val < 31
            · by_cases h_29_31 : i.val < 30
              · have heq : i = Fin.ofNat 159 29 := Fin.ext (by change i.val = 29; omega)
                subst i
                exact block_0029
              · have heq : i = Fin.ofNat 159 30 := Fin.ext (by change i.val = 30; omega)
                subst i
                exact block_0030
            · by_cases h_31_34 : i.val < 32
              · have heq : i = Fin.ofNat 159 31 := Fin.ext (by change i.val = 31; omega)
                subst i
                exact block_0031
              · by_cases h_32_34 : i.val < 33
                · have heq : i = Fin.ofNat 159 32 := Fin.ext (by change i.val = 32; omega)
                  subst i
                  exact block_0032
                · have heq : i = Fin.ofNat 159 33 := Fin.ext (by change i.val = 33; omega)
                  subst i
                  exact block_0033
          · by_cases h_34_39 : i.val < 36
            · by_cases h_34_36 : i.val < 35
              · have heq : i = Fin.ofNat 159 34 := Fin.ext (by change i.val = 34; omega)
                subst i
                exact block_0034
              · have heq : i = Fin.ofNat 159 35 := Fin.ext (by change i.val = 35; omega)
                subst i
                exact block_0035
            · by_cases h_36_39 : i.val < 37
              · have heq : i = Fin.ofNat 159 36 := Fin.ext (by change i.val = 36; omega)
                subst i
                exact block_0036
              · by_cases h_37_39 : i.val < 38
                · have heq : i = Fin.ofNat 159 37 := Fin.ext (by change i.val = 37; omega)
                  subst i
                  exact block_0037
                · have heq : i = Fin.ofNat 159 38 := Fin.ext (by change i.val = 38; omega)
                  subst i
                  exact block_0038
    · by_cases h_39_79 : i.val < 59
      · by_cases h_39_59 : i.val < 49
        · by_cases h_39_49 : i.val < 44
          · by_cases h_39_44 : i.val < 41
            · by_cases h_39_41 : i.val < 40
              · have heq : i = Fin.ofNat 159 39 := Fin.ext (by change i.val = 39; omega)
                subst i
                exact block_0039
              · have heq : i = Fin.ofNat 159 40 := Fin.ext (by change i.val = 40; omega)
                subst i
                exact block_0040
            · by_cases h_41_44 : i.val < 42
              · have heq : i = Fin.ofNat 159 41 := Fin.ext (by change i.val = 41; omega)
                subst i
                exact block_0041
              · by_cases h_42_44 : i.val < 43
                · have heq : i = Fin.ofNat 159 42 := Fin.ext (by change i.val = 42; omega)
                  subst i
                  exact block_0042
                · have heq : i = Fin.ofNat 159 43 := Fin.ext (by change i.val = 43; omega)
                  subst i
                  exact block_0043
          · by_cases h_44_49 : i.val < 46
            · by_cases h_44_46 : i.val < 45
              · have heq : i = Fin.ofNat 159 44 := Fin.ext (by change i.val = 44; omega)
                subst i
                exact block_0044
              · have heq : i = Fin.ofNat 159 45 := Fin.ext (by change i.val = 45; omega)
                subst i
                exact block_0045
            · by_cases h_46_49 : i.val < 47
              · have heq : i = Fin.ofNat 159 46 := Fin.ext (by change i.val = 46; omega)
                subst i
                exact block_0046
              · by_cases h_47_49 : i.val < 48
                · have heq : i = Fin.ofNat 159 47 := Fin.ext (by change i.val = 47; omega)
                  subst i
                  exact block_0047
                · have heq : i = Fin.ofNat 159 48 := Fin.ext (by change i.val = 48; omega)
                  subst i
                  exact block_0048
        · by_cases h_49_59 : i.val < 54
          · by_cases h_49_54 : i.val < 51
            · by_cases h_49_51 : i.val < 50
              · have heq : i = Fin.ofNat 159 49 := Fin.ext (by change i.val = 49; omega)
                subst i
                exact block_0049
              · have heq : i = Fin.ofNat 159 50 := Fin.ext (by change i.val = 50; omega)
                subst i
                exact block_0050
            · by_cases h_51_54 : i.val < 52
              · have heq : i = Fin.ofNat 159 51 := Fin.ext (by change i.val = 51; omega)
                subst i
                exact block_0051
              · by_cases h_52_54 : i.val < 53
                · have heq : i = Fin.ofNat 159 52 := Fin.ext (by change i.val = 52; omega)
                  subst i
                  exact block_0052
                · have heq : i = Fin.ofNat 159 53 := Fin.ext (by change i.val = 53; omega)
                  subst i
                  exact block_0053
          · by_cases h_54_59 : i.val < 56
            · by_cases h_54_56 : i.val < 55
              · have heq : i = Fin.ofNat 159 54 := Fin.ext (by change i.val = 54; omega)
                subst i
                exact block_0054
              · have heq : i = Fin.ofNat 159 55 := Fin.ext (by change i.val = 55; omega)
                subst i
                exact block_0055
            · by_cases h_56_59 : i.val < 57
              · have heq : i = Fin.ofNat 159 56 := Fin.ext (by change i.val = 56; omega)
                subst i
                exact block_0056
              · by_cases h_57_59 : i.val < 58
                · have heq : i = Fin.ofNat 159 57 := Fin.ext (by change i.val = 57; omega)
                  subst i
                  exact block_0057
                · have heq : i = Fin.ofNat 159 58 := Fin.ext (by change i.val = 58; omega)
                  subst i
                  exact block_0058
      · by_cases h_59_79 : i.val < 69
        · by_cases h_59_69 : i.val < 64
          · by_cases h_59_64 : i.val < 61
            · by_cases h_59_61 : i.val < 60
              · have heq : i = Fin.ofNat 159 59 := Fin.ext (by change i.val = 59; omega)
                subst i
                exact block_0059
              · have heq : i = Fin.ofNat 159 60 := Fin.ext (by change i.val = 60; omega)
                subst i
                exact block_0060
            · by_cases h_61_64 : i.val < 62
              · have heq : i = Fin.ofNat 159 61 := Fin.ext (by change i.val = 61; omega)
                subst i
                exact block_0061
              · by_cases h_62_64 : i.val < 63
                · have heq : i = Fin.ofNat 159 62 := Fin.ext (by change i.val = 62; omega)
                  subst i
                  exact block_0062
                · have heq : i = Fin.ofNat 159 63 := Fin.ext (by change i.val = 63; omega)
                  subst i
                  exact block_0063
          · by_cases h_64_69 : i.val < 66
            · by_cases h_64_66 : i.val < 65
              · have heq : i = Fin.ofNat 159 64 := Fin.ext (by change i.val = 64; omega)
                subst i
                exact block_0064
              · have heq : i = Fin.ofNat 159 65 := Fin.ext (by change i.val = 65; omega)
                subst i
                exact block_0065
            · by_cases h_66_69 : i.val < 67
              · have heq : i = Fin.ofNat 159 66 := Fin.ext (by change i.val = 66; omega)
                subst i
                exact block_0066
              · by_cases h_67_69 : i.val < 68
                · have heq : i = Fin.ofNat 159 67 := Fin.ext (by change i.val = 67; omega)
                  subst i
                  exact block_0067
                · have heq : i = Fin.ofNat 159 68 := Fin.ext (by change i.val = 68; omega)
                  subst i
                  exact block_0068
        · by_cases h_69_79 : i.val < 74
          · by_cases h_69_74 : i.val < 71
            · by_cases h_69_71 : i.val < 70
              · have heq : i = Fin.ofNat 159 69 := Fin.ext (by change i.val = 69; omega)
                subst i
                exact block_0069
              · have heq : i = Fin.ofNat 159 70 := Fin.ext (by change i.val = 70; omega)
                subst i
                exact block_0070
            · by_cases h_71_74 : i.val < 72
              · have heq : i = Fin.ofNat 159 71 := Fin.ext (by change i.val = 71; omega)
                subst i
                exact block_0071
              · by_cases h_72_74 : i.val < 73
                · have heq : i = Fin.ofNat 159 72 := Fin.ext (by change i.val = 72; omega)
                  subst i
                  exact block_0072
                · have heq : i = Fin.ofNat 159 73 := Fin.ext (by change i.val = 73; omega)
                  subst i
                  exact block_0073
          · by_cases h_74_79 : i.val < 76
            · by_cases h_74_76 : i.val < 75
              · have heq : i = Fin.ofNat 159 74 := Fin.ext (by change i.val = 74; omega)
                subst i
                exact block_0074
              · have heq : i = Fin.ofNat 159 75 := Fin.ext (by change i.val = 75; omega)
                subst i
                exact block_0075
            · by_cases h_76_79 : i.val < 77
              · have heq : i = Fin.ofNat 159 76 := Fin.ext (by change i.val = 76; omega)
                subst i
                exact block_0076
              · by_cases h_77_79 : i.val < 78
                · have heq : i = Fin.ofNat 159 77 := Fin.ext (by change i.val = 77; omega)
                  subst i
                  exact block_0077
                · have heq : i = Fin.ofNat 159 78 := Fin.ext (by change i.val = 78; omega)
                  subst i
                  exact block_0078
  · by_cases h_79_159 : i.val < 119
    · by_cases h_79_119 : i.val < 99
      · by_cases h_79_99 : i.val < 89
        · by_cases h_79_89 : i.val < 84
          · by_cases h_79_84 : i.val < 81
            · by_cases h_79_81 : i.val < 80
              · have heq : i = Fin.ofNat 159 79 := Fin.ext (by change i.val = 79; omega)
                subst i
                exact block_0079
              · have heq : i = Fin.ofNat 159 80 := Fin.ext (by change i.val = 80; omega)
                subst i
                exact block_0080
            · by_cases h_81_84 : i.val < 82
              · have heq : i = Fin.ofNat 159 81 := Fin.ext (by change i.val = 81; omega)
                subst i
                exact block_0081
              · by_cases h_82_84 : i.val < 83
                · have heq : i = Fin.ofNat 159 82 := Fin.ext (by change i.val = 82; omega)
                  subst i
                  exact block_0082
                · have heq : i = Fin.ofNat 159 83 := Fin.ext (by change i.val = 83; omega)
                  subst i
                  exact block_0083
          · by_cases h_84_89 : i.val < 86
            · by_cases h_84_86 : i.val < 85
              · have heq : i = Fin.ofNat 159 84 := Fin.ext (by change i.val = 84; omega)
                subst i
                exact block_0084
              · have heq : i = Fin.ofNat 159 85 := Fin.ext (by change i.val = 85; omega)
                subst i
                exact block_0085
            · by_cases h_86_89 : i.val < 87
              · have heq : i = Fin.ofNat 159 86 := Fin.ext (by change i.val = 86; omega)
                subst i
                exact block_0086
              · by_cases h_87_89 : i.val < 88
                · have heq : i = Fin.ofNat 159 87 := Fin.ext (by change i.val = 87; omega)
                  subst i
                  exact block_0087
                · have heq : i = Fin.ofNat 159 88 := Fin.ext (by change i.val = 88; omega)
                  subst i
                  exact block_0088
        · by_cases h_89_99 : i.val < 94
          · by_cases h_89_94 : i.val < 91
            · by_cases h_89_91 : i.val < 90
              · have heq : i = Fin.ofNat 159 89 := Fin.ext (by change i.val = 89; omega)
                subst i
                exact block_0089
              · have heq : i = Fin.ofNat 159 90 := Fin.ext (by change i.val = 90; omega)
                subst i
                exact block_0090
            · by_cases h_91_94 : i.val < 92
              · have heq : i = Fin.ofNat 159 91 := Fin.ext (by change i.val = 91; omega)
                subst i
                exact block_0091
              · by_cases h_92_94 : i.val < 93
                · have heq : i = Fin.ofNat 159 92 := Fin.ext (by change i.val = 92; omega)
                  subst i
                  exact block_0092
                · have heq : i = Fin.ofNat 159 93 := Fin.ext (by change i.val = 93; omega)
                  subst i
                  exact block_0093
          · by_cases h_94_99 : i.val < 96
            · by_cases h_94_96 : i.val < 95
              · have heq : i = Fin.ofNat 159 94 := Fin.ext (by change i.val = 94; omega)
                subst i
                exact block_0094
              · have heq : i = Fin.ofNat 159 95 := Fin.ext (by change i.val = 95; omega)
                subst i
                exact block_0095
            · by_cases h_96_99 : i.val < 97
              · have heq : i = Fin.ofNat 159 96 := Fin.ext (by change i.val = 96; omega)
                subst i
                exact block_0096
              · by_cases h_97_99 : i.val < 98
                · have heq : i = Fin.ofNat 159 97 := Fin.ext (by change i.val = 97; omega)
                  subst i
                  exact block_0097
                · have heq : i = Fin.ofNat 159 98 := Fin.ext (by change i.val = 98; omega)
                  subst i
                  exact block_0098
      · by_cases h_99_119 : i.val < 109
        · by_cases h_99_109 : i.val < 104
          · by_cases h_99_104 : i.val < 101
            · by_cases h_99_101 : i.val < 100
              · have heq : i = Fin.ofNat 159 99 := Fin.ext (by change i.val = 99; omega)
                subst i
                exact block_0099
              · have heq : i = Fin.ofNat 159 100 := Fin.ext (by change i.val = 100; omega)
                subst i
                exact block_0100
            · by_cases h_101_104 : i.val < 102
              · have heq : i = Fin.ofNat 159 101 := Fin.ext (by change i.val = 101; omega)
                subst i
                exact block_0101
              · by_cases h_102_104 : i.val < 103
                · have heq : i = Fin.ofNat 159 102 := Fin.ext (by change i.val = 102; omega)
                  subst i
                  exact block_0102
                · have heq : i = Fin.ofNat 159 103 := Fin.ext (by change i.val = 103; omega)
                  subst i
                  exact block_0103
          · by_cases h_104_109 : i.val < 106
            · by_cases h_104_106 : i.val < 105
              · have heq : i = Fin.ofNat 159 104 := Fin.ext (by change i.val = 104; omega)
                subst i
                exact block_0104
              · have heq : i = Fin.ofNat 159 105 := Fin.ext (by change i.val = 105; omega)
                subst i
                exact block_0105
            · by_cases h_106_109 : i.val < 107
              · have heq : i = Fin.ofNat 159 106 := Fin.ext (by change i.val = 106; omega)
                subst i
                exact block_0106
              · by_cases h_107_109 : i.val < 108
                · have heq : i = Fin.ofNat 159 107 := Fin.ext (by change i.val = 107; omega)
                  subst i
                  exact block_0107
                · have heq : i = Fin.ofNat 159 108 := Fin.ext (by change i.val = 108; omega)
                  subst i
                  exact block_0108
        · by_cases h_109_119 : i.val < 114
          · by_cases h_109_114 : i.val < 111
            · by_cases h_109_111 : i.val < 110
              · have heq : i = Fin.ofNat 159 109 := Fin.ext (by change i.val = 109; omega)
                subst i
                exact block_0109
              · have heq : i = Fin.ofNat 159 110 := Fin.ext (by change i.val = 110; omega)
                subst i
                exact block_0110
            · by_cases h_111_114 : i.val < 112
              · have heq : i = Fin.ofNat 159 111 := Fin.ext (by change i.val = 111; omega)
                subst i
                exact block_0111
              · by_cases h_112_114 : i.val < 113
                · have heq : i = Fin.ofNat 159 112 := Fin.ext (by change i.val = 112; omega)
                  subst i
                  exact block_0112
                · have heq : i = Fin.ofNat 159 113 := Fin.ext (by change i.val = 113; omega)
                  subst i
                  exact block_0113
          · by_cases h_114_119 : i.val < 116
            · by_cases h_114_116 : i.val < 115
              · have heq : i = Fin.ofNat 159 114 := Fin.ext (by change i.val = 114; omega)
                subst i
                exact block_0114
              · have heq : i = Fin.ofNat 159 115 := Fin.ext (by change i.val = 115; omega)
                subst i
                exact block_0115
            · by_cases h_116_119 : i.val < 117
              · have heq : i = Fin.ofNat 159 116 := Fin.ext (by change i.val = 116; omega)
                subst i
                exact block_0116
              · by_cases h_117_119 : i.val < 118
                · have heq : i = Fin.ofNat 159 117 := Fin.ext (by change i.val = 117; omega)
                  subst i
                  exact block_0117
                · have heq : i = Fin.ofNat 159 118 := Fin.ext (by change i.val = 118; omega)
                  subst i
                  exact block_0118
    · by_cases h_119_159 : i.val < 139
      · by_cases h_119_139 : i.val < 129
        · by_cases h_119_129 : i.val < 124
          · by_cases h_119_124 : i.val < 121
            · by_cases h_119_121 : i.val < 120
              · have heq : i = Fin.ofNat 159 119 := Fin.ext (by change i.val = 119; omega)
                subst i
                exact block_0119
              · have heq : i = Fin.ofNat 159 120 := Fin.ext (by change i.val = 120; omega)
                subst i
                exact block_0120
            · by_cases h_121_124 : i.val < 122
              · have heq : i = Fin.ofNat 159 121 := Fin.ext (by change i.val = 121; omega)
                subst i
                exact block_0121
              · by_cases h_122_124 : i.val < 123
                · have heq : i = Fin.ofNat 159 122 := Fin.ext (by change i.val = 122; omega)
                  subst i
                  exact block_0122
                · have heq : i = Fin.ofNat 159 123 := Fin.ext (by change i.val = 123; omega)
                  subst i
                  exact block_0123
          · by_cases h_124_129 : i.val < 126
            · by_cases h_124_126 : i.val < 125
              · have heq : i = Fin.ofNat 159 124 := Fin.ext (by change i.val = 124; omega)
                subst i
                exact block_0124
              · have heq : i = Fin.ofNat 159 125 := Fin.ext (by change i.val = 125; omega)
                subst i
                exact block_0125
            · by_cases h_126_129 : i.val < 127
              · have heq : i = Fin.ofNat 159 126 := Fin.ext (by change i.val = 126; omega)
                subst i
                exact block_0126
              · by_cases h_127_129 : i.val < 128
                · have heq : i = Fin.ofNat 159 127 := Fin.ext (by change i.val = 127; omega)
                  subst i
                  exact block_0127
                · have heq : i = Fin.ofNat 159 128 := Fin.ext (by change i.val = 128; omega)
                  subst i
                  exact block_0128
        · by_cases h_129_139 : i.val < 134
          · by_cases h_129_134 : i.val < 131
            · by_cases h_129_131 : i.val < 130
              · have heq : i = Fin.ofNat 159 129 := Fin.ext (by change i.val = 129; omega)
                subst i
                exact block_0129
              · have heq : i = Fin.ofNat 159 130 := Fin.ext (by change i.val = 130; omega)
                subst i
                exact block_0130
            · by_cases h_131_134 : i.val < 132
              · have heq : i = Fin.ofNat 159 131 := Fin.ext (by change i.val = 131; omega)
                subst i
                exact block_0131
              · by_cases h_132_134 : i.val < 133
                · have heq : i = Fin.ofNat 159 132 := Fin.ext (by change i.val = 132; omega)
                  subst i
                  exact block_0132
                · have heq : i = Fin.ofNat 159 133 := Fin.ext (by change i.val = 133; omega)
                  subst i
                  exact block_0133
          · by_cases h_134_139 : i.val < 136
            · by_cases h_134_136 : i.val < 135
              · have heq : i = Fin.ofNat 159 134 := Fin.ext (by change i.val = 134; omega)
                subst i
                exact block_0134
              · have heq : i = Fin.ofNat 159 135 := Fin.ext (by change i.val = 135; omega)
                subst i
                exact block_0135
            · by_cases h_136_139 : i.val < 137
              · have heq : i = Fin.ofNat 159 136 := Fin.ext (by change i.val = 136; omega)
                subst i
                exact block_0136
              · by_cases h_137_139 : i.val < 138
                · have heq : i = Fin.ofNat 159 137 := Fin.ext (by change i.val = 137; omega)
                  subst i
                  exact block_0137
                · have heq : i = Fin.ofNat 159 138 := Fin.ext (by change i.val = 138; omega)
                  subst i
                  exact block_0138
      · by_cases h_139_159 : i.val < 149
        · by_cases h_139_149 : i.val < 144
          · by_cases h_139_144 : i.val < 141
            · by_cases h_139_141 : i.val < 140
              · have heq : i = Fin.ofNat 159 139 := Fin.ext (by change i.val = 139; omega)
                subst i
                exact block_0139
              · have heq : i = Fin.ofNat 159 140 := Fin.ext (by change i.val = 140; omega)
                subst i
                exact block_0140
            · by_cases h_141_144 : i.val < 142
              · have heq : i = Fin.ofNat 159 141 := Fin.ext (by change i.val = 141; omega)
                subst i
                exact block_0141
              · by_cases h_142_144 : i.val < 143
                · have heq : i = Fin.ofNat 159 142 := Fin.ext (by change i.val = 142; omega)
                  subst i
                  exact block_0142
                · have heq : i = Fin.ofNat 159 143 := Fin.ext (by change i.val = 143; omega)
                  subst i
                  exact block_0143
          · by_cases h_144_149 : i.val < 146
            · by_cases h_144_146 : i.val < 145
              · have heq : i = Fin.ofNat 159 144 := Fin.ext (by change i.val = 144; omega)
                subst i
                exact block_0144
              · have heq : i = Fin.ofNat 159 145 := Fin.ext (by change i.val = 145; omega)
                subst i
                exact block_0145
            · by_cases h_146_149 : i.val < 147
              · have heq : i = Fin.ofNat 159 146 := Fin.ext (by change i.val = 146; omega)
                subst i
                exact block_0146
              · by_cases h_147_149 : i.val < 148
                · have heq : i = Fin.ofNat 159 147 := Fin.ext (by change i.val = 147; omega)
                  subst i
                  exact block_0147
                · have heq : i = Fin.ofNat 159 148 := Fin.ext (by change i.val = 148; omega)
                  subst i
                  exact block_0148
        · by_cases h_149_159 : i.val < 154
          · by_cases h_149_154 : i.val < 151
            · by_cases h_149_151 : i.val < 150
              · have heq : i = Fin.ofNat 159 149 := Fin.ext (by change i.val = 149; omega)
                subst i
                exact block_0149
              · have heq : i = Fin.ofNat 159 150 := Fin.ext (by change i.val = 150; omega)
                subst i
                exact block_0150
            · by_cases h_151_154 : i.val < 152
              · have heq : i = Fin.ofNat 159 151 := Fin.ext (by change i.val = 151; omega)
                subst i
                exact block_0151
              · by_cases h_152_154 : i.val < 153
                · have heq : i = Fin.ofNat 159 152 := Fin.ext (by change i.val = 152; omega)
                  subst i
                  exact block_0152
                · have heq : i = Fin.ofNat 159 153 := Fin.ext (by change i.val = 153; omega)
                  subst i
                  exact block_0153
          · by_cases h_154_159 : i.val < 156
            · by_cases h_154_156 : i.val < 155
              · have heq : i = Fin.ofNat 159 154 := Fin.ext (by change i.val = 154; omega)
                subst i
                exact block_0154
              · have heq : i = Fin.ofNat 159 155 := Fin.ext (by change i.val = 155; omega)
                subst i
                exact block_0155
            · by_cases h_156_159 : i.val < 157
              · have heq : i = Fin.ofNat 159 156 := Fin.ext (by change i.val = 156; omega)
                subst i
                exact block_0156
              · by_cases h_157_159 : i.val < 158
                · have heq : i = Fin.ofNat 159 157 := Fin.ext (by change i.val = 157; omega)
                  subst i
                  exact block_0157
                · have heq : i = Fin.ofNat 159 158 := Fin.ext (by change i.val = 158; omega)
                  subst i
                  exact block_0158
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed031.S5T0
