module
prelude
public import RootedSevenPure036CanonicalS4T0Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenPure036.S4T0
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 4 (raw i) template root
      FacetUniverses.RootedSevenPure036.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 144 := i.isLt
  by_cases h_0_144 : i.val < 72
  · by_cases h_0_72 : i.val < 36
    · by_cases h_0_36 : i.val < 18
      · by_cases h_0_18 : i.val < 9
        · by_cases h_0_9 : i.val < 4
          · by_cases h_0_4 : i.val < 2
            · by_cases h_0_2 : i.val < 1
              · have heq : i = Fin.ofNat 144 0 := Fin.ext (by change i.val = 0; omega)
                subst i
                exact block_0000
              · have heq : i = Fin.ofNat 144 1 := Fin.ext (by change i.val = 1; omega)
                subst i
                exact block_0001
            · by_cases h_2_4 : i.val < 3
              · have heq : i = Fin.ofNat 144 2 := Fin.ext (by change i.val = 2; omega)
                subst i
                exact block_0002
              · have heq : i = Fin.ofNat 144 3 := Fin.ext (by change i.val = 3; omega)
                subst i
                exact block_0003
          · by_cases h_4_9 : i.val < 6
            · by_cases h_4_6 : i.val < 5
              · have heq : i = Fin.ofNat 144 4 := Fin.ext (by change i.val = 4; omega)
                subst i
                exact block_0004
              · have heq : i = Fin.ofNat 144 5 := Fin.ext (by change i.val = 5; omega)
                subst i
                exact block_0005
            · by_cases h_6_9 : i.val < 7
              · have heq : i = Fin.ofNat 144 6 := Fin.ext (by change i.val = 6; omega)
                subst i
                exact block_0006
              · by_cases h_7_9 : i.val < 8
                · have heq : i = Fin.ofNat 144 7 := Fin.ext (by change i.val = 7; omega)
                  subst i
                  exact block_0007
                · have heq : i = Fin.ofNat 144 8 := Fin.ext (by change i.val = 8; omega)
                  subst i
                  exact block_0008
        · by_cases h_9_18 : i.val < 13
          · by_cases h_9_13 : i.val < 11
            · by_cases h_9_11 : i.val < 10
              · have heq : i = Fin.ofNat 144 9 := Fin.ext (by change i.val = 9; omega)
                subst i
                exact block_0009
              · have heq : i = Fin.ofNat 144 10 := Fin.ext (by change i.val = 10; omega)
                subst i
                exact block_0010
            · by_cases h_11_13 : i.val < 12
              · have heq : i = Fin.ofNat 144 11 := Fin.ext (by change i.val = 11; omega)
                subst i
                exact block_0011
              · have heq : i = Fin.ofNat 144 12 := Fin.ext (by change i.val = 12; omega)
                subst i
                exact block_0012
          · by_cases h_13_18 : i.val < 15
            · by_cases h_13_15 : i.val < 14
              · have heq : i = Fin.ofNat 144 13 := Fin.ext (by change i.val = 13; omega)
                subst i
                exact block_0013
              · have heq : i = Fin.ofNat 144 14 := Fin.ext (by change i.val = 14; omega)
                subst i
                exact block_0014
            · by_cases h_15_18 : i.val < 16
              · have heq : i = Fin.ofNat 144 15 := Fin.ext (by change i.val = 15; omega)
                subst i
                exact block_0015
              · by_cases h_16_18 : i.val < 17
                · have heq : i = Fin.ofNat 144 16 := Fin.ext (by change i.val = 16; omega)
                  subst i
                  exact block_0016
                · have heq : i = Fin.ofNat 144 17 := Fin.ext (by change i.val = 17; omega)
                  subst i
                  exact block_0017
      · by_cases h_18_36 : i.val < 27
        · by_cases h_18_27 : i.val < 22
          · by_cases h_18_22 : i.val < 20
            · by_cases h_18_20 : i.val < 19
              · have heq : i = Fin.ofNat 144 18 := Fin.ext (by change i.val = 18; omega)
                subst i
                exact block_0018
              · have heq : i = Fin.ofNat 144 19 := Fin.ext (by change i.val = 19; omega)
                subst i
                exact block_0019
            · by_cases h_20_22 : i.val < 21
              · have heq : i = Fin.ofNat 144 20 := Fin.ext (by change i.val = 20; omega)
                subst i
                exact block_0020
              · have heq : i = Fin.ofNat 144 21 := Fin.ext (by change i.val = 21; omega)
                subst i
                exact block_0021
          · by_cases h_22_27 : i.val < 24
            · by_cases h_22_24 : i.val < 23
              · have heq : i = Fin.ofNat 144 22 := Fin.ext (by change i.val = 22; omega)
                subst i
                exact block_0022
              · have heq : i = Fin.ofNat 144 23 := Fin.ext (by change i.val = 23; omega)
                subst i
                exact block_0023
            · by_cases h_24_27 : i.val < 25
              · have heq : i = Fin.ofNat 144 24 := Fin.ext (by change i.val = 24; omega)
                subst i
                exact block_0024
              · by_cases h_25_27 : i.val < 26
                · have heq : i = Fin.ofNat 144 25 := Fin.ext (by change i.val = 25; omega)
                  subst i
                  exact block_0025
                · have heq : i = Fin.ofNat 144 26 := Fin.ext (by change i.val = 26; omega)
                  subst i
                  exact block_0026
        · by_cases h_27_36 : i.val < 31
          · by_cases h_27_31 : i.val < 29
            · by_cases h_27_29 : i.val < 28
              · have heq : i = Fin.ofNat 144 27 := Fin.ext (by change i.val = 27; omega)
                subst i
                exact block_0027
              · have heq : i = Fin.ofNat 144 28 := Fin.ext (by change i.val = 28; omega)
                subst i
                exact block_0028
            · by_cases h_29_31 : i.val < 30
              · have heq : i = Fin.ofNat 144 29 := Fin.ext (by change i.val = 29; omega)
                subst i
                exact block_0029
              · have heq : i = Fin.ofNat 144 30 := Fin.ext (by change i.val = 30; omega)
                subst i
                exact block_0030
          · by_cases h_31_36 : i.val < 33
            · by_cases h_31_33 : i.val < 32
              · have heq : i = Fin.ofNat 144 31 := Fin.ext (by change i.val = 31; omega)
                subst i
                exact block_0031
              · have heq : i = Fin.ofNat 144 32 := Fin.ext (by change i.val = 32; omega)
                subst i
                exact block_0032
            · by_cases h_33_36 : i.val < 34
              · have heq : i = Fin.ofNat 144 33 := Fin.ext (by change i.val = 33; omega)
                subst i
                exact block_0033
              · by_cases h_34_36 : i.val < 35
                · have heq : i = Fin.ofNat 144 34 := Fin.ext (by change i.val = 34; omega)
                  subst i
                  exact block_0034
                · have heq : i = Fin.ofNat 144 35 := Fin.ext (by change i.val = 35; omega)
                  subst i
                  exact block_0035
    · by_cases h_36_72 : i.val < 54
      · by_cases h_36_54 : i.val < 45
        · by_cases h_36_45 : i.val < 40
          · by_cases h_36_40 : i.val < 38
            · by_cases h_36_38 : i.val < 37
              · have heq : i = Fin.ofNat 144 36 := Fin.ext (by change i.val = 36; omega)
                subst i
                exact block_0036
              · have heq : i = Fin.ofNat 144 37 := Fin.ext (by change i.val = 37; omega)
                subst i
                exact block_0037
            · by_cases h_38_40 : i.val < 39
              · have heq : i = Fin.ofNat 144 38 := Fin.ext (by change i.val = 38; omega)
                subst i
                exact block_0038
              · have heq : i = Fin.ofNat 144 39 := Fin.ext (by change i.val = 39; omega)
                subst i
                exact block_0039
          · by_cases h_40_45 : i.val < 42
            · by_cases h_40_42 : i.val < 41
              · have heq : i = Fin.ofNat 144 40 := Fin.ext (by change i.val = 40; omega)
                subst i
                exact block_0040
              · have heq : i = Fin.ofNat 144 41 := Fin.ext (by change i.val = 41; omega)
                subst i
                exact block_0041
            · by_cases h_42_45 : i.val < 43
              · have heq : i = Fin.ofNat 144 42 := Fin.ext (by change i.val = 42; omega)
                subst i
                exact block_0042
              · by_cases h_43_45 : i.val < 44
                · have heq : i = Fin.ofNat 144 43 := Fin.ext (by change i.val = 43; omega)
                  subst i
                  exact block_0043
                · have heq : i = Fin.ofNat 144 44 := Fin.ext (by change i.val = 44; omega)
                  subst i
                  exact block_0044
        · by_cases h_45_54 : i.val < 49
          · by_cases h_45_49 : i.val < 47
            · by_cases h_45_47 : i.val < 46
              · have heq : i = Fin.ofNat 144 45 := Fin.ext (by change i.val = 45; omega)
                subst i
                exact block_0045
              · have heq : i = Fin.ofNat 144 46 := Fin.ext (by change i.val = 46; omega)
                subst i
                exact block_0046
            · by_cases h_47_49 : i.val < 48
              · have heq : i = Fin.ofNat 144 47 := Fin.ext (by change i.val = 47; omega)
                subst i
                exact block_0047
              · have heq : i = Fin.ofNat 144 48 := Fin.ext (by change i.val = 48; omega)
                subst i
                exact block_0048
          · by_cases h_49_54 : i.val < 51
            · by_cases h_49_51 : i.val < 50
              · have heq : i = Fin.ofNat 144 49 := Fin.ext (by change i.val = 49; omega)
                subst i
                exact block_0049
              · have heq : i = Fin.ofNat 144 50 := Fin.ext (by change i.val = 50; omega)
                subst i
                exact block_0050
            · by_cases h_51_54 : i.val < 52
              · have heq : i = Fin.ofNat 144 51 := Fin.ext (by change i.val = 51; omega)
                subst i
                exact block_0051
              · by_cases h_52_54 : i.val < 53
                · have heq : i = Fin.ofNat 144 52 := Fin.ext (by change i.val = 52; omega)
                  subst i
                  exact block_0052
                · have heq : i = Fin.ofNat 144 53 := Fin.ext (by change i.val = 53; omega)
                  subst i
                  exact block_0053
      · by_cases h_54_72 : i.val < 63
        · by_cases h_54_63 : i.val < 58
          · by_cases h_54_58 : i.val < 56
            · by_cases h_54_56 : i.val < 55
              · have heq : i = Fin.ofNat 144 54 := Fin.ext (by change i.val = 54; omega)
                subst i
                exact block_0054
              · have heq : i = Fin.ofNat 144 55 := Fin.ext (by change i.val = 55; omega)
                subst i
                exact block_0055
            · by_cases h_56_58 : i.val < 57
              · have heq : i = Fin.ofNat 144 56 := Fin.ext (by change i.val = 56; omega)
                subst i
                exact block_0056
              · have heq : i = Fin.ofNat 144 57 := Fin.ext (by change i.val = 57; omega)
                subst i
                exact block_0057
          · by_cases h_58_63 : i.val < 60
            · by_cases h_58_60 : i.val < 59
              · have heq : i = Fin.ofNat 144 58 := Fin.ext (by change i.val = 58; omega)
                subst i
                exact block_0058
              · have heq : i = Fin.ofNat 144 59 := Fin.ext (by change i.val = 59; omega)
                subst i
                exact block_0059
            · by_cases h_60_63 : i.val < 61
              · have heq : i = Fin.ofNat 144 60 := Fin.ext (by change i.val = 60; omega)
                subst i
                exact block_0060
              · by_cases h_61_63 : i.val < 62
                · have heq : i = Fin.ofNat 144 61 := Fin.ext (by change i.val = 61; omega)
                  subst i
                  exact block_0061
                · have heq : i = Fin.ofNat 144 62 := Fin.ext (by change i.val = 62; omega)
                  subst i
                  exact block_0062
        · by_cases h_63_72 : i.val < 67
          · by_cases h_63_67 : i.val < 65
            · by_cases h_63_65 : i.val < 64
              · have heq : i = Fin.ofNat 144 63 := Fin.ext (by change i.val = 63; omega)
                subst i
                exact block_0063
              · have heq : i = Fin.ofNat 144 64 := Fin.ext (by change i.val = 64; omega)
                subst i
                exact block_0064
            · by_cases h_65_67 : i.val < 66
              · have heq : i = Fin.ofNat 144 65 := Fin.ext (by change i.val = 65; omega)
                subst i
                exact block_0065
              · have heq : i = Fin.ofNat 144 66 := Fin.ext (by change i.val = 66; omega)
                subst i
                exact block_0066
          · by_cases h_67_72 : i.val < 69
            · by_cases h_67_69 : i.val < 68
              · have heq : i = Fin.ofNat 144 67 := Fin.ext (by change i.val = 67; omega)
                subst i
                exact block_0067
              · have heq : i = Fin.ofNat 144 68 := Fin.ext (by change i.val = 68; omega)
                subst i
                exact block_0068
            · by_cases h_69_72 : i.val < 70
              · have heq : i = Fin.ofNat 144 69 := Fin.ext (by change i.val = 69; omega)
                subst i
                exact block_0069
              · by_cases h_70_72 : i.val < 71
                · have heq : i = Fin.ofNat 144 70 := Fin.ext (by change i.val = 70; omega)
                  subst i
                  exact block_0070
                · have heq : i = Fin.ofNat 144 71 := Fin.ext (by change i.val = 71; omega)
                  subst i
                  exact block_0071
  · by_cases h_72_144 : i.val < 108
    · by_cases h_72_108 : i.val < 90
      · by_cases h_72_90 : i.val < 81
        · by_cases h_72_81 : i.val < 76
          · by_cases h_72_76 : i.val < 74
            · by_cases h_72_74 : i.val < 73
              · have heq : i = Fin.ofNat 144 72 := Fin.ext (by change i.val = 72; omega)
                subst i
                exact block_0072
              · have heq : i = Fin.ofNat 144 73 := Fin.ext (by change i.val = 73; omega)
                subst i
                exact block_0073
            · by_cases h_74_76 : i.val < 75
              · have heq : i = Fin.ofNat 144 74 := Fin.ext (by change i.val = 74; omega)
                subst i
                exact block_0074
              · have heq : i = Fin.ofNat 144 75 := Fin.ext (by change i.val = 75; omega)
                subst i
                exact block_0075
          · by_cases h_76_81 : i.val < 78
            · by_cases h_76_78 : i.val < 77
              · have heq : i = Fin.ofNat 144 76 := Fin.ext (by change i.val = 76; omega)
                subst i
                exact block_0076
              · have heq : i = Fin.ofNat 144 77 := Fin.ext (by change i.val = 77; omega)
                subst i
                exact block_0077
            · by_cases h_78_81 : i.val < 79
              · have heq : i = Fin.ofNat 144 78 := Fin.ext (by change i.val = 78; omega)
                subst i
                exact block_0078
              · by_cases h_79_81 : i.val < 80
                · have heq : i = Fin.ofNat 144 79 := Fin.ext (by change i.val = 79; omega)
                  subst i
                  exact block_0079
                · have heq : i = Fin.ofNat 144 80 := Fin.ext (by change i.val = 80; omega)
                  subst i
                  exact block_0080
        · by_cases h_81_90 : i.val < 85
          · by_cases h_81_85 : i.val < 83
            · by_cases h_81_83 : i.val < 82
              · have heq : i = Fin.ofNat 144 81 := Fin.ext (by change i.val = 81; omega)
                subst i
                exact block_0081
              · have heq : i = Fin.ofNat 144 82 := Fin.ext (by change i.val = 82; omega)
                subst i
                exact block_0082
            · by_cases h_83_85 : i.val < 84
              · have heq : i = Fin.ofNat 144 83 := Fin.ext (by change i.val = 83; omega)
                subst i
                exact block_0083
              · have heq : i = Fin.ofNat 144 84 := Fin.ext (by change i.val = 84; omega)
                subst i
                exact block_0084
          · by_cases h_85_90 : i.val < 87
            · by_cases h_85_87 : i.val < 86
              · have heq : i = Fin.ofNat 144 85 := Fin.ext (by change i.val = 85; omega)
                subst i
                exact block_0085
              · have heq : i = Fin.ofNat 144 86 := Fin.ext (by change i.val = 86; omega)
                subst i
                exact block_0086
            · by_cases h_87_90 : i.val < 88
              · have heq : i = Fin.ofNat 144 87 := Fin.ext (by change i.val = 87; omega)
                subst i
                exact block_0087
              · by_cases h_88_90 : i.val < 89
                · have heq : i = Fin.ofNat 144 88 := Fin.ext (by change i.val = 88; omega)
                  subst i
                  exact block_0088
                · have heq : i = Fin.ofNat 144 89 := Fin.ext (by change i.val = 89; omega)
                  subst i
                  exact block_0089
      · by_cases h_90_108 : i.val < 99
        · by_cases h_90_99 : i.val < 94
          · by_cases h_90_94 : i.val < 92
            · by_cases h_90_92 : i.val < 91
              · have heq : i = Fin.ofNat 144 90 := Fin.ext (by change i.val = 90; omega)
                subst i
                exact block_0090
              · have heq : i = Fin.ofNat 144 91 := Fin.ext (by change i.val = 91; omega)
                subst i
                exact block_0091
            · by_cases h_92_94 : i.val < 93
              · have heq : i = Fin.ofNat 144 92 := Fin.ext (by change i.val = 92; omega)
                subst i
                exact block_0092
              · have heq : i = Fin.ofNat 144 93 := Fin.ext (by change i.val = 93; omega)
                subst i
                exact block_0093
          · by_cases h_94_99 : i.val < 96
            · by_cases h_94_96 : i.val < 95
              · have heq : i = Fin.ofNat 144 94 := Fin.ext (by change i.val = 94; omega)
                subst i
                exact block_0094
              · have heq : i = Fin.ofNat 144 95 := Fin.ext (by change i.val = 95; omega)
                subst i
                exact block_0095
            · by_cases h_96_99 : i.val < 97
              · have heq : i = Fin.ofNat 144 96 := Fin.ext (by change i.val = 96; omega)
                subst i
                exact block_0096
              · by_cases h_97_99 : i.val < 98
                · have heq : i = Fin.ofNat 144 97 := Fin.ext (by change i.val = 97; omega)
                  subst i
                  exact block_0097
                · have heq : i = Fin.ofNat 144 98 := Fin.ext (by change i.val = 98; omega)
                  subst i
                  exact block_0098
        · by_cases h_99_108 : i.val < 103
          · by_cases h_99_103 : i.val < 101
            · by_cases h_99_101 : i.val < 100
              · have heq : i = Fin.ofNat 144 99 := Fin.ext (by change i.val = 99; omega)
                subst i
                exact block_0099
              · have heq : i = Fin.ofNat 144 100 := Fin.ext (by change i.val = 100; omega)
                subst i
                exact block_0100
            · by_cases h_101_103 : i.val < 102
              · have heq : i = Fin.ofNat 144 101 := Fin.ext (by change i.val = 101; omega)
                subst i
                exact block_0101
              · have heq : i = Fin.ofNat 144 102 := Fin.ext (by change i.val = 102; omega)
                subst i
                exact block_0102
          · by_cases h_103_108 : i.val < 105
            · by_cases h_103_105 : i.val < 104
              · have heq : i = Fin.ofNat 144 103 := Fin.ext (by change i.val = 103; omega)
                subst i
                exact block_0103
              · have heq : i = Fin.ofNat 144 104 := Fin.ext (by change i.val = 104; omega)
                subst i
                exact block_0104
            · by_cases h_105_108 : i.val < 106
              · have heq : i = Fin.ofNat 144 105 := Fin.ext (by change i.val = 105; omega)
                subst i
                exact block_0105
              · by_cases h_106_108 : i.val < 107
                · have heq : i = Fin.ofNat 144 106 := Fin.ext (by change i.val = 106; omega)
                  subst i
                  exact block_0106
                · have heq : i = Fin.ofNat 144 107 := Fin.ext (by change i.val = 107; omega)
                  subst i
                  exact block_0107
    · by_cases h_108_144 : i.val < 126
      · by_cases h_108_126 : i.val < 117
        · by_cases h_108_117 : i.val < 112
          · by_cases h_108_112 : i.val < 110
            · by_cases h_108_110 : i.val < 109
              · have heq : i = Fin.ofNat 144 108 := Fin.ext (by change i.val = 108; omega)
                subst i
                exact block_0108
              · have heq : i = Fin.ofNat 144 109 := Fin.ext (by change i.val = 109; omega)
                subst i
                exact block_0109
            · by_cases h_110_112 : i.val < 111
              · have heq : i = Fin.ofNat 144 110 := Fin.ext (by change i.val = 110; omega)
                subst i
                exact block_0110
              · have heq : i = Fin.ofNat 144 111 := Fin.ext (by change i.val = 111; omega)
                subst i
                exact block_0111
          · by_cases h_112_117 : i.val < 114
            · by_cases h_112_114 : i.val < 113
              · have heq : i = Fin.ofNat 144 112 := Fin.ext (by change i.val = 112; omega)
                subst i
                exact block_0112
              · have heq : i = Fin.ofNat 144 113 := Fin.ext (by change i.val = 113; omega)
                subst i
                exact block_0113
            · by_cases h_114_117 : i.val < 115
              · have heq : i = Fin.ofNat 144 114 := Fin.ext (by change i.val = 114; omega)
                subst i
                exact block_0114
              · by_cases h_115_117 : i.val < 116
                · have heq : i = Fin.ofNat 144 115 := Fin.ext (by change i.val = 115; omega)
                  subst i
                  exact block_0115
                · have heq : i = Fin.ofNat 144 116 := Fin.ext (by change i.val = 116; omega)
                  subst i
                  exact block_0116
        · by_cases h_117_126 : i.val < 121
          · by_cases h_117_121 : i.val < 119
            · by_cases h_117_119 : i.val < 118
              · have heq : i = Fin.ofNat 144 117 := Fin.ext (by change i.val = 117; omega)
                subst i
                exact block_0117
              · have heq : i = Fin.ofNat 144 118 := Fin.ext (by change i.val = 118; omega)
                subst i
                exact block_0118
            · by_cases h_119_121 : i.val < 120
              · have heq : i = Fin.ofNat 144 119 := Fin.ext (by change i.val = 119; omega)
                subst i
                exact block_0119
              · have heq : i = Fin.ofNat 144 120 := Fin.ext (by change i.val = 120; omega)
                subst i
                exact block_0120
          · by_cases h_121_126 : i.val < 123
            · by_cases h_121_123 : i.val < 122
              · have heq : i = Fin.ofNat 144 121 := Fin.ext (by change i.val = 121; omega)
                subst i
                exact block_0121
              · have heq : i = Fin.ofNat 144 122 := Fin.ext (by change i.val = 122; omega)
                subst i
                exact block_0122
            · by_cases h_123_126 : i.val < 124
              · have heq : i = Fin.ofNat 144 123 := Fin.ext (by change i.val = 123; omega)
                subst i
                exact block_0123
              · by_cases h_124_126 : i.val < 125
                · have heq : i = Fin.ofNat 144 124 := Fin.ext (by change i.val = 124; omega)
                  subst i
                  exact block_0124
                · have heq : i = Fin.ofNat 144 125 := Fin.ext (by change i.val = 125; omega)
                  subst i
                  exact block_0125
      · by_cases h_126_144 : i.val < 135
        · by_cases h_126_135 : i.val < 130
          · by_cases h_126_130 : i.val < 128
            · by_cases h_126_128 : i.val < 127
              · have heq : i = Fin.ofNat 144 126 := Fin.ext (by change i.val = 126; omega)
                subst i
                exact block_0126
              · have heq : i = Fin.ofNat 144 127 := Fin.ext (by change i.val = 127; omega)
                subst i
                exact block_0127
            · by_cases h_128_130 : i.val < 129
              · have heq : i = Fin.ofNat 144 128 := Fin.ext (by change i.val = 128; omega)
                subst i
                exact block_0128
              · have heq : i = Fin.ofNat 144 129 := Fin.ext (by change i.val = 129; omega)
                subst i
                exact block_0129
          · by_cases h_130_135 : i.val < 132
            · by_cases h_130_132 : i.val < 131
              · have heq : i = Fin.ofNat 144 130 := Fin.ext (by change i.val = 130; omega)
                subst i
                exact block_0130
              · have heq : i = Fin.ofNat 144 131 := Fin.ext (by change i.val = 131; omega)
                subst i
                exact block_0131
            · by_cases h_132_135 : i.val < 133
              · have heq : i = Fin.ofNat 144 132 := Fin.ext (by change i.val = 132; omega)
                subst i
                exact block_0132
              · by_cases h_133_135 : i.val < 134
                · have heq : i = Fin.ofNat 144 133 := Fin.ext (by change i.val = 133; omega)
                  subst i
                  exact block_0133
                · have heq : i = Fin.ofNat 144 134 := Fin.ext (by change i.val = 134; omega)
                  subst i
                  exact block_0134
        · by_cases h_135_144 : i.val < 139
          · by_cases h_135_139 : i.val < 137
            · by_cases h_135_137 : i.val < 136
              · have heq : i = Fin.ofNat 144 135 := Fin.ext (by change i.val = 135; omega)
                subst i
                exact block_0135
              · have heq : i = Fin.ofNat 144 136 := Fin.ext (by change i.val = 136; omega)
                subst i
                exact block_0136
            · by_cases h_137_139 : i.val < 138
              · have heq : i = Fin.ofNat 144 137 := Fin.ext (by change i.val = 137; omega)
                subst i
                exact block_0137
              · have heq : i = Fin.ofNat 144 138 := Fin.ext (by change i.val = 138; omega)
                subst i
                exact block_0138
          · by_cases h_139_144 : i.val < 141
            · by_cases h_139_141 : i.val < 140
              · have heq : i = Fin.ofNat 144 139 := Fin.ext (by change i.val = 139; omega)
                subst i
                exact block_0139
              · have heq : i = Fin.ofNat 144 140 := Fin.ext (by change i.val = 140; omega)
                subst i
                exact block_0140
            · by_cases h_141_144 : i.val < 142
              · have heq : i = Fin.ofNat 144 141 := Fin.ext (by change i.val = 141; omega)
                subst i
                exact block_0141
              · by_cases h_142_144 : i.val < 143
                · have heq : i = Fin.ofNat 144 142 := Fin.ext (by change i.val = 142; omega)
                  subst i
                  exact block_0142
                · have heq : i = Fin.ofNat 144 143 := Fin.ext (by change i.val = 143; omega)
                  subst i
                  exact block_0143
end Papers.RationalityTen.RootedCanonical.RootedSevenPure036.S4T0
