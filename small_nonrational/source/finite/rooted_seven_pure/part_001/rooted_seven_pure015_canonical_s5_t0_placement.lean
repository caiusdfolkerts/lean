module
prelude
public import RootedSevenPure015CanonicalS5T0Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenPure015.S5T0
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 5 (raw i) template root
      FacetUniverses.RootedSevenPure015.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 174 := i.isLt
  by_cases h_0_174 : i.val < 87
  · by_cases h_0_87 : i.val < 43
    · by_cases h_0_43 : i.val < 21
      · by_cases h_0_21 : i.val < 10
        · by_cases h_0_10 : i.val < 5
          · by_cases h_0_5 : i.val < 2
            · by_cases h_0_2 : i.val < 1
              · have heq : i = Fin.ofNat 174 0 := Fin.ext (by change i.val = 0; omega)
                subst i
                exact block_0000
              · have heq : i = Fin.ofNat 174 1 := Fin.ext (by change i.val = 1; omega)
                subst i
                exact block_0001
            · by_cases h_2_5 : i.val < 3
              · have heq : i = Fin.ofNat 174 2 := Fin.ext (by change i.val = 2; omega)
                subst i
                exact block_0002
              · by_cases h_3_5 : i.val < 4
                · have heq : i = Fin.ofNat 174 3 := Fin.ext (by change i.val = 3; omega)
                  subst i
                  exact block_0003
                · have heq : i = Fin.ofNat 174 4 := Fin.ext (by change i.val = 4; omega)
                  subst i
                  exact block_0004
          · by_cases h_5_10 : i.val < 7
            · by_cases h_5_7 : i.val < 6
              · have heq : i = Fin.ofNat 174 5 := Fin.ext (by change i.val = 5; omega)
                subst i
                exact block_0005
              · have heq : i = Fin.ofNat 174 6 := Fin.ext (by change i.val = 6; omega)
                subst i
                exact block_0006
            · by_cases h_7_10 : i.val < 8
              · have heq : i = Fin.ofNat 174 7 := Fin.ext (by change i.val = 7; omega)
                subst i
                exact block_0007
              · by_cases h_8_10 : i.val < 9
                · have heq : i = Fin.ofNat 174 8 := Fin.ext (by change i.val = 8; omega)
                  subst i
                  exact block_0008
                · have heq : i = Fin.ofNat 174 9 := Fin.ext (by change i.val = 9; omega)
                  subst i
                  exact block_0009
        · by_cases h_10_21 : i.val < 15
          · by_cases h_10_15 : i.val < 12
            · by_cases h_10_12 : i.val < 11
              · have heq : i = Fin.ofNat 174 10 := Fin.ext (by change i.val = 10; omega)
                subst i
                exact block_0010
              · have heq : i = Fin.ofNat 174 11 := Fin.ext (by change i.val = 11; omega)
                subst i
                exact block_0011
            · by_cases h_12_15 : i.val < 13
              · have heq : i = Fin.ofNat 174 12 := Fin.ext (by change i.val = 12; omega)
                subst i
                exact block_0012
              · by_cases h_13_15 : i.val < 14
                · have heq : i = Fin.ofNat 174 13 := Fin.ext (by change i.val = 13; omega)
                  subst i
                  exact block_0013
                · have heq : i = Fin.ofNat 174 14 := Fin.ext (by change i.val = 14; omega)
                  subst i
                  exact block_0014
          · by_cases h_15_21 : i.val < 18
            · by_cases h_15_18 : i.val < 16
              · have heq : i = Fin.ofNat 174 15 := Fin.ext (by change i.val = 15; omega)
                subst i
                exact block_0015
              · by_cases h_16_18 : i.val < 17
                · have heq : i = Fin.ofNat 174 16 := Fin.ext (by change i.val = 16; omega)
                  subst i
                  exact block_0016
                · have heq : i = Fin.ofNat 174 17 := Fin.ext (by change i.val = 17; omega)
                  subst i
                  exact block_0017
            · by_cases h_18_21 : i.val < 19
              · have heq : i = Fin.ofNat 174 18 := Fin.ext (by change i.val = 18; omega)
                subst i
                exact block_0018
              · by_cases h_19_21 : i.val < 20
                · have heq : i = Fin.ofNat 174 19 := Fin.ext (by change i.val = 19; omega)
                  subst i
                  exact block_0019
                · have heq : i = Fin.ofNat 174 20 := Fin.ext (by change i.val = 20; omega)
                  subst i
                  exact block_0020
      · by_cases h_21_43 : i.val < 32
        · by_cases h_21_32 : i.val < 26
          · by_cases h_21_26 : i.val < 23
            · by_cases h_21_23 : i.val < 22
              · have heq : i = Fin.ofNat 174 21 := Fin.ext (by change i.val = 21; omega)
                subst i
                exact block_0021
              · have heq : i = Fin.ofNat 174 22 := Fin.ext (by change i.val = 22; omega)
                subst i
                exact block_0022
            · by_cases h_23_26 : i.val < 24
              · have heq : i = Fin.ofNat 174 23 := Fin.ext (by change i.val = 23; omega)
                subst i
                exact block_0023
              · by_cases h_24_26 : i.val < 25
                · have heq : i = Fin.ofNat 174 24 := Fin.ext (by change i.val = 24; omega)
                  subst i
                  exact block_0024
                · have heq : i = Fin.ofNat 174 25 := Fin.ext (by change i.val = 25; omega)
                  subst i
                  exact block_0025
          · by_cases h_26_32 : i.val < 29
            · by_cases h_26_29 : i.val < 27
              · have heq : i = Fin.ofNat 174 26 := Fin.ext (by change i.val = 26; omega)
                subst i
                exact block_0026
              · by_cases h_27_29 : i.val < 28
                · have heq : i = Fin.ofNat 174 27 := Fin.ext (by change i.val = 27; omega)
                  subst i
                  exact block_0027
                · have heq : i = Fin.ofNat 174 28 := Fin.ext (by change i.val = 28; omega)
                  subst i
                  exact block_0028
            · by_cases h_29_32 : i.val < 30
              · have heq : i = Fin.ofNat 174 29 := Fin.ext (by change i.val = 29; omega)
                subst i
                exact block_0029
              · by_cases h_30_32 : i.val < 31
                · have heq : i = Fin.ofNat 174 30 := Fin.ext (by change i.val = 30; omega)
                  subst i
                  exact block_0030
                · have heq : i = Fin.ofNat 174 31 := Fin.ext (by change i.val = 31; omega)
                  subst i
                  exact block_0031
        · by_cases h_32_43 : i.val < 37
          · by_cases h_32_37 : i.val < 34
            · by_cases h_32_34 : i.val < 33
              · have heq : i = Fin.ofNat 174 32 := Fin.ext (by change i.val = 32; omega)
                subst i
                exact block_0032
              · have heq : i = Fin.ofNat 174 33 := Fin.ext (by change i.val = 33; omega)
                subst i
                exact block_0033
            · by_cases h_34_37 : i.val < 35
              · have heq : i = Fin.ofNat 174 34 := Fin.ext (by change i.val = 34; omega)
                subst i
                exact block_0034
              · by_cases h_35_37 : i.val < 36
                · have heq : i = Fin.ofNat 174 35 := Fin.ext (by change i.val = 35; omega)
                  subst i
                  exact block_0035
                · have heq : i = Fin.ofNat 174 36 := Fin.ext (by change i.val = 36; omega)
                  subst i
                  exact block_0036
          · by_cases h_37_43 : i.val < 40
            · by_cases h_37_40 : i.val < 38
              · have heq : i = Fin.ofNat 174 37 := Fin.ext (by change i.val = 37; omega)
                subst i
                exact block_0037
              · by_cases h_38_40 : i.val < 39
                · have heq : i = Fin.ofNat 174 38 := Fin.ext (by change i.val = 38; omega)
                  subst i
                  exact block_0038
                · have heq : i = Fin.ofNat 174 39 := Fin.ext (by change i.val = 39; omega)
                  subst i
                  exact block_0039
            · by_cases h_40_43 : i.val < 41
              · have heq : i = Fin.ofNat 174 40 := Fin.ext (by change i.val = 40; omega)
                subst i
                exact block_0040
              · by_cases h_41_43 : i.val < 42
                · have heq : i = Fin.ofNat 174 41 := Fin.ext (by change i.val = 41; omega)
                  subst i
                  exact block_0041
                · have heq : i = Fin.ofNat 174 42 := Fin.ext (by change i.val = 42; omega)
                  subst i
                  exact block_0042
    · by_cases h_43_87 : i.val < 65
      · by_cases h_43_65 : i.val < 54
        · by_cases h_43_54 : i.val < 48
          · by_cases h_43_48 : i.val < 45
            · by_cases h_43_45 : i.val < 44
              · have heq : i = Fin.ofNat 174 43 := Fin.ext (by change i.val = 43; omega)
                subst i
                exact block_0043
              · have heq : i = Fin.ofNat 174 44 := Fin.ext (by change i.val = 44; omega)
                subst i
                exact block_0044
            · by_cases h_45_48 : i.val < 46
              · have heq : i = Fin.ofNat 174 45 := Fin.ext (by change i.val = 45; omega)
                subst i
                exact block_0045
              · by_cases h_46_48 : i.val < 47
                · have heq : i = Fin.ofNat 174 46 := Fin.ext (by change i.val = 46; omega)
                  subst i
                  exact block_0046
                · have heq : i = Fin.ofNat 174 47 := Fin.ext (by change i.val = 47; omega)
                  subst i
                  exact block_0047
          · by_cases h_48_54 : i.val < 51
            · by_cases h_48_51 : i.val < 49
              · have heq : i = Fin.ofNat 174 48 := Fin.ext (by change i.val = 48; omega)
                subst i
                exact block_0048
              · by_cases h_49_51 : i.val < 50
                · have heq : i = Fin.ofNat 174 49 := Fin.ext (by change i.val = 49; omega)
                  subst i
                  exact block_0049
                · have heq : i = Fin.ofNat 174 50 := Fin.ext (by change i.val = 50; omega)
                  subst i
                  exact block_0050
            · by_cases h_51_54 : i.val < 52
              · have heq : i = Fin.ofNat 174 51 := Fin.ext (by change i.val = 51; omega)
                subst i
                exact block_0051
              · by_cases h_52_54 : i.val < 53
                · have heq : i = Fin.ofNat 174 52 := Fin.ext (by change i.val = 52; omega)
                  subst i
                  exact block_0052
                · have heq : i = Fin.ofNat 174 53 := Fin.ext (by change i.val = 53; omega)
                  subst i
                  exact block_0053
        · by_cases h_54_65 : i.val < 59
          · by_cases h_54_59 : i.val < 56
            · by_cases h_54_56 : i.val < 55
              · have heq : i = Fin.ofNat 174 54 := Fin.ext (by change i.val = 54; omega)
                subst i
                exact block_0054
              · have heq : i = Fin.ofNat 174 55 := Fin.ext (by change i.val = 55; omega)
                subst i
                exact block_0055
            · by_cases h_56_59 : i.val < 57
              · have heq : i = Fin.ofNat 174 56 := Fin.ext (by change i.val = 56; omega)
                subst i
                exact block_0056
              · by_cases h_57_59 : i.val < 58
                · have heq : i = Fin.ofNat 174 57 := Fin.ext (by change i.val = 57; omega)
                  subst i
                  exact block_0057
                · have heq : i = Fin.ofNat 174 58 := Fin.ext (by change i.val = 58; omega)
                  subst i
                  exact block_0058
          · by_cases h_59_65 : i.val < 62
            · by_cases h_59_62 : i.val < 60
              · have heq : i = Fin.ofNat 174 59 := Fin.ext (by change i.val = 59; omega)
                subst i
                exact block_0059
              · by_cases h_60_62 : i.val < 61
                · have heq : i = Fin.ofNat 174 60 := Fin.ext (by change i.val = 60; omega)
                  subst i
                  exact block_0060
                · have heq : i = Fin.ofNat 174 61 := Fin.ext (by change i.val = 61; omega)
                  subst i
                  exact block_0061
            · by_cases h_62_65 : i.val < 63
              · have heq : i = Fin.ofNat 174 62 := Fin.ext (by change i.val = 62; omega)
                subst i
                exact block_0062
              · by_cases h_63_65 : i.val < 64
                · have heq : i = Fin.ofNat 174 63 := Fin.ext (by change i.val = 63; omega)
                  subst i
                  exact block_0063
                · have heq : i = Fin.ofNat 174 64 := Fin.ext (by change i.val = 64; omega)
                  subst i
                  exact block_0064
      · by_cases h_65_87 : i.val < 76
        · by_cases h_65_76 : i.val < 70
          · by_cases h_65_70 : i.val < 67
            · by_cases h_65_67 : i.val < 66
              · have heq : i = Fin.ofNat 174 65 := Fin.ext (by change i.val = 65; omega)
                subst i
                exact block_0065
              · have heq : i = Fin.ofNat 174 66 := Fin.ext (by change i.val = 66; omega)
                subst i
                exact block_0066
            · by_cases h_67_70 : i.val < 68
              · have heq : i = Fin.ofNat 174 67 := Fin.ext (by change i.val = 67; omega)
                subst i
                exact block_0067
              · by_cases h_68_70 : i.val < 69
                · have heq : i = Fin.ofNat 174 68 := Fin.ext (by change i.val = 68; omega)
                  subst i
                  exact block_0068
                · have heq : i = Fin.ofNat 174 69 := Fin.ext (by change i.val = 69; omega)
                  subst i
                  exact block_0069
          · by_cases h_70_76 : i.val < 73
            · by_cases h_70_73 : i.val < 71
              · have heq : i = Fin.ofNat 174 70 := Fin.ext (by change i.val = 70; omega)
                subst i
                exact block_0070
              · by_cases h_71_73 : i.val < 72
                · have heq : i = Fin.ofNat 174 71 := Fin.ext (by change i.val = 71; omega)
                  subst i
                  exact block_0071
                · have heq : i = Fin.ofNat 174 72 := Fin.ext (by change i.val = 72; omega)
                  subst i
                  exact block_0072
            · by_cases h_73_76 : i.val < 74
              · have heq : i = Fin.ofNat 174 73 := Fin.ext (by change i.val = 73; omega)
                subst i
                exact block_0073
              · by_cases h_74_76 : i.val < 75
                · have heq : i = Fin.ofNat 174 74 := Fin.ext (by change i.val = 74; omega)
                  subst i
                  exact block_0074
                · have heq : i = Fin.ofNat 174 75 := Fin.ext (by change i.val = 75; omega)
                  subst i
                  exact block_0075
        · by_cases h_76_87 : i.val < 81
          · by_cases h_76_81 : i.val < 78
            · by_cases h_76_78 : i.val < 77
              · have heq : i = Fin.ofNat 174 76 := Fin.ext (by change i.val = 76; omega)
                subst i
                exact block_0076
              · have heq : i = Fin.ofNat 174 77 := Fin.ext (by change i.val = 77; omega)
                subst i
                exact block_0077
            · by_cases h_78_81 : i.val < 79
              · have heq : i = Fin.ofNat 174 78 := Fin.ext (by change i.val = 78; omega)
                subst i
                exact block_0078
              · by_cases h_79_81 : i.val < 80
                · have heq : i = Fin.ofNat 174 79 := Fin.ext (by change i.val = 79; omega)
                  subst i
                  exact block_0079
                · have heq : i = Fin.ofNat 174 80 := Fin.ext (by change i.val = 80; omega)
                  subst i
                  exact block_0080
          · by_cases h_81_87 : i.val < 84
            · by_cases h_81_84 : i.val < 82
              · have heq : i = Fin.ofNat 174 81 := Fin.ext (by change i.val = 81; omega)
                subst i
                exact block_0081
              · by_cases h_82_84 : i.val < 83
                · have heq : i = Fin.ofNat 174 82 := Fin.ext (by change i.val = 82; omega)
                  subst i
                  exact block_0082
                · have heq : i = Fin.ofNat 174 83 := Fin.ext (by change i.val = 83; omega)
                  subst i
                  exact block_0083
            · by_cases h_84_87 : i.val < 85
              · have heq : i = Fin.ofNat 174 84 := Fin.ext (by change i.val = 84; omega)
                subst i
                exact block_0084
              · by_cases h_85_87 : i.val < 86
                · have heq : i = Fin.ofNat 174 85 := Fin.ext (by change i.val = 85; omega)
                  subst i
                  exact block_0085
                · have heq : i = Fin.ofNat 174 86 := Fin.ext (by change i.val = 86; omega)
                  subst i
                  exact block_0086
  · by_cases h_87_174 : i.val < 130
    · by_cases h_87_130 : i.val < 108
      · by_cases h_87_108 : i.val < 97
        · by_cases h_87_97 : i.val < 92
          · by_cases h_87_92 : i.val < 89
            · by_cases h_87_89 : i.val < 88
              · have heq : i = Fin.ofNat 174 87 := Fin.ext (by change i.val = 87; omega)
                subst i
                exact block_0087
              · have heq : i = Fin.ofNat 174 88 := Fin.ext (by change i.val = 88; omega)
                subst i
                exact block_0088
            · by_cases h_89_92 : i.val < 90
              · have heq : i = Fin.ofNat 174 89 := Fin.ext (by change i.val = 89; omega)
                subst i
                exact block_0089
              · by_cases h_90_92 : i.val < 91
                · have heq : i = Fin.ofNat 174 90 := Fin.ext (by change i.val = 90; omega)
                  subst i
                  exact block_0090
                · have heq : i = Fin.ofNat 174 91 := Fin.ext (by change i.val = 91; omega)
                  subst i
                  exact block_0091
          · by_cases h_92_97 : i.val < 94
            · by_cases h_92_94 : i.val < 93
              · have heq : i = Fin.ofNat 174 92 := Fin.ext (by change i.val = 92; omega)
                subst i
                exact block_0092
              · have heq : i = Fin.ofNat 174 93 := Fin.ext (by change i.val = 93; omega)
                subst i
                exact block_0093
            · by_cases h_94_97 : i.val < 95
              · have heq : i = Fin.ofNat 174 94 := Fin.ext (by change i.val = 94; omega)
                subst i
                exact block_0094
              · by_cases h_95_97 : i.val < 96
                · have heq : i = Fin.ofNat 174 95 := Fin.ext (by change i.val = 95; omega)
                  subst i
                  exact block_0095
                · have heq : i = Fin.ofNat 174 96 := Fin.ext (by change i.val = 96; omega)
                  subst i
                  exact block_0096
        · by_cases h_97_108 : i.val < 102
          · by_cases h_97_102 : i.val < 99
            · by_cases h_97_99 : i.val < 98
              · have heq : i = Fin.ofNat 174 97 := Fin.ext (by change i.val = 97; omega)
                subst i
                exact block_0097
              · have heq : i = Fin.ofNat 174 98 := Fin.ext (by change i.val = 98; omega)
                subst i
                exact block_0098
            · by_cases h_99_102 : i.val < 100
              · have heq : i = Fin.ofNat 174 99 := Fin.ext (by change i.val = 99; omega)
                subst i
                exact block_0099
              · by_cases h_100_102 : i.val < 101
                · have heq : i = Fin.ofNat 174 100 := Fin.ext (by change i.val = 100; omega)
                  subst i
                  exact block_0100
                · have heq : i = Fin.ofNat 174 101 := Fin.ext (by change i.val = 101; omega)
                  subst i
                  exact block_0101
          · by_cases h_102_108 : i.val < 105
            · by_cases h_102_105 : i.val < 103
              · have heq : i = Fin.ofNat 174 102 := Fin.ext (by change i.val = 102; omega)
                subst i
                exact block_0102
              · by_cases h_103_105 : i.val < 104
                · have heq : i = Fin.ofNat 174 103 := Fin.ext (by change i.val = 103; omega)
                  subst i
                  exact block_0103
                · have heq : i = Fin.ofNat 174 104 := Fin.ext (by change i.val = 104; omega)
                  subst i
                  exact block_0104
            · by_cases h_105_108 : i.val < 106
              · have heq : i = Fin.ofNat 174 105 := Fin.ext (by change i.val = 105; omega)
                subst i
                exact block_0105
              · by_cases h_106_108 : i.val < 107
                · have heq : i = Fin.ofNat 174 106 := Fin.ext (by change i.val = 106; omega)
                  subst i
                  exact block_0106
                · have heq : i = Fin.ofNat 174 107 := Fin.ext (by change i.val = 107; omega)
                  subst i
                  exact block_0107
      · by_cases h_108_130 : i.val < 119
        · by_cases h_108_119 : i.val < 113
          · by_cases h_108_113 : i.val < 110
            · by_cases h_108_110 : i.val < 109
              · have heq : i = Fin.ofNat 174 108 := Fin.ext (by change i.val = 108; omega)
                subst i
                exact block_0108
              · have heq : i = Fin.ofNat 174 109 := Fin.ext (by change i.val = 109; omega)
                subst i
                exact block_0109
            · by_cases h_110_113 : i.val < 111
              · have heq : i = Fin.ofNat 174 110 := Fin.ext (by change i.val = 110; omega)
                subst i
                exact block_0110
              · by_cases h_111_113 : i.val < 112
                · have heq : i = Fin.ofNat 174 111 := Fin.ext (by change i.val = 111; omega)
                  subst i
                  exact block_0111
                · have heq : i = Fin.ofNat 174 112 := Fin.ext (by change i.val = 112; omega)
                  subst i
                  exact block_0112
          · by_cases h_113_119 : i.val < 116
            · by_cases h_113_116 : i.val < 114
              · have heq : i = Fin.ofNat 174 113 := Fin.ext (by change i.val = 113; omega)
                subst i
                exact block_0113
              · by_cases h_114_116 : i.val < 115
                · have heq : i = Fin.ofNat 174 114 := Fin.ext (by change i.val = 114; omega)
                  subst i
                  exact block_0114
                · have heq : i = Fin.ofNat 174 115 := Fin.ext (by change i.val = 115; omega)
                  subst i
                  exact block_0115
            · by_cases h_116_119 : i.val < 117
              · have heq : i = Fin.ofNat 174 116 := Fin.ext (by change i.val = 116; omega)
                subst i
                exact block_0116
              · by_cases h_117_119 : i.val < 118
                · have heq : i = Fin.ofNat 174 117 := Fin.ext (by change i.val = 117; omega)
                  subst i
                  exact block_0117
                · have heq : i = Fin.ofNat 174 118 := Fin.ext (by change i.val = 118; omega)
                  subst i
                  exact block_0118
        · by_cases h_119_130 : i.val < 124
          · by_cases h_119_124 : i.val < 121
            · by_cases h_119_121 : i.val < 120
              · have heq : i = Fin.ofNat 174 119 := Fin.ext (by change i.val = 119; omega)
                subst i
                exact block_0119
              · have heq : i = Fin.ofNat 174 120 := Fin.ext (by change i.val = 120; omega)
                subst i
                exact block_0120
            · by_cases h_121_124 : i.val < 122
              · have heq : i = Fin.ofNat 174 121 := Fin.ext (by change i.val = 121; omega)
                subst i
                exact block_0121
              · by_cases h_122_124 : i.val < 123
                · have heq : i = Fin.ofNat 174 122 := Fin.ext (by change i.val = 122; omega)
                  subst i
                  exact block_0122
                · have heq : i = Fin.ofNat 174 123 := Fin.ext (by change i.val = 123; omega)
                  subst i
                  exact block_0123
          · by_cases h_124_130 : i.val < 127
            · by_cases h_124_127 : i.val < 125
              · have heq : i = Fin.ofNat 174 124 := Fin.ext (by change i.val = 124; omega)
                subst i
                exact block_0124
              · by_cases h_125_127 : i.val < 126
                · have heq : i = Fin.ofNat 174 125 := Fin.ext (by change i.val = 125; omega)
                  subst i
                  exact block_0125
                · have heq : i = Fin.ofNat 174 126 := Fin.ext (by change i.val = 126; omega)
                  subst i
                  exact block_0126
            · by_cases h_127_130 : i.val < 128
              · have heq : i = Fin.ofNat 174 127 := Fin.ext (by change i.val = 127; omega)
                subst i
                exact block_0127
              · by_cases h_128_130 : i.val < 129
                · have heq : i = Fin.ofNat 174 128 := Fin.ext (by change i.val = 128; omega)
                  subst i
                  exact block_0128
                · have heq : i = Fin.ofNat 174 129 := Fin.ext (by change i.val = 129; omega)
                  subst i
                  exact block_0129
    · by_cases h_130_174 : i.val < 152
      · by_cases h_130_152 : i.val < 141
        · by_cases h_130_141 : i.val < 135
          · by_cases h_130_135 : i.val < 132
            · by_cases h_130_132 : i.val < 131
              · have heq : i = Fin.ofNat 174 130 := Fin.ext (by change i.val = 130; omega)
                subst i
                exact block_0130
              · have heq : i = Fin.ofNat 174 131 := Fin.ext (by change i.val = 131; omega)
                subst i
                exact block_0131
            · by_cases h_132_135 : i.val < 133
              · have heq : i = Fin.ofNat 174 132 := Fin.ext (by change i.val = 132; omega)
                subst i
                exact block_0132
              · by_cases h_133_135 : i.val < 134
                · have heq : i = Fin.ofNat 174 133 := Fin.ext (by change i.val = 133; omega)
                  subst i
                  exact block_0133
                · have heq : i = Fin.ofNat 174 134 := Fin.ext (by change i.val = 134; omega)
                  subst i
                  exact block_0134
          · by_cases h_135_141 : i.val < 138
            · by_cases h_135_138 : i.val < 136
              · have heq : i = Fin.ofNat 174 135 := Fin.ext (by change i.val = 135; omega)
                subst i
                exact block_0135
              · by_cases h_136_138 : i.val < 137
                · have heq : i = Fin.ofNat 174 136 := Fin.ext (by change i.val = 136; omega)
                  subst i
                  exact block_0136
                · have heq : i = Fin.ofNat 174 137 := Fin.ext (by change i.val = 137; omega)
                  subst i
                  exact block_0137
            · by_cases h_138_141 : i.val < 139
              · have heq : i = Fin.ofNat 174 138 := Fin.ext (by change i.val = 138; omega)
                subst i
                exact block_0138
              · by_cases h_139_141 : i.val < 140
                · have heq : i = Fin.ofNat 174 139 := Fin.ext (by change i.val = 139; omega)
                  subst i
                  exact block_0139
                · have heq : i = Fin.ofNat 174 140 := Fin.ext (by change i.val = 140; omega)
                  subst i
                  exact block_0140
        · by_cases h_141_152 : i.val < 146
          · by_cases h_141_146 : i.val < 143
            · by_cases h_141_143 : i.val < 142
              · have heq : i = Fin.ofNat 174 141 := Fin.ext (by change i.val = 141; omega)
                subst i
                exact block_0141
              · have heq : i = Fin.ofNat 174 142 := Fin.ext (by change i.val = 142; omega)
                subst i
                exact block_0142
            · by_cases h_143_146 : i.val < 144
              · have heq : i = Fin.ofNat 174 143 := Fin.ext (by change i.val = 143; omega)
                subst i
                exact block_0143
              · by_cases h_144_146 : i.val < 145
                · have heq : i = Fin.ofNat 174 144 := Fin.ext (by change i.val = 144; omega)
                  subst i
                  exact block_0144
                · have heq : i = Fin.ofNat 174 145 := Fin.ext (by change i.val = 145; omega)
                  subst i
                  exact block_0145
          · by_cases h_146_152 : i.val < 149
            · by_cases h_146_149 : i.val < 147
              · have heq : i = Fin.ofNat 174 146 := Fin.ext (by change i.val = 146; omega)
                subst i
                exact block_0146
              · by_cases h_147_149 : i.val < 148
                · have heq : i = Fin.ofNat 174 147 := Fin.ext (by change i.val = 147; omega)
                  subst i
                  exact block_0147
                · have heq : i = Fin.ofNat 174 148 := Fin.ext (by change i.val = 148; omega)
                  subst i
                  exact block_0148
            · by_cases h_149_152 : i.val < 150
              · have heq : i = Fin.ofNat 174 149 := Fin.ext (by change i.val = 149; omega)
                subst i
                exact block_0149
              · by_cases h_150_152 : i.val < 151
                · have heq : i = Fin.ofNat 174 150 := Fin.ext (by change i.val = 150; omega)
                  subst i
                  exact block_0150
                · have heq : i = Fin.ofNat 174 151 := Fin.ext (by change i.val = 151; omega)
                  subst i
                  exact block_0151
      · by_cases h_152_174 : i.val < 163
        · by_cases h_152_163 : i.val < 157
          · by_cases h_152_157 : i.val < 154
            · by_cases h_152_154 : i.val < 153
              · have heq : i = Fin.ofNat 174 152 := Fin.ext (by change i.val = 152; omega)
                subst i
                exact block_0152
              · have heq : i = Fin.ofNat 174 153 := Fin.ext (by change i.val = 153; omega)
                subst i
                exact block_0153
            · by_cases h_154_157 : i.val < 155
              · have heq : i = Fin.ofNat 174 154 := Fin.ext (by change i.val = 154; omega)
                subst i
                exact block_0154
              · by_cases h_155_157 : i.val < 156
                · have heq : i = Fin.ofNat 174 155 := Fin.ext (by change i.val = 155; omega)
                  subst i
                  exact block_0155
                · have heq : i = Fin.ofNat 174 156 := Fin.ext (by change i.val = 156; omega)
                  subst i
                  exact block_0156
          · by_cases h_157_163 : i.val < 160
            · by_cases h_157_160 : i.val < 158
              · have heq : i = Fin.ofNat 174 157 := Fin.ext (by change i.val = 157; omega)
                subst i
                exact block_0157
              · by_cases h_158_160 : i.val < 159
                · have heq : i = Fin.ofNat 174 158 := Fin.ext (by change i.val = 158; omega)
                  subst i
                  exact block_0158
                · have heq : i = Fin.ofNat 174 159 := Fin.ext (by change i.val = 159; omega)
                  subst i
                  exact block_0159
            · by_cases h_160_163 : i.val < 161
              · have heq : i = Fin.ofNat 174 160 := Fin.ext (by change i.val = 160; omega)
                subst i
                exact block_0160
              · by_cases h_161_163 : i.val < 162
                · have heq : i = Fin.ofNat 174 161 := Fin.ext (by change i.val = 161; omega)
                  subst i
                  exact block_0161
                · have heq : i = Fin.ofNat 174 162 := Fin.ext (by change i.val = 162; omega)
                  subst i
                  exact block_0162
        · by_cases h_163_174 : i.val < 168
          · by_cases h_163_168 : i.val < 165
            · by_cases h_163_165 : i.val < 164
              · have heq : i = Fin.ofNat 174 163 := Fin.ext (by change i.val = 163; omega)
                subst i
                exact block_0163
              · have heq : i = Fin.ofNat 174 164 := Fin.ext (by change i.val = 164; omega)
                subst i
                exact block_0164
            · by_cases h_165_168 : i.val < 166
              · have heq : i = Fin.ofNat 174 165 := Fin.ext (by change i.val = 165; omega)
                subst i
                exact block_0165
              · by_cases h_166_168 : i.val < 167
                · have heq : i = Fin.ofNat 174 166 := Fin.ext (by change i.val = 166; omega)
                  subst i
                  exact block_0166
                · have heq : i = Fin.ofNat 174 167 := Fin.ext (by change i.val = 167; omega)
                  subst i
                  exact block_0167
          · by_cases h_168_174 : i.val < 171
            · by_cases h_168_171 : i.val < 169
              · have heq : i = Fin.ofNat 174 168 := Fin.ext (by change i.val = 168; omega)
                subst i
                exact block_0168
              · by_cases h_169_171 : i.val < 170
                · have heq : i = Fin.ofNat 174 169 := Fin.ext (by change i.val = 169; omega)
                  subst i
                  exact block_0169
                · have heq : i = Fin.ofNat 174 170 := Fin.ext (by change i.val = 170; omega)
                  subst i
                  exact block_0170
            · by_cases h_171_174 : i.val < 172
              · have heq : i = Fin.ofNat 174 171 := Fin.ext (by change i.val = 171; omega)
                subst i
                exact block_0171
              · by_cases h_172_174 : i.val < 173
                · have heq : i = Fin.ofNat 174 172 := Fin.ext (by change i.val = 172; omega)
                  subst i
                  exact block_0172
                · have heq : i = Fin.ofNat 174 173 := Fin.ext (by change i.val = 173; omega)
                  subst i
                  exact block_0173
end Papers.RationalityTen.RootedCanonical.RootedSevenPure015.S5T0
