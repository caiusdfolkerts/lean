module
prelude
public import RootedSixBase00CanonicalS5T0Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.S5T0
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 5 (raw i) template root
      FacetUniverses.RootedSixBase00.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 186 := i.isLt
  by_cases h_0_186 : i.val < 93
  · by_cases h_0_93 : i.val < 46
    · by_cases h_0_46 : i.val < 23
      · by_cases h_0_23 : i.val < 11
        · by_cases h_0_11 : i.val < 5
          · by_cases h_0_5 : i.val < 2
            · by_cases h_0_2 : i.val < 1
              · have heq : i = Fin.ofNat 186 0 := Fin.ext (by change i.val = 0; omega)
                subst i
                exact block_0000
              · have heq : i = Fin.ofNat 186 1 := Fin.ext (by change i.val = 1; omega)
                subst i
                exact block_0001
            · by_cases h_2_5 : i.val < 3
              · have heq : i = Fin.ofNat 186 2 := Fin.ext (by change i.val = 2; omega)
                subst i
                exact block_0002
              · by_cases h_3_5 : i.val < 4
                · have heq : i = Fin.ofNat 186 3 := Fin.ext (by change i.val = 3; omega)
                  subst i
                  exact block_0003
                · have heq : i = Fin.ofNat 186 4 := Fin.ext (by change i.val = 4; omega)
                  subst i
                  exact block_0004
          · by_cases h_5_11 : i.val < 8
            · by_cases h_5_8 : i.val < 6
              · have heq : i = Fin.ofNat 186 5 := Fin.ext (by change i.val = 5; omega)
                subst i
                exact block_0005
              · by_cases h_6_8 : i.val < 7
                · have heq : i = Fin.ofNat 186 6 := Fin.ext (by change i.val = 6; omega)
                  subst i
                  exact block_0006
                · have heq : i = Fin.ofNat 186 7 := Fin.ext (by change i.val = 7; omega)
                  subst i
                  exact block_0007
            · by_cases h_8_11 : i.val < 9
              · have heq : i = Fin.ofNat 186 8 := Fin.ext (by change i.val = 8; omega)
                subst i
                exact block_0008
              · by_cases h_9_11 : i.val < 10
                · have heq : i = Fin.ofNat 186 9 := Fin.ext (by change i.val = 9; omega)
                  subst i
                  exact block_0009
                · have heq : i = Fin.ofNat 186 10 := Fin.ext (by change i.val = 10; omega)
                  subst i
                  exact block_0010
        · by_cases h_11_23 : i.val < 17
          · by_cases h_11_17 : i.val < 14
            · by_cases h_11_14 : i.val < 12
              · have heq : i = Fin.ofNat 186 11 := Fin.ext (by change i.val = 11; omega)
                subst i
                exact block_0011
              · by_cases h_12_14 : i.val < 13
                · have heq : i = Fin.ofNat 186 12 := Fin.ext (by change i.val = 12; omega)
                  subst i
                  exact block_0012
                · have heq : i = Fin.ofNat 186 13 := Fin.ext (by change i.val = 13; omega)
                  subst i
                  exact block_0013
            · by_cases h_14_17 : i.val < 15
              · have heq : i = Fin.ofNat 186 14 := Fin.ext (by change i.val = 14; omega)
                subst i
                exact block_0014
              · by_cases h_15_17 : i.val < 16
                · have heq : i = Fin.ofNat 186 15 := Fin.ext (by change i.val = 15; omega)
                  subst i
                  exact block_0015
                · have heq : i = Fin.ofNat 186 16 := Fin.ext (by change i.val = 16; omega)
                  subst i
                  exact block_0016
          · by_cases h_17_23 : i.val < 20
            · by_cases h_17_20 : i.val < 18
              · have heq : i = Fin.ofNat 186 17 := Fin.ext (by change i.val = 17; omega)
                subst i
                exact block_0017
              · by_cases h_18_20 : i.val < 19
                · have heq : i = Fin.ofNat 186 18 := Fin.ext (by change i.val = 18; omega)
                  subst i
                  exact block_0018
                · have heq : i = Fin.ofNat 186 19 := Fin.ext (by change i.val = 19; omega)
                  subst i
                  exact block_0019
            · by_cases h_20_23 : i.val < 21
              · have heq : i = Fin.ofNat 186 20 := Fin.ext (by change i.val = 20; omega)
                subst i
                exact block_0020
              · by_cases h_21_23 : i.val < 22
                · have heq : i = Fin.ofNat 186 21 := Fin.ext (by change i.val = 21; omega)
                  subst i
                  exact block_0021
                · have heq : i = Fin.ofNat 186 22 := Fin.ext (by change i.val = 22; omega)
                  subst i
                  exact block_0022
      · by_cases h_23_46 : i.val < 34
        · by_cases h_23_34 : i.val < 28
          · by_cases h_23_28 : i.val < 25
            · by_cases h_23_25 : i.val < 24
              · have heq : i = Fin.ofNat 186 23 := Fin.ext (by change i.val = 23; omega)
                subst i
                exact block_0023
              · have heq : i = Fin.ofNat 186 24 := Fin.ext (by change i.val = 24; omega)
                subst i
                exact block_0024
            · by_cases h_25_28 : i.val < 26
              · have heq : i = Fin.ofNat 186 25 := Fin.ext (by change i.val = 25; omega)
                subst i
                exact block_0025
              · by_cases h_26_28 : i.val < 27
                · have heq : i = Fin.ofNat 186 26 := Fin.ext (by change i.val = 26; omega)
                  subst i
                  exact block_0026
                · have heq : i = Fin.ofNat 186 27 := Fin.ext (by change i.val = 27; omega)
                  subst i
                  exact block_0027
          · by_cases h_28_34 : i.val < 31
            · by_cases h_28_31 : i.val < 29
              · have heq : i = Fin.ofNat 186 28 := Fin.ext (by change i.val = 28; omega)
                subst i
                exact block_0028
              · by_cases h_29_31 : i.val < 30
                · have heq : i = Fin.ofNat 186 29 := Fin.ext (by change i.val = 29; omega)
                  subst i
                  exact block_0029
                · have heq : i = Fin.ofNat 186 30 := Fin.ext (by change i.val = 30; omega)
                  subst i
                  exact block_0030
            · by_cases h_31_34 : i.val < 32
              · have heq : i = Fin.ofNat 186 31 := Fin.ext (by change i.val = 31; omega)
                subst i
                exact block_0031
              · by_cases h_32_34 : i.val < 33
                · have heq : i = Fin.ofNat 186 32 := Fin.ext (by change i.val = 32; omega)
                  subst i
                  exact block_0032
                · have heq : i = Fin.ofNat 186 33 := Fin.ext (by change i.val = 33; omega)
                  subst i
                  exact block_0033
        · by_cases h_34_46 : i.val < 40
          · by_cases h_34_40 : i.val < 37
            · by_cases h_34_37 : i.val < 35
              · have heq : i = Fin.ofNat 186 34 := Fin.ext (by change i.val = 34; omega)
                subst i
                exact block_0034
              · by_cases h_35_37 : i.val < 36
                · have heq : i = Fin.ofNat 186 35 := Fin.ext (by change i.val = 35; omega)
                  subst i
                  exact block_0035
                · have heq : i = Fin.ofNat 186 36 := Fin.ext (by change i.val = 36; omega)
                  subst i
                  exact block_0036
            · by_cases h_37_40 : i.val < 38
              · have heq : i = Fin.ofNat 186 37 := Fin.ext (by change i.val = 37; omega)
                subst i
                exact block_0037
              · by_cases h_38_40 : i.val < 39
                · have heq : i = Fin.ofNat 186 38 := Fin.ext (by change i.val = 38; omega)
                  subst i
                  exact block_0038
                · have heq : i = Fin.ofNat 186 39 := Fin.ext (by change i.val = 39; omega)
                  subst i
                  exact block_0039
          · by_cases h_40_46 : i.val < 43
            · by_cases h_40_43 : i.val < 41
              · have heq : i = Fin.ofNat 186 40 := Fin.ext (by change i.val = 40; omega)
                subst i
                exact block_0040
              · by_cases h_41_43 : i.val < 42
                · have heq : i = Fin.ofNat 186 41 := Fin.ext (by change i.val = 41; omega)
                  subst i
                  exact block_0041
                · have heq : i = Fin.ofNat 186 42 := Fin.ext (by change i.val = 42; omega)
                  subst i
                  exact block_0042
            · by_cases h_43_46 : i.val < 44
              · have heq : i = Fin.ofNat 186 43 := Fin.ext (by change i.val = 43; omega)
                subst i
                exact block_0043
              · by_cases h_44_46 : i.val < 45
                · have heq : i = Fin.ofNat 186 44 := Fin.ext (by change i.val = 44; omega)
                  subst i
                  exact block_0044
                · have heq : i = Fin.ofNat 186 45 := Fin.ext (by change i.val = 45; omega)
                  subst i
                  exact block_0045
    · by_cases h_46_93 : i.val < 69
      · by_cases h_46_69 : i.val < 57
        · by_cases h_46_57 : i.val < 51
          · by_cases h_46_51 : i.val < 48
            · by_cases h_46_48 : i.val < 47
              · have heq : i = Fin.ofNat 186 46 := Fin.ext (by change i.val = 46; omega)
                subst i
                exact block_0046
              · have heq : i = Fin.ofNat 186 47 := Fin.ext (by change i.val = 47; omega)
                subst i
                exact block_0047
            · by_cases h_48_51 : i.val < 49
              · have heq : i = Fin.ofNat 186 48 := Fin.ext (by change i.val = 48; omega)
                subst i
                exact block_0048
              · by_cases h_49_51 : i.val < 50
                · have heq : i = Fin.ofNat 186 49 := Fin.ext (by change i.val = 49; omega)
                  subst i
                  exact block_0049
                · have heq : i = Fin.ofNat 186 50 := Fin.ext (by change i.val = 50; omega)
                  subst i
                  exact block_0050
          · by_cases h_51_57 : i.val < 54
            · by_cases h_51_54 : i.val < 52
              · have heq : i = Fin.ofNat 186 51 := Fin.ext (by change i.val = 51; omega)
                subst i
                exact block_0051
              · by_cases h_52_54 : i.val < 53
                · have heq : i = Fin.ofNat 186 52 := Fin.ext (by change i.val = 52; omega)
                  subst i
                  exact block_0052
                · have heq : i = Fin.ofNat 186 53 := Fin.ext (by change i.val = 53; omega)
                  subst i
                  exact block_0053
            · by_cases h_54_57 : i.val < 55
              · have heq : i = Fin.ofNat 186 54 := Fin.ext (by change i.val = 54; omega)
                subst i
                exact block_0054
              · by_cases h_55_57 : i.val < 56
                · have heq : i = Fin.ofNat 186 55 := Fin.ext (by change i.val = 55; omega)
                  subst i
                  exact block_0055
                · have heq : i = Fin.ofNat 186 56 := Fin.ext (by change i.val = 56; omega)
                  subst i
                  exact block_0056
        · by_cases h_57_69 : i.val < 63
          · by_cases h_57_63 : i.val < 60
            · by_cases h_57_60 : i.val < 58
              · have heq : i = Fin.ofNat 186 57 := Fin.ext (by change i.val = 57; omega)
                subst i
                exact block_0057
              · by_cases h_58_60 : i.val < 59
                · have heq : i = Fin.ofNat 186 58 := Fin.ext (by change i.val = 58; omega)
                  subst i
                  exact block_0058
                · have heq : i = Fin.ofNat 186 59 := Fin.ext (by change i.val = 59; omega)
                  subst i
                  exact block_0059
            · by_cases h_60_63 : i.val < 61
              · have heq : i = Fin.ofNat 186 60 := Fin.ext (by change i.val = 60; omega)
                subst i
                exact block_0060
              · by_cases h_61_63 : i.val < 62
                · have heq : i = Fin.ofNat 186 61 := Fin.ext (by change i.val = 61; omega)
                  subst i
                  exact block_0061
                · have heq : i = Fin.ofNat 186 62 := Fin.ext (by change i.val = 62; omega)
                  subst i
                  exact block_0062
          · by_cases h_63_69 : i.val < 66
            · by_cases h_63_66 : i.val < 64
              · have heq : i = Fin.ofNat 186 63 := Fin.ext (by change i.val = 63; omega)
                subst i
                exact block_0063
              · by_cases h_64_66 : i.val < 65
                · have heq : i = Fin.ofNat 186 64 := Fin.ext (by change i.val = 64; omega)
                  subst i
                  exact block_0064
                · have heq : i = Fin.ofNat 186 65 := Fin.ext (by change i.val = 65; omega)
                  subst i
                  exact block_0065
            · by_cases h_66_69 : i.val < 67
              · have heq : i = Fin.ofNat 186 66 := Fin.ext (by change i.val = 66; omega)
                subst i
                exact block_0066
              · by_cases h_67_69 : i.val < 68
                · have heq : i = Fin.ofNat 186 67 := Fin.ext (by change i.val = 67; omega)
                  subst i
                  exact block_0067
                · have heq : i = Fin.ofNat 186 68 := Fin.ext (by change i.val = 68; omega)
                  subst i
                  exact block_0068
      · by_cases h_69_93 : i.val < 81
        · by_cases h_69_81 : i.val < 75
          · by_cases h_69_75 : i.val < 72
            · by_cases h_69_72 : i.val < 70
              · have heq : i = Fin.ofNat 186 69 := Fin.ext (by change i.val = 69; omega)
                subst i
                exact block_0069
              · by_cases h_70_72 : i.val < 71
                · have heq : i = Fin.ofNat 186 70 := Fin.ext (by change i.val = 70; omega)
                  subst i
                  exact block_0070
                · have heq : i = Fin.ofNat 186 71 := Fin.ext (by change i.val = 71; omega)
                  subst i
                  exact block_0071
            · by_cases h_72_75 : i.val < 73
              · have heq : i = Fin.ofNat 186 72 := Fin.ext (by change i.val = 72; omega)
                subst i
                exact block_0072
              · by_cases h_73_75 : i.val < 74
                · have heq : i = Fin.ofNat 186 73 := Fin.ext (by change i.val = 73; omega)
                  subst i
                  exact block_0073
                · have heq : i = Fin.ofNat 186 74 := Fin.ext (by change i.val = 74; omega)
                  subst i
                  exact block_0074
          · by_cases h_75_81 : i.val < 78
            · by_cases h_75_78 : i.val < 76
              · have heq : i = Fin.ofNat 186 75 := Fin.ext (by change i.val = 75; omega)
                subst i
                exact block_0075
              · by_cases h_76_78 : i.val < 77
                · have heq : i = Fin.ofNat 186 76 := Fin.ext (by change i.val = 76; omega)
                  subst i
                  exact block_0076
                · have heq : i = Fin.ofNat 186 77 := Fin.ext (by change i.val = 77; omega)
                  subst i
                  exact block_0077
            · by_cases h_78_81 : i.val < 79
              · have heq : i = Fin.ofNat 186 78 := Fin.ext (by change i.val = 78; omega)
                subst i
                exact block_0078
              · by_cases h_79_81 : i.val < 80
                · have heq : i = Fin.ofNat 186 79 := Fin.ext (by change i.val = 79; omega)
                  subst i
                  exact block_0079
                · have heq : i = Fin.ofNat 186 80 := Fin.ext (by change i.val = 80; omega)
                  subst i
                  exact block_0080
        · by_cases h_81_93 : i.val < 87
          · by_cases h_81_87 : i.val < 84
            · by_cases h_81_84 : i.val < 82
              · have heq : i = Fin.ofNat 186 81 := Fin.ext (by change i.val = 81; omega)
                subst i
                exact block_0081
              · by_cases h_82_84 : i.val < 83
                · have heq : i = Fin.ofNat 186 82 := Fin.ext (by change i.val = 82; omega)
                  subst i
                  exact block_0082
                · have heq : i = Fin.ofNat 186 83 := Fin.ext (by change i.val = 83; omega)
                  subst i
                  exact block_0083
            · by_cases h_84_87 : i.val < 85
              · have heq : i = Fin.ofNat 186 84 := Fin.ext (by change i.val = 84; omega)
                subst i
                exact block_0084
              · by_cases h_85_87 : i.val < 86
                · have heq : i = Fin.ofNat 186 85 := Fin.ext (by change i.val = 85; omega)
                  subst i
                  exact block_0085
                · have heq : i = Fin.ofNat 186 86 := Fin.ext (by change i.val = 86; omega)
                  subst i
                  exact block_0086
          · by_cases h_87_93 : i.val < 90
            · by_cases h_87_90 : i.val < 88
              · have heq : i = Fin.ofNat 186 87 := Fin.ext (by change i.val = 87; omega)
                subst i
                exact block_0087
              · by_cases h_88_90 : i.val < 89
                · have heq : i = Fin.ofNat 186 88 := Fin.ext (by change i.val = 88; omega)
                  subst i
                  exact block_0088
                · have heq : i = Fin.ofNat 186 89 := Fin.ext (by change i.val = 89; omega)
                  subst i
                  exact block_0089
            · by_cases h_90_93 : i.val < 91
              · have heq : i = Fin.ofNat 186 90 := Fin.ext (by change i.val = 90; omega)
                subst i
                exact block_0090
              · by_cases h_91_93 : i.val < 92
                · have heq : i = Fin.ofNat 186 91 := Fin.ext (by change i.val = 91; omega)
                  subst i
                  exact block_0091
                · have heq : i = Fin.ofNat 186 92 := Fin.ext (by change i.val = 92; omega)
                  subst i
                  exact block_0092
  · by_cases h_93_186 : i.val < 139
    · by_cases h_93_139 : i.val < 116
      · by_cases h_93_116 : i.val < 104
        · by_cases h_93_104 : i.val < 98
          · by_cases h_93_98 : i.val < 95
            · by_cases h_93_95 : i.val < 94
              · have heq : i = Fin.ofNat 186 93 := Fin.ext (by change i.val = 93; omega)
                subst i
                exact block_0093
              · have heq : i = Fin.ofNat 186 94 := Fin.ext (by change i.val = 94; omega)
                subst i
                exact block_0094
            · by_cases h_95_98 : i.val < 96
              · have heq : i = Fin.ofNat 186 95 := Fin.ext (by change i.val = 95; omega)
                subst i
                exact block_0095
              · by_cases h_96_98 : i.val < 97
                · have heq : i = Fin.ofNat 186 96 := Fin.ext (by change i.val = 96; omega)
                  subst i
                  exact block_0096
                · have heq : i = Fin.ofNat 186 97 := Fin.ext (by change i.val = 97; omega)
                  subst i
                  exact block_0097
          · by_cases h_98_104 : i.val < 101
            · by_cases h_98_101 : i.val < 99
              · have heq : i = Fin.ofNat 186 98 := Fin.ext (by change i.val = 98; omega)
                subst i
                exact block_0098
              · by_cases h_99_101 : i.val < 100
                · have heq : i = Fin.ofNat 186 99 := Fin.ext (by change i.val = 99; omega)
                  subst i
                  exact block_0099
                · have heq : i = Fin.ofNat 186 100 := Fin.ext (by change i.val = 100; omega)
                  subst i
                  exact block_0100
            · by_cases h_101_104 : i.val < 102
              · have heq : i = Fin.ofNat 186 101 := Fin.ext (by change i.val = 101; omega)
                subst i
                exact block_0101
              · by_cases h_102_104 : i.val < 103
                · have heq : i = Fin.ofNat 186 102 := Fin.ext (by change i.val = 102; omega)
                  subst i
                  exact block_0102
                · have heq : i = Fin.ofNat 186 103 := Fin.ext (by change i.val = 103; omega)
                  subst i
                  exact block_0103
        · by_cases h_104_116 : i.val < 110
          · by_cases h_104_110 : i.val < 107
            · by_cases h_104_107 : i.val < 105
              · have heq : i = Fin.ofNat 186 104 := Fin.ext (by change i.val = 104; omega)
                subst i
                exact block_0104
              · by_cases h_105_107 : i.val < 106
                · have heq : i = Fin.ofNat 186 105 := Fin.ext (by change i.val = 105; omega)
                  subst i
                  exact block_0105
                · have heq : i = Fin.ofNat 186 106 := Fin.ext (by change i.val = 106; omega)
                  subst i
                  exact block_0106
            · by_cases h_107_110 : i.val < 108
              · have heq : i = Fin.ofNat 186 107 := Fin.ext (by change i.val = 107; omega)
                subst i
                exact block_0107
              · by_cases h_108_110 : i.val < 109
                · have heq : i = Fin.ofNat 186 108 := Fin.ext (by change i.val = 108; omega)
                  subst i
                  exact block_0108
                · have heq : i = Fin.ofNat 186 109 := Fin.ext (by change i.val = 109; omega)
                  subst i
                  exact block_0109
          · by_cases h_110_116 : i.val < 113
            · by_cases h_110_113 : i.val < 111
              · have heq : i = Fin.ofNat 186 110 := Fin.ext (by change i.val = 110; omega)
                subst i
                exact block_0110
              · by_cases h_111_113 : i.val < 112
                · have heq : i = Fin.ofNat 186 111 := Fin.ext (by change i.val = 111; omega)
                  subst i
                  exact block_0111
                · have heq : i = Fin.ofNat 186 112 := Fin.ext (by change i.val = 112; omega)
                  subst i
                  exact block_0112
            · by_cases h_113_116 : i.val < 114
              · have heq : i = Fin.ofNat 186 113 := Fin.ext (by change i.val = 113; omega)
                subst i
                exact block_0113
              · by_cases h_114_116 : i.val < 115
                · have heq : i = Fin.ofNat 186 114 := Fin.ext (by change i.val = 114; omega)
                  subst i
                  exact block_0114
                · have heq : i = Fin.ofNat 186 115 := Fin.ext (by change i.val = 115; omega)
                  subst i
                  exact block_0115
      · by_cases h_116_139 : i.val < 127
        · by_cases h_116_127 : i.val < 121
          · by_cases h_116_121 : i.val < 118
            · by_cases h_116_118 : i.val < 117
              · have heq : i = Fin.ofNat 186 116 := Fin.ext (by change i.val = 116; omega)
                subst i
                exact block_0116
              · have heq : i = Fin.ofNat 186 117 := Fin.ext (by change i.val = 117; omega)
                subst i
                exact block_0117
            · by_cases h_118_121 : i.val < 119
              · have heq : i = Fin.ofNat 186 118 := Fin.ext (by change i.val = 118; omega)
                subst i
                exact block_0118
              · by_cases h_119_121 : i.val < 120
                · have heq : i = Fin.ofNat 186 119 := Fin.ext (by change i.val = 119; omega)
                  subst i
                  exact block_0119
                · have heq : i = Fin.ofNat 186 120 := Fin.ext (by change i.val = 120; omega)
                  subst i
                  exact block_0120
          · by_cases h_121_127 : i.val < 124
            · by_cases h_121_124 : i.val < 122
              · have heq : i = Fin.ofNat 186 121 := Fin.ext (by change i.val = 121; omega)
                subst i
                exact block_0121
              · by_cases h_122_124 : i.val < 123
                · have heq : i = Fin.ofNat 186 122 := Fin.ext (by change i.val = 122; omega)
                  subst i
                  exact block_0122
                · have heq : i = Fin.ofNat 186 123 := Fin.ext (by change i.val = 123; omega)
                  subst i
                  exact block_0123
            · by_cases h_124_127 : i.val < 125
              · have heq : i = Fin.ofNat 186 124 := Fin.ext (by change i.val = 124; omega)
                subst i
                exact block_0124
              · by_cases h_125_127 : i.val < 126
                · have heq : i = Fin.ofNat 186 125 := Fin.ext (by change i.val = 125; omega)
                  subst i
                  exact block_0125
                · have heq : i = Fin.ofNat 186 126 := Fin.ext (by change i.val = 126; omega)
                  subst i
                  exact block_0126
        · by_cases h_127_139 : i.val < 133
          · by_cases h_127_133 : i.val < 130
            · by_cases h_127_130 : i.val < 128
              · have heq : i = Fin.ofNat 186 127 := Fin.ext (by change i.val = 127; omega)
                subst i
                exact block_0127
              · by_cases h_128_130 : i.val < 129
                · have heq : i = Fin.ofNat 186 128 := Fin.ext (by change i.val = 128; omega)
                  subst i
                  exact block_0128
                · have heq : i = Fin.ofNat 186 129 := Fin.ext (by change i.val = 129; omega)
                  subst i
                  exact block_0129
            · by_cases h_130_133 : i.val < 131
              · have heq : i = Fin.ofNat 186 130 := Fin.ext (by change i.val = 130; omega)
                subst i
                exact block_0130
              · by_cases h_131_133 : i.val < 132
                · have heq : i = Fin.ofNat 186 131 := Fin.ext (by change i.val = 131; omega)
                  subst i
                  exact block_0131
                · have heq : i = Fin.ofNat 186 132 := Fin.ext (by change i.val = 132; omega)
                  subst i
                  exact block_0132
          · by_cases h_133_139 : i.val < 136
            · by_cases h_133_136 : i.val < 134
              · have heq : i = Fin.ofNat 186 133 := Fin.ext (by change i.val = 133; omega)
                subst i
                exact block_0133
              · by_cases h_134_136 : i.val < 135
                · have heq : i = Fin.ofNat 186 134 := Fin.ext (by change i.val = 134; omega)
                  subst i
                  exact block_0134
                · have heq : i = Fin.ofNat 186 135 := Fin.ext (by change i.val = 135; omega)
                  subst i
                  exact block_0135
            · by_cases h_136_139 : i.val < 137
              · have heq : i = Fin.ofNat 186 136 := Fin.ext (by change i.val = 136; omega)
                subst i
                exact block_0136
              · by_cases h_137_139 : i.val < 138
                · have heq : i = Fin.ofNat 186 137 := Fin.ext (by change i.val = 137; omega)
                  subst i
                  exact block_0137
                · have heq : i = Fin.ofNat 186 138 := Fin.ext (by change i.val = 138; omega)
                  subst i
                  exact block_0138
    · by_cases h_139_186 : i.val < 162
      · by_cases h_139_162 : i.val < 150
        · by_cases h_139_150 : i.val < 144
          · by_cases h_139_144 : i.val < 141
            · by_cases h_139_141 : i.val < 140
              · have heq : i = Fin.ofNat 186 139 := Fin.ext (by change i.val = 139; omega)
                subst i
                exact block_0139
              · have heq : i = Fin.ofNat 186 140 := Fin.ext (by change i.val = 140; omega)
                subst i
                exact block_0140
            · by_cases h_141_144 : i.val < 142
              · have heq : i = Fin.ofNat 186 141 := Fin.ext (by change i.val = 141; omega)
                subst i
                exact block_0141
              · by_cases h_142_144 : i.val < 143
                · have heq : i = Fin.ofNat 186 142 := Fin.ext (by change i.val = 142; omega)
                  subst i
                  exact block_0142
                · have heq : i = Fin.ofNat 186 143 := Fin.ext (by change i.val = 143; omega)
                  subst i
                  exact block_0143
          · by_cases h_144_150 : i.val < 147
            · by_cases h_144_147 : i.val < 145
              · have heq : i = Fin.ofNat 186 144 := Fin.ext (by change i.val = 144; omega)
                subst i
                exact block_0144
              · by_cases h_145_147 : i.val < 146
                · have heq : i = Fin.ofNat 186 145 := Fin.ext (by change i.val = 145; omega)
                  subst i
                  exact block_0145
                · have heq : i = Fin.ofNat 186 146 := Fin.ext (by change i.val = 146; omega)
                  subst i
                  exact block_0146
            · by_cases h_147_150 : i.val < 148
              · have heq : i = Fin.ofNat 186 147 := Fin.ext (by change i.val = 147; omega)
                subst i
                exact block_0147
              · by_cases h_148_150 : i.val < 149
                · have heq : i = Fin.ofNat 186 148 := Fin.ext (by change i.val = 148; omega)
                  subst i
                  exact block_0148
                · have heq : i = Fin.ofNat 186 149 := Fin.ext (by change i.val = 149; omega)
                  subst i
                  exact block_0149
        · by_cases h_150_162 : i.val < 156
          · by_cases h_150_156 : i.val < 153
            · by_cases h_150_153 : i.val < 151
              · have heq : i = Fin.ofNat 186 150 := Fin.ext (by change i.val = 150; omega)
                subst i
                exact block_0150
              · by_cases h_151_153 : i.val < 152
                · have heq : i = Fin.ofNat 186 151 := Fin.ext (by change i.val = 151; omega)
                  subst i
                  exact block_0151
                · have heq : i = Fin.ofNat 186 152 := Fin.ext (by change i.val = 152; omega)
                  subst i
                  exact block_0152
            · by_cases h_153_156 : i.val < 154
              · have heq : i = Fin.ofNat 186 153 := Fin.ext (by change i.val = 153; omega)
                subst i
                exact block_0153
              · by_cases h_154_156 : i.val < 155
                · have heq : i = Fin.ofNat 186 154 := Fin.ext (by change i.val = 154; omega)
                  subst i
                  exact block_0154
                · have heq : i = Fin.ofNat 186 155 := Fin.ext (by change i.val = 155; omega)
                  subst i
                  exact block_0155
          · by_cases h_156_162 : i.val < 159
            · by_cases h_156_159 : i.val < 157
              · have heq : i = Fin.ofNat 186 156 := Fin.ext (by change i.val = 156; omega)
                subst i
                exact block_0156
              · by_cases h_157_159 : i.val < 158
                · have heq : i = Fin.ofNat 186 157 := Fin.ext (by change i.val = 157; omega)
                  subst i
                  exact block_0157
                · have heq : i = Fin.ofNat 186 158 := Fin.ext (by change i.val = 158; omega)
                  subst i
                  exact block_0158
            · by_cases h_159_162 : i.val < 160
              · have heq : i = Fin.ofNat 186 159 := Fin.ext (by change i.val = 159; omega)
                subst i
                exact block_0159
              · by_cases h_160_162 : i.val < 161
                · have heq : i = Fin.ofNat 186 160 := Fin.ext (by change i.val = 160; omega)
                  subst i
                  exact block_0160
                · have heq : i = Fin.ofNat 186 161 := Fin.ext (by change i.val = 161; omega)
                  subst i
                  exact block_0161
      · by_cases h_162_186 : i.val < 174
        · by_cases h_162_174 : i.val < 168
          · by_cases h_162_168 : i.val < 165
            · by_cases h_162_165 : i.val < 163
              · have heq : i = Fin.ofNat 186 162 := Fin.ext (by change i.val = 162; omega)
                subst i
                exact block_0162
              · by_cases h_163_165 : i.val < 164
                · have heq : i = Fin.ofNat 186 163 := Fin.ext (by change i.val = 163; omega)
                  subst i
                  exact block_0163
                · have heq : i = Fin.ofNat 186 164 := Fin.ext (by change i.val = 164; omega)
                  subst i
                  exact block_0164
            · by_cases h_165_168 : i.val < 166
              · have heq : i = Fin.ofNat 186 165 := Fin.ext (by change i.val = 165; omega)
                subst i
                exact block_0165
              · by_cases h_166_168 : i.val < 167
                · have heq : i = Fin.ofNat 186 166 := Fin.ext (by change i.val = 166; omega)
                  subst i
                  exact block_0166
                · have heq : i = Fin.ofNat 186 167 := Fin.ext (by change i.val = 167; omega)
                  subst i
                  exact block_0167
          · by_cases h_168_174 : i.val < 171
            · by_cases h_168_171 : i.val < 169
              · have heq : i = Fin.ofNat 186 168 := Fin.ext (by change i.val = 168; omega)
                subst i
                exact block_0168
              · by_cases h_169_171 : i.val < 170
                · have heq : i = Fin.ofNat 186 169 := Fin.ext (by change i.val = 169; omega)
                  subst i
                  exact block_0169
                · have heq : i = Fin.ofNat 186 170 := Fin.ext (by change i.val = 170; omega)
                  subst i
                  exact block_0170
            · by_cases h_171_174 : i.val < 172
              · have heq : i = Fin.ofNat 186 171 := Fin.ext (by change i.val = 171; omega)
                subst i
                exact block_0171
              · by_cases h_172_174 : i.val < 173
                · have heq : i = Fin.ofNat 186 172 := Fin.ext (by change i.val = 172; omega)
                  subst i
                  exact block_0172
                · have heq : i = Fin.ofNat 186 173 := Fin.ext (by change i.val = 173; omega)
                  subst i
                  exact block_0173
        · by_cases h_174_186 : i.val < 180
          · by_cases h_174_180 : i.val < 177
            · by_cases h_174_177 : i.val < 175
              · have heq : i = Fin.ofNat 186 174 := Fin.ext (by change i.val = 174; omega)
                subst i
                exact block_0174
              · by_cases h_175_177 : i.val < 176
                · have heq : i = Fin.ofNat 186 175 := Fin.ext (by change i.val = 175; omega)
                  subst i
                  exact block_0175
                · have heq : i = Fin.ofNat 186 176 := Fin.ext (by change i.val = 176; omega)
                  subst i
                  exact block_0176
            · by_cases h_177_180 : i.val < 178
              · have heq : i = Fin.ofNat 186 177 := Fin.ext (by change i.val = 177; omega)
                subst i
                exact block_0177
              · by_cases h_178_180 : i.val < 179
                · have heq : i = Fin.ofNat 186 178 := Fin.ext (by change i.val = 178; omega)
                  subst i
                  exact block_0178
                · have heq : i = Fin.ofNat 186 179 := Fin.ext (by change i.val = 179; omega)
                  subst i
                  exact block_0179
          · by_cases h_180_186 : i.val < 183
            · by_cases h_180_183 : i.val < 181
              · have heq : i = Fin.ofNat 186 180 := Fin.ext (by change i.val = 180; omega)
                subst i
                exact block_0180
              · by_cases h_181_183 : i.val < 182
                · have heq : i = Fin.ofNat 186 181 := Fin.ext (by change i.val = 181; omega)
                  subst i
                  exact block_0181
                · have heq : i = Fin.ofNat 186 182 := Fin.ext (by change i.val = 182; omega)
                  subst i
                  exact block_0182
            · by_cases h_183_186 : i.val < 184
              · have heq : i = Fin.ofNat 186 183 := Fin.ext (by change i.val = 183; omega)
                subst i
                exact block_0183
              · by_cases h_184_186 : i.val < 185
                · have heq : i = Fin.ofNat 186 184 := Fin.ext (by change i.val = 184; omega)
                  subst i
                  exact block_0184
                · have heq : i = Fin.ofNat 186 185 := Fin.ext (by change i.val = 185; omega)
                  subst i
                  exact block_0185
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.S5T0
