module
prelude
public import RootedSixBase00CanonicalT1Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase00.T1
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 6 (raw i) template root
      FacetUniverses.RootedSixBase00.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 180 := i.isLt
  by_cases h_0_180 : i.val < 90
  · by_cases h_0_90 : i.val < 45
    · by_cases h_0_45 : i.val < 22
      · by_cases h_0_22 : i.val < 11
        · by_cases h_0_11 : i.val < 5
          · by_cases h_0_5 : i.val < 2
            · by_cases h_0_2 : i.val < 1
              · have heq : i = Fin.ofNat 180 0 := Fin.ext (by change i.val = 0; omega)
                subst i
                exact block_0000
              · have heq : i = Fin.ofNat 180 1 := Fin.ext (by change i.val = 1; omega)
                subst i
                exact block_0001
            · by_cases h_2_5 : i.val < 3
              · have heq : i = Fin.ofNat 180 2 := Fin.ext (by change i.val = 2; omega)
                subst i
                exact block_0002
              · by_cases h_3_5 : i.val < 4
                · have heq : i = Fin.ofNat 180 3 := Fin.ext (by change i.val = 3; omega)
                  subst i
                  exact block_0003
                · have heq : i = Fin.ofNat 180 4 := Fin.ext (by change i.val = 4; omega)
                  subst i
                  exact block_0004
          · by_cases h_5_11 : i.val < 8
            · by_cases h_5_8 : i.val < 6
              · have heq : i = Fin.ofNat 180 5 := Fin.ext (by change i.val = 5; omega)
                subst i
                exact block_0005
              · by_cases h_6_8 : i.val < 7
                · have heq : i = Fin.ofNat 180 6 := Fin.ext (by change i.val = 6; omega)
                  subst i
                  exact block_0006
                · have heq : i = Fin.ofNat 180 7 := Fin.ext (by change i.val = 7; omega)
                  subst i
                  exact block_0007
            · by_cases h_8_11 : i.val < 9
              · have heq : i = Fin.ofNat 180 8 := Fin.ext (by change i.val = 8; omega)
                subst i
                exact block_0008
              · by_cases h_9_11 : i.val < 10
                · have heq : i = Fin.ofNat 180 9 := Fin.ext (by change i.val = 9; omega)
                  subst i
                  exact block_0009
                · have heq : i = Fin.ofNat 180 10 := Fin.ext (by change i.val = 10; omega)
                  subst i
                  exact block_0010
        · by_cases h_11_22 : i.val < 16
          · by_cases h_11_16 : i.val < 13
            · by_cases h_11_13 : i.val < 12
              · have heq : i = Fin.ofNat 180 11 := Fin.ext (by change i.val = 11; omega)
                subst i
                exact block_0011
              · have heq : i = Fin.ofNat 180 12 := Fin.ext (by change i.val = 12; omega)
                subst i
                exact block_0012
            · by_cases h_13_16 : i.val < 14
              · have heq : i = Fin.ofNat 180 13 := Fin.ext (by change i.val = 13; omega)
                subst i
                exact block_0013
              · by_cases h_14_16 : i.val < 15
                · have heq : i = Fin.ofNat 180 14 := Fin.ext (by change i.val = 14; omega)
                  subst i
                  exact block_0014
                · have heq : i = Fin.ofNat 180 15 := Fin.ext (by change i.val = 15; omega)
                  subst i
                  exact block_0015
          · by_cases h_16_22 : i.val < 19
            · by_cases h_16_19 : i.val < 17
              · have heq : i = Fin.ofNat 180 16 := Fin.ext (by change i.val = 16; omega)
                subst i
                exact block_0016
              · by_cases h_17_19 : i.val < 18
                · have heq : i = Fin.ofNat 180 17 := Fin.ext (by change i.val = 17; omega)
                  subst i
                  exact block_0017
                · have heq : i = Fin.ofNat 180 18 := Fin.ext (by change i.val = 18; omega)
                  subst i
                  exact block_0018
            · by_cases h_19_22 : i.val < 20
              · have heq : i = Fin.ofNat 180 19 := Fin.ext (by change i.val = 19; omega)
                subst i
                exact block_0019
              · by_cases h_20_22 : i.val < 21
                · have heq : i = Fin.ofNat 180 20 := Fin.ext (by change i.val = 20; omega)
                  subst i
                  exact block_0020
                · have heq : i = Fin.ofNat 180 21 := Fin.ext (by change i.val = 21; omega)
                  subst i
                  exact block_0021
      · by_cases h_22_45 : i.val < 33
        · by_cases h_22_33 : i.val < 27
          · by_cases h_22_27 : i.val < 24
            · by_cases h_22_24 : i.val < 23
              · have heq : i = Fin.ofNat 180 22 := Fin.ext (by change i.val = 22; omega)
                subst i
                exact block_0022
              · have heq : i = Fin.ofNat 180 23 := Fin.ext (by change i.val = 23; omega)
                subst i
                exact block_0023
            · by_cases h_24_27 : i.val < 25
              · have heq : i = Fin.ofNat 180 24 := Fin.ext (by change i.val = 24; omega)
                subst i
                exact block_0024
              · by_cases h_25_27 : i.val < 26
                · have heq : i = Fin.ofNat 180 25 := Fin.ext (by change i.val = 25; omega)
                  subst i
                  exact block_0025
                · have heq : i = Fin.ofNat 180 26 := Fin.ext (by change i.val = 26; omega)
                  subst i
                  exact block_0026
          · by_cases h_27_33 : i.val < 30
            · by_cases h_27_30 : i.val < 28
              · have heq : i = Fin.ofNat 180 27 := Fin.ext (by change i.val = 27; omega)
                subst i
                exact block_0027
              · by_cases h_28_30 : i.val < 29
                · have heq : i = Fin.ofNat 180 28 := Fin.ext (by change i.val = 28; omega)
                  subst i
                  exact block_0028
                · have heq : i = Fin.ofNat 180 29 := Fin.ext (by change i.val = 29; omega)
                  subst i
                  exact block_0029
            · by_cases h_30_33 : i.val < 31
              · have heq : i = Fin.ofNat 180 30 := Fin.ext (by change i.val = 30; omega)
                subst i
                exact block_0030
              · by_cases h_31_33 : i.val < 32
                · have heq : i = Fin.ofNat 180 31 := Fin.ext (by change i.val = 31; omega)
                  subst i
                  exact block_0031
                · have heq : i = Fin.ofNat 180 32 := Fin.ext (by change i.val = 32; omega)
                  subst i
                  exact block_0032
        · by_cases h_33_45 : i.val < 39
          · by_cases h_33_39 : i.val < 36
            · by_cases h_33_36 : i.val < 34
              · have heq : i = Fin.ofNat 180 33 := Fin.ext (by change i.val = 33; omega)
                subst i
                exact block_0033
              · by_cases h_34_36 : i.val < 35
                · have heq : i = Fin.ofNat 180 34 := Fin.ext (by change i.val = 34; omega)
                  subst i
                  exact block_0034
                · have heq : i = Fin.ofNat 180 35 := Fin.ext (by change i.val = 35; omega)
                  subst i
                  exact block_0035
            · by_cases h_36_39 : i.val < 37
              · have heq : i = Fin.ofNat 180 36 := Fin.ext (by change i.val = 36; omega)
                subst i
                exact block_0036
              · by_cases h_37_39 : i.val < 38
                · have heq : i = Fin.ofNat 180 37 := Fin.ext (by change i.val = 37; omega)
                  subst i
                  exact block_0037
                · have heq : i = Fin.ofNat 180 38 := Fin.ext (by change i.val = 38; omega)
                  subst i
                  exact block_0038
          · by_cases h_39_45 : i.val < 42
            · by_cases h_39_42 : i.val < 40
              · have heq : i = Fin.ofNat 180 39 := Fin.ext (by change i.val = 39; omega)
                subst i
                exact block_0039
              · by_cases h_40_42 : i.val < 41
                · have heq : i = Fin.ofNat 180 40 := Fin.ext (by change i.val = 40; omega)
                  subst i
                  exact block_0040
                · have heq : i = Fin.ofNat 180 41 := Fin.ext (by change i.val = 41; omega)
                  subst i
                  exact block_0041
            · by_cases h_42_45 : i.val < 43
              · have heq : i = Fin.ofNat 180 42 := Fin.ext (by change i.val = 42; omega)
                subst i
                exact block_0042
              · by_cases h_43_45 : i.val < 44
                · have heq : i = Fin.ofNat 180 43 := Fin.ext (by change i.val = 43; omega)
                  subst i
                  exact block_0043
                · have heq : i = Fin.ofNat 180 44 := Fin.ext (by change i.val = 44; omega)
                  subst i
                  exact block_0044
    · by_cases h_45_90 : i.val < 67
      · by_cases h_45_67 : i.val < 56
        · by_cases h_45_56 : i.val < 50
          · by_cases h_45_50 : i.val < 47
            · by_cases h_45_47 : i.val < 46
              · have heq : i = Fin.ofNat 180 45 := Fin.ext (by change i.val = 45; omega)
                subst i
                exact block_0045
              · have heq : i = Fin.ofNat 180 46 := Fin.ext (by change i.val = 46; omega)
                subst i
                exact block_0046
            · by_cases h_47_50 : i.val < 48
              · have heq : i = Fin.ofNat 180 47 := Fin.ext (by change i.val = 47; omega)
                subst i
                exact block_0047
              · by_cases h_48_50 : i.val < 49
                · have heq : i = Fin.ofNat 180 48 := Fin.ext (by change i.val = 48; omega)
                  subst i
                  exact block_0048
                · have heq : i = Fin.ofNat 180 49 := Fin.ext (by change i.val = 49; omega)
                  subst i
                  exact block_0049
          · by_cases h_50_56 : i.val < 53
            · by_cases h_50_53 : i.val < 51
              · have heq : i = Fin.ofNat 180 50 := Fin.ext (by change i.val = 50; omega)
                subst i
                exact block_0050
              · by_cases h_51_53 : i.val < 52
                · have heq : i = Fin.ofNat 180 51 := Fin.ext (by change i.val = 51; omega)
                  subst i
                  exact block_0051
                · have heq : i = Fin.ofNat 180 52 := Fin.ext (by change i.val = 52; omega)
                  subst i
                  exact block_0052
            · by_cases h_53_56 : i.val < 54
              · have heq : i = Fin.ofNat 180 53 := Fin.ext (by change i.val = 53; omega)
                subst i
                exact block_0053
              · by_cases h_54_56 : i.val < 55
                · have heq : i = Fin.ofNat 180 54 := Fin.ext (by change i.val = 54; omega)
                  subst i
                  exact block_0054
                · have heq : i = Fin.ofNat 180 55 := Fin.ext (by change i.val = 55; omega)
                  subst i
                  exact block_0055
        · by_cases h_56_67 : i.val < 61
          · by_cases h_56_61 : i.val < 58
            · by_cases h_56_58 : i.val < 57
              · have heq : i = Fin.ofNat 180 56 := Fin.ext (by change i.val = 56; omega)
                subst i
                exact block_0056
              · have heq : i = Fin.ofNat 180 57 := Fin.ext (by change i.val = 57; omega)
                subst i
                exact block_0057
            · by_cases h_58_61 : i.val < 59
              · have heq : i = Fin.ofNat 180 58 := Fin.ext (by change i.val = 58; omega)
                subst i
                exact block_0058
              · by_cases h_59_61 : i.val < 60
                · have heq : i = Fin.ofNat 180 59 := Fin.ext (by change i.val = 59; omega)
                  subst i
                  exact block_0059
                · have heq : i = Fin.ofNat 180 60 := Fin.ext (by change i.val = 60; omega)
                  subst i
                  exact block_0060
          · by_cases h_61_67 : i.val < 64
            · by_cases h_61_64 : i.val < 62
              · have heq : i = Fin.ofNat 180 61 := Fin.ext (by change i.val = 61; omega)
                subst i
                exact block_0061
              · by_cases h_62_64 : i.val < 63
                · have heq : i = Fin.ofNat 180 62 := Fin.ext (by change i.val = 62; omega)
                  subst i
                  exact block_0062
                · have heq : i = Fin.ofNat 180 63 := Fin.ext (by change i.val = 63; omega)
                  subst i
                  exact block_0063
            · by_cases h_64_67 : i.val < 65
              · have heq : i = Fin.ofNat 180 64 := Fin.ext (by change i.val = 64; omega)
                subst i
                exact block_0064
              · by_cases h_65_67 : i.val < 66
                · have heq : i = Fin.ofNat 180 65 := Fin.ext (by change i.val = 65; omega)
                  subst i
                  exact block_0065
                · have heq : i = Fin.ofNat 180 66 := Fin.ext (by change i.val = 66; omega)
                  subst i
                  exact block_0066
      · by_cases h_67_90 : i.val < 78
        · by_cases h_67_78 : i.val < 72
          · by_cases h_67_72 : i.val < 69
            · by_cases h_67_69 : i.val < 68
              · have heq : i = Fin.ofNat 180 67 := Fin.ext (by change i.val = 67; omega)
                subst i
                exact block_0067
              · have heq : i = Fin.ofNat 180 68 := Fin.ext (by change i.val = 68; omega)
                subst i
                exact block_0068
            · by_cases h_69_72 : i.val < 70
              · have heq : i = Fin.ofNat 180 69 := Fin.ext (by change i.val = 69; omega)
                subst i
                exact block_0069
              · by_cases h_70_72 : i.val < 71
                · have heq : i = Fin.ofNat 180 70 := Fin.ext (by change i.val = 70; omega)
                  subst i
                  exact block_0070
                · have heq : i = Fin.ofNat 180 71 := Fin.ext (by change i.val = 71; omega)
                  subst i
                  exact block_0071
          · by_cases h_72_78 : i.val < 75
            · by_cases h_72_75 : i.val < 73
              · have heq : i = Fin.ofNat 180 72 := Fin.ext (by change i.val = 72; omega)
                subst i
                exact block_0072
              · by_cases h_73_75 : i.val < 74
                · have heq : i = Fin.ofNat 180 73 := Fin.ext (by change i.val = 73; omega)
                  subst i
                  exact block_0073
                · have heq : i = Fin.ofNat 180 74 := Fin.ext (by change i.val = 74; omega)
                  subst i
                  exact block_0074
            · by_cases h_75_78 : i.val < 76
              · have heq : i = Fin.ofNat 180 75 := Fin.ext (by change i.val = 75; omega)
                subst i
                exact block_0075
              · by_cases h_76_78 : i.val < 77
                · have heq : i = Fin.ofNat 180 76 := Fin.ext (by change i.val = 76; omega)
                  subst i
                  exact block_0076
                · have heq : i = Fin.ofNat 180 77 := Fin.ext (by change i.val = 77; omega)
                  subst i
                  exact block_0077
        · by_cases h_78_90 : i.val < 84
          · by_cases h_78_84 : i.val < 81
            · by_cases h_78_81 : i.val < 79
              · have heq : i = Fin.ofNat 180 78 := Fin.ext (by change i.val = 78; omega)
                subst i
                exact block_0078
              · by_cases h_79_81 : i.val < 80
                · have heq : i = Fin.ofNat 180 79 := Fin.ext (by change i.val = 79; omega)
                  subst i
                  exact block_0079
                · have heq : i = Fin.ofNat 180 80 := Fin.ext (by change i.val = 80; omega)
                  subst i
                  exact block_0080
            · by_cases h_81_84 : i.val < 82
              · have heq : i = Fin.ofNat 180 81 := Fin.ext (by change i.val = 81; omega)
                subst i
                exact block_0081
              · by_cases h_82_84 : i.val < 83
                · have heq : i = Fin.ofNat 180 82 := Fin.ext (by change i.val = 82; omega)
                  subst i
                  exact block_0082
                · have heq : i = Fin.ofNat 180 83 := Fin.ext (by change i.val = 83; omega)
                  subst i
                  exact block_0083
          · by_cases h_84_90 : i.val < 87
            · by_cases h_84_87 : i.val < 85
              · have heq : i = Fin.ofNat 180 84 := Fin.ext (by change i.val = 84; omega)
                subst i
                exact block_0084
              · by_cases h_85_87 : i.val < 86
                · have heq : i = Fin.ofNat 180 85 := Fin.ext (by change i.val = 85; omega)
                  subst i
                  exact block_0085
                · have heq : i = Fin.ofNat 180 86 := Fin.ext (by change i.val = 86; omega)
                  subst i
                  exact block_0086
            · by_cases h_87_90 : i.val < 88
              · have heq : i = Fin.ofNat 180 87 := Fin.ext (by change i.val = 87; omega)
                subst i
                exact block_0087
              · by_cases h_88_90 : i.val < 89
                · have heq : i = Fin.ofNat 180 88 := Fin.ext (by change i.val = 88; omega)
                  subst i
                  exact block_0088
                · have heq : i = Fin.ofNat 180 89 := Fin.ext (by change i.val = 89; omega)
                  subst i
                  exact block_0089
  · by_cases h_90_180 : i.val < 135
    · by_cases h_90_135 : i.val < 112
      · by_cases h_90_112 : i.val < 101
        · by_cases h_90_101 : i.val < 95
          · by_cases h_90_95 : i.val < 92
            · by_cases h_90_92 : i.val < 91
              · have heq : i = Fin.ofNat 180 90 := Fin.ext (by change i.val = 90; omega)
                subst i
                exact block_0090
              · have heq : i = Fin.ofNat 180 91 := Fin.ext (by change i.val = 91; omega)
                subst i
                exact block_0091
            · by_cases h_92_95 : i.val < 93
              · have heq : i = Fin.ofNat 180 92 := Fin.ext (by change i.val = 92; omega)
                subst i
                exact block_0092
              · by_cases h_93_95 : i.val < 94
                · have heq : i = Fin.ofNat 180 93 := Fin.ext (by change i.val = 93; omega)
                  subst i
                  exact block_0093
                · have heq : i = Fin.ofNat 180 94 := Fin.ext (by change i.val = 94; omega)
                  subst i
                  exact block_0094
          · by_cases h_95_101 : i.val < 98
            · by_cases h_95_98 : i.val < 96
              · have heq : i = Fin.ofNat 180 95 := Fin.ext (by change i.val = 95; omega)
                subst i
                exact block_0095
              · by_cases h_96_98 : i.val < 97
                · have heq : i = Fin.ofNat 180 96 := Fin.ext (by change i.val = 96; omega)
                  subst i
                  exact block_0096
                · have heq : i = Fin.ofNat 180 97 := Fin.ext (by change i.val = 97; omega)
                  subst i
                  exact block_0097
            · by_cases h_98_101 : i.val < 99
              · have heq : i = Fin.ofNat 180 98 := Fin.ext (by change i.val = 98; omega)
                subst i
                exact block_0098
              · by_cases h_99_101 : i.val < 100
                · have heq : i = Fin.ofNat 180 99 := Fin.ext (by change i.val = 99; omega)
                  subst i
                  exact block_0099
                · have heq : i = Fin.ofNat 180 100 := Fin.ext (by change i.val = 100; omega)
                  subst i
                  exact block_0100
        · by_cases h_101_112 : i.val < 106
          · by_cases h_101_106 : i.val < 103
            · by_cases h_101_103 : i.val < 102
              · have heq : i = Fin.ofNat 180 101 := Fin.ext (by change i.val = 101; omega)
                subst i
                exact block_0101
              · have heq : i = Fin.ofNat 180 102 := Fin.ext (by change i.val = 102; omega)
                subst i
                exact block_0102
            · by_cases h_103_106 : i.val < 104
              · have heq : i = Fin.ofNat 180 103 := Fin.ext (by change i.val = 103; omega)
                subst i
                exact block_0103
              · by_cases h_104_106 : i.val < 105
                · have heq : i = Fin.ofNat 180 104 := Fin.ext (by change i.val = 104; omega)
                  subst i
                  exact block_0104
                · have heq : i = Fin.ofNat 180 105 := Fin.ext (by change i.val = 105; omega)
                  subst i
                  exact block_0105
          · by_cases h_106_112 : i.val < 109
            · by_cases h_106_109 : i.val < 107
              · have heq : i = Fin.ofNat 180 106 := Fin.ext (by change i.val = 106; omega)
                subst i
                exact block_0106
              · by_cases h_107_109 : i.val < 108
                · have heq : i = Fin.ofNat 180 107 := Fin.ext (by change i.val = 107; omega)
                  subst i
                  exact block_0107
                · have heq : i = Fin.ofNat 180 108 := Fin.ext (by change i.val = 108; omega)
                  subst i
                  exact block_0108
            · by_cases h_109_112 : i.val < 110
              · have heq : i = Fin.ofNat 180 109 := Fin.ext (by change i.val = 109; omega)
                subst i
                exact block_0109
              · by_cases h_110_112 : i.val < 111
                · have heq : i = Fin.ofNat 180 110 := Fin.ext (by change i.val = 110; omega)
                  subst i
                  exact block_0110
                · have heq : i = Fin.ofNat 180 111 := Fin.ext (by change i.val = 111; omega)
                  subst i
                  exact block_0111
      · by_cases h_112_135 : i.val < 123
        · by_cases h_112_123 : i.val < 117
          · by_cases h_112_117 : i.val < 114
            · by_cases h_112_114 : i.val < 113
              · have heq : i = Fin.ofNat 180 112 := Fin.ext (by change i.val = 112; omega)
                subst i
                exact block_0112
              · have heq : i = Fin.ofNat 180 113 := Fin.ext (by change i.val = 113; omega)
                subst i
                exact block_0113
            · by_cases h_114_117 : i.val < 115
              · have heq : i = Fin.ofNat 180 114 := Fin.ext (by change i.val = 114; omega)
                subst i
                exact block_0114
              · by_cases h_115_117 : i.val < 116
                · have heq : i = Fin.ofNat 180 115 := Fin.ext (by change i.val = 115; omega)
                  subst i
                  exact block_0115
                · have heq : i = Fin.ofNat 180 116 := Fin.ext (by change i.val = 116; omega)
                  subst i
                  exact block_0116
          · by_cases h_117_123 : i.val < 120
            · by_cases h_117_120 : i.val < 118
              · have heq : i = Fin.ofNat 180 117 := Fin.ext (by change i.val = 117; omega)
                subst i
                exact block_0117
              · by_cases h_118_120 : i.val < 119
                · have heq : i = Fin.ofNat 180 118 := Fin.ext (by change i.val = 118; omega)
                  subst i
                  exact block_0118
                · have heq : i = Fin.ofNat 180 119 := Fin.ext (by change i.val = 119; omega)
                  subst i
                  exact block_0119
            · by_cases h_120_123 : i.val < 121
              · have heq : i = Fin.ofNat 180 120 := Fin.ext (by change i.val = 120; omega)
                subst i
                exact block_0120
              · by_cases h_121_123 : i.val < 122
                · have heq : i = Fin.ofNat 180 121 := Fin.ext (by change i.val = 121; omega)
                  subst i
                  exact block_0121
                · have heq : i = Fin.ofNat 180 122 := Fin.ext (by change i.val = 122; omega)
                  subst i
                  exact block_0122
        · by_cases h_123_135 : i.val < 129
          · by_cases h_123_129 : i.val < 126
            · by_cases h_123_126 : i.val < 124
              · have heq : i = Fin.ofNat 180 123 := Fin.ext (by change i.val = 123; omega)
                subst i
                exact block_0123
              · by_cases h_124_126 : i.val < 125
                · have heq : i = Fin.ofNat 180 124 := Fin.ext (by change i.val = 124; omega)
                  subst i
                  exact block_0124
                · have heq : i = Fin.ofNat 180 125 := Fin.ext (by change i.val = 125; omega)
                  subst i
                  exact block_0125
            · by_cases h_126_129 : i.val < 127
              · have heq : i = Fin.ofNat 180 126 := Fin.ext (by change i.val = 126; omega)
                subst i
                exact block_0126
              · by_cases h_127_129 : i.val < 128
                · have heq : i = Fin.ofNat 180 127 := Fin.ext (by change i.val = 127; omega)
                  subst i
                  exact block_0127
                · have heq : i = Fin.ofNat 180 128 := Fin.ext (by change i.val = 128; omega)
                  subst i
                  exact block_0128
          · by_cases h_129_135 : i.val < 132
            · by_cases h_129_132 : i.val < 130
              · have heq : i = Fin.ofNat 180 129 := Fin.ext (by change i.val = 129; omega)
                subst i
                exact block_0129
              · by_cases h_130_132 : i.val < 131
                · have heq : i = Fin.ofNat 180 130 := Fin.ext (by change i.val = 130; omega)
                  subst i
                  exact block_0130
                · have heq : i = Fin.ofNat 180 131 := Fin.ext (by change i.val = 131; omega)
                  subst i
                  exact block_0131
            · by_cases h_132_135 : i.val < 133
              · have heq : i = Fin.ofNat 180 132 := Fin.ext (by change i.val = 132; omega)
                subst i
                exact block_0132
              · by_cases h_133_135 : i.val < 134
                · have heq : i = Fin.ofNat 180 133 := Fin.ext (by change i.val = 133; omega)
                  subst i
                  exact block_0133
                · have heq : i = Fin.ofNat 180 134 := Fin.ext (by change i.val = 134; omega)
                  subst i
                  exact block_0134
    · by_cases h_135_180 : i.val < 157
      · by_cases h_135_157 : i.val < 146
        · by_cases h_135_146 : i.val < 140
          · by_cases h_135_140 : i.val < 137
            · by_cases h_135_137 : i.val < 136
              · have heq : i = Fin.ofNat 180 135 := Fin.ext (by change i.val = 135; omega)
                subst i
                exact block_0135
              · have heq : i = Fin.ofNat 180 136 := Fin.ext (by change i.val = 136; omega)
                subst i
                exact block_0136
            · by_cases h_137_140 : i.val < 138
              · have heq : i = Fin.ofNat 180 137 := Fin.ext (by change i.val = 137; omega)
                subst i
                exact block_0137
              · by_cases h_138_140 : i.val < 139
                · have heq : i = Fin.ofNat 180 138 := Fin.ext (by change i.val = 138; omega)
                  subst i
                  exact block_0138
                · have heq : i = Fin.ofNat 180 139 := Fin.ext (by change i.val = 139; omega)
                  subst i
                  exact block_0139
          · by_cases h_140_146 : i.val < 143
            · by_cases h_140_143 : i.val < 141
              · have heq : i = Fin.ofNat 180 140 := Fin.ext (by change i.val = 140; omega)
                subst i
                exact block_0140
              · by_cases h_141_143 : i.val < 142
                · have heq : i = Fin.ofNat 180 141 := Fin.ext (by change i.val = 141; omega)
                  subst i
                  exact block_0141
                · have heq : i = Fin.ofNat 180 142 := Fin.ext (by change i.val = 142; omega)
                  subst i
                  exact block_0142
            · by_cases h_143_146 : i.val < 144
              · have heq : i = Fin.ofNat 180 143 := Fin.ext (by change i.val = 143; omega)
                subst i
                exact block_0143
              · by_cases h_144_146 : i.val < 145
                · have heq : i = Fin.ofNat 180 144 := Fin.ext (by change i.val = 144; omega)
                  subst i
                  exact block_0144
                · have heq : i = Fin.ofNat 180 145 := Fin.ext (by change i.val = 145; omega)
                  subst i
                  exact block_0145
        · by_cases h_146_157 : i.val < 151
          · by_cases h_146_151 : i.val < 148
            · by_cases h_146_148 : i.val < 147
              · have heq : i = Fin.ofNat 180 146 := Fin.ext (by change i.val = 146; omega)
                subst i
                exact block_0146
              · have heq : i = Fin.ofNat 180 147 := Fin.ext (by change i.val = 147; omega)
                subst i
                exact block_0147
            · by_cases h_148_151 : i.val < 149
              · have heq : i = Fin.ofNat 180 148 := Fin.ext (by change i.val = 148; omega)
                subst i
                exact block_0148
              · by_cases h_149_151 : i.val < 150
                · have heq : i = Fin.ofNat 180 149 := Fin.ext (by change i.val = 149; omega)
                  subst i
                  exact block_0149
                · have heq : i = Fin.ofNat 180 150 := Fin.ext (by change i.val = 150; omega)
                  subst i
                  exact block_0150
          · by_cases h_151_157 : i.val < 154
            · by_cases h_151_154 : i.val < 152
              · have heq : i = Fin.ofNat 180 151 := Fin.ext (by change i.val = 151; omega)
                subst i
                exact block_0151
              · by_cases h_152_154 : i.val < 153
                · have heq : i = Fin.ofNat 180 152 := Fin.ext (by change i.val = 152; omega)
                  subst i
                  exact block_0152
                · have heq : i = Fin.ofNat 180 153 := Fin.ext (by change i.val = 153; omega)
                  subst i
                  exact block_0153
            · by_cases h_154_157 : i.val < 155
              · have heq : i = Fin.ofNat 180 154 := Fin.ext (by change i.val = 154; omega)
                subst i
                exact block_0154
              · by_cases h_155_157 : i.val < 156
                · have heq : i = Fin.ofNat 180 155 := Fin.ext (by change i.val = 155; omega)
                  subst i
                  exact block_0155
                · have heq : i = Fin.ofNat 180 156 := Fin.ext (by change i.val = 156; omega)
                  subst i
                  exact block_0156
      · by_cases h_157_180 : i.val < 168
        · by_cases h_157_168 : i.val < 162
          · by_cases h_157_162 : i.val < 159
            · by_cases h_157_159 : i.val < 158
              · have heq : i = Fin.ofNat 180 157 := Fin.ext (by change i.val = 157; omega)
                subst i
                exact block_0157
              · have heq : i = Fin.ofNat 180 158 := Fin.ext (by change i.val = 158; omega)
                subst i
                exact block_0158
            · by_cases h_159_162 : i.val < 160
              · have heq : i = Fin.ofNat 180 159 := Fin.ext (by change i.val = 159; omega)
                subst i
                exact block_0159
              · by_cases h_160_162 : i.val < 161
                · have heq : i = Fin.ofNat 180 160 := Fin.ext (by change i.val = 160; omega)
                  subst i
                  exact block_0160
                · have heq : i = Fin.ofNat 180 161 := Fin.ext (by change i.val = 161; omega)
                  subst i
                  exact block_0161
          · by_cases h_162_168 : i.val < 165
            · by_cases h_162_165 : i.val < 163
              · have heq : i = Fin.ofNat 180 162 := Fin.ext (by change i.val = 162; omega)
                subst i
                exact block_0162
              · by_cases h_163_165 : i.val < 164
                · have heq : i = Fin.ofNat 180 163 := Fin.ext (by change i.val = 163; omega)
                  subst i
                  exact block_0163
                · have heq : i = Fin.ofNat 180 164 := Fin.ext (by change i.val = 164; omega)
                  subst i
                  exact block_0164
            · by_cases h_165_168 : i.val < 166
              · have heq : i = Fin.ofNat 180 165 := Fin.ext (by change i.val = 165; omega)
                subst i
                exact block_0165
              · by_cases h_166_168 : i.val < 167
                · have heq : i = Fin.ofNat 180 166 := Fin.ext (by change i.val = 166; omega)
                  subst i
                  exact block_0166
                · have heq : i = Fin.ofNat 180 167 := Fin.ext (by change i.val = 167; omega)
                  subst i
                  exact block_0167
        · by_cases h_168_180 : i.val < 174
          · by_cases h_168_174 : i.val < 171
            · by_cases h_168_171 : i.val < 169
              · have heq : i = Fin.ofNat 180 168 := Fin.ext (by change i.val = 168; omega)
                subst i
                exact block_0168
              · by_cases h_169_171 : i.val < 170
                · have heq : i = Fin.ofNat 180 169 := Fin.ext (by change i.val = 169; omega)
                  subst i
                  exact block_0169
                · have heq : i = Fin.ofNat 180 170 := Fin.ext (by change i.val = 170; omega)
                  subst i
                  exact block_0170
            · by_cases h_171_174 : i.val < 172
              · have heq : i = Fin.ofNat 180 171 := Fin.ext (by change i.val = 171; omega)
                subst i
                exact block_0171
              · by_cases h_172_174 : i.val < 173
                · have heq : i = Fin.ofNat 180 172 := Fin.ext (by change i.val = 172; omega)
                  subst i
                  exact block_0172
                · have heq : i = Fin.ofNat 180 173 := Fin.ext (by change i.val = 173; omega)
                  subst i
                  exact block_0173
          · by_cases h_174_180 : i.val < 177
            · by_cases h_174_177 : i.val < 175
              · have heq : i = Fin.ofNat 180 174 := Fin.ext (by change i.val = 174; omega)
                subst i
                exact block_0174
              · by_cases h_175_177 : i.val < 176
                · have heq : i = Fin.ofNat 180 175 := Fin.ext (by change i.val = 175; omega)
                  subst i
                  exact block_0175
                · have heq : i = Fin.ofNat 180 176 := Fin.ext (by change i.val = 176; omega)
                  subst i
                  exact block_0176
            · by_cases h_177_180 : i.val < 178
              · have heq : i = Fin.ofNat 180 177 := Fin.ext (by change i.val = 177; omega)
                subst i
                exact block_0177
              · by_cases h_178_180 : i.val < 179
                · have heq : i = Fin.ofNat 180 178 := Fin.ext (by change i.val = 178; omega)
                  subst i
                  exact block_0178
                · have heq : i = Fin.ofNat 180 179 := Fin.ext (by change i.val = 179; omega)
                  subst i
                  exact block_0179
end Papers.RationalityTen.RootedCanonical.RootedSixBase00.T1
