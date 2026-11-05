module
prelude
public import RootedSevenMixed008CanonicalS5T1Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed008.S5T1
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 5 (raw i) template root
      FacetUniverses.RootedSevenMixed008.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 115 := i.isLt
  by_cases h_0_115 : i.val < 57
  · by_cases h_0_57 : i.val < 28
    · by_cases h_0_28 : i.val < 14
      · by_cases h_0_14 : i.val < 7
        · by_cases h_0_7 : i.val < 3
          · by_cases h_0_3 : i.val < 1
            · have heq : i = Fin.ofNat 115 0 := Fin.ext (by change i.val = 0; omega)
              subst i
              exact block_0000
            · by_cases h_1_3 : i.val < 2
              · have heq : i = Fin.ofNat 115 1 := Fin.ext (by change i.val = 1; omega)
                subst i
                exact block_0001
              · have heq : i = Fin.ofNat 115 2 := Fin.ext (by change i.val = 2; omega)
                subst i
                exact block_0002
          · by_cases h_3_7 : i.val < 5
            · by_cases h_3_5 : i.val < 4
              · have heq : i = Fin.ofNat 115 3 := Fin.ext (by change i.val = 3; omega)
                subst i
                exact block_0003
              · have heq : i = Fin.ofNat 115 4 := Fin.ext (by change i.val = 4; omega)
                subst i
                exact block_0004
            · by_cases h_5_7 : i.val < 6
              · have heq : i = Fin.ofNat 115 5 := Fin.ext (by change i.val = 5; omega)
                subst i
                exact block_0005
              · have heq : i = Fin.ofNat 115 6 := Fin.ext (by change i.val = 6; omega)
                subst i
                exact block_0006
        · by_cases h_7_14 : i.val < 10
          · by_cases h_7_10 : i.val < 8
            · have heq : i = Fin.ofNat 115 7 := Fin.ext (by change i.val = 7; omega)
              subst i
              exact block_0007
            · by_cases h_8_10 : i.val < 9
              · have heq : i = Fin.ofNat 115 8 := Fin.ext (by change i.val = 8; omega)
                subst i
                exact block_0008
              · have heq : i = Fin.ofNat 115 9 := Fin.ext (by change i.val = 9; omega)
                subst i
                exact block_0009
          · by_cases h_10_14 : i.val < 12
            · by_cases h_10_12 : i.val < 11
              · have heq : i = Fin.ofNat 115 10 := Fin.ext (by change i.val = 10; omega)
                subst i
                exact block_0010
              · have heq : i = Fin.ofNat 115 11 := Fin.ext (by change i.val = 11; omega)
                subst i
                exact block_0011
            · by_cases h_12_14 : i.val < 13
              · have heq : i = Fin.ofNat 115 12 := Fin.ext (by change i.val = 12; omega)
                subst i
                exact block_0012
              · have heq : i = Fin.ofNat 115 13 := Fin.ext (by change i.val = 13; omega)
                subst i
                exact block_0013
      · by_cases h_14_28 : i.val < 21
        · by_cases h_14_21 : i.val < 17
          · by_cases h_14_17 : i.val < 15
            · have heq : i = Fin.ofNat 115 14 := Fin.ext (by change i.val = 14; omega)
              subst i
              exact block_0014
            · by_cases h_15_17 : i.val < 16
              · have heq : i = Fin.ofNat 115 15 := Fin.ext (by change i.val = 15; omega)
                subst i
                exact block_0015
              · have heq : i = Fin.ofNat 115 16 := Fin.ext (by change i.val = 16; omega)
                subst i
                exact block_0016
          · by_cases h_17_21 : i.val < 19
            · by_cases h_17_19 : i.val < 18
              · have heq : i = Fin.ofNat 115 17 := Fin.ext (by change i.val = 17; omega)
                subst i
                exact block_0017
              · have heq : i = Fin.ofNat 115 18 := Fin.ext (by change i.val = 18; omega)
                subst i
                exact block_0018
            · by_cases h_19_21 : i.val < 20
              · have heq : i = Fin.ofNat 115 19 := Fin.ext (by change i.val = 19; omega)
                subst i
                exact block_0019
              · have heq : i = Fin.ofNat 115 20 := Fin.ext (by change i.val = 20; omega)
                subst i
                exact block_0020
        · by_cases h_21_28 : i.val < 24
          · by_cases h_21_24 : i.val < 22
            · have heq : i = Fin.ofNat 115 21 := Fin.ext (by change i.val = 21; omega)
              subst i
              exact block_0021
            · by_cases h_22_24 : i.val < 23
              · have heq : i = Fin.ofNat 115 22 := Fin.ext (by change i.val = 22; omega)
                subst i
                exact block_0022
              · have heq : i = Fin.ofNat 115 23 := Fin.ext (by change i.val = 23; omega)
                subst i
                exact block_0023
          · by_cases h_24_28 : i.val < 26
            · by_cases h_24_26 : i.val < 25
              · have heq : i = Fin.ofNat 115 24 := Fin.ext (by change i.val = 24; omega)
                subst i
                exact block_0024
              · have heq : i = Fin.ofNat 115 25 := Fin.ext (by change i.val = 25; omega)
                subst i
                exact block_0025
            · by_cases h_26_28 : i.val < 27
              · have heq : i = Fin.ofNat 115 26 := Fin.ext (by change i.val = 26; omega)
                subst i
                exact block_0026
              · have heq : i = Fin.ofNat 115 27 := Fin.ext (by change i.val = 27; omega)
                subst i
                exact block_0027
    · by_cases h_28_57 : i.val < 42
      · by_cases h_28_42 : i.val < 35
        · by_cases h_28_35 : i.val < 31
          · by_cases h_28_31 : i.val < 29
            · have heq : i = Fin.ofNat 115 28 := Fin.ext (by change i.val = 28; omega)
              subst i
              exact block_0028
            · by_cases h_29_31 : i.val < 30
              · have heq : i = Fin.ofNat 115 29 := Fin.ext (by change i.val = 29; omega)
                subst i
                exact block_0029
              · have heq : i = Fin.ofNat 115 30 := Fin.ext (by change i.val = 30; omega)
                subst i
                exact block_0030
          · by_cases h_31_35 : i.val < 33
            · by_cases h_31_33 : i.val < 32
              · have heq : i = Fin.ofNat 115 31 := Fin.ext (by change i.val = 31; omega)
                subst i
                exact block_0031
              · have heq : i = Fin.ofNat 115 32 := Fin.ext (by change i.val = 32; omega)
                subst i
                exact block_0032
            · by_cases h_33_35 : i.val < 34
              · have heq : i = Fin.ofNat 115 33 := Fin.ext (by change i.val = 33; omega)
                subst i
                exact block_0033
              · have heq : i = Fin.ofNat 115 34 := Fin.ext (by change i.val = 34; omega)
                subst i
                exact block_0034
        · by_cases h_35_42 : i.val < 38
          · by_cases h_35_38 : i.val < 36
            · have heq : i = Fin.ofNat 115 35 := Fin.ext (by change i.val = 35; omega)
              subst i
              exact block_0035
            · by_cases h_36_38 : i.val < 37
              · have heq : i = Fin.ofNat 115 36 := Fin.ext (by change i.val = 36; omega)
                subst i
                exact block_0036
              · have heq : i = Fin.ofNat 115 37 := Fin.ext (by change i.val = 37; omega)
                subst i
                exact block_0037
          · by_cases h_38_42 : i.val < 40
            · by_cases h_38_40 : i.val < 39
              · have heq : i = Fin.ofNat 115 38 := Fin.ext (by change i.val = 38; omega)
                subst i
                exact block_0038
              · have heq : i = Fin.ofNat 115 39 := Fin.ext (by change i.val = 39; omega)
                subst i
                exact block_0039
            · by_cases h_40_42 : i.val < 41
              · have heq : i = Fin.ofNat 115 40 := Fin.ext (by change i.val = 40; omega)
                subst i
                exact block_0040
              · have heq : i = Fin.ofNat 115 41 := Fin.ext (by change i.val = 41; omega)
                subst i
                exact block_0041
      · by_cases h_42_57 : i.val < 49
        · by_cases h_42_49 : i.val < 45
          · by_cases h_42_45 : i.val < 43
            · have heq : i = Fin.ofNat 115 42 := Fin.ext (by change i.val = 42; omega)
              subst i
              exact block_0042
            · by_cases h_43_45 : i.val < 44
              · have heq : i = Fin.ofNat 115 43 := Fin.ext (by change i.val = 43; omega)
                subst i
                exact block_0043
              · have heq : i = Fin.ofNat 115 44 := Fin.ext (by change i.val = 44; omega)
                subst i
                exact block_0044
          · by_cases h_45_49 : i.val < 47
            · by_cases h_45_47 : i.val < 46
              · have heq : i = Fin.ofNat 115 45 := Fin.ext (by change i.val = 45; omega)
                subst i
                exact block_0045
              · have heq : i = Fin.ofNat 115 46 := Fin.ext (by change i.val = 46; omega)
                subst i
                exact block_0046
            · by_cases h_47_49 : i.val < 48
              · have heq : i = Fin.ofNat 115 47 := Fin.ext (by change i.val = 47; omega)
                subst i
                exact block_0047
              · have heq : i = Fin.ofNat 115 48 := Fin.ext (by change i.val = 48; omega)
                subst i
                exact block_0048
        · by_cases h_49_57 : i.val < 53
          · by_cases h_49_53 : i.val < 51
            · by_cases h_49_51 : i.val < 50
              · have heq : i = Fin.ofNat 115 49 := Fin.ext (by change i.val = 49; omega)
                subst i
                exact block_0049
              · have heq : i = Fin.ofNat 115 50 := Fin.ext (by change i.val = 50; omega)
                subst i
                exact block_0050
            · by_cases h_51_53 : i.val < 52
              · have heq : i = Fin.ofNat 115 51 := Fin.ext (by change i.val = 51; omega)
                subst i
                exact block_0051
              · have heq : i = Fin.ofNat 115 52 := Fin.ext (by change i.val = 52; omega)
                subst i
                exact block_0052
          · by_cases h_53_57 : i.val < 55
            · by_cases h_53_55 : i.val < 54
              · have heq : i = Fin.ofNat 115 53 := Fin.ext (by change i.val = 53; omega)
                subst i
                exact block_0053
              · have heq : i = Fin.ofNat 115 54 := Fin.ext (by change i.val = 54; omega)
                subst i
                exact block_0054
            · by_cases h_55_57 : i.val < 56
              · have heq : i = Fin.ofNat 115 55 := Fin.ext (by change i.val = 55; omega)
                subst i
                exact block_0055
              · have heq : i = Fin.ofNat 115 56 := Fin.ext (by change i.val = 56; omega)
                subst i
                exact block_0056
  · by_cases h_57_115 : i.val < 86
    · by_cases h_57_86 : i.val < 71
      · by_cases h_57_71 : i.val < 64
        · by_cases h_57_64 : i.val < 60
          · by_cases h_57_60 : i.val < 58
            · have heq : i = Fin.ofNat 115 57 := Fin.ext (by change i.val = 57; omega)
              subst i
              exact block_0057
            · by_cases h_58_60 : i.val < 59
              · have heq : i = Fin.ofNat 115 58 := Fin.ext (by change i.val = 58; omega)
                subst i
                exact block_0058
              · have heq : i = Fin.ofNat 115 59 := Fin.ext (by change i.val = 59; omega)
                subst i
                exact block_0059
          · by_cases h_60_64 : i.val < 62
            · by_cases h_60_62 : i.val < 61
              · have heq : i = Fin.ofNat 115 60 := Fin.ext (by change i.val = 60; omega)
                subst i
                exact block_0060
              · have heq : i = Fin.ofNat 115 61 := Fin.ext (by change i.val = 61; omega)
                subst i
                exact block_0061
            · by_cases h_62_64 : i.val < 63
              · have heq : i = Fin.ofNat 115 62 := Fin.ext (by change i.val = 62; omega)
                subst i
                exact block_0062
              · have heq : i = Fin.ofNat 115 63 := Fin.ext (by change i.val = 63; omega)
                subst i
                exact block_0063
        · by_cases h_64_71 : i.val < 67
          · by_cases h_64_67 : i.val < 65
            · have heq : i = Fin.ofNat 115 64 := Fin.ext (by change i.val = 64; omega)
              subst i
              exact block_0064
            · by_cases h_65_67 : i.val < 66
              · have heq : i = Fin.ofNat 115 65 := Fin.ext (by change i.val = 65; omega)
                subst i
                exact block_0065
              · have heq : i = Fin.ofNat 115 66 := Fin.ext (by change i.val = 66; omega)
                subst i
                exact block_0066
          · by_cases h_67_71 : i.val < 69
            · by_cases h_67_69 : i.val < 68
              · have heq : i = Fin.ofNat 115 67 := Fin.ext (by change i.val = 67; omega)
                subst i
                exact block_0067
              · have heq : i = Fin.ofNat 115 68 := Fin.ext (by change i.val = 68; omega)
                subst i
                exact block_0068
            · by_cases h_69_71 : i.val < 70
              · have heq : i = Fin.ofNat 115 69 := Fin.ext (by change i.val = 69; omega)
                subst i
                exact block_0069
              · have heq : i = Fin.ofNat 115 70 := Fin.ext (by change i.val = 70; omega)
                subst i
                exact block_0070
      · by_cases h_71_86 : i.val < 78
        · by_cases h_71_78 : i.val < 74
          · by_cases h_71_74 : i.val < 72
            · have heq : i = Fin.ofNat 115 71 := Fin.ext (by change i.val = 71; omega)
              subst i
              exact block_0071
            · by_cases h_72_74 : i.val < 73
              · have heq : i = Fin.ofNat 115 72 := Fin.ext (by change i.val = 72; omega)
                subst i
                exact block_0072
              · have heq : i = Fin.ofNat 115 73 := Fin.ext (by change i.val = 73; omega)
                subst i
                exact block_0073
          · by_cases h_74_78 : i.val < 76
            · by_cases h_74_76 : i.val < 75
              · have heq : i = Fin.ofNat 115 74 := Fin.ext (by change i.val = 74; omega)
                subst i
                exact block_0074
              · have heq : i = Fin.ofNat 115 75 := Fin.ext (by change i.val = 75; omega)
                subst i
                exact block_0075
            · by_cases h_76_78 : i.val < 77
              · have heq : i = Fin.ofNat 115 76 := Fin.ext (by change i.val = 76; omega)
                subst i
                exact block_0076
              · have heq : i = Fin.ofNat 115 77 := Fin.ext (by change i.val = 77; omega)
                subst i
                exact block_0077
        · by_cases h_78_86 : i.val < 82
          · by_cases h_78_82 : i.val < 80
            · by_cases h_78_80 : i.val < 79
              · have heq : i = Fin.ofNat 115 78 := Fin.ext (by change i.val = 78; omega)
                subst i
                exact block_0078
              · have heq : i = Fin.ofNat 115 79 := Fin.ext (by change i.val = 79; omega)
                subst i
                exact block_0079
            · by_cases h_80_82 : i.val < 81
              · have heq : i = Fin.ofNat 115 80 := Fin.ext (by change i.val = 80; omega)
                subst i
                exact block_0080
              · have heq : i = Fin.ofNat 115 81 := Fin.ext (by change i.val = 81; omega)
                subst i
                exact block_0081
          · by_cases h_82_86 : i.val < 84
            · by_cases h_82_84 : i.val < 83
              · have heq : i = Fin.ofNat 115 82 := Fin.ext (by change i.val = 82; omega)
                subst i
                exact block_0082
              · have heq : i = Fin.ofNat 115 83 := Fin.ext (by change i.val = 83; omega)
                subst i
                exact block_0083
            · by_cases h_84_86 : i.val < 85
              · have heq : i = Fin.ofNat 115 84 := Fin.ext (by change i.val = 84; omega)
                subst i
                exact block_0084
              · have heq : i = Fin.ofNat 115 85 := Fin.ext (by change i.val = 85; omega)
                subst i
                exact block_0085
    · by_cases h_86_115 : i.val < 100
      · by_cases h_86_100 : i.val < 93
        · by_cases h_86_93 : i.val < 89
          · by_cases h_86_89 : i.val < 87
            · have heq : i = Fin.ofNat 115 86 := Fin.ext (by change i.val = 86; omega)
              subst i
              exact block_0086
            · by_cases h_87_89 : i.val < 88
              · have heq : i = Fin.ofNat 115 87 := Fin.ext (by change i.val = 87; omega)
                subst i
                exact block_0087
              · have heq : i = Fin.ofNat 115 88 := Fin.ext (by change i.val = 88; omega)
                subst i
                exact block_0088
          · by_cases h_89_93 : i.val < 91
            · by_cases h_89_91 : i.val < 90
              · have heq : i = Fin.ofNat 115 89 := Fin.ext (by change i.val = 89; omega)
                subst i
                exact block_0089
              · have heq : i = Fin.ofNat 115 90 := Fin.ext (by change i.val = 90; omega)
                subst i
                exact block_0090
            · by_cases h_91_93 : i.val < 92
              · have heq : i = Fin.ofNat 115 91 := Fin.ext (by change i.val = 91; omega)
                subst i
                exact block_0091
              · have heq : i = Fin.ofNat 115 92 := Fin.ext (by change i.val = 92; omega)
                subst i
                exact block_0092
        · by_cases h_93_100 : i.val < 96
          · by_cases h_93_96 : i.val < 94
            · have heq : i = Fin.ofNat 115 93 := Fin.ext (by change i.val = 93; omega)
              subst i
              exact block_0093
            · by_cases h_94_96 : i.val < 95
              · have heq : i = Fin.ofNat 115 94 := Fin.ext (by change i.val = 94; omega)
                subst i
                exact block_0094
              · have heq : i = Fin.ofNat 115 95 := Fin.ext (by change i.val = 95; omega)
                subst i
                exact block_0095
          · by_cases h_96_100 : i.val < 98
            · by_cases h_96_98 : i.val < 97
              · have heq : i = Fin.ofNat 115 96 := Fin.ext (by change i.val = 96; omega)
                subst i
                exact block_0096
              · have heq : i = Fin.ofNat 115 97 := Fin.ext (by change i.val = 97; omega)
                subst i
                exact block_0097
            · by_cases h_98_100 : i.val < 99
              · have heq : i = Fin.ofNat 115 98 := Fin.ext (by change i.val = 98; omega)
                subst i
                exact block_0098
              · have heq : i = Fin.ofNat 115 99 := Fin.ext (by change i.val = 99; omega)
                subst i
                exact block_0099
      · by_cases h_100_115 : i.val < 107
        · by_cases h_100_107 : i.val < 103
          · by_cases h_100_103 : i.val < 101
            · have heq : i = Fin.ofNat 115 100 := Fin.ext (by change i.val = 100; omega)
              subst i
              exact block_0100
            · by_cases h_101_103 : i.val < 102
              · have heq : i = Fin.ofNat 115 101 := Fin.ext (by change i.val = 101; omega)
                subst i
                exact block_0101
              · have heq : i = Fin.ofNat 115 102 := Fin.ext (by change i.val = 102; omega)
                subst i
                exact block_0102
          · by_cases h_103_107 : i.val < 105
            · by_cases h_103_105 : i.val < 104
              · have heq : i = Fin.ofNat 115 103 := Fin.ext (by change i.val = 103; omega)
                subst i
                exact block_0103
              · have heq : i = Fin.ofNat 115 104 := Fin.ext (by change i.val = 104; omega)
                subst i
                exact block_0104
            · by_cases h_105_107 : i.val < 106
              · have heq : i = Fin.ofNat 115 105 := Fin.ext (by change i.val = 105; omega)
                subst i
                exact block_0105
              · have heq : i = Fin.ofNat 115 106 := Fin.ext (by change i.val = 106; omega)
                subst i
                exact block_0106
        · by_cases h_107_115 : i.val < 111
          · by_cases h_107_111 : i.val < 109
            · by_cases h_107_109 : i.val < 108
              · have heq : i = Fin.ofNat 115 107 := Fin.ext (by change i.val = 107; omega)
                subst i
                exact block_0107
              · have heq : i = Fin.ofNat 115 108 := Fin.ext (by change i.val = 108; omega)
                subst i
                exact block_0108
            · by_cases h_109_111 : i.val < 110
              · have heq : i = Fin.ofNat 115 109 := Fin.ext (by change i.val = 109; omega)
                subst i
                exact block_0109
              · have heq : i = Fin.ofNat 115 110 := Fin.ext (by change i.val = 110; omega)
                subst i
                exact block_0110
          · by_cases h_111_115 : i.val < 113
            · by_cases h_111_113 : i.val < 112
              · have heq : i = Fin.ofNat 115 111 := Fin.ext (by change i.val = 111; omega)
                subst i
                exact block_0111
              · have heq : i = Fin.ofNat 115 112 := Fin.ext (by change i.val = 112; omega)
                subst i
                exact block_0112
            · by_cases h_113_115 : i.val < 114
              · have heq : i = Fin.ofNat 115 113 := Fin.ext (by change i.val = 113; omega)
                subst i
                exact block_0113
              · have heq : i = Fin.ofNat 115 114 := Fin.ext (by change i.val = 114; omega)
                subst i
                exact block_0114
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed008.S5T1
