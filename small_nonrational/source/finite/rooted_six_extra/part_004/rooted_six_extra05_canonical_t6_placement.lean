module
prelude
public import RootedSixExtra05CanonicalT6Finite
public import Init.Omega

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.T6
theorem placement_checks (i : Fin blockCount) : FiniteChecks.Interval
    (fun inner => RawKindedFacePlacement.check 6 (raw i) template root
      FacetUniverses.RootedSixExtra05.cells inner 0 (witness i inner))
    0 (RawFacePlacement.count (raw i).shared (raw i).shared) := by
  have hi : i.val < 94 := i.isLt
  by_cases h_0_94 : i.val < 47
  · by_cases h_0_47 : i.val < 23
    · by_cases h_0_23 : i.val < 11
      · by_cases h_0_11 : i.val < 5
        · by_cases h_0_5 : i.val < 2
          · by_cases h_0_2 : i.val < 1
            · have heq : i = Fin.ofNat 94 0 := Fin.ext (by change i.val = 0; omega)
              subst i
              exact block_0000
            · have heq : i = Fin.ofNat 94 1 := Fin.ext (by change i.val = 1; omega)
              subst i
              exact block_0001
          · by_cases h_2_5 : i.val < 3
            · have heq : i = Fin.ofNat 94 2 := Fin.ext (by change i.val = 2; omega)
              subst i
              exact block_0002
            · by_cases h_3_5 : i.val < 4
              · have heq : i = Fin.ofNat 94 3 := Fin.ext (by change i.val = 3; omega)
                subst i
                exact block_0003
              · have heq : i = Fin.ofNat 94 4 := Fin.ext (by change i.val = 4; omega)
                subst i
                exact block_0004
        · by_cases h_5_11 : i.val < 8
          · by_cases h_5_8 : i.val < 6
            · have heq : i = Fin.ofNat 94 5 := Fin.ext (by change i.val = 5; omega)
              subst i
              exact block_0005
            · by_cases h_6_8 : i.val < 7
              · have heq : i = Fin.ofNat 94 6 := Fin.ext (by change i.val = 6; omega)
                subst i
                exact block_0006
              · have heq : i = Fin.ofNat 94 7 := Fin.ext (by change i.val = 7; omega)
                subst i
                exact block_0007
          · by_cases h_8_11 : i.val < 9
            · have heq : i = Fin.ofNat 94 8 := Fin.ext (by change i.val = 8; omega)
              subst i
              exact block_0008
            · by_cases h_9_11 : i.val < 10
              · have heq : i = Fin.ofNat 94 9 := Fin.ext (by change i.val = 9; omega)
                subst i
                exact block_0009
              · have heq : i = Fin.ofNat 94 10 := Fin.ext (by change i.val = 10; omega)
                subst i
                exact block_0010
      · by_cases h_11_23 : i.val < 17
        · by_cases h_11_17 : i.val < 14
          · by_cases h_11_14 : i.val < 12
            · have heq : i = Fin.ofNat 94 11 := Fin.ext (by change i.val = 11; omega)
              subst i
              exact block_0011
            · by_cases h_12_14 : i.val < 13
              · have heq : i = Fin.ofNat 94 12 := Fin.ext (by change i.val = 12; omega)
                subst i
                exact block_0012
              · have heq : i = Fin.ofNat 94 13 := Fin.ext (by change i.val = 13; omega)
                subst i
                exact block_0013
          · by_cases h_14_17 : i.val < 15
            · have heq : i = Fin.ofNat 94 14 := Fin.ext (by change i.val = 14; omega)
              subst i
              exact block_0014
            · by_cases h_15_17 : i.val < 16
              · have heq : i = Fin.ofNat 94 15 := Fin.ext (by change i.val = 15; omega)
                subst i
                exact block_0015
              · have heq : i = Fin.ofNat 94 16 := Fin.ext (by change i.val = 16; omega)
                subst i
                exact block_0016
        · by_cases h_17_23 : i.val < 20
          · by_cases h_17_20 : i.val < 18
            · have heq : i = Fin.ofNat 94 17 := Fin.ext (by change i.val = 17; omega)
              subst i
              exact block_0017
            · by_cases h_18_20 : i.val < 19
              · have heq : i = Fin.ofNat 94 18 := Fin.ext (by change i.val = 18; omega)
                subst i
                exact block_0018
              · have heq : i = Fin.ofNat 94 19 := Fin.ext (by change i.val = 19; omega)
                subst i
                exact block_0019
          · by_cases h_20_23 : i.val < 21
            · have heq : i = Fin.ofNat 94 20 := Fin.ext (by change i.val = 20; omega)
              subst i
              exact block_0020
            · by_cases h_21_23 : i.val < 22
              · have heq : i = Fin.ofNat 94 21 := Fin.ext (by change i.val = 21; omega)
                subst i
                exact block_0021
              · have heq : i = Fin.ofNat 94 22 := Fin.ext (by change i.val = 22; omega)
                subst i
                exact block_0022
    · by_cases h_23_47 : i.val < 35
      · by_cases h_23_35 : i.val < 29
        · by_cases h_23_29 : i.val < 26
          · by_cases h_23_26 : i.val < 24
            · have heq : i = Fin.ofNat 94 23 := Fin.ext (by change i.val = 23; omega)
              subst i
              exact block_0023
            · by_cases h_24_26 : i.val < 25
              · have heq : i = Fin.ofNat 94 24 := Fin.ext (by change i.val = 24; omega)
                subst i
                exact block_0024
              · have heq : i = Fin.ofNat 94 25 := Fin.ext (by change i.val = 25; omega)
                subst i
                exact block_0025
          · by_cases h_26_29 : i.val < 27
            · have heq : i = Fin.ofNat 94 26 := Fin.ext (by change i.val = 26; omega)
              subst i
              exact block_0026
            · by_cases h_27_29 : i.val < 28
              · have heq : i = Fin.ofNat 94 27 := Fin.ext (by change i.val = 27; omega)
                subst i
                exact block_0027
              · have heq : i = Fin.ofNat 94 28 := Fin.ext (by change i.val = 28; omega)
                subst i
                exact block_0028
        · by_cases h_29_35 : i.val < 32
          · by_cases h_29_32 : i.val < 30
            · have heq : i = Fin.ofNat 94 29 := Fin.ext (by change i.val = 29; omega)
              subst i
              exact block_0029
            · by_cases h_30_32 : i.val < 31
              · have heq : i = Fin.ofNat 94 30 := Fin.ext (by change i.val = 30; omega)
                subst i
                exact block_0030
              · have heq : i = Fin.ofNat 94 31 := Fin.ext (by change i.val = 31; omega)
                subst i
                exact block_0031
          · by_cases h_32_35 : i.val < 33
            · have heq : i = Fin.ofNat 94 32 := Fin.ext (by change i.val = 32; omega)
              subst i
              exact block_0032
            · by_cases h_33_35 : i.val < 34
              · have heq : i = Fin.ofNat 94 33 := Fin.ext (by change i.val = 33; omega)
                subst i
                exact block_0033
              · have heq : i = Fin.ofNat 94 34 := Fin.ext (by change i.val = 34; omega)
                subst i
                exact block_0034
      · by_cases h_35_47 : i.val < 41
        · by_cases h_35_41 : i.val < 38
          · by_cases h_35_38 : i.val < 36
            · have heq : i = Fin.ofNat 94 35 := Fin.ext (by change i.val = 35; omega)
              subst i
              exact block_0035
            · by_cases h_36_38 : i.val < 37
              · have heq : i = Fin.ofNat 94 36 := Fin.ext (by change i.val = 36; omega)
                subst i
                exact block_0036
              · have heq : i = Fin.ofNat 94 37 := Fin.ext (by change i.val = 37; omega)
                subst i
                exact block_0037
          · by_cases h_38_41 : i.val < 39
            · have heq : i = Fin.ofNat 94 38 := Fin.ext (by change i.val = 38; omega)
              subst i
              exact block_0038
            · by_cases h_39_41 : i.val < 40
              · have heq : i = Fin.ofNat 94 39 := Fin.ext (by change i.val = 39; omega)
                subst i
                exact block_0039
              · have heq : i = Fin.ofNat 94 40 := Fin.ext (by change i.val = 40; omega)
                subst i
                exact block_0040
        · by_cases h_41_47 : i.val < 44
          · by_cases h_41_44 : i.val < 42
            · have heq : i = Fin.ofNat 94 41 := Fin.ext (by change i.val = 41; omega)
              subst i
              exact block_0041
            · by_cases h_42_44 : i.val < 43
              · have heq : i = Fin.ofNat 94 42 := Fin.ext (by change i.val = 42; omega)
                subst i
                exact block_0042
              · have heq : i = Fin.ofNat 94 43 := Fin.ext (by change i.val = 43; omega)
                subst i
                exact block_0043
          · by_cases h_44_47 : i.val < 45
            · have heq : i = Fin.ofNat 94 44 := Fin.ext (by change i.val = 44; omega)
              subst i
              exact block_0044
            · by_cases h_45_47 : i.val < 46
              · have heq : i = Fin.ofNat 94 45 := Fin.ext (by change i.val = 45; omega)
                subst i
                exact block_0045
              · have heq : i = Fin.ofNat 94 46 := Fin.ext (by change i.val = 46; omega)
                subst i
                exact block_0046
  · by_cases h_47_94 : i.val < 70
    · by_cases h_47_70 : i.val < 58
      · by_cases h_47_58 : i.val < 52
        · by_cases h_47_52 : i.val < 49
          · by_cases h_47_49 : i.val < 48
            · have heq : i = Fin.ofNat 94 47 := Fin.ext (by change i.val = 47; omega)
              subst i
              exact block_0047
            · have heq : i = Fin.ofNat 94 48 := Fin.ext (by change i.val = 48; omega)
              subst i
              exact block_0048
          · by_cases h_49_52 : i.val < 50
            · have heq : i = Fin.ofNat 94 49 := Fin.ext (by change i.val = 49; omega)
              subst i
              exact block_0049
            · by_cases h_50_52 : i.val < 51
              · have heq : i = Fin.ofNat 94 50 := Fin.ext (by change i.val = 50; omega)
                subst i
                exact block_0050
              · have heq : i = Fin.ofNat 94 51 := Fin.ext (by change i.val = 51; omega)
                subst i
                exact block_0051
        · by_cases h_52_58 : i.val < 55
          · by_cases h_52_55 : i.val < 53
            · have heq : i = Fin.ofNat 94 52 := Fin.ext (by change i.val = 52; omega)
              subst i
              exact block_0052
            · by_cases h_53_55 : i.val < 54
              · have heq : i = Fin.ofNat 94 53 := Fin.ext (by change i.val = 53; omega)
                subst i
                exact block_0053
              · have heq : i = Fin.ofNat 94 54 := Fin.ext (by change i.val = 54; omega)
                subst i
                exact block_0054
          · by_cases h_55_58 : i.val < 56
            · have heq : i = Fin.ofNat 94 55 := Fin.ext (by change i.val = 55; omega)
              subst i
              exact block_0055
            · by_cases h_56_58 : i.val < 57
              · have heq : i = Fin.ofNat 94 56 := Fin.ext (by change i.val = 56; omega)
                subst i
                exact block_0056
              · have heq : i = Fin.ofNat 94 57 := Fin.ext (by change i.val = 57; omega)
                subst i
                exact block_0057
      · by_cases h_58_70 : i.val < 64
        · by_cases h_58_64 : i.val < 61
          · by_cases h_58_61 : i.val < 59
            · have heq : i = Fin.ofNat 94 58 := Fin.ext (by change i.val = 58; omega)
              subst i
              exact block_0058
            · by_cases h_59_61 : i.val < 60
              · have heq : i = Fin.ofNat 94 59 := Fin.ext (by change i.val = 59; omega)
                subst i
                exact block_0059
              · have heq : i = Fin.ofNat 94 60 := Fin.ext (by change i.val = 60; omega)
                subst i
                exact block_0060
          · by_cases h_61_64 : i.val < 62
            · have heq : i = Fin.ofNat 94 61 := Fin.ext (by change i.val = 61; omega)
              subst i
              exact block_0061
            · by_cases h_62_64 : i.val < 63
              · have heq : i = Fin.ofNat 94 62 := Fin.ext (by change i.val = 62; omega)
                subst i
                exact block_0062
              · have heq : i = Fin.ofNat 94 63 := Fin.ext (by change i.val = 63; omega)
                subst i
                exact block_0063
        · by_cases h_64_70 : i.val < 67
          · by_cases h_64_67 : i.val < 65
            · have heq : i = Fin.ofNat 94 64 := Fin.ext (by change i.val = 64; omega)
              subst i
              exact block_0064
            · by_cases h_65_67 : i.val < 66
              · have heq : i = Fin.ofNat 94 65 := Fin.ext (by change i.val = 65; omega)
                subst i
                exact block_0065
              · have heq : i = Fin.ofNat 94 66 := Fin.ext (by change i.val = 66; omega)
                subst i
                exact block_0066
          · by_cases h_67_70 : i.val < 68
            · have heq : i = Fin.ofNat 94 67 := Fin.ext (by change i.val = 67; omega)
              subst i
              exact block_0067
            · by_cases h_68_70 : i.val < 69
              · have heq : i = Fin.ofNat 94 68 := Fin.ext (by change i.val = 68; omega)
                subst i
                exact block_0068
              · have heq : i = Fin.ofNat 94 69 := Fin.ext (by change i.val = 69; omega)
                subst i
                exact block_0069
    · by_cases h_70_94 : i.val < 82
      · by_cases h_70_82 : i.val < 76
        · by_cases h_70_76 : i.val < 73
          · by_cases h_70_73 : i.val < 71
            · have heq : i = Fin.ofNat 94 70 := Fin.ext (by change i.val = 70; omega)
              subst i
              exact block_0070
            · by_cases h_71_73 : i.val < 72
              · have heq : i = Fin.ofNat 94 71 := Fin.ext (by change i.val = 71; omega)
                subst i
                exact block_0071
              · have heq : i = Fin.ofNat 94 72 := Fin.ext (by change i.val = 72; omega)
                subst i
                exact block_0072
          · by_cases h_73_76 : i.val < 74
            · have heq : i = Fin.ofNat 94 73 := Fin.ext (by change i.val = 73; omega)
              subst i
              exact block_0073
            · by_cases h_74_76 : i.val < 75
              · have heq : i = Fin.ofNat 94 74 := Fin.ext (by change i.val = 74; omega)
                subst i
                exact block_0074
              · have heq : i = Fin.ofNat 94 75 := Fin.ext (by change i.val = 75; omega)
                subst i
                exact block_0075
        · by_cases h_76_82 : i.val < 79
          · by_cases h_76_79 : i.val < 77
            · have heq : i = Fin.ofNat 94 76 := Fin.ext (by change i.val = 76; omega)
              subst i
              exact block_0076
            · by_cases h_77_79 : i.val < 78
              · have heq : i = Fin.ofNat 94 77 := Fin.ext (by change i.val = 77; omega)
                subst i
                exact block_0077
              · have heq : i = Fin.ofNat 94 78 := Fin.ext (by change i.val = 78; omega)
                subst i
                exact block_0078
          · by_cases h_79_82 : i.val < 80
            · have heq : i = Fin.ofNat 94 79 := Fin.ext (by change i.val = 79; omega)
              subst i
              exact block_0079
            · by_cases h_80_82 : i.val < 81
              · have heq : i = Fin.ofNat 94 80 := Fin.ext (by change i.val = 80; omega)
                subst i
                exact block_0080
              · have heq : i = Fin.ofNat 94 81 := Fin.ext (by change i.val = 81; omega)
                subst i
                exact block_0081
      · by_cases h_82_94 : i.val < 88
        · by_cases h_82_88 : i.val < 85
          · by_cases h_82_85 : i.val < 83
            · have heq : i = Fin.ofNat 94 82 := Fin.ext (by change i.val = 82; omega)
              subst i
              exact block_0082
            · by_cases h_83_85 : i.val < 84
              · have heq : i = Fin.ofNat 94 83 := Fin.ext (by change i.val = 83; omega)
                subst i
                exact block_0083
              · have heq : i = Fin.ofNat 94 84 := Fin.ext (by change i.val = 84; omega)
                subst i
                exact block_0084
          · by_cases h_85_88 : i.val < 86
            · have heq : i = Fin.ofNat 94 85 := Fin.ext (by change i.val = 85; omega)
              subst i
              exact block_0085
            · by_cases h_86_88 : i.val < 87
              · have heq : i = Fin.ofNat 94 86 := Fin.ext (by change i.val = 86; omega)
                subst i
                exact block_0086
              · have heq : i = Fin.ofNat 94 87 := Fin.ext (by change i.val = 87; omega)
                subst i
                exact block_0087
        · by_cases h_88_94 : i.val < 91
          · by_cases h_88_91 : i.val < 89
            · have heq : i = Fin.ofNat 94 88 := Fin.ext (by change i.val = 88; omega)
              subst i
              exact block_0088
            · by_cases h_89_91 : i.val < 90
              · have heq : i = Fin.ofNat 94 89 := Fin.ext (by change i.val = 89; omega)
                subst i
                exact block_0089
              · have heq : i = Fin.ofNat 94 90 := Fin.ext (by change i.val = 90; omega)
                subst i
                exact block_0090
          · by_cases h_91_94 : i.val < 92
            · have heq : i = Fin.ofNat 94 91 := Fin.ext (by change i.val = 91; omega)
              subst i
              exact block_0091
            · by_cases h_92_94 : i.val < 93
              · have heq : i = Fin.ofNat 94 92 := Fin.ext (by change i.val = 92; omega)
                subst i
                exact block_0092
              · have heq : i = Fin.ofNat 94 93 := Fin.ext (by change i.val = 93; omega)
                subst i
                exact block_0093
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.T6
