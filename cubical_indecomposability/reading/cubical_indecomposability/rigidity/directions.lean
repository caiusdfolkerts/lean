import cubical_indecomposability.rigidity.constraints

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CubicalIndecomposability.Rigidity

theorem multiplier_pos : ∀ e : Fin 404, 0 < multiplier e := by decide +kernel

theorem pivot_nonzero : ∀ e : Fin 404, direction e (pivot e) ≠ 0 := by decide +kernel

theorem direction_scale_000 : ∀ i : Fin 4,
    q (edgeVertex 0 1) i.castSucc * q (edgeVertex 0 0) 4 -
      q (edgeVertex 0 0) i.castSucc * q (edgeVertex 0 1) 4 =
        multiplier 0 * direction 0 i := by decide +kernel

theorem direction_scale_001 : ∀ i : Fin 4,
    q (edgeVertex 1 1) i.castSucc * q (edgeVertex 1 0) 4 -
      q (edgeVertex 1 0) i.castSucc * q (edgeVertex 1 1) 4 =
        multiplier 1 * direction 1 i := by decide +kernel

theorem direction_scale_002 : ∀ i : Fin 4,
    q (edgeVertex 2 1) i.castSucc * q (edgeVertex 2 0) 4 -
      q (edgeVertex 2 0) i.castSucc * q (edgeVertex 2 1) 4 =
        multiplier 2 * direction 2 i := by decide +kernel

theorem direction_scale_003 : ∀ i : Fin 4,
    q (edgeVertex 3 1) i.castSucc * q (edgeVertex 3 0) 4 -
      q (edgeVertex 3 0) i.castSucc * q (edgeVertex 3 1) 4 =
        multiplier 3 * direction 3 i := by decide +kernel

theorem direction_scale_004 : ∀ i : Fin 4,
    q (edgeVertex 4 1) i.castSucc * q (edgeVertex 4 0) 4 -
      q (edgeVertex 4 0) i.castSucc * q (edgeVertex 4 1) 4 =
        multiplier 4 * direction 4 i := by decide +kernel

theorem direction_scale_005 : ∀ i : Fin 4,
    q (edgeVertex 5 1) i.castSucc * q (edgeVertex 5 0) 4 -
      q (edgeVertex 5 0) i.castSucc * q (edgeVertex 5 1) 4 =
        multiplier 5 * direction 5 i := by decide +kernel

theorem direction_scale_006 : ∀ i : Fin 4,
    q (edgeVertex 6 1) i.castSucc * q (edgeVertex 6 0) 4 -
      q (edgeVertex 6 0) i.castSucc * q (edgeVertex 6 1) 4 =
        multiplier 6 * direction 6 i := by decide +kernel

theorem direction_scale_007 : ∀ i : Fin 4,
    q (edgeVertex 7 1) i.castSucc * q (edgeVertex 7 0) 4 -
      q (edgeVertex 7 0) i.castSucc * q (edgeVertex 7 1) 4 =
        multiplier 7 * direction 7 i := by decide +kernel

theorem direction_scale_008 : ∀ i : Fin 4,
    q (edgeVertex 8 1) i.castSucc * q (edgeVertex 8 0) 4 -
      q (edgeVertex 8 0) i.castSucc * q (edgeVertex 8 1) 4 =
        multiplier 8 * direction 8 i := by decide +kernel

theorem direction_scale_009 : ∀ i : Fin 4,
    q (edgeVertex 9 1) i.castSucc * q (edgeVertex 9 0) 4 -
      q (edgeVertex 9 0) i.castSucc * q (edgeVertex 9 1) 4 =
        multiplier 9 * direction 9 i := by decide +kernel

theorem direction_scale_010 : ∀ i : Fin 4,
    q (edgeVertex 10 1) i.castSucc * q (edgeVertex 10 0) 4 -
      q (edgeVertex 10 0) i.castSucc * q (edgeVertex 10 1) 4 =
        multiplier 10 * direction 10 i := by decide +kernel

theorem direction_scale_011 : ∀ i : Fin 4,
    q (edgeVertex 11 1) i.castSucc * q (edgeVertex 11 0) 4 -
      q (edgeVertex 11 0) i.castSucc * q (edgeVertex 11 1) 4 =
        multiplier 11 * direction 11 i := by decide +kernel

theorem direction_scale_012 : ∀ i : Fin 4,
    q (edgeVertex 12 1) i.castSucc * q (edgeVertex 12 0) 4 -
      q (edgeVertex 12 0) i.castSucc * q (edgeVertex 12 1) 4 =
        multiplier 12 * direction 12 i := by decide +kernel

theorem direction_scale_013 : ∀ i : Fin 4,
    q (edgeVertex 13 1) i.castSucc * q (edgeVertex 13 0) 4 -
      q (edgeVertex 13 0) i.castSucc * q (edgeVertex 13 1) 4 =
        multiplier 13 * direction 13 i := by decide +kernel

theorem direction_scale_014 : ∀ i : Fin 4,
    q (edgeVertex 14 1) i.castSucc * q (edgeVertex 14 0) 4 -
      q (edgeVertex 14 0) i.castSucc * q (edgeVertex 14 1) 4 =
        multiplier 14 * direction 14 i := by decide +kernel

theorem direction_scale_015 : ∀ i : Fin 4,
    q (edgeVertex 15 1) i.castSucc * q (edgeVertex 15 0) 4 -
      q (edgeVertex 15 0) i.castSucc * q (edgeVertex 15 1) 4 =
        multiplier 15 * direction 15 i := by decide +kernel

theorem direction_scale_016 : ∀ i : Fin 4,
    q (edgeVertex 16 1) i.castSucc * q (edgeVertex 16 0) 4 -
      q (edgeVertex 16 0) i.castSucc * q (edgeVertex 16 1) 4 =
        multiplier 16 * direction 16 i := by decide +kernel

theorem direction_scale_017 : ∀ i : Fin 4,
    q (edgeVertex 17 1) i.castSucc * q (edgeVertex 17 0) 4 -
      q (edgeVertex 17 0) i.castSucc * q (edgeVertex 17 1) 4 =
        multiplier 17 * direction 17 i := by decide +kernel

theorem direction_scale_018 : ∀ i : Fin 4,
    q (edgeVertex 18 1) i.castSucc * q (edgeVertex 18 0) 4 -
      q (edgeVertex 18 0) i.castSucc * q (edgeVertex 18 1) 4 =
        multiplier 18 * direction 18 i := by decide +kernel

theorem direction_scale_019 : ∀ i : Fin 4,
    q (edgeVertex 19 1) i.castSucc * q (edgeVertex 19 0) 4 -
      q (edgeVertex 19 0) i.castSucc * q (edgeVertex 19 1) 4 =
        multiplier 19 * direction 19 i := by decide +kernel

theorem direction_scale_020 : ∀ i : Fin 4,
    q (edgeVertex 20 1) i.castSucc * q (edgeVertex 20 0) 4 -
      q (edgeVertex 20 0) i.castSucc * q (edgeVertex 20 1) 4 =
        multiplier 20 * direction 20 i := by decide +kernel

theorem direction_scale_021 : ∀ i : Fin 4,
    q (edgeVertex 21 1) i.castSucc * q (edgeVertex 21 0) 4 -
      q (edgeVertex 21 0) i.castSucc * q (edgeVertex 21 1) 4 =
        multiplier 21 * direction 21 i := by decide +kernel

theorem direction_scale_022 : ∀ i : Fin 4,
    q (edgeVertex 22 1) i.castSucc * q (edgeVertex 22 0) 4 -
      q (edgeVertex 22 0) i.castSucc * q (edgeVertex 22 1) 4 =
        multiplier 22 * direction 22 i := by decide +kernel

theorem direction_scale_023 : ∀ i : Fin 4,
    q (edgeVertex 23 1) i.castSucc * q (edgeVertex 23 0) 4 -
      q (edgeVertex 23 0) i.castSucc * q (edgeVertex 23 1) 4 =
        multiplier 23 * direction 23 i := by decide +kernel

theorem direction_scale_024 : ∀ i : Fin 4,
    q (edgeVertex 24 1) i.castSucc * q (edgeVertex 24 0) 4 -
      q (edgeVertex 24 0) i.castSucc * q (edgeVertex 24 1) 4 =
        multiplier 24 * direction 24 i := by decide +kernel

theorem direction_scale_025 : ∀ i : Fin 4,
    q (edgeVertex 25 1) i.castSucc * q (edgeVertex 25 0) 4 -
      q (edgeVertex 25 0) i.castSucc * q (edgeVertex 25 1) 4 =
        multiplier 25 * direction 25 i := by decide +kernel

theorem direction_scale_026 : ∀ i : Fin 4,
    q (edgeVertex 26 1) i.castSucc * q (edgeVertex 26 0) 4 -
      q (edgeVertex 26 0) i.castSucc * q (edgeVertex 26 1) 4 =
        multiplier 26 * direction 26 i := by decide +kernel

theorem direction_scale_027 : ∀ i : Fin 4,
    q (edgeVertex 27 1) i.castSucc * q (edgeVertex 27 0) 4 -
      q (edgeVertex 27 0) i.castSucc * q (edgeVertex 27 1) 4 =
        multiplier 27 * direction 27 i := by decide +kernel

theorem direction_scale_028 : ∀ i : Fin 4,
    q (edgeVertex 28 1) i.castSucc * q (edgeVertex 28 0) 4 -
      q (edgeVertex 28 0) i.castSucc * q (edgeVertex 28 1) 4 =
        multiplier 28 * direction 28 i := by decide +kernel

theorem direction_scale_029 : ∀ i : Fin 4,
    q (edgeVertex 29 1) i.castSucc * q (edgeVertex 29 0) 4 -
      q (edgeVertex 29 0) i.castSucc * q (edgeVertex 29 1) 4 =
        multiplier 29 * direction 29 i := by decide +kernel

theorem direction_scale_030 : ∀ i : Fin 4,
    q (edgeVertex 30 1) i.castSucc * q (edgeVertex 30 0) 4 -
      q (edgeVertex 30 0) i.castSucc * q (edgeVertex 30 1) 4 =
        multiplier 30 * direction 30 i := by decide +kernel

theorem direction_scale_031 : ∀ i : Fin 4,
    q (edgeVertex 31 1) i.castSucc * q (edgeVertex 31 0) 4 -
      q (edgeVertex 31 0) i.castSucc * q (edgeVertex 31 1) 4 =
        multiplier 31 * direction 31 i := by decide +kernel

theorem direction_scale_032 : ∀ i : Fin 4,
    q (edgeVertex 32 1) i.castSucc * q (edgeVertex 32 0) 4 -
      q (edgeVertex 32 0) i.castSucc * q (edgeVertex 32 1) 4 =
        multiplier 32 * direction 32 i := by decide +kernel

theorem direction_scale_033 : ∀ i : Fin 4,
    q (edgeVertex 33 1) i.castSucc * q (edgeVertex 33 0) 4 -
      q (edgeVertex 33 0) i.castSucc * q (edgeVertex 33 1) 4 =
        multiplier 33 * direction 33 i := by decide +kernel

theorem direction_scale_034 : ∀ i : Fin 4,
    q (edgeVertex 34 1) i.castSucc * q (edgeVertex 34 0) 4 -
      q (edgeVertex 34 0) i.castSucc * q (edgeVertex 34 1) 4 =
        multiplier 34 * direction 34 i := by decide +kernel

theorem direction_scale_035 : ∀ i : Fin 4,
    q (edgeVertex 35 1) i.castSucc * q (edgeVertex 35 0) 4 -
      q (edgeVertex 35 0) i.castSucc * q (edgeVertex 35 1) 4 =
        multiplier 35 * direction 35 i := by decide +kernel

theorem direction_scale_036 : ∀ i : Fin 4,
    q (edgeVertex 36 1) i.castSucc * q (edgeVertex 36 0) 4 -
      q (edgeVertex 36 0) i.castSucc * q (edgeVertex 36 1) 4 =
        multiplier 36 * direction 36 i := by decide +kernel

theorem direction_scale_037 : ∀ i : Fin 4,
    q (edgeVertex 37 1) i.castSucc * q (edgeVertex 37 0) 4 -
      q (edgeVertex 37 0) i.castSucc * q (edgeVertex 37 1) 4 =
        multiplier 37 * direction 37 i := by decide +kernel

theorem direction_scale_038 : ∀ i : Fin 4,
    q (edgeVertex 38 1) i.castSucc * q (edgeVertex 38 0) 4 -
      q (edgeVertex 38 0) i.castSucc * q (edgeVertex 38 1) 4 =
        multiplier 38 * direction 38 i := by decide +kernel

theorem direction_scale_039 : ∀ i : Fin 4,
    q (edgeVertex 39 1) i.castSucc * q (edgeVertex 39 0) 4 -
      q (edgeVertex 39 0) i.castSucc * q (edgeVertex 39 1) 4 =
        multiplier 39 * direction 39 i := by decide +kernel

theorem direction_scale_040 : ∀ i : Fin 4,
    q (edgeVertex 40 1) i.castSucc * q (edgeVertex 40 0) 4 -
      q (edgeVertex 40 0) i.castSucc * q (edgeVertex 40 1) 4 =
        multiplier 40 * direction 40 i := by decide +kernel

theorem direction_scale_041 : ∀ i : Fin 4,
    q (edgeVertex 41 1) i.castSucc * q (edgeVertex 41 0) 4 -
      q (edgeVertex 41 0) i.castSucc * q (edgeVertex 41 1) 4 =
        multiplier 41 * direction 41 i := by decide +kernel

theorem direction_scale_042 : ∀ i : Fin 4,
    q (edgeVertex 42 1) i.castSucc * q (edgeVertex 42 0) 4 -
      q (edgeVertex 42 0) i.castSucc * q (edgeVertex 42 1) 4 =
        multiplier 42 * direction 42 i := by decide +kernel

theorem direction_scale_043 : ∀ i : Fin 4,
    q (edgeVertex 43 1) i.castSucc * q (edgeVertex 43 0) 4 -
      q (edgeVertex 43 0) i.castSucc * q (edgeVertex 43 1) 4 =
        multiplier 43 * direction 43 i := by decide +kernel

theorem direction_scale_044 : ∀ i : Fin 4,
    q (edgeVertex 44 1) i.castSucc * q (edgeVertex 44 0) 4 -
      q (edgeVertex 44 0) i.castSucc * q (edgeVertex 44 1) 4 =
        multiplier 44 * direction 44 i := by decide +kernel

theorem direction_scale_045 : ∀ i : Fin 4,
    q (edgeVertex 45 1) i.castSucc * q (edgeVertex 45 0) 4 -
      q (edgeVertex 45 0) i.castSucc * q (edgeVertex 45 1) 4 =
        multiplier 45 * direction 45 i := by decide +kernel

theorem direction_scale_046 : ∀ i : Fin 4,
    q (edgeVertex 46 1) i.castSucc * q (edgeVertex 46 0) 4 -
      q (edgeVertex 46 0) i.castSucc * q (edgeVertex 46 1) 4 =
        multiplier 46 * direction 46 i := by decide +kernel

theorem direction_scale_047 : ∀ i : Fin 4,
    q (edgeVertex 47 1) i.castSucc * q (edgeVertex 47 0) 4 -
      q (edgeVertex 47 0) i.castSucc * q (edgeVertex 47 1) 4 =
        multiplier 47 * direction 47 i := by decide +kernel

theorem direction_scale_048 : ∀ i : Fin 4,
    q (edgeVertex 48 1) i.castSucc * q (edgeVertex 48 0) 4 -
      q (edgeVertex 48 0) i.castSucc * q (edgeVertex 48 1) 4 =
        multiplier 48 * direction 48 i := by decide +kernel

theorem direction_scale_049 : ∀ i : Fin 4,
    q (edgeVertex 49 1) i.castSucc * q (edgeVertex 49 0) 4 -
      q (edgeVertex 49 0) i.castSucc * q (edgeVertex 49 1) 4 =
        multiplier 49 * direction 49 i := by decide +kernel

theorem direction_scale_050 : ∀ i : Fin 4,
    q (edgeVertex 50 1) i.castSucc * q (edgeVertex 50 0) 4 -
      q (edgeVertex 50 0) i.castSucc * q (edgeVertex 50 1) 4 =
        multiplier 50 * direction 50 i := by decide +kernel

theorem direction_scale_051 : ∀ i : Fin 4,
    q (edgeVertex 51 1) i.castSucc * q (edgeVertex 51 0) 4 -
      q (edgeVertex 51 0) i.castSucc * q (edgeVertex 51 1) 4 =
        multiplier 51 * direction 51 i := by decide +kernel

theorem direction_scale_052 : ∀ i : Fin 4,
    q (edgeVertex 52 1) i.castSucc * q (edgeVertex 52 0) 4 -
      q (edgeVertex 52 0) i.castSucc * q (edgeVertex 52 1) 4 =
        multiplier 52 * direction 52 i := by decide +kernel

theorem direction_scale_053 : ∀ i : Fin 4,
    q (edgeVertex 53 1) i.castSucc * q (edgeVertex 53 0) 4 -
      q (edgeVertex 53 0) i.castSucc * q (edgeVertex 53 1) 4 =
        multiplier 53 * direction 53 i := by decide +kernel

theorem direction_scale_054 : ∀ i : Fin 4,
    q (edgeVertex 54 1) i.castSucc * q (edgeVertex 54 0) 4 -
      q (edgeVertex 54 0) i.castSucc * q (edgeVertex 54 1) 4 =
        multiplier 54 * direction 54 i := by decide +kernel

theorem direction_scale_055 : ∀ i : Fin 4,
    q (edgeVertex 55 1) i.castSucc * q (edgeVertex 55 0) 4 -
      q (edgeVertex 55 0) i.castSucc * q (edgeVertex 55 1) 4 =
        multiplier 55 * direction 55 i := by decide +kernel

theorem direction_scale_056 : ∀ i : Fin 4,
    q (edgeVertex 56 1) i.castSucc * q (edgeVertex 56 0) 4 -
      q (edgeVertex 56 0) i.castSucc * q (edgeVertex 56 1) 4 =
        multiplier 56 * direction 56 i := by decide +kernel

theorem direction_scale_057 : ∀ i : Fin 4,
    q (edgeVertex 57 1) i.castSucc * q (edgeVertex 57 0) 4 -
      q (edgeVertex 57 0) i.castSucc * q (edgeVertex 57 1) 4 =
        multiplier 57 * direction 57 i := by decide +kernel

theorem direction_scale_058 : ∀ i : Fin 4,
    q (edgeVertex 58 1) i.castSucc * q (edgeVertex 58 0) 4 -
      q (edgeVertex 58 0) i.castSucc * q (edgeVertex 58 1) 4 =
        multiplier 58 * direction 58 i := by decide +kernel

theorem direction_scale_059 : ∀ i : Fin 4,
    q (edgeVertex 59 1) i.castSucc * q (edgeVertex 59 0) 4 -
      q (edgeVertex 59 0) i.castSucc * q (edgeVertex 59 1) 4 =
        multiplier 59 * direction 59 i := by decide +kernel

theorem direction_scale_060 : ∀ i : Fin 4,
    q (edgeVertex 60 1) i.castSucc * q (edgeVertex 60 0) 4 -
      q (edgeVertex 60 0) i.castSucc * q (edgeVertex 60 1) 4 =
        multiplier 60 * direction 60 i := by decide +kernel

theorem direction_scale_061 : ∀ i : Fin 4,
    q (edgeVertex 61 1) i.castSucc * q (edgeVertex 61 0) 4 -
      q (edgeVertex 61 0) i.castSucc * q (edgeVertex 61 1) 4 =
        multiplier 61 * direction 61 i := by decide +kernel

theorem direction_scale_062 : ∀ i : Fin 4,
    q (edgeVertex 62 1) i.castSucc * q (edgeVertex 62 0) 4 -
      q (edgeVertex 62 0) i.castSucc * q (edgeVertex 62 1) 4 =
        multiplier 62 * direction 62 i := by decide +kernel

theorem direction_scale_063 : ∀ i : Fin 4,
    q (edgeVertex 63 1) i.castSucc * q (edgeVertex 63 0) 4 -
      q (edgeVertex 63 0) i.castSucc * q (edgeVertex 63 1) 4 =
        multiplier 63 * direction 63 i := by decide +kernel

theorem direction_scale_064 : ∀ i : Fin 4,
    q (edgeVertex 64 1) i.castSucc * q (edgeVertex 64 0) 4 -
      q (edgeVertex 64 0) i.castSucc * q (edgeVertex 64 1) 4 =
        multiplier 64 * direction 64 i := by decide +kernel

theorem direction_scale_065 : ∀ i : Fin 4,
    q (edgeVertex 65 1) i.castSucc * q (edgeVertex 65 0) 4 -
      q (edgeVertex 65 0) i.castSucc * q (edgeVertex 65 1) 4 =
        multiplier 65 * direction 65 i := by decide +kernel

theorem direction_scale_066 : ∀ i : Fin 4,
    q (edgeVertex 66 1) i.castSucc * q (edgeVertex 66 0) 4 -
      q (edgeVertex 66 0) i.castSucc * q (edgeVertex 66 1) 4 =
        multiplier 66 * direction 66 i := by decide +kernel

theorem direction_scale_067 : ∀ i : Fin 4,
    q (edgeVertex 67 1) i.castSucc * q (edgeVertex 67 0) 4 -
      q (edgeVertex 67 0) i.castSucc * q (edgeVertex 67 1) 4 =
        multiplier 67 * direction 67 i := by decide +kernel

theorem direction_scale_068 : ∀ i : Fin 4,
    q (edgeVertex 68 1) i.castSucc * q (edgeVertex 68 0) 4 -
      q (edgeVertex 68 0) i.castSucc * q (edgeVertex 68 1) 4 =
        multiplier 68 * direction 68 i := by decide +kernel

theorem direction_scale_069 : ∀ i : Fin 4,
    q (edgeVertex 69 1) i.castSucc * q (edgeVertex 69 0) 4 -
      q (edgeVertex 69 0) i.castSucc * q (edgeVertex 69 1) 4 =
        multiplier 69 * direction 69 i := by decide +kernel

theorem direction_scale_070 : ∀ i : Fin 4,
    q (edgeVertex 70 1) i.castSucc * q (edgeVertex 70 0) 4 -
      q (edgeVertex 70 0) i.castSucc * q (edgeVertex 70 1) 4 =
        multiplier 70 * direction 70 i := by decide +kernel

theorem direction_scale_071 : ∀ i : Fin 4,
    q (edgeVertex 71 1) i.castSucc * q (edgeVertex 71 0) 4 -
      q (edgeVertex 71 0) i.castSucc * q (edgeVertex 71 1) 4 =
        multiplier 71 * direction 71 i := by decide +kernel

theorem direction_scale_072 : ∀ i : Fin 4,
    q (edgeVertex 72 1) i.castSucc * q (edgeVertex 72 0) 4 -
      q (edgeVertex 72 0) i.castSucc * q (edgeVertex 72 1) 4 =
        multiplier 72 * direction 72 i := by decide +kernel

theorem direction_scale_073 : ∀ i : Fin 4,
    q (edgeVertex 73 1) i.castSucc * q (edgeVertex 73 0) 4 -
      q (edgeVertex 73 0) i.castSucc * q (edgeVertex 73 1) 4 =
        multiplier 73 * direction 73 i := by decide +kernel

theorem direction_scale_074 : ∀ i : Fin 4,
    q (edgeVertex 74 1) i.castSucc * q (edgeVertex 74 0) 4 -
      q (edgeVertex 74 0) i.castSucc * q (edgeVertex 74 1) 4 =
        multiplier 74 * direction 74 i := by decide +kernel

theorem direction_scale_075 : ∀ i : Fin 4,
    q (edgeVertex 75 1) i.castSucc * q (edgeVertex 75 0) 4 -
      q (edgeVertex 75 0) i.castSucc * q (edgeVertex 75 1) 4 =
        multiplier 75 * direction 75 i := by decide +kernel

theorem direction_scale_076 : ∀ i : Fin 4,
    q (edgeVertex 76 1) i.castSucc * q (edgeVertex 76 0) 4 -
      q (edgeVertex 76 0) i.castSucc * q (edgeVertex 76 1) 4 =
        multiplier 76 * direction 76 i := by decide +kernel

theorem direction_scale_077 : ∀ i : Fin 4,
    q (edgeVertex 77 1) i.castSucc * q (edgeVertex 77 0) 4 -
      q (edgeVertex 77 0) i.castSucc * q (edgeVertex 77 1) 4 =
        multiplier 77 * direction 77 i := by decide +kernel

theorem direction_scale_078 : ∀ i : Fin 4,
    q (edgeVertex 78 1) i.castSucc * q (edgeVertex 78 0) 4 -
      q (edgeVertex 78 0) i.castSucc * q (edgeVertex 78 1) 4 =
        multiplier 78 * direction 78 i := by decide +kernel

theorem direction_scale_079 : ∀ i : Fin 4,
    q (edgeVertex 79 1) i.castSucc * q (edgeVertex 79 0) 4 -
      q (edgeVertex 79 0) i.castSucc * q (edgeVertex 79 1) 4 =
        multiplier 79 * direction 79 i := by decide +kernel

theorem direction_scale_080 : ∀ i : Fin 4,
    q (edgeVertex 80 1) i.castSucc * q (edgeVertex 80 0) 4 -
      q (edgeVertex 80 0) i.castSucc * q (edgeVertex 80 1) 4 =
        multiplier 80 * direction 80 i := by decide +kernel

theorem direction_scale_081 : ∀ i : Fin 4,
    q (edgeVertex 81 1) i.castSucc * q (edgeVertex 81 0) 4 -
      q (edgeVertex 81 0) i.castSucc * q (edgeVertex 81 1) 4 =
        multiplier 81 * direction 81 i := by decide +kernel

theorem direction_scale_082 : ∀ i : Fin 4,
    q (edgeVertex 82 1) i.castSucc * q (edgeVertex 82 0) 4 -
      q (edgeVertex 82 0) i.castSucc * q (edgeVertex 82 1) 4 =
        multiplier 82 * direction 82 i := by decide +kernel

theorem direction_scale_083 : ∀ i : Fin 4,
    q (edgeVertex 83 1) i.castSucc * q (edgeVertex 83 0) 4 -
      q (edgeVertex 83 0) i.castSucc * q (edgeVertex 83 1) 4 =
        multiplier 83 * direction 83 i := by decide +kernel

theorem direction_scale_084 : ∀ i : Fin 4,
    q (edgeVertex 84 1) i.castSucc * q (edgeVertex 84 0) 4 -
      q (edgeVertex 84 0) i.castSucc * q (edgeVertex 84 1) 4 =
        multiplier 84 * direction 84 i := by decide +kernel

theorem direction_scale_085 : ∀ i : Fin 4,
    q (edgeVertex 85 1) i.castSucc * q (edgeVertex 85 0) 4 -
      q (edgeVertex 85 0) i.castSucc * q (edgeVertex 85 1) 4 =
        multiplier 85 * direction 85 i := by decide +kernel

theorem direction_scale_086 : ∀ i : Fin 4,
    q (edgeVertex 86 1) i.castSucc * q (edgeVertex 86 0) 4 -
      q (edgeVertex 86 0) i.castSucc * q (edgeVertex 86 1) 4 =
        multiplier 86 * direction 86 i := by decide +kernel

theorem direction_scale_087 : ∀ i : Fin 4,
    q (edgeVertex 87 1) i.castSucc * q (edgeVertex 87 0) 4 -
      q (edgeVertex 87 0) i.castSucc * q (edgeVertex 87 1) 4 =
        multiplier 87 * direction 87 i := by decide +kernel

theorem direction_scale_088 : ∀ i : Fin 4,
    q (edgeVertex 88 1) i.castSucc * q (edgeVertex 88 0) 4 -
      q (edgeVertex 88 0) i.castSucc * q (edgeVertex 88 1) 4 =
        multiplier 88 * direction 88 i := by decide +kernel

theorem direction_scale_089 : ∀ i : Fin 4,
    q (edgeVertex 89 1) i.castSucc * q (edgeVertex 89 0) 4 -
      q (edgeVertex 89 0) i.castSucc * q (edgeVertex 89 1) 4 =
        multiplier 89 * direction 89 i := by decide +kernel

theorem direction_scale_090 : ∀ i : Fin 4,
    q (edgeVertex 90 1) i.castSucc * q (edgeVertex 90 0) 4 -
      q (edgeVertex 90 0) i.castSucc * q (edgeVertex 90 1) 4 =
        multiplier 90 * direction 90 i := by decide +kernel

theorem direction_scale_091 : ∀ i : Fin 4,
    q (edgeVertex 91 1) i.castSucc * q (edgeVertex 91 0) 4 -
      q (edgeVertex 91 0) i.castSucc * q (edgeVertex 91 1) 4 =
        multiplier 91 * direction 91 i := by decide +kernel

theorem direction_scale_092 : ∀ i : Fin 4,
    q (edgeVertex 92 1) i.castSucc * q (edgeVertex 92 0) 4 -
      q (edgeVertex 92 0) i.castSucc * q (edgeVertex 92 1) 4 =
        multiplier 92 * direction 92 i := by decide +kernel

theorem direction_scale_093 : ∀ i : Fin 4,
    q (edgeVertex 93 1) i.castSucc * q (edgeVertex 93 0) 4 -
      q (edgeVertex 93 0) i.castSucc * q (edgeVertex 93 1) 4 =
        multiplier 93 * direction 93 i := by decide +kernel

theorem direction_scale_094 : ∀ i : Fin 4,
    q (edgeVertex 94 1) i.castSucc * q (edgeVertex 94 0) 4 -
      q (edgeVertex 94 0) i.castSucc * q (edgeVertex 94 1) 4 =
        multiplier 94 * direction 94 i := by decide +kernel

theorem direction_scale_095 : ∀ i : Fin 4,
    q (edgeVertex 95 1) i.castSucc * q (edgeVertex 95 0) 4 -
      q (edgeVertex 95 0) i.castSucc * q (edgeVertex 95 1) 4 =
        multiplier 95 * direction 95 i := by decide +kernel

theorem direction_scale_096 : ∀ i : Fin 4,
    q (edgeVertex 96 1) i.castSucc * q (edgeVertex 96 0) 4 -
      q (edgeVertex 96 0) i.castSucc * q (edgeVertex 96 1) 4 =
        multiplier 96 * direction 96 i := by decide +kernel

theorem direction_scale_097 : ∀ i : Fin 4,
    q (edgeVertex 97 1) i.castSucc * q (edgeVertex 97 0) 4 -
      q (edgeVertex 97 0) i.castSucc * q (edgeVertex 97 1) 4 =
        multiplier 97 * direction 97 i := by decide +kernel

theorem direction_scale_098 : ∀ i : Fin 4,
    q (edgeVertex 98 1) i.castSucc * q (edgeVertex 98 0) 4 -
      q (edgeVertex 98 0) i.castSucc * q (edgeVertex 98 1) 4 =
        multiplier 98 * direction 98 i := by decide +kernel

theorem direction_scale_099 : ∀ i : Fin 4,
    q (edgeVertex 99 1) i.castSucc * q (edgeVertex 99 0) 4 -
      q (edgeVertex 99 0) i.castSucc * q (edgeVertex 99 1) 4 =
        multiplier 99 * direction 99 i := by decide +kernel

theorem direction_scale_100 : ∀ i : Fin 4,
    q (edgeVertex 100 1) i.castSucc * q (edgeVertex 100 0) 4 -
      q (edgeVertex 100 0) i.castSucc * q (edgeVertex 100 1) 4 =
        multiplier 100 * direction 100 i := by decide +kernel

theorem direction_scale_101 : ∀ i : Fin 4,
    q (edgeVertex 101 1) i.castSucc * q (edgeVertex 101 0) 4 -
      q (edgeVertex 101 0) i.castSucc * q (edgeVertex 101 1) 4 =
        multiplier 101 * direction 101 i := by decide +kernel

theorem direction_scale_102 : ∀ i : Fin 4,
    q (edgeVertex 102 1) i.castSucc * q (edgeVertex 102 0) 4 -
      q (edgeVertex 102 0) i.castSucc * q (edgeVertex 102 1) 4 =
        multiplier 102 * direction 102 i := by decide +kernel

theorem direction_scale_103 : ∀ i : Fin 4,
    q (edgeVertex 103 1) i.castSucc * q (edgeVertex 103 0) 4 -
      q (edgeVertex 103 0) i.castSucc * q (edgeVertex 103 1) 4 =
        multiplier 103 * direction 103 i := by decide +kernel

theorem direction_scale_104 : ∀ i : Fin 4,
    q (edgeVertex 104 1) i.castSucc * q (edgeVertex 104 0) 4 -
      q (edgeVertex 104 0) i.castSucc * q (edgeVertex 104 1) 4 =
        multiplier 104 * direction 104 i := by decide +kernel

theorem direction_scale_105 : ∀ i : Fin 4,
    q (edgeVertex 105 1) i.castSucc * q (edgeVertex 105 0) 4 -
      q (edgeVertex 105 0) i.castSucc * q (edgeVertex 105 1) 4 =
        multiplier 105 * direction 105 i := by decide +kernel

theorem direction_scale_106 : ∀ i : Fin 4,
    q (edgeVertex 106 1) i.castSucc * q (edgeVertex 106 0) 4 -
      q (edgeVertex 106 0) i.castSucc * q (edgeVertex 106 1) 4 =
        multiplier 106 * direction 106 i := by decide +kernel

theorem direction_scale_107 : ∀ i : Fin 4,
    q (edgeVertex 107 1) i.castSucc * q (edgeVertex 107 0) 4 -
      q (edgeVertex 107 0) i.castSucc * q (edgeVertex 107 1) 4 =
        multiplier 107 * direction 107 i := by decide +kernel

theorem direction_scale_108 : ∀ i : Fin 4,
    q (edgeVertex 108 1) i.castSucc * q (edgeVertex 108 0) 4 -
      q (edgeVertex 108 0) i.castSucc * q (edgeVertex 108 1) 4 =
        multiplier 108 * direction 108 i := by decide +kernel

theorem direction_scale_109 : ∀ i : Fin 4,
    q (edgeVertex 109 1) i.castSucc * q (edgeVertex 109 0) 4 -
      q (edgeVertex 109 0) i.castSucc * q (edgeVertex 109 1) 4 =
        multiplier 109 * direction 109 i := by decide +kernel

theorem direction_scale_110 : ∀ i : Fin 4,
    q (edgeVertex 110 1) i.castSucc * q (edgeVertex 110 0) 4 -
      q (edgeVertex 110 0) i.castSucc * q (edgeVertex 110 1) 4 =
        multiplier 110 * direction 110 i := by decide +kernel

theorem direction_scale_111 : ∀ i : Fin 4,
    q (edgeVertex 111 1) i.castSucc * q (edgeVertex 111 0) 4 -
      q (edgeVertex 111 0) i.castSucc * q (edgeVertex 111 1) 4 =
        multiplier 111 * direction 111 i := by decide +kernel

theorem direction_scale_112 : ∀ i : Fin 4,
    q (edgeVertex 112 1) i.castSucc * q (edgeVertex 112 0) 4 -
      q (edgeVertex 112 0) i.castSucc * q (edgeVertex 112 1) 4 =
        multiplier 112 * direction 112 i := by decide +kernel

theorem direction_scale_113 : ∀ i : Fin 4,
    q (edgeVertex 113 1) i.castSucc * q (edgeVertex 113 0) 4 -
      q (edgeVertex 113 0) i.castSucc * q (edgeVertex 113 1) 4 =
        multiplier 113 * direction 113 i := by decide +kernel

theorem direction_scale_114 : ∀ i : Fin 4,
    q (edgeVertex 114 1) i.castSucc * q (edgeVertex 114 0) 4 -
      q (edgeVertex 114 0) i.castSucc * q (edgeVertex 114 1) 4 =
        multiplier 114 * direction 114 i := by decide +kernel

theorem direction_scale_115 : ∀ i : Fin 4,
    q (edgeVertex 115 1) i.castSucc * q (edgeVertex 115 0) 4 -
      q (edgeVertex 115 0) i.castSucc * q (edgeVertex 115 1) 4 =
        multiplier 115 * direction 115 i := by decide +kernel

theorem direction_scale_116 : ∀ i : Fin 4,
    q (edgeVertex 116 1) i.castSucc * q (edgeVertex 116 0) 4 -
      q (edgeVertex 116 0) i.castSucc * q (edgeVertex 116 1) 4 =
        multiplier 116 * direction 116 i := by decide +kernel

theorem direction_scale_117 : ∀ i : Fin 4,
    q (edgeVertex 117 1) i.castSucc * q (edgeVertex 117 0) 4 -
      q (edgeVertex 117 0) i.castSucc * q (edgeVertex 117 1) 4 =
        multiplier 117 * direction 117 i := by decide +kernel

theorem direction_scale_118 : ∀ i : Fin 4,
    q (edgeVertex 118 1) i.castSucc * q (edgeVertex 118 0) 4 -
      q (edgeVertex 118 0) i.castSucc * q (edgeVertex 118 1) 4 =
        multiplier 118 * direction 118 i := by decide +kernel

theorem direction_scale_119 : ∀ i : Fin 4,
    q (edgeVertex 119 1) i.castSucc * q (edgeVertex 119 0) 4 -
      q (edgeVertex 119 0) i.castSucc * q (edgeVertex 119 1) 4 =
        multiplier 119 * direction 119 i := by decide +kernel

theorem direction_scale_120 : ∀ i : Fin 4,
    q (edgeVertex 120 1) i.castSucc * q (edgeVertex 120 0) 4 -
      q (edgeVertex 120 0) i.castSucc * q (edgeVertex 120 1) 4 =
        multiplier 120 * direction 120 i := by decide +kernel

theorem direction_scale_121 : ∀ i : Fin 4,
    q (edgeVertex 121 1) i.castSucc * q (edgeVertex 121 0) 4 -
      q (edgeVertex 121 0) i.castSucc * q (edgeVertex 121 1) 4 =
        multiplier 121 * direction 121 i := by decide +kernel

theorem direction_scale_122 : ∀ i : Fin 4,
    q (edgeVertex 122 1) i.castSucc * q (edgeVertex 122 0) 4 -
      q (edgeVertex 122 0) i.castSucc * q (edgeVertex 122 1) 4 =
        multiplier 122 * direction 122 i := by decide +kernel

theorem direction_scale_123 : ∀ i : Fin 4,
    q (edgeVertex 123 1) i.castSucc * q (edgeVertex 123 0) 4 -
      q (edgeVertex 123 0) i.castSucc * q (edgeVertex 123 1) 4 =
        multiplier 123 * direction 123 i := by decide +kernel

theorem direction_scale_124 : ∀ i : Fin 4,
    q (edgeVertex 124 1) i.castSucc * q (edgeVertex 124 0) 4 -
      q (edgeVertex 124 0) i.castSucc * q (edgeVertex 124 1) 4 =
        multiplier 124 * direction 124 i := by decide +kernel

theorem direction_scale_125 : ∀ i : Fin 4,
    q (edgeVertex 125 1) i.castSucc * q (edgeVertex 125 0) 4 -
      q (edgeVertex 125 0) i.castSucc * q (edgeVertex 125 1) 4 =
        multiplier 125 * direction 125 i := by decide +kernel

theorem direction_scale_126 : ∀ i : Fin 4,
    q (edgeVertex 126 1) i.castSucc * q (edgeVertex 126 0) 4 -
      q (edgeVertex 126 0) i.castSucc * q (edgeVertex 126 1) 4 =
        multiplier 126 * direction 126 i := by decide +kernel

theorem direction_scale_127 : ∀ i : Fin 4,
    q (edgeVertex 127 1) i.castSucc * q (edgeVertex 127 0) 4 -
      q (edgeVertex 127 0) i.castSucc * q (edgeVertex 127 1) 4 =
        multiplier 127 * direction 127 i := by decide +kernel

theorem direction_scale_128 : ∀ i : Fin 4,
    q (edgeVertex 128 1) i.castSucc * q (edgeVertex 128 0) 4 -
      q (edgeVertex 128 0) i.castSucc * q (edgeVertex 128 1) 4 =
        multiplier 128 * direction 128 i := by decide +kernel

theorem direction_scale_129 : ∀ i : Fin 4,
    q (edgeVertex 129 1) i.castSucc * q (edgeVertex 129 0) 4 -
      q (edgeVertex 129 0) i.castSucc * q (edgeVertex 129 1) 4 =
        multiplier 129 * direction 129 i := by decide +kernel

theorem direction_scale_130 : ∀ i : Fin 4,
    q (edgeVertex 130 1) i.castSucc * q (edgeVertex 130 0) 4 -
      q (edgeVertex 130 0) i.castSucc * q (edgeVertex 130 1) 4 =
        multiplier 130 * direction 130 i := by decide +kernel

theorem direction_scale_131 : ∀ i : Fin 4,
    q (edgeVertex 131 1) i.castSucc * q (edgeVertex 131 0) 4 -
      q (edgeVertex 131 0) i.castSucc * q (edgeVertex 131 1) 4 =
        multiplier 131 * direction 131 i := by decide +kernel

theorem direction_scale_132 : ∀ i : Fin 4,
    q (edgeVertex 132 1) i.castSucc * q (edgeVertex 132 0) 4 -
      q (edgeVertex 132 0) i.castSucc * q (edgeVertex 132 1) 4 =
        multiplier 132 * direction 132 i := by decide +kernel

theorem direction_scale_133 : ∀ i : Fin 4,
    q (edgeVertex 133 1) i.castSucc * q (edgeVertex 133 0) 4 -
      q (edgeVertex 133 0) i.castSucc * q (edgeVertex 133 1) 4 =
        multiplier 133 * direction 133 i := by decide +kernel

theorem direction_scale_134 : ∀ i : Fin 4,
    q (edgeVertex 134 1) i.castSucc * q (edgeVertex 134 0) 4 -
      q (edgeVertex 134 0) i.castSucc * q (edgeVertex 134 1) 4 =
        multiplier 134 * direction 134 i := by decide +kernel

theorem direction_scale_135 : ∀ i : Fin 4,
    q (edgeVertex 135 1) i.castSucc * q (edgeVertex 135 0) 4 -
      q (edgeVertex 135 0) i.castSucc * q (edgeVertex 135 1) 4 =
        multiplier 135 * direction 135 i := by decide +kernel

theorem direction_scale_136 : ∀ i : Fin 4,
    q (edgeVertex 136 1) i.castSucc * q (edgeVertex 136 0) 4 -
      q (edgeVertex 136 0) i.castSucc * q (edgeVertex 136 1) 4 =
        multiplier 136 * direction 136 i := by decide +kernel

theorem direction_scale_137 : ∀ i : Fin 4,
    q (edgeVertex 137 1) i.castSucc * q (edgeVertex 137 0) 4 -
      q (edgeVertex 137 0) i.castSucc * q (edgeVertex 137 1) 4 =
        multiplier 137 * direction 137 i := by decide +kernel

theorem direction_scale_138 : ∀ i : Fin 4,
    q (edgeVertex 138 1) i.castSucc * q (edgeVertex 138 0) 4 -
      q (edgeVertex 138 0) i.castSucc * q (edgeVertex 138 1) 4 =
        multiplier 138 * direction 138 i := by decide +kernel

theorem direction_scale_139 : ∀ i : Fin 4,
    q (edgeVertex 139 1) i.castSucc * q (edgeVertex 139 0) 4 -
      q (edgeVertex 139 0) i.castSucc * q (edgeVertex 139 1) 4 =
        multiplier 139 * direction 139 i := by decide +kernel

theorem direction_scale_140 : ∀ i : Fin 4,
    q (edgeVertex 140 1) i.castSucc * q (edgeVertex 140 0) 4 -
      q (edgeVertex 140 0) i.castSucc * q (edgeVertex 140 1) 4 =
        multiplier 140 * direction 140 i := by decide +kernel

theorem direction_scale_141 : ∀ i : Fin 4,
    q (edgeVertex 141 1) i.castSucc * q (edgeVertex 141 0) 4 -
      q (edgeVertex 141 0) i.castSucc * q (edgeVertex 141 1) 4 =
        multiplier 141 * direction 141 i := by decide +kernel

theorem direction_scale_142 : ∀ i : Fin 4,
    q (edgeVertex 142 1) i.castSucc * q (edgeVertex 142 0) 4 -
      q (edgeVertex 142 0) i.castSucc * q (edgeVertex 142 1) 4 =
        multiplier 142 * direction 142 i := by decide +kernel

theorem direction_scale_143 : ∀ i : Fin 4,
    q (edgeVertex 143 1) i.castSucc * q (edgeVertex 143 0) 4 -
      q (edgeVertex 143 0) i.castSucc * q (edgeVertex 143 1) 4 =
        multiplier 143 * direction 143 i := by decide +kernel

theorem direction_scale_144 : ∀ i : Fin 4,
    q (edgeVertex 144 1) i.castSucc * q (edgeVertex 144 0) 4 -
      q (edgeVertex 144 0) i.castSucc * q (edgeVertex 144 1) 4 =
        multiplier 144 * direction 144 i := by decide +kernel

theorem direction_scale_145 : ∀ i : Fin 4,
    q (edgeVertex 145 1) i.castSucc * q (edgeVertex 145 0) 4 -
      q (edgeVertex 145 0) i.castSucc * q (edgeVertex 145 1) 4 =
        multiplier 145 * direction 145 i := by decide +kernel

theorem direction_scale_146 : ∀ i : Fin 4,
    q (edgeVertex 146 1) i.castSucc * q (edgeVertex 146 0) 4 -
      q (edgeVertex 146 0) i.castSucc * q (edgeVertex 146 1) 4 =
        multiplier 146 * direction 146 i := by decide +kernel

theorem direction_scale_147 : ∀ i : Fin 4,
    q (edgeVertex 147 1) i.castSucc * q (edgeVertex 147 0) 4 -
      q (edgeVertex 147 0) i.castSucc * q (edgeVertex 147 1) 4 =
        multiplier 147 * direction 147 i := by decide +kernel

theorem direction_scale_148 : ∀ i : Fin 4,
    q (edgeVertex 148 1) i.castSucc * q (edgeVertex 148 0) 4 -
      q (edgeVertex 148 0) i.castSucc * q (edgeVertex 148 1) 4 =
        multiplier 148 * direction 148 i := by decide +kernel

theorem direction_scale_149 : ∀ i : Fin 4,
    q (edgeVertex 149 1) i.castSucc * q (edgeVertex 149 0) 4 -
      q (edgeVertex 149 0) i.castSucc * q (edgeVertex 149 1) 4 =
        multiplier 149 * direction 149 i := by decide +kernel

theorem direction_scale_150 : ∀ i : Fin 4,
    q (edgeVertex 150 1) i.castSucc * q (edgeVertex 150 0) 4 -
      q (edgeVertex 150 0) i.castSucc * q (edgeVertex 150 1) 4 =
        multiplier 150 * direction 150 i := by decide +kernel

theorem direction_scale_151 : ∀ i : Fin 4,
    q (edgeVertex 151 1) i.castSucc * q (edgeVertex 151 0) 4 -
      q (edgeVertex 151 0) i.castSucc * q (edgeVertex 151 1) 4 =
        multiplier 151 * direction 151 i := by decide +kernel

theorem direction_scale_152 : ∀ i : Fin 4,
    q (edgeVertex 152 1) i.castSucc * q (edgeVertex 152 0) 4 -
      q (edgeVertex 152 0) i.castSucc * q (edgeVertex 152 1) 4 =
        multiplier 152 * direction 152 i := by decide +kernel

theorem direction_scale_153 : ∀ i : Fin 4,
    q (edgeVertex 153 1) i.castSucc * q (edgeVertex 153 0) 4 -
      q (edgeVertex 153 0) i.castSucc * q (edgeVertex 153 1) 4 =
        multiplier 153 * direction 153 i := by decide +kernel

theorem direction_scale_154 : ∀ i : Fin 4,
    q (edgeVertex 154 1) i.castSucc * q (edgeVertex 154 0) 4 -
      q (edgeVertex 154 0) i.castSucc * q (edgeVertex 154 1) 4 =
        multiplier 154 * direction 154 i := by decide +kernel

theorem direction_scale_155 : ∀ i : Fin 4,
    q (edgeVertex 155 1) i.castSucc * q (edgeVertex 155 0) 4 -
      q (edgeVertex 155 0) i.castSucc * q (edgeVertex 155 1) 4 =
        multiplier 155 * direction 155 i := by decide +kernel

theorem direction_scale_156 : ∀ i : Fin 4,
    q (edgeVertex 156 1) i.castSucc * q (edgeVertex 156 0) 4 -
      q (edgeVertex 156 0) i.castSucc * q (edgeVertex 156 1) 4 =
        multiplier 156 * direction 156 i := by decide +kernel

theorem direction_scale_157 : ∀ i : Fin 4,
    q (edgeVertex 157 1) i.castSucc * q (edgeVertex 157 0) 4 -
      q (edgeVertex 157 0) i.castSucc * q (edgeVertex 157 1) 4 =
        multiplier 157 * direction 157 i := by decide +kernel

theorem direction_scale_158 : ∀ i : Fin 4,
    q (edgeVertex 158 1) i.castSucc * q (edgeVertex 158 0) 4 -
      q (edgeVertex 158 0) i.castSucc * q (edgeVertex 158 1) 4 =
        multiplier 158 * direction 158 i := by decide +kernel

theorem direction_scale_159 : ∀ i : Fin 4,
    q (edgeVertex 159 1) i.castSucc * q (edgeVertex 159 0) 4 -
      q (edgeVertex 159 0) i.castSucc * q (edgeVertex 159 1) 4 =
        multiplier 159 * direction 159 i := by decide +kernel

theorem direction_scale_160 : ∀ i : Fin 4,
    q (edgeVertex 160 1) i.castSucc * q (edgeVertex 160 0) 4 -
      q (edgeVertex 160 0) i.castSucc * q (edgeVertex 160 1) 4 =
        multiplier 160 * direction 160 i := by decide +kernel

theorem direction_scale_161 : ∀ i : Fin 4,
    q (edgeVertex 161 1) i.castSucc * q (edgeVertex 161 0) 4 -
      q (edgeVertex 161 0) i.castSucc * q (edgeVertex 161 1) 4 =
        multiplier 161 * direction 161 i := by decide +kernel

theorem direction_scale_162 : ∀ i : Fin 4,
    q (edgeVertex 162 1) i.castSucc * q (edgeVertex 162 0) 4 -
      q (edgeVertex 162 0) i.castSucc * q (edgeVertex 162 1) 4 =
        multiplier 162 * direction 162 i := by decide +kernel

theorem direction_scale_163 : ∀ i : Fin 4,
    q (edgeVertex 163 1) i.castSucc * q (edgeVertex 163 0) 4 -
      q (edgeVertex 163 0) i.castSucc * q (edgeVertex 163 1) 4 =
        multiplier 163 * direction 163 i := by decide +kernel

theorem direction_scale_164 : ∀ i : Fin 4,
    q (edgeVertex 164 1) i.castSucc * q (edgeVertex 164 0) 4 -
      q (edgeVertex 164 0) i.castSucc * q (edgeVertex 164 1) 4 =
        multiplier 164 * direction 164 i := by decide +kernel

theorem direction_scale_165 : ∀ i : Fin 4,
    q (edgeVertex 165 1) i.castSucc * q (edgeVertex 165 0) 4 -
      q (edgeVertex 165 0) i.castSucc * q (edgeVertex 165 1) 4 =
        multiplier 165 * direction 165 i := by decide +kernel

theorem direction_scale_166 : ∀ i : Fin 4,
    q (edgeVertex 166 1) i.castSucc * q (edgeVertex 166 0) 4 -
      q (edgeVertex 166 0) i.castSucc * q (edgeVertex 166 1) 4 =
        multiplier 166 * direction 166 i := by decide +kernel

theorem direction_scale_167 : ∀ i : Fin 4,
    q (edgeVertex 167 1) i.castSucc * q (edgeVertex 167 0) 4 -
      q (edgeVertex 167 0) i.castSucc * q (edgeVertex 167 1) 4 =
        multiplier 167 * direction 167 i := by decide +kernel

theorem direction_scale_168 : ∀ i : Fin 4,
    q (edgeVertex 168 1) i.castSucc * q (edgeVertex 168 0) 4 -
      q (edgeVertex 168 0) i.castSucc * q (edgeVertex 168 1) 4 =
        multiplier 168 * direction 168 i := by decide +kernel

theorem direction_scale_169 : ∀ i : Fin 4,
    q (edgeVertex 169 1) i.castSucc * q (edgeVertex 169 0) 4 -
      q (edgeVertex 169 0) i.castSucc * q (edgeVertex 169 1) 4 =
        multiplier 169 * direction 169 i := by decide +kernel

theorem direction_scale_170 : ∀ i : Fin 4,
    q (edgeVertex 170 1) i.castSucc * q (edgeVertex 170 0) 4 -
      q (edgeVertex 170 0) i.castSucc * q (edgeVertex 170 1) 4 =
        multiplier 170 * direction 170 i := by decide +kernel

theorem direction_scale_171 : ∀ i : Fin 4,
    q (edgeVertex 171 1) i.castSucc * q (edgeVertex 171 0) 4 -
      q (edgeVertex 171 0) i.castSucc * q (edgeVertex 171 1) 4 =
        multiplier 171 * direction 171 i := by decide +kernel

theorem direction_scale_172 : ∀ i : Fin 4,
    q (edgeVertex 172 1) i.castSucc * q (edgeVertex 172 0) 4 -
      q (edgeVertex 172 0) i.castSucc * q (edgeVertex 172 1) 4 =
        multiplier 172 * direction 172 i := by decide +kernel

theorem direction_scale_173 : ∀ i : Fin 4,
    q (edgeVertex 173 1) i.castSucc * q (edgeVertex 173 0) 4 -
      q (edgeVertex 173 0) i.castSucc * q (edgeVertex 173 1) 4 =
        multiplier 173 * direction 173 i := by decide +kernel

theorem direction_scale_174 : ∀ i : Fin 4,
    q (edgeVertex 174 1) i.castSucc * q (edgeVertex 174 0) 4 -
      q (edgeVertex 174 0) i.castSucc * q (edgeVertex 174 1) 4 =
        multiplier 174 * direction 174 i := by decide +kernel

theorem direction_scale_175 : ∀ i : Fin 4,
    q (edgeVertex 175 1) i.castSucc * q (edgeVertex 175 0) 4 -
      q (edgeVertex 175 0) i.castSucc * q (edgeVertex 175 1) 4 =
        multiplier 175 * direction 175 i := by decide +kernel

theorem direction_scale_176 : ∀ i : Fin 4,
    q (edgeVertex 176 1) i.castSucc * q (edgeVertex 176 0) 4 -
      q (edgeVertex 176 0) i.castSucc * q (edgeVertex 176 1) 4 =
        multiplier 176 * direction 176 i := by decide +kernel

theorem direction_scale_177 : ∀ i : Fin 4,
    q (edgeVertex 177 1) i.castSucc * q (edgeVertex 177 0) 4 -
      q (edgeVertex 177 0) i.castSucc * q (edgeVertex 177 1) 4 =
        multiplier 177 * direction 177 i := by decide +kernel

theorem direction_scale_178 : ∀ i : Fin 4,
    q (edgeVertex 178 1) i.castSucc * q (edgeVertex 178 0) 4 -
      q (edgeVertex 178 0) i.castSucc * q (edgeVertex 178 1) 4 =
        multiplier 178 * direction 178 i := by decide +kernel

theorem direction_scale_179 : ∀ i : Fin 4,
    q (edgeVertex 179 1) i.castSucc * q (edgeVertex 179 0) 4 -
      q (edgeVertex 179 0) i.castSucc * q (edgeVertex 179 1) 4 =
        multiplier 179 * direction 179 i := by decide +kernel

theorem direction_scale_180 : ∀ i : Fin 4,
    q (edgeVertex 180 1) i.castSucc * q (edgeVertex 180 0) 4 -
      q (edgeVertex 180 0) i.castSucc * q (edgeVertex 180 1) 4 =
        multiplier 180 * direction 180 i := by decide +kernel

theorem direction_scale_181 : ∀ i : Fin 4,
    q (edgeVertex 181 1) i.castSucc * q (edgeVertex 181 0) 4 -
      q (edgeVertex 181 0) i.castSucc * q (edgeVertex 181 1) 4 =
        multiplier 181 * direction 181 i := by decide +kernel

theorem direction_scale_182 : ∀ i : Fin 4,
    q (edgeVertex 182 1) i.castSucc * q (edgeVertex 182 0) 4 -
      q (edgeVertex 182 0) i.castSucc * q (edgeVertex 182 1) 4 =
        multiplier 182 * direction 182 i := by decide +kernel

theorem direction_scale_183 : ∀ i : Fin 4,
    q (edgeVertex 183 1) i.castSucc * q (edgeVertex 183 0) 4 -
      q (edgeVertex 183 0) i.castSucc * q (edgeVertex 183 1) 4 =
        multiplier 183 * direction 183 i := by decide +kernel

theorem direction_scale_184 : ∀ i : Fin 4,
    q (edgeVertex 184 1) i.castSucc * q (edgeVertex 184 0) 4 -
      q (edgeVertex 184 0) i.castSucc * q (edgeVertex 184 1) 4 =
        multiplier 184 * direction 184 i := by decide +kernel

theorem direction_scale_185 : ∀ i : Fin 4,
    q (edgeVertex 185 1) i.castSucc * q (edgeVertex 185 0) 4 -
      q (edgeVertex 185 0) i.castSucc * q (edgeVertex 185 1) 4 =
        multiplier 185 * direction 185 i := by decide +kernel

theorem direction_scale_186 : ∀ i : Fin 4,
    q (edgeVertex 186 1) i.castSucc * q (edgeVertex 186 0) 4 -
      q (edgeVertex 186 0) i.castSucc * q (edgeVertex 186 1) 4 =
        multiplier 186 * direction 186 i := by decide +kernel

theorem direction_scale_187 : ∀ i : Fin 4,
    q (edgeVertex 187 1) i.castSucc * q (edgeVertex 187 0) 4 -
      q (edgeVertex 187 0) i.castSucc * q (edgeVertex 187 1) 4 =
        multiplier 187 * direction 187 i := by decide +kernel

theorem direction_scale_188 : ∀ i : Fin 4,
    q (edgeVertex 188 1) i.castSucc * q (edgeVertex 188 0) 4 -
      q (edgeVertex 188 0) i.castSucc * q (edgeVertex 188 1) 4 =
        multiplier 188 * direction 188 i := by decide +kernel

theorem direction_scale_189 : ∀ i : Fin 4,
    q (edgeVertex 189 1) i.castSucc * q (edgeVertex 189 0) 4 -
      q (edgeVertex 189 0) i.castSucc * q (edgeVertex 189 1) 4 =
        multiplier 189 * direction 189 i := by decide +kernel

theorem direction_scale_190 : ∀ i : Fin 4,
    q (edgeVertex 190 1) i.castSucc * q (edgeVertex 190 0) 4 -
      q (edgeVertex 190 0) i.castSucc * q (edgeVertex 190 1) 4 =
        multiplier 190 * direction 190 i := by decide +kernel

theorem direction_scale_191 : ∀ i : Fin 4,
    q (edgeVertex 191 1) i.castSucc * q (edgeVertex 191 0) 4 -
      q (edgeVertex 191 0) i.castSucc * q (edgeVertex 191 1) 4 =
        multiplier 191 * direction 191 i := by decide +kernel

theorem direction_scale_192 : ∀ i : Fin 4,
    q (edgeVertex 192 1) i.castSucc * q (edgeVertex 192 0) 4 -
      q (edgeVertex 192 0) i.castSucc * q (edgeVertex 192 1) 4 =
        multiplier 192 * direction 192 i := by decide +kernel

theorem direction_scale_193 : ∀ i : Fin 4,
    q (edgeVertex 193 1) i.castSucc * q (edgeVertex 193 0) 4 -
      q (edgeVertex 193 0) i.castSucc * q (edgeVertex 193 1) 4 =
        multiplier 193 * direction 193 i := by decide +kernel

theorem direction_scale_194 : ∀ i : Fin 4,
    q (edgeVertex 194 1) i.castSucc * q (edgeVertex 194 0) 4 -
      q (edgeVertex 194 0) i.castSucc * q (edgeVertex 194 1) 4 =
        multiplier 194 * direction 194 i := by decide +kernel

theorem direction_scale_195 : ∀ i : Fin 4,
    q (edgeVertex 195 1) i.castSucc * q (edgeVertex 195 0) 4 -
      q (edgeVertex 195 0) i.castSucc * q (edgeVertex 195 1) 4 =
        multiplier 195 * direction 195 i := by decide +kernel

theorem direction_scale_196 : ∀ i : Fin 4,
    q (edgeVertex 196 1) i.castSucc * q (edgeVertex 196 0) 4 -
      q (edgeVertex 196 0) i.castSucc * q (edgeVertex 196 1) 4 =
        multiplier 196 * direction 196 i := by decide +kernel

theorem direction_scale_197 : ∀ i : Fin 4,
    q (edgeVertex 197 1) i.castSucc * q (edgeVertex 197 0) 4 -
      q (edgeVertex 197 0) i.castSucc * q (edgeVertex 197 1) 4 =
        multiplier 197 * direction 197 i := by decide +kernel

theorem direction_scale_198 : ∀ i : Fin 4,
    q (edgeVertex 198 1) i.castSucc * q (edgeVertex 198 0) 4 -
      q (edgeVertex 198 0) i.castSucc * q (edgeVertex 198 1) 4 =
        multiplier 198 * direction 198 i := by decide +kernel

theorem direction_scale_199 : ∀ i : Fin 4,
    q (edgeVertex 199 1) i.castSucc * q (edgeVertex 199 0) 4 -
      q (edgeVertex 199 0) i.castSucc * q (edgeVertex 199 1) 4 =
        multiplier 199 * direction 199 i := by decide +kernel

theorem direction_scale_200 : ∀ i : Fin 4,
    q (edgeVertex 200 1) i.castSucc * q (edgeVertex 200 0) 4 -
      q (edgeVertex 200 0) i.castSucc * q (edgeVertex 200 1) 4 =
        multiplier 200 * direction 200 i := by decide +kernel

theorem direction_scale_201 : ∀ i : Fin 4,
    q (edgeVertex 201 1) i.castSucc * q (edgeVertex 201 0) 4 -
      q (edgeVertex 201 0) i.castSucc * q (edgeVertex 201 1) 4 =
        multiplier 201 * direction 201 i := by decide +kernel

theorem direction_scale_202 : ∀ i : Fin 4,
    q (edgeVertex 202 1) i.castSucc * q (edgeVertex 202 0) 4 -
      q (edgeVertex 202 0) i.castSucc * q (edgeVertex 202 1) 4 =
        multiplier 202 * direction 202 i := by decide +kernel

theorem direction_scale_203 : ∀ i : Fin 4,
    q (edgeVertex 203 1) i.castSucc * q (edgeVertex 203 0) 4 -
      q (edgeVertex 203 0) i.castSucc * q (edgeVertex 203 1) 4 =
        multiplier 203 * direction 203 i := by decide +kernel

theorem direction_scale_204 : ∀ i : Fin 4,
    q (edgeVertex 204 1) i.castSucc * q (edgeVertex 204 0) 4 -
      q (edgeVertex 204 0) i.castSucc * q (edgeVertex 204 1) 4 =
        multiplier 204 * direction 204 i := by decide +kernel

theorem direction_scale_205 : ∀ i : Fin 4,
    q (edgeVertex 205 1) i.castSucc * q (edgeVertex 205 0) 4 -
      q (edgeVertex 205 0) i.castSucc * q (edgeVertex 205 1) 4 =
        multiplier 205 * direction 205 i := by decide +kernel

theorem direction_scale_206 : ∀ i : Fin 4,
    q (edgeVertex 206 1) i.castSucc * q (edgeVertex 206 0) 4 -
      q (edgeVertex 206 0) i.castSucc * q (edgeVertex 206 1) 4 =
        multiplier 206 * direction 206 i := by decide +kernel

theorem direction_scale_207 : ∀ i : Fin 4,
    q (edgeVertex 207 1) i.castSucc * q (edgeVertex 207 0) 4 -
      q (edgeVertex 207 0) i.castSucc * q (edgeVertex 207 1) 4 =
        multiplier 207 * direction 207 i := by decide +kernel

theorem direction_scale_208 : ∀ i : Fin 4,
    q (edgeVertex 208 1) i.castSucc * q (edgeVertex 208 0) 4 -
      q (edgeVertex 208 0) i.castSucc * q (edgeVertex 208 1) 4 =
        multiplier 208 * direction 208 i := by decide +kernel

theorem direction_scale_209 : ∀ i : Fin 4,
    q (edgeVertex 209 1) i.castSucc * q (edgeVertex 209 0) 4 -
      q (edgeVertex 209 0) i.castSucc * q (edgeVertex 209 1) 4 =
        multiplier 209 * direction 209 i := by decide +kernel

theorem direction_scale_210 : ∀ i : Fin 4,
    q (edgeVertex 210 1) i.castSucc * q (edgeVertex 210 0) 4 -
      q (edgeVertex 210 0) i.castSucc * q (edgeVertex 210 1) 4 =
        multiplier 210 * direction 210 i := by decide +kernel

theorem direction_scale_211 : ∀ i : Fin 4,
    q (edgeVertex 211 1) i.castSucc * q (edgeVertex 211 0) 4 -
      q (edgeVertex 211 0) i.castSucc * q (edgeVertex 211 1) 4 =
        multiplier 211 * direction 211 i := by decide +kernel

theorem direction_scale_212 : ∀ i : Fin 4,
    q (edgeVertex 212 1) i.castSucc * q (edgeVertex 212 0) 4 -
      q (edgeVertex 212 0) i.castSucc * q (edgeVertex 212 1) 4 =
        multiplier 212 * direction 212 i := by decide +kernel

theorem direction_scale_213 : ∀ i : Fin 4,
    q (edgeVertex 213 1) i.castSucc * q (edgeVertex 213 0) 4 -
      q (edgeVertex 213 0) i.castSucc * q (edgeVertex 213 1) 4 =
        multiplier 213 * direction 213 i := by decide +kernel

theorem direction_scale_214 : ∀ i : Fin 4,
    q (edgeVertex 214 1) i.castSucc * q (edgeVertex 214 0) 4 -
      q (edgeVertex 214 0) i.castSucc * q (edgeVertex 214 1) 4 =
        multiplier 214 * direction 214 i := by decide +kernel

theorem direction_scale_215 : ∀ i : Fin 4,
    q (edgeVertex 215 1) i.castSucc * q (edgeVertex 215 0) 4 -
      q (edgeVertex 215 0) i.castSucc * q (edgeVertex 215 1) 4 =
        multiplier 215 * direction 215 i := by decide +kernel

theorem direction_scale_216 : ∀ i : Fin 4,
    q (edgeVertex 216 1) i.castSucc * q (edgeVertex 216 0) 4 -
      q (edgeVertex 216 0) i.castSucc * q (edgeVertex 216 1) 4 =
        multiplier 216 * direction 216 i := by decide +kernel

theorem direction_scale_217 : ∀ i : Fin 4,
    q (edgeVertex 217 1) i.castSucc * q (edgeVertex 217 0) 4 -
      q (edgeVertex 217 0) i.castSucc * q (edgeVertex 217 1) 4 =
        multiplier 217 * direction 217 i := by decide +kernel

theorem direction_scale_218 : ∀ i : Fin 4,
    q (edgeVertex 218 1) i.castSucc * q (edgeVertex 218 0) 4 -
      q (edgeVertex 218 0) i.castSucc * q (edgeVertex 218 1) 4 =
        multiplier 218 * direction 218 i := by decide +kernel

theorem direction_scale_219 : ∀ i : Fin 4,
    q (edgeVertex 219 1) i.castSucc * q (edgeVertex 219 0) 4 -
      q (edgeVertex 219 0) i.castSucc * q (edgeVertex 219 1) 4 =
        multiplier 219 * direction 219 i := by decide +kernel

theorem direction_scale_220 : ∀ i : Fin 4,
    q (edgeVertex 220 1) i.castSucc * q (edgeVertex 220 0) 4 -
      q (edgeVertex 220 0) i.castSucc * q (edgeVertex 220 1) 4 =
        multiplier 220 * direction 220 i := by decide +kernel

theorem direction_scale_221 : ∀ i : Fin 4,
    q (edgeVertex 221 1) i.castSucc * q (edgeVertex 221 0) 4 -
      q (edgeVertex 221 0) i.castSucc * q (edgeVertex 221 1) 4 =
        multiplier 221 * direction 221 i := by decide +kernel

theorem direction_scale_222 : ∀ i : Fin 4,
    q (edgeVertex 222 1) i.castSucc * q (edgeVertex 222 0) 4 -
      q (edgeVertex 222 0) i.castSucc * q (edgeVertex 222 1) 4 =
        multiplier 222 * direction 222 i := by decide +kernel

theorem direction_scale_223 : ∀ i : Fin 4,
    q (edgeVertex 223 1) i.castSucc * q (edgeVertex 223 0) 4 -
      q (edgeVertex 223 0) i.castSucc * q (edgeVertex 223 1) 4 =
        multiplier 223 * direction 223 i := by decide +kernel

theorem direction_scale_224 : ∀ i : Fin 4,
    q (edgeVertex 224 1) i.castSucc * q (edgeVertex 224 0) 4 -
      q (edgeVertex 224 0) i.castSucc * q (edgeVertex 224 1) 4 =
        multiplier 224 * direction 224 i := by decide +kernel

theorem direction_scale_225 : ∀ i : Fin 4,
    q (edgeVertex 225 1) i.castSucc * q (edgeVertex 225 0) 4 -
      q (edgeVertex 225 0) i.castSucc * q (edgeVertex 225 1) 4 =
        multiplier 225 * direction 225 i := by decide +kernel

theorem direction_scale_226 : ∀ i : Fin 4,
    q (edgeVertex 226 1) i.castSucc * q (edgeVertex 226 0) 4 -
      q (edgeVertex 226 0) i.castSucc * q (edgeVertex 226 1) 4 =
        multiplier 226 * direction 226 i := by decide +kernel

theorem direction_scale_227 : ∀ i : Fin 4,
    q (edgeVertex 227 1) i.castSucc * q (edgeVertex 227 0) 4 -
      q (edgeVertex 227 0) i.castSucc * q (edgeVertex 227 1) 4 =
        multiplier 227 * direction 227 i := by decide +kernel

theorem direction_scale_228 : ∀ i : Fin 4,
    q (edgeVertex 228 1) i.castSucc * q (edgeVertex 228 0) 4 -
      q (edgeVertex 228 0) i.castSucc * q (edgeVertex 228 1) 4 =
        multiplier 228 * direction 228 i := by decide +kernel

theorem direction_scale_229 : ∀ i : Fin 4,
    q (edgeVertex 229 1) i.castSucc * q (edgeVertex 229 0) 4 -
      q (edgeVertex 229 0) i.castSucc * q (edgeVertex 229 1) 4 =
        multiplier 229 * direction 229 i := by decide +kernel

theorem direction_scale_230 : ∀ i : Fin 4,
    q (edgeVertex 230 1) i.castSucc * q (edgeVertex 230 0) 4 -
      q (edgeVertex 230 0) i.castSucc * q (edgeVertex 230 1) 4 =
        multiplier 230 * direction 230 i := by decide +kernel

theorem direction_scale_231 : ∀ i : Fin 4,
    q (edgeVertex 231 1) i.castSucc * q (edgeVertex 231 0) 4 -
      q (edgeVertex 231 0) i.castSucc * q (edgeVertex 231 1) 4 =
        multiplier 231 * direction 231 i := by decide +kernel

theorem direction_scale_232 : ∀ i : Fin 4,
    q (edgeVertex 232 1) i.castSucc * q (edgeVertex 232 0) 4 -
      q (edgeVertex 232 0) i.castSucc * q (edgeVertex 232 1) 4 =
        multiplier 232 * direction 232 i := by decide +kernel

theorem direction_scale_233 : ∀ i : Fin 4,
    q (edgeVertex 233 1) i.castSucc * q (edgeVertex 233 0) 4 -
      q (edgeVertex 233 0) i.castSucc * q (edgeVertex 233 1) 4 =
        multiplier 233 * direction 233 i := by decide +kernel

theorem direction_scale_234 : ∀ i : Fin 4,
    q (edgeVertex 234 1) i.castSucc * q (edgeVertex 234 0) 4 -
      q (edgeVertex 234 0) i.castSucc * q (edgeVertex 234 1) 4 =
        multiplier 234 * direction 234 i := by decide +kernel

theorem direction_scale_235 : ∀ i : Fin 4,
    q (edgeVertex 235 1) i.castSucc * q (edgeVertex 235 0) 4 -
      q (edgeVertex 235 0) i.castSucc * q (edgeVertex 235 1) 4 =
        multiplier 235 * direction 235 i := by decide +kernel

theorem direction_scale_236 : ∀ i : Fin 4,
    q (edgeVertex 236 1) i.castSucc * q (edgeVertex 236 0) 4 -
      q (edgeVertex 236 0) i.castSucc * q (edgeVertex 236 1) 4 =
        multiplier 236 * direction 236 i := by decide +kernel

theorem direction_scale_237 : ∀ i : Fin 4,
    q (edgeVertex 237 1) i.castSucc * q (edgeVertex 237 0) 4 -
      q (edgeVertex 237 0) i.castSucc * q (edgeVertex 237 1) 4 =
        multiplier 237 * direction 237 i := by decide +kernel

theorem direction_scale_238 : ∀ i : Fin 4,
    q (edgeVertex 238 1) i.castSucc * q (edgeVertex 238 0) 4 -
      q (edgeVertex 238 0) i.castSucc * q (edgeVertex 238 1) 4 =
        multiplier 238 * direction 238 i := by decide +kernel

theorem direction_scale_239 : ∀ i : Fin 4,
    q (edgeVertex 239 1) i.castSucc * q (edgeVertex 239 0) 4 -
      q (edgeVertex 239 0) i.castSucc * q (edgeVertex 239 1) 4 =
        multiplier 239 * direction 239 i := by decide +kernel

theorem direction_scale_240 : ∀ i : Fin 4,
    q (edgeVertex 240 1) i.castSucc * q (edgeVertex 240 0) 4 -
      q (edgeVertex 240 0) i.castSucc * q (edgeVertex 240 1) 4 =
        multiplier 240 * direction 240 i := by decide +kernel

theorem direction_scale_241 : ∀ i : Fin 4,
    q (edgeVertex 241 1) i.castSucc * q (edgeVertex 241 0) 4 -
      q (edgeVertex 241 0) i.castSucc * q (edgeVertex 241 1) 4 =
        multiplier 241 * direction 241 i := by decide +kernel

theorem direction_scale_242 : ∀ i : Fin 4,
    q (edgeVertex 242 1) i.castSucc * q (edgeVertex 242 0) 4 -
      q (edgeVertex 242 0) i.castSucc * q (edgeVertex 242 1) 4 =
        multiplier 242 * direction 242 i := by decide +kernel

theorem direction_scale_243 : ∀ i : Fin 4,
    q (edgeVertex 243 1) i.castSucc * q (edgeVertex 243 0) 4 -
      q (edgeVertex 243 0) i.castSucc * q (edgeVertex 243 1) 4 =
        multiplier 243 * direction 243 i := by decide +kernel

theorem direction_scale_244 : ∀ i : Fin 4,
    q (edgeVertex 244 1) i.castSucc * q (edgeVertex 244 0) 4 -
      q (edgeVertex 244 0) i.castSucc * q (edgeVertex 244 1) 4 =
        multiplier 244 * direction 244 i := by decide +kernel

theorem direction_scale_245 : ∀ i : Fin 4,
    q (edgeVertex 245 1) i.castSucc * q (edgeVertex 245 0) 4 -
      q (edgeVertex 245 0) i.castSucc * q (edgeVertex 245 1) 4 =
        multiplier 245 * direction 245 i := by decide +kernel

theorem direction_scale_246 : ∀ i : Fin 4,
    q (edgeVertex 246 1) i.castSucc * q (edgeVertex 246 0) 4 -
      q (edgeVertex 246 0) i.castSucc * q (edgeVertex 246 1) 4 =
        multiplier 246 * direction 246 i := by decide +kernel

theorem direction_scale_247 : ∀ i : Fin 4,
    q (edgeVertex 247 1) i.castSucc * q (edgeVertex 247 0) 4 -
      q (edgeVertex 247 0) i.castSucc * q (edgeVertex 247 1) 4 =
        multiplier 247 * direction 247 i := by decide +kernel

theorem direction_scale_248 : ∀ i : Fin 4,
    q (edgeVertex 248 1) i.castSucc * q (edgeVertex 248 0) 4 -
      q (edgeVertex 248 0) i.castSucc * q (edgeVertex 248 1) 4 =
        multiplier 248 * direction 248 i := by decide +kernel

theorem direction_scale_249 : ∀ i : Fin 4,
    q (edgeVertex 249 1) i.castSucc * q (edgeVertex 249 0) 4 -
      q (edgeVertex 249 0) i.castSucc * q (edgeVertex 249 1) 4 =
        multiplier 249 * direction 249 i := by decide +kernel

theorem direction_scale_250 : ∀ i : Fin 4,
    q (edgeVertex 250 1) i.castSucc * q (edgeVertex 250 0) 4 -
      q (edgeVertex 250 0) i.castSucc * q (edgeVertex 250 1) 4 =
        multiplier 250 * direction 250 i := by decide +kernel

theorem direction_scale_251 : ∀ i : Fin 4,
    q (edgeVertex 251 1) i.castSucc * q (edgeVertex 251 0) 4 -
      q (edgeVertex 251 0) i.castSucc * q (edgeVertex 251 1) 4 =
        multiplier 251 * direction 251 i := by decide +kernel

theorem direction_scale_252 : ∀ i : Fin 4,
    q (edgeVertex 252 1) i.castSucc * q (edgeVertex 252 0) 4 -
      q (edgeVertex 252 0) i.castSucc * q (edgeVertex 252 1) 4 =
        multiplier 252 * direction 252 i := by decide +kernel

theorem direction_scale_253 : ∀ i : Fin 4,
    q (edgeVertex 253 1) i.castSucc * q (edgeVertex 253 0) 4 -
      q (edgeVertex 253 0) i.castSucc * q (edgeVertex 253 1) 4 =
        multiplier 253 * direction 253 i := by decide +kernel

theorem direction_scale_254 : ∀ i : Fin 4,
    q (edgeVertex 254 1) i.castSucc * q (edgeVertex 254 0) 4 -
      q (edgeVertex 254 0) i.castSucc * q (edgeVertex 254 1) 4 =
        multiplier 254 * direction 254 i := by decide +kernel

theorem direction_scale_255 : ∀ i : Fin 4,
    q (edgeVertex 255 1) i.castSucc * q (edgeVertex 255 0) 4 -
      q (edgeVertex 255 0) i.castSucc * q (edgeVertex 255 1) 4 =
        multiplier 255 * direction 255 i := by decide +kernel

theorem direction_scale_256 : ∀ i : Fin 4,
    q (edgeVertex 256 1) i.castSucc * q (edgeVertex 256 0) 4 -
      q (edgeVertex 256 0) i.castSucc * q (edgeVertex 256 1) 4 =
        multiplier 256 * direction 256 i := by decide +kernel

theorem direction_scale_257 : ∀ i : Fin 4,
    q (edgeVertex 257 1) i.castSucc * q (edgeVertex 257 0) 4 -
      q (edgeVertex 257 0) i.castSucc * q (edgeVertex 257 1) 4 =
        multiplier 257 * direction 257 i := by decide +kernel

theorem direction_scale_258 : ∀ i : Fin 4,
    q (edgeVertex 258 1) i.castSucc * q (edgeVertex 258 0) 4 -
      q (edgeVertex 258 0) i.castSucc * q (edgeVertex 258 1) 4 =
        multiplier 258 * direction 258 i := by decide +kernel

theorem direction_scale_259 : ∀ i : Fin 4,
    q (edgeVertex 259 1) i.castSucc * q (edgeVertex 259 0) 4 -
      q (edgeVertex 259 0) i.castSucc * q (edgeVertex 259 1) 4 =
        multiplier 259 * direction 259 i := by decide +kernel

theorem direction_scale_260 : ∀ i : Fin 4,
    q (edgeVertex 260 1) i.castSucc * q (edgeVertex 260 0) 4 -
      q (edgeVertex 260 0) i.castSucc * q (edgeVertex 260 1) 4 =
        multiplier 260 * direction 260 i := by decide +kernel

theorem direction_scale_261 : ∀ i : Fin 4,
    q (edgeVertex 261 1) i.castSucc * q (edgeVertex 261 0) 4 -
      q (edgeVertex 261 0) i.castSucc * q (edgeVertex 261 1) 4 =
        multiplier 261 * direction 261 i := by decide +kernel

theorem direction_scale_262 : ∀ i : Fin 4,
    q (edgeVertex 262 1) i.castSucc * q (edgeVertex 262 0) 4 -
      q (edgeVertex 262 0) i.castSucc * q (edgeVertex 262 1) 4 =
        multiplier 262 * direction 262 i := by decide +kernel

theorem direction_scale_263 : ∀ i : Fin 4,
    q (edgeVertex 263 1) i.castSucc * q (edgeVertex 263 0) 4 -
      q (edgeVertex 263 0) i.castSucc * q (edgeVertex 263 1) 4 =
        multiplier 263 * direction 263 i := by decide +kernel

theorem direction_scale_264 : ∀ i : Fin 4,
    q (edgeVertex 264 1) i.castSucc * q (edgeVertex 264 0) 4 -
      q (edgeVertex 264 0) i.castSucc * q (edgeVertex 264 1) 4 =
        multiplier 264 * direction 264 i := by decide +kernel

theorem direction_scale_265 : ∀ i : Fin 4,
    q (edgeVertex 265 1) i.castSucc * q (edgeVertex 265 0) 4 -
      q (edgeVertex 265 0) i.castSucc * q (edgeVertex 265 1) 4 =
        multiplier 265 * direction 265 i := by decide +kernel

theorem direction_scale_266 : ∀ i : Fin 4,
    q (edgeVertex 266 1) i.castSucc * q (edgeVertex 266 0) 4 -
      q (edgeVertex 266 0) i.castSucc * q (edgeVertex 266 1) 4 =
        multiplier 266 * direction 266 i := by decide +kernel

theorem direction_scale_267 : ∀ i : Fin 4,
    q (edgeVertex 267 1) i.castSucc * q (edgeVertex 267 0) 4 -
      q (edgeVertex 267 0) i.castSucc * q (edgeVertex 267 1) 4 =
        multiplier 267 * direction 267 i := by decide +kernel

theorem direction_scale_268 : ∀ i : Fin 4,
    q (edgeVertex 268 1) i.castSucc * q (edgeVertex 268 0) 4 -
      q (edgeVertex 268 0) i.castSucc * q (edgeVertex 268 1) 4 =
        multiplier 268 * direction 268 i := by decide +kernel

theorem direction_scale_269 : ∀ i : Fin 4,
    q (edgeVertex 269 1) i.castSucc * q (edgeVertex 269 0) 4 -
      q (edgeVertex 269 0) i.castSucc * q (edgeVertex 269 1) 4 =
        multiplier 269 * direction 269 i := by decide +kernel

theorem direction_scale_270 : ∀ i : Fin 4,
    q (edgeVertex 270 1) i.castSucc * q (edgeVertex 270 0) 4 -
      q (edgeVertex 270 0) i.castSucc * q (edgeVertex 270 1) 4 =
        multiplier 270 * direction 270 i := by decide +kernel

theorem direction_scale_271 : ∀ i : Fin 4,
    q (edgeVertex 271 1) i.castSucc * q (edgeVertex 271 0) 4 -
      q (edgeVertex 271 0) i.castSucc * q (edgeVertex 271 1) 4 =
        multiplier 271 * direction 271 i := by decide +kernel

theorem direction_scale_272 : ∀ i : Fin 4,
    q (edgeVertex 272 1) i.castSucc * q (edgeVertex 272 0) 4 -
      q (edgeVertex 272 0) i.castSucc * q (edgeVertex 272 1) 4 =
        multiplier 272 * direction 272 i := by decide +kernel

theorem direction_scale_273 : ∀ i : Fin 4,
    q (edgeVertex 273 1) i.castSucc * q (edgeVertex 273 0) 4 -
      q (edgeVertex 273 0) i.castSucc * q (edgeVertex 273 1) 4 =
        multiplier 273 * direction 273 i := by decide +kernel

theorem direction_scale_274 : ∀ i : Fin 4,
    q (edgeVertex 274 1) i.castSucc * q (edgeVertex 274 0) 4 -
      q (edgeVertex 274 0) i.castSucc * q (edgeVertex 274 1) 4 =
        multiplier 274 * direction 274 i := by decide +kernel

theorem direction_scale_275 : ∀ i : Fin 4,
    q (edgeVertex 275 1) i.castSucc * q (edgeVertex 275 0) 4 -
      q (edgeVertex 275 0) i.castSucc * q (edgeVertex 275 1) 4 =
        multiplier 275 * direction 275 i := by decide +kernel

theorem direction_scale_276 : ∀ i : Fin 4,
    q (edgeVertex 276 1) i.castSucc * q (edgeVertex 276 0) 4 -
      q (edgeVertex 276 0) i.castSucc * q (edgeVertex 276 1) 4 =
        multiplier 276 * direction 276 i := by decide +kernel

theorem direction_scale_277 : ∀ i : Fin 4,
    q (edgeVertex 277 1) i.castSucc * q (edgeVertex 277 0) 4 -
      q (edgeVertex 277 0) i.castSucc * q (edgeVertex 277 1) 4 =
        multiplier 277 * direction 277 i := by decide +kernel

theorem direction_scale_278 : ∀ i : Fin 4,
    q (edgeVertex 278 1) i.castSucc * q (edgeVertex 278 0) 4 -
      q (edgeVertex 278 0) i.castSucc * q (edgeVertex 278 1) 4 =
        multiplier 278 * direction 278 i := by decide +kernel

theorem direction_scale_279 : ∀ i : Fin 4,
    q (edgeVertex 279 1) i.castSucc * q (edgeVertex 279 0) 4 -
      q (edgeVertex 279 0) i.castSucc * q (edgeVertex 279 1) 4 =
        multiplier 279 * direction 279 i := by decide +kernel

theorem direction_scale_280 : ∀ i : Fin 4,
    q (edgeVertex 280 1) i.castSucc * q (edgeVertex 280 0) 4 -
      q (edgeVertex 280 0) i.castSucc * q (edgeVertex 280 1) 4 =
        multiplier 280 * direction 280 i := by decide +kernel

theorem direction_scale_281 : ∀ i : Fin 4,
    q (edgeVertex 281 1) i.castSucc * q (edgeVertex 281 0) 4 -
      q (edgeVertex 281 0) i.castSucc * q (edgeVertex 281 1) 4 =
        multiplier 281 * direction 281 i := by decide +kernel

theorem direction_scale_282 : ∀ i : Fin 4,
    q (edgeVertex 282 1) i.castSucc * q (edgeVertex 282 0) 4 -
      q (edgeVertex 282 0) i.castSucc * q (edgeVertex 282 1) 4 =
        multiplier 282 * direction 282 i := by decide +kernel

theorem direction_scale_283 : ∀ i : Fin 4,
    q (edgeVertex 283 1) i.castSucc * q (edgeVertex 283 0) 4 -
      q (edgeVertex 283 0) i.castSucc * q (edgeVertex 283 1) 4 =
        multiplier 283 * direction 283 i := by decide +kernel

theorem direction_scale_284 : ∀ i : Fin 4,
    q (edgeVertex 284 1) i.castSucc * q (edgeVertex 284 0) 4 -
      q (edgeVertex 284 0) i.castSucc * q (edgeVertex 284 1) 4 =
        multiplier 284 * direction 284 i := by decide +kernel

theorem direction_scale_285 : ∀ i : Fin 4,
    q (edgeVertex 285 1) i.castSucc * q (edgeVertex 285 0) 4 -
      q (edgeVertex 285 0) i.castSucc * q (edgeVertex 285 1) 4 =
        multiplier 285 * direction 285 i := by decide +kernel

theorem direction_scale_286 : ∀ i : Fin 4,
    q (edgeVertex 286 1) i.castSucc * q (edgeVertex 286 0) 4 -
      q (edgeVertex 286 0) i.castSucc * q (edgeVertex 286 1) 4 =
        multiplier 286 * direction 286 i := by decide +kernel

theorem direction_scale_287 : ∀ i : Fin 4,
    q (edgeVertex 287 1) i.castSucc * q (edgeVertex 287 0) 4 -
      q (edgeVertex 287 0) i.castSucc * q (edgeVertex 287 1) 4 =
        multiplier 287 * direction 287 i := by decide +kernel

theorem direction_scale_288 : ∀ i : Fin 4,
    q (edgeVertex 288 1) i.castSucc * q (edgeVertex 288 0) 4 -
      q (edgeVertex 288 0) i.castSucc * q (edgeVertex 288 1) 4 =
        multiplier 288 * direction 288 i := by decide +kernel

theorem direction_scale_289 : ∀ i : Fin 4,
    q (edgeVertex 289 1) i.castSucc * q (edgeVertex 289 0) 4 -
      q (edgeVertex 289 0) i.castSucc * q (edgeVertex 289 1) 4 =
        multiplier 289 * direction 289 i := by decide +kernel

theorem direction_scale_290 : ∀ i : Fin 4,
    q (edgeVertex 290 1) i.castSucc * q (edgeVertex 290 0) 4 -
      q (edgeVertex 290 0) i.castSucc * q (edgeVertex 290 1) 4 =
        multiplier 290 * direction 290 i := by decide +kernel

theorem direction_scale_291 : ∀ i : Fin 4,
    q (edgeVertex 291 1) i.castSucc * q (edgeVertex 291 0) 4 -
      q (edgeVertex 291 0) i.castSucc * q (edgeVertex 291 1) 4 =
        multiplier 291 * direction 291 i := by decide +kernel

theorem direction_scale_292 : ∀ i : Fin 4,
    q (edgeVertex 292 1) i.castSucc * q (edgeVertex 292 0) 4 -
      q (edgeVertex 292 0) i.castSucc * q (edgeVertex 292 1) 4 =
        multiplier 292 * direction 292 i := by decide +kernel

theorem direction_scale_293 : ∀ i : Fin 4,
    q (edgeVertex 293 1) i.castSucc * q (edgeVertex 293 0) 4 -
      q (edgeVertex 293 0) i.castSucc * q (edgeVertex 293 1) 4 =
        multiplier 293 * direction 293 i := by decide +kernel

theorem direction_scale_294 : ∀ i : Fin 4,
    q (edgeVertex 294 1) i.castSucc * q (edgeVertex 294 0) 4 -
      q (edgeVertex 294 0) i.castSucc * q (edgeVertex 294 1) 4 =
        multiplier 294 * direction 294 i := by decide +kernel

theorem direction_scale_295 : ∀ i : Fin 4,
    q (edgeVertex 295 1) i.castSucc * q (edgeVertex 295 0) 4 -
      q (edgeVertex 295 0) i.castSucc * q (edgeVertex 295 1) 4 =
        multiplier 295 * direction 295 i := by decide +kernel

theorem direction_scale_296 : ∀ i : Fin 4,
    q (edgeVertex 296 1) i.castSucc * q (edgeVertex 296 0) 4 -
      q (edgeVertex 296 0) i.castSucc * q (edgeVertex 296 1) 4 =
        multiplier 296 * direction 296 i := by decide +kernel

theorem direction_scale_297 : ∀ i : Fin 4,
    q (edgeVertex 297 1) i.castSucc * q (edgeVertex 297 0) 4 -
      q (edgeVertex 297 0) i.castSucc * q (edgeVertex 297 1) 4 =
        multiplier 297 * direction 297 i := by decide +kernel

theorem direction_scale_298 : ∀ i : Fin 4,
    q (edgeVertex 298 1) i.castSucc * q (edgeVertex 298 0) 4 -
      q (edgeVertex 298 0) i.castSucc * q (edgeVertex 298 1) 4 =
        multiplier 298 * direction 298 i := by decide +kernel

theorem direction_scale_299 : ∀ i : Fin 4,
    q (edgeVertex 299 1) i.castSucc * q (edgeVertex 299 0) 4 -
      q (edgeVertex 299 0) i.castSucc * q (edgeVertex 299 1) 4 =
        multiplier 299 * direction 299 i := by decide +kernel

theorem direction_scale_300 : ∀ i : Fin 4,
    q (edgeVertex 300 1) i.castSucc * q (edgeVertex 300 0) 4 -
      q (edgeVertex 300 0) i.castSucc * q (edgeVertex 300 1) 4 =
        multiplier 300 * direction 300 i := by decide +kernel

theorem direction_scale_301 : ∀ i : Fin 4,
    q (edgeVertex 301 1) i.castSucc * q (edgeVertex 301 0) 4 -
      q (edgeVertex 301 0) i.castSucc * q (edgeVertex 301 1) 4 =
        multiplier 301 * direction 301 i := by decide +kernel

theorem direction_scale_302 : ∀ i : Fin 4,
    q (edgeVertex 302 1) i.castSucc * q (edgeVertex 302 0) 4 -
      q (edgeVertex 302 0) i.castSucc * q (edgeVertex 302 1) 4 =
        multiplier 302 * direction 302 i := by decide +kernel

theorem direction_scale_303 : ∀ i : Fin 4,
    q (edgeVertex 303 1) i.castSucc * q (edgeVertex 303 0) 4 -
      q (edgeVertex 303 0) i.castSucc * q (edgeVertex 303 1) 4 =
        multiplier 303 * direction 303 i := by decide +kernel

theorem direction_scale_304 : ∀ i : Fin 4,
    q (edgeVertex 304 1) i.castSucc * q (edgeVertex 304 0) 4 -
      q (edgeVertex 304 0) i.castSucc * q (edgeVertex 304 1) 4 =
        multiplier 304 * direction 304 i := by decide +kernel

theorem direction_scale_305 : ∀ i : Fin 4,
    q (edgeVertex 305 1) i.castSucc * q (edgeVertex 305 0) 4 -
      q (edgeVertex 305 0) i.castSucc * q (edgeVertex 305 1) 4 =
        multiplier 305 * direction 305 i := by decide +kernel

theorem direction_scale_306 : ∀ i : Fin 4,
    q (edgeVertex 306 1) i.castSucc * q (edgeVertex 306 0) 4 -
      q (edgeVertex 306 0) i.castSucc * q (edgeVertex 306 1) 4 =
        multiplier 306 * direction 306 i := by decide +kernel

theorem direction_scale_307 : ∀ i : Fin 4,
    q (edgeVertex 307 1) i.castSucc * q (edgeVertex 307 0) 4 -
      q (edgeVertex 307 0) i.castSucc * q (edgeVertex 307 1) 4 =
        multiplier 307 * direction 307 i := by decide +kernel

theorem direction_scale_308 : ∀ i : Fin 4,
    q (edgeVertex 308 1) i.castSucc * q (edgeVertex 308 0) 4 -
      q (edgeVertex 308 0) i.castSucc * q (edgeVertex 308 1) 4 =
        multiplier 308 * direction 308 i := by decide +kernel

theorem direction_scale_309 : ∀ i : Fin 4,
    q (edgeVertex 309 1) i.castSucc * q (edgeVertex 309 0) 4 -
      q (edgeVertex 309 0) i.castSucc * q (edgeVertex 309 1) 4 =
        multiplier 309 * direction 309 i := by decide +kernel

theorem direction_scale_310 : ∀ i : Fin 4,
    q (edgeVertex 310 1) i.castSucc * q (edgeVertex 310 0) 4 -
      q (edgeVertex 310 0) i.castSucc * q (edgeVertex 310 1) 4 =
        multiplier 310 * direction 310 i := by decide +kernel

theorem direction_scale_311 : ∀ i : Fin 4,
    q (edgeVertex 311 1) i.castSucc * q (edgeVertex 311 0) 4 -
      q (edgeVertex 311 0) i.castSucc * q (edgeVertex 311 1) 4 =
        multiplier 311 * direction 311 i := by decide +kernel

theorem direction_scale_312 : ∀ i : Fin 4,
    q (edgeVertex 312 1) i.castSucc * q (edgeVertex 312 0) 4 -
      q (edgeVertex 312 0) i.castSucc * q (edgeVertex 312 1) 4 =
        multiplier 312 * direction 312 i := by decide +kernel

theorem direction_scale_313 : ∀ i : Fin 4,
    q (edgeVertex 313 1) i.castSucc * q (edgeVertex 313 0) 4 -
      q (edgeVertex 313 0) i.castSucc * q (edgeVertex 313 1) 4 =
        multiplier 313 * direction 313 i := by decide +kernel

theorem direction_scale_314 : ∀ i : Fin 4,
    q (edgeVertex 314 1) i.castSucc * q (edgeVertex 314 0) 4 -
      q (edgeVertex 314 0) i.castSucc * q (edgeVertex 314 1) 4 =
        multiplier 314 * direction 314 i := by decide +kernel

theorem direction_scale_315 : ∀ i : Fin 4,
    q (edgeVertex 315 1) i.castSucc * q (edgeVertex 315 0) 4 -
      q (edgeVertex 315 0) i.castSucc * q (edgeVertex 315 1) 4 =
        multiplier 315 * direction 315 i := by decide +kernel

theorem direction_scale_316 : ∀ i : Fin 4,
    q (edgeVertex 316 1) i.castSucc * q (edgeVertex 316 0) 4 -
      q (edgeVertex 316 0) i.castSucc * q (edgeVertex 316 1) 4 =
        multiplier 316 * direction 316 i := by decide +kernel

theorem direction_scale_317 : ∀ i : Fin 4,
    q (edgeVertex 317 1) i.castSucc * q (edgeVertex 317 0) 4 -
      q (edgeVertex 317 0) i.castSucc * q (edgeVertex 317 1) 4 =
        multiplier 317 * direction 317 i := by decide +kernel

theorem direction_scale_318 : ∀ i : Fin 4,
    q (edgeVertex 318 1) i.castSucc * q (edgeVertex 318 0) 4 -
      q (edgeVertex 318 0) i.castSucc * q (edgeVertex 318 1) 4 =
        multiplier 318 * direction 318 i := by decide +kernel

theorem direction_scale_319 : ∀ i : Fin 4,
    q (edgeVertex 319 1) i.castSucc * q (edgeVertex 319 0) 4 -
      q (edgeVertex 319 0) i.castSucc * q (edgeVertex 319 1) 4 =
        multiplier 319 * direction 319 i := by decide +kernel

theorem direction_scale_320 : ∀ i : Fin 4,
    q (edgeVertex 320 1) i.castSucc * q (edgeVertex 320 0) 4 -
      q (edgeVertex 320 0) i.castSucc * q (edgeVertex 320 1) 4 =
        multiplier 320 * direction 320 i := by decide +kernel

theorem direction_scale_321 : ∀ i : Fin 4,
    q (edgeVertex 321 1) i.castSucc * q (edgeVertex 321 0) 4 -
      q (edgeVertex 321 0) i.castSucc * q (edgeVertex 321 1) 4 =
        multiplier 321 * direction 321 i := by decide +kernel

theorem direction_scale_322 : ∀ i : Fin 4,
    q (edgeVertex 322 1) i.castSucc * q (edgeVertex 322 0) 4 -
      q (edgeVertex 322 0) i.castSucc * q (edgeVertex 322 1) 4 =
        multiplier 322 * direction 322 i := by decide +kernel

theorem direction_scale_323 : ∀ i : Fin 4,
    q (edgeVertex 323 1) i.castSucc * q (edgeVertex 323 0) 4 -
      q (edgeVertex 323 0) i.castSucc * q (edgeVertex 323 1) 4 =
        multiplier 323 * direction 323 i := by decide +kernel

theorem direction_scale_324 : ∀ i : Fin 4,
    q (edgeVertex 324 1) i.castSucc * q (edgeVertex 324 0) 4 -
      q (edgeVertex 324 0) i.castSucc * q (edgeVertex 324 1) 4 =
        multiplier 324 * direction 324 i := by decide +kernel

theorem direction_scale_325 : ∀ i : Fin 4,
    q (edgeVertex 325 1) i.castSucc * q (edgeVertex 325 0) 4 -
      q (edgeVertex 325 0) i.castSucc * q (edgeVertex 325 1) 4 =
        multiplier 325 * direction 325 i := by decide +kernel

theorem direction_scale_326 : ∀ i : Fin 4,
    q (edgeVertex 326 1) i.castSucc * q (edgeVertex 326 0) 4 -
      q (edgeVertex 326 0) i.castSucc * q (edgeVertex 326 1) 4 =
        multiplier 326 * direction 326 i := by decide +kernel

theorem direction_scale_327 : ∀ i : Fin 4,
    q (edgeVertex 327 1) i.castSucc * q (edgeVertex 327 0) 4 -
      q (edgeVertex 327 0) i.castSucc * q (edgeVertex 327 1) 4 =
        multiplier 327 * direction 327 i := by decide +kernel

theorem direction_scale_328 : ∀ i : Fin 4,
    q (edgeVertex 328 1) i.castSucc * q (edgeVertex 328 0) 4 -
      q (edgeVertex 328 0) i.castSucc * q (edgeVertex 328 1) 4 =
        multiplier 328 * direction 328 i := by decide +kernel

theorem direction_scale_329 : ∀ i : Fin 4,
    q (edgeVertex 329 1) i.castSucc * q (edgeVertex 329 0) 4 -
      q (edgeVertex 329 0) i.castSucc * q (edgeVertex 329 1) 4 =
        multiplier 329 * direction 329 i := by decide +kernel

theorem direction_scale_330 : ∀ i : Fin 4,
    q (edgeVertex 330 1) i.castSucc * q (edgeVertex 330 0) 4 -
      q (edgeVertex 330 0) i.castSucc * q (edgeVertex 330 1) 4 =
        multiplier 330 * direction 330 i := by decide +kernel

theorem direction_scale_331 : ∀ i : Fin 4,
    q (edgeVertex 331 1) i.castSucc * q (edgeVertex 331 0) 4 -
      q (edgeVertex 331 0) i.castSucc * q (edgeVertex 331 1) 4 =
        multiplier 331 * direction 331 i := by decide +kernel

theorem direction_scale_332 : ∀ i : Fin 4,
    q (edgeVertex 332 1) i.castSucc * q (edgeVertex 332 0) 4 -
      q (edgeVertex 332 0) i.castSucc * q (edgeVertex 332 1) 4 =
        multiplier 332 * direction 332 i := by decide +kernel

theorem direction_scale_333 : ∀ i : Fin 4,
    q (edgeVertex 333 1) i.castSucc * q (edgeVertex 333 0) 4 -
      q (edgeVertex 333 0) i.castSucc * q (edgeVertex 333 1) 4 =
        multiplier 333 * direction 333 i := by decide +kernel

theorem direction_scale_334 : ∀ i : Fin 4,
    q (edgeVertex 334 1) i.castSucc * q (edgeVertex 334 0) 4 -
      q (edgeVertex 334 0) i.castSucc * q (edgeVertex 334 1) 4 =
        multiplier 334 * direction 334 i := by decide +kernel

theorem direction_scale_335 : ∀ i : Fin 4,
    q (edgeVertex 335 1) i.castSucc * q (edgeVertex 335 0) 4 -
      q (edgeVertex 335 0) i.castSucc * q (edgeVertex 335 1) 4 =
        multiplier 335 * direction 335 i := by decide +kernel

theorem direction_scale_336 : ∀ i : Fin 4,
    q (edgeVertex 336 1) i.castSucc * q (edgeVertex 336 0) 4 -
      q (edgeVertex 336 0) i.castSucc * q (edgeVertex 336 1) 4 =
        multiplier 336 * direction 336 i := by decide +kernel

theorem direction_scale_337 : ∀ i : Fin 4,
    q (edgeVertex 337 1) i.castSucc * q (edgeVertex 337 0) 4 -
      q (edgeVertex 337 0) i.castSucc * q (edgeVertex 337 1) 4 =
        multiplier 337 * direction 337 i := by decide +kernel

theorem direction_scale_338 : ∀ i : Fin 4,
    q (edgeVertex 338 1) i.castSucc * q (edgeVertex 338 0) 4 -
      q (edgeVertex 338 0) i.castSucc * q (edgeVertex 338 1) 4 =
        multiplier 338 * direction 338 i := by decide +kernel

theorem direction_scale_339 : ∀ i : Fin 4,
    q (edgeVertex 339 1) i.castSucc * q (edgeVertex 339 0) 4 -
      q (edgeVertex 339 0) i.castSucc * q (edgeVertex 339 1) 4 =
        multiplier 339 * direction 339 i := by decide +kernel

theorem direction_scale_340 : ∀ i : Fin 4,
    q (edgeVertex 340 1) i.castSucc * q (edgeVertex 340 0) 4 -
      q (edgeVertex 340 0) i.castSucc * q (edgeVertex 340 1) 4 =
        multiplier 340 * direction 340 i := by decide +kernel

theorem direction_scale_341 : ∀ i : Fin 4,
    q (edgeVertex 341 1) i.castSucc * q (edgeVertex 341 0) 4 -
      q (edgeVertex 341 0) i.castSucc * q (edgeVertex 341 1) 4 =
        multiplier 341 * direction 341 i := by decide +kernel

theorem direction_scale_342 : ∀ i : Fin 4,
    q (edgeVertex 342 1) i.castSucc * q (edgeVertex 342 0) 4 -
      q (edgeVertex 342 0) i.castSucc * q (edgeVertex 342 1) 4 =
        multiplier 342 * direction 342 i := by decide +kernel

theorem direction_scale_343 : ∀ i : Fin 4,
    q (edgeVertex 343 1) i.castSucc * q (edgeVertex 343 0) 4 -
      q (edgeVertex 343 0) i.castSucc * q (edgeVertex 343 1) 4 =
        multiplier 343 * direction 343 i := by decide +kernel

theorem direction_scale_344 : ∀ i : Fin 4,
    q (edgeVertex 344 1) i.castSucc * q (edgeVertex 344 0) 4 -
      q (edgeVertex 344 0) i.castSucc * q (edgeVertex 344 1) 4 =
        multiplier 344 * direction 344 i := by decide +kernel

theorem direction_scale_345 : ∀ i : Fin 4,
    q (edgeVertex 345 1) i.castSucc * q (edgeVertex 345 0) 4 -
      q (edgeVertex 345 0) i.castSucc * q (edgeVertex 345 1) 4 =
        multiplier 345 * direction 345 i := by decide +kernel

theorem direction_scale_346 : ∀ i : Fin 4,
    q (edgeVertex 346 1) i.castSucc * q (edgeVertex 346 0) 4 -
      q (edgeVertex 346 0) i.castSucc * q (edgeVertex 346 1) 4 =
        multiplier 346 * direction 346 i := by decide +kernel

theorem direction_scale_347 : ∀ i : Fin 4,
    q (edgeVertex 347 1) i.castSucc * q (edgeVertex 347 0) 4 -
      q (edgeVertex 347 0) i.castSucc * q (edgeVertex 347 1) 4 =
        multiplier 347 * direction 347 i := by decide +kernel

theorem direction_scale_348 : ∀ i : Fin 4,
    q (edgeVertex 348 1) i.castSucc * q (edgeVertex 348 0) 4 -
      q (edgeVertex 348 0) i.castSucc * q (edgeVertex 348 1) 4 =
        multiplier 348 * direction 348 i := by decide +kernel

theorem direction_scale_349 : ∀ i : Fin 4,
    q (edgeVertex 349 1) i.castSucc * q (edgeVertex 349 0) 4 -
      q (edgeVertex 349 0) i.castSucc * q (edgeVertex 349 1) 4 =
        multiplier 349 * direction 349 i := by decide +kernel

theorem direction_scale_350 : ∀ i : Fin 4,
    q (edgeVertex 350 1) i.castSucc * q (edgeVertex 350 0) 4 -
      q (edgeVertex 350 0) i.castSucc * q (edgeVertex 350 1) 4 =
        multiplier 350 * direction 350 i := by decide +kernel

theorem direction_scale_351 : ∀ i : Fin 4,
    q (edgeVertex 351 1) i.castSucc * q (edgeVertex 351 0) 4 -
      q (edgeVertex 351 0) i.castSucc * q (edgeVertex 351 1) 4 =
        multiplier 351 * direction 351 i := by decide +kernel

theorem direction_scale_352 : ∀ i : Fin 4,
    q (edgeVertex 352 1) i.castSucc * q (edgeVertex 352 0) 4 -
      q (edgeVertex 352 0) i.castSucc * q (edgeVertex 352 1) 4 =
        multiplier 352 * direction 352 i := by decide +kernel

theorem direction_scale_353 : ∀ i : Fin 4,
    q (edgeVertex 353 1) i.castSucc * q (edgeVertex 353 0) 4 -
      q (edgeVertex 353 0) i.castSucc * q (edgeVertex 353 1) 4 =
        multiplier 353 * direction 353 i := by decide +kernel

theorem direction_scale_354 : ∀ i : Fin 4,
    q (edgeVertex 354 1) i.castSucc * q (edgeVertex 354 0) 4 -
      q (edgeVertex 354 0) i.castSucc * q (edgeVertex 354 1) 4 =
        multiplier 354 * direction 354 i := by decide +kernel

theorem direction_scale_355 : ∀ i : Fin 4,
    q (edgeVertex 355 1) i.castSucc * q (edgeVertex 355 0) 4 -
      q (edgeVertex 355 0) i.castSucc * q (edgeVertex 355 1) 4 =
        multiplier 355 * direction 355 i := by decide +kernel

theorem direction_scale_356 : ∀ i : Fin 4,
    q (edgeVertex 356 1) i.castSucc * q (edgeVertex 356 0) 4 -
      q (edgeVertex 356 0) i.castSucc * q (edgeVertex 356 1) 4 =
        multiplier 356 * direction 356 i := by decide +kernel

theorem direction_scale_357 : ∀ i : Fin 4,
    q (edgeVertex 357 1) i.castSucc * q (edgeVertex 357 0) 4 -
      q (edgeVertex 357 0) i.castSucc * q (edgeVertex 357 1) 4 =
        multiplier 357 * direction 357 i := by decide +kernel

theorem direction_scale_358 : ∀ i : Fin 4,
    q (edgeVertex 358 1) i.castSucc * q (edgeVertex 358 0) 4 -
      q (edgeVertex 358 0) i.castSucc * q (edgeVertex 358 1) 4 =
        multiplier 358 * direction 358 i := by decide +kernel

theorem direction_scale_359 : ∀ i : Fin 4,
    q (edgeVertex 359 1) i.castSucc * q (edgeVertex 359 0) 4 -
      q (edgeVertex 359 0) i.castSucc * q (edgeVertex 359 1) 4 =
        multiplier 359 * direction 359 i := by decide +kernel

theorem direction_scale_360 : ∀ i : Fin 4,
    q (edgeVertex 360 1) i.castSucc * q (edgeVertex 360 0) 4 -
      q (edgeVertex 360 0) i.castSucc * q (edgeVertex 360 1) 4 =
        multiplier 360 * direction 360 i := by decide +kernel

theorem direction_scale_361 : ∀ i : Fin 4,
    q (edgeVertex 361 1) i.castSucc * q (edgeVertex 361 0) 4 -
      q (edgeVertex 361 0) i.castSucc * q (edgeVertex 361 1) 4 =
        multiplier 361 * direction 361 i := by decide +kernel

theorem direction_scale_362 : ∀ i : Fin 4,
    q (edgeVertex 362 1) i.castSucc * q (edgeVertex 362 0) 4 -
      q (edgeVertex 362 0) i.castSucc * q (edgeVertex 362 1) 4 =
        multiplier 362 * direction 362 i := by decide +kernel

theorem direction_scale_363 : ∀ i : Fin 4,
    q (edgeVertex 363 1) i.castSucc * q (edgeVertex 363 0) 4 -
      q (edgeVertex 363 0) i.castSucc * q (edgeVertex 363 1) 4 =
        multiplier 363 * direction 363 i := by decide +kernel

theorem direction_scale_364 : ∀ i : Fin 4,
    q (edgeVertex 364 1) i.castSucc * q (edgeVertex 364 0) 4 -
      q (edgeVertex 364 0) i.castSucc * q (edgeVertex 364 1) 4 =
        multiplier 364 * direction 364 i := by decide +kernel

theorem direction_scale_365 : ∀ i : Fin 4,
    q (edgeVertex 365 1) i.castSucc * q (edgeVertex 365 0) 4 -
      q (edgeVertex 365 0) i.castSucc * q (edgeVertex 365 1) 4 =
        multiplier 365 * direction 365 i := by decide +kernel

theorem direction_scale_366 : ∀ i : Fin 4,
    q (edgeVertex 366 1) i.castSucc * q (edgeVertex 366 0) 4 -
      q (edgeVertex 366 0) i.castSucc * q (edgeVertex 366 1) 4 =
        multiplier 366 * direction 366 i := by decide +kernel

theorem direction_scale_367 : ∀ i : Fin 4,
    q (edgeVertex 367 1) i.castSucc * q (edgeVertex 367 0) 4 -
      q (edgeVertex 367 0) i.castSucc * q (edgeVertex 367 1) 4 =
        multiplier 367 * direction 367 i := by decide +kernel

theorem direction_scale_368 : ∀ i : Fin 4,
    q (edgeVertex 368 1) i.castSucc * q (edgeVertex 368 0) 4 -
      q (edgeVertex 368 0) i.castSucc * q (edgeVertex 368 1) 4 =
        multiplier 368 * direction 368 i := by decide +kernel

theorem direction_scale_369 : ∀ i : Fin 4,
    q (edgeVertex 369 1) i.castSucc * q (edgeVertex 369 0) 4 -
      q (edgeVertex 369 0) i.castSucc * q (edgeVertex 369 1) 4 =
        multiplier 369 * direction 369 i := by decide +kernel

theorem direction_scale_370 : ∀ i : Fin 4,
    q (edgeVertex 370 1) i.castSucc * q (edgeVertex 370 0) 4 -
      q (edgeVertex 370 0) i.castSucc * q (edgeVertex 370 1) 4 =
        multiplier 370 * direction 370 i := by decide +kernel

theorem direction_scale_371 : ∀ i : Fin 4,
    q (edgeVertex 371 1) i.castSucc * q (edgeVertex 371 0) 4 -
      q (edgeVertex 371 0) i.castSucc * q (edgeVertex 371 1) 4 =
        multiplier 371 * direction 371 i := by decide +kernel

theorem direction_scale_372 : ∀ i : Fin 4,
    q (edgeVertex 372 1) i.castSucc * q (edgeVertex 372 0) 4 -
      q (edgeVertex 372 0) i.castSucc * q (edgeVertex 372 1) 4 =
        multiplier 372 * direction 372 i := by decide +kernel

theorem direction_scale_373 : ∀ i : Fin 4,
    q (edgeVertex 373 1) i.castSucc * q (edgeVertex 373 0) 4 -
      q (edgeVertex 373 0) i.castSucc * q (edgeVertex 373 1) 4 =
        multiplier 373 * direction 373 i := by decide +kernel

theorem direction_scale_374 : ∀ i : Fin 4,
    q (edgeVertex 374 1) i.castSucc * q (edgeVertex 374 0) 4 -
      q (edgeVertex 374 0) i.castSucc * q (edgeVertex 374 1) 4 =
        multiplier 374 * direction 374 i := by decide +kernel

theorem direction_scale_375 : ∀ i : Fin 4,
    q (edgeVertex 375 1) i.castSucc * q (edgeVertex 375 0) 4 -
      q (edgeVertex 375 0) i.castSucc * q (edgeVertex 375 1) 4 =
        multiplier 375 * direction 375 i := by decide +kernel

theorem direction_scale_376 : ∀ i : Fin 4,
    q (edgeVertex 376 1) i.castSucc * q (edgeVertex 376 0) 4 -
      q (edgeVertex 376 0) i.castSucc * q (edgeVertex 376 1) 4 =
        multiplier 376 * direction 376 i := by decide +kernel

theorem direction_scale_377 : ∀ i : Fin 4,
    q (edgeVertex 377 1) i.castSucc * q (edgeVertex 377 0) 4 -
      q (edgeVertex 377 0) i.castSucc * q (edgeVertex 377 1) 4 =
        multiplier 377 * direction 377 i := by decide +kernel

theorem direction_scale_378 : ∀ i : Fin 4,
    q (edgeVertex 378 1) i.castSucc * q (edgeVertex 378 0) 4 -
      q (edgeVertex 378 0) i.castSucc * q (edgeVertex 378 1) 4 =
        multiplier 378 * direction 378 i := by decide +kernel

theorem direction_scale_379 : ∀ i : Fin 4,
    q (edgeVertex 379 1) i.castSucc * q (edgeVertex 379 0) 4 -
      q (edgeVertex 379 0) i.castSucc * q (edgeVertex 379 1) 4 =
        multiplier 379 * direction 379 i := by decide +kernel

theorem direction_scale_380 : ∀ i : Fin 4,
    q (edgeVertex 380 1) i.castSucc * q (edgeVertex 380 0) 4 -
      q (edgeVertex 380 0) i.castSucc * q (edgeVertex 380 1) 4 =
        multiplier 380 * direction 380 i := by decide +kernel

theorem direction_scale_381 : ∀ i : Fin 4,
    q (edgeVertex 381 1) i.castSucc * q (edgeVertex 381 0) 4 -
      q (edgeVertex 381 0) i.castSucc * q (edgeVertex 381 1) 4 =
        multiplier 381 * direction 381 i := by decide +kernel

theorem direction_scale_382 : ∀ i : Fin 4,
    q (edgeVertex 382 1) i.castSucc * q (edgeVertex 382 0) 4 -
      q (edgeVertex 382 0) i.castSucc * q (edgeVertex 382 1) 4 =
        multiplier 382 * direction 382 i := by decide +kernel

theorem direction_scale_383 : ∀ i : Fin 4,
    q (edgeVertex 383 1) i.castSucc * q (edgeVertex 383 0) 4 -
      q (edgeVertex 383 0) i.castSucc * q (edgeVertex 383 1) 4 =
        multiplier 383 * direction 383 i := by decide +kernel

theorem direction_scale_384 : ∀ i : Fin 4,
    q (edgeVertex 384 1) i.castSucc * q (edgeVertex 384 0) 4 -
      q (edgeVertex 384 0) i.castSucc * q (edgeVertex 384 1) 4 =
        multiplier 384 * direction 384 i := by decide +kernel

theorem direction_scale_385 : ∀ i : Fin 4,
    q (edgeVertex 385 1) i.castSucc * q (edgeVertex 385 0) 4 -
      q (edgeVertex 385 0) i.castSucc * q (edgeVertex 385 1) 4 =
        multiplier 385 * direction 385 i := by decide +kernel

theorem direction_scale_386 : ∀ i : Fin 4,
    q (edgeVertex 386 1) i.castSucc * q (edgeVertex 386 0) 4 -
      q (edgeVertex 386 0) i.castSucc * q (edgeVertex 386 1) 4 =
        multiplier 386 * direction 386 i := by decide +kernel

theorem direction_scale_387 : ∀ i : Fin 4,
    q (edgeVertex 387 1) i.castSucc * q (edgeVertex 387 0) 4 -
      q (edgeVertex 387 0) i.castSucc * q (edgeVertex 387 1) 4 =
        multiplier 387 * direction 387 i := by decide +kernel

theorem direction_scale_388 : ∀ i : Fin 4,
    q (edgeVertex 388 1) i.castSucc * q (edgeVertex 388 0) 4 -
      q (edgeVertex 388 0) i.castSucc * q (edgeVertex 388 1) 4 =
        multiplier 388 * direction 388 i := by decide +kernel

theorem direction_scale_389 : ∀ i : Fin 4,
    q (edgeVertex 389 1) i.castSucc * q (edgeVertex 389 0) 4 -
      q (edgeVertex 389 0) i.castSucc * q (edgeVertex 389 1) 4 =
        multiplier 389 * direction 389 i := by decide +kernel

theorem direction_scale_390 : ∀ i : Fin 4,
    q (edgeVertex 390 1) i.castSucc * q (edgeVertex 390 0) 4 -
      q (edgeVertex 390 0) i.castSucc * q (edgeVertex 390 1) 4 =
        multiplier 390 * direction 390 i := by decide +kernel

theorem direction_scale_391 : ∀ i : Fin 4,
    q (edgeVertex 391 1) i.castSucc * q (edgeVertex 391 0) 4 -
      q (edgeVertex 391 0) i.castSucc * q (edgeVertex 391 1) 4 =
        multiplier 391 * direction 391 i := by decide +kernel

theorem direction_scale_392 : ∀ i : Fin 4,
    q (edgeVertex 392 1) i.castSucc * q (edgeVertex 392 0) 4 -
      q (edgeVertex 392 0) i.castSucc * q (edgeVertex 392 1) 4 =
        multiplier 392 * direction 392 i := by decide +kernel

theorem direction_scale_393 : ∀ i : Fin 4,
    q (edgeVertex 393 1) i.castSucc * q (edgeVertex 393 0) 4 -
      q (edgeVertex 393 0) i.castSucc * q (edgeVertex 393 1) 4 =
        multiplier 393 * direction 393 i := by decide +kernel

theorem direction_scale_394 : ∀ i : Fin 4,
    q (edgeVertex 394 1) i.castSucc * q (edgeVertex 394 0) 4 -
      q (edgeVertex 394 0) i.castSucc * q (edgeVertex 394 1) 4 =
        multiplier 394 * direction 394 i := by decide +kernel

theorem direction_scale_395 : ∀ i : Fin 4,
    q (edgeVertex 395 1) i.castSucc * q (edgeVertex 395 0) 4 -
      q (edgeVertex 395 0) i.castSucc * q (edgeVertex 395 1) 4 =
        multiplier 395 * direction 395 i := by decide +kernel

theorem direction_scale_396 : ∀ i : Fin 4,
    q (edgeVertex 396 1) i.castSucc * q (edgeVertex 396 0) 4 -
      q (edgeVertex 396 0) i.castSucc * q (edgeVertex 396 1) 4 =
        multiplier 396 * direction 396 i := by decide +kernel

theorem direction_scale_397 : ∀ i : Fin 4,
    q (edgeVertex 397 1) i.castSucc * q (edgeVertex 397 0) 4 -
      q (edgeVertex 397 0) i.castSucc * q (edgeVertex 397 1) 4 =
        multiplier 397 * direction 397 i := by decide +kernel

theorem direction_scale_398 : ∀ i : Fin 4,
    q (edgeVertex 398 1) i.castSucc * q (edgeVertex 398 0) 4 -
      q (edgeVertex 398 0) i.castSucc * q (edgeVertex 398 1) 4 =
        multiplier 398 * direction 398 i := by decide +kernel

theorem direction_scale_399 : ∀ i : Fin 4,
    q (edgeVertex 399 1) i.castSucc * q (edgeVertex 399 0) 4 -
      q (edgeVertex 399 0) i.castSucc * q (edgeVertex 399 1) 4 =
        multiplier 399 * direction 399 i := by decide +kernel

theorem direction_scale_400 : ∀ i : Fin 4,
    q (edgeVertex 400 1) i.castSucc * q (edgeVertex 400 0) 4 -
      q (edgeVertex 400 0) i.castSucc * q (edgeVertex 400 1) 4 =
        multiplier 400 * direction 400 i := by decide +kernel

theorem direction_scale_401 : ∀ i : Fin 4,
    q (edgeVertex 401 1) i.castSucc * q (edgeVertex 401 0) 4 -
      q (edgeVertex 401 0) i.castSucc * q (edgeVertex 401 1) 4 =
        multiplier 401 * direction 401 i := by decide +kernel

theorem direction_scale_402 : ∀ i : Fin 4,
    q (edgeVertex 402 1) i.castSucc * q (edgeVertex 402 0) 4 -
      q (edgeVertex 402 0) i.castSucc * q (edgeVertex 402 1) 4 =
        multiplier 402 * direction 402 i := by decide +kernel

theorem direction_scale_403 : ∀ i : Fin 4,
    q (edgeVertex 403 1) i.castSucc * q (edgeVertex 403 0) 4 -
      q (edgeVertex 403 0) i.castSucc * q (edgeVertex 403 1) 4 =
        multiplier 403 * direction 403 i := by decide +kernel

theorem direction_scale (e : Fin 404) (i : Fin 4) :
    q (edgeVertex e 1) i.castSucc * q (edgeVertex e 0) 4 -
      q (edgeVertex e 0) i.castSucc * q (edgeVertex e 1) 4 =
        multiplier e * direction e i := by
  fin_cases e
  · exact direction_scale_000 i
  · exact direction_scale_001 i
  · exact direction_scale_002 i
  · exact direction_scale_003 i
  · exact direction_scale_004 i
  · exact direction_scale_005 i
  · exact direction_scale_006 i
  · exact direction_scale_007 i
  · exact direction_scale_008 i
  · exact direction_scale_009 i
  · exact direction_scale_010 i
  · exact direction_scale_011 i
  · exact direction_scale_012 i
  · exact direction_scale_013 i
  · exact direction_scale_014 i
  · exact direction_scale_015 i
  · exact direction_scale_016 i
  · exact direction_scale_017 i
  · exact direction_scale_018 i
  · exact direction_scale_019 i
  · exact direction_scale_020 i
  · exact direction_scale_021 i
  · exact direction_scale_022 i
  · exact direction_scale_023 i
  · exact direction_scale_024 i
  · exact direction_scale_025 i
  · exact direction_scale_026 i
  · exact direction_scale_027 i
  · exact direction_scale_028 i
  · exact direction_scale_029 i
  · exact direction_scale_030 i
  · exact direction_scale_031 i
  · exact direction_scale_032 i
  · exact direction_scale_033 i
  · exact direction_scale_034 i
  · exact direction_scale_035 i
  · exact direction_scale_036 i
  · exact direction_scale_037 i
  · exact direction_scale_038 i
  · exact direction_scale_039 i
  · exact direction_scale_040 i
  · exact direction_scale_041 i
  · exact direction_scale_042 i
  · exact direction_scale_043 i
  · exact direction_scale_044 i
  · exact direction_scale_045 i
  · exact direction_scale_046 i
  · exact direction_scale_047 i
  · exact direction_scale_048 i
  · exact direction_scale_049 i
  · exact direction_scale_050 i
  · exact direction_scale_051 i
  · exact direction_scale_052 i
  · exact direction_scale_053 i
  · exact direction_scale_054 i
  · exact direction_scale_055 i
  · exact direction_scale_056 i
  · exact direction_scale_057 i
  · exact direction_scale_058 i
  · exact direction_scale_059 i
  · exact direction_scale_060 i
  · exact direction_scale_061 i
  · exact direction_scale_062 i
  · exact direction_scale_063 i
  · exact direction_scale_064 i
  · exact direction_scale_065 i
  · exact direction_scale_066 i
  · exact direction_scale_067 i
  · exact direction_scale_068 i
  · exact direction_scale_069 i
  · exact direction_scale_070 i
  · exact direction_scale_071 i
  · exact direction_scale_072 i
  · exact direction_scale_073 i
  · exact direction_scale_074 i
  · exact direction_scale_075 i
  · exact direction_scale_076 i
  · exact direction_scale_077 i
  · exact direction_scale_078 i
  · exact direction_scale_079 i
  · exact direction_scale_080 i
  · exact direction_scale_081 i
  · exact direction_scale_082 i
  · exact direction_scale_083 i
  · exact direction_scale_084 i
  · exact direction_scale_085 i
  · exact direction_scale_086 i
  · exact direction_scale_087 i
  · exact direction_scale_088 i
  · exact direction_scale_089 i
  · exact direction_scale_090 i
  · exact direction_scale_091 i
  · exact direction_scale_092 i
  · exact direction_scale_093 i
  · exact direction_scale_094 i
  · exact direction_scale_095 i
  · exact direction_scale_096 i
  · exact direction_scale_097 i
  · exact direction_scale_098 i
  · exact direction_scale_099 i
  · exact direction_scale_100 i
  · exact direction_scale_101 i
  · exact direction_scale_102 i
  · exact direction_scale_103 i
  · exact direction_scale_104 i
  · exact direction_scale_105 i
  · exact direction_scale_106 i
  · exact direction_scale_107 i
  · exact direction_scale_108 i
  · exact direction_scale_109 i
  · exact direction_scale_110 i
  · exact direction_scale_111 i
  · exact direction_scale_112 i
  · exact direction_scale_113 i
  · exact direction_scale_114 i
  · exact direction_scale_115 i
  · exact direction_scale_116 i
  · exact direction_scale_117 i
  · exact direction_scale_118 i
  · exact direction_scale_119 i
  · exact direction_scale_120 i
  · exact direction_scale_121 i
  · exact direction_scale_122 i
  · exact direction_scale_123 i
  · exact direction_scale_124 i
  · exact direction_scale_125 i
  · exact direction_scale_126 i
  · exact direction_scale_127 i
  · exact direction_scale_128 i
  · exact direction_scale_129 i
  · exact direction_scale_130 i
  · exact direction_scale_131 i
  · exact direction_scale_132 i
  · exact direction_scale_133 i
  · exact direction_scale_134 i
  · exact direction_scale_135 i
  · exact direction_scale_136 i
  · exact direction_scale_137 i
  · exact direction_scale_138 i
  · exact direction_scale_139 i
  · exact direction_scale_140 i
  · exact direction_scale_141 i
  · exact direction_scale_142 i
  · exact direction_scale_143 i
  · exact direction_scale_144 i
  · exact direction_scale_145 i
  · exact direction_scale_146 i
  · exact direction_scale_147 i
  · exact direction_scale_148 i
  · exact direction_scale_149 i
  · exact direction_scale_150 i
  · exact direction_scale_151 i
  · exact direction_scale_152 i
  · exact direction_scale_153 i
  · exact direction_scale_154 i
  · exact direction_scale_155 i
  · exact direction_scale_156 i
  · exact direction_scale_157 i
  · exact direction_scale_158 i
  · exact direction_scale_159 i
  · exact direction_scale_160 i
  · exact direction_scale_161 i
  · exact direction_scale_162 i
  · exact direction_scale_163 i
  · exact direction_scale_164 i
  · exact direction_scale_165 i
  · exact direction_scale_166 i
  · exact direction_scale_167 i
  · exact direction_scale_168 i
  · exact direction_scale_169 i
  · exact direction_scale_170 i
  · exact direction_scale_171 i
  · exact direction_scale_172 i
  · exact direction_scale_173 i
  · exact direction_scale_174 i
  · exact direction_scale_175 i
  · exact direction_scale_176 i
  · exact direction_scale_177 i
  · exact direction_scale_178 i
  · exact direction_scale_179 i
  · exact direction_scale_180 i
  · exact direction_scale_181 i
  · exact direction_scale_182 i
  · exact direction_scale_183 i
  · exact direction_scale_184 i
  · exact direction_scale_185 i
  · exact direction_scale_186 i
  · exact direction_scale_187 i
  · exact direction_scale_188 i
  · exact direction_scale_189 i
  · exact direction_scale_190 i
  · exact direction_scale_191 i
  · exact direction_scale_192 i
  · exact direction_scale_193 i
  · exact direction_scale_194 i
  · exact direction_scale_195 i
  · exact direction_scale_196 i
  · exact direction_scale_197 i
  · exact direction_scale_198 i
  · exact direction_scale_199 i
  · exact direction_scale_200 i
  · exact direction_scale_201 i
  · exact direction_scale_202 i
  · exact direction_scale_203 i
  · exact direction_scale_204 i
  · exact direction_scale_205 i
  · exact direction_scale_206 i
  · exact direction_scale_207 i
  · exact direction_scale_208 i
  · exact direction_scale_209 i
  · exact direction_scale_210 i
  · exact direction_scale_211 i
  · exact direction_scale_212 i
  · exact direction_scale_213 i
  · exact direction_scale_214 i
  · exact direction_scale_215 i
  · exact direction_scale_216 i
  · exact direction_scale_217 i
  · exact direction_scale_218 i
  · exact direction_scale_219 i
  · exact direction_scale_220 i
  · exact direction_scale_221 i
  · exact direction_scale_222 i
  · exact direction_scale_223 i
  · exact direction_scale_224 i
  · exact direction_scale_225 i
  · exact direction_scale_226 i
  · exact direction_scale_227 i
  · exact direction_scale_228 i
  · exact direction_scale_229 i
  · exact direction_scale_230 i
  · exact direction_scale_231 i
  · exact direction_scale_232 i
  · exact direction_scale_233 i
  · exact direction_scale_234 i
  · exact direction_scale_235 i
  · exact direction_scale_236 i
  · exact direction_scale_237 i
  · exact direction_scale_238 i
  · exact direction_scale_239 i
  · exact direction_scale_240 i
  · exact direction_scale_241 i
  · exact direction_scale_242 i
  · exact direction_scale_243 i
  · exact direction_scale_244 i
  · exact direction_scale_245 i
  · exact direction_scale_246 i
  · exact direction_scale_247 i
  · exact direction_scale_248 i
  · exact direction_scale_249 i
  · exact direction_scale_250 i
  · exact direction_scale_251 i
  · exact direction_scale_252 i
  · exact direction_scale_253 i
  · exact direction_scale_254 i
  · exact direction_scale_255 i
  · exact direction_scale_256 i
  · exact direction_scale_257 i
  · exact direction_scale_258 i
  · exact direction_scale_259 i
  · exact direction_scale_260 i
  · exact direction_scale_261 i
  · exact direction_scale_262 i
  · exact direction_scale_263 i
  · exact direction_scale_264 i
  · exact direction_scale_265 i
  · exact direction_scale_266 i
  · exact direction_scale_267 i
  · exact direction_scale_268 i
  · exact direction_scale_269 i
  · exact direction_scale_270 i
  · exact direction_scale_271 i
  · exact direction_scale_272 i
  · exact direction_scale_273 i
  · exact direction_scale_274 i
  · exact direction_scale_275 i
  · exact direction_scale_276 i
  · exact direction_scale_277 i
  · exact direction_scale_278 i
  · exact direction_scale_279 i
  · exact direction_scale_280 i
  · exact direction_scale_281 i
  · exact direction_scale_282 i
  · exact direction_scale_283 i
  · exact direction_scale_284 i
  · exact direction_scale_285 i
  · exact direction_scale_286 i
  · exact direction_scale_287 i
  · exact direction_scale_288 i
  · exact direction_scale_289 i
  · exact direction_scale_290 i
  · exact direction_scale_291 i
  · exact direction_scale_292 i
  · exact direction_scale_293 i
  · exact direction_scale_294 i
  · exact direction_scale_295 i
  · exact direction_scale_296 i
  · exact direction_scale_297 i
  · exact direction_scale_298 i
  · exact direction_scale_299 i
  · exact direction_scale_300 i
  · exact direction_scale_301 i
  · exact direction_scale_302 i
  · exact direction_scale_303 i
  · exact direction_scale_304 i
  · exact direction_scale_305 i
  · exact direction_scale_306 i
  · exact direction_scale_307 i
  · exact direction_scale_308 i
  · exact direction_scale_309 i
  · exact direction_scale_310 i
  · exact direction_scale_311 i
  · exact direction_scale_312 i
  · exact direction_scale_313 i
  · exact direction_scale_314 i
  · exact direction_scale_315 i
  · exact direction_scale_316 i
  · exact direction_scale_317 i
  · exact direction_scale_318 i
  · exact direction_scale_319 i
  · exact direction_scale_320 i
  · exact direction_scale_321 i
  · exact direction_scale_322 i
  · exact direction_scale_323 i
  · exact direction_scale_324 i
  · exact direction_scale_325 i
  · exact direction_scale_326 i
  · exact direction_scale_327 i
  · exact direction_scale_328 i
  · exact direction_scale_329 i
  · exact direction_scale_330 i
  · exact direction_scale_331 i
  · exact direction_scale_332 i
  · exact direction_scale_333 i
  · exact direction_scale_334 i
  · exact direction_scale_335 i
  · exact direction_scale_336 i
  · exact direction_scale_337 i
  · exact direction_scale_338 i
  · exact direction_scale_339 i
  · exact direction_scale_340 i
  · exact direction_scale_341 i
  · exact direction_scale_342 i
  · exact direction_scale_343 i
  · exact direction_scale_344 i
  · exact direction_scale_345 i
  · exact direction_scale_346 i
  · exact direction_scale_347 i
  · exact direction_scale_348 i
  · exact direction_scale_349 i
  · exact direction_scale_350 i
  · exact direction_scale_351 i
  · exact direction_scale_352 i
  · exact direction_scale_353 i
  · exact direction_scale_354 i
  · exact direction_scale_355 i
  · exact direction_scale_356 i
  · exact direction_scale_357 i
  · exact direction_scale_358 i
  · exact direction_scale_359 i
  · exact direction_scale_360 i
  · exact direction_scale_361 i
  · exact direction_scale_362 i
  · exact direction_scale_363 i
  · exact direction_scale_364 i
  · exact direction_scale_365 i
  · exact direction_scale_366 i
  · exact direction_scale_367 i
  · exact direction_scale_368 i
  · exact direction_scale_369 i
  · exact direction_scale_370 i
  · exact direction_scale_371 i
  · exact direction_scale_372 i
  · exact direction_scale_373 i
  · exact direction_scale_374 i
  · exact direction_scale_375 i
  · exact direction_scale_376 i
  · exact direction_scale_377 i
  · exact direction_scale_378 i
  · exact direction_scale_379 i
  · exact direction_scale_380 i
  · exact direction_scale_381 i
  · exact direction_scale_382 i
  · exact direction_scale_383 i
  · exact direction_scale_384 i
  · exact direction_scale_385 i
  · exact direction_scale_386 i
  · exact direction_scale_387 i
  · exact direction_scale_388 i
  · exact direction_scale_389 i
  · exact direction_scale_390 i
  · exact direction_scale_391 i
  · exact direction_scale_392 i
  · exact direction_scale_393 i
  · exact direction_scale_394 i
  · exact direction_scale_395 i
  · exact direction_scale_396 i
  · exact direction_scale_397 i
  · exact direction_scale_398 i
  · exact direction_scale_399 i
  · exact direction_scale_400 i
  · exact direction_scale_401 i
  · exact direction_scale_402 i
  · exact direction_scale_403 i

end CubicalIndecomposability.Rigidity
