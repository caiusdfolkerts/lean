module
/- UNCOMPILED, exact-source-checked staging helper. Must be replayed with
   Lean 4.35.0 + pinned Mathlib, with regular kernel checking.
   Clause identity/order is fully present in the proposition; no hash axioms. -/
public import Consolidated.SemanticChecks28
public import Consolidated.SemanticChecks29
public import Consolidated.SemanticChecks30
public import Consolidated.SemanticChecks31
public import Consolidated.SemanticChecks32
public import Consolidated.SemanticChecks33
public import MatroidChecked.PublicRefutations.N8R4C84
import Init.Data.List.TakeDrop

public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.MatroidChecked.C84ClauseMap
open Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C84

private noncomputable def suffix_000 : List (List Sat.Literal) := Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C84.formula
private theorem suffix_length_000 : suffix_000.length = 7442 := by rfl

private noncomputable def suffix_001 : List (List Sat.Literal) := suffix_000.drop 128
private theorem suffix_step_000 : suffix_001 = suffix_000.drop 128 := rfl
private theorem suffix_length_001 : suffix_001.length = 7314 := by
  rw [suffix_step_000, List.length_drop, suffix_length_000]
private theorem block_length_000 : certificates_0.length = 128 := by rfl
private theorem block_clauses_000 :
    certificates_0.map Prod.snd = suffix_000.take 128 := by rfl

private noncomputable def suffix_002 : List (List Sat.Literal) := suffix_001.drop 128
private theorem suffix_step_001 : suffix_002 = suffix_001.drop 128 := rfl
private theorem suffix_length_002 : suffix_002.length = 7186 := by
  rw [suffix_step_001, List.length_drop, suffix_length_001]
private theorem block_length_001 : certificates_1.length = 128 := by rfl
private theorem block_clauses_001 :
    certificates_1.map Prod.snd = suffix_001.take 128 := by rfl

private noncomputable def suffix_003 : List (List Sat.Literal) := suffix_002.drop 128
private theorem suffix_step_002 : suffix_003 = suffix_002.drop 128 := rfl
private theorem suffix_length_003 : suffix_003.length = 7058 := by
  rw [suffix_step_002, List.length_drop, suffix_length_002]
private theorem block_length_002 : certificates_2.length = 128 := by rfl
private theorem block_clauses_002 :
    certificates_2.map Prod.snd = suffix_002.take 128 := by rfl

private noncomputable def suffix_004 : List (List Sat.Literal) := suffix_003.drop 128
private theorem suffix_step_003 : suffix_004 = suffix_003.drop 128 := rfl
private theorem suffix_length_004 : suffix_004.length = 6930 := by
  rw [suffix_step_003, List.length_drop, suffix_length_003]
private theorem block_length_003 : certificates_3.length = 128 := by rfl
private theorem block_clauses_003 :
    certificates_3.map Prod.snd = suffix_003.take 128 := by rfl

private noncomputable def suffix_005 : List (List Sat.Literal) := suffix_004.drop 128
private theorem suffix_step_004 : suffix_005 = suffix_004.drop 128 := rfl
private theorem suffix_length_005 : suffix_005.length = 6802 := by
  rw [suffix_step_004, List.length_drop, suffix_length_004]
private theorem block_length_004 : certificates_4.length = 128 := by rfl
private theorem block_clauses_004 :
    certificates_4.map Prod.snd = suffix_004.take 128 := by rfl

private noncomputable def suffix_006 : List (List Sat.Literal) := suffix_005.drop 128
private theorem suffix_step_005 : suffix_006 = suffix_005.drop 128 := rfl
private theorem suffix_length_006 : suffix_006.length = 6674 := by
  rw [suffix_step_005, List.length_drop, suffix_length_005]
private theorem block_length_005 : certificates_5.length = 128 := by rfl
private theorem block_clauses_005 :
    certificates_5.map Prod.snd = suffix_005.take 128 := by rfl

private noncomputable def suffix_007 : List (List Sat.Literal) := suffix_006.drop 128
private theorem suffix_step_006 : suffix_007 = suffix_006.drop 128 := rfl
private theorem suffix_length_007 : suffix_007.length = 6546 := by
  rw [suffix_step_006, List.length_drop, suffix_length_006]
private theorem block_length_006 : certificates_6.length = 128 := by rfl
private theorem block_clauses_006 :
    certificates_6.map Prod.snd = suffix_006.take 128 := by rfl

private noncomputable def suffix_008 : List (List Sat.Literal) := suffix_007.drop 128
private theorem suffix_step_007 : suffix_008 = suffix_007.drop 128 := rfl
private theorem suffix_length_008 : suffix_008.length = 6418 := by
  rw [suffix_step_007, List.length_drop, suffix_length_007]
private theorem block_length_007 : certificates_7.length = 128 := by rfl
private theorem block_clauses_007 :
    certificates_7.map Prod.snd = suffix_007.take 128 := by rfl

private noncomputable def suffix_009 : List (List Sat.Literal) := suffix_008.drop 128
private theorem suffix_step_008 : suffix_009 = suffix_008.drop 128 := rfl
private theorem suffix_length_009 : suffix_009.length = 6290 := by
  rw [suffix_step_008, List.length_drop, suffix_length_008]
private theorem block_length_008 : certificates_8.length = 128 := by rfl
private theorem block_clauses_008 :
    certificates_8.map Prod.snd = suffix_008.take 128 := by rfl

private noncomputable def suffix_010 : List (List Sat.Literal) := suffix_009.drop 128
private theorem suffix_step_009 : suffix_010 = suffix_009.drop 128 := rfl
private theorem suffix_length_010 : suffix_010.length = 6162 := by
  rw [suffix_step_009, List.length_drop, suffix_length_009]
private theorem block_length_009 : certificates_9.length = 128 := by rfl
private theorem block_clauses_009 :
    certificates_9.map Prod.snd = suffix_009.take 128 := by rfl

private noncomputable def suffix_011 : List (List Sat.Literal) := suffix_010.drop 128
private theorem suffix_step_010 : suffix_011 = suffix_010.drop 128 := rfl
private theorem suffix_length_011 : suffix_011.length = 6034 := by
  rw [suffix_step_010, List.length_drop, suffix_length_010]
private theorem block_length_010 : certificates_10.length = 128 := by rfl
private theorem block_clauses_010 :
    certificates_10.map Prod.snd = suffix_010.take 128 := by rfl

private noncomputable def suffix_012 : List (List Sat.Literal) := suffix_011.drop 128
private theorem suffix_step_011 : suffix_012 = suffix_011.drop 128 := rfl
private theorem suffix_length_012 : suffix_012.length = 5906 := by
  rw [suffix_step_011, List.length_drop, suffix_length_011]
private theorem block_length_011 : certificates_11.length = 128 := by rfl
private theorem block_clauses_011 :
    certificates_11.map Prod.snd = suffix_011.take 128 := by rfl

private noncomputable def suffix_013 : List (List Sat.Literal) := suffix_012.drop 128
private theorem suffix_step_012 : suffix_013 = suffix_012.drop 128 := rfl
private theorem suffix_length_013 : suffix_013.length = 5778 := by
  rw [suffix_step_012, List.length_drop, suffix_length_012]
private theorem block_length_012 : certificates_12.length = 128 := by rfl
private theorem block_clauses_012 :
    certificates_12.map Prod.snd = suffix_012.take 128 := by rfl

private noncomputable def suffix_014 : List (List Sat.Literal) := suffix_013.drop 128
private theorem suffix_step_013 : suffix_014 = suffix_013.drop 128 := rfl
private theorem suffix_length_014 : suffix_014.length = 5650 := by
  rw [suffix_step_013, List.length_drop, suffix_length_013]
private theorem block_length_013 : certificates_13.length = 128 := by rfl
private theorem block_clauses_013 :
    certificates_13.map Prod.snd = suffix_013.take 128 := by rfl

private noncomputable def suffix_015 : List (List Sat.Literal) := suffix_014.drop 128
private theorem suffix_step_014 : suffix_015 = suffix_014.drop 128 := rfl
private theorem suffix_length_015 : suffix_015.length = 5522 := by
  rw [suffix_step_014, List.length_drop, suffix_length_014]
private theorem block_length_014 : certificates_14.length = 128 := by rfl
private theorem block_clauses_014 :
    certificates_14.map Prod.snd = suffix_014.take 128 := by rfl

private noncomputable def suffix_016 : List (List Sat.Literal) := suffix_015.drop 128
private theorem suffix_step_015 : suffix_016 = suffix_015.drop 128 := rfl
private theorem suffix_length_016 : suffix_016.length = 5394 := by
  rw [suffix_step_015, List.length_drop, suffix_length_015]
private theorem block_length_015 : certificates_15.length = 128 := by rfl
private theorem block_clauses_015 :
    certificates_15.map Prod.snd = suffix_015.take 128 := by rfl

private noncomputable def suffix_017 : List (List Sat.Literal) := suffix_016.drop 128
private theorem suffix_step_016 : suffix_017 = suffix_016.drop 128 := rfl
private theorem suffix_length_017 : suffix_017.length = 5266 := by
  rw [suffix_step_016, List.length_drop, suffix_length_016]
private theorem block_length_016 : certificates_16.length = 128 := by rfl
private theorem block_clauses_016 :
    certificates_16.map Prod.snd = suffix_016.take 128 := by rfl

private noncomputable def suffix_018 : List (List Sat.Literal) := suffix_017.drop 128
private theorem suffix_step_017 : suffix_018 = suffix_017.drop 128 := rfl
private theorem suffix_length_018 : suffix_018.length = 5138 := by
  rw [suffix_step_017, List.length_drop, suffix_length_017]
private theorem block_length_017 : certificates_17.length = 128 := by rfl
private theorem block_clauses_017 :
    certificates_17.map Prod.snd = suffix_017.take 128 := by rfl

private noncomputable def suffix_019 : List (List Sat.Literal) := suffix_018.drop 128
private theorem suffix_step_018 : suffix_019 = suffix_018.drop 128 := rfl
private theorem suffix_length_019 : suffix_019.length = 5010 := by
  rw [suffix_step_018, List.length_drop, suffix_length_018]
private theorem block_length_018 : certificates_18.length = 128 := by rfl
private theorem block_clauses_018 :
    certificates_18.map Prod.snd = suffix_018.take 128 := by rfl

private noncomputable def suffix_020 : List (List Sat.Literal) := suffix_019.drop 128
private theorem suffix_step_019 : suffix_020 = suffix_019.drop 128 := rfl
private theorem suffix_length_020 : suffix_020.length = 4882 := by
  rw [suffix_step_019, List.length_drop, suffix_length_019]
private theorem block_length_019 : certificates_19.length = 128 := by rfl
private theorem block_clauses_019 :
    certificates_19.map Prod.snd = suffix_019.take 128 := by rfl

private noncomputable def suffix_021 : List (List Sat.Literal) := suffix_020.drop 128
private theorem suffix_step_020 : suffix_021 = suffix_020.drop 128 := rfl
private theorem suffix_length_021 : suffix_021.length = 4754 := by
  rw [suffix_step_020, List.length_drop, suffix_length_020]
private theorem block_length_020 : certificates_20.length = 128 := by rfl
private theorem block_clauses_020 :
    certificates_20.map Prod.snd = suffix_020.take 128 := by rfl

private noncomputable def suffix_022 : List (List Sat.Literal) := suffix_021.drop 128
private theorem suffix_step_021 : suffix_022 = suffix_021.drop 128 := rfl
private theorem suffix_length_022 : suffix_022.length = 4626 := by
  rw [suffix_step_021, List.length_drop, suffix_length_021]
private theorem block_length_021 : certificates_21.length = 128 := by rfl
private theorem block_clauses_021 :
    certificates_21.map Prod.snd = suffix_021.take 128 := by rfl

private noncomputable def suffix_023 : List (List Sat.Literal) := suffix_022.drop 128
private theorem suffix_step_022 : suffix_023 = suffix_022.drop 128 := rfl
private theorem suffix_length_023 : suffix_023.length = 4498 := by
  rw [suffix_step_022, List.length_drop, suffix_length_022]
private theorem block_length_022 : certificates_22.length = 128 := by rfl
private theorem block_clauses_022 :
    certificates_22.map Prod.snd = suffix_022.take 128 := by rfl

private noncomputable def suffix_024 : List (List Sat.Literal) := suffix_023.drop 128
private theorem suffix_step_023 : suffix_024 = suffix_023.drop 128 := rfl
private theorem suffix_length_024 : suffix_024.length = 4370 := by
  rw [suffix_step_023, List.length_drop, suffix_length_023]
private theorem block_length_023 : certificates_23.length = 128 := by rfl
private theorem block_clauses_023 :
    certificates_23.map Prod.snd = suffix_023.take 128 := by rfl

private noncomputable def suffix_025 : List (List Sat.Literal) := suffix_024.drop 128
private theorem suffix_step_024 : suffix_025 = suffix_024.drop 128 := rfl
private theorem suffix_length_025 : suffix_025.length = 4242 := by
  rw [suffix_step_024, List.length_drop, suffix_length_024]
private theorem block_length_024 : certificates_24.length = 128 := by rfl
private theorem block_clauses_024 :
    certificates_24.map Prod.snd = suffix_024.take 128 := by rfl

private noncomputable def suffix_026 : List (List Sat.Literal) := suffix_025.drop 128
private theorem suffix_step_025 : suffix_026 = suffix_025.drop 128 := rfl
private theorem suffix_length_026 : suffix_026.length = 4114 := by
  rw [suffix_step_025, List.length_drop, suffix_length_025]
private theorem block_length_025 : certificates_25.length = 128 := by rfl
private theorem block_clauses_025 :
    certificates_25.map Prod.snd = suffix_025.take 128 := by rfl

private noncomputable def suffix_027 : List (List Sat.Literal) := suffix_026.drop 128
private theorem suffix_step_026 : suffix_027 = suffix_026.drop 128 := rfl
private theorem suffix_length_027 : suffix_027.length = 3986 := by
  rw [suffix_step_026, List.length_drop, suffix_length_026]
private theorem block_length_026 : certificates_26.length = 128 := by rfl
private theorem block_clauses_026 :
    certificates_26.map Prod.snd = suffix_026.take 128 := by rfl

private noncomputable def suffix_028 : List (List Sat.Literal) := suffix_027.drop 128
private theorem suffix_step_027 : suffix_028 = suffix_027.drop 128 := rfl
private theorem suffix_length_028 : suffix_028.length = 3858 := by
  rw [suffix_step_027, List.length_drop, suffix_length_027]
private theorem block_length_027 : certificates_27.length = 128 := by rfl
private theorem block_clauses_027 :
    certificates_27.map Prod.snd = suffix_027.take 128 := by rfl

private noncomputable def suffix_029 : List (List Sat.Literal) := suffix_028.drop 128
private theorem suffix_step_028 : suffix_029 = suffix_028.drop 128 := rfl
private theorem suffix_length_029 : suffix_029.length = 3730 := by
  rw [suffix_step_028, List.length_drop, suffix_length_028]
private theorem block_length_028 : certificates_28.length = 128 := by rfl
private theorem block_clauses_028 :
    certificates_28.map Prod.snd = suffix_028.take 128 := by rfl

private noncomputable def suffix_030 : List (List Sat.Literal) := suffix_029.drop 128
private theorem suffix_step_029 : suffix_030 = suffix_029.drop 128 := rfl
private theorem suffix_length_030 : suffix_030.length = 3602 := by
  rw [suffix_step_029, List.length_drop, suffix_length_029]
private theorem block_length_029 : certificates_29.length = 128 := by rfl
private theorem block_clauses_029 :
    certificates_29.map Prod.snd = suffix_029.take 128 := by rfl

private noncomputable def suffix_031 : List (List Sat.Literal) := suffix_030.drop 128
private theorem suffix_step_030 : suffix_031 = suffix_030.drop 128 := rfl
private theorem suffix_length_031 : suffix_031.length = 3474 := by
  rw [suffix_step_030, List.length_drop, suffix_length_030]
private theorem block_length_030 : certificates_30.length = 128 := by rfl
private theorem block_clauses_030 :
    certificates_30.map Prod.snd = suffix_030.take 128 := by rfl

private noncomputable def suffix_032 : List (List Sat.Literal) := suffix_031.drop 128
private theorem suffix_step_031 : suffix_032 = suffix_031.drop 128 := rfl
private theorem suffix_length_032 : suffix_032.length = 3346 := by
  rw [suffix_step_031, List.length_drop, suffix_length_031]
private theorem block_length_031 : certificates_31.length = 128 := by rfl
private theorem block_clauses_031 :
    certificates_31.map Prod.snd = suffix_031.take 128 := by rfl

private noncomputable def suffix_033 : List (List Sat.Literal) := suffix_032.drop 128
private theorem suffix_step_032 : suffix_033 = suffix_032.drop 128 := rfl
private theorem suffix_length_033 : suffix_033.length = 3218 := by
  rw [suffix_step_032, List.length_drop, suffix_length_032]
private theorem block_length_032 : certificates_32.length = 128 := by rfl
private theorem block_clauses_032 :
    certificates_32.map Prod.snd = suffix_032.take 128 := by rfl

private noncomputable def suffix_034 : List (List Sat.Literal) := suffix_033.drop 128
private theorem suffix_step_033 : suffix_034 = suffix_033.drop 128 := rfl
private theorem suffix_length_034 : suffix_034.length = 3090 := by
  rw [suffix_step_033, List.length_drop, suffix_length_033]
private theorem block_length_033 : certificates_33.length = 128 := by rfl
private theorem block_clauses_033 :
    certificates_33.map Prod.snd = suffix_033.take 128 := by rfl

private noncomputable def suffix_035 : List (List Sat.Literal) := suffix_034.drop 128
private theorem suffix_step_034 : suffix_035 = suffix_034.drop 128 := rfl
private theorem suffix_length_035 : suffix_035.length = 2962 := by
  rw [suffix_step_034, List.length_drop, suffix_length_034]
private theorem block_length_034 : certificates_34.length = 128 := by rfl
private theorem block_clauses_034 :
    certificates_34.map Prod.snd = suffix_034.take 128 := by rfl

private noncomputable def suffix_036 : List (List Sat.Literal) := suffix_035.drop 128
private theorem suffix_step_035 : suffix_036 = suffix_035.drop 128 := rfl
private theorem suffix_length_036 : suffix_036.length = 2834 := by
  rw [suffix_step_035, List.length_drop, suffix_length_035]
private theorem block_length_035 : certificates_35.length = 128 := by rfl
private theorem block_clauses_035 :
    certificates_35.map Prod.snd = suffix_035.take 128 := by rfl

private noncomputable def suffix_037 : List (List Sat.Literal) := suffix_036.drop 128
private theorem suffix_step_036 : suffix_037 = suffix_036.drop 128 := rfl
private theorem suffix_length_037 : suffix_037.length = 2706 := by
  rw [suffix_step_036, List.length_drop, suffix_length_036]
private theorem block_length_036 : certificates_36.length = 128 := by rfl
private theorem block_clauses_036 :
    certificates_36.map Prod.snd = suffix_036.take 128 := by rfl

private noncomputable def suffix_038 : List (List Sat.Literal) := suffix_037.drop 128
private theorem suffix_step_037 : suffix_038 = suffix_037.drop 128 := rfl
private theorem suffix_length_038 : suffix_038.length = 2578 := by
  rw [suffix_step_037, List.length_drop, suffix_length_037]
private theorem block_length_037 : certificates_37.length = 128 := by rfl
private theorem block_clauses_037 :
    certificates_37.map Prod.snd = suffix_037.take 128 := by rfl

private noncomputable def suffix_039 : List (List Sat.Literal) := suffix_038.drop 128
private theorem suffix_step_038 : suffix_039 = suffix_038.drop 128 := rfl
private theorem suffix_length_039 : suffix_039.length = 2450 := by
  rw [suffix_step_038, List.length_drop, suffix_length_038]
private theorem block_length_038 : certificates_38.length = 128 := by rfl
private theorem block_clauses_038 :
    certificates_38.map Prod.snd = suffix_038.take 128 := by rfl

private noncomputable def suffix_040 : List (List Sat.Literal) := suffix_039.drop 128
private theorem suffix_step_039 : suffix_040 = suffix_039.drop 128 := rfl
private theorem suffix_length_040 : suffix_040.length = 2322 := by
  rw [suffix_step_039, List.length_drop, suffix_length_039]
private theorem block_length_039 : certificates_39.length = 128 := by rfl
private theorem block_clauses_039 :
    certificates_39.map Prod.snd = suffix_039.take 128 := by rfl

private noncomputable def suffix_041 : List (List Sat.Literal) := suffix_040.drop 128
private theorem suffix_step_040 : suffix_041 = suffix_040.drop 128 := rfl
private theorem suffix_length_041 : suffix_041.length = 2194 := by
  rw [suffix_step_040, List.length_drop, suffix_length_040]
private theorem block_length_040 : certificates_40.length = 128 := by rfl
private theorem block_clauses_040 :
    certificates_40.map Prod.snd = suffix_040.take 128 := by rfl

private noncomputable def suffix_042 : List (List Sat.Literal) := suffix_041.drop 128
private theorem suffix_step_041 : suffix_042 = suffix_041.drop 128 := rfl
private theorem suffix_length_042 : suffix_042.length = 2066 := by
  rw [suffix_step_041, List.length_drop, suffix_length_041]
private theorem block_length_041 : certificates_41.length = 128 := by rfl
private theorem block_clauses_041 :
    certificates_41.map Prod.snd = suffix_041.take 128 := by rfl

private noncomputable def suffix_043 : List (List Sat.Literal) := suffix_042.drop 128
private theorem suffix_step_042 : suffix_043 = suffix_042.drop 128 := rfl
private theorem suffix_length_043 : suffix_043.length = 1938 := by
  rw [suffix_step_042, List.length_drop, suffix_length_042]
private theorem block_length_042 : certificates_42.length = 128 := by rfl
private theorem block_clauses_042 :
    certificates_42.map Prod.snd = suffix_042.take 128 := by rfl

private noncomputable def suffix_044 : List (List Sat.Literal) := suffix_043.drop 128
private theorem suffix_step_043 : suffix_044 = suffix_043.drop 128 := rfl
private theorem suffix_length_044 : suffix_044.length = 1810 := by
  rw [suffix_step_043, List.length_drop, suffix_length_043]
private theorem block_length_043 : certificates_43.length = 128 := by rfl
private theorem block_clauses_043 :
    certificates_43.map Prod.snd = suffix_043.take 128 := by rfl

private noncomputable def suffix_045 : List (List Sat.Literal) := suffix_044.drop 128
private theorem suffix_step_044 : suffix_045 = suffix_044.drop 128 := rfl
private theorem suffix_length_045 : suffix_045.length = 1682 := by
  rw [suffix_step_044, List.length_drop, suffix_length_044]
private theorem block_length_044 : certificates_44.length = 128 := by rfl
private theorem block_clauses_044 :
    certificates_44.map Prod.snd = suffix_044.take 128 := by rfl

private noncomputable def suffix_046 : List (List Sat.Literal) := suffix_045.drop 128
private theorem suffix_step_045 : suffix_046 = suffix_045.drop 128 := rfl
private theorem suffix_length_046 : suffix_046.length = 1554 := by
  rw [suffix_step_045, List.length_drop, suffix_length_045]
private theorem block_length_045 : certificates_45.length = 128 := by rfl
private theorem block_clauses_045 :
    certificates_45.map Prod.snd = suffix_045.take 128 := by rfl

private noncomputable def suffix_047 : List (List Sat.Literal) := suffix_046.drop 128
private theorem suffix_step_046 : suffix_047 = suffix_046.drop 128 := rfl
private theorem suffix_length_047 : suffix_047.length = 1426 := by
  rw [suffix_step_046, List.length_drop, suffix_length_046]
private theorem block_length_046 : certificates_46.length = 128 := by rfl
private theorem block_clauses_046 :
    certificates_46.map Prod.snd = suffix_046.take 128 := by rfl

private noncomputable def suffix_048 : List (List Sat.Literal) := suffix_047.drop 128
private theorem suffix_step_047 : suffix_048 = suffix_047.drop 128 := rfl
private theorem suffix_length_048 : suffix_048.length = 1298 := by
  rw [suffix_step_047, List.length_drop, suffix_length_047]
private theorem block_length_047 : certificates_47.length = 128 := by rfl
private theorem block_clauses_047 :
    certificates_47.map Prod.snd = suffix_047.take 128 := by rfl

private noncomputable def suffix_049 : List (List Sat.Literal) := suffix_048.drop 128
private theorem suffix_step_048 : suffix_049 = suffix_048.drop 128 := rfl
private theorem suffix_length_049 : suffix_049.length = 1170 := by
  rw [suffix_step_048, List.length_drop, suffix_length_048]
private theorem block_length_048 : certificates_48.length = 128 := by rfl
private theorem block_clauses_048 :
    certificates_48.map Prod.snd = suffix_048.take 128 := by rfl

private noncomputable def suffix_050 : List (List Sat.Literal) := suffix_049.drop 128
private theorem suffix_step_049 : suffix_050 = suffix_049.drop 128 := rfl
private theorem suffix_length_050 : suffix_050.length = 1042 := by
  rw [suffix_step_049, List.length_drop, suffix_length_049]
private theorem block_length_049 : certificates_49.length = 128 := by rfl
private theorem block_clauses_049 :
    certificates_49.map Prod.snd = suffix_049.take 128 := by rfl

private noncomputable def suffix_051 : List (List Sat.Literal) := suffix_050.drop 128
private theorem suffix_step_050 : suffix_051 = suffix_050.drop 128 := rfl
private theorem suffix_length_051 : suffix_051.length = 914 := by
  rw [suffix_step_050, List.length_drop, suffix_length_050]
private theorem block_length_050 : certificates_50.length = 128 := by rfl
private theorem block_clauses_050 :
    certificates_50.map Prod.snd = suffix_050.take 128 := by rfl

private noncomputable def suffix_052 : List (List Sat.Literal) := suffix_051.drop 128
private theorem suffix_step_051 : suffix_052 = suffix_051.drop 128 := rfl
private theorem suffix_length_052 : suffix_052.length = 786 := by
  rw [suffix_step_051, List.length_drop, suffix_length_051]
private theorem block_length_051 : certificates_51.length = 128 := by rfl
private theorem block_clauses_051 :
    certificates_51.map Prod.snd = suffix_051.take 128 := by rfl

private noncomputable def suffix_053 : List (List Sat.Literal) := suffix_052.drop 128
private theorem suffix_step_052 : suffix_053 = suffix_052.drop 128 := rfl
private theorem suffix_length_053 : suffix_053.length = 658 := by
  rw [suffix_step_052, List.length_drop, suffix_length_052]
private theorem block_length_052 : certificates_52.length = 128 := by rfl
private theorem block_clauses_052 :
    certificates_52.map Prod.snd = suffix_052.take 128 := by rfl

private noncomputable def suffix_054 : List (List Sat.Literal) := suffix_053.drop 128
private theorem suffix_step_053 : suffix_054 = suffix_053.drop 128 := rfl
private theorem suffix_length_054 : suffix_054.length = 530 := by
  rw [suffix_step_053, List.length_drop, suffix_length_053]
private theorem block_length_053 : certificates_53.length = 128 := by rfl
private theorem block_clauses_053 :
    certificates_53.map Prod.snd = suffix_053.take 128 := by rfl

private noncomputable def suffix_055 : List (List Sat.Literal) := suffix_054.drop 128
private theorem suffix_step_054 : suffix_055 = suffix_054.drop 128 := rfl
private theorem suffix_length_055 : suffix_055.length = 402 := by
  rw [suffix_step_054, List.length_drop, suffix_length_054]
private theorem block_length_054 : certificates_54.length = 128 := by rfl
private theorem block_clauses_054 :
    certificates_54.map Prod.snd = suffix_054.take 128 := by rfl

private noncomputable def suffix_056 : List (List Sat.Literal) := suffix_055.drop 128
private theorem suffix_step_055 : suffix_056 = suffix_055.drop 128 := rfl
private theorem suffix_length_056 : suffix_056.length = 274 := by
  rw [suffix_step_055, List.length_drop, suffix_length_055]
private theorem block_length_055 : certificates_55.length = 128 := by rfl
private theorem block_clauses_055 :
    certificates_55.map Prod.snd = suffix_055.take 128 := by rfl

private noncomputable def suffix_057 : List (List Sat.Literal) := suffix_056.drop 128
private theorem suffix_step_056 : suffix_057 = suffix_056.drop 128 := rfl
private theorem suffix_length_057 : suffix_057.length = 146 := by
  rw [suffix_step_056, List.length_drop, suffix_length_056]
private theorem block_length_056 : certificates_56.length = 128 := by rfl
private theorem block_clauses_056 :
    certificates_56.map Prod.snd = suffix_056.take 128 := by rfl

private noncomputable def suffix_058 : List (List Sat.Literal) := suffix_057.drop 128
private theorem suffix_step_057 : suffix_058 = suffix_057.drop 128 := rfl
private theorem suffix_length_058 : suffix_058.length = 18 := by
  rw [suffix_step_057, List.length_drop, suffix_length_057]
private theorem block_length_057 : certificates_57.length = 128 := by rfl
private theorem block_clauses_057 :
    certificates_57.map Prod.snd = suffix_057.take 128 := by rfl

private noncomputable def suffix_059 : List (List Sat.Literal) := suffix_058.drop 18
private theorem suffix_step_058 : suffix_059 = suffix_058.drop 18 := rfl
private theorem suffix_length_059 : suffix_059.length = 0 := by
  rw [suffix_step_058, List.length_drop, suffix_length_058]
private theorem block_length_058 : certificates_58.length = 18 := by rfl
private theorem block_clauses_058 :
    certificates_58.map Prod.snd = suffix_058.take 18 := by rfl

private theorem suffix_final_empty : suffix_059 = [] :=
  List.eq_nil_of_length_eq_zero suffix_length_059

private noncomputable def tail_058 := certificates_58
private theorem map_tail_058 : tail_058.map Prod.snd = suffix_058 := by
  change certificates_58.map Prod.snd = suffix_058
  rw [block_clauses_058]
  have h := List.take_append_drop 18 suffix_058
  rw [← suffix_step_058, suffix_final_empty, List.append_nil] at h
  exact h

private noncomputable def tail_057 := certificates_57 ++ tail_058
private theorem map_tail_057 : tail_057.map Prod.snd = suffix_057 := by
  change (certificates_57 ++ tail_058).map Prod.snd = suffix_057
  rw [List.map_append, block_clauses_057, map_tail_058, suffix_step_057,
    List.take_append_drop]

private noncomputable def tail_056 := certificates_56 ++ tail_057
private theorem map_tail_056 : tail_056.map Prod.snd = suffix_056 := by
  change (certificates_56 ++ tail_057).map Prod.snd = suffix_056
  rw [List.map_append, block_clauses_056, map_tail_057, suffix_step_056,
    List.take_append_drop]

private noncomputable def tail_055 := certificates_55 ++ tail_056
private theorem map_tail_055 : tail_055.map Prod.snd = suffix_055 := by
  change (certificates_55 ++ tail_056).map Prod.snd = suffix_055
  rw [List.map_append, block_clauses_055, map_tail_056, suffix_step_055,
    List.take_append_drop]

private noncomputable def tail_054 := certificates_54 ++ tail_055
private theorem map_tail_054 : tail_054.map Prod.snd = suffix_054 := by
  change (certificates_54 ++ tail_055).map Prod.snd = suffix_054
  rw [List.map_append, block_clauses_054, map_tail_055, suffix_step_054,
    List.take_append_drop]

private noncomputable def tail_053 := certificates_53 ++ tail_054
private theorem map_tail_053 : tail_053.map Prod.snd = suffix_053 := by
  change (certificates_53 ++ tail_054).map Prod.snd = suffix_053
  rw [List.map_append, block_clauses_053, map_tail_054, suffix_step_053,
    List.take_append_drop]

private noncomputable def tail_052 := certificates_52 ++ tail_053
private theorem map_tail_052 : tail_052.map Prod.snd = suffix_052 := by
  change (certificates_52 ++ tail_053).map Prod.snd = suffix_052
  rw [List.map_append, block_clauses_052, map_tail_053, suffix_step_052,
    List.take_append_drop]

private noncomputable def tail_051 := certificates_51 ++ tail_052
private theorem map_tail_051 : tail_051.map Prod.snd = suffix_051 := by
  change (certificates_51 ++ tail_052).map Prod.snd = suffix_051
  rw [List.map_append, block_clauses_051, map_tail_052, suffix_step_051,
    List.take_append_drop]

private noncomputable def tail_050 := certificates_50 ++ tail_051
private theorem map_tail_050 : tail_050.map Prod.snd = suffix_050 := by
  change (certificates_50 ++ tail_051).map Prod.snd = suffix_050
  rw [List.map_append, block_clauses_050, map_tail_051, suffix_step_050,
    List.take_append_drop]

private noncomputable def tail_049 := certificates_49 ++ tail_050
private theorem map_tail_049 : tail_049.map Prod.snd = suffix_049 := by
  change (certificates_49 ++ tail_050).map Prod.snd = suffix_049
  rw [List.map_append, block_clauses_049, map_tail_050, suffix_step_049,
    List.take_append_drop]

private noncomputable def tail_048 := certificates_48 ++ tail_049
private theorem map_tail_048 : tail_048.map Prod.snd = suffix_048 := by
  change (certificates_48 ++ tail_049).map Prod.snd = suffix_048
  rw [List.map_append, block_clauses_048, map_tail_049, suffix_step_048,
    List.take_append_drop]

private noncomputable def tail_047 := certificates_47 ++ tail_048
private theorem map_tail_047 : tail_047.map Prod.snd = suffix_047 := by
  change (certificates_47 ++ tail_048).map Prod.snd = suffix_047
  rw [List.map_append, block_clauses_047, map_tail_048, suffix_step_047,
    List.take_append_drop]

private noncomputable def tail_046 := certificates_46 ++ tail_047
private theorem map_tail_046 : tail_046.map Prod.snd = suffix_046 := by
  change (certificates_46 ++ tail_047).map Prod.snd = suffix_046
  rw [List.map_append, block_clauses_046, map_tail_047, suffix_step_046,
    List.take_append_drop]

private noncomputable def tail_045 := certificates_45 ++ tail_046
private theorem map_tail_045 : tail_045.map Prod.snd = suffix_045 := by
  change (certificates_45 ++ tail_046).map Prod.snd = suffix_045
  rw [List.map_append, block_clauses_045, map_tail_046, suffix_step_045,
    List.take_append_drop]

private noncomputable def tail_044 := certificates_44 ++ tail_045
private theorem map_tail_044 : tail_044.map Prod.snd = suffix_044 := by
  change (certificates_44 ++ tail_045).map Prod.snd = suffix_044
  rw [List.map_append, block_clauses_044, map_tail_045, suffix_step_044,
    List.take_append_drop]

private noncomputable def tail_043 := certificates_43 ++ tail_044
private theorem map_tail_043 : tail_043.map Prod.snd = suffix_043 := by
  change (certificates_43 ++ tail_044).map Prod.snd = suffix_043
  rw [List.map_append, block_clauses_043, map_tail_044, suffix_step_043,
    List.take_append_drop]

private noncomputable def tail_042 := certificates_42 ++ tail_043
private theorem map_tail_042 : tail_042.map Prod.snd = suffix_042 := by
  change (certificates_42 ++ tail_043).map Prod.snd = suffix_042
  rw [List.map_append, block_clauses_042, map_tail_043, suffix_step_042,
    List.take_append_drop]

private noncomputable def tail_041 := certificates_41 ++ tail_042
private theorem map_tail_041 : tail_041.map Prod.snd = suffix_041 := by
  change (certificates_41 ++ tail_042).map Prod.snd = suffix_041
  rw [List.map_append, block_clauses_041, map_tail_042, suffix_step_041,
    List.take_append_drop]

private noncomputable def tail_040 := certificates_40 ++ tail_041
private theorem map_tail_040 : tail_040.map Prod.snd = suffix_040 := by
  change (certificates_40 ++ tail_041).map Prod.snd = suffix_040
  rw [List.map_append, block_clauses_040, map_tail_041, suffix_step_040,
    List.take_append_drop]

private noncomputable def tail_039 := certificates_39 ++ tail_040
private theorem map_tail_039 : tail_039.map Prod.snd = suffix_039 := by
  change (certificates_39 ++ tail_040).map Prod.snd = suffix_039
  rw [List.map_append, block_clauses_039, map_tail_040, suffix_step_039,
    List.take_append_drop]

private noncomputable def tail_038 := certificates_38 ++ tail_039
private theorem map_tail_038 : tail_038.map Prod.snd = suffix_038 := by
  change (certificates_38 ++ tail_039).map Prod.snd = suffix_038
  rw [List.map_append, block_clauses_038, map_tail_039, suffix_step_038,
    List.take_append_drop]

private noncomputable def tail_037 := certificates_37 ++ tail_038
private theorem map_tail_037 : tail_037.map Prod.snd = suffix_037 := by
  change (certificates_37 ++ tail_038).map Prod.snd = suffix_037
  rw [List.map_append, block_clauses_037, map_tail_038, suffix_step_037,
    List.take_append_drop]

private noncomputable def tail_036 := certificates_36 ++ tail_037
private theorem map_tail_036 : tail_036.map Prod.snd = suffix_036 := by
  change (certificates_36 ++ tail_037).map Prod.snd = suffix_036
  rw [List.map_append, block_clauses_036, map_tail_037, suffix_step_036,
    List.take_append_drop]

private noncomputable def tail_035 := certificates_35 ++ tail_036
private theorem map_tail_035 : tail_035.map Prod.snd = suffix_035 := by
  change (certificates_35 ++ tail_036).map Prod.snd = suffix_035
  rw [List.map_append, block_clauses_035, map_tail_036, suffix_step_035,
    List.take_append_drop]

private noncomputable def tail_034 := certificates_34 ++ tail_035
private theorem map_tail_034 : tail_034.map Prod.snd = suffix_034 := by
  change (certificates_34 ++ tail_035).map Prod.snd = suffix_034
  rw [List.map_append, block_clauses_034, map_tail_035, suffix_step_034,
    List.take_append_drop]

private noncomputable def tail_033 := certificates_33 ++ tail_034
private theorem map_tail_033 : tail_033.map Prod.snd = suffix_033 := by
  change (certificates_33 ++ tail_034).map Prod.snd = suffix_033
  rw [List.map_append, block_clauses_033, map_tail_034, suffix_step_033,
    List.take_append_drop]

private noncomputable def tail_032 := certificates_32 ++ tail_033
private theorem map_tail_032 : tail_032.map Prod.snd = suffix_032 := by
  change (certificates_32 ++ tail_033).map Prod.snd = suffix_032
  rw [List.map_append, block_clauses_032, map_tail_033, suffix_step_032,
    List.take_append_drop]

private noncomputable def tail_031 := certificates_31 ++ tail_032
private theorem map_tail_031 : tail_031.map Prod.snd = suffix_031 := by
  change (certificates_31 ++ tail_032).map Prod.snd = suffix_031
  rw [List.map_append, block_clauses_031, map_tail_032, suffix_step_031,
    List.take_append_drop]

private noncomputable def tail_030 := certificates_30 ++ tail_031
private theorem map_tail_030 : tail_030.map Prod.snd = suffix_030 := by
  change (certificates_30 ++ tail_031).map Prod.snd = suffix_030
  rw [List.map_append, block_clauses_030, map_tail_031, suffix_step_030,
    List.take_append_drop]

private noncomputable def tail_029 := certificates_29 ++ tail_030
private theorem map_tail_029 : tail_029.map Prod.snd = suffix_029 := by
  change (certificates_29 ++ tail_030).map Prod.snd = suffix_029
  rw [List.map_append, block_clauses_029, map_tail_030, suffix_step_029,
    List.take_append_drop]

private noncomputable def tail_028 := certificates_28 ++ tail_029
private theorem map_tail_028 : tail_028.map Prod.snd = suffix_028 := by
  change (certificates_28 ++ tail_029).map Prod.snd = suffix_028
  rw [List.map_append, block_clauses_028, map_tail_029, suffix_step_028,
    List.take_append_drop]

private noncomputable def tail_027 := certificates_27 ++ tail_028
private theorem map_tail_027 : tail_027.map Prod.snd = suffix_027 := by
  change (certificates_27 ++ tail_028).map Prod.snd = suffix_027
  rw [List.map_append, block_clauses_027, map_tail_028, suffix_step_027,
    List.take_append_drop]

private noncomputable def tail_026 := certificates_26 ++ tail_027
private theorem map_tail_026 : tail_026.map Prod.snd = suffix_026 := by
  change (certificates_26 ++ tail_027).map Prod.snd = suffix_026
  rw [List.map_append, block_clauses_026, map_tail_027, suffix_step_026,
    List.take_append_drop]

private noncomputable def tail_025 := certificates_25 ++ tail_026
private theorem map_tail_025 : tail_025.map Prod.snd = suffix_025 := by
  change (certificates_25 ++ tail_026).map Prod.snd = suffix_025
  rw [List.map_append, block_clauses_025, map_tail_026, suffix_step_025,
    List.take_append_drop]

private noncomputable def tail_024 := certificates_24 ++ tail_025
private theorem map_tail_024 : tail_024.map Prod.snd = suffix_024 := by
  change (certificates_24 ++ tail_025).map Prod.snd = suffix_024
  rw [List.map_append, block_clauses_024, map_tail_025, suffix_step_024,
    List.take_append_drop]

private noncomputable def tail_023 := certificates_23 ++ tail_024
private theorem map_tail_023 : tail_023.map Prod.snd = suffix_023 := by
  change (certificates_23 ++ tail_024).map Prod.snd = suffix_023
  rw [List.map_append, block_clauses_023, map_tail_024, suffix_step_023,
    List.take_append_drop]

private noncomputable def tail_022 := certificates_22 ++ tail_023
private theorem map_tail_022 : tail_022.map Prod.snd = suffix_022 := by
  change (certificates_22 ++ tail_023).map Prod.snd = suffix_022
  rw [List.map_append, block_clauses_022, map_tail_023, suffix_step_022,
    List.take_append_drop]

private noncomputable def tail_021 := certificates_21 ++ tail_022
private theorem map_tail_021 : tail_021.map Prod.snd = suffix_021 := by
  change (certificates_21 ++ tail_022).map Prod.snd = suffix_021
  rw [List.map_append, block_clauses_021, map_tail_022, suffix_step_021,
    List.take_append_drop]

private noncomputable def tail_020 := certificates_20 ++ tail_021
private theorem map_tail_020 : tail_020.map Prod.snd = suffix_020 := by
  change (certificates_20 ++ tail_021).map Prod.snd = suffix_020
  rw [List.map_append, block_clauses_020, map_tail_021, suffix_step_020,
    List.take_append_drop]

private noncomputable def tail_019 := certificates_19 ++ tail_020
private theorem map_tail_019 : tail_019.map Prod.snd = suffix_019 := by
  change (certificates_19 ++ tail_020).map Prod.snd = suffix_019
  rw [List.map_append, block_clauses_019, map_tail_020, suffix_step_019,
    List.take_append_drop]

private noncomputable def tail_018 := certificates_18 ++ tail_019
private theorem map_tail_018 : tail_018.map Prod.snd = suffix_018 := by
  change (certificates_18 ++ tail_019).map Prod.snd = suffix_018
  rw [List.map_append, block_clauses_018, map_tail_019, suffix_step_018,
    List.take_append_drop]

private noncomputable def tail_017 := certificates_17 ++ tail_018
private theorem map_tail_017 : tail_017.map Prod.snd = suffix_017 := by
  change (certificates_17 ++ tail_018).map Prod.snd = suffix_017
  rw [List.map_append, block_clauses_017, map_tail_018, suffix_step_017,
    List.take_append_drop]

private noncomputable def tail_016 := certificates_16 ++ tail_017
private theorem map_tail_016 : tail_016.map Prod.snd = suffix_016 := by
  change (certificates_16 ++ tail_017).map Prod.snd = suffix_016
  rw [List.map_append, block_clauses_016, map_tail_017, suffix_step_016,
    List.take_append_drop]

private noncomputable def tail_015 := certificates_15 ++ tail_016
private theorem map_tail_015 : tail_015.map Prod.snd = suffix_015 := by
  change (certificates_15 ++ tail_016).map Prod.snd = suffix_015
  rw [List.map_append, block_clauses_015, map_tail_016, suffix_step_015,
    List.take_append_drop]

private noncomputable def tail_014 := certificates_14 ++ tail_015
private theorem map_tail_014 : tail_014.map Prod.snd = suffix_014 := by
  change (certificates_14 ++ tail_015).map Prod.snd = suffix_014
  rw [List.map_append, block_clauses_014, map_tail_015, suffix_step_014,
    List.take_append_drop]

private noncomputable def tail_013 := certificates_13 ++ tail_014
private theorem map_tail_013 : tail_013.map Prod.snd = suffix_013 := by
  change (certificates_13 ++ tail_014).map Prod.snd = suffix_013
  rw [List.map_append, block_clauses_013, map_tail_014, suffix_step_013,
    List.take_append_drop]

private noncomputable def tail_012 := certificates_12 ++ tail_013
private theorem map_tail_012 : tail_012.map Prod.snd = suffix_012 := by
  change (certificates_12 ++ tail_013).map Prod.snd = suffix_012
  rw [List.map_append, block_clauses_012, map_tail_013, suffix_step_012,
    List.take_append_drop]

private noncomputable def tail_011 := certificates_11 ++ tail_012
private theorem map_tail_011 : tail_011.map Prod.snd = suffix_011 := by
  change (certificates_11 ++ tail_012).map Prod.snd = suffix_011
  rw [List.map_append, block_clauses_011, map_tail_012, suffix_step_011,
    List.take_append_drop]

private noncomputable def tail_010 := certificates_10 ++ tail_011
private theorem map_tail_010 : tail_010.map Prod.snd = suffix_010 := by
  change (certificates_10 ++ tail_011).map Prod.snd = suffix_010
  rw [List.map_append, block_clauses_010, map_tail_011, suffix_step_010,
    List.take_append_drop]

private noncomputable def tail_009 := certificates_9 ++ tail_010
private theorem map_tail_009 : tail_009.map Prod.snd = suffix_009 := by
  change (certificates_9 ++ tail_010).map Prod.snd = suffix_009
  rw [List.map_append, block_clauses_009, map_tail_010, suffix_step_009,
    List.take_append_drop]

private noncomputable def tail_008 := certificates_8 ++ tail_009
private theorem map_tail_008 : tail_008.map Prod.snd = suffix_008 := by
  change (certificates_8 ++ tail_009).map Prod.snd = suffix_008
  rw [List.map_append, block_clauses_008, map_tail_009, suffix_step_008,
    List.take_append_drop]

private noncomputable def tail_007 := certificates_7 ++ tail_008
private theorem map_tail_007 : tail_007.map Prod.snd = suffix_007 := by
  change (certificates_7 ++ tail_008).map Prod.snd = suffix_007
  rw [List.map_append, block_clauses_007, map_tail_008, suffix_step_007,
    List.take_append_drop]

private noncomputable def tail_006 := certificates_6 ++ tail_007
private theorem map_tail_006 : tail_006.map Prod.snd = suffix_006 := by
  change (certificates_6 ++ tail_007).map Prod.snd = suffix_006
  rw [List.map_append, block_clauses_006, map_tail_007, suffix_step_006,
    List.take_append_drop]

private noncomputable def tail_005 := certificates_5 ++ tail_006
private theorem map_tail_005 : tail_005.map Prod.snd = suffix_005 := by
  change (certificates_5 ++ tail_006).map Prod.snd = suffix_005
  rw [List.map_append, block_clauses_005, map_tail_006, suffix_step_005,
    List.take_append_drop]

private noncomputable def tail_004 := certificates_4 ++ tail_005
private theorem map_tail_004 : tail_004.map Prod.snd = suffix_004 := by
  change (certificates_4 ++ tail_005).map Prod.snd = suffix_004
  rw [List.map_append, block_clauses_004, map_tail_005, suffix_step_004,
    List.take_append_drop]

private noncomputable def tail_003 := certificates_3 ++ tail_004
private theorem map_tail_003 : tail_003.map Prod.snd = suffix_003 := by
  change (certificates_3 ++ tail_004).map Prod.snd = suffix_003
  rw [List.map_append, block_clauses_003, map_tail_004, suffix_step_003,
    List.take_append_drop]

private noncomputable def tail_002 := certificates_2 ++ tail_003
private theorem map_tail_002 : tail_002.map Prod.snd = suffix_002 := by
  change (certificates_2 ++ tail_003).map Prod.snd = suffix_002
  rw [List.map_append, block_clauses_002, map_tail_003, suffix_step_002,
    List.take_append_drop]

private noncomputable def tail_001 := certificates_1 ++ tail_002
private theorem map_tail_001 : tail_001.map Prod.snd = suffix_001 := by
  change (certificates_1 ++ tail_002).map Prod.snd = suffix_001
  rw [List.map_append, block_clauses_001, map_tail_002, suffix_step_001,
    List.take_append_drop]

private noncomputable def tail_000 := certificates_0 ++ tail_001
private theorem map_tail_000 : tail_000.map Prod.snd = suffix_000 := by
  change (certificates_0 ++ tail_001).map Prod.snd = suffix_000
  rw [List.map_append, block_clauses_000, map_tail_001, suffix_step_000,
    List.take_append_drop]

/-- Entire original C84 certificate clause-map, including order and duplicates. -/
theorem clauses_eq :
    (certificates_0 ++ certificates_1 ++ certificates_2 ++ certificates_3 ++ certificates_4 ++ certificates_5 ++ certificates_6 ++ certificates_7 ++ certificates_8 ++ certificates_9 ++ certificates_10 ++ certificates_11 ++ certificates_12 ++ certificates_13 ++ certificates_14 ++ certificates_15 ++ certificates_16 ++ certificates_17 ++ certificates_18 ++ certificates_19 ++ certificates_20 ++ certificates_21 ++ certificates_22 ++ certificates_23 ++ certificates_24 ++ certificates_25 ++ certificates_26 ++ certificates_27 ++ certificates_28 ++ certificates_29 ++ certificates_30 ++ certificates_31 ++ certificates_32 ++ certificates_33 ++ certificates_34 ++ certificates_35 ++ certificates_36 ++ certificates_37 ++ certificates_38 ++ certificates_39 ++ certificates_40 ++ certificates_41 ++ certificates_42 ++ certificates_43 ++ certificates_44 ++ certificates_45 ++ certificates_46 ++ certificates_47 ++ certificates_48 ++ certificates_49 ++ certificates_50 ++ certificates_51 ++ certificates_52 ++ certificates_53 ++ certificates_54 ++ certificates_55 ++ certificates_56 ++ certificates_57 ++ certificates_58).map Prod.snd = Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C84.formula := by
  simpa only [tail_000, tail_001, tail_002, tail_003, tail_004, tail_005, tail_006, tail_007, tail_008, tail_009, tail_010, tail_011, tail_012, tail_013, tail_014, tail_015, tail_016, tail_017, tail_018, tail_019, tail_020, tail_021, tail_022, tail_023, tail_024, tail_025, tail_026, tail_027, tail_028, tail_029, tail_030, tail_031, tail_032, tail_033, tail_034, tail_035, tail_036, tail_037, tail_038, tail_039, tail_040, tail_041, tail_042, tail_043, tail_044, tail_045, tail_046, tail_047, tail_048, tail_049, tail_050, tail_051, tail_052, tail_053, tail_054, tail_055, tail_056, tail_057, tail_058, suffix_000, List.append_assoc] using map_tail_000

theorem formula_length : Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C84.formula.length = 7442 := suffix_length_000
end Papers.RationalityTen.MatroidChecked.C84ClauseMap

#print axioms Papers.RationalityTen.MatroidChecked.C84ClauseMap.clauses_eq
#print axioms Papers.RationalityTen.MatroidChecked.C84ClauseMap.formula_length

