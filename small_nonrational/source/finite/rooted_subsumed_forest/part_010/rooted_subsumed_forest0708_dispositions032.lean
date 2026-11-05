module
prelude
public import RootedSubsumedForest0708DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem disposition_at_1024 : dispositionTest 1024 = true := by decide +kernel

theorem disposition_at_1025 : dispositionTest 1025 = true := by decide +kernel

theorem disposition_at_1026 : dispositionTest 1026 = true := by decide +kernel

theorem disposition_at_1027 : dispositionTest 1027 = true := by decide +kernel

theorem disposition_at_1028 : dispositionTest 1028 = true := by decide +kernel

theorem disposition_at_1029 : dispositionTest 1029 = true := by decide +kernel

theorem disposition_at_1030 : dispositionTest 1030 = true := by decide +kernel

theorem disposition_at_1031 : dispositionTest 1031 = true := by decide +kernel

theorem disposition_at_1032 : dispositionTest 1032 = true := by decide +kernel

theorem disposition_at_1033 : dispositionTest 1033 = true := by decide +kernel

theorem disposition_at_1034 : dispositionTest 1034 = true := by decide +kernel

theorem disposition_at_1035 : dispositionTest 1035 = true := by decide +kernel

theorem disposition_at_1036 : dispositionTest 1036 = true := by decide +kernel

theorem disposition_at_1037 : dispositionTest 1037 = true := by decide +kernel

theorem disposition_at_1038 : dispositionTest 1038 = true := by decide +kernel

theorem disposition_at_1039 : dispositionTest 1039 = true := by decide +kernel

theorem disposition_at_1040 : dispositionTest 1040 = true := by decide +kernel

theorem disposition_at_1041 : dispositionTest 1041 = true := by decide +kernel

theorem disposition_at_1042 : dispositionTest 1042 = true := by decide +kernel

theorem disposition_at_1043 : dispositionTest 1043 = true := by decide +kernel

theorem disposition_at_1044 : dispositionTest 1044 = true := by decide +kernel

theorem disposition_at_1045 : dispositionTest 1045 = true := by decide +kernel

theorem disposition_at_1046 : dispositionTest 1046 = true := by decide +kernel

theorem disposition_at_1047 : dispositionTest 1047 = true := by decide +kernel

theorem disposition_at_1048 : dispositionTest 1048 = true := by decide +kernel

theorem disposition_at_1049 : dispositionTest 1049 = true := by decide +kernel

theorem disposition_at_1050 : dispositionTest 1050 = true := by decide +kernel

theorem disposition_at_1051 : dispositionTest 1051 = true := by decide +kernel

theorem disposition_at_1052 : dispositionTest 1052 = true := by decide +kernel

theorem disposition_at_1053 : dispositionTest 1053 = true := by decide +kernel

theorem disposition_at_1054 : dispositionTest 1054 = true := by decide +kernel

theorem disposition_at_1055 : dispositionTest 1055 = true := by decide +kernel

theorem disposition_interval_1024 : Interval dispositionTest 1024 1025 := by
  intro i hlo hhi
  have h : i = 1024 := by omega
  subst i
  exact disposition_at_1024


theorem disposition_interval_1025 : Interval dispositionTest 1025 1026 := by
  intro i hlo hhi
  have h : i = 1025 := by omega
  subst i
  exact disposition_at_1025


theorem disposition_interval_1026 : Interval dispositionTest 1026 1027 := by
  intro i hlo hhi
  have h : i = 1026 := by omega
  subst i
  exact disposition_at_1026


theorem disposition_interval_1027 : Interval dispositionTest 1027 1028 := by
  intro i hlo hhi
  have h : i = 1027 := by omega
  subst i
  exact disposition_at_1027


theorem disposition_interval_1028 : Interval dispositionTest 1028 1029 := by
  intro i hlo hhi
  have h : i = 1028 := by omega
  subst i
  exact disposition_at_1028


theorem disposition_interval_1029 : Interval dispositionTest 1029 1030 := by
  intro i hlo hhi
  have h : i = 1029 := by omega
  subst i
  exact disposition_at_1029


theorem disposition_interval_1030 : Interval dispositionTest 1030 1031 := by
  intro i hlo hhi
  have h : i = 1030 := by omega
  subst i
  exact disposition_at_1030


theorem disposition_interval_1031 : Interval dispositionTest 1031 1032 := by
  intro i hlo hhi
  have h : i = 1031 := by omega
  subst i
  exact disposition_at_1031


theorem disposition_interval_1032 : Interval dispositionTest 1032 1033 := by
  intro i hlo hhi
  have h : i = 1032 := by omega
  subst i
  exact disposition_at_1032


theorem disposition_interval_1033 : Interval dispositionTest 1033 1034 := by
  intro i hlo hhi
  have h : i = 1033 := by omega
  subst i
  exact disposition_at_1033


theorem disposition_interval_1034 : Interval dispositionTest 1034 1035 := by
  intro i hlo hhi
  have h : i = 1034 := by omega
  subst i
  exact disposition_at_1034


theorem disposition_interval_1035 : Interval dispositionTest 1035 1036 := by
  intro i hlo hhi
  have h : i = 1035 := by omega
  subst i
  exact disposition_at_1035


theorem disposition_interval_1036 : Interval dispositionTest 1036 1037 := by
  intro i hlo hhi
  have h : i = 1036 := by omega
  subst i
  exact disposition_at_1036


theorem disposition_interval_1037 : Interval dispositionTest 1037 1038 := by
  intro i hlo hhi
  have h : i = 1037 := by omega
  subst i
  exact disposition_at_1037


theorem disposition_interval_1038 : Interval dispositionTest 1038 1039 := by
  intro i hlo hhi
  have h : i = 1038 := by omega
  subst i
  exact disposition_at_1038


theorem disposition_interval_1039 : Interval dispositionTest 1039 1040 := by
  intro i hlo hhi
  have h : i = 1039 := by omega
  subst i
  exact disposition_at_1039


theorem disposition_interval_1040 : Interval dispositionTest 1040 1041 := by
  intro i hlo hhi
  have h : i = 1040 := by omega
  subst i
  exact disposition_at_1040


theorem disposition_interval_1041 : Interval dispositionTest 1041 1042 := by
  intro i hlo hhi
  have h : i = 1041 := by omega
  subst i
  exact disposition_at_1041


theorem disposition_interval_1042 : Interval dispositionTest 1042 1043 := by
  intro i hlo hhi
  have h : i = 1042 := by omega
  subst i
  exact disposition_at_1042


theorem disposition_interval_1043 : Interval dispositionTest 1043 1044 := by
  intro i hlo hhi
  have h : i = 1043 := by omega
  subst i
  exact disposition_at_1043


theorem disposition_interval_1044 : Interval dispositionTest 1044 1045 := by
  intro i hlo hhi
  have h : i = 1044 := by omega
  subst i
  exact disposition_at_1044


theorem disposition_interval_1045 : Interval dispositionTest 1045 1046 := by
  intro i hlo hhi
  have h : i = 1045 := by omega
  subst i
  exact disposition_at_1045


theorem disposition_interval_1046 : Interval dispositionTest 1046 1047 := by
  intro i hlo hhi
  have h : i = 1046 := by omega
  subst i
  exact disposition_at_1046


theorem disposition_interval_1047 : Interval dispositionTest 1047 1048 := by
  intro i hlo hhi
  have h : i = 1047 := by omega
  subst i
  exact disposition_at_1047


theorem disposition_interval_1048 : Interval dispositionTest 1048 1049 := by
  intro i hlo hhi
  have h : i = 1048 := by omega
  subst i
  exact disposition_at_1048


theorem disposition_interval_1049 : Interval dispositionTest 1049 1050 := by
  intro i hlo hhi
  have h : i = 1049 := by omega
  subst i
  exact disposition_at_1049


theorem disposition_interval_1050 : Interval dispositionTest 1050 1051 := by
  intro i hlo hhi
  have h : i = 1050 := by omega
  subst i
  exact disposition_at_1050


theorem disposition_interval_1051 : Interval dispositionTest 1051 1052 := by
  intro i hlo hhi
  have h : i = 1051 := by omega
  subst i
  exact disposition_at_1051


theorem disposition_interval_1052 : Interval dispositionTest 1052 1053 := by
  intro i hlo hhi
  have h : i = 1052 := by omega
  subst i
  exact disposition_at_1052


theorem disposition_interval_1053 : Interval dispositionTest 1053 1054 := by
  intro i hlo hhi
  have h : i = 1053 := by omega
  subst i
  exact disposition_at_1053


theorem disposition_interval_1054 : Interval dispositionTest 1054 1055 := by
  intro i hlo hhi
  have h : i = 1054 := by omega
  subst i
  exact disposition_at_1054


theorem disposition_interval_1055 : Interval dispositionTest 1055 1056 := by
  intro i hlo hhi
  have h : i = 1055 := by omega
  subst i
  exact disposition_at_1055

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
