module
prelude
public import RootedSubsumedForest0348DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0348
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem disposition_at_64 : dispositionTest 64 = true := by decide +kernel

theorem disposition_at_65 : dispositionTest 65 = true := by decide +kernel

theorem disposition_at_66 : dispositionTest 66 = true := by decide +kernel

theorem disposition_at_67 : dispositionTest 67 = true := by decide +kernel

theorem disposition_at_68 : dispositionTest 68 = true := by decide +kernel

theorem disposition_at_69 : dispositionTest 69 = true := by decide +kernel


theorem disposition_at_70 : dispositionTest 70 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 70).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells) Nonrational.OldTerminalMatches.M011.r0733.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M011.r0733) = true
  rw [Nonrational.OldTerminalMatches.M011.r0733_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_71 : dispositionTest 71 = true := by decide +kernel

theorem disposition_at_72 : dispositionTest 72 = true := by decide +kernel

theorem disposition_at_73 : dispositionTest 73 = true := by decide +kernel

theorem disposition_at_74 : dispositionTest 74 = true := by decide +kernel

theorem disposition_at_75 : dispositionTest 75 = true := by decide +kernel

theorem disposition_at_76 : dispositionTest 76 = true := by decide +kernel

theorem disposition_at_77 : dispositionTest 77 = true := by decide +kernel

theorem disposition_at_78 : dispositionTest 78 = true := by decide +kernel

theorem disposition_at_79 : dispositionTest 79 = true := by decide +kernel

theorem disposition_at_80 : dispositionTest 80 = true := by decide +kernel

theorem disposition_at_81 : dispositionTest 81 = true := by decide +kernel

theorem disposition_at_82 : dispositionTest 82 = true := by decide +kernel

theorem disposition_at_83 : dispositionTest 83 = true := by decide +kernel

theorem disposition_at_84 : dispositionTest 84 = true := by decide +kernel

theorem disposition_at_85 : dispositionTest 85 = true := by decide +kernel

theorem disposition_at_86 : dispositionTest 86 = true := by decide +kernel

theorem disposition_at_87 : dispositionTest 87 = true := by decide +kernel

theorem disposition_at_88 : dispositionTest 88 = true := by decide +kernel

theorem disposition_interval_64 : Interval dispositionTest 64 65 := by
  intro i hlo hhi
  have h : i = 64 := by omega
  subst i
  exact disposition_at_64


theorem disposition_interval_65 : Interval dispositionTest 65 66 := by
  intro i hlo hhi
  have h : i = 65 := by omega
  subst i
  exact disposition_at_65


theorem disposition_interval_66 : Interval dispositionTest 66 67 := by
  intro i hlo hhi
  have h : i = 66 := by omega
  subst i
  exact disposition_at_66


theorem disposition_interval_67 : Interval dispositionTest 67 68 := by
  intro i hlo hhi
  have h : i = 67 := by omega
  subst i
  exact disposition_at_67


theorem disposition_interval_68 : Interval dispositionTest 68 69 := by
  intro i hlo hhi
  have h : i = 68 := by omega
  subst i
  exact disposition_at_68


theorem disposition_interval_69 : Interval dispositionTest 69 70 := by
  intro i hlo hhi
  have h : i = 69 := by omega
  subst i
  exact disposition_at_69


theorem disposition_interval_70 : Interval dispositionTest 70 71 := by
  intro i hlo hhi
  have h : i = 70 := by omega
  subst i
  exact disposition_at_70


theorem disposition_interval_71 : Interval dispositionTest 71 72 := by
  intro i hlo hhi
  have h : i = 71 := by omega
  subst i
  exact disposition_at_71


theorem disposition_interval_72 : Interval dispositionTest 72 73 := by
  intro i hlo hhi
  have h : i = 72 := by omega
  subst i
  exact disposition_at_72


theorem disposition_interval_73 : Interval dispositionTest 73 74 := by
  intro i hlo hhi
  have h : i = 73 := by omega
  subst i
  exact disposition_at_73


theorem disposition_interval_74 : Interval dispositionTest 74 75 := by
  intro i hlo hhi
  have h : i = 74 := by omega
  subst i
  exact disposition_at_74


theorem disposition_interval_75 : Interval dispositionTest 75 76 := by
  intro i hlo hhi
  have h : i = 75 := by omega
  subst i
  exact disposition_at_75


theorem disposition_interval_76 : Interval dispositionTest 76 77 := by
  intro i hlo hhi
  have h : i = 76 := by omega
  subst i
  exact disposition_at_76


theorem disposition_interval_77 : Interval dispositionTest 77 78 := by
  intro i hlo hhi
  have h : i = 77 := by omega
  subst i
  exact disposition_at_77


theorem disposition_interval_78 : Interval dispositionTest 78 79 := by
  intro i hlo hhi
  have h : i = 78 := by omega
  subst i
  exact disposition_at_78


theorem disposition_interval_79 : Interval dispositionTest 79 80 := by
  intro i hlo hhi
  have h : i = 79 := by omega
  subst i
  exact disposition_at_79


theorem disposition_interval_80 : Interval dispositionTest 80 81 := by
  intro i hlo hhi
  have h : i = 80 := by omega
  subst i
  exact disposition_at_80


theorem disposition_interval_81 : Interval dispositionTest 81 82 := by
  intro i hlo hhi
  have h : i = 81 := by omega
  subst i
  exact disposition_at_81


theorem disposition_interval_82 : Interval dispositionTest 82 83 := by
  intro i hlo hhi
  have h : i = 82 := by omega
  subst i
  exact disposition_at_82


theorem disposition_interval_83 : Interval dispositionTest 83 84 := by
  intro i hlo hhi
  have h : i = 83 := by omega
  subst i
  exact disposition_at_83


theorem disposition_interval_84 : Interval dispositionTest 84 85 := by
  intro i hlo hhi
  have h : i = 84 := by omega
  subst i
  exact disposition_at_84


theorem disposition_interval_85 : Interval dispositionTest 85 86 := by
  intro i hlo hhi
  have h : i = 85 := by omega
  subst i
  exact disposition_at_85


theorem disposition_interval_86 : Interval dispositionTest 86 87 := by
  intro i hlo hhi
  have h : i = 86 := by omega
  subst i
  exact disposition_at_86


theorem disposition_interval_87 : Interval dispositionTest 87 88 := by
  intro i hlo hhi
  have h : i = 87 := by omega
  subst i
  exact disposition_at_87


theorem disposition_interval_88 : Interval dispositionTest 88 89 := by
  intro i hlo hhi
  have h : i = 88 := by omega
  subst i
  exact disposition_at_88

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0348
