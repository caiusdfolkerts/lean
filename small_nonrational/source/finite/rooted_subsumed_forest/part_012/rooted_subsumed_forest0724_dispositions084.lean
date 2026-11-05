module
prelude
public import RootedSubsumedForest0724DispositionData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem disposition_at_2688 : dispositionTest 2688 = true := by decide +kernel

theorem disposition_at_2689 : dispositionTest 2689 = true := by decide +kernel

theorem disposition_at_2690 : dispositionTest 2690 = true := by decide +kernel

theorem disposition_at_2691 : dispositionTest 2691 = true := by decide +kernel

theorem disposition_at_2692 : dispositionTest 2692 = true := by decide +kernel

theorem disposition_at_2693 : dispositionTest 2693 = true := by decide +kernel

theorem disposition_at_2694 : dispositionTest 2694 = true := by decide +kernel

theorem disposition_at_2695 : dispositionTest 2695 = true := by decide +kernel


theorem disposition_at_2696 : dispositionTest 2696 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 2696).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) Nonrational.OldTerminalMatches.M024.r1544.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M024.r1544) = true
  rw [Nonrational.OldTerminalMatches.M024.r1544_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_2697 : dispositionTest 2697 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 2697).map Papers.RationalityTen.RootedCaches.RootedSixBase03.rawCells) Nonrational.OldTerminalMatches.M024.r1545.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M024.r1545) = true
  rw [Nonrational.OldTerminalMatches.M024.r1545_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_2698 : dispositionTest 2698 = true := by decide +kernel

theorem disposition_at_2699 : dispositionTest 2699 = true := by decide +kernel

theorem disposition_at_2700 : dispositionTest 2700 = true := by decide +kernel

theorem disposition_at_2701 : dispositionTest 2701 = true := by decide +kernel

theorem disposition_at_2702 : dispositionTest 2702 = true := by decide +kernel

theorem disposition_at_2703 : dispositionTest 2703 = true := by decide +kernel

theorem disposition_at_2704 : dispositionTest 2704 = true := by decide +kernel

theorem disposition_at_2705 : dispositionTest 2705 = true := by decide +kernel

theorem disposition_at_2706 : dispositionTest 2706 = true := by decide +kernel

theorem disposition_at_2707 : dispositionTest 2707 = true := by decide +kernel

theorem disposition_at_2708 : dispositionTest 2708 = true := by decide +kernel

theorem disposition_at_2709 : dispositionTest 2709 = true := by decide +kernel

theorem disposition_at_2710 : dispositionTest 2710 = true := by decide +kernel

theorem disposition_at_2711 : dispositionTest 2711 = true := by decide +kernel

theorem disposition_at_2712 : dispositionTest 2712 = true := by decide +kernel

theorem disposition_at_2713 : dispositionTest 2713 = true := by decide +kernel

theorem disposition_at_2714 : dispositionTest 2714 = true := by decide +kernel

theorem disposition_at_2715 : dispositionTest 2715 = true := by decide +kernel

theorem disposition_at_2716 : dispositionTest 2716 = true := by decide +kernel

theorem disposition_at_2717 : dispositionTest 2717 = true := by decide +kernel

theorem disposition_at_2718 : dispositionTest 2718 = true := by decide +kernel

theorem disposition_at_2719 : dispositionTest 2719 = true := by decide +kernel

theorem disposition_interval_2688 : Interval dispositionTest 2688 2689 := by
  intro i hlo hhi
  have h : i = 2688 := by omega
  subst i
  exact disposition_at_2688


theorem disposition_interval_2689 : Interval dispositionTest 2689 2690 := by
  intro i hlo hhi
  have h : i = 2689 := by omega
  subst i
  exact disposition_at_2689


theorem disposition_interval_2690 : Interval dispositionTest 2690 2691 := by
  intro i hlo hhi
  have h : i = 2690 := by omega
  subst i
  exact disposition_at_2690


theorem disposition_interval_2691 : Interval dispositionTest 2691 2692 := by
  intro i hlo hhi
  have h : i = 2691 := by omega
  subst i
  exact disposition_at_2691


theorem disposition_interval_2692 : Interval dispositionTest 2692 2693 := by
  intro i hlo hhi
  have h : i = 2692 := by omega
  subst i
  exact disposition_at_2692


theorem disposition_interval_2693 : Interval dispositionTest 2693 2694 := by
  intro i hlo hhi
  have h : i = 2693 := by omega
  subst i
  exact disposition_at_2693


theorem disposition_interval_2694 : Interval dispositionTest 2694 2695 := by
  intro i hlo hhi
  have h : i = 2694 := by omega
  subst i
  exact disposition_at_2694


theorem disposition_interval_2695 : Interval dispositionTest 2695 2696 := by
  intro i hlo hhi
  have h : i = 2695 := by omega
  subst i
  exact disposition_at_2695


theorem disposition_interval_2696 : Interval dispositionTest 2696 2697 := by
  intro i hlo hhi
  have h : i = 2696 := by omega
  subst i
  exact disposition_at_2696


theorem disposition_interval_2697 : Interval dispositionTest 2697 2698 := by
  intro i hlo hhi
  have h : i = 2697 := by omega
  subst i
  exact disposition_at_2697


theorem disposition_interval_2698 : Interval dispositionTest 2698 2699 := by
  intro i hlo hhi
  have h : i = 2698 := by omega
  subst i
  exact disposition_at_2698


theorem disposition_interval_2699 : Interval dispositionTest 2699 2700 := by
  intro i hlo hhi
  have h : i = 2699 := by omega
  subst i
  exact disposition_at_2699


theorem disposition_interval_2700 : Interval dispositionTest 2700 2701 := by
  intro i hlo hhi
  have h : i = 2700 := by omega
  subst i
  exact disposition_at_2700


theorem disposition_interval_2701 : Interval dispositionTest 2701 2702 := by
  intro i hlo hhi
  have h : i = 2701 := by omega
  subst i
  exact disposition_at_2701


theorem disposition_interval_2702 : Interval dispositionTest 2702 2703 := by
  intro i hlo hhi
  have h : i = 2702 := by omega
  subst i
  exact disposition_at_2702


theorem disposition_interval_2703 : Interval dispositionTest 2703 2704 := by
  intro i hlo hhi
  have h : i = 2703 := by omega
  subst i
  exact disposition_at_2703


theorem disposition_interval_2704 : Interval dispositionTest 2704 2705 := by
  intro i hlo hhi
  have h : i = 2704 := by omega
  subst i
  exact disposition_at_2704


theorem disposition_interval_2705 : Interval dispositionTest 2705 2706 := by
  intro i hlo hhi
  have h : i = 2705 := by omega
  subst i
  exact disposition_at_2705


theorem disposition_interval_2706 : Interval dispositionTest 2706 2707 := by
  intro i hlo hhi
  have h : i = 2706 := by omega
  subst i
  exact disposition_at_2706


theorem disposition_interval_2707 : Interval dispositionTest 2707 2708 := by
  intro i hlo hhi
  have h : i = 2707 := by omega
  subst i
  exact disposition_at_2707


theorem disposition_interval_2708 : Interval dispositionTest 2708 2709 := by
  intro i hlo hhi
  have h : i = 2708 := by omega
  subst i
  exact disposition_at_2708


theorem disposition_interval_2709 : Interval dispositionTest 2709 2710 := by
  intro i hlo hhi
  have h : i = 2709 := by omega
  subst i
  exact disposition_at_2709


theorem disposition_interval_2710 : Interval dispositionTest 2710 2711 := by
  intro i hlo hhi
  have h : i = 2710 := by omega
  subst i
  exact disposition_at_2710


theorem disposition_interval_2711 : Interval dispositionTest 2711 2712 := by
  intro i hlo hhi
  have h : i = 2711 := by omega
  subst i
  exact disposition_at_2711


theorem disposition_interval_2712 : Interval dispositionTest 2712 2713 := by
  intro i hlo hhi
  have h : i = 2712 := by omega
  subst i
  exact disposition_at_2712


theorem disposition_interval_2713 : Interval dispositionTest 2713 2714 := by
  intro i hlo hhi
  have h : i = 2713 := by omega
  subst i
  exact disposition_at_2713


theorem disposition_interval_2714 : Interval dispositionTest 2714 2715 := by
  intro i hlo hhi
  have h : i = 2714 := by omega
  subst i
  exact disposition_at_2714


theorem disposition_interval_2715 : Interval dispositionTest 2715 2716 := by
  intro i hlo hhi
  have h : i = 2715 := by omega
  subst i
  exact disposition_at_2715


theorem disposition_interval_2716 : Interval dispositionTest 2716 2717 := by
  intro i hlo hhi
  have h : i = 2716 := by omega
  subst i
  exact disposition_at_2716


theorem disposition_interval_2717 : Interval dispositionTest 2717 2718 := by
  intro i hlo hhi
  have h : i = 2717 := by omega
  subst i
  exact disposition_at_2717


theorem disposition_interval_2718 : Interval dispositionTest 2718 2719 := by
  intro i hlo hhi
  have h : i = 2718 := by omega
  subst i
  exact disposition_at_2718


theorem disposition_interval_2719 : Interval dispositionTest 2719 2720 := by
  intro i hlo hhi
  have h : i = 2719 := by omega
  subst i
  exact disposition_at_2719

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
