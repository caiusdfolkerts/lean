module
prelude
public import SmallSubsumedForest10Data
public import RawLeafCertificate
public import OldTerminalMatches.M000

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest10
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.quota 2))
 (.leaf (.incidence 6)))
 (.leaf (.incidence 6)))
 (.branch 6
 (.branch 5
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0020))
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0021)))
 (.branch 7
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0022))
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0023)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (.incidence 4))
 (.leaf (.quota 2)))
 (.leaf (.incidence 4)))
 (.branch 14
 (.branch 13
 (.leaf (.incidence 4))
 (.leaf (.quota 2)))
 (.leaf (.incidence 7)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0024))
 (.leaf (.incidence 7)))
 (.branch 19
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0025))
 (.leaf (.incidence 7))))
 (.branch 22
 (.branch 21
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0026))
 (.leaf (.incidence 7)))
 (.branch 23
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0027))
 (.leaf (.incidence 7)))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf (.incidence 9))
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0028)))
 (.leaf (.incidence 3)))
 (.branch 30
 (.branch 29
 (.leaf (.incidence 3))
 (.leaf (.quota 2)))
 (.branch 31
 (.leaf (.incidence 3))
 (.leaf (.quota 2)))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map RootedSmallCache.rawCells) (dispositionTable.get i)
theorem disposition_at_0 : dispositionTest 0 = true := by decide +kernel

theorem disposition_at_1 : dispositionTest 1 = true := by decide +kernel

theorem disposition_at_2 : dispositionTest 2 = true := by decide +kernel

theorem disposition_at_3 : dispositionTest 3 = true := by decide +kernel


theorem disposition_at_4 : dispositionTest 4 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 4).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M000.r0020.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M000.r0020) = true
  rw [Nonrational.OldTerminalMatches.M000.r0020_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_5 : dispositionTest 5 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 5).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M000.r0021.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M000.r0021) = true
  rw [Nonrational.OldTerminalMatches.M000.r0021_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_6 : dispositionTest 6 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 6).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M000.r0022.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M000.r0022) = true
  rw [Nonrational.OldTerminalMatches.M000.r0022_checked, Bool.and_true]
  decide +kernel


theorem disposition_at_7 : dispositionTest 7 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 7).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M000.r0023.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M000.r0023) = true
  rw [Nonrational.OldTerminalMatches.M000.r0023_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_8 : dispositionTest 8 = true := by decide +kernel

theorem disposition_at_9 : dispositionTest 9 = true := by decide +kernel

theorem disposition_at_10 : dispositionTest 10 = true := by decide +kernel

theorem disposition_at_11 : dispositionTest 11 = true := by decide +kernel

theorem disposition_at_12 : dispositionTest 12 = true := by decide +kernel

theorem disposition_at_13 : dispositionTest 13 = true := by decide +kernel

theorem disposition_at_14 : dispositionTest 14 = true := by decide +kernel

theorem disposition_at_15 : dispositionTest 15 = true := by decide +kernel


theorem disposition_at_16 : dispositionTest 16 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 16).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M000.r0024.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M000.r0024) = true
  rw [Nonrational.OldTerminalMatches.M000.r0024_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_17 : dispositionTest 17 = true := by decide +kernel


theorem disposition_at_18 : dispositionTest 18 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 18).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M000.r0025.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M000.r0025) = true
  rw [Nonrational.OldTerminalMatches.M000.r0025_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_19 : dispositionTest 19 = true := by decide +kernel


theorem disposition_at_20 : dispositionTest 20 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 20).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M000.r0026.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M000.r0026) = true
  rw [Nonrational.OldTerminalMatches.M000.r0026_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_21 : dispositionTest 21 = true := by decide +kernel


theorem disposition_at_22 : dispositionTest 22 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 22).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M000.r0027.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M000.r0027) = true
  rw [Nonrational.OldTerminalMatches.M000.r0027_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_23 : dispositionTest 23 = true := by decide +kernel

theorem disposition_at_24 : dispositionTest 24 = true := by decide +kernel


theorem disposition_at_25 : dispositionTest 25 = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves 25).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M000.r0028.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M000.r0028) = true
  rw [Nonrational.OldTerminalMatches.M000.r0028_checked, Bool.and_true]
  decide +kernel

theorem disposition_at_26 : dispositionTest 26 = true := by decide +kernel

theorem disposition_at_27 : dispositionTest 27 = true := by decide +kernel

theorem disposition_at_28 : dispositionTest 28 = true := by decide +kernel

theorem disposition_at_29 : dispositionTest 29 = true := by decide +kernel

theorem disposition_at_30 : dispositionTest 30 = true := by decide +kernel

theorem disposition_at_31 : dispositionTest 31 = true := by decide +kernel

theorem disposition_interval_0 : Interval dispositionTest 0 1 := by
  intro i hlo hhi
  have h : i = 0 := by omega
  subst i
  exact disposition_at_0

theorem disposition_interval_1 : Interval dispositionTest 1 2 := by
  intro i hlo hhi
  have h : i = 1 := by omega
  subst i
  exact disposition_at_1

theorem disposition_interval_2 : Interval dispositionTest 2 3 := by
  intro i hlo hhi
  have h : i = 2 := by omega
  subst i
  exact disposition_at_2

theorem disposition_interval_3 : Interval dispositionTest 3 4 := by
  intro i hlo hhi
  have h : i = 3 := by omega
  subst i
  exact disposition_at_3

theorem disposition_interval_4 : Interval dispositionTest 4 5 := by
  intro i hlo hhi
  have h : i = 4 := by omega
  subst i
  exact disposition_at_4

theorem disposition_interval_5 : Interval dispositionTest 5 6 := by
  intro i hlo hhi
  have h : i = 5 := by omega
  subst i
  exact disposition_at_5

theorem disposition_interval_6 : Interval dispositionTest 6 7 := by
  intro i hlo hhi
  have h : i = 6 := by omega
  subst i
  exact disposition_at_6

theorem disposition_interval_7 : Interval dispositionTest 7 8 := by
  intro i hlo hhi
  have h : i = 7 := by omega
  subst i
  exact disposition_at_7

theorem disposition_interval_8 : Interval dispositionTest 8 9 := by
  intro i hlo hhi
  have h : i = 8 := by omega
  subst i
  exact disposition_at_8

theorem disposition_interval_9 : Interval dispositionTest 9 10 := by
  intro i hlo hhi
  have h : i = 9 := by omega
  subst i
  exact disposition_at_9

theorem disposition_interval_10 : Interval dispositionTest 10 11 := by
  intro i hlo hhi
  have h : i = 10 := by omega
  subst i
  exact disposition_at_10

theorem disposition_interval_11 : Interval dispositionTest 11 12 := by
  intro i hlo hhi
  have h : i = 11 := by omega
  subst i
  exact disposition_at_11

theorem disposition_interval_12 : Interval dispositionTest 12 13 := by
  intro i hlo hhi
  have h : i = 12 := by omega
  subst i
  exact disposition_at_12

theorem disposition_interval_13 : Interval dispositionTest 13 14 := by
  intro i hlo hhi
  have h : i = 13 := by omega
  subst i
  exact disposition_at_13

theorem disposition_interval_14 : Interval dispositionTest 14 15 := by
  intro i hlo hhi
  have h : i = 14 := by omega
  subst i
  exact disposition_at_14

theorem disposition_interval_15 : Interval dispositionTest 15 16 := by
  intro i hlo hhi
  have h : i = 15 := by omega
  subst i
  exact disposition_at_15

theorem disposition_interval_16 : Interval dispositionTest 16 17 := by
  intro i hlo hhi
  have h : i = 16 := by omega
  subst i
  exact disposition_at_16

theorem disposition_interval_17 : Interval dispositionTest 17 18 := by
  intro i hlo hhi
  have h : i = 17 := by omega
  subst i
  exact disposition_at_17

theorem disposition_interval_18 : Interval dispositionTest 18 19 := by
  intro i hlo hhi
  have h : i = 18 := by omega
  subst i
  exact disposition_at_18

theorem disposition_interval_19 : Interval dispositionTest 19 20 := by
  intro i hlo hhi
  have h : i = 19 := by omega
  subst i
  exact disposition_at_19

theorem disposition_interval_20 : Interval dispositionTest 20 21 := by
  intro i hlo hhi
  have h : i = 20 := by omega
  subst i
  exact disposition_at_20

theorem disposition_interval_21 : Interval dispositionTest 21 22 := by
  intro i hlo hhi
  have h : i = 21 := by omega
  subst i
  exact disposition_at_21

theorem disposition_interval_22 : Interval dispositionTest 22 23 := by
  intro i hlo hhi
  have h : i = 22 := by omega
  subst i
  exact disposition_at_22

theorem disposition_interval_23 : Interval dispositionTest 23 24 := by
  intro i hlo hhi
  have h : i = 23 := by omega
  subst i
  exact disposition_at_23

theorem disposition_interval_24 : Interval dispositionTest 24 25 := by
  intro i hlo hhi
  have h : i = 24 := by omega
  subst i
  exact disposition_at_24

theorem disposition_interval_25 : Interval dispositionTest 25 26 := by
  intro i hlo hhi
  have h : i = 25 := by omega
  subst i
  exact disposition_at_25

theorem disposition_interval_26 : Interval dispositionTest 26 27 := by
  intro i hlo hhi
  have h : i = 26 := by omega
  subst i
  exact disposition_at_26

theorem disposition_interval_27 : Interval dispositionTest 27 28 := by
  intro i hlo hhi
  have h : i = 27 := by omega
  subst i
  exact disposition_at_27

theorem disposition_interval_28 : Interval dispositionTest 28 29 := by
  intro i hlo hhi
  have h : i = 28 := by omega
  subst i
  exact disposition_at_28

theorem disposition_interval_29 : Interval dispositionTest 29 30 := by
  intro i hlo hhi
  have h : i = 29 := by omega
  subst i
  exact disposition_at_29

theorem disposition_interval_30 : Interval dispositionTest 30 31 := by
  intro i hlo hhi
  have h : i = 30 := by omega
  subst i
  exact disposition_at_30

theorem disposition_interval_31 : Interval dispositionTest 31 32 := by
  intro i hlo hhi
  have h : i = 31 := by omega
  subst i
  exact disposition_at_31

theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 16 32 (interval_append dispositionTest 0 8 16 (interval_append dispositionTest 0 4 8 (interval_append dispositionTest 0 2 4 (interval_append dispositionTest 0 1 2 disposition_interval_0 disposition_interval_1) (interval_append dispositionTest 2 3 4 disposition_interval_2 disposition_interval_3)) (interval_append dispositionTest 4 6 8 (interval_append dispositionTest 4 5 6 disposition_interval_4 disposition_interval_5) (interval_append dispositionTest 6 7 8 disposition_interval_6 disposition_interval_7))) (interval_append dispositionTest 8 12 16 (interval_append dispositionTest 8 10 12 (interval_append dispositionTest 8 9 10 disposition_interval_8 disposition_interval_9) (interval_append dispositionTest 10 11 12 disposition_interval_10 disposition_interval_11)) (interval_append dispositionTest 12 14 16 (interval_append dispositionTest 12 13 14 disposition_interval_12 disposition_interval_13) (interval_append dispositionTest 14 15 16 disposition_interval_14 disposition_interval_15)))) (interval_append dispositionTest 16 24 32 (interval_append dispositionTest 16 20 24 (interval_append dispositionTest 16 18 20 (interval_append dispositionTest 16 17 18 disposition_interval_16 disposition_interval_17) (interval_append dispositionTest 18 19 20 disposition_interval_18 disposition_interval_19)) (interval_append dispositionTest 20 22 24 (interval_append dispositionTest 20 21 22 disposition_interval_20 disposition_interval_21) (interval_append dispositionTest 22 23 24 disposition_interval_22 disposition_interval_23))) (interval_append dispositionTest 24 28 32 (interval_append dispositionTest 24 26 28 (interval_append dispositionTest 24 25 26 disposition_interval_24 disposition_interval_25) (interval_append dispositionTest 26 27 28 disposition_interval_26 disposition_interval_27)) (interval_append dispositionTest 28 30 32 (interval_append dispositionTest 28 29 30 disposition_interval_28 disposition_interval_29) (interval_append dispositionTest 30 31 32 disposition_interval_30 disposition_interval_31)))))
theorem disposition_checked (j : Fin leafCount) :
    RawLeafCertificate.check quota ((rawLeaves j.val).map RootedSmallCache.rawCells)
      (disposition j) = true :=
  dispositionTest_complete j.val (Nat.zero_le _) j.isLt

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest10
