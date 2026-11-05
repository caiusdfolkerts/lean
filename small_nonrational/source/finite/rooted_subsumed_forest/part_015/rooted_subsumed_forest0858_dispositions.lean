module
prelude
public import RootedSubsumedForest0858Dispositions000
public import RootedSubsumedForest0858Dispositions001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0858
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 25 50 (interval_append dispositionTest 0 12 25 (interval_append dispositionTest 0 6 12 (interval_append dispositionTest 0 3 6 (interval_append dispositionTest 0 1 3 disposition_interval_0 (interval_append dispositionTest 1 2 3 disposition_interval_1 disposition_interval_2)) (interval_append dispositionTest 3 4 6 disposition_interval_3 (interval_append dispositionTest 4 5 6 disposition_interval_4 disposition_interval_5))) (interval_append dispositionTest 6 9 12 (interval_append dispositionTest 6 7 9 disposition_interval_6 (interval_append dispositionTest 7 8 9 disposition_interval_7 disposition_interval_8)) (interval_append dispositionTest 9 10 12 disposition_interval_9 (interval_append dispositionTest 10 11 12 disposition_interval_10 disposition_interval_11)))) (interval_append dispositionTest 12 18 25 (interval_append dispositionTest 12 15 18 (interval_append dispositionTest 12 13 15 disposition_interval_12 (interval_append dispositionTest 13 14 15 disposition_interval_13 disposition_interval_14)) (interval_append dispositionTest 15 16 18 disposition_interval_15 (interval_append dispositionTest 16 17 18 disposition_interval_16 disposition_interval_17))) (interval_append dispositionTest 18 21 25 (interval_append dispositionTest 18 19 21 disposition_interval_18 (interval_append dispositionTest 19 20 21 disposition_interval_19 disposition_interval_20)) (interval_append dispositionTest 21 23 25 (interval_append dispositionTest 21 22 23 disposition_interval_21 disposition_interval_22) (interval_append dispositionTest 23 24 25 disposition_interval_23 disposition_interval_24))))) (interval_append dispositionTest 25 37 50 (interval_append dispositionTest 25 31 37 (interval_append dispositionTest 25 28 31 (interval_append dispositionTest 25 26 28 disposition_interval_25 (interval_append dispositionTest 26 27 28 disposition_interval_26 disposition_interval_27)) (interval_append dispositionTest 28 29 31 disposition_interval_28 (interval_append dispositionTest 29 30 31 disposition_interval_29 disposition_interval_30))) (interval_append dispositionTest 31 34 37 (interval_append dispositionTest 31 32 34 disposition_interval_31 (interval_append dispositionTest 32 33 34 disposition_interval_32 disposition_interval_33)) (interval_append dispositionTest 34 35 37 disposition_interval_34 (interval_append dispositionTest 35 36 37 disposition_interval_35 disposition_interval_36)))) (interval_append dispositionTest 37 43 50 (interval_append dispositionTest 37 40 43 (interval_append dispositionTest 37 38 40 disposition_interval_37 (interval_append dispositionTest 38 39 40 disposition_interval_38 disposition_interval_39)) (interval_append dispositionTest 40 41 43 disposition_interval_40 (interval_append dispositionTest 41 42 43 disposition_interval_41 disposition_interval_42))) (interval_append dispositionTest 43 46 50 (interval_append dispositionTest 43 44 46 disposition_interval_43 (interval_append dispositionTest 44 45 46 disposition_interval_44 disposition_interval_45)) (interval_append dispositionTest 46 48 50 (interval_append dispositionTest 46 47 48 disposition_interval_46 disposition_interval_47) (interval_append dispositionTest 48 49 50 disposition_interval_48 disposition_interval_49))))))
theorem disposition_checked (j : Fin leafCount) :
    RawLeafCertificate.check quota ((rawLeaves j.val).map Papers.RationalityTen.RootedCaches.RootedSixExtra06.rawCells)
      (disposition j) = true :=
  dispositionTest_complete j.val (Nat.zero_le _) j.isLt

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0858
