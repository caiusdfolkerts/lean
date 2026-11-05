module
prelude
public import RootedSubsumedForest0857Dispositions000
public import RootedSubsumedForest0857Dispositions001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0857
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 26 52 (interval_append dispositionTest 0 13 26 (interval_append dispositionTest 0 6 13 (interval_append dispositionTest 0 3 6 (interval_append dispositionTest 0 1 3 disposition_interval_0 (interval_append dispositionTest 1 2 3 disposition_interval_1 disposition_interval_2)) (interval_append dispositionTest 3 4 6 disposition_interval_3 (interval_append dispositionTest 4 5 6 disposition_interval_4 disposition_interval_5))) (interval_append dispositionTest 6 9 13 (interval_append dispositionTest 6 7 9 disposition_interval_6 (interval_append dispositionTest 7 8 9 disposition_interval_7 disposition_interval_8)) (interval_append dispositionTest 9 11 13 (interval_append dispositionTest 9 10 11 disposition_interval_9 disposition_interval_10) (interval_append dispositionTest 11 12 13 disposition_interval_11 disposition_interval_12)))) (interval_append dispositionTest 13 19 26 (interval_append dispositionTest 13 16 19 (interval_append dispositionTest 13 14 16 disposition_interval_13 (interval_append dispositionTest 14 15 16 disposition_interval_14 disposition_interval_15)) (interval_append dispositionTest 16 17 19 disposition_interval_16 (interval_append dispositionTest 17 18 19 disposition_interval_17 disposition_interval_18))) (interval_append dispositionTest 19 22 26 (interval_append dispositionTest 19 20 22 disposition_interval_19 (interval_append dispositionTest 20 21 22 disposition_interval_20 disposition_interval_21)) (interval_append dispositionTest 22 24 26 (interval_append dispositionTest 22 23 24 disposition_interval_22 disposition_interval_23) (interval_append dispositionTest 24 25 26 disposition_interval_24 disposition_interval_25))))) (interval_append dispositionTest 26 39 52 (interval_append dispositionTest 26 32 39 (interval_append dispositionTest 26 29 32 (interval_append dispositionTest 26 27 29 disposition_interval_26 (interval_append dispositionTest 27 28 29 disposition_interval_27 disposition_interval_28)) (interval_append dispositionTest 29 30 32 disposition_interval_29 (interval_append dispositionTest 30 31 32 disposition_interval_30 disposition_interval_31))) (interval_append dispositionTest 32 35 39 (interval_append dispositionTest 32 33 35 disposition_interval_32 (interval_append dispositionTest 33 34 35 disposition_interval_33 disposition_interval_34)) (interval_append dispositionTest 35 37 39 (interval_append dispositionTest 35 36 37 disposition_interval_35 disposition_interval_36) (interval_append dispositionTest 37 38 39 disposition_interval_37 disposition_interval_38)))) (interval_append dispositionTest 39 45 52 (interval_append dispositionTest 39 42 45 (interval_append dispositionTest 39 40 42 disposition_interval_39 (interval_append dispositionTest 40 41 42 disposition_interval_40 disposition_interval_41)) (interval_append dispositionTest 42 43 45 disposition_interval_42 (interval_append dispositionTest 43 44 45 disposition_interval_43 disposition_interval_44))) (interval_append dispositionTest 45 48 52 (interval_append dispositionTest 45 46 48 disposition_interval_45 (interval_append dispositionTest 46 47 48 disposition_interval_46 disposition_interval_47)) (interval_append dispositionTest 48 50 52 (interval_append dispositionTest 48 49 50 disposition_interval_48 disposition_interval_49) (interval_append dispositionTest 50 51 52 disposition_interval_50 disposition_interval_51))))))
theorem disposition_checked (j : Fin leafCount) :
    RawLeafCertificate.check quota ((rawLeaves j.val).map Papers.RationalityTen.RootedCaches.RootedSixExtra05.rawCells)
      (disposition j) = true :=
  dispositionTest_complete j.val (Nat.zero_le _) j.isLt

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0857
