module
prelude
public import RootedSubsumedForest0311Dispositions000
public import RootedSubsumedForest0311Dispositions001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0311
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 21 42 (interval_append dispositionTest 0 10 21 (interval_append dispositionTest 0 5 10 (interval_append dispositionTest 0 2 5 (interval_append dispositionTest 0 1 2 disposition_interval_0 disposition_interval_1) (interval_append dispositionTest 2 3 5 disposition_interval_2 (interval_append dispositionTest 3 4 5 disposition_interval_3 disposition_interval_4))) (interval_append dispositionTest 5 7 10 (interval_append dispositionTest 5 6 7 disposition_interval_5 disposition_interval_6) (interval_append dispositionTest 7 8 10 disposition_interval_7 (interval_append dispositionTest 8 9 10 disposition_interval_8 disposition_interval_9)))) (interval_append dispositionTest 10 15 21 (interval_append dispositionTest 10 12 15 (interval_append dispositionTest 10 11 12 disposition_interval_10 disposition_interval_11) (interval_append dispositionTest 12 13 15 disposition_interval_12 (interval_append dispositionTest 13 14 15 disposition_interval_13 disposition_interval_14))) (interval_append dispositionTest 15 18 21 (interval_append dispositionTest 15 16 18 disposition_interval_15 (interval_append dispositionTest 16 17 18 disposition_interval_16 disposition_interval_17)) (interval_append dispositionTest 18 19 21 disposition_interval_18 (interval_append dispositionTest 19 20 21 disposition_interval_19 disposition_interval_20))))) (interval_append dispositionTest 21 31 42 (interval_append dispositionTest 21 26 31 (interval_append dispositionTest 21 23 26 (interval_append dispositionTest 21 22 23 disposition_interval_21 disposition_interval_22) (interval_append dispositionTest 23 24 26 disposition_interval_23 (interval_append dispositionTest 24 25 26 disposition_interval_24 disposition_interval_25))) (interval_append dispositionTest 26 28 31 (interval_append dispositionTest 26 27 28 disposition_interval_26 disposition_interval_27) (interval_append dispositionTest 28 29 31 disposition_interval_28 (interval_append dispositionTest 29 30 31 disposition_interval_29 disposition_interval_30)))) (interval_append dispositionTest 31 36 42 (interval_append dispositionTest 31 33 36 (interval_append dispositionTest 31 32 33 disposition_interval_31 disposition_interval_32) (interval_append dispositionTest 33 34 36 disposition_interval_33 (interval_append dispositionTest 34 35 36 disposition_interval_34 disposition_interval_35))) (interval_append dispositionTest 36 39 42 (interval_append dispositionTest 36 37 39 disposition_interval_36 (interval_append dispositionTest 37 38 39 disposition_interval_37 disposition_interval_38)) (interval_append dispositionTest 39 40 42 disposition_interval_39 (interval_append dispositionTest 40 41 42 disposition_interval_40 disposition_interval_41))))))
theorem disposition_checked (j : Fin leafCount) :
    RawLeafCertificate.check quota ((rawLeaves j.val).map Papers.RationalityTen.RootedCaches.RootedSixBase01.rawCells)
      (disposition j) = true :=
  dispositionTest_complete j.val (Nat.zero_le _) j.isLt

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0311
