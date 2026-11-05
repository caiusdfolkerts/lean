module
prelude
public import RootedSubsumedForest0741Dispositions000
public import RootedSubsumedForest0741Dispositions001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0741
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 23 47 (interval_append dispositionTest 0 11 23 (interval_append dispositionTest 0 5 11 (interval_append dispositionTest 0 2 5 (interval_append dispositionTest 0 1 2 disposition_interval_0 disposition_interval_1) (interval_append dispositionTest 2 3 5 disposition_interval_2 (interval_append dispositionTest 3 4 5 disposition_interval_3 disposition_interval_4))) (interval_append dispositionTest 5 8 11 (interval_append dispositionTest 5 6 8 disposition_interval_5 (interval_append dispositionTest 6 7 8 disposition_interval_6 disposition_interval_7)) (interval_append dispositionTest 8 9 11 disposition_interval_8 (interval_append dispositionTest 9 10 11 disposition_interval_9 disposition_interval_10)))) (interval_append dispositionTest 11 17 23 (interval_append dispositionTest 11 14 17 (interval_append dispositionTest 11 12 14 disposition_interval_11 (interval_append dispositionTest 12 13 14 disposition_interval_12 disposition_interval_13)) (interval_append dispositionTest 14 15 17 disposition_interval_14 (interval_append dispositionTest 15 16 17 disposition_interval_15 disposition_interval_16))) (interval_append dispositionTest 17 20 23 (interval_append dispositionTest 17 18 20 disposition_interval_17 (interval_append dispositionTest 18 19 20 disposition_interval_18 disposition_interval_19)) (interval_append dispositionTest 20 21 23 disposition_interval_20 (interval_append dispositionTest 21 22 23 disposition_interval_21 disposition_interval_22))))) (interval_append dispositionTest 23 35 47 (interval_append dispositionTest 23 29 35 (interval_append dispositionTest 23 26 29 (interval_append dispositionTest 23 24 26 disposition_interval_23 (interval_append dispositionTest 24 25 26 disposition_interval_24 disposition_interval_25)) (interval_append dispositionTest 26 27 29 disposition_interval_26 (interval_append dispositionTest 27 28 29 disposition_interval_27 disposition_interval_28))) (interval_append dispositionTest 29 32 35 (interval_append dispositionTest 29 30 32 disposition_interval_29 (interval_append dispositionTest 30 31 32 disposition_interval_30 disposition_interval_31)) (interval_append dispositionTest 32 33 35 disposition_interval_32 (interval_append dispositionTest 33 34 35 disposition_interval_33 disposition_interval_34)))) (interval_append dispositionTest 35 41 47 (interval_append dispositionTest 35 38 41 (interval_append dispositionTest 35 36 38 disposition_interval_35 (interval_append dispositionTest 36 37 38 disposition_interval_36 disposition_interval_37)) (interval_append dispositionTest 38 39 41 disposition_interval_38 (interval_append dispositionTest 39 40 41 disposition_interval_39 disposition_interval_40))) (interval_append dispositionTest 41 44 47 (interval_append dispositionTest 41 42 44 disposition_interval_41 (interval_append dispositionTest 42 43 44 disposition_interval_42 disposition_interval_43)) (interval_append dispositionTest 44 45 47 disposition_interval_44 (interval_append dispositionTest 45 46 47 disposition_interval_45 disposition_interval_46))))))
theorem disposition_checked (j : Fin leafCount) :
    RawLeafCertificate.check quota ((rawLeaves j.val).map Papers.RationalityTen.RootedCaches.RootedSixBase04.rawCells)
      (disposition j) = true :=
  dispositionTest_complete j.val (Nat.zero_le _) j.isLt

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0741
