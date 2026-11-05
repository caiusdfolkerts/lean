module
prelude
public import RootedSubsumedForest0707Data
public import RawLeafCertificate

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0707
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 9
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 13
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 15
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 16
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 17
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 1)))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase04.rawCells) (dispositionTable.get i)
theorem dispositionTest_block_0 : Interval dispositionTest 0 1 :=
  interval_of_check dispositionTest 0 1 (by decide +kernel)

theorem dispositionTest_block_1 : Interval dispositionTest 1 2 :=
  interval_of_check dispositionTest 1 1 (by decide +kernel)

theorem dispositionTest_block_2 : Interval dispositionTest 2 3 :=
  interval_of_check dispositionTest 2 1 (by decide +kernel)

theorem dispositionTest_block_3 : Interval dispositionTest 3 4 :=
  interval_of_check dispositionTest 3 1 (by decide +kernel)

theorem dispositionTest_block_4 : Interval dispositionTest 4 5 :=
  interval_of_check dispositionTest 4 1 (by decide +kernel)

theorem dispositionTest_block_5 : Interval dispositionTest 5 6 :=
  interval_of_check dispositionTest 5 1 (by decide +kernel)

theorem dispositionTest_block_6 : Interval dispositionTest 6 7 :=
  interval_of_check dispositionTest 6 1 (by decide +kernel)

theorem dispositionTest_block_7 : Interval dispositionTest 7 8 :=
  interval_of_check dispositionTest 7 1 (by decide +kernel)

theorem dispositionTest_block_8 : Interval dispositionTest 8 9 :=
  interval_of_check dispositionTest 8 1 (by decide +kernel)

theorem dispositionTest_block_9 : Interval dispositionTest 9 10 :=
  interval_of_check dispositionTest 9 1 (by decide +kernel)

theorem dispositionTest_block_10 : Interval dispositionTest 10 11 :=
  interval_of_check dispositionTest 10 1 (by decide +kernel)

theorem dispositionTest_block_11 : Interval dispositionTest 11 12 :=
  interval_of_check dispositionTest 11 1 (by decide +kernel)

theorem dispositionTest_block_12 : Interval dispositionTest 12 13 :=
  interval_of_check dispositionTest 12 1 (by decide +kernel)

theorem dispositionTest_block_13 : Interval dispositionTest 13 14 :=
  interval_of_check dispositionTest 13 1 (by decide +kernel)

theorem dispositionTest_block_14 : Interval dispositionTest 14 15 :=
  interval_of_check dispositionTest 14 1 (by decide +kernel)

theorem dispositionTest_block_15 : Interval dispositionTest 15 16 :=
  interval_of_check dispositionTest 15 1 (by decide +kernel)

theorem dispositionTest_block_16 : Interval dispositionTest 16 17 :=
  interval_of_check dispositionTest 16 1 (by decide +kernel)

theorem dispositionTest_block_17 : Interval dispositionTest 17 18 :=
  interval_of_check dispositionTest 17 1 (by decide +kernel)

theorem dispositionTest_complete : Interval dispositionTest 0 18 :=
  (interval_append dispositionTest 0 9 18
  (interval_append dispositionTest 0 4 9
  (interval_append dispositionTest 0 2 4
  (interval_append dispositionTest 0 1 2
  dispositionTest_block_0
  dispositionTest_block_1)
  (interval_append dispositionTest 2 3 4
  dispositionTest_block_2
  dispositionTest_block_3))
  (interval_append dispositionTest 4 6 9
  (interval_append dispositionTest 4 5 6
  dispositionTest_block_4
  dispositionTest_block_5)
  (interval_append dispositionTest 6 7 9
  dispositionTest_block_6
  (interval_append dispositionTest 7 8 9
  dispositionTest_block_7
  dispositionTest_block_8))))
  (interval_append dispositionTest 9 13 18
  (interval_append dispositionTest 9 11 13
  (interval_append dispositionTest 9 10 11
  dispositionTest_block_9
  dispositionTest_block_10)
  (interval_append dispositionTest 11 12 13
  dispositionTest_block_11
  dispositionTest_block_12))
  (interval_append dispositionTest 13 15 18
  (interval_append dispositionTest 13 14 15
  dispositionTest_block_13
  dispositionTest_block_14)
  (interval_append dispositionTest 15 16 18
  dispositionTest_block_15
  (interval_append dispositionTest 16 17 18
  dispositionTest_block_16
  dispositionTest_block_17)))))
theorem disposition_checked (j : Fin leafCount) :
    RawLeafCertificate.check quota ((rawLeaves j.val).map Papers.RationalityTen.RootedCaches.RootedSixBase04.rawCells)
      (disposition j) = true :=
  dispositionTest_complete j.val (Nat.zero_le _) j.isLt

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0707
