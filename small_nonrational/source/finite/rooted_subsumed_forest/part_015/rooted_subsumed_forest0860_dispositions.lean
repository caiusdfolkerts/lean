module
prelude
public import RootedSubsumedForest0860Data
public import RawLeafCertificate

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0860
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 1)))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))
 (.branch 12
 (.branch 10
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 11
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 3))))
 (.branch 14
 (.branch 13
 (.leaf (RawLeafCertificate.Certificate.quota 3))
 (.leaf (RawLeafCertificate.Certificate.quota 1)))
 (.branch 15
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.leaf (RawLeafCertificate.Certificate.quota 2))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixExtra05.rawCells) (dispositionTable.get i)
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

theorem dispositionTest_complete : Interval dispositionTest 0 17 :=
  (interval_append dispositionTest 0 8 17
  (interval_append dispositionTest 0 4 8
  (interval_append dispositionTest 0 2 4
  (interval_append dispositionTest 0 1 2
  dispositionTest_block_0
  dispositionTest_block_1)
  (interval_append dispositionTest 2 3 4
  dispositionTest_block_2
  dispositionTest_block_3))
  (interval_append dispositionTest 4 6 8
  (interval_append dispositionTest 4 5 6
  dispositionTest_block_4
  dispositionTest_block_5)
  (interval_append dispositionTest 6 7 8
  dispositionTest_block_6
  dispositionTest_block_7)))
  (interval_append dispositionTest 8 12 17
  (interval_append dispositionTest 8 10 12
  (interval_append dispositionTest 8 9 10
  dispositionTest_block_8
  dispositionTest_block_9)
  (interval_append dispositionTest 10 11 12
  dispositionTest_block_10
  dispositionTest_block_11))
  (interval_append dispositionTest 12 14 17
  (interval_append dispositionTest 12 13 14
  dispositionTest_block_12
  dispositionTest_block_13)
  (interval_append dispositionTest 14 15 17
  dispositionTest_block_14
  (interval_append dispositionTest 15 16 17
  dispositionTest_block_15
  dispositionTest_block_16)))))
theorem disposition_checked (j : Fin leafCount) :
    RawLeafCertificate.check quota ((rawLeaves j.val).map Papers.RationalityTen.RootedCaches.RootedSixExtra05.rawCells)
      (disposition j) = true :=
  dispositionTest_complete j.val (Nat.zero_le _) j.isLt

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0860
