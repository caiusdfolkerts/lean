module
prelude
public import RootedSubsumedForest0851Data
public import RawLeafCertificate

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0851
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf (RawLeafCertificate.Certificate.quota 3))
 (.branch 2
 (.leaf (RawLeafCertificate.Certificate.quota 9))
 (.leaf (RawLeafCertificate.Certificate.quota 1))))
 (.branch 4
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.leaf (RawLeafCertificate.Certificate.quota 2))))
 (.branch 9
 (.branch 7
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.branch 8
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.leaf (RawLeafCertificate.Certificate.quota 2))))
 (.branch 11
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 1)))))
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

theorem dispositionTest_complete : Interval dispositionTest 0 13 :=
  (interval_append dispositionTest 0 6 13
  (interval_append dispositionTest 0 3 6
  (interval_append dispositionTest 0 1 3
  dispositionTest_block_0
  (interval_append dispositionTest 1 2 3
  dispositionTest_block_1
  dispositionTest_block_2))
  (interval_append dispositionTest 3 4 6
  dispositionTest_block_3
  (interval_append dispositionTest 4 5 6
  dispositionTest_block_4
  dispositionTest_block_5)))
  (interval_append dispositionTest 6 9 13
  (interval_append dispositionTest 6 7 9
  dispositionTest_block_6
  (interval_append dispositionTest 7 8 9
  dispositionTest_block_7
  dispositionTest_block_8))
  (interval_append dispositionTest 9 11 13
  (interval_append dispositionTest 9 10 11
  dispositionTest_block_9
  dispositionTest_block_10)
  (interval_append dispositionTest 11 12 13
  dispositionTest_block_11
  dispositionTest_block_12))))
theorem disposition_checked (j : Fin leafCount) :
    RawLeafCertificate.check quota ((rawLeaves j.val).map Papers.RationalityTen.RootedCaches.RootedSixExtra05.rawCells)
      (disposition j) = true :=
  dispositionTest_complete j.val (Nat.zero_le _) j.isLt

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0851
