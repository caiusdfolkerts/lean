module
prelude
public import RootedSubsumedForest0862Data
public import RawLeafCertificate

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0862
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf (RawLeafCertificate.Certificate.quota 3))
 (.branch 2
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.leaf (RawLeafCertificate.Certificate.quota 2))))
 (.branch 5
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 1))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))
 (.leaf (RawLeafCertificate.Certificate.quota 1)))
 (.branch 13
 (.branch 12
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 1)))
 (.leaf (RawLeafCertificate.Certificate.quota 1)))))
 (.branch 23
 (.branch 19
 (.branch 17
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 1)))
 (.branch 21
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 22
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))))
 (.branch 27
 (.branch 25
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.branch 26
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 1))))
 (.branch 29
 (.branch 28
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))
 (.leaf (RawLeafCertificate.Certificate.quota 1))))))
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

theorem dispositionTest_block_17 : Interval dispositionTest 17 18 :=
  interval_of_check dispositionTest 17 1 (by decide +kernel)

theorem dispositionTest_block_18 : Interval dispositionTest 18 19 :=
  interval_of_check dispositionTest 18 1 (by decide +kernel)

theorem dispositionTest_block_19 : Interval dispositionTest 19 20 :=
  interval_of_check dispositionTest 19 1 (by decide +kernel)

theorem dispositionTest_block_20 : Interval dispositionTest 20 21 :=
  interval_of_check dispositionTest 20 1 (by decide +kernel)

theorem dispositionTest_block_21 : Interval dispositionTest 21 22 :=
  interval_of_check dispositionTest 21 1 (by decide +kernel)

theorem dispositionTest_block_22 : Interval dispositionTest 22 23 :=
  interval_of_check dispositionTest 22 1 (by decide +kernel)

theorem dispositionTest_block_23 : Interval dispositionTest 23 24 :=
  interval_of_check dispositionTest 23 1 (by decide +kernel)

theorem dispositionTest_block_24 : Interval dispositionTest 24 25 :=
  interval_of_check dispositionTest 24 1 (by decide +kernel)

theorem dispositionTest_block_25 : Interval dispositionTest 25 26 :=
  interval_of_check dispositionTest 25 1 (by decide +kernel)

theorem dispositionTest_block_26 : Interval dispositionTest 26 27 :=
  interval_of_check dispositionTest 26 1 (by decide +kernel)

theorem dispositionTest_block_27 : Interval dispositionTest 27 28 :=
  interval_of_check dispositionTest 27 1 (by decide +kernel)

theorem dispositionTest_block_28 : Interval dispositionTest 28 29 :=
  interval_of_check dispositionTest 28 1 (by decide +kernel)

theorem dispositionTest_block_29 : Interval dispositionTest 29 30 :=
  interval_of_check dispositionTest 29 1 (by decide +kernel)

theorem dispositionTest_block_30 : Interval dispositionTest 30 31 :=
  interval_of_check dispositionTest 30 1 (by decide +kernel)

theorem dispositionTest_complete : Interval dispositionTest 0 31 :=
  (interval_append dispositionTest 0 15 31
  (interval_append dispositionTest 0 7 15
  (interval_append dispositionTest 0 3 7
  (interval_append dispositionTest 0 1 3
  dispositionTest_block_0
  (interval_append dispositionTest 1 2 3
  dispositionTest_block_1
  dispositionTest_block_2))
  (interval_append dispositionTest 3 5 7
  (interval_append dispositionTest 3 4 5
  dispositionTest_block_3
  dispositionTest_block_4)
  (interval_append dispositionTest 5 6 7
  dispositionTest_block_5
  dispositionTest_block_6)))
  (interval_append dispositionTest 7 11 15
  (interval_append dispositionTest 7 9 11
  (interval_append dispositionTest 7 8 9
  dispositionTest_block_7
  dispositionTest_block_8)
  (interval_append dispositionTest 9 10 11
  dispositionTest_block_9
  dispositionTest_block_10))
  (interval_append dispositionTest 11 13 15
  (interval_append dispositionTest 11 12 13
  dispositionTest_block_11
  dispositionTest_block_12)
  (interval_append dispositionTest 13 14 15
  dispositionTest_block_13
  dispositionTest_block_14))))
  (interval_append dispositionTest 15 23 31
  (interval_append dispositionTest 15 19 23
  (interval_append dispositionTest 15 17 19
  (interval_append dispositionTest 15 16 17
  dispositionTest_block_15
  dispositionTest_block_16)
  (interval_append dispositionTest 17 18 19
  dispositionTest_block_17
  dispositionTest_block_18))
  (interval_append dispositionTest 19 21 23
  (interval_append dispositionTest 19 20 21
  dispositionTest_block_19
  dispositionTest_block_20)
  (interval_append dispositionTest 21 22 23
  dispositionTest_block_21
  dispositionTest_block_22)))
  (interval_append dispositionTest 23 27 31
  (interval_append dispositionTest 23 25 27
  (interval_append dispositionTest 23 24 25
  dispositionTest_block_23
  dispositionTest_block_24)
  (interval_append dispositionTest 25 26 27
  dispositionTest_block_25
  dispositionTest_block_26))
  (interval_append dispositionTest 27 29 31
  (interval_append dispositionTest 27 28 29
  dispositionTest_block_27
  dispositionTest_block_28)
  (interval_append dispositionTest 29 30 31
  dispositionTest_block_29
  dispositionTest_block_30)))))
theorem disposition_checked (j : Fin leafCount) :
    RawLeafCertificate.check quota ((rawLeaves j.val).map Papers.RationalityTen.RootedCaches.RootedSixExtra05.rawCells)
      (disposition j) = true :=
  dispositionTest_complete j.val (Nat.zero_le _) j.isLt

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0862
