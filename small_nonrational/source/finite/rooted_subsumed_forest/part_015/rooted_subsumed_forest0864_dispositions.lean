module
prelude
public import RootedSubsumedForest0864Data
public import RawLeafCertificate

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0864
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 20
 (.branch 10
 (.branch 5
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 7
 (.branch 6
 (.leaf (RawLeafCertificate.Certificate.quota 3))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))
 (.branch 8
 (.leaf (RawLeafCertificate.Certificate.quota 3))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))))
 (.branch 15
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 17
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 18
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 3))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf (RawLeafCertificate.Certificate.quota 3))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))
 (.branch 27
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 28
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 29
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.leaf (RawLeafCertificate.Certificate.quota 3))))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf (RawLeafCertificate.Certificate.quota 3))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))
 (.branch 38
 (.branch 36
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 37
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 1))))
 (.leaf (RawLeafCertificate.Certificate.quota 3))))))
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

theorem dispositionTest_block_31 : Interval dispositionTest 31 32 :=
  interval_of_check dispositionTest 31 1 (by decide +kernel)

theorem dispositionTest_block_32 : Interval dispositionTest 32 33 :=
  interval_of_check dispositionTest 32 1 (by decide +kernel)

theorem dispositionTest_block_33 : Interval dispositionTest 33 34 :=
  interval_of_check dispositionTest 33 1 (by decide +kernel)

theorem dispositionTest_block_34 : Interval dispositionTest 34 35 :=
  interval_of_check dispositionTest 34 1 (by decide +kernel)

theorem dispositionTest_block_35 : Interval dispositionTest 35 36 :=
  interval_of_check dispositionTest 35 1 (by decide +kernel)

theorem dispositionTest_block_36 : Interval dispositionTest 36 37 :=
  interval_of_check dispositionTest 36 1 (by decide +kernel)

theorem dispositionTest_block_37 : Interval dispositionTest 37 38 :=
  interval_of_check dispositionTest 37 1 (by decide +kernel)

theorem dispositionTest_block_38 : Interval dispositionTest 38 39 :=
  interval_of_check dispositionTest 38 1 (by decide +kernel)

theorem dispositionTest_block_39 : Interval dispositionTest 39 40 :=
  interval_of_check dispositionTest 39 1 (by decide +kernel)

theorem dispositionTest_block_40 : Interval dispositionTest 40 41 :=
  interval_of_check dispositionTest 40 1 (by decide +kernel)

theorem dispositionTest_complete : Interval dispositionTest 0 41 :=
  (interval_append dispositionTest 0 20 41
  (interval_append dispositionTest 0 10 20
  (interval_append dispositionTest 0 5 10
  (interval_append dispositionTest 0 2 5
  (interval_append dispositionTest 0 1 2
  dispositionTest_block_0
  dispositionTest_block_1)
  (interval_append dispositionTest 2 3 5
  dispositionTest_block_2
  (interval_append dispositionTest 3 4 5
  dispositionTest_block_3
  dispositionTest_block_4)))
  (interval_append dispositionTest 5 7 10
  (interval_append dispositionTest 5 6 7
  dispositionTest_block_5
  dispositionTest_block_6)
  (interval_append dispositionTest 7 8 10
  dispositionTest_block_7
  (interval_append dispositionTest 8 9 10
  dispositionTest_block_8
  dispositionTest_block_9))))
  (interval_append dispositionTest 10 15 20
  (interval_append dispositionTest 10 12 15
  (interval_append dispositionTest 10 11 12
  dispositionTest_block_10
  dispositionTest_block_11)
  (interval_append dispositionTest 12 13 15
  dispositionTest_block_12
  (interval_append dispositionTest 13 14 15
  dispositionTest_block_13
  dispositionTest_block_14)))
  (interval_append dispositionTest 15 17 20
  (interval_append dispositionTest 15 16 17
  dispositionTest_block_15
  dispositionTest_block_16)
  (interval_append dispositionTest 17 18 20
  dispositionTest_block_17
  (interval_append dispositionTest 18 19 20
  dispositionTest_block_18
  dispositionTest_block_19)))))
  (interval_append dispositionTest 20 30 41
  (interval_append dispositionTest 20 25 30
  (interval_append dispositionTest 20 22 25
  (interval_append dispositionTest 20 21 22
  dispositionTest_block_20
  dispositionTest_block_21)
  (interval_append dispositionTest 22 23 25
  dispositionTest_block_22
  (interval_append dispositionTest 23 24 25
  dispositionTest_block_23
  dispositionTest_block_24)))
  (interval_append dispositionTest 25 27 30
  (interval_append dispositionTest 25 26 27
  dispositionTest_block_25
  dispositionTest_block_26)
  (interval_append dispositionTest 27 28 30
  dispositionTest_block_27
  (interval_append dispositionTest 28 29 30
  dispositionTest_block_28
  dispositionTest_block_29))))
  (interval_append dispositionTest 30 35 41
  (interval_append dispositionTest 30 32 35
  (interval_append dispositionTest 30 31 32
  dispositionTest_block_30
  dispositionTest_block_31)
  (interval_append dispositionTest 32 33 35
  dispositionTest_block_32
  (interval_append dispositionTest 33 34 35
  dispositionTest_block_33
  dispositionTest_block_34)))
  (interval_append dispositionTest 35 38 41
  (interval_append dispositionTest 35 36 38
  dispositionTest_block_35
  (interval_append dispositionTest 36 37 38
  dispositionTest_block_36
  dispositionTest_block_37))
  (interval_append dispositionTest 38 39 41
  dispositionTest_block_38
  (interval_append dispositionTest 39 40 41
  dispositionTest_block_39
  dispositionTest_block_40))))))
theorem disposition_checked (j : Fin leafCount) :
    RawLeafCertificate.check quota ((rawLeaves j.val).map Papers.RationalityTen.RootedCaches.RootedSixExtra05.rawCells)
      (disposition j) = true :=
  dispositionTest_complete j.val (Nat.zero_le _) j.isLt

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0864
