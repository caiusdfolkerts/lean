module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
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
cert_disposition_3
cert_dispositionTest_4 05
cert_dispositionTest_block_2 0 1
cert_dispositionTest_block_2 1 2
cert_dispositionTest_block_2 2 3
cert_dispositionTest_block_2 3 4
cert_dispositionTest_block_2 4 5
cert_dispositionTest_block_2 5 6
cert_dispositionTest_block_2 6 7
cert_dispositionTest_block_2 7 8
cert_dispositionTest_block_2 8 9
cert_dispositionTest_block_2 9 10
cert_dispositionTest_block_2 10 11
cert_dispositionTest_block_2 11 12
cert_dispositionTest_block_2 12 13
cert_dispositionTest_block_2 13 14
cert_dispositionTest_block_2 14 15
cert_dispositionTest_block_2 15 16
cert_dispositionTest_block_2 16 17
cert_dispositionTest_block_2 17 18
cert_dispositionTest_block_2 18 19
cert_dispositionTest_block_2 19 20
cert_dispositionTest_block_2 20 21
cert_dispositionTest_block_2 21 22
cert_dispositionTest_block_2 22 23
cert_dispositionTest_block_2 23 24
cert_dispositionTest_block_2 24 25
cert_dispositionTest_block_2 25 26
cert_dispositionTest_block_2 26 27
cert_dispositionTest_block_2 27 28
cert_dispositionTest_block_2 28 29
cert_dispositionTest_block_2 29 30
cert_dispositionTest_block_2 30 31
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
cert_disposition_checked_4 05
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0862
