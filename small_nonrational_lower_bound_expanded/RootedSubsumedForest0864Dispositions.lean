module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
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
cert_dispositionTest_block_2 31 32
cert_dispositionTest_block_2 32 33
cert_dispositionTest_block_2 33 34
cert_dispositionTest_block_2 34 35
cert_dispositionTest_block_2 35 36
cert_dispositionTest_block_2 36 37
cert_dispositionTest_block_2 37 38
cert_dispositionTest_block_2 38 39
cert_dispositionTest_block_2 39 40
cert_dispositionTest_block_2 40 41
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
cert_disposition_checked_4 05
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0864
