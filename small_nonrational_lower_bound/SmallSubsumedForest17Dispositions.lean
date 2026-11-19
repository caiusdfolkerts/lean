module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest17Data
public import RawLeafCertificate

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest17
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 43
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 65
 (.branch 54
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 59
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 62
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 63
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 64
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 1)))))))
 (.branch 76
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 81
 (.branch 78
 (.branch 77
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 1)))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))
 (.branch 84
 (.branch 82
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 83
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 1))))
 (.branch 85
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 86
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 1)))))))))
cert_disposition_4
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map RootedSmallCache.rawCells) (dispositionTable.get i)
cert_dispositionTest_block_3 0 1
cert_dispositionTest_block_3 1 2
cert_dispositionTest_block_3 2 3
cert_dispositionTest_block_3 3 4
cert_dispositionTest_block_3 4 5
cert_dispositionTest_block_3 5 6
cert_dispositionTest_block_3 6 7
cert_dispositionTest_block_3 7 8
cert_dispositionTest_block_3 8 9
cert_dispositionTest_block_3 9 10
cert_dispositionTest_block_3 10 11
cert_dispositionTest_block_3 11 12
cert_dispositionTest_block_3 12 13
cert_dispositionTest_block_3 13 14
cert_dispositionTest_block_3 14 15
cert_dispositionTest_block_3 15 16
cert_dispositionTest_block_3 16 17
cert_dispositionTest_block_3 17 18
cert_dispositionTest_block_3 18 19
cert_dispositionTest_block_3 19 20
cert_dispositionTest_block_3 20 21
cert_dispositionTest_block_3 21 22
cert_dispositionTest_block_3 22 23
cert_dispositionTest_block_3 23 24
cert_dispositionTest_block_3 24 25
cert_dispositionTest_block_3 25 26
cert_dispositionTest_block_3 26 27
cert_dispositionTest_block_3 27 28
cert_dispositionTest_block_3 28 29
cert_dispositionTest_block_3 29 30
cert_dispositionTest_block_3 30 31
cert_dispositionTest_block_3 31 32
cert_dispositionTest_block_3 32 33
cert_dispositionTest_block_3 33 34
cert_dispositionTest_block_3 34 35
cert_dispositionTest_block_3 35 36
cert_dispositionTest_block_3 36 37
cert_dispositionTest_block_3 37 38
cert_dispositionTest_block_3 38 39
cert_dispositionTest_block_3 39 40
cert_dispositionTest_block_3 40 41
cert_dispositionTest_block_3 41 42
cert_dispositionTest_block_3 42 43
cert_dispositionTest_block_3 43 44
cert_dispositionTest_block_3 44 45
cert_dispositionTest_block_3 45 46
cert_dispositionTest_block_3 46 47
cert_dispositionTest_block_3 47 48
cert_dispositionTest_block_3 48 49
cert_dispositionTest_block_3 49 50
cert_dispositionTest_block_3 50 51
cert_dispositionTest_block_3 51 52
cert_dispositionTest_block_3 52 53
cert_dispositionTest_block_3 53 54
cert_dispositionTest_block_3 54 55
cert_dispositionTest_block_3 55 56
cert_dispositionTest_block_3 56 57
cert_dispositionTest_block_3 57 58
cert_dispositionTest_block_3 58 59
cert_dispositionTest_block_3 59 60
cert_dispositionTest_block_3 60 61
cert_dispositionTest_block_3 61 62
cert_dispositionTest_block_3 62 63
cert_dispositionTest_block_3 63 64
cert_dispositionTest_block_3 64 65
cert_dispositionTest_block_3 65 66
cert_dispositionTest_block_3 66 67
cert_dispositionTest_block_3 67 68
cert_dispositionTest_block_3 68 69
cert_dispositionTest_block_3 69 70
cert_dispositionTest_block_3 70 71
cert_dispositionTest_block_3 71 72
cert_dispositionTest_block_3 72 73
cert_dispositionTest_block_3 73 74
cert_dispositionTest_block_3 74 75
cert_dispositionTest_block_3 75 76
cert_dispositionTest_block_3 76 77
cert_dispositionTest_block_3 77 78
cert_dispositionTest_block_3 78 79
cert_dispositionTest_block_3 79 80
cert_dispositionTest_block_3 80 81
cert_dispositionTest_block_3 81 82
cert_dispositionTest_block_3 82 83
cert_dispositionTest_block_3 83 84
cert_dispositionTest_block_3 84 85
cert_dispositionTest_block_3 85 86
cert_dispositionTest_block_3 86 87
theorem dispositionTest_complete : Interval dispositionTest 0 87 :=
  (interval_append dispositionTest 0 43 87
  (interval_append dispositionTest 0 21 43
  (interval_append dispositionTest 0 10 21
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
  (interval_append dispositionTest 10 15 21
  (interval_append dispositionTest 10 12 15
  (interval_append dispositionTest 10 11 12
  dispositionTest_block_10
  dispositionTest_block_11)
  (interval_append dispositionTest 12 13 15
  dispositionTest_block_12
  (interval_append dispositionTest 13 14 15
  dispositionTest_block_13
  dispositionTest_block_14)))
  (interval_append dispositionTest 15 18 21
  (interval_append dispositionTest 15 16 18
  dispositionTest_block_15
  (interval_append dispositionTest 16 17 18
  dispositionTest_block_16
  dispositionTest_block_17))
  (interval_append dispositionTest 18 19 21
  dispositionTest_block_18
  (interval_append dispositionTest 19 20 21
  dispositionTest_block_19
  dispositionTest_block_20)))))
  (interval_append dispositionTest 21 32 43
  (interval_append dispositionTest 21 26 32
  (interval_append dispositionTest 21 23 26
  (interval_append dispositionTest 21 22 23
  dispositionTest_block_21
  dispositionTest_block_22)
  (interval_append dispositionTest 23 24 26
  dispositionTest_block_23
  (interval_append dispositionTest 24 25 26
  dispositionTest_block_24
  dispositionTest_block_25)))
  (interval_append dispositionTest 26 29 32
  (interval_append dispositionTest 26 27 29
  dispositionTest_block_26
  (interval_append dispositionTest 27 28 29
  dispositionTest_block_27
  dispositionTest_block_28))
  (interval_append dispositionTest 29 30 32
  dispositionTest_block_29
  (interval_append dispositionTest 30 31 32
  dispositionTest_block_30
  dispositionTest_block_31))))
  (interval_append dispositionTest 32 37 43
  (interval_append dispositionTest 32 34 37
  (interval_append dispositionTest 32 33 34
  dispositionTest_block_32
  dispositionTest_block_33)
  (interval_append dispositionTest 34 35 37
  dispositionTest_block_34
  (interval_append dispositionTest 35 36 37
  dispositionTest_block_35
  dispositionTest_block_36)))
  (interval_append dispositionTest 37 40 43
  (interval_append dispositionTest 37 38 40
  dispositionTest_block_37
  (interval_append dispositionTest 38 39 40
  dispositionTest_block_38
  dispositionTest_block_39))
  (interval_append dispositionTest 40 41 43
  dispositionTest_block_40
  (interval_append dispositionTest 41 42 43
  dispositionTest_block_41
  dispositionTest_block_42))))))
  (interval_append dispositionTest 43 65 87
  (interval_append dispositionTest 43 54 65
  (interval_append dispositionTest 43 48 54
  (interval_append dispositionTest 43 45 48
  (interval_append dispositionTest 43 44 45
  dispositionTest_block_43
  dispositionTest_block_44)
  (interval_append dispositionTest 45 46 48
  dispositionTest_block_45
  (interval_append dispositionTest 46 47 48
  dispositionTest_block_46
  dispositionTest_block_47)))
  (interval_append dispositionTest 48 51 54
  (interval_append dispositionTest 48 49 51
  dispositionTest_block_48
  (interval_append dispositionTest 49 50 51
  dispositionTest_block_49
  dispositionTest_block_50))
  (interval_append dispositionTest 51 52 54
  dispositionTest_block_51
  (interval_append dispositionTest 52 53 54
  dispositionTest_block_52
  dispositionTest_block_53))))
  (interval_append dispositionTest 54 59 65
  (interval_append dispositionTest 54 56 59
  (interval_append dispositionTest 54 55 56
  dispositionTest_block_54
  dispositionTest_block_55)
  (interval_append dispositionTest 56 57 59
  dispositionTest_block_56
  (interval_append dispositionTest 57 58 59
  dispositionTest_block_57
  dispositionTest_block_58)))
  (interval_append dispositionTest 59 62 65
  (interval_append dispositionTest 59 60 62
  dispositionTest_block_59
  (interval_append dispositionTest 60 61 62
  dispositionTest_block_60
  dispositionTest_block_61))
  (interval_append dispositionTest 62 63 65
  dispositionTest_block_62
  (interval_append dispositionTest 63 64 65
  dispositionTest_block_63
  dispositionTest_block_64)))))
  (interval_append dispositionTest 65 76 87
  (interval_append dispositionTest 65 70 76
  (interval_append dispositionTest 65 67 70
  (interval_append dispositionTest 65 66 67
  dispositionTest_block_65
  dispositionTest_block_66)
  (interval_append dispositionTest 67 68 70
  dispositionTest_block_67
  (interval_append dispositionTest 68 69 70
  dispositionTest_block_68
  dispositionTest_block_69)))
  (interval_append dispositionTest 70 73 76
  (interval_append dispositionTest 70 71 73
  dispositionTest_block_70
  (interval_append dispositionTest 71 72 73
  dispositionTest_block_71
  dispositionTest_block_72))
  (interval_append dispositionTest 73 74 76
  dispositionTest_block_73
  (interval_append dispositionTest 74 75 76
  dispositionTest_block_74
  dispositionTest_block_75))))
  (interval_append dispositionTest 76 81 87
  (interval_append dispositionTest 76 78 81
  (interval_append dispositionTest 76 77 78
  dispositionTest_block_76
  dispositionTest_block_77)
  (interval_append dispositionTest 78 79 81
  dispositionTest_block_78
  (interval_append dispositionTest 79 80 81
  dispositionTest_block_79
  dispositionTest_block_80)))
  (interval_append dispositionTest 81 84 87
  (interval_append dispositionTest 81 82 84
  dispositionTest_block_81
  (interval_append dispositionTest 82 83 84
  dispositionTest_block_82
  dispositionTest_block_83))
  (interval_append dispositionTest 84 85 87
  dispositionTest_block_84
  (interval_append dispositionTest 85 86 87
  dispositionTest_block_85
  dispositionTest_block_86)))))))
cert_disposition_checked_6
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest17
