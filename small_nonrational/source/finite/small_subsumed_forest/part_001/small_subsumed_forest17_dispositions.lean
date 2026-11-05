module
prelude
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
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map RootedSmallCache.rawCells) (dispositionTable.get i)
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

theorem dispositionTest_block_41 : Interval dispositionTest 41 42 :=
  interval_of_check dispositionTest 41 1 (by decide +kernel)

theorem dispositionTest_block_42 : Interval dispositionTest 42 43 :=
  interval_of_check dispositionTest 42 1 (by decide +kernel)

theorem dispositionTest_block_43 : Interval dispositionTest 43 44 :=
  interval_of_check dispositionTest 43 1 (by decide +kernel)

theorem dispositionTest_block_44 : Interval dispositionTest 44 45 :=
  interval_of_check dispositionTest 44 1 (by decide +kernel)

theorem dispositionTest_block_45 : Interval dispositionTest 45 46 :=
  interval_of_check dispositionTest 45 1 (by decide +kernel)

theorem dispositionTest_block_46 : Interval dispositionTest 46 47 :=
  interval_of_check dispositionTest 46 1 (by decide +kernel)

theorem dispositionTest_block_47 : Interval dispositionTest 47 48 :=
  interval_of_check dispositionTest 47 1 (by decide +kernel)

theorem dispositionTest_block_48 : Interval dispositionTest 48 49 :=
  interval_of_check dispositionTest 48 1 (by decide +kernel)

theorem dispositionTest_block_49 : Interval dispositionTest 49 50 :=
  interval_of_check dispositionTest 49 1 (by decide +kernel)

theorem dispositionTest_block_50 : Interval dispositionTest 50 51 :=
  interval_of_check dispositionTest 50 1 (by decide +kernel)

theorem dispositionTest_block_51 : Interval dispositionTest 51 52 :=
  interval_of_check dispositionTest 51 1 (by decide +kernel)

theorem dispositionTest_block_52 : Interval dispositionTest 52 53 :=
  interval_of_check dispositionTest 52 1 (by decide +kernel)

theorem dispositionTest_block_53 : Interval dispositionTest 53 54 :=
  interval_of_check dispositionTest 53 1 (by decide +kernel)

theorem dispositionTest_block_54 : Interval dispositionTest 54 55 :=
  interval_of_check dispositionTest 54 1 (by decide +kernel)

theorem dispositionTest_block_55 : Interval dispositionTest 55 56 :=
  interval_of_check dispositionTest 55 1 (by decide +kernel)

theorem dispositionTest_block_56 : Interval dispositionTest 56 57 :=
  interval_of_check dispositionTest 56 1 (by decide +kernel)

theorem dispositionTest_block_57 : Interval dispositionTest 57 58 :=
  interval_of_check dispositionTest 57 1 (by decide +kernel)

theorem dispositionTest_block_58 : Interval dispositionTest 58 59 :=
  interval_of_check dispositionTest 58 1 (by decide +kernel)

theorem dispositionTest_block_59 : Interval dispositionTest 59 60 :=
  interval_of_check dispositionTest 59 1 (by decide +kernel)

theorem dispositionTest_block_60 : Interval dispositionTest 60 61 :=
  interval_of_check dispositionTest 60 1 (by decide +kernel)

theorem dispositionTest_block_61 : Interval dispositionTest 61 62 :=
  interval_of_check dispositionTest 61 1 (by decide +kernel)

theorem dispositionTest_block_62 : Interval dispositionTest 62 63 :=
  interval_of_check dispositionTest 62 1 (by decide +kernel)

theorem dispositionTest_block_63 : Interval dispositionTest 63 64 :=
  interval_of_check dispositionTest 63 1 (by decide +kernel)

theorem dispositionTest_block_64 : Interval dispositionTest 64 65 :=
  interval_of_check dispositionTest 64 1 (by decide +kernel)

theorem dispositionTest_block_65 : Interval dispositionTest 65 66 :=
  interval_of_check dispositionTest 65 1 (by decide +kernel)

theorem dispositionTest_block_66 : Interval dispositionTest 66 67 :=
  interval_of_check dispositionTest 66 1 (by decide +kernel)

theorem dispositionTest_block_67 : Interval dispositionTest 67 68 :=
  interval_of_check dispositionTest 67 1 (by decide +kernel)

theorem dispositionTest_block_68 : Interval dispositionTest 68 69 :=
  interval_of_check dispositionTest 68 1 (by decide +kernel)

theorem dispositionTest_block_69 : Interval dispositionTest 69 70 :=
  interval_of_check dispositionTest 69 1 (by decide +kernel)

theorem dispositionTest_block_70 : Interval dispositionTest 70 71 :=
  interval_of_check dispositionTest 70 1 (by decide +kernel)

theorem dispositionTest_block_71 : Interval dispositionTest 71 72 :=
  interval_of_check dispositionTest 71 1 (by decide +kernel)

theorem dispositionTest_block_72 : Interval dispositionTest 72 73 :=
  interval_of_check dispositionTest 72 1 (by decide +kernel)

theorem dispositionTest_block_73 : Interval dispositionTest 73 74 :=
  interval_of_check dispositionTest 73 1 (by decide +kernel)

theorem dispositionTest_block_74 : Interval dispositionTest 74 75 :=
  interval_of_check dispositionTest 74 1 (by decide +kernel)

theorem dispositionTest_block_75 : Interval dispositionTest 75 76 :=
  interval_of_check dispositionTest 75 1 (by decide +kernel)

theorem dispositionTest_block_76 : Interval dispositionTest 76 77 :=
  interval_of_check dispositionTest 76 1 (by decide +kernel)

theorem dispositionTest_block_77 : Interval dispositionTest 77 78 :=
  interval_of_check dispositionTest 77 1 (by decide +kernel)

theorem dispositionTest_block_78 : Interval dispositionTest 78 79 :=
  interval_of_check dispositionTest 78 1 (by decide +kernel)

theorem dispositionTest_block_79 : Interval dispositionTest 79 80 :=
  interval_of_check dispositionTest 79 1 (by decide +kernel)

theorem dispositionTest_block_80 : Interval dispositionTest 80 81 :=
  interval_of_check dispositionTest 80 1 (by decide +kernel)

theorem dispositionTest_block_81 : Interval dispositionTest 81 82 :=
  interval_of_check dispositionTest 81 1 (by decide +kernel)

theorem dispositionTest_block_82 : Interval dispositionTest 82 83 :=
  interval_of_check dispositionTest 82 1 (by decide +kernel)

theorem dispositionTest_block_83 : Interval dispositionTest 83 84 :=
  interval_of_check dispositionTest 83 1 (by decide +kernel)

theorem dispositionTest_block_84 : Interval dispositionTest 84 85 :=
  interval_of_check dispositionTest 84 1 (by decide +kernel)

theorem dispositionTest_block_85 : Interval dispositionTest 85 86 :=
  interval_of_check dispositionTest 85 1 (by decide +kernel)

theorem dispositionTest_block_86 : Interval dispositionTest 86 87 :=
  interval_of_check dispositionTest 86 1 (by decide +kernel)

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
theorem disposition_checked (j : Fin leafCount) :
    RawLeafCertificate.check quota ((rawLeaves j.val).map RootedSmallCache.rawCells)
      (disposition j) = true :=
  dispositionTest_complete j.val (Nat.zero_le _) j.isLt

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest17
