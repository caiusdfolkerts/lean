module
prelude
public import RootedRawForest0066Data
public import RawLeafCertificate

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0066
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 81
 (.branch 40
 (.branch 20
 (.branch 10
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 15
 (.branch 12
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 13
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.leaf (RawLeafCertificate.Certificate.quota 2))))
 (.leaf (RawLeafCertificate.Certificate.quota 2))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))
 (.branch 27
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 28
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 29
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.leaf (RawLeafCertificate.Certificate.quota 2))))))
 (.branch 35
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 37
 (.branch 36
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 1)))
 (.leaf (RawLeafCertificate.Certificate.quota 2))))))
 (.branch 60
 (.branch 50
 (.branch 45
 (.branch 42
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 43
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 44
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 1)))))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))
 (.branch 55
 (.branch 52
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 53
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.leaf (RawLeafCertificate.Certificate.quota 2))))
 (.leaf (RawLeafCertificate.Certificate.quota 2))))
 (.branch 70
 (.branch 65
 (.branch 62
 (.branch 61
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))
 (.branch 67
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 68
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 69
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.leaf (RawLeafCertificate.Certificate.quota 2))))))
 (.branch 75
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 78
 (.branch 76
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 77
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.leaf (RawLeafCertificate.Certificate.quota 2))))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))))))
 (.branch 121
 (.branch 101
 (.branch 91
 (.branch 86
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 88
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 89
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 90
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 1))))))
 (.branch 96
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 98
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 99
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.leaf (RawLeafCertificate.Certificate.quota 2))))))
 (.branch 111
 (.branch 106
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 108
 (.branch 107
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))
 (.leaf (RawLeafCertificate.Certificate.quota 2))))
 (.branch 116
 (.branch 113
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 114
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 115
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))))
 (.branch 141
 (.branch 131
 (.branch 126
 (.branch 123
 (.branch 122
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 1)))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))
 (.branch 128
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 129
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 130
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 1))))))
 (.branch 136
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 138
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 139
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.leaf (RawLeafCertificate.Certificate.quota 2))))))
 (.branch 151
 (.branch 146
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 148
 (.branch 147
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))
 (.leaf (RawLeafCertificate.Certificate.quota 2))))
 (.branch 156
 (.branch 153
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 154
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 155
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSevenPure032.rawCells) (dispositionTable.get i)
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

theorem dispositionTest_block_87 : Interval dispositionTest 87 88 :=
  interval_of_check dispositionTest 87 1 (by decide +kernel)

theorem dispositionTest_block_88 : Interval dispositionTest 88 89 :=
  interval_of_check dispositionTest 88 1 (by decide +kernel)

theorem dispositionTest_block_89 : Interval dispositionTest 89 90 :=
  interval_of_check dispositionTest 89 1 (by decide +kernel)

theorem dispositionTest_block_90 : Interval dispositionTest 90 91 :=
  interval_of_check dispositionTest 90 1 (by decide +kernel)

theorem dispositionTest_block_91 : Interval dispositionTest 91 92 :=
  interval_of_check dispositionTest 91 1 (by decide +kernel)

theorem dispositionTest_block_92 : Interval dispositionTest 92 93 :=
  interval_of_check dispositionTest 92 1 (by decide +kernel)

theorem dispositionTest_block_93 : Interval dispositionTest 93 94 :=
  interval_of_check dispositionTest 93 1 (by decide +kernel)

theorem dispositionTest_block_94 : Interval dispositionTest 94 95 :=
  interval_of_check dispositionTest 94 1 (by decide +kernel)

theorem dispositionTest_block_95 : Interval dispositionTest 95 96 :=
  interval_of_check dispositionTest 95 1 (by decide +kernel)

theorem dispositionTest_block_96 : Interval dispositionTest 96 97 :=
  interval_of_check dispositionTest 96 1 (by decide +kernel)

theorem dispositionTest_block_97 : Interval dispositionTest 97 98 :=
  interval_of_check dispositionTest 97 1 (by decide +kernel)

theorem dispositionTest_block_98 : Interval dispositionTest 98 99 :=
  interval_of_check dispositionTest 98 1 (by decide +kernel)

theorem dispositionTest_block_99 : Interval dispositionTest 99 100 :=
  interval_of_check dispositionTest 99 1 (by decide +kernel)

theorem dispositionTest_block_100 : Interval dispositionTest 100 101 :=
  interval_of_check dispositionTest 100 1 (by decide +kernel)

theorem dispositionTest_block_101 : Interval dispositionTest 101 102 :=
  interval_of_check dispositionTest 101 1 (by decide +kernel)

theorem dispositionTest_block_102 : Interval dispositionTest 102 103 :=
  interval_of_check dispositionTest 102 1 (by decide +kernel)

theorem dispositionTest_block_103 : Interval dispositionTest 103 104 :=
  interval_of_check dispositionTest 103 1 (by decide +kernel)

theorem dispositionTest_block_104 : Interval dispositionTest 104 105 :=
  interval_of_check dispositionTest 104 1 (by decide +kernel)

theorem dispositionTest_block_105 : Interval dispositionTest 105 106 :=
  interval_of_check dispositionTest 105 1 (by decide +kernel)

theorem dispositionTest_block_106 : Interval dispositionTest 106 107 :=
  interval_of_check dispositionTest 106 1 (by decide +kernel)

theorem dispositionTest_block_107 : Interval dispositionTest 107 108 :=
  interval_of_check dispositionTest 107 1 (by decide +kernel)

theorem dispositionTest_block_108 : Interval dispositionTest 108 109 :=
  interval_of_check dispositionTest 108 1 (by decide +kernel)

theorem dispositionTest_block_109 : Interval dispositionTest 109 110 :=
  interval_of_check dispositionTest 109 1 (by decide +kernel)

theorem dispositionTest_block_110 : Interval dispositionTest 110 111 :=
  interval_of_check dispositionTest 110 1 (by decide +kernel)

theorem dispositionTest_block_111 : Interval dispositionTest 111 112 :=
  interval_of_check dispositionTest 111 1 (by decide +kernel)

theorem dispositionTest_block_112 : Interval dispositionTest 112 113 :=
  interval_of_check dispositionTest 112 1 (by decide +kernel)

theorem dispositionTest_block_113 : Interval dispositionTest 113 114 :=
  interval_of_check dispositionTest 113 1 (by decide +kernel)

theorem dispositionTest_block_114 : Interval dispositionTest 114 115 :=
  interval_of_check dispositionTest 114 1 (by decide +kernel)

theorem dispositionTest_block_115 : Interval dispositionTest 115 116 :=
  interval_of_check dispositionTest 115 1 (by decide +kernel)

theorem dispositionTest_block_116 : Interval dispositionTest 116 117 :=
  interval_of_check dispositionTest 116 1 (by decide +kernel)

theorem dispositionTest_block_117 : Interval dispositionTest 117 118 :=
  interval_of_check dispositionTest 117 1 (by decide +kernel)

theorem dispositionTest_block_118 : Interval dispositionTest 118 119 :=
  interval_of_check dispositionTest 118 1 (by decide +kernel)

theorem dispositionTest_block_119 : Interval dispositionTest 119 120 :=
  interval_of_check dispositionTest 119 1 (by decide +kernel)

theorem dispositionTest_block_120 : Interval dispositionTest 120 121 :=
  interval_of_check dispositionTest 120 1 (by decide +kernel)

theorem dispositionTest_block_121 : Interval dispositionTest 121 122 :=
  interval_of_check dispositionTest 121 1 (by decide +kernel)

theorem dispositionTest_block_122 : Interval dispositionTest 122 123 :=
  interval_of_check dispositionTest 122 1 (by decide +kernel)

theorem dispositionTest_block_123 : Interval dispositionTest 123 124 :=
  interval_of_check dispositionTest 123 1 (by decide +kernel)

theorem dispositionTest_block_124 : Interval dispositionTest 124 125 :=
  interval_of_check dispositionTest 124 1 (by decide +kernel)

theorem dispositionTest_block_125 : Interval dispositionTest 125 126 :=
  interval_of_check dispositionTest 125 1 (by decide +kernel)

theorem dispositionTest_block_126 : Interval dispositionTest 126 127 :=
  interval_of_check dispositionTest 126 1 (by decide +kernel)

theorem dispositionTest_block_127 : Interval dispositionTest 127 128 :=
  interval_of_check dispositionTest 127 1 (by decide +kernel)

theorem dispositionTest_block_128 : Interval dispositionTest 128 129 :=
  interval_of_check dispositionTest 128 1 (by decide +kernel)

theorem dispositionTest_block_129 : Interval dispositionTest 129 130 :=
  interval_of_check dispositionTest 129 1 (by decide +kernel)

theorem dispositionTest_block_130 : Interval dispositionTest 130 131 :=
  interval_of_check dispositionTest 130 1 (by decide +kernel)

theorem dispositionTest_block_131 : Interval dispositionTest 131 132 :=
  interval_of_check dispositionTest 131 1 (by decide +kernel)

theorem dispositionTest_block_132 : Interval dispositionTest 132 133 :=
  interval_of_check dispositionTest 132 1 (by decide +kernel)

theorem dispositionTest_block_133 : Interval dispositionTest 133 134 :=
  interval_of_check dispositionTest 133 1 (by decide +kernel)

theorem dispositionTest_block_134 : Interval dispositionTest 134 135 :=
  interval_of_check dispositionTest 134 1 (by decide +kernel)

theorem dispositionTest_block_135 : Interval dispositionTest 135 136 :=
  interval_of_check dispositionTest 135 1 (by decide +kernel)

theorem dispositionTest_block_136 : Interval dispositionTest 136 137 :=
  interval_of_check dispositionTest 136 1 (by decide +kernel)

theorem dispositionTest_block_137 : Interval dispositionTest 137 138 :=
  interval_of_check dispositionTest 137 1 (by decide +kernel)

theorem dispositionTest_block_138 : Interval dispositionTest 138 139 :=
  interval_of_check dispositionTest 138 1 (by decide +kernel)

theorem dispositionTest_block_139 : Interval dispositionTest 139 140 :=
  interval_of_check dispositionTest 139 1 (by decide +kernel)

theorem dispositionTest_block_140 : Interval dispositionTest 140 141 :=
  interval_of_check dispositionTest 140 1 (by decide +kernel)

theorem dispositionTest_block_141 : Interval dispositionTest 141 142 :=
  interval_of_check dispositionTest 141 1 (by decide +kernel)

theorem dispositionTest_block_142 : Interval dispositionTest 142 143 :=
  interval_of_check dispositionTest 142 1 (by decide +kernel)

theorem dispositionTest_block_143 : Interval dispositionTest 143 144 :=
  interval_of_check dispositionTest 143 1 (by decide +kernel)

theorem dispositionTest_block_144 : Interval dispositionTest 144 145 :=
  interval_of_check dispositionTest 144 1 (by decide +kernel)

theorem dispositionTest_block_145 : Interval dispositionTest 145 146 :=
  interval_of_check dispositionTest 145 1 (by decide +kernel)

theorem dispositionTest_block_146 : Interval dispositionTest 146 147 :=
  interval_of_check dispositionTest 146 1 (by decide +kernel)

theorem dispositionTest_block_147 : Interval dispositionTest 147 148 :=
  interval_of_check dispositionTest 147 1 (by decide +kernel)

theorem dispositionTest_block_148 : Interval dispositionTest 148 149 :=
  interval_of_check dispositionTest 148 1 (by decide +kernel)

theorem dispositionTest_block_149 : Interval dispositionTest 149 150 :=
  interval_of_check dispositionTest 149 1 (by decide +kernel)

theorem dispositionTest_block_150 : Interval dispositionTest 150 151 :=
  interval_of_check dispositionTest 150 1 (by decide +kernel)

theorem dispositionTest_block_151 : Interval dispositionTest 151 152 :=
  interval_of_check dispositionTest 151 1 (by decide +kernel)

theorem dispositionTest_block_152 : Interval dispositionTest 152 153 :=
  interval_of_check dispositionTest 152 1 (by decide +kernel)

theorem dispositionTest_block_153 : Interval dispositionTest 153 154 :=
  interval_of_check dispositionTest 153 1 (by decide +kernel)

theorem dispositionTest_block_154 : Interval dispositionTest 154 155 :=
  interval_of_check dispositionTest 154 1 (by decide +kernel)

theorem dispositionTest_block_155 : Interval dispositionTest 155 156 :=
  interval_of_check dispositionTest 155 1 (by decide +kernel)

theorem dispositionTest_block_156 : Interval dispositionTest 156 157 :=
  interval_of_check dispositionTest 156 1 (by decide +kernel)

theorem dispositionTest_block_157 : Interval dispositionTest 157 158 :=
  interval_of_check dispositionTest 157 1 (by decide +kernel)

theorem dispositionTest_block_158 : Interval dispositionTest 158 159 :=
  interval_of_check dispositionTest 158 1 (by decide +kernel)

theorem dispositionTest_block_159 : Interval dispositionTest 159 160 :=
  interval_of_check dispositionTest 159 1 (by decide +kernel)

theorem dispositionTest_block_160 : Interval dispositionTest 160 161 :=
  interval_of_check dispositionTest 160 1 (by decide +kernel)

theorem dispositionTest_block_161 : Interval dispositionTest 161 162 :=
  interval_of_check dispositionTest 161 1 (by decide +kernel)

theorem dispositionTest_complete : Interval dispositionTest 0 162 :=
  (interval_append dispositionTest 0 81 162
  (interval_append dispositionTest 0 40 81
  (interval_append dispositionTest 0 20 40
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
  (interval_append dispositionTest 20 30 40
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
  (interval_append dispositionTest 30 35 40
  (interval_append dispositionTest 30 32 35
  (interval_append dispositionTest 30 31 32
  dispositionTest_block_30
  dispositionTest_block_31)
  (interval_append dispositionTest 32 33 35
  dispositionTest_block_32
  (interval_append dispositionTest 33 34 35
  dispositionTest_block_33
  dispositionTest_block_34)))
  (interval_append dispositionTest 35 37 40
  (interval_append dispositionTest 35 36 37
  dispositionTest_block_35
  dispositionTest_block_36)
  (interval_append dispositionTest 37 38 40
  dispositionTest_block_37
  (interval_append dispositionTest 38 39 40
  dispositionTest_block_38
  dispositionTest_block_39))))))
  (interval_append dispositionTest 40 60 81
  (interval_append dispositionTest 40 50 60
  (interval_append dispositionTest 40 45 50
  (interval_append dispositionTest 40 42 45
  (interval_append dispositionTest 40 41 42
  dispositionTest_block_40
  dispositionTest_block_41)
  (interval_append dispositionTest 42 43 45
  dispositionTest_block_42
  (interval_append dispositionTest 43 44 45
  dispositionTest_block_43
  dispositionTest_block_44)))
  (interval_append dispositionTest 45 47 50
  (interval_append dispositionTest 45 46 47
  dispositionTest_block_45
  dispositionTest_block_46)
  (interval_append dispositionTest 47 48 50
  dispositionTest_block_47
  (interval_append dispositionTest 48 49 50
  dispositionTest_block_48
  dispositionTest_block_49))))
  (interval_append dispositionTest 50 55 60
  (interval_append dispositionTest 50 52 55
  (interval_append dispositionTest 50 51 52
  dispositionTest_block_50
  dispositionTest_block_51)
  (interval_append dispositionTest 52 53 55
  dispositionTest_block_52
  (interval_append dispositionTest 53 54 55
  dispositionTest_block_53
  dispositionTest_block_54)))
  (interval_append dispositionTest 55 57 60
  (interval_append dispositionTest 55 56 57
  dispositionTest_block_55
  dispositionTest_block_56)
  (interval_append dispositionTest 57 58 60
  dispositionTest_block_57
  (interval_append dispositionTest 58 59 60
  dispositionTest_block_58
  dispositionTest_block_59)))))
  (interval_append dispositionTest 60 70 81
  (interval_append dispositionTest 60 65 70
  (interval_append dispositionTest 60 62 65
  (interval_append dispositionTest 60 61 62
  dispositionTest_block_60
  dispositionTest_block_61)
  (interval_append dispositionTest 62 63 65
  dispositionTest_block_62
  (interval_append dispositionTest 63 64 65
  dispositionTest_block_63
  dispositionTest_block_64)))
  (interval_append dispositionTest 65 67 70
  (interval_append dispositionTest 65 66 67
  dispositionTest_block_65
  dispositionTest_block_66)
  (interval_append dispositionTest 67 68 70
  dispositionTest_block_67
  (interval_append dispositionTest 68 69 70
  dispositionTest_block_68
  dispositionTest_block_69))))
  (interval_append dispositionTest 70 75 81
  (interval_append dispositionTest 70 72 75
  (interval_append dispositionTest 70 71 72
  dispositionTest_block_70
  dispositionTest_block_71)
  (interval_append dispositionTest 72 73 75
  dispositionTest_block_72
  (interval_append dispositionTest 73 74 75
  dispositionTest_block_73
  dispositionTest_block_74)))
  (interval_append dispositionTest 75 78 81
  (interval_append dispositionTest 75 76 78
  dispositionTest_block_75
  (interval_append dispositionTest 76 77 78
  dispositionTest_block_76
  dispositionTest_block_77))
  (interval_append dispositionTest 78 79 81
  dispositionTest_block_78
  (interval_append dispositionTest 79 80 81
  dispositionTest_block_79
  dispositionTest_block_80)))))))
  (interval_append dispositionTest 81 121 162
  (interval_append dispositionTest 81 101 121
  (interval_append dispositionTest 81 91 101
  (interval_append dispositionTest 81 86 91
  (interval_append dispositionTest 81 83 86
  (interval_append dispositionTest 81 82 83
  dispositionTest_block_81
  dispositionTest_block_82)
  (interval_append dispositionTest 83 84 86
  dispositionTest_block_83
  (interval_append dispositionTest 84 85 86
  dispositionTest_block_84
  dispositionTest_block_85)))
  (interval_append dispositionTest 86 88 91
  (interval_append dispositionTest 86 87 88
  dispositionTest_block_86
  dispositionTest_block_87)
  (interval_append dispositionTest 88 89 91
  dispositionTest_block_88
  (interval_append dispositionTest 89 90 91
  dispositionTest_block_89
  dispositionTest_block_90))))
  (interval_append dispositionTest 91 96 101
  (interval_append dispositionTest 91 93 96
  (interval_append dispositionTest 91 92 93
  dispositionTest_block_91
  dispositionTest_block_92)
  (interval_append dispositionTest 93 94 96
  dispositionTest_block_93
  (interval_append dispositionTest 94 95 96
  dispositionTest_block_94
  dispositionTest_block_95)))
  (interval_append dispositionTest 96 98 101
  (interval_append dispositionTest 96 97 98
  dispositionTest_block_96
  dispositionTest_block_97)
  (interval_append dispositionTest 98 99 101
  dispositionTest_block_98
  (interval_append dispositionTest 99 100 101
  dispositionTest_block_99
  dispositionTest_block_100)))))
  (interval_append dispositionTest 101 111 121
  (interval_append dispositionTest 101 106 111
  (interval_append dispositionTest 101 103 106
  (interval_append dispositionTest 101 102 103
  dispositionTest_block_101
  dispositionTest_block_102)
  (interval_append dispositionTest 103 104 106
  dispositionTest_block_103
  (interval_append dispositionTest 104 105 106
  dispositionTest_block_104
  dispositionTest_block_105)))
  (interval_append dispositionTest 106 108 111
  (interval_append dispositionTest 106 107 108
  dispositionTest_block_106
  dispositionTest_block_107)
  (interval_append dispositionTest 108 109 111
  dispositionTest_block_108
  (interval_append dispositionTest 109 110 111
  dispositionTest_block_109
  dispositionTest_block_110))))
  (interval_append dispositionTest 111 116 121
  (interval_append dispositionTest 111 113 116
  (interval_append dispositionTest 111 112 113
  dispositionTest_block_111
  dispositionTest_block_112)
  (interval_append dispositionTest 113 114 116
  dispositionTest_block_113
  (interval_append dispositionTest 114 115 116
  dispositionTest_block_114
  dispositionTest_block_115)))
  (interval_append dispositionTest 116 118 121
  (interval_append dispositionTest 116 117 118
  dispositionTest_block_116
  dispositionTest_block_117)
  (interval_append dispositionTest 118 119 121
  dispositionTest_block_118
  (interval_append dispositionTest 119 120 121
  dispositionTest_block_119
  dispositionTest_block_120))))))
  (interval_append dispositionTest 121 141 162
  (interval_append dispositionTest 121 131 141
  (interval_append dispositionTest 121 126 131
  (interval_append dispositionTest 121 123 126
  (interval_append dispositionTest 121 122 123
  dispositionTest_block_121
  dispositionTest_block_122)
  (interval_append dispositionTest 123 124 126
  dispositionTest_block_123
  (interval_append dispositionTest 124 125 126
  dispositionTest_block_124
  dispositionTest_block_125)))
  (interval_append dispositionTest 126 128 131
  (interval_append dispositionTest 126 127 128
  dispositionTest_block_126
  dispositionTest_block_127)
  (interval_append dispositionTest 128 129 131
  dispositionTest_block_128
  (interval_append dispositionTest 129 130 131
  dispositionTest_block_129
  dispositionTest_block_130))))
  (interval_append dispositionTest 131 136 141
  (interval_append dispositionTest 131 133 136
  (interval_append dispositionTest 131 132 133
  dispositionTest_block_131
  dispositionTest_block_132)
  (interval_append dispositionTest 133 134 136
  dispositionTest_block_133
  (interval_append dispositionTest 134 135 136
  dispositionTest_block_134
  dispositionTest_block_135)))
  (interval_append dispositionTest 136 138 141
  (interval_append dispositionTest 136 137 138
  dispositionTest_block_136
  dispositionTest_block_137)
  (interval_append dispositionTest 138 139 141
  dispositionTest_block_138
  (interval_append dispositionTest 139 140 141
  dispositionTest_block_139
  dispositionTest_block_140)))))
  (interval_append dispositionTest 141 151 162
  (interval_append dispositionTest 141 146 151
  (interval_append dispositionTest 141 143 146
  (interval_append dispositionTest 141 142 143
  dispositionTest_block_141
  dispositionTest_block_142)
  (interval_append dispositionTest 143 144 146
  dispositionTest_block_143
  (interval_append dispositionTest 144 145 146
  dispositionTest_block_144
  dispositionTest_block_145)))
  (interval_append dispositionTest 146 148 151
  (interval_append dispositionTest 146 147 148
  dispositionTest_block_146
  dispositionTest_block_147)
  (interval_append dispositionTest 148 149 151
  dispositionTest_block_148
  (interval_append dispositionTest 149 150 151
  dispositionTest_block_149
  dispositionTest_block_150))))
  (interval_append dispositionTest 151 156 162
  (interval_append dispositionTest 151 153 156
  (interval_append dispositionTest 151 152 153
  dispositionTest_block_151
  dispositionTest_block_152)
  (interval_append dispositionTest 153 154 156
  dispositionTest_block_153
  (interval_append dispositionTest 154 155 156
  dispositionTest_block_154
  dispositionTest_block_155)))
  (interval_append dispositionTest 156 159 162
  (interval_append dispositionTest 156 157 159
  dispositionTest_block_156
  (interval_append dispositionTest 157 158 159
  dispositionTest_block_157
  dispositionTest_block_158))
  (interval_append dispositionTest 159 160 162
  dispositionTest_block_159
  (interval_append dispositionTest 160 161 162
  dispositionTest_block_160
  dispositionTest_block_161))))))))
theorem disposition_checked (j : Fin leafCount) :
    RawLeafCertificate.check quota ((rawLeaves j.val).map Papers.RationalityTen.RootedCaches.RootedSevenPure032.rawCells)
      (disposition j) = true :=
  dispositionTest_complete j.val (Nat.zero_le _) j.isLt

end Papers.RationalityTen.RootedForests.RootedRawForest0066
