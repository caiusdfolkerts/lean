module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
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
cert_disposition_2
cert_dispositionTest_2 032
cert_dispositionTest_block 0 1
cert_dispositionTest_block 1 2
cert_dispositionTest_block 2 3
cert_dispositionTest_block 3 4
cert_dispositionTest_block 4 5
cert_dispositionTest_block 5 6
cert_dispositionTest_block 6 7
cert_dispositionTest_block 7 8
cert_dispositionTest_block 8 9
cert_dispositionTest_block 9 10
cert_dispositionTest_block 10 11
cert_dispositionTest_block 11 12
cert_dispositionTest_block 12 13
cert_dispositionTest_block 13 14
cert_dispositionTest_block 14 15
cert_dispositionTest_block 15 16
cert_dispositionTest_block 16 17
cert_dispositionTest_block 17 18
cert_dispositionTest_block 18 19
cert_dispositionTest_block 19 20
cert_dispositionTest_block 20 21
cert_dispositionTest_block 21 22
cert_dispositionTest_block 22 23
cert_dispositionTest_block 23 24
cert_dispositionTest_block 24 25
cert_dispositionTest_block 25 26
cert_dispositionTest_block 26 27
cert_dispositionTest_block 27 28
cert_dispositionTest_block 28 29
cert_dispositionTest_block 29 30
cert_dispositionTest_block 30 31
cert_dispositionTest_block 31 32
cert_dispositionTest_block 32 33
cert_dispositionTest_block 33 34
cert_dispositionTest_block 34 35
cert_dispositionTest_block 35 36
cert_dispositionTest_block 36 37
cert_dispositionTest_block 37 38
cert_dispositionTest_block 38 39
cert_dispositionTest_block 39 40
cert_dispositionTest_block 40 41
cert_dispositionTest_block 41 42
cert_dispositionTest_block 42 43
cert_dispositionTest_block 43 44
cert_dispositionTest_block 44 45
cert_dispositionTest_block 45 46
cert_dispositionTest_block 46 47
cert_dispositionTest_block 47 48
cert_dispositionTest_block 48 49
cert_dispositionTest_block 49 50
cert_dispositionTest_block 50 51
cert_dispositionTest_block 51 52
cert_dispositionTest_block 52 53
cert_dispositionTest_block 53 54
cert_dispositionTest_block 54 55
cert_dispositionTest_block 55 56
cert_dispositionTest_block 56 57
cert_dispositionTest_block 57 58
cert_dispositionTest_block 58 59
cert_dispositionTest_block 59 60
cert_dispositionTest_block 60 61
cert_dispositionTest_block 61 62
cert_dispositionTest_block 62 63
cert_dispositionTest_block 63 64
cert_dispositionTest_block 64 65
cert_dispositionTest_block 65 66
cert_dispositionTest_block 66 67
cert_dispositionTest_block 67 68
cert_dispositionTest_block 68 69
cert_dispositionTest_block 69 70
cert_dispositionTest_block 70 71
cert_dispositionTest_block 71 72
cert_dispositionTest_block 72 73
cert_dispositionTest_block 73 74
cert_dispositionTest_block 74 75
cert_dispositionTest_block 75 76
cert_dispositionTest_block 76 77
cert_dispositionTest_block 77 78
cert_dispositionTest_block 78 79
cert_dispositionTest_block 79 80
cert_dispositionTest_block 80 81
cert_dispositionTest_block 81 82
cert_dispositionTest_block 82 83
cert_dispositionTest_block 83 84
cert_dispositionTest_block 84 85
cert_dispositionTest_block 85 86
cert_dispositionTest_block 86 87
cert_dispositionTest_block 87 88
cert_dispositionTest_block 88 89
cert_dispositionTest_block 89 90
cert_dispositionTest_block 90 91
cert_dispositionTest_block 91 92
cert_dispositionTest_block 92 93
cert_dispositionTest_block 93 94
cert_dispositionTest_block 94 95
cert_dispositionTest_block 95 96
cert_dispositionTest_block 96 97
cert_dispositionTest_block 97 98
cert_dispositionTest_block 98 99
cert_dispositionTest_block 99 100
cert_dispositionTest_block 100 101
cert_dispositionTest_block 101 102
cert_dispositionTest_block 102 103
cert_dispositionTest_block 103 104
cert_dispositionTest_block 104 105
cert_dispositionTest_block 105 106
cert_dispositionTest_block 106 107
cert_dispositionTest_block 107 108
cert_dispositionTest_block 108 109
cert_dispositionTest_block 109 110
cert_dispositionTest_block 110 111
cert_dispositionTest_block 111 112
cert_dispositionTest_block 112 113
cert_dispositionTest_block 113 114
cert_dispositionTest_block 114 115
cert_dispositionTest_block 115 116
cert_dispositionTest_block 116 117
cert_dispositionTest_block 117 118
cert_dispositionTest_block 118 119
cert_dispositionTest_block 119 120
cert_dispositionTest_block 120 121
cert_dispositionTest_block 121 122
cert_dispositionTest_block 122 123
cert_dispositionTest_block 123 124
cert_dispositionTest_block 124 125
cert_dispositionTest_block 125 126
cert_dispositionTest_block 126 127
cert_dispositionTest_block 127 128
cert_dispositionTest_block 128 129
cert_dispositionTest_block 129 130
cert_dispositionTest_block 130 131
cert_dispositionTest_block 131 132
cert_dispositionTest_block 132 133
cert_dispositionTest_block 133 134
cert_dispositionTest_block 134 135
cert_dispositionTest_block 135 136
cert_dispositionTest_block 136 137
cert_dispositionTest_block 137 138
cert_dispositionTest_block 138 139
cert_dispositionTest_block 139 140
cert_dispositionTest_block 140 141
cert_dispositionTest_block 141 142
cert_dispositionTest_block 142 143
cert_dispositionTest_block 143 144
cert_dispositionTest_block 144 145
cert_dispositionTest_block 145 146
cert_dispositionTest_block 146 147
cert_dispositionTest_block 147 148
cert_dispositionTest_block 148 149
cert_dispositionTest_block 149 150
cert_dispositionTest_block 150 151
cert_dispositionTest_block 151 152
cert_dispositionTest_block 152 153
cert_dispositionTest_block 153 154
cert_dispositionTest_block 154 155
cert_dispositionTest_block 155 156
cert_dispositionTest_block 156 157
cert_dispositionTest_block 157 158
cert_dispositionTest_block 158 159
cert_dispositionTest_block 159 160
cert_dispositionTest_block 160 161
cert_dispositionTest_block 161 162
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
cert_disposition_checked_2 032
end Papers.RationalityTen.RootedForests.RootedRawForest0066
