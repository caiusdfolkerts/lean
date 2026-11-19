module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0868Data
public import RawLeafCertificate

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0868
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 90
 (.branch 45
 (.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (RawLeafCertificate.Certificate.quota 3))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))
 (.branch 8
 (.branch 6
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 7
 (.leaf (RawLeafCertificate.Certificate.quota 3))
 (.leaf (RawLeafCertificate.Certificate.quota 2))))
 (.leaf (RawLeafCertificate.Certificate.quota 2))))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))
 (.branch 67
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 78
 (.branch 72
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 75
 (.branch 73
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 74
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 3))))
 (.branch 76
 (.leaf (RawLeafCertificate.Certificate.quota 3))
 (.branch 77
 (.leaf (RawLeafCertificate.Certificate.quota 3))
 (.leaf (RawLeafCertificate.Certificate.quota 2))))))
 (.branch 84
 (.branch 81
 (.branch 79
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 3)))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))
 (.branch 87
 (.branch 85
 (.leaf (RawLeafCertificate.Certificate.quota 3))
 (.branch 86
 (.leaf (RawLeafCertificate.Certificate.quota 3))
 (.leaf (RawLeafCertificate.Certificate.quota 2))))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))))))
 (.branch 135
 (.branch 112
 (.branch 101
 (.branch 95
 (.branch 92
 (.branch 91
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.leaf (RawLeafCertificate.Certificate.quota 3)))
 (.leaf (RawLeafCertificate.Certificate.quota 3)))
 (.branch 98
 (.branch 96
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 3)))
 (.branch 99
 (.leaf (RawLeafCertificate.Certificate.quota 3))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))))
 (.branch 106
 (.branch 103
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 104
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 105
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 1)))))
 (.branch 109
 (.branch 107
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 108
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 1))))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))))
 (.branch 123
 (.branch 117
 (.branch 114
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.branch 115
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 3))))
 (.branch 120
 (.branch 118
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 3)))
 (.branch 121
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 3)))))
 (.leaf (RawLeafCertificate.Certificate.quota 2))))
 (.branch 157
 (.branch 146
 (.branch 140
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 143
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 144
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 145
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.leaf (RawLeafCertificate.Certificate.quota 2))))))
 (.branch 151
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 154
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 155
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 156
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 1)))))))
 (.branch 168
 (.branch 162
 (.branch 159
 (.leaf (RawLeafCertificate.Certificate.quota 3))
 (.branch 160
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 161
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.leaf (RawLeafCertificate.Certificate.quota 3)))))
 (.branch 165
 (.branch 163
 (.leaf (RawLeafCertificate.Certificate.quota 3))
 (.branch 164
 (.leaf (RawLeafCertificate.Certificate.quota 3))
 (.leaf (RawLeafCertificate.Certificate.quota 1))))
 (.branch 166
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.branch 167
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.leaf (RawLeafCertificate.Certificate.quota 3))))))
 (.branch 174
 (.branch 171
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.branch 172
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 1))))
 (.branch 177
 (.branch 175
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 176
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.leaf (RawLeafCertificate.Certificate.quota 2))))
 (.leaf (RawLeafCertificate.Certificate.quota 2))))))))
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
cert_dispositionTest_block_2 41 42
cert_dispositionTest_block_2 42 43
cert_dispositionTest_block_2 43 44
cert_dispositionTest_block_2 44 45
cert_dispositionTest_block_2 45 46
cert_dispositionTest_block_2 46 47
cert_dispositionTest_block_2 47 48
cert_dispositionTest_block_2 48 49
cert_dispositionTest_block_2 49 50
cert_dispositionTest_block_2 50 51
cert_dispositionTest_block_2 51 52
cert_dispositionTest_block_2 52 53
cert_dispositionTest_block_2 53 54
cert_dispositionTest_block_2 54 55
cert_dispositionTest_block_2 55 56
cert_dispositionTest_block_2 56 57
cert_dispositionTest_block_2 57 58
cert_dispositionTest_block_2 58 59
cert_dispositionTest_block_2 59 60
cert_dispositionTest_block_2 60 61
cert_dispositionTest_block_2 61 62
cert_dispositionTest_block_2 62 63
cert_dispositionTest_block_2 63 64
cert_dispositionTest_block_2 64 65
cert_dispositionTest_block_2 65 66
cert_dispositionTest_block_2 66 67
cert_dispositionTest_block_2 67 68
cert_dispositionTest_block_2 68 69
cert_dispositionTest_block_2 69 70
cert_dispositionTest_block_2 70 71
cert_dispositionTest_block_2 71 72
cert_dispositionTest_block_2 72 73
cert_dispositionTest_block_2 73 74
cert_dispositionTest_block_2 74 75
cert_dispositionTest_block_2 75 76
cert_dispositionTest_block_2 76 77
cert_dispositionTest_block_2 77 78
cert_dispositionTest_block_2 78 79
cert_dispositionTest_block_2 79 80
cert_dispositionTest_block_2 80 81
cert_dispositionTest_block_2 81 82
cert_dispositionTest_block_2 82 83
cert_dispositionTest_block_2 83 84
cert_dispositionTest_block_2 84 85
cert_dispositionTest_block_2 85 86
cert_dispositionTest_block_2 86 87
cert_dispositionTest_block_2 87 88
cert_dispositionTest_block_2 88 89
cert_dispositionTest_block_2 89 90
cert_dispositionTest_block_2 90 91
cert_dispositionTest_block_2 91 92
cert_dispositionTest_block_2 92 93
cert_dispositionTest_block_2 93 94
cert_dispositionTest_block_2 94 95
cert_dispositionTest_block_2 95 96
cert_dispositionTest_block_2 96 97
cert_dispositionTest_block_2 97 98
cert_dispositionTest_block_2 98 99
cert_dispositionTest_block_2 99 100
cert_dispositionTest_block_2 100 101
cert_dispositionTest_block_2 101 102
cert_dispositionTest_block_2 102 103
cert_dispositionTest_block_2 103 104
cert_dispositionTest_block_2 104 105
cert_dispositionTest_block_2 105 106
cert_dispositionTest_block_2 106 107
cert_dispositionTest_block_2 107 108
cert_dispositionTest_block_2 108 109
cert_dispositionTest_block_2 109 110
cert_dispositionTest_block_2 110 111
cert_dispositionTest_block_2 111 112
cert_dispositionTest_block_2 112 113
cert_dispositionTest_block_2 113 114
cert_dispositionTest_block_2 114 115
cert_dispositionTest_block_2 115 116
cert_dispositionTest_block_2 116 117
cert_dispositionTest_block_2 117 118
cert_dispositionTest_block_2 118 119
cert_dispositionTest_block_2 119 120
cert_dispositionTest_block_2 120 121
cert_dispositionTest_block_2 121 122
cert_dispositionTest_block_2 122 123
cert_dispositionTest_block_2 123 124
cert_dispositionTest_block_2 124 125
cert_dispositionTest_block_2 125 126
cert_dispositionTest_block_2 126 127
cert_dispositionTest_block_2 127 128
cert_dispositionTest_block_2 128 129
cert_dispositionTest_block_2 129 130
cert_dispositionTest_block_2 130 131
cert_dispositionTest_block_2 131 132
cert_dispositionTest_block_2 132 133
cert_dispositionTest_block_2 133 134
cert_dispositionTest_block_2 134 135
cert_dispositionTest_block_2 135 136
cert_dispositionTest_block_2 136 137
cert_dispositionTest_block_2 137 138
cert_dispositionTest_block_2 138 139
cert_dispositionTest_block_2 139 140
cert_dispositionTest_block_2 140 141
cert_dispositionTest_block_2 141 142
cert_dispositionTest_block_2 142 143
cert_dispositionTest_block_2 143 144
cert_dispositionTest_block_2 144 145
cert_dispositionTest_block_2 145 146
cert_dispositionTest_block_2 146 147
cert_dispositionTest_block_2 147 148
cert_dispositionTest_block_2 148 149
cert_dispositionTest_block_2 149 150
cert_dispositionTest_block_2 150 151
cert_dispositionTest_block_2 151 152
cert_dispositionTest_block_2 152 153
cert_dispositionTest_block_2 153 154
cert_dispositionTest_block_2 154 155
cert_dispositionTest_block_2 155 156
cert_dispositionTest_block_2 156 157
cert_dispositionTest_block_2 157 158
cert_dispositionTest_block_2 158 159
cert_dispositionTest_block_2 159 160
cert_dispositionTest_block_2 160 161
cert_dispositionTest_block_2 161 162
cert_dispositionTest_block_2 162 163
cert_dispositionTest_block_2 163 164
cert_dispositionTest_block_2 164 165
cert_dispositionTest_block_2 165 166
cert_dispositionTest_block_2 166 167
cert_dispositionTest_block_2 167 168
cert_dispositionTest_block_2 168 169
cert_dispositionTest_block_2 169 170
cert_dispositionTest_block_2 170 171
cert_dispositionTest_block_2 171 172
cert_dispositionTest_block_2 172 173
cert_dispositionTest_block_2 173 174
cert_dispositionTest_block_2 174 175
cert_dispositionTest_block_2 175 176
cert_dispositionTest_block_2 176 177
cert_dispositionTest_block_2 177 178
cert_dispositionTest_block_2 178 179
cert_dispositionTest_block_2 179 180
theorem dispositionTest_complete : Interval dispositionTest 0 180 :=
  (interval_append dispositionTest 0 90 180
  (interval_append dispositionTest 0 45 90
  (interval_append dispositionTest 0 22 45
  (interval_append dispositionTest 0 11 22
  (interval_append dispositionTest 0 5 11
  (interval_append dispositionTest 0 2 5
  (interval_append dispositionTest 0 1 2
  dispositionTest_block_0
  dispositionTest_block_1)
  (interval_append dispositionTest 2 3 5
  dispositionTest_block_2
  (interval_append dispositionTest 3 4 5
  dispositionTest_block_3
  dispositionTest_block_4)))
  (interval_append dispositionTest 5 8 11
  (interval_append dispositionTest 5 6 8
  dispositionTest_block_5
  (interval_append dispositionTest 6 7 8
  dispositionTest_block_6
  dispositionTest_block_7))
  (interval_append dispositionTest 8 9 11
  dispositionTest_block_8
  (interval_append dispositionTest 9 10 11
  dispositionTest_block_9
  dispositionTest_block_10))))
  (interval_append dispositionTest 11 16 22
  (interval_append dispositionTest 11 13 16
  (interval_append dispositionTest 11 12 13
  dispositionTest_block_11
  dispositionTest_block_12)
  (interval_append dispositionTest 13 14 16
  dispositionTest_block_13
  (interval_append dispositionTest 14 15 16
  dispositionTest_block_14
  dispositionTest_block_15)))
  (interval_append dispositionTest 16 19 22
  (interval_append dispositionTest 16 17 19
  dispositionTest_block_16
  (interval_append dispositionTest 17 18 19
  dispositionTest_block_17
  dispositionTest_block_18))
  (interval_append dispositionTest 19 20 22
  dispositionTest_block_19
  (interval_append dispositionTest 20 21 22
  dispositionTest_block_20
  dispositionTest_block_21)))))
  (interval_append dispositionTest 22 33 45
  (interval_append dispositionTest 22 27 33
  (interval_append dispositionTest 22 24 27
  (interval_append dispositionTest 22 23 24
  dispositionTest_block_22
  dispositionTest_block_23)
  (interval_append dispositionTest 24 25 27
  dispositionTest_block_24
  (interval_append dispositionTest 25 26 27
  dispositionTest_block_25
  dispositionTest_block_26)))
  (interval_append dispositionTest 27 30 33
  (interval_append dispositionTest 27 28 30
  dispositionTest_block_27
  (interval_append dispositionTest 28 29 30
  dispositionTest_block_28
  dispositionTest_block_29))
  (interval_append dispositionTest 30 31 33
  dispositionTest_block_30
  (interval_append dispositionTest 31 32 33
  dispositionTest_block_31
  dispositionTest_block_32))))
  (interval_append dispositionTest 33 39 45
  (interval_append dispositionTest 33 36 39
  (interval_append dispositionTest 33 34 36
  dispositionTest_block_33
  (interval_append dispositionTest 34 35 36
  dispositionTest_block_34
  dispositionTest_block_35))
  (interval_append dispositionTest 36 37 39
  dispositionTest_block_36
  (interval_append dispositionTest 37 38 39
  dispositionTest_block_37
  dispositionTest_block_38)))
  (interval_append dispositionTest 39 42 45
  (interval_append dispositionTest 39 40 42
  dispositionTest_block_39
  (interval_append dispositionTest 40 41 42
  dispositionTest_block_40
  dispositionTest_block_41))
  (interval_append dispositionTest 42 43 45
  dispositionTest_block_42
  (interval_append dispositionTest 43 44 45
  dispositionTest_block_43
  dispositionTest_block_44))))))
  (interval_append dispositionTest 45 67 90
  (interval_append dispositionTest 45 56 67
  (interval_append dispositionTest 45 50 56
  (interval_append dispositionTest 45 47 50
  (interval_append dispositionTest 45 46 47
  dispositionTest_block_45
  dispositionTest_block_46)
  (interval_append dispositionTest 47 48 50
  dispositionTest_block_47
  (interval_append dispositionTest 48 49 50
  dispositionTest_block_48
  dispositionTest_block_49)))
  (interval_append dispositionTest 50 53 56
  (interval_append dispositionTest 50 51 53
  dispositionTest_block_50
  (interval_append dispositionTest 51 52 53
  dispositionTest_block_51
  dispositionTest_block_52))
  (interval_append dispositionTest 53 54 56
  dispositionTest_block_53
  (interval_append dispositionTest 54 55 56
  dispositionTest_block_54
  dispositionTest_block_55))))
  (interval_append dispositionTest 56 61 67
  (interval_append dispositionTest 56 58 61
  (interval_append dispositionTest 56 57 58
  dispositionTest_block_56
  dispositionTest_block_57)
  (interval_append dispositionTest 58 59 61
  dispositionTest_block_58
  (interval_append dispositionTest 59 60 61
  dispositionTest_block_59
  dispositionTest_block_60)))
  (interval_append dispositionTest 61 64 67
  (interval_append dispositionTest 61 62 64
  dispositionTest_block_61
  (interval_append dispositionTest 62 63 64
  dispositionTest_block_62
  dispositionTest_block_63))
  (interval_append dispositionTest 64 65 67
  dispositionTest_block_64
  (interval_append dispositionTest 65 66 67
  dispositionTest_block_65
  dispositionTest_block_66)))))
  (interval_append dispositionTest 67 78 90
  (interval_append dispositionTest 67 72 78
  (interval_append dispositionTest 67 69 72
  (interval_append dispositionTest 67 68 69
  dispositionTest_block_67
  dispositionTest_block_68)
  (interval_append dispositionTest 69 70 72
  dispositionTest_block_69
  (interval_append dispositionTest 70 71 72
  dispositionTest_block_70
  dispositionTest_block_71)))
  (interval_append dispositionTest 72 75 78
  (interval_append dispositionTest 72 73 75
  dispositionTest_block_72
  (interval_append dispositionTest 73 74 75
  dispositionTest_block_73
  dispositionTest_block_74))
  (interval_append dispositionTest 75 76 78
  dispositionTest_block_75
  (interval_append dispositionTest 76 77 78
  dispositionTest_block_76
  dispositionTest_block_77))))
  (interval_append dispositionTest 78 84 90
  (interval_append dispositionTest 78 81 84
  (interval_append dispositionTest 78 79 81
  dispositionTest_block_78
  (interval_append dispositionTest 79 80 81
  dispositionTest_block_79
  dispositionTest_block_80))
  (interval_append dispositionTest 81 82 84
  dispositionTest_block_81
  (interval_append dispositionTest 82 83 84
  dispositionTest_block_82
  dispositionTest_block_83)))
  (interval_append dispositionTest 84 87 90
  (interval_append dispositionTest 84 85 87
  dispositionTest_block_84
  (interval_append dispositionTest 85 86 87
  dispositionTest_block_85
  dispositionTest_block_86))
  (interval_append dispositionTest 87 88 90
  dispositionTest_block_87
  (interval_append dispositionTest 88 89 90
  dispositionTest_block_88
  dispositionTest_block_89)))))))
  (interval_append dispositionTest 90 135 180
  (interval_append dispositionTest 90 112 135
  (interval_append dispositionTest 90 101 112
  (interval_append dispositionTest 90 95 101
  (interval_append dispositionTest 90 92 95
  (interval_append dispositionTest 90 91 92
  dispositionTest_block_90
  dispositionTest_block_91)
  (interval_append dispositionTest 92 93 95
  dispositionTest_block_92
  (interval_append dispositionTest 93 94 95
  dispositionTest_block_93
  dispositionTest_block_94)))
  (interval_append dispositionTest 95 98 101
  (interval_append dispositionTest 95 96 98
  dispositionTest_block_95
  (interval_append dispositionTest 96 97 98
  dispositionTest_block_96
  dispositionTest_block_97))
  (interval_append dispositionTest 98 99 101
  dispositionTest_block_98
  (interval_append dispositionTest 99 100 101
  dispositionTest_block_99
  dispositionTest_block_100))))
  (interval_append dispositionTest 101 106 112
  (interval_append dispositionTest 101 103 106
  (interval_append dispositionTest 101 102 103
  dispositionTest_block_101
  dispositionTest_block_102)
  (interval_append dispositionTest 103 104 106
  dispositionTest_block_103
  (interval_append dispositionTest 104 105 106
  dispositionTest_block_104
  dispositionTest_block_105)))
  (interval_append dispositionTest 106 109 112
  (interval_append dispositionTest 106 107 109
  dispositionTest_block_106
  (interval_append dispositionTest 107 108 109
  dispositionTest_block_107
  dispositionTest_block_108))
  (interval_append dispositionTest 109 110 112
  dispositionTest_block_109
  (interval_append dispositionTest 110 111 112
  dispositionTest_block_110
  dispositionTest_block_111)))))
  (interval_append dispositionTest 112 123 135
  (interval_append dispositionTest 112 117 123
  (interval_append dispositionTest 112 114 117
  (interval_append dispositionTest 112 113 114
  dispositionTest_block_112
  dispositionTest_block_113)
  (interval_append dispositionTest 114 115 117
  dispositionTest_block_114
  (interval_append dispositionTest 115 116 117
  dispositionTest_block_115
  dispositionTest_block_116)))
  (interval_append dispositionTest 117 120 123
  (interval_append dispositionTest 117 118 120
  dispositionTest_block_117
  (interval_append dispositionTest 118 119 120
  dispositionTest_block_118
  dispositionTest_block_119))
  (interval_append dispositionTest 120 121 123
  dispositionTest_block_120
  (interval_append dispositionTest 121 122 123
  dispositionTest_block_121
  dispositionTest_block_122))))
  (interval_append dispositionTest 123 129 135
  (interval_append dispositionTest 123 126 129
  (interval_append dispositionTest 123 124 126
  dispositionTest_block_123
  (interval_append dispositionTest 124 125 126
  dispositionTest_block_124
  dispositionTest_block_125))
  (interval_append dispositionTest 126 127 129
  dispositionTest_block_126
  (interval_append dispositionTest 127 128 129
  dispositionTest_block_127
  dispositionTest_block_128)))
  (interval_append dispositionTest 129 132 135
  (interval_append dispositionTest 129 130 132
  dispositionTest_block_129
  (interval_append dispositionTest 130 131 132
  dispositionTest_block_130
  dispositionTest_block_131))
  (interval_append dispositionTest 132 133 135
  dispositionTest_block_132
  (interval_append dispositionTest 133 134 135
  dispositionTest_block_133
  dispositionTest_block_134))))))
  (interval_append dispositionTest 135 157 180
  (interval_append dispositionTest 135 146 157
  (interval_append dispositionTest 135 140 146
  (interval_append dispositionTest 135 137 140
  (interval_append dispositionTest 135 136 137
  dispositionTest_block_135
  dispositionTest_block_136)
  (interval_append dispositionTest 137 138 140
  dispositionTest_block_137
  (interval_append dispositionTest 138 139 140
  dispositionTest_block_138
  dispositionTest_block_139)))
  (interval_append dispositionTest 140 143 146
  (interval_append dispositionTest 140 141 143
  dispositionTest_block_140
  (interval_append dispositionTest 141 142 143
  dispositionTest_block_141
  dispositionTest_block_142))
  (interval_append dispositionTest 143 144 146
  dispositionTest_block_143
  (interval_append dispositionTest 144 145 146
  dispositionTest_block_144
  dispositionTest_block_145))))
  (interval_append dispositionTest 146 151 157
  (interval_append dispositionTest 146 148 151
  (interval_append dispositionTest 146 147 148
  dispositionTest_block_146
  dispositionTest_block_147)
  (interval_append dispositionTest 148 149 151
  dispositionTest_block_148
  (interval_append dispositionTest 149 150 151
  dispositionTest_block_149
  dispositionTest_block_150)))
  (interval_append dispositionTest 151 154 157
  (interval_append dispositionTest 151 152 154
  dispositionTest_block_151
  (interval_append dispositionTest 152 153 154
  dispositionTest_block_152
  dispositionTest_block_153))
  (interval_append dispositionTest 154 155 157
  dispositionTest_block_154
  (interval_append dispositionTest 155 156 157
  dispositionTest_block_155
  dispositionTest_block_156)))))
  (interval_append dispositionTest 157 168 180
  (interval_append dispositionTest 157 162 168
  (interval_append dispositionTest 157 159 162
  (interval_append dispositionTest 157 158 159
  dispositionTest_block_157
  dispositionTest_block_158)
  (interval_append dispositionTest 159 160 162
  dispositionTest_block_159
  (interval_append dispositionTest 160 161 162
  dispositionTest_block_160
  dispositionTest_block_161)))
  (interval_append dispositionTest 162 165 168
  (interval_append dispositionTest 162 163 165
  dispositionTest_block_162
  (interval_append dispositionTest 163 164 165
  dispositionTest_block_163
  dispositionTest_block_164))
  (interval_append dispositionTest 165 166 168
  dispositionTest_block_165
  (interval_append dispositionTest 166 167 168
  dispositionTest_block_166
  dispositionTest_block_167))))
  (interval_append dispositionTest 168 174 180
  (interval_append dispositionTest 168 171 174
  (interval_append dispositionTest 168 169 171
  dispositionTest_block_168
  (interval_append dispositionTest 169 170 171
  dispositionTest_block_169
  dispositionTest_block_170))
  (interval_append dispositionTest 171 172 174
  dispositionTest_block_171
  (interval_append dispositionTest 172 173 174
  dispositionTest_block_172
  dispositionTest_block_173)))
  (interval_append dispositionTest 174 177 180
  (interval_append dispositionTest 174 175 177
  dispositionTest_block_174
  (interval_append dispositionTest 175 176 177
  dispositionTest_block_175
  dispositionTest_block_176))
  (interval_append dispositionTest 177 178 180
  dispositionTest_block_177
  (interval_append dispositionTest 178 179 180
  dispositionTest_block_178
  dispositionTest_block_179))))))))
cert_disposition_checked_4 05
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0868
