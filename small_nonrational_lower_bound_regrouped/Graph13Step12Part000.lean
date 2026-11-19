module
prelude
public meta import LowerSchemas.FiniteGraph
public meta import IntegerTables
public import GraphCatalogueData
public import Graph13Frames
public import Graph13Level12
public import Graph13Level13
public import FastGraphCatalogueCheck
public import Graph13FastEdgeMaps

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step12.Part000
open Papers.RationalityTen
open ConcreteGrowth GraphCatalogueCore GraphCatalogueCheck GraphCatalogueData FiniteChecks
cert_table_2 255
cert_lookup_5
cert_test 12 8333 13
cert_fastTest 12 8333 13
cert_fastTest_eq
cert_fast_interval
cert_checked_3 0 1
cert_checked_3 1 2
cert_checked_3 2 3
cert_checked_3 3 4
cert_checked_3 4 5
cert_checked_3 5 6
cert_checked_3 6 7
cert_checked_3 7 8
cert_checked_3 8 9
cert_checked_3 9 10
cert_checked_3 10 11
cert_checked_3 11 12
cert_checked_3 12 13
cert_checked_3 13 14
cert_checked_3 14 15
cert_checked_3 15 16
cert_checked_3 16 17
cert_checked_3 17 18
cert_checked_3 18 19
cert_checked_3 19 20
cert_checked_3 20 21
cert_checked_3 21 22
cert_checked_3 22 23
cert_checked_3 23 24
cert_checked_3 24 25
cert_checked_3 25 26
cert_checked_3 26 27
cert_checked_3 27 28
cert_checked_3 28 29
cert_checked_3 29 30
cert_checked_3 30 31
cert_checked_3 31 32
cert_checked_3 32 33
cert_checked_3 33 34
cert_checked_3 34 35
cert_checked_3 35 36
cert_checked_3 36 37
cert_checked_3 37 38
cert_checked_3 38 39
cert_checked_3 39 40
cert_checked_3 40 41
cert_checked_3 41 42
cert_checked_3 42 43
cert_checked_3 43 44
cert_checked_3 44 45
cert_checked_3 45 46
cert_checked_3 46 47
cert_checked_3 47 48
cert_checked_3 48 49
cert_checked_3 49 50
cert_checked_3 50 51
cert_checked_3 51 52
cert_checked_3 52 53
cert_checked_3 53 54
cert_checked_3 54 55
cert_checked_3 55 56
cert_checked_3 56 57
cert_checked_3 57 58
cert_checked_3 58 59
cert_checked_3 59 60
cert_checked_3 60 61
cert_checked_3 61 62
cert_checked_3 62 63
cert_checked_3 63 64
cert_checked_3 64 65
cert_checked_3 65 66
cert_checked_3 66 67
cert_checked_3 67 68
cert_checked_3 68 69
cert_checked_3 69 70
cert_checked_3 70 71
cert_checked_3 71 72
cert_checked_3 72 73
cert_checked_3 73 74
cert_checked_3 74 75
cert_checked_3 75 76
cert_checked_3 76 77
cert_checked_3 77 78
cert_checked_3 78 79
cert_checked_3 79 80
cert_checked_3 80 81
cert_checked_3 81 82
cert_checked_3 82 83
cert_checked_3 83 84
cert_checked_3 84 85
cert_checked_3 85 86
cert_checked_3 86 87
cert_checked_3 87 88
cert_checked_3 88 89
cert_checked_3 89 90
cert_checked_3 90 91
cert_checked_3 91 92
cert_checked_3 92 93
cert_checked_3 93 94
cert_checked_3 94 95
cert_checked_3 95 96
cert_checked_3 96 97
cert_checked_3 97 98
cert_checked_3 98 99
cert_checked_3 99 100
cert_checked_3 100 101
cert_checked_3 101 102
cert_checked_3 102 103
cert_checked_3 103 104
cert_checked_3 104 105
cert_checked_3 105 106
cert_checked_3 106 107
cert_checked_3 107 108
cert_checked_3 108 109
cert_checked_3 109 110
cert_checked_3 110 111
cert_checked_3 111 112
cert_checked_3 112 113
cert_checked_3 113 114
cert_checked_3 114 115
cert_checked_3 115 116
cert_checked_3 116 117
cert_checked_3 117 118
cert_checked_3 118 119
cert_checked_3 119 120
cert_checked_3 120 121
cert_checked_3 121 122
cert_checked_3 122 123
cert_checked_3 123 124
cert_checked_3 124 125
cert_checked_3 125 126
cert_checked_3 126 127
cert_checked_3 127 128
theorem checked : Interval test 0 128 :=
  (interval_append test 0 64 128
  (interval_append test 0 32 64
  (interval_append test 0 16 32
  (interval_append test 0 8 16
  (interval_append test 0 4 8
  (interval_append test 0 2 4
  (interval_append test 0 1 2
  checked_0
  checked_1)
  (interval_append test 2 3 4
  checked_2
  checked_3))
  (interval_append test 4 6 8
  (interval_append test 4 5 6
  checked_4
  checked_5)
  (interval_append test 6 7 8
  checked_6
  checked_7)))
  (interval_append test 8 12 16
  (interval_append test 8 10 12
  (interval_append test 8 9 10
  checked_8
  checked_9)
  (interval_append test 10 11 12
  checked_10
  checked_11))
  (interval_append test 12 14 16
  (interval_append test 12 13 14
  checked_12
  checked_13)
  (interval_append test 14 15 16
  checked_14
  checked_15))))
  (interval_append test 16 24 32
  (interval_append test 16 20 24
  (interval_append test 16 18 20
  (interval_append test 16 17 18
  checked_16
  checked_17)
  (interval_append test 18 19 20
  checked_18
  checked_19))
  (interval_append test 20 22 24
  (interval_append test 20 21 22
  checked_20
  checked_21)
  (interval_append test 22 23 24
  checked_22
  checked_23)))
  (interval_append test 24 28 32
  (interval_append test 24 26 28
  (interval_append test 24 25 26
  checked_24
  checked_25)
  (interval_append test 26 27 28
  checked_26
  checked_27))
  (interval_append test 28 30 32
  (interval_append test 28 29 30
  checked_28
  checked_29)
  (interval_append test 30 31 32
  checked_30
  checked_31)))))
  (interval_append test 32 48 64
  (interval_append test 32 40 48
  (interval_append test 32 36 40
  (interval_append test 32 34 36
  (interval_append test 32 33 34
  checked_32
  checked_33)
  (interval_append test 34 35 36
  checked_34
  checked_35))
  (interval_append test 36 38 40
  (interval_append test 36 37 38
  checked_36
  checked_37)
  (interval_append test 38 39 40
  checked_38
  checked_39)))
  (interval_append test 40 44 48
  (interval_append test 40 42 44
  (interval_append test 40 41 42
  checked_40
  checked_41)
  (interval_append test 42 43 44
  checked_42
  checked_43))
  (interval_append test 44 46 48
  (interval_append test 44 45 46
  checked_44
  checked_45)
  (interval_append test 46 47 48
  checked_46
  checked_47))))
  (interval_append test 48 56 64
  (interval_append test 48 52 56
  (interval_append test 48 50 52
  (interval_append test 48 49 50
  checked_48
  checked_49)
  (interval_append test 50 51 52
  checked_50
  checked_51))
  (interval_append test 52 54 56
  (interval_append test 52 53 54
  checked_52
  checked_53)
  (interval_append test 54 55 56
  checked_54
  checked_55)))
  (interval_append test 56 60 64
  (interval_append test 56 58 60
  (interval_append test 56 57 58
  checked_56
  checked_57)
  (interval_append test 58 59 60
  checked_58
  checked_59))
  (interval_append test 60 62 64
  (interval_append test 60 61 62
  checked_60
  checked_61)
  (interval_append test 62 63 64
  checked_62
  checked_63))))))
  (interval_append test 64 96 128
  (interval_append test 64 80 96
  (interval_append test 64 72 80
  (interval_append test 64 68 72
  (interval_append test 64 66 68
  (interval_append test 64 65 66
  checked_64
  checked_65)
  (interval_append test 66 67 68
  checked_66
  checked_67))
  (interval_append test 68 70 72
  (interval_append test 68 69 70
  checked_68
  checked_69)
  (interval_append test 70 71 72
  checked_70
  checked_71)))
  (interval_append test 72 76 80
  (interval_append test 72 74 76
  (interval_append test 72 73 74
  checked_72
  checked_73)
  (interval_append test 74 75 76
  checked_74
  checked_75))
  (interval_append test 76 78 80
  (interval_append test 76 77 78
  checked_76
  checked_77)
  (interval_append test 78 79 80
  checked_78
  checked_79))))
  (interval_append test 80 88 96
  (interval_append test 80 84 88
  (interval_append test 80 82 84
  (interval_append test 80 81 82
  checked_80
  checked_81)
  (interval_append test 82 83 84
  checked_82
  checked_83))
  (interval_append test 84 86 88
  (interval_append test 84 85 86
  checked_84
  checked_85)
  (interval_append test 86 87 88
  checked_86
  checked_87)))
  (interval_append test 88 92 96
  (interval_append test 88 90 92
  (interval_append test 88 89 90
  checked_88
  checked_89)
  (interval_append test 90 91 92
  checked_90
  checked_91))
  (interval_append test 92 94 96
  (interval_append test 92 93 94
  checked_92
  checked_93)
  (interval_append test 94 95 96
  checked_94
  checked_95)))))
  (interval_append test 96 112 128
  (interval_append test 96 104 112
  (interval_append test 96 100 104
  (interval_append test 96 98 100
  (interval_append test 96 97 98
  checked_96
  checked_97)
  (interval_append test 98 99 100
  checked_98
  checked_99))
  (interval_append test 100 102 104
  (interval_append test 100 101 102
  checked_100
  checked_101)
  (interval_append test 102 103 104
  checked_102
  checked_103)))
  (interval_append test 104 108 112
  (interval_append test 104 106 108
  (interval_append test 104 105 106
  checked_104
  checked_105)
  (interval_append test 106 107 108
  checked_106
  checked_107))
  (interval_append test 108 110 112
  (interval_append test 108 109 110
  checked_108
  checked_109)
  (interval_append test 110 111 112
  checked_110
  checked_111))))
  (interval_append test 112 120 128
  (interval_append test 112 116 120
  (interval_append test 112 114 116
  (interval_append test 112 113 114
  checked_112
  checked_113)
  (interval_append test 114 115 116
  checked_114
  checked_115))
  (interval_append test 116 118 120
  (interval_append test 116 117 118
  checked_116
  checked_117)
  (interval_append test 118 119 120
  checked_118
  checked_119)))
  (interval_append test 120 124 128
  (interval_append test 120 122 124
  (interval_append test 120 121 122
  checked_120
  checked_121)
  (interval_append test 122 123 124
  checked_122
  checked_123))
  (interval_append test 124 126 128
  (interval_append test 124 125 126
  checked_124
  checked_125)
  (interval_append test 126 127 128
  checked_126
  checked_127)))))))
end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step12.Part000
