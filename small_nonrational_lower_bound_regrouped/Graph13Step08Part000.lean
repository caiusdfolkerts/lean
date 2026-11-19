module
prelude
public meta import LowerSchemas.FiniteGraph
public meta import IntegerTables
public import GraphCatalogueData
public import Graph13Frames
public import Graph13Level08
public import Graph13Level09
public import FastGraphCatalogueCheck

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step08.Part000
open Papers.RationalityTen
open ConcreteGrowth GraphCatalogueCore GraphCatalogueCheck GraphCatalogueData FiniteChecks
cert_table_2 255
cert_lookup_5
cert_test 08 367 09
cert_checked 0 1 1
cert_checked 1 2 1
cert_checked 2 3 1
cert_checked 3 4 1
cert_checked 4 5 1
cert_checked 5 6 1
cert_checked 6 7 1
cert_checked 7 8 1
cert_checked 8 9 1
cert_checked 9 10 1
cert_checked 10 11 1
cert_checked 11 12 1
cert_checked 12 13 1
cert_checked 13 14 1
cert_checked 14 15 1
cert_checked 15 16 1
cert_checked 16 17 1
cert_checked 17 18 1
cert_checked 18 19 1
cert_checked 19 20 1
cert_checked 20 21 1
cert_checked 21 22 1
cert_checked 22 23 1
cert_checked 23 24 1
cert_checked 24 25 1
cert_checked 25 26 1
cert_checked 26 27 1
cert_checked 27 28 1
cert_checked 28 29 1
cert_checked 29 30 1
cert_checked 30 31 1
cert_checked 31 32 1
cert_checked 32 33 1
cert_checked 33 34 1
cert_checked 34 35 1
cert_checked 35 36 1
cert_checked 36 37 1
cert_checked 37 38 1
cert_checked 38 39 1
cert_checked 39 40 1
cert_checked 40 41 1
cert_checked 41 42 1
cert_checked 42 43 1
cert_checked 43 44 1
cert_checked 44 45 1
cert_checked 45 46 1
cert_checked 46 47 1
cert_checked 47 48 1
cert_checked 48 49 1
cert_checked 49 50 1
cert_checked 50 51 1
cert_checked 51 52 1
cert_checked 52 53 1
cert_checked 53 54 1
cert_checked 54 55 1
cert_checked 55 56 1
cert_checked 56 57 1
cert_checked 57 58 1
cert_checked 58 59 1
cert_checked 59 60 1
cert_checked 60 61 1
cert_checked 61 62 1
cert_checked 62 63 1
cert_checked 63 64 1
cert_checked 64 65 1
cert_checked 65 66 1
cert_checked 66 67 1
cert_checked 67 68 1
cert_checked 68 69 1
cert_checked 69 70 1
cert_checked 70 71 1
cert_checked 71 72 1
cert_checked 72 73 1
cert_checked 73 74 1
cert_checked 74 75 1
cert_checked 75 76 1
cert_checked 76 77 1
cert_checked 77 78 1
cert_checked 78 79 1
cert_checked 79 80 1
cert_checked 80 81 1
cert_checked 81 82 1
cert_checked 82 83 1
cert_checked 83 84 1
cert_checked 84 85 1
cert_checked 85 86 1
cert_checked 86 87 1
cert_checked 87 88 1
cert_checked 88 89 1
cert_checked 89 90 1
cert_checked 90 91 1
cert_checked 91 92 1
cert_checked 92 93 1
cert_checked 93 94 1
cert_checked 94 95 1
cert_checked 95 96 1
cert_checked 96 97 1
cert_checked 97 98 1
cert_checked 98 99 1
cert_checked 99 100 1
cert_checked 100 101 1
cert_checked 101 102 1
cert_checked 102 103 1
cert_checked 103 104 1
cert_checked 104 105 1
cert_checked 105 106 1
cert_checked 106 107 1
cert_checked 107 108 1
cert_checked 108 109 1
cert_checked 109 110 1
cert_checked 110 111 1
cert_checked 111 112 1
cert_checked 112 113 1
cert_checked 113 114 1
cert_checked 114 115 1
cert_checked 115 116 1
cert_checked 116 117 1
cert_checked 117 118 1
cert_checked 118 119 1
cert_checked 119 120 1
cert_checked 120 121 1
cert_checked 121 122 1
cert_checked 122 123 1
cert_checked 123 124 1
cert_checked 124 125 1
cert_checked 125 126 1
cert_checked 126 127 1
cert_checked 127 128 1
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
end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step08.Part000
