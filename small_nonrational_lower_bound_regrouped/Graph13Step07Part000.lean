module
prelude
public meta import LowerSchemas.FiniteGraph
public meta import IntegerTables
public import GraphCatalogueData
public import Graph13Frames
public import Graph13Level07
public import Graph13Level08
public import FastGraphCatalogueCheck

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step07.Part000
open Papers.RationalityTen
open ConcreteGrowth GraphCatalogueCore GraphCatalogueCheck GraphCatalogueData FiniteChecks
cert_table_2 297
cert_lookup_5
cert_test 07 149 08
cert_checked 0 2 2
cert_checked 2 4 2
cert_checked 4 6 2
cert_checked 6 8 2
cert_checked 8 10 2
cert_checked 10 12 2
cert_checked 12 14 2
cert_checked 14 16 2
cert_checked 16 18 2
cert_checked 18 20 2
cert_checked 20 22 2
cert_checked 22 24 2
cert_checked 24 26 2
cert_checked 26 28 2
cert_checked 28 30 2
cert_checked 30 32 2
cert_checked 32 34 2
cert_checked 34 36 2
cert_checked 36 38 2
cert_checked 38 40 2
cert_checked 40 42 2
cert_checked 42 44 2
cert_checked 44 46 2
cert_checked 46 48 2
cert_checked 48 50 2
cert_checked 50 52 2
cert_checked 52 54 2
cert_checked 54 56 2
cert_checked 56 58 2
cert_checked 58 60 2
cert_checked 60 62 2
cert_checked 62 64 2
cert_checked 64 66 2
cert_checked 66 68 2
cert_checked 68 70 2
cert_checked 70 72 2
cert_checked 72 74 2
cert_checked 74 76 2
cert_checked 76 78 2
cert_checked 78 80 2
cert_checked 80 82 2
cert_checked 82 84 2
cert_checked 84 86 2
cert_checked 86 88 2
cert_checked 88 90 2
cert_checked 90 92 2
cert_checked 92 94 2
cert_checked 94 96 2
cert_checked 96 98 2
cert_checked 98 100 2
cert_checked 100 102 2
cert_checked 102 104 2
cert_checked 104 106 2
cert_checked 106 108 2
cert_checked 108 110 2
cert_checked 110 112 2
cert_checked 112 114 2
cert_checked 114 116 2
cert_checked 116 118 2
cert_checked 118 120 2
cert_checked 120 122 2
cert_checked 122 124 2
cert_checked 124 126 2
cert_checked 126 128 2
cert_checked 128 130 2
cert_checked 130 132 2
cert_checked 132 134 2
cert_checked 134 136 2
cert_checked 136 138 2
cert_checked 138 140 2
cert_checked 140 142 2
cert_checked 142 144 2
cert_checked 144 146 2
cert_checked 146 148 2
cert_checked 148 149 1
theorem checked : Interval test 0 149 :=
  (interval_append test 0 74 149
  (interval_append test 0 36 74
  (interval_append test 0 18 36
  (interval_append test 0 8 18
  (interval_append test 0 4 8
  (interval_append test 0 2 4
  checked_0
  checked_2)
  (interval_append test 4 6 8
  checked_4
  checked_6))
  (interval_append test 8 12 18
  (interval_append test 8 10 12
  checked_8
  checked_10)
  (interval_append test 12 14 18
  checked_12
  (interval_append test 14 16 18
  checked_14
  checked_16))))
  (interval_append test 18 26 36
  (interval_append test 18 22 26
  (interval_append test 18 20 22
  checked_18
  checked_20)
  (interval_append test 22 24 26
  checked_22
  checked_24))
  (interval_append test 26 30 36
  (interval_append test 26 28 30
  checked_26
  checked_28)
  (interval_append test 30 32 36
  checked_30
  (interval_append test 32 34 36
  checked_32
  checked_34)))))
  (interval_append test 36 54 74
  (interval_append test 36 44 54
  (interval_append test 36 40 44
  (interval_append test 36 38 40
  checked_36
  checked_38)
  (interval_append test 40 42 44
  checked_40
  checked_42))
  (interval_append test 44 48 54
  (interval_append test 44 46 48
  checked_44
  checked_46)
  (interval_append test 48 50 54
  checked_48
  (interval_append test 50 52 54
  checked_50
  checked_52))))
  (interval_append test 54 64 74
  (interval_append test 54 58 64
  (interval_append test 54 56 58
  checked_54
  checked_56)
  (interval_append test 58 60 64
  checked_58
  (interval_append test 60 62 64
  checked_60
  checked_62)))
  (interval_append test 64 68 74
  (interval_append test 64 66 68
  checked_64
  checked_66)
  (interval_append test 68 70 74
  checked_68
  (interval_append test 70 72 74
  checked_70
  checked_72))))))
  (interval_append test 74 112 149
  (interval_append test 74 92 112
  (interval_append test 74 82 92
  (interval_append test 74 78 82
  (interval_append test 74 76 78
  checked_74
  checked_76)
  (interval_append test 78 80 82
  checked_78
  checked_80))
  (interval_append test 82 86 92
  (interval_append test 82 84 86
  checked_82
  checked_84)
  (interval_append test 86 88 92
  checked_86
  (interval_append test 88 90 92
  checked_88
  checked_90))))
  (interval_append test 92 102 112
  (interval_append test 92 96 102
  (interval_append test 92 94 96
  checked_92
  checked_94)
  (interval_append test 96 98 102
  checked_96
  (interval_append test 98 100 102
  checked_98
  checked_100)))
  (interval_append test 102 106 112
  (interval_append test 102 104 106
  checked_102
  checked_104)
  (interval_append test 106 108 112
  checked_106
  (interval_append test 108 110 112
  checked_108
  checked_110)))))
  (interval_append test 112 130 149
  (interval_append test 112 120 130
  (interval_append test 112 116 120
  (interval_append test 112 114 116
  checked_112
  checked_114)
  (interval_append test 116 118 120
  checked_116
  checked_118))
  (interval_append test 120 124 130
  (interval_append test 120 122 124
  checked_120
  checked_122)
  (interval_append test 124 126 130
  checked_124
  (interval_append test 126 128 130
  checked_126
  checked_128))))
  (interval_append test 130 140 149
  (interval_append test 130 134 140
  (interval_append test 130 132 134
  checked_130
  checked_132)
  (interval_append test 134 136 140
  checked_134
  (interval_append test 136 138 140
  checked_136
  checked_138)))
  (interval_append test 140 144 149
  (interval_append test 140 142 144
  checked_140
  checked_142)
  (interval_append test 144 146 149
  checked_144
  (interval_append test 146 148 149
  checked_146
  checked_148)))))))
end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step07.Part000
