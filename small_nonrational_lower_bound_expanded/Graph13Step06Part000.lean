module
prelude
public meta import LowerSchemas.FiniteGraph
public meta import IntegerTables
public import GraphCatalogueData
public import Graph13Frames
public import Graph13Level06
public import Graph13Level07
public import FastGraphCatalogueCheck

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step06.Part000
open Papers.RationalityTen
open ConcreteGrowth GraphCatalogueCore GraphCatalogueCheck GraphCatalogueData FiniteChecks
cert_table_2 123
cert_lookup_5
cert_test 06 62 07
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
theorem checked : Interval test 0 62 :=
  (interval_append test 0 30 62
  (interval_append test 0 14 30
  (interval_append test 0 6 14
  (interval_append test 0 2 6
  checked_0
  (interval_append test 2 4 6
  checked_2
  checked_4))
  (interval_append test 6 10 14
  (interval_append test 6 8 10
  checked_6
  checked_8)
  (interval_append test 10 12 14
  checked_10
  checked_12)))
  (interval_append test 14 22 30
  (interval_append test 14 18 22
  (interval_append test 14 16 18
  checked_14
  checked_16)
  (interval_append test 18 20 22
  checked_18
  checked_20))
  (interval_append test 22 26 30
  (interval_append test 22 24 26
  checked_22
  checked_24)
  (interval_append test 26 28 30
  checked_26
  checked_28))))
  (interval_append test 30 46 62
  (interval_append test 30 38 46
  (interval_append test 30 34 38
  (interval_append test 30 32 34
  checked_30
  checked_32)
  (interval_append test 34 36 38
  checked_34
  checked_36))
  (interval_append test 38 42 46
  (interval_append test 38 40 42
  checked_38
  checked_40)
  (interval_append test 42 44 46
  checked_42
  checked_44)))
  (interval_append test 46 54 62
  (interval_append test 46 50 54
  (interval_append test 46 48 50
  checked_46
  checked_48)
  (interval_append test 50 52 54
  checked_50
  checked_52))
  (interval_append test 54 58 62
  (interval_append test 54 56 58
  checked_54
  checked_56)
  (interval_append test 58 60 62
  checked_58
  checked_60)))))
end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step06.Part000
