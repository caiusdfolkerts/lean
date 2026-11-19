module
prelude
public meta import LowerSchemas.FiniteGraph
public meta import IntegerTables
public import GraphCatalogueData
public import Graph13Frames
public import Graph13Level05
public import Graph13Level06
public import FastGraphCatalogueCheck

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step05.Part000
open Papers.RationalityTen
open ConcreteGrowth GraphCatalogueCore GraphCatalogueCheck GraphCatalogueData FiniteChecks
cert_table_2 49
cert_lookup_5
cert_test 05 25 06
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
cert_checked 24 25 1
theorem checked : Interval test 0 25 :=
  (interval_append test 0 12 25
  (interval_append test 0 6 12
  (interval_append test 0 2 6
  checked_0
  (interval_append test 2 4 6
  checked_2
  checked_4))
  (interval_append test 6 8 12
  checked_6
  (interval_append test 8 10 12
  checked_8
  checked_10)))
  (interval_append test 12 18 25
  (interval_append test 12 14 18
  checked_12
  (interval_append test 14 16 18
  checked_14
  checked_16))
  (interval_append test 18 22 25
  (interval_append test 18 20 22
  checked_18
  checked_20)
  (interval_append test 22 24 25
  checked_22
  checked_24))))
end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step05.Part000
