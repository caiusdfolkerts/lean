module

public meta import LowerSchemas.FinitePolygonN
public import PolygonN7ClassificationPart016

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

cert_terminal_data_join 03736 03796 3736 3796 3768 03768
cert_terminal_data_join 03680 03796 3680 3796 3736 03736
cert_terminal_data_join 03560 03796 3560 3796 3680 03680
cert_terminal_data_join 03320 03796 3320 3796 3560 03560
cert_terminal_data_join 02848 03796 2848 3796 3320 03320
cert_terminal_data_join 01896 03796 1896 3796 2848 02848
theorem terminal_data_join_00000_03796 : FiniteChecks.Interval terminalTest 0 3796 :=
  FiniteChecks.interval_append terminalTest 0 1896 3796 terminal_data_join_00000_01896 terminal_data_join_01896_03796


end Papers.RationalityTen.ConcretePolygonClassification.N7
