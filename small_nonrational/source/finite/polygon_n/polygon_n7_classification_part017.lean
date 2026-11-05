module

public import PolygonN7ClassificationPart016

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

theorem terminal_data_join_03736_03796 : FiniteChecks.Interval terminalTest 3736 3796 :=
  FiniteChecks.interval_append terminalTest 3736 3768 3796 terminal_data_join_03736_03768 terminal_data_join_03768_03796

theorem terminal_data_join_03680_03796 : FiniteChecks.Interval terminalTest 3680 3796 :=
  FiniteChecks.interval_append terminalTest 3680 3736 3796 terminal_data_join_03680_03736 terminal_data_join_03736_03796

theorem terminal_data_join_03560_03796 : FiniteChecks.Interval terminalTest 3560 3796 :=
  FiniteChecks.interval_append terminalTest 3560 3680 3796 terminal_data_join_03560_03680 terminal_data_join_03680_03796

theorem terminal_data_join_03320_03796 : FiniteChecks.Interval terminalTest 3320 3796 :=
  FiniteChecks.interval_append terminalTest 3320 3560 3796 terminal_data_join_03320_03560 terminal_data_join_03560_03796

theorem terminal_data_join_02848_03796 : FiniteChecks.Interval terminalTest 2848 3796 :=
  FiniteChecks.interval_append terminalTest 2848 3320 3796 terminal_data_join_02848_03320 terminal_data_join_03320_03796

theorem terminal_data_join_01896_03796 : FiniteChecks.Interval terminalTest 1896 3796 :=
  FiniteChecks.interval_append terminalTest 1896 2848 3796 terminal_data_join_01896_02848 terminal_data_join_02848_03796

theorem terminal_data_join_00000_03796 : FiniteChecks.Interval terminalTest 0 3796 :=
  FiniteChecks.interval_append terminalTest 0 1896 3796 terminal_data_join_00000_01896 terminal_data_join_01896_03796


end Papers.RationalityTen.ConcretePolygonClassification.N7
