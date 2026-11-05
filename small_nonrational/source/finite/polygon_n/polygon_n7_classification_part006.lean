module

public import PolygonN7ClassificationPart005

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

theorem terminal_data_01904 : FiniteChecks.Interval terminalTest 1904 1912 :=
  FiniteChecks.interval_of_check terminalTest 1904 8 (by decide +kernel)

theorem terminal_data_01912 : FiniteChecks.Interval terminalTest 1912 1920 :=
  FiniteChecks.interval_of_check terminalTest 1912 8 (by decide +kernel)

theorem terminal_data_01920 : FiniteChecks.Interval terminalTest 1920 1928 :=
  FiniteChecks.interval_of_check terminalTest 1920 8 (by decide +kernel)

theorem terminal_data_01928 : FiniteChecks.Interval terminalTest 1928 1936 :=
  FiniteChecks.interval_of_check terminalTest 1928 8 (by decide +kernel)

theorem terminal_data_01936 : FiniteChecks.Interval terminalTest 1936 1944 :=
  FiniteChecks.interval_of_check terminalTest 1936 8 (by decide +kernel)

theorem terminal_data_01944 : FiniteChecks.Interval terminalTest 1944 1952 :=
  FiniteChecks.interval_of_check terminalTest 1944 8 (by decide +kernel)

theorem terminal_data_01952 : FiniteChecks.Interval terminalTest 1952 1960 :=
  FiniteChecks.interval_of_check terminalTest 1952 8 (by decide +kernel)

theorem terminal_data_01960 : FiniteChecks.Interval terminalTest 1960 1968 :=
  FiniteChecks.interval_of_check terminalTest 1960 8 (by decide +kernel)

theorem terminal_data_01968 : FiniteChecks.Interval terminalTest 1968 1976 :=
  FiniteChecks.interval_of_check terminalTest 1968 8 (by decide +kernel)

theorem terminal_data_01976 : FiniteChecks.Interval terminalTest 1976 1984 :=
  FiniteChecks.interval_of_check terminalTest 1976 8 (by decide +kernel)

theorem terminal_data_01984 : FiniteChecks.Interval terminalTest 1984 1992 :=
  FiniteChecks.interval_of_check terminalTest 1984 8 (by decide +kernel)

theorem terminal_data_01992 : FiniteChecks.Interval terminalTest 1992 2000 :=
  FiniteChecks.interval_of_check terminalTest 1992 8 (by decide +kernel)

theorem terminal_data_02000 : FiniteChecks.Interval terminalTest 2000 2008 :=
  FiniteChecks.interval_of_check terminalTest 2000 8 (by decide +kernel)

theorem terminal_data_02008 : FiniteChecks.Interval terminalTest 2008 2016 :=
  FiniteChecks.interval_of_check terminalTest 2008 8 (by decide +kernel)

theorem terminal_data_02016 : FiniteChecks.Interval terminalTest 2016 2024 :=
  FiniteChecks.interval_of_check terminalTest 2016 8 (by decide +kernel)

theorem terminal_data_02024 : FiniteChecks.Interval terminalTest 2024 2032 :=
  FiniteChecks.interval_of_check terminalTest 2024 8 (by decide +kernel)

theorem terminal_data_02032 : FiniteChecks.Interval terminalTest 2032 2040 :=
  FiniteChecks.interval_of_check terminalTest 2032 8 (by decide +kernel)

theorem terminal_data_02040 : FiniteChecks.Interval terminalTest 2040 2048 :=
  FiniteChecks.interval_of_check terminalTest 2040 8 (by decide +kernel)

theorem terminal_data_02048 : FiniteChecks.Interval terminalTest 2048 2056 :=
  FiniteChecks.interval_of_check terminalTest 2048 8 (by decide +kernel)

theorem terminal_data_02056 : FiniteChecks.Interval terminalTest 2056 2064 :=
  FiniteChecks.interval_of_check terminalTest 2056 8 (by decide +kernel)

theorem terminal_data_02064 : FiniteChecks.Interval terminalTest 2064 2072 :=
  FiniteChecks.interval_of_check terminalTest 2064 8 (by decide +kernel)

theorem terminal_data_02072 : FiniteChecks.Interval terminalTest 2072 2080 :=
  FiniteChecks.interval_of_check terminalTest 2072 8 (by decide +kernel)

theorem terminal_data_02080 : FiniteChecks.Interval terminalTest 2080 2088 :=
  FiniteChecks.interval_of_check terminalTest 2080 8 (by decide +kernel)

theorem terminal_data_02088 : FiniteChecks.Interval terminalTest 2088 2096 :=
  FiniteChecks.interval_of_check terminalTest 2088 8 (by decide +kernel)

theorem terminal_data_02096 : FiniteChecks.Interval terminalTest 2096 2104 :=
  FiniteChecks.interval_of_check terminalTest 2096 8 (by decide +kernel)

theorem terminal_data_02104 : FiniteChecks.Interval terminalTest 2104 2112 :=
  FiniteChecks.interval_of_check terminalTest 2104 8 (by decide +kernel)

theorem terminal_data_02112 : FiniteChecks.Interval terminalTest 2112 2120 :=
  FiniteChecks.interval_of_check terminalTest 2112 8 (by decide +kernel)

theorem terminal_data_02120 : FiniteChecks.Interval terminalTest 2120 2128 :=
  FiniteChecks.interval_of_check terminalTest 2120 8 (by decide +kernel)

theorem terminal_data_02128 : FiniteChecks.Interval terminalTest 2128 2136 :=
  FiniteChecks.interval_of_check terminalTest 2128 8 (by decide +kernel)

theorem terminal_data_02136 : FiniteChecks.Interval terminalTest 2136 2144 :=
  FiniteChecks.interval_of_check terminalTest 2136 8 (by decide +kernel)

theorem terminal_data_02144 : FiniteChecks.Interval terminalTest 2144 2152 :=
  FiniteChecks.interval_of_check terminalTest 2144 8 (by decide +kernel)

theorem terminal_data_02152 : FiniteChecks.Interval terminalTest 2152 2160 :=
  FiniteChecks.interval_of_check terminalTest 2152 8 (by decide +kernel)

theorem terminal_data_02160 : FiniteChecks.Interval terminalTest 2160 2168 :=
  FiniteChecks.interval_of_check terminalTest 2160 8 (by decide +kernel)

theorem terminal_data_02168 : FiniteChecks.Interval terminalTest 2168 2176 :=
  FiniteChecks.interval_of_check terminalTest 2168 8 (by decide +kernel)

theorem terminal_data_02176 : FiniteChecks.Interval terminalTest 2176 2184 :=
  FiniteChecks.interval_of_check terminalTest 2176 8 (by decide +kernel)

theorem terminal_data_02184 : FiniteChecks.Interval terminalTest 2184 2192 :=
  FiniteChecks.interval_of_check terminalTest 2184 8 (by decide +kernel)

theorem terminal_data_02192 : FiniteChecks.Interval terminalTest 2192 2200 :=
  FiniteChecks.interval_of_check terminalTest 2192 8 (by decide +kernel)

theorem terminal_data_02200 : FiniteChecks.Interval terminalTest 2200 2208 :=
  FiniteChecks.interval_of_check terminalTest 2200 8 (by decide +kernel)

theorem terminal_data_02208 : FiniteChecks.Interval terminalTest 2208 2216 :=
  FiniteChecks.interval_of_check terminalTest 2208 8 (by decide +kernel)

theorem terminal_data_02216 : FiniteChecks.Interval terminalTest 2216 2224 :=
  FiniteChecks.interval_of_check terminalTest 2216 8 (by decide +kernel)

theorem terminal_data_02224 : FiniteChecks.Interval terminalTest 2224 2232 :=
  FiniteChecks.interval_of_check terminalTest 2224 8 (by decide +kernel)

theorem terminal_data_02232 : FiniteChecks.Interval terminalTest 2232 2240 :=
  FiniteChecks.interval_of_check terminalTest 2232 8 (by decide +kernel)

theorem terminal_data_02240 : FiniteChecks.Interval terminalTest 2240 2248 :=
  FiniteChecks.interval_of_check terminalTest 2240 8 (by decide +kernel)

theorem terminal_data_02248 : FiniteChecks.Interval terminalTest 2248 2256 :=
  FiniteChecks.interval_of_check terminalTest 2248 8 (by decide +kernel)

theorem terminal_data_02256 : FiniteChecks.Interval terminalTest 2256 2264 :=
  FiniteChecks.interval_of_check terminalTest 2256 8 (by decide +kernel)

theorem terminal_data_02264 : FiniteChecks.Interval terminalTest 2264 2272 :=
  FiniteChecks.interval_of_check terminalTest 2264 8 (by decide +kernel)

theorem terminal_data_02272 : FiniteChecks.Interval terminalTest 2272 2280 :=
  FiniteChecks.interval_of_check terminalTest 2272 8 (by decide +kernel)

theorem terminal_data_02280 : FiniteChecks.Interval terminalTest 2280 2288 :=
  FiniteChecks.interval_of_check terminalTest 2280 8 (by decide +kernel)

theorem terminal_data_02288 : FiniteChecks.Interval terminalTest 2288 2296 :=
  FiniteChecks.interval_of_check terminalTest 2288 8 (by decide +kernel)

theorem terminal_data_02296 : FiniteChecks.Interval terminalTest 2296 2304 :=
  FiniteChecks.interval_of_check terminalTest 2296 8 (by decide +kernel)

theorem terminal_data_02304 : FiniteChecks.Interval terminalTest 2304 2312 :=
  FiniteChecks.interval_of_check terminalTest 2304 8 (by decide +kernel)

theorem terminal_data_02312 : FiniteChecks.Interval terminalTest 2312 2320 :=
  FiniteChecks.interval_of_check terminalTest 2312 8 (by decide +kernel)

theorem terminal_data_02320 : FiniteChecks.Interval terminalTest 2320 2328 :=
  FiniteChecks.interval_of_check terminalTest 2320 8 (by decide +kernel)

theorem terminal_data_02328 : FiniteChecks.Interval terminalTest 2328 2336 :=
  FiniteChecks.interval_of_check terminalTest 2328 8 (by decide +kernel)

theorem terminal_data_02336 : FiniteChecks.Interval terminalTest 2336 2344 :=
  FiniteChecks.interval_of_check terminalTest 2336 8 (by decide +kernel)

theorem terminal_data_02344 : FiniteChecks.Interval terminalTest 2344 2352 :=
  FiniteChecks.interval_of_check terminalTest 2344 8 (by decide +kernel)

theorem terminal_data_02352 : FiniteChecks.Interval terminalTest 2352 2360 :=
  FiniteChecks.interval_of_check terminalTest 2352 8 (by decide +kernel)

theorem terminal_data_02360 : FiniteChecks.Interval terminalTest 2360 2368 :=
  FiniteChecks.interval_of_check terminalTest 2360 8 (by decide +kernel)

theorem terminal_data_02368 : FiniteChecks.Interval terminalTest 2368 2376 :=
  FiniteChecks.interval_of_check terminalTest 2368 8 (by decide +kernel)

theorem terminal_data_02376 : FiniteChecks.Interval terminalTest 2376 2384 :=
  FiniteChecks.interval_of_check terminalTest 2376 8 (by decide +kernel)

theorem terminal_data_02384 : FiniteChecks.Interval terminalTest 2384 2392 :=
  FiniteChecks.interval_of_check terminalTest 2384 8 (by decide +kernel)

theorem terminal_data_02392 : FiniteChecks.Interval terminalTest 2392 2400 :=
  FiniteChecks.interval_of_check terminalTest 2392 8 (by decide +kernel)

theorem terminal_data_02400 : FiniteChecks.Interval terminalTest 2400 2408 :=
  FiniteChecks.interval_of_check terminalTest 2400 8 (by decide +kernel)

theorem terminal_data_02408 : FiniteChecks.Interval terminalTest 2408 2416 :=
  FiniteChecks.interval_of_check terminalTest 2408 8 (by decide +kernel)


end Papers.RationalityTen.ConcretePolygonClassification.N7
