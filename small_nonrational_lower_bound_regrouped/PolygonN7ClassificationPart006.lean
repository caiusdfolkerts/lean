module

public meta import LowerSchemas.FinitePolygonN
public import PolygonN7ClassificationPart005

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

cert_terminal_data 01904 1904 1912 8
cert_terminal_data 01912 1912 1920 8
cert_terminal_data 01920 1920 1928 8
cert_terminal_data 01928 1928 1936 8
cert_terminal_data 01936 1936 1944 8
cert_terminal_data 01944 1944 1952 8
cert_terminal_data 01952 1952 1960 8
cert_terminal_data 01960 1960 1968 8
cert_terminal_data 01968 1968 1976 8
cert_terminal_data 01976 1976 1984 8
cert_terminal_data 01984 1984 1992 8
cert_terminal_data 01992 1992 2000 8
cert_terminal_data 02000 2000 2008 8
cert_terminal_data 02008 2008 2016 8
cert_terminal_data 02016 2016 2024 8
cert_terminal_data 02024 2024 2032 8
cert_terminal_data 02032 2032 2040 8
cert_terminal_data 02040 2040 2048 8
cert_terminal_data 02048 2048 2056 8
cert_terminal_data 02056 2056 2064 8
cert_terminal_data 02064 2064 2072 8
cert_terminal_data 02072 2072 2080 8
cert_terminal_data 02080 2080 2088 8
cert_terminal_data 02088 2088 2096 8
cert_terminal_data 02096 2096 2104 8
cert_terminal_data 02104 2104 2112 8
cert_terminal_data 02112 2112 2120 8
cert_terminal_data 02120 2120 2128 8
cert_terminal_data 02128 2128 2136 8
cert_terminal_data 02136 2136 2144 8
cert_terminal_data 02144 2144 2152 8
cert_terminal_data 02152 2152 2160 8
cert_terminal_data 02160 2160 2168 8
cert_terminal_data 02168 2168 2176 8
cert_terminal_data 02176 2176 2184 8
cert_terminal_data 02184 2184 2192 8
cert_terminal_data 02192 2192 2200 8
cert_terminal_data 02200 2200 2208 8
cert_terminal_data 02208 2208 2216 8
cert_terminal_data 02216 2216 2224 8
cert_terminal_data 02224 2224 2232 8
cert_terminal_data 02232 2232 2240 8
cert_terminal_data 02240 2240 2248 8
cert_terminal_data 02248 2248 2256 8
cert_terminal_data 02256 2256 2264 8
cert_terminal_data 02264 2264 2272 8
cert_terminal_data 02272 2272 2280 8
cert_terminal_data 02280 2280 2288 8
cert_terminal_data 02288 2288 2296 8
cert_terminal_data 02296 2296 2304 8
cert_terminal_data 02304 2304 2312 8
cert_terminal_data 02312 2312 2320 8
cert_terminal_data 02320 2320 2328 8
cert_terminal_data 02328 2328 2336 8
cert_terminal_data 02336 2336 2344 8
cert_terminal_data 02344 2344 2352 8
cert_terminal_data 02352 2352 2360 8
cert_terminal_data 02360 2360 2368 8
cert_terminal_data 02368 2368 2376 8
cert_terminal_data 02376 2376 2384 8
cert_terminal_data 02384 2384 2392 8
cert_terminal_data 02392 2392 2400 8
cert_terminal_data 02400 2400 2408 8
theorem terminal_data_02408 : FiniteChecks.Interval terminalTest 2408 2416 :=
  FiniteChecks.interval_of_check terminalTest 2408 8 (by decide +kernel)


end Papers.RationalityTen.ConcretePolygonClassification.N7
