module
prelude
public import SharedSmallGraphData

@[expose] public section
namespace Papers.RationalityTen.SharedSmallGraph
open Papers.RationalityTen
open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming GrowthBitsets
open BatchedGrowthPruning GraphGrowthConstraints FiniteChecks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem cells_008_b2048 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2048 2056 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2048 8 (by decide +kernel)

theorem cells_008_b2056 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2056 2064 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2056 8 (by decide +kernel)

theorem cells_008_b2064 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2064 2072 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2064 8 (by decide +kernel)

theorem cells_008_b2072 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2072 2080 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2072 8 (by decide +kernel)

theorem cells_008_b2080 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2080 2088 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2080 8 (by decide +kernel)

theorem cells_008_b2088 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2088 2096 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2088 8 (by decide +kernel)

theorem cells_008_b2096 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2096 2104 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2096 8 (by decide +kernel)

theorem cells_008_b2104 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2104 2112 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2104 8 (by decide +kernel)

theorem cells_008_b2112 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2112 2120 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2112 8 (by decide +kernel)

theorem cells_008_b2120 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2120 2128 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2120 8 (by decide +kernel)

theorem cells_008_b2128 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2128 2136 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2128 8 (by decide +kernel)

theorem cells_008_b2136 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2136 2144 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2136 8 (by decide +kernel)

theorem cells_008_b2144 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2144 2152 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2144 8 (by decide +kernel)

theorem cells_008_b2152 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2152 2160 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2152 8 (by decide +kernel)

theorem cells_008_b2160 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2160 2168 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2160 8 (by decide +kernel)

theorem cells_008_b2168 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2168 2176 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2168 8 (by decide +kernel)

theorem cells_008_b2176 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2176 2184 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2176 8 (by decide +kernel)

theorem cells_008_b2184 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2184 2192 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2184 8 (by decide +kernel)

theorem cells_008_b2192 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2192 2200 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2192 8 (by decide +kernel)

theorem cells_008_b2200 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2200 2208 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2200 8 (by decide +kernel)

theorem cells_008_b2208 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2208 2216 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2208 8 (by decide +kernel)

theorem cells_008_b2216 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2216 2224 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2216 8 (by decide +kernel)

theorem cells_008_b2224 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2224 2232 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2224 8 (by decide +kernel)

theorem cells_008_b2232 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2232 2240 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2232 8 (by decide +kernel)

theorem cells_008_b2240 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2240 2248 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2240 8 (by decide +kernel)

theorem cells_008_b2248 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2248 2256 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2248 8 (by decide +kernel)

theorem cells_008_b2256 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2256 2264 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2256 8 (by decide +kernel)

theorem cells_008_b2264 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2264 2272 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2264 8 (by decide +kernel)

theorem cells_008_b2272 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2272 2280 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2272 8 (by decide +kernel)

theorem cells_008_b2280 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2280 2288 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2280 8 (by decide +kernel)

theorem cells_008_b2288 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2288 2296 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2288 8 (by decide +kernel)

theorem cells_008_b2296 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2296 2304 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2296 8 (by decide +kernel)

theorem cells_008 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2048 2304 :=
  (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2048 2176 2304
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2048 2112 2176
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2048 2080 2112
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2048 2064 2080
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2048 2056 2064
 cells_008_b2048
 cells_008_b2056)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2064 2072 2080
 cells_008_b2064
 cells_008_b2072))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2080 2096 2112
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2080 2088 2096
 cells_008_b2080
 cells_008_b2088)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2096 2104 2112
 cells_008_b2096
 cells_008_b2104)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2112 2144 2176
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2112 2128 2144
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2112 2120 2128
 cells_008_b2112
 cells_008_b2120)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2128 2136 2144
 cells_008_b2128
 cells_008_b2136))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2144 2160 2176
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2144 2152 2160
 cells_008_b2144
 cells_008_b2152)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2160 2168 2176
 cells_008_b2160
 cells_008_b2168))))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2176 2240 2304
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2176 2208 2240
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2176 2192 2208
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2176 2184 2192
 cells_008_b2176
 cells_008_b2184)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2192 2200 2208
 cells_008_b2192
 cells_008_b2200))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2208 2224 2240
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2208 2216 2224
 cells_008_b2208
 cells_008_b2216)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2224 2232 2240
 cells_008_b2224
 cells_008_b2232)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2240 2272 2304
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2240 2256 2272
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2240 2248 2256
 cells_008_b2240
 cells_008_b2248)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2256 2264 2272
 cells_008_b2256
 cells_008_b2264))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2272 2288 2304
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2272 2280 2288
 cells_008_b2272
 cells_008_b2280)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2288 2296 2304
 cells_008_b2288
 cells_008_b2296)))))
end Papers.RationalityTen.SharedSmallGraph
