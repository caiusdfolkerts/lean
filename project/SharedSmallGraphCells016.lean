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
theorem cells_016_b4096 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4096 4104 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4096 8 (by decide +kernel)

theorem cells_016_b4104 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4104 4112 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4104 8 (by decide +kernel)

theorem cells_016_b4112 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4112 4120 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4112 8 (by decide +kernel)

theorem cells_016_b4120 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4120 4128 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4120 8 (by decide +kernel)

theorem cells_016_b4128 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4128 4136 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4128 8 (by decide +kernel)

theorem cells_016_b4136 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4136 4144 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4136 8 (by decide +kernel)

theorem cells_016_b4144 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4144 4152 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4144 8 (by decide +kernel)

theorem cells_016_b4152 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4152 4160 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4152 8 (by decide +kernel)

theorem cells_016_b4160 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4160 4168 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4160 8 (by decide +kernel)

theorem cells_016_b4168 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4168 4176 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4168 8 (by decide +kernel)

theorem cells_016_b4176 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4176 4184 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4176 8 (by decide +kernel)

theorem cells_016_b4184 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4184 4192 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4184 8 (by decide +kernel)

theorem cells_016_b4192 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4192 4200 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4192 8 (by decide +kernel)

theorem cells_016_b4200 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4200 4208 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4200 8 (by decide +kernel)

theorem cells_016_b4208 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4208 4216 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4208 8 (by decide +kernel)

theorem cells_016_b4216 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4216 4224 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4216 8 (by decide +kernel)

theorem cells_016_b4224 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4224 4232 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4224 8 (by decide +kernel)

theorem cells_016_b4232 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4232 4240 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4232 8 (by decide +kernel)

theorem cells_016_b4240 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4240 4248 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4240 8 (by decide +kernel)

theorem cells_016_b4248 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4248 4256 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4248 8 (by decide +kernel)

theorem cells_016_b4256 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4256 4264 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4256 8 (by decide +kernel)

theorem cells_016_b4264 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4264 4272 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4264 8 (by decide +kernel)

theorem cells_016_b4272 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4272 4280 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4272 8 (by decide +kernel)

theorem cells_016_b4280 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4280 4288 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4280 8 (by decide +kernel)

theorem cells_016_b4288 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4288 4296 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4288 8 (by decide +kernel)

theorem cells_016_b4296 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4296 4304 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4296 8 (by decide +kernel)

theorem cells_016_b4304 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4304 4312 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4304 8 (by decide +kernel)

theorem cells_016_b4312 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4312 4320 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4312 8 (by decide +kernel)

theorem cells_016_b4320 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4320 4328 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4320 8 (by decide +kernel)

theorem cells_016_b4328 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4328 4336 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4328 8 (by decide +kernel)

theorem cells_016_b4336 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4336 4344 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4336 8 (by decide +kernel)

theorem cells_016_b4344 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4344 4352 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4344 8 (by decide +kernel)

theorem cells_016 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4096 4352 :=
  (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4096 4224 4352
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4096 4160 4224
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4096 4128 4160
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4096 4112 4128
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4096 4104 4112
 cells_016_b4096
 cells_016_b4104)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4112 4120 4128
 cells_016_b4112
 cells_016_b4120))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4128 4144 4160
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4128 4136 4144
 cells_016_b4128
 cells_016_b4136)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4144 4152 4160
 cells_016_b4144
 cells_016_b4152)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4160 4192 4224
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4160 4176 4192
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4160 4168 4176
 cells_016_b4160
 cells_016_b4168)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4176 4184 4192
 cells_016_b4176
 cells_016_b4184))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4192 4208 4224
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4192 4200 4208
 cells_016_b4192
 cells_016_b4200)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4208 4216 4224
 cells_016_b4208
 cells_016_b4216))))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4224 4288 4352
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4224 4256 4288
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4224 4240 4256
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4224 4232 4240
 cells_016_b4224
 cells_016_b4232)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4240 4248 4256
 cells_016_b4240
 cells_016_b4248))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4256 4272 4288
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4256 4264 4272
 cells_016_b4256
 cells_016_b4264)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4272 4280 4288
 cells_016_b4272
 cells_016_b4280)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4288 4320 4352
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4288 4304 4320
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4288 4296 4304
 cells_016_b4288
 cells_016_b4296)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4304 4312 4320
 cells_016_b4304
 cells_016_b4312))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4320 4336 4352
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4320 4328 4336
 cells_016_b4320
 cells_016_b4328)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4336 4344 4352
 cells_016_b4336
 cells_016_b4344)))))
end Papers.RationalityTen.SharedSmallGraph
