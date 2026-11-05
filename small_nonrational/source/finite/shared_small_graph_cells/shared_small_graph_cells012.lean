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
theorem cells_012_b3072 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3072 3080 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3072 8 (by decide +kernel)

theorem cells_012_b3080 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3080 3088 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3080 8 (by decide +kernel)

theorem cells_012_b3088 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3088 3096 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3088 8 (by decide +kernel)

theorem cells_012_b3096 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3096 3104 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3096 8 (by decide +kernel)

theorem cells_012_b3104 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3104 3112 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3104 8 (by decide +kernel)

theorem cells_012_b3112 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3112 3120 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3112 8 (by decide +kernel)

theorem cells_012_b3120 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3120 3128 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3120 8 (by decide +kernel)

theorem cells_012_b3128 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3128 3136 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3128 8 (by decide +kernel)

theorem cells_012_b3136 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3136 3144 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3136 8 (by decide +kernel)

theorem cells_012_b3144 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3144 3152 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3144 8 (by decide +kernel)

theorem cells_012_b3152 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3152 3160 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3152 8 (by decide +kernel)

theorem cells_012_b3160 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3160 3168 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3160 8 (by decide +kernel)

theorem cells_012_b3168 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3168 3176 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3168 8 (by decide +kernel)

theorem cells_012_b3176 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3176 3184 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3176 8 (by decide +kernel)

theorem cells_012_b3184 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3184 3192 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3184 8 (by decide +kernel)

theorem cells_012_b3192 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3192 3200 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3192 8 (by decide +kernel)

theorem cells_012_b3200 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3200 3208 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3200 8 (by decide +kernel)

theorem cells_012_b3208 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3208 3216 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3208 8 (by decide +kernel)

theorem cells_012_b3216 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3216 3224 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3216 8 (by decide +kernel)

theorem cells_012_b3224 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3224 3232 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3224 8 (by decide +kernel)

theorem cells_012_b3232 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3232 3240 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3232 8 (by decide +kernel)

theorem cells_012_b3240 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3240 3248 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3240 8 (by decide +kernel)

theorem cells_012_b3248 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3248 3256 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3248 8 (by decide +kernel)

theorem cells_012_b3256 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3256 3264 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3256 8 (by decide +kernel)

theorem cells_012_b3264 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3264 3272 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3264 8 (by decide +kernel)

theorem cells_012_b3272 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3272 3280 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3272 8 (by decide +kernel)

theorem cells_012_b3280 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3280 3288 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3280 8 (by decide +kernel)

theorem cells_012_b3288 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3288 3296 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3288 8 (by decide +kernel)

theorem cells_012_b3296 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3296 3304 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3296 8 (by decide +kernel)

theorem cells_012_b3304 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3304 3312 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3304 8 (by decide +kernel)

theorem cells_012_b3312 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3312 3320 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3312 8 (by decide +kernel)

theorem cells_012_b3320 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3320 3328 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3320 8 (by decide +kernel)

theorem cells_012 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3072 3328 :=
  (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3072 3200 3328
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3072 3136 3200
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3072 3104 3136
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3072 3088 3104
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3072 3080 3088
 cells_012_b3072
 cells_012_b3080)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3088 3096 3104
 cells_012_b3088
 cells_012_b3096))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3104 3120 3136
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3104 3112 3120
 cells_012_b3104
 cells_012_b3112)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3120 3128 3136
 cells_012_b3120
 cells_012_b3128)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3136 3168 3200
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3136 3152 3168
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3136 3144 3152
 cells_012_b3136
 cells_012_b3144)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3152 3160 3168
 cells_012_b3152
 cells_012_b3160))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3168 3184 3200
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3168 3176 3184
 cells_012_b3168
 cells_012_b3176)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3184 3192 3200
 cells_012_b3184
 cells_012_b3192))))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3200 3264 3328
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3200 3232 3264
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3200 3216 3232
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3200 3208 3216
 cells_012_b3200
 cells_012_b3208)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3216 3224 3232
 cells_012_b3216
 cells_012_b3224))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3232 3248 3264
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3232 3240 3248
 cells_012_b3232
 cells_012_b3240)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3248 3256 3264
 cells_012_b3248
 cells_012_b3256)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3264 3296 3328
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3264 3280 3296
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3264 3272 3280
 cells_012_b3264
 cells_012_b3272)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3280 3288 3296
 cells_012_b3280
 cells_012_b3288))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3296 3312 3328
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3296 3304 3312
 cells_012_b3296
 cells_012_b3304)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3312 3320 3328
 cells_012_b3312
 cells_012_b3320)))))
end Papers.RationalityTen.SharedSmallGraph
