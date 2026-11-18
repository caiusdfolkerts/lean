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
theorem ridges_001_b128 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 128 132 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 128 4 (by decide +kernel)

theorem ridges_001_b132 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 132 136 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 132 4 (by decide +kernel)

theorem ridges_001_b136 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 136 140 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 136 4 (by decide +kernel)

theorem ridges_001_b140 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 140 144 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 140 4 (by decide +kernel)

theorem ridges_001_b144 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 144 148 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 144 4 (by decide +kernel)

theorem ridges_001_b148 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 148 152 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 148 4 (by decide +kernel)

theorem ridges_001_b152 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 152 156 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 152 4 (by decide +kernel)

theorem ridges_001_b156 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 156 160 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 156 4 (by decide +kernel)

theorem ridges_001_b160 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 160 164 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 160 4 (by decide +kernel)

theorem ridges_001_b164 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 164 168 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 164 4 (by decide +kernel)

theorem ridges_001_b168 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 168 172 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 168 4 (by decide +kernel)

theorem ridges_001_b172 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 172 176 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 172 4 (by decide +kernel)

theorem ridges_001_b176 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 176 180 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 176 4 (by decide +kernel)

theorem ridges_001_b180 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 180 184 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 180 4 (by decide +kernel)

theorem ridges_001_b184 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 184 188 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 184 4 (by decide +kernel)

theorem ridges_001_b188 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 188 192 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 188 4 (by decide +kernel)

theorem ridges_001_b192 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 192 196 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 192 4 (by decide +kernel)

theorem ridges_001_b196 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 196 200 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 196 4 (by decide +kernel)

theorem ridges_001_b200 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 200 204 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 200 4 (by decide +kernel)

theorem ridges_001_b204 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 204 208 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 204 4 (by decide +kernel)

theorem ridges_001_b208 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 208 212 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 208 4 (by decide +kernel)

theorem ridges_001_b212 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 212 216 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 212 4 (by decide +kernel)

theorem ridges_001_b216 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 216 220 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 216 4 (by decide +kernel)

theorem ridges_001_b220 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 220 224 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 220 4 (by decide +kernel)

theorem ridges_001_b224 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 224 228 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 224 4 (by decide +kernel)

theorem ridges_001_b228 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 228 232 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 228 4 (by decide +kernel)

theorem ridges_001_b232 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 232 236 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 232 4 (by decide +kernel)

theorem ridges_001_b236 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 236 240 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 236 4 (by decide +kernel)

theorem ridges_001_b240 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 240 244 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 240 4 (by decide +kernel)

theorem ridges_001_b244 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 244 248 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 244 4 (by decide +kernel)

theorem ridges_001_b248 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 248 252 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 248 4 (by decide +kernel)

theorem ridges_001_b252 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 252 256 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 252 4 (by decide +kernel)

theorem ridges_001 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 128 256 :=
  (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 128 192 256
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 128 160 192
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 128 144 160
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 128 136 144
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 128 132 136
 ridges_001_b128
 ridges_001_b132)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 136 140 144
 ridges_001_b136
 ridges_001_b140))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 144 152 160
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 144 148 152
 ridges_001_b144
 ridges_001_b148)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 152 156 160
 ridges_001_b152
 ridges_001_b156)))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 160 176 192
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 160 168 176
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 160 164 168
 ridges_001_b160
 ridges_001_b164)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 168 172 176
 ridges_001_b168
 ridges_001_b172))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 176 184 192
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 176 180 184
 ridges_001_b176
 ridges_001_b180)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 184 188 192
 ridges_001_b184
 ridges_001_b188))))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 192 224 256
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 192 208 224
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 192 200 208
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 192 196 200
 ridges_001_b192
 ridges_001_b196)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 200 204 208
 ridges_001_b200
 ridges_001_b204))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 208 216 224
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 208 212 216
 ridges_001_b208
 ridges_001_b212)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 216 220 224
 ridges_001_b216
 ridges_001_b220)))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 224 240 256
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 224 232 240
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 224 228 232
 ridges_001_b224
 ridges_001_b228)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 232 236 240
 ridges_001_b232
 ridges_001_b236))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 240 248 256
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 240 244 248
 ridges_001_b240
 ridges_001_b244)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 248 252 256
 ridges_001_b248
 ridges_001_b252)))))
end Papers.RationalityTen.SharedSmallGraph
