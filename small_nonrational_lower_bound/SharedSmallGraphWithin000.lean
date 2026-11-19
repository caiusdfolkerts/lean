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
theorem within_000_b0 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 0 8 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 0 8 (by decide +kernel)

theorem within_000_b8 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 8 16 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 8 8 (by decide +kernel)

theorem within_000_b16 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 16 24 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 16 8 (by decide +kernel)

theorem within_000_b24 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 24 32 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 24 8 (by decide +kernel)

theorem within_000_b32 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 32 40 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 32 8 (by decide +kernel)

theorem within_000_b40 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 40 48 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 40 8 (by decide +kernel)

theorem within_000_b48 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 48 56 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 48 8 (by decide +kernel)

theorem within_000_b56 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 56 64 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 56 8 (by decide +kernel)

theorem within_000_b64 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 64 72 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 64 8 (by decide +kernel)

theorem within_000_b72 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 72 80 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 72 8 (by decide +kernel)

theorem within_000_b80 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 80 88 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 80 8 (by decide +kernel)

theorem within_000_b88 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 88 96 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 88 8 (by decide +kernel)

theorem within_000_b96 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 96 104 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 96 8 (by decide +kernel)

theorem within_000_b104 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 104 112 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 104 8 (by decide +kernel)

theorem within_000_b112 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 112 120 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 112 8 (by decide +kernel)

theorem within_000_b120 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 120 128 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 120 8 (by decide +kernel)

theorem within_000_b128 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 128 136 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 128 8 (by decide +kernel)

theorem within_000_b136 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 136 144 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 136 8 (by decide +kernel)

theorem within_000_b144 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 144 152 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 144 8 (by decide +kernel)

theorem within_000_b152 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 152 160 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 152 8 (by decide +kernel)

theorem within_000_b160 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 160 168 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 160 8 (by decide +kernel)

theorem within_000_b168 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 168 176 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 168 8 (by decide +kernel)

theorem within_000_b176 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 176 184 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 176 8 (by decide +kernel)

theorem within_000_b184 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 184 192 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 184 8 (by decide +kernel)

theorem within_000_b192 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 192 200 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 192 8 (by decide +kernel)

theorem within_000_b200 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 200 208 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 200 8 (by decide +kernel)

theorem within_000_b208 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 208 216 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 208 8 (by decide +kernel)

theorem within_000_b216 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 216 224 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 216 8 (by decide +kernel)

theorem within_000_b224 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 224 232 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 224 8 (by decide +kernel)

theorem within_000_b232 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 232 240 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 232 8 (by decide +kernel)

theorem within_000_b240 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 240 248 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 240 8 (by decide +kernel)

theorem within_000_b248 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 248 256 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 248 8 (by decide +kernel)

theorem within_000 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 0 256 :=
  (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 0 128 256
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 0 64 128
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 0 32 64
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 0 16 32
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 0 8 16
 within_000_b0
 within_000_b8)
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 16 24 32
 within_000_b16
 within_000_b24))
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 32 48 64
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 32 40 48
 within_000_b32
 within_000_b40)
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 48 56 64
 within_000_b48
 within_000_b56)))
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 64 96 128
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 64 80 96
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 64 72 80
 within_000_b64
 within_000_b72)
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 80 88 96
 within_000_b80
 within_000_b88))
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 96 112 128
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 96 104 112
 within_000_b96
 within_000_b104)
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 112 120 128
 within_000_b112
 within_000_b120))))
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 128 192 256
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 128 160 192
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 128 144 160
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 128 136 144
 within_000_b128
 within_000_b136)
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 144 152 160
 within_000_b144
 within_000_b152))
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 160 176 192
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 160 168 176
 within_000_b160
 within_000_b168)
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 176 184 192
 within_000_b176
 within_000_b184)))
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 192 224 256
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 192 208 224
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 192 200 208
 within_000_b192
 within_000_b200)
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 208 216 224
 within_000_b208
 within_000_b216))
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 224 240 256
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 224 232 240
 within_000_b224
 within_000_b232)
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 240 248 256
 within_000_b240
 within_000_b248)))))
end Papers.RationalityTen.SharedSmallGraph
