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
theorem ridges_002_b256 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 256 260 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 256 4 (by decide +kernel)

theorem ridges_002_b260 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 260 264 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 260 4 (by decide +kernel)

theorem ridges_002_b264 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 264 268 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 264 4 (by decide +kernel)

theorem ridges_002_b268 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 268 272 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 268 4 (by decide +kernel)

theorem ridges_002_b272 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 272 276 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 272 4 (by decide +kernel)

theorem ridges_002_b276 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 276 280 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 276 4 (by decide +kernel)

theorem ridges_002_b280 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 280 284 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 280 4 (by decide +kernel)

theorem ridges_002_b284 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 284 288 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 284 4 (by decide +kernel)

theorem ridges_002_b288 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 288 292 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 288 4 (by decide +kernel)

theorem ridges_002_b292 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 292 296 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 292 4 (by decide +kernel)

theorem ridges_002_b296 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 296 300 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 296 4 (by decide +kernel)

theorem ridges_002_b300 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 300 304 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 300 4 (by decide +kernel)

theorem ridges_002_b304 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 304 308 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 304 4 (by decide +kernel)

theorem ridges_002_b308 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 308 312 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 308 4 (by decide +kernel)

theorem ridges_002_b312 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 312 316 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 312 4 (by decide +kernel)

theorem ridges_002_b316 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 316 320 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 316 4 (by decide +kernel)

theorem ridges_002_b320 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 320 324 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 320 4 (by decide +kernel)

theorem ridges_002_b324 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 324 328 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 324 4 (by decide +kernel)

theorem ridges_002_b328 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 328 332 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 328 4 (by decide +kernel)

theorem ridges_002_b332 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 332 336 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 332 4 (by decide +kernel)

theorem ridges_002_b336 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 336 340 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 336 4 (by decide +kernel)

theorem ridges_002_b340 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 340 344 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 340 4 (by decide +kernel)

theorem ridges_002_b344 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 344 348 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 344 4 (by decide +kernel)

theorem ridges_002_b348 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 348 352 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 348 4 (by decide +kernel)

theorem ridges_002_b352 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 352 356 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 352 4 (by decide +kernel)

theorem ridges_002_b356 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 356 360 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 356 4 (by decide +kernel)

theorem ridges_002_b360 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 360 364 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 360 4 (by decide +kernel)

theorem ridges_002_b364 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 364 368 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 364 4 (by decide +kernel)

theorem ridges_002_b368 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 368 372 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 368 4 (by decide +kernel)

theorem ridges_002_b372 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 372 376 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 372 4 (by decide +kernel)

theorem ridges_002_b376 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 376 380 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 376 4 (by decide +kernel)

theorem ridges_002_b380 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 380 384 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 380 4 (by decide +kernel)

theorem ridges_002 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 256 384 :=
  (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 256 320 384
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 256 288 320
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 256 272 288
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 256 264 272
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 256 260 264
 ridges_002_b256
 ridges_002_b260)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 264 268 272
 ridges_002_b264
 ridges_002_b268))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 272 280 288
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 272 276 280
 ridges_002_b272
 ridges_002_b276)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 280 284 288
 ridges_002_b280
 ridges_002_b284)))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 288 304 320
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 288 296 304
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 288 292 296
 ridges_002_b288
 ridges_002_b292)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 296 300 304
 ridges_002_b296
 ridges_002_b300))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 304 312 320
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 304 308 312
 ridges_002_b304
 ridges_002_b308)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 312 316 320
 ridges_002_b312
 ridges_002_b316))))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 320 352 384
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 320 336 352
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 320 328 336
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 320 324 328
 ridges_002_b320
 ridges_002_b324)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 328 332 336
 ridges_002_b328
 ridges_002_b332))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 336 344 352
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 336 340 344
 ridges_002_b336
 ridges_002_b340)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 344 348 352
 ridges_002_b344
 ridges_002_b348)))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 352 368 384
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 352 360 368
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 352 356 360
 ridges_002_b352
 ridges_002_b356)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 360 364 368
 ridges_002_b360
 ridges_002_b364))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 368 376 384
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 368 372 376
 ridges_002_b368
 ridges_002_b372)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 376 380 384
 ridges_002_b376
 ridges_002_b380)))))
end Papers.RationalityTen.SharedSmallGraph
