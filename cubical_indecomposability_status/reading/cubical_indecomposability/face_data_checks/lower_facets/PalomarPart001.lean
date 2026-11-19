module
public import cubical_indecomposability.face_data_checks.lower_facets.PalomarPart000
import all cubical_indecomposability.face_data_checks.lower_facets.PalomarPart000
public import cubical_indecomposability.face_data_checks.anchors
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Interval.Finset.Fin
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Sparse, exact finite certificates

The proposed finite data are checked by ordinary Lean kernel reduction.
The generic proof then recovers the full universally quantified statement.
Exhaustive case splits have at most 32 leaves per declaration.

Regenerate with `python3 scripts/sparse_supports_lower.py`.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option autoImplicit false

namespace CubicalIndecomposability

/- A face of rank one less than `i` contained in `i` has its chosen
vertex in `i`. Thus these small buckets contain every possible lower face.
They may contain extra entries: the final rank/containment filter removes
those entries, and the equality certificate checks the resulting table. -/

private theorem bucketGroup0011 (i : Fin 1069)
    (hlo : 352 ≤ i.val) (hhi : i.val < 384) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
  have hi_bound := i.isLt
  by_cases h368 : i.val < 368
  ·
    by_cases h360 : i.val < 360
    ·
      by_cases h356 : i.val < 356
      ·
        by_cases h354 : i.val < 354
        ·
          by_cases h353 : i.val < 353
          ·
            have he : (⟨352, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 352 = i.val
              omega
            simpa only [he] using bucket0352
          ·
            have he : (⟨353, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 353 = i.val
              omega
            simpa only [he] using bucket0353
        ·
          by_cases h355 : i.val < 355
          ·
            have he : (⟨354, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 354 = i.val
              omega
            simpa only [he] using bucket0354
          ·
            have he : (⟨355, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 355 = i.val
              omega
            simpa only [he] using bucket0355
      ·
        by_cases h358 : i.val < 358
        ·
          by_cases h357 : i.val < 357
          ·
            have he : (⟨356, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 356 = i.val
              omega
            simpa only [he] using bucket0356
          ·
            have he : (⟨357, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 357 = i.val
              omega
            simpa only [he] using bucket0357
        ·
          by_cases h359 : i.val < 359
          ·
            have he : (⟨358, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 358 = i.val
              omega
            simpa only [he] using bucket0358
          ·
            have he : (⟨359, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 359 = i.val
              omega
            simpa only [he] using bucket0359
    ·
      by_cases h364 : i.val < 364
      ·
        by_cases h362 : i.val < 362
        ·
          by_cases h361 : i.val < 361
          ·
            have he : (⟨360, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 360 = i.val
              omega
            simpa only [he] using bucket0360
          ·
            have he : (⟨361, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 361 = i.val
              omega
            simpa only [he] using bucket0361
        ·
          by_cases h363 : i.val < 363
          ·
            have he : (⟨362, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 362 = i.val
              omega
            simpa only [he] using bucket0362
          ·
            have he : (⟨363, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 363 = i.val
              omega
            simpa only [he] using bucket0363
      ·
        by_cases h366 : i.val < 366
        ·
          by_cases h365 : i.val < 365
          ·
            have he : (⟨364, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 364 = i.val
              omega
            simpa only [he] using bucket0364
          ·
            have he : (⟨365, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 365 = i.val
              omega
            simpa only [he] using bucket0365
        ·
          by_cases h367 : i.val < 367
          ·
            have he : (⟨366, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 366 = i.val
              omega
            simpa only [he] using bucket0366
          ·
            have he : (⟨367, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 367 = i.val
              omega
            simpa only [he] using bucket0367
  ·
    by_cases h376 : i.val < 376
    ·
      by_cases h372 : i.val < 372
      ·
        by_cases h370 : i.val < 370
        ·
          by_cases h369 : i.val < 369
          ·
            have he : (⟨368, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 368 = i.val
              omega
            simpa only [he] using bucket0368
          ·
            have he : (⟨369, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 369 = i.val
              omega
            simpa only [he] using bucket0369
        ·
          by_cases h371 : i.val < 371
          ·
            have he : (⟨370, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 370 = i.val
              omega
            simpa only [he] using bucket0370
          ·
            have he : (⟨371, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 371 = i.val
              omega
            simpa only [he] using bucket0371
      ·
        by_cases h374 : i.val < 374
        ·
          by_cases h373 : i.val < 373
          ·
            have he : (⟨372, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 372 = i.val
              omega
            simpa only [he] using bucket0372
          ·
            have he : (⟨373, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 373 = i.val
              omega
            simpa only [he] using bucket0373
        ·
          by_cases h375 : i.val < 375
          ·
            have he : (⟨374, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 374 = i.val
              omega
            simpa only [he] using bucket0374
          ·
            have he : (⟨375, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 375 = i.val
              omega
            simpa only [he] using bucket0375
    ·
      by_cases h380 : i.val < 380
      ·
        by_cases h378 : i.val < 378
        ·
          by_cases h377 : i.val < 377
          ·
            have he : (⟨376, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 376 = i.val
              omega
            simpa only [he] using bucket0376
          ·
            have he : (⟨377, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 377 = i.val
              omega
            simpa only [he] using bucket0377
        ·
          by_cases h379 : i.val < 379
          ·
            have he : (⟨378, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 378 = i.val
              omega
            simpa only [he] using bucket0378
          ·
            have he : (⟨379, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 379 = i.val
              omega
            simpa only [he] using bucket0379
      ·
        by_cases h382 : i.val < 382
        ·
          by_cases h381 : i.val < 381
          ·
            have he : (⟨380, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 380 = i.val
              omega
            simpa only [he] using bucket0380
          ·
            have he : (⟨381, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 381 = i.val
              omega
            simpa only [he] using bucket0381
        ·
          by_cases h383 : i.val < 383
          ·
            have he : (⟨382, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 382 = i.val
              omega
            simpa only [he] using bucket0382
          ·
            have he : (⟨383, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 383 = i.val
              omega
            simpa only [he] using bucket0383

private theorem bucketGroup0012 (i : Fin 1069)
    (hlo : 384 ≤ i.val) (hhi : i.val < 416) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
  have hi_bound := i.isLt
  by_cases h400 : i.val < 400
  ·
    by_cases h392 : i.val < 392
    ·
      by_cases h388 : i.val < 388
      ·
        by_cases h386 : i.val < 386
        ·
          by_cases h385 : i.val < 385
          ·
            have he : (⟨384, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 384 = i.val
              omega
            simpa only [he] using bucket0384
          ·
            have he : (⟨385, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 385 = i.val
              omega
            simpa only [he] using bucket0385
        ·
          by_cases h387 : i.val < 387
          ·
            have he : (⟨386, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 386 = i.val
              omega
            simpa only [he] using bucket0386
          ·
            have he : (⟨387, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 387 = i.val
              omega
            simpa only [he] using bucket0387
      ·
        by_cases h390 : i.val < 390
        ·
          by_cases h389 : i.val < 389
          ·
            have he : (⟨388, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 388 = i.val
              omega
            simpa only [he] using bucket0388
          ·
            have he : (⟨389, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 389 = i.val
              omega
            simpa only [he] using bucket0389
        ·
          by_cases h391 : i.val < 391
          ·
            have he : (⟨390, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 390 = i.val
              omega
            simpa only [he] using bucket0390
          ·
            have he : (⟨391, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 391 = i.val
              omega
            simpa only [he] using bucket0391
    ·
      by_cases h396 : i.val < 396
      ·
        by_cases h394 : i.val < 394
        ·
          by_cases h393 : i.val < 393
          ·
            have he : (⟨392, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 392 = i.val
              omega
            simpa only [he] using bucket0392
          ·
            have he : (⟨393, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 393 = i.val
              omega
            simpa only [he] using bucket0393
        ·
          by_cases h395 : i.val < 395
          ·
            have he : (⟨394, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 394 = i.val
              omega
            simpa only [he] using bucket0394
          ·
            have he : (⟨395, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 395 = i.val
              omega
            simpa only [he] using bucket0395
      ·
        by_cases h398 : i.val < 398
        ·
          by_cases h397 : i.val < 397
          ·
            have he : (⟨396, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 396 = i.val
              omega
            simpa only [he] using bucket0396
          ·
            have he : (⟨397, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 397 = i.val
              omega
            simpa only [he] using bucket0397
        ·
          by_cases h399 : i.val < 399
          ·
            have he : (⟨398, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 398 = i.val
              omega
            simpa only [he] using bucket0398
          ·
            have he : (⟨399, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 399 = i.val
              omega
            simpa only [he] using bucket0399
  ·
    by_cases h408 : i.val < 408
    ·
      by_cases h404 : i.val < 404
      ·
        by_cases h402 : i.val < 402
        ·
          by_cases h401 : i.val < 401
          ·
            have he : (⟨400, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 400 = i.val
              omega
            simpa only [he] using bucket0400
          ·
            have he : (⟨401, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 401 = i.val
              omega
            simpa only [he] using bucket0401
        ·
          by_cases h403 : i.val < 403
          ·
            have he : (⟨402, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 402 = i.val
              omega
            simpa only [he] using bucket0402
          ·
            have he : (⟨403, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 403 = i.val
              omega
            simpa only [he] using bucket0403
      ·
        by_cases h406 : i.val < 406
        ·
          by_cases h405 : i.val < 405
          ·
            have he : (⟨404, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 404 = i.val
              omega
            simpa only [he] using bucket0404
          ·
            have he : (⟨405, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 405 = i.val
              omega
            simpa only [he] using bucket0405
        ·
          by_cases h407 : i.val < 407
          ·
            have he : (⟨406, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 406 = i.val
              omega
            simpa only [he] using bucket0406
          ·
            have he : (⟨407, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 407 = i.val
              omega
            simpa only [he] using bucket0407
    ·
      by_cases h412 : i.val < 412
      ·
        by_cases h410 : i.val < 410
        ·
          by_cases h409 : i.val < 409
          ·
            have he : (⟨408, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 408 = i.val
              omega
            simpa only [he] using bucket0408
          ·
            have he : (⟨409, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 409 = i.val
              omega
            simpa only [he] using bucket0409
        ·
          by_cases h411 : i.val < 411
          ·
            have he : (⟨410, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 410 = i.val
              omega
            simpa only [he] using bucket0410
          ·
            have he : (⟨411, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 411 = i.val
              omega
            simpa only [he] using bucket0411
      ·
        by_cases h414 : i.val < 414
        ·
          by_cases h413 : i.val < 413
          ·
            have he : (⟨412, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 412 = i.val
              omega
            simpa only [he] using bucket0412
          ·
            have he : (⟨413, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 413 = i.val
              omega
            simpa only [he] using bucket0413
        ·
          by_cases h415 : i.val < 415
          ·
            have he : (⟨414, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 414 = i.val
              omega
            simpa only [he] using bucket0414
          ·
            have he : (⟨415, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 415 = i.val
              omega
            simpa only [he] using bucket0415

private theorem bucketGroup0013 (i : Fin 1069)
    (hlo : 416 ≤ i.val) (hhi : i.val < 448) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
  have hi_bound := i.isLt
  by_cases h432 : i.val < 432
  ·
    by_cases h424 : i.val < 424
    ·
      by_cases h420 : i.val < 420
      ·
        by_cases h418 : i.val < 418
        ·
          by_cases h417 : i.val < 417
          ·
            have he : (⟨416, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 416 = i.val
              omega
            simpa only [he] using bucket0416
          ·
            have he : (⟨417, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 417 = i.val
              omega
            simpa only [he] using bucket0417
        ·
          by_cases h419 : i.val < 419
          ·
            have he : (⟨418, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 418 = i.val
              omega
            simpa only [he] using bucket0418
          ·
            have he : (⟨419, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 419 = i.val
              omega
            simpa only [he] using bucket0419
      ·
        by_cases h422 : i.val < 422
        ·
          by_cases h421 : i.val < 421
          ·
            have he : (⟨420, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 420 = i.val
              omega
            simpa only [he] using bucket0420
          ·
            have he : (⟨421, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 421 = i.val
              omega
            simpa only [he] using bucket0421
        ·
          by_cases h423 : i.val < 423
          ·
            have he : (⟨422, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 422 = i.val
              omega
            simpa only [he] using bucket0422
          ·
            have he : (⟨423, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 423 = i.val
              omega
            simpa only [he] using bucket0423
    ·
      by_cases h428 : i.val < 428
      ·
        by_cases h426 : i.val < 426
        ·
          by_cases h425 : i.val < 425
          ·
            have he : (⟨424, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 424 = i.val
              omega
            simpa only [he] using bucket0424
          ·
            have he : (⟨425, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 425 = i.val
              omega
            simpa only [he] using bucket0425
        ·
          by_cases h427 : i.val < 427
          ·
            have he : (⟨426, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 426 = i.val
              omega
            simpa only [he] using bucket0426
          ·
            have he : (⟨427, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 427 = i.val
              omega
            simpa only [he] using bucket0427
      ·
        by_cases h430 : i.val < 430
        ·
          by_cases h429 : i.val < 429
          ·
            have he : (⟨428, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 428 = i.val
              omega
            simpa only [he] using bucket0428
          ·
            have he : (⟨429, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 429 = i.val
              omega
            simpa only [he] using bucket0429
        ·
          by_cases h431 : i.val < 431
          ·
            have he : (⟨430, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 430 = i.val
              omega
            simpa only [he] using bucket0430
          ·
            have he : (⟨431, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 431 = i.val
              omega
            simpa only [he] using bucket0431
  ·
    by_cases h440 : i.val < 440
    ·
      by_cases h436 : i.val < 436
      ·
        by_cases h434 : i.val < 434
        ·
          by_cases h433 : i.val < 433
          ·
            have he : (⟨432, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 432 = i.val
              omega
            simpa only [he] using bucket0432
          ·
            have he : (⟨433, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 433 = i.val
              omega
            simpa only [he] using bucket0433
        ·
          by_cases h435 : i.val < 435
          ·
            have he : (⟨434, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 434 = i.val
              omega
            simpa only [he] using bucket0434
          ·
            have he : (⟨435, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 435 = i.val
              omega
            simpa only [he] using bucket0435
      ·
        by_cases h438 : i.val < 438
        ·
          by_cases h437 : i.val < 437
          ·
            have he : (⟨436, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 436 = i.val
              omega
            simpa only [he] using bucket0436
          ·
            have he : (⟨437, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 437 = i.val
              omega
            simpa only [he] using bucket0437
        ·
          by_cases h439 : i.val < 439
          ·
            have he : (⟨438, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 438 = i.val
              omega
            simpa only [he] using bucket0438
          ·
            have he : (⟨439, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 439 = i.val
              omega
            simpa only [he] using bucket0439
    ·
      by_cases h444 : i.val < 444
      ·
        by_cases h442 : i.val < 442
        ·
          by_cases h441 : i.val < 441
          ·
            have he : (⟨440, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 440 = i.val
              omega
            simpa only [he] using bucket0440
          ·
            have he : (⟨441, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 441 = i.val
              omega
            simpa only [he] using bucket0441
        ·
          by_cases h443 : i.val < 443
          ·
            have he : (⟨442, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 442 = i.val
              omega
            simpa only [he] using bucket0442
          ·
            have he : (⟨443, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 443 = i.val
              omega
            simpa only [he] using bucket0443
      ·
        by_cases h446 : i.val < 446
        ·
          by_cases h445 : i.val < 445
          ·
            have he : (⟨444, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 444 = i.val
              omega
            simpa only [he] using bucket0444
          ·
            have he : (⟨445, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 445 = i.val
              omega
            simpa only [he] using bucket0445
        ·
          by_cases h447 : i.val < 447
          ·
            have he : (⟨446, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 446 = i.val
              omega
            simpa only [he] using bucket0446
          ·
            have he : (⟨447, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 447 = i.val
              omega
            simpa only [he] using bucket0447

private theorem bucketGroup0014 (i : Fin 1069)
    (hlo : 448 ≤ i.val) (hhi : i.val < 480) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
  have hi_bound := i.isLt
  by_cases h464 : i.val < 464
  ·
    by_cases h456 : i.val < 456
    ·
      by_cases h452 : i.val < 452
      ·
        by_cases h450 : i.val < 450
        ·
          by_cases h449 : i.val < 449
          ·
            have he : (⟨448, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 448 = i.val
              omega
            simpa only [he] using bucket0448
          ·
            have he : (⟨449, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 449 = i.val
              omega
            simpa only [he] using bucket0449
        ·
          by_cases h451 : i.val < 451
          ·
            have he : (⟨450, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 450 = i.val
              omega
            simpa only [he] using bucket0450
          ·
            have he : (⟨451, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 451 = i.val
              omega
            simpa only [he] using bucket0451
      ·
        by_cases h454 : i.val < 454
        ·
          by_cases h453 : i.val < 453
          ·
            have he : (⟨452, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 452 = i.val
              omega
            simpa only [he] using bucket0452
          ·
            have he : (⟨453, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 453 = i.val
              omega
            simpa only [he] using bucket0453
        ·
          by_cases h455 : i.val < 455
          ·
            have he : (⟨454, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 454 = i.val
              omega
            simpa only [he] using bucket0454
          ·
            have he : (⟨455, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 455 = i.val
              omega
            simpa only [he] using bucket0455
    ·
      by_cases h460 : i.val < 460
      ·
        by_cases h458 : i.val < 458
        ·
          by_cases h457 : i.val < 457
          ·
            have he : (⟨456, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 456 = i.val
              omega
            simpa only [he] using bucket0456
          ·
            have he : (⟨457, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 457 = i.val
              omega
            simpa only [he] using bucket0457
        ·
          by_cases h459 : i.val < 459
          ·
            have he : (⟨458, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 458 = i.val
              omega
            simpa only [he] using bucket0458
          ·
            have he : (⟨459, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 459 = i.val
              omega
            simpa only [he] using bucket0459
      ·
        by_cases h462 : i.val < 462
        ·
          by_cases h461 : i.val < 461
          ·
            have he : (⟨460, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 460 = i.val
              omega
            simpa only [he] using bucket0460
          ·
            have he : (⟨461, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 461 = i.val
              omega
            simpa only [he] using bucket0461
        ·
          by_cases h463 : i.val < 463
          ·
            have he : (⟨462, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 462 = i.val
              omega
            simpa only [he] using bucket0462
          ·
            have he : (⟨463, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 463 = i.val
              omega
            simpa only [he] using bucket0463
  ·
    by_cases h472 : i.val < 472
    ·
      by_cases h468 : i.val < 468
      ·
        by_cases h466 : i.val < 466
        ·
          by_cases h465 : i.val < 465
          ·
            have he : (⟨464, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 464 = i.val
              omega
            simpa only [he] using bucket0464
          ·
            have he : (⟨465, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 465 = i.val
              omega
            simpa only [he] using bucket0465
        ·
          by_cases h467 : i.val < 467
          ·
            have he : (⟨466, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 466 = i.val
              omega
            simpa only [he] using bucket0466
          ·
            have he : (⟨467, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 467 = i.val
              omega
            simpa only [he] using bucket0467
      ·
        by_cases h470 : i.val < 470
        ·
          by_cases h469 : i.val < 469
          ·
            have he : (⟨468, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 468 = i.val
              omega
            simpa only [he] using bucket0468
          ·
            have he : (⟨469, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 469 = i.val
              omega
            simpa only [he] using bucket0469
        ·
          by_cases h471 : i.val < 471
          ·
            have he : (⟨470, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 470 = i.val
              omega
            simpa only [he] using bucket0470
          ·
            have he : (⟨471, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 471 = i.val
              omega
            simpa only [he] using bucket0471
    ·
      by_cases h476 : i.val < 476
      ·
        by_cases h474 : i.val < 474
        ·
          by_cases h473 : i.val < 473
          ·
            have he : (⟨472, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 472 = i.val
              omega
            simpa only [he] using bucket0472
          ·
            have he : (⟨473, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 473 = i.val
              omega
            simpa only [he] using bucket0473
        ·
          by_cases h475 : i.val < 475
          ·
            have he : (⟨474, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 474 = i.val
              omega
            simpa only [he] using bucket0474
          ·
            have he : (⟨475, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 475 = i.val
              omega
            simpa only [he] using bucket0475
      ·
        by_cases h478 : i.val < 478
        ·
          by_cases h477 : i.val < 477
          ·
            have he : (⟨476, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 476 = i.val
              omega
            simpa only [he] using bucket0476
          ·
            have he : (⟨477, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 477 = i.val
              omega
            simpa only [he] using bucket0477
        ·
          by_cases h479 : i.val < 479
          ·
            have he : (⟨478, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 478 = i.val
              omega
            simpa only [he] using bucket0478
          ·
            have he : (⟨479, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 479 = i.val
              omega
            simpa only [he] using bucket0479

private theorem bucketGroup0015 (i : Fin 1069)
    (hlo : 480 ≤ i.val) (hhi : i.val < 512) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
  have hi_bound := i.isLt
  by_cases h496 : i.val < 496
  ·
    by_cases h488 : i.val < 488
    ·
      by_cases h484 : i.val < 484
      ·
        by_cases h482 : i.val < 482
        ·
          by_cases h481 : i.val < 481
          ·
            have he : (⟨480, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 480 = i.val
              omega
            simpa only [he] using bucket0480
          ·
            have he : (⟨481, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 481 = i.val
              omega
            simpa only [he] using bucket0481
        ·
          by_cases h483 : i.val < 483
          ·
            have he : (⟨482, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 482 = i.val
              omega
            simpa only [he] using bucket0482
          ·
            have he : (⟨483, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 483 = i.val
              omega
            simpa only [he] using bucket0483
      ·
        by_cases h486 : i.val < 486
        ·
          by_cases h485 : i.val < 485
          ·
            have he : (⟨484, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 484 = i.val
              omega
            simpa only [he] using bucket0484
          ·
            have he : (⟨485, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 485 = i.val
              omega
            simpa only [he] using bucket0485
        ·
          by_cases h487 : i.val < 487
          ·
            have he : (⟨486, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 486 = i.val
              omega
            simpa only [he] using bucket0486
          ·
            have he : (⟨487, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 487 = i.val
              omega
            simpa only [he] using bucket0487
    ·
      by_cases h492 : i.val < 492
      ·
        by_cases h490 : i.val < 490
        ·
          by_cases h489 : i.val < 489
          ·
            have he : (⟨488, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 488 = i.val
              omega
            simpa only [he] using bucket0488
          ·
            have he : (⟨489, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 489 = i.val
              omega
            simpa only [he] using bucket0489
        ·
          by_cases h491 : i.val < 491
          ·
            have he : (⟨490, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 490 = i.val
              omega
            simpa only [he] using bucket0490
          ·
            have he : (⟨491, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 491 = i.val
              omega
            simpa only [he] using bucket0491
      ·
        by_cases h494 : i.val < 494
        ·
          by_cases h493 : i.val < 493
          ·
            have he : (⟨492, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 492 = i.val
              omega
            simpa only [he] using bucket0492
          ·
            have he : (⟨493, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 493 = i.val
              omega
            simpa only [he] using bucket0493
        ·
          by_cases h495 : i.val < 495
          ·
            have he : (⟨494, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 494 = i.val
              omega
            simpa only [he] using bucket0494
          ·
            have he : (⟨495, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 495 = i.val
              omega
            simpa only [he] using bucket0495
  ·
    by_cases h504 : i.val < 504
    ·
      by_cases h500 : i.val < 500
      ·
        by_cases h498 : i.val < 498
        ·
          by_cases h497 : i.val < 497
          ·
            have he : (⟨496, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 496 = i.val
              omega
            simpa only [he] using bucket0496
          ·
            have he : (⟨497, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 497 = i.val
              omega
            simpa only [he] using bucket0497
        ·
          by_cases h499 : i.val < 499
          ·
            have he : (⟨498, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 498 = i.val
              omega
            simpa only [he] using bucket0498
          ·
            have he : (⟨499, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 499 = i.val
              omega
            simpa only [he] using bucket0499
      ·
        by_cases h502 : i.val < 502
        ·
          by_cases h501 : i.val < 501
          ·
            have he : (⟨500, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 500 = i.val
              omega
            simpa only [he] using bucket0500
          ·
            have he : (⟨501, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 501 = i.val
              omega
            simpa only [he] using bucket0501
        ·
          by_cases h503 : i.val < 503
          ·
            have he : (⟨502, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 502 = i.val
              omega
            simpa only [he] using bucket0502
          ·
            have he : (⟨503, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 503 = i.val
              omega
            simpa only [he] using bucket0503
    ·
      by_cases h508 : i.val < 508
      ·
        by_cases h506 : i.val < 506
        ·
          by_cases h505 : i.val < 505
          ·
            have he : (⟨504, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 504 = i.val
              omega
            simpa only [he] using bucket0504
          ·
            have he : (⟨505, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 505 = i.val
              omega
            simpa only [he] using bucket0505
        ·
          by_cases h507 : i.val < 507
          ·
            have he : (⟨506, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 506 = i.val
              omega
            simpa only [he] using bucket0506
          ·
            have he : (⟨507, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 507 = i.val
              omega
            simpa only [he] using bucket0507
      ·
        by_cases h510 : i.val < 510
        ·
          by_cases h509 : i.val < 509
          ·
            have he : (⟨508, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 508 = i.val
              omega
            simpa only [he] using bucket0508
          ·
            have he : (⟨509, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 509 = i.val
              omega
            simpa only [he] using bucket0509
        ·
          by_cases h511 : i.val < 511
          ·
            have he : (⟨510, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 510 = i.val
              omega
            simpa only [he] using bucket0510
          ·
            have he : (⟨511, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 511 = i.val
              omega
            simpa only [he] using bucket0511

private theorem bucketGroup0016 (i : Fin 1069)
    (hlo : 512 ≤ i.val) (hhi : i.val < 544) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
  have hi_bound := i.isLt
  by_cases h528 : i.val < 528
  ·
    by_cases h520 : i.val < 520
    ·
      by_cases h516 : i.val < 516
      ·
        by_cases h514 : i.val < 514
        ·
          by_cases h513 : i.val < 513
          ·
            have he : (⟨512, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 512 = i.val
              omega
            simpa only [he] using bucket0512
          ·
            have he : (⟨513, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 513 = i.val
              omega
            simpa only [he] using bucket0513
        ·
          by_cases h515 : i.val < 515
          ·
            have he : (⟨514, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 514 = i.val
              omega
            simpa only [he] using bucket0514
          ·
            have he : (⟨515, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 515 = i.val
              omega
            simpa only [he] using bucket0515
      ·
        by_cases h518 : i.val < 518
        ·
          by_cases h517 : i.val < 517
          ·
            have he : (⟨516, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 516 = i.val
              omega
            simpa only [he] using bucket0516
          ·
            have he : (⟨517, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 517 = i.val
              omega
            simpa only [he] using bucket0517
        ·
          by_cases h519 : i.val < 519
          ·
            have he : (⟨518, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 518 = i.val
              omega
            simpa only [he] using bucket0518
          ·
            have he : (⟨519, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 519 = i.val
              omega
            simpa only [he] using bucket0519
    ·
      by_cases h524 : i.val < 524
      ·
        by_cases h522 : i.val < 522
        ·
          by_cases h521 : i.val < 521
          ·
            have he : (⟨520, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 520 = i.val
              omega
            simpa only [he] using bucket0520
          ·
            have he : (⟨521, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 521 = i.val
              omega
            simpa only [he] using bucket0521
        ·
          by_cases h523 : i.val < 523
          ·
            have he : (⟨522, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 522 = i.val
              omega
            simpa only [he] using bucket0522
          ·
            have he : (⟨523, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 523 = i.val
              omega
            simpa only [he] using bucket0523
      ·
        by_cases h526 : i.val < 526
        ·
          by_cases h525 : i.val < 525
          ·
            have he : (⟨524, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 524 = i.val
              omega
            simpa only [he] using bucket0524
          ·
            have he : (⟨525, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 525 = i.val
              omega
            simpa only [he] using bucket0525
        ·
          by_cases h527 : i.val < 527
          ·
            have he : (⟨526, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 526 = i.val
              omega
            simpa only [he] using bucket0526
          ·
            have he : (⟨527, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 527 = i.val
              omega
            simpa only [he] using bucket0527
  ·
    by_cases h536 : i.val < 536
    ·
      by_cases h532 : i.val < 532
      ·
        by_cases h530 : i.val < 530
        ·
          by_cases h529 : i.val < 529
          ·
            have he : (⟨528, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 528 = i.val
              omega
            simpa only [he] using bucket0528
          ·
            have he : (⟨529, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 529 = i.val
              omega
            simpa only [he] using bucket0529
        ·
          by_cases h531 : i.val < 531
          ·
            have he : (⟨530, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 530 = i.val
              omega
            simpa only [he] using bucket0530
          ·
            have he : (⟨531, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 531 = i.val
              omega
            simpa only [he] using bucket0531
      ·
        by_cases h534 : i.val < 534
        ·
          by_cases h533 : i.val < 533
          ·
            have he : (⟨532, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 532 = i.val
              omega
            simpa only [he] using bucket0532
          ·
            have he : (⟨533, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 533 = i.val
              omega
            simpa only [he] using bucket0533
        ·
          by_cases h535 : i.val < 535
          ·
            have he : (⟨534, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 534 = i.val
              omega
            simpa only [he] using bucket0534
          ·
            have he : (⟨535, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 535 = i.val
              omega
            simpa only [he] using bucket0535
    ·
      by_cases h540 : i.val < 540
      ·
        by_cases h538 : i.val < 538
        ·
          by_cases h537 : i.val < 537
          ·
            have he : (⟨536, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 536 = i.val
              omega
            simpa only [he] using bucket0536
          ·
            have he : (⟨537, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 537 = i.val
              omega
            simpa only [he] using bucket0537
        ·
          by_cases h539 : i.val < 539
          ·
            have he : (⟨538, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 538 = i.val
              omega
            simpa only [he] using bucket0538
          ·
            have he : (⟨539, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 539 = i.val
              omega
            simpa only [he] using bucket0539
      ·
        by_cases h542 : i.val < 542
        ·
          by_cases h541 : i.val < 541
          ·
            have he : (⟨540, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 540 = i.val
              omega
            simpa only [he] using bucket0540
          ·
            have he : (⟨541, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 541 = i.val
              omega
            simpa only [he] using bucket0541
        ·
          by_cases h543 : i.val < 543
          ·
            have he : (⟨542, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 542 = i.val
              omega
            simpa only [he] using bucket0542
          ·
            have he : (⟨543, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 543 = i.val
              omega
            simpa only [he] using bucket0543

private theorem bucketGroup0017 (i : Fin 1069)
    (hlo : 544 ≤ i.val) (hhi : i.val < 576) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
  have hi_bound := i.isLt
  by_cases h560 : i.val < 560
  ·
    by_cases h552 : i.val < 552
    ·
      by_cases h548 : i.val < 548
      ·
        by_cases h546 : i.val < 546
        ·
          by_cases h545 : i.val < 545
          ·
            have he : (⟨544, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 544 = i.val
              omega
            simpa only [he] using bucket0544
          ·
            have he : (⟨545, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 545 = i.val
              omega
            simpa only [he] using bucket0545
        ·
          by_cases h547 : i.val < 547
          ·
            have he : (⟨546, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 546 = i.val
              omega
            simpa only [he] using bucket0546
          ·
            have he : (⟨547, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 547 = i.val
              omega
            simpa only [he] using bucket0547
      ·
        by_cases h550 : i.val < 550
        ·
          by_cases h549 : i.val < 549
          ·
            have he : (⟨548, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 548 = i.val
              omega
            simpa only [he] using bucket0548
          ·
            have he : (⟨549, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 549 = i.val
              omega
            simpa only [he] using bucket0549
        ·
          by_cases h551 : i.val < 551
          ·
            have he : (⟨550, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 550 = i.val
              omega
            simpa only [he] using bucket0550
          ·
            have he : (⟨551, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 551 = i.val
              omega
            simpa only [he] using bucket0551
    ·
      by_cases h556 : i.val < 556
      ·
        by_cases h554 : i.val < 554
        ·
          by_cases h553 : i.val < 553
          ·
            have he : (⟨552, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 552 = i.val
              omega
            simpa only [he] using bucket0552
          ·
            have he : (⟨553, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 553 = i.val
              omega
            simpa only [he] using bucket0553
        ·
          by_cases h555 : i.val < 555
          ·
            have he : (⟨554, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 554 = i.val
              omega
            simpa only [he] using bucket0554
          ·
            have he : (⟨555, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 555 = i.val
              omega
            simpa only [he] using bucket0555
      ·
        by_cases h558 : i.val < 558
        ·
          by_cases h557 : i.val < 557
          ·
            have he : (⟨556, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 556 = i.val
              omega
            simpa only [he] using bucket0556
          ·
            have he : (⟨557, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 557 = i.val
              omega
            simpa only [he] using bucket0557
        ·
          by_cases h559 : i.val < 559
          ·
            have he : (⟨558, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 558 = i.val
              omega
            simpa only [he] using bucket0558
          ·
            have he : (⟨559, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 559 = i.val
              omega
            simpa only [he] using bucket0559
  ·
    by_cases h568 : i.val < 568
    ·
      by_cases h564 : i.val < 564
      ·
        by_cases h562 : i.val < 562
        ·
          by_cases h561 : i.val < 561
          ·
            have he : (⟨560, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 560 = i.val
              omega
            simpa only [he] using bucket0560
          ·
            have he : (⟨561, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 561 = i.val
              omega
            simpa only [he] using bucket0561
        ·
          by_cases h563 : i.val < 563
          ·
            have he : (⟨562, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 562 = i.val
              omega
            simpa only [he] using bucket0562
          ·
            have he : (⟨563, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 563 = i.val
              omega
            simpa only [he] using bucket0563
      ·
        by_cases h566 : i.val < 566
        ·
          by_cases h565 : i.val < 565
          ·
            have he : (⟨564, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 564 = i.val
              omega
            simpa only [he] using bucket0564
          ·
            have he : (⟨565, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 565 = i.val
              omega
            simpa only [he] using bucket0565
        ·
          by_cases h567 : i.val < 567
          ·
            have he : (⟨566, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 566 = i.val
              omega
            simpa only [he] using bucket0566
          ·
            have he : (⟨567, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 567 = i.val
              omega
            simpa only [he] using bucket0567
    ·
      by_cases h572 : i.val < 572
      ·
        by_cases h570 : i.val < 570
        ·
          by_cases h569 : i.val < 569
          ·
            have he : (⟨568, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 568 = i.val
              omega
            simpa only [he] using bucket0568
          ·
            have he : (⟨569, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 569 = i.val
              omega
            simpa only [he] using bucket0569
        ·
          by_cases h571 : i.val < 571
          ·
            have he : (⟨570, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 570 = i.val
              omega
            simpa only [he] using bucket0570
          ·
            have he : (⟨571, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 571 = i.val
              omega
            simpa only [he] using bucket0571
      ·
        by_cases h574 : i.val < 574
        ·
          by_cases h573 : i.val < 573
          ·
            have he : (⟨572, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 572 = i.val
              omega
            simpa only [he] using bucket0572
          ·
            have he : (⟨573, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 573 = i.val
              omega
            simpa only [he] using bucket0573
        ·
          by_cases h575 : i.val < 575
          ·
            have he : (⟨574, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 574 = i.val
              omega
            simpa only [he] using bucket0574
          ·
            have he : (⟨575, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 575 = i.val
              omega
            simpa only [he] using bucket0575

private theorem bucketGroup0018 (i : Fin 1069)
    (hlo : 576 ≤ i.val) (hhi : i.val < 608) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
  have hi_bound := i.isLt
  by_cases h592 : i.val < 592
  ·
    by_cases h584 : i.val < 584
    ·
      by_cases h580 : i.val < 580
      ·
        by_cases h578 : i.val < 578
        ·
          by_cases h577 : i.val < 577
          ·
            have he : (⟨576, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 576 = i.val
              omega
            simpa only [he] using bucket0576
          ·
            have he : (⟨577, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 577 = i.val
              omega
            simpa only [he] using bucket0577
        ·
          by_cases h579 : i.val < 579
          ·
            have he : (⟨578, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 578 = i.val
              omega
            simpa only [he] using bucket0578
          ·
            have he : (⟨579, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 579 = i.val
              omega
            simpa only [he] using bucket0579
      ·
        by_cases h582 : i.val < 582
        ·
          by_cases h581 : i.val < 581
          ·
            have he : (⟨580, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 580 = i.val
              omega
            simpa only [he] using bucket0580
          ·
            have he : (⟨581, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 581 = i.val
              omega
            simpa only [he] using bucket0581
        ·
          by_cases h583 : i.val < 583
          ·
            have he : (⟨582, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 582 = i.val
              omega
            simpa only [he] using bucket0582
          ·
            have he : (⟨583, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 583 = i.val
              omega
            simpa only [he] using bucket0583
    ·
      by_cases h588 : i.val < 588
      ·
        by_cases h586 : i.val < 586
        ·
          by_cases h585 : i.val < 585
          ·
            have he : (⟨584, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 584 = i.val
              omega
            simpa only [he] using bucket0584
          ·
            have he : (⟨585, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 585 = i.val
              omega
            simpa only [he] using bucket0585
        ·
          by_cases h587 : i.val < 587
          ·
            have he : (⟨586, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 586 = i.val
              omega
            simpa only [he] using bucket0586
          ·
            have he : (⟨587, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 587 = i.val
              omega
            simpa only [he] using bucket0587
      ·
        by_cases h590 : i.val < 590
        ·
          by_cases h589 : i.val < 589
          ·
            have he : (⟨588, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 588 = i.val
              omega
            simpa only [he] using bucket0588
          ·
            have he : (⟨589, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 589 = i.val
              omega
            simpa only [he] using bucket0589
        ·
          by_cases h591 : i.val < 591
          ·
            have he : (⟨590, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 590 = i.val
              omega
            simpa only [he] using bucket0590
          ·
            have he : (⟨591, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 591 = i.val
              omega
            simpa only [he] using bucket0591
  ·
    by_cases h600 : i.val < 600
    ·
      by_cases h596 : i.val < 596
      ·
        by_cases h594 : i.val < 594
        ·
          by_cases h593 : i.val < 593
          ·
            have he : (⟨592, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 592 = i.val
              omega
            simpa only [he] using bucket0592
          ·
            have he : (⟨593, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 593 = i.val
              omega
            simpa only [he] using bucket0593
        ·
          by_cases h595 : i.val < 595
          ·
            have he : (⟨594, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 594 = i.val
              omega
            simpa only [he] using bucket0594
          ·
            have he : (⟨595, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 595 = i.val
              omega
            simpa only [he] using bucket0595
      ·
        by_cases h598 : i.val < 598
        ·
          by_cases h597 : i.val < 597
          ·
            have he : (⟨596, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 596 = i.val
              omega
            simpa only [he] using bucket0596
          ·
            have he : (⟨597, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 597 = i.val
              omega
            simpa only [he] using bucket0597
        ·
          by_cases h599 : i.val < 599
          ·
            have he : (⟨598, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 598 = i.val
              omega
            simpa only [he] using bucket0598
          ·
            have he : (⟨599, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 599 = i.val
              omega
            simpa only [he] using bucket0599
    ·
      by_cases h604 : i.val < 604
      ·
        by_cases h602 : i.val < 602
        ·
          by_cases h601 : i.val < 601
          ·
            have he : (⟨600, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 600 = i.val
              omega
            simpa only [he] using bucket0600
          ·
            have he : (⟨601, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 601 = i.val
              omega
            simpa only [he] using bucket0601
        ·
          by_cases h603 : i.val < 603
          ·
            have he : (⟨602, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 602 = i.val
              omega
            simpa only [he] using bucket0602
          ·
            have he : (⟨603, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 603 = i.val
              omega
            simpa only [he] using bucket0603
      ·
        by_cases h606 : i.val < 606
        ·
          by_cases h605 : i.val < 605
          ·
            have he : (⟨604, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 604 = i.val
              omega
            simpa only [he] using bucket0604
          ·
            have he : (⟨605, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 605 = i.val
              omega
            simpa only [he] using bucket0605
        ·
          by_cases h607 : i.val < 607
          ·
            have he : (⟨606, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 606 = i.val
              omega
            simpa only [he] using bucket0606
          ·
            have he : (⟨607, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 607 = i.val
              omega
            simpa only [he] using bucket0607

private theorem bucketGroup0019 (i : Fin 1069)
    (hlo : 608 ≤ i.val) (hhi : i.val < 640) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
  have hi_bound := i.isLt
  by_cases h624 : i.val < 624
  ·
    by_cases h616 : i.val < 616
    ·
      by_cases h612 : i.val < 612
      ·
        by_cases h610 : i.val < 610
        ·
          by_cases h609 : i.val < 609
          ·
            have he : (⟨608, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 608 = i.val
              omega
            simpa only [he] using bucket0608
          ·
            have he : (⟨609, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 609 = i.val
              omega
            simpa only [he] using bucket0609
        ·
          by_cases h611 : i.val < 611
          ·
            have he : (⟨610, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 610 = i.val
              omega
            simpa only [he] using bucket0610
          ·
            have he : (⟨611, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 611 = i.val
              omega
            simpa only [he] using bucket0611
      ·
        by_cases h614 : i.val < 614
        ·
          by_cases h613 : i.val < 613
          ·
            have he : (⟨612, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 612 = i.val
              omega
            simpa only [he] using bucket0612
          ·
            have he : (⟨613, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 613 = i.val
              omega
            simpa only [he] using bucket0613
        ·
          by_cases h615 : i.val < 615
          ·
            have he : (⟨614, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 614 = i.val
              omega
            simpa only [he] using bucket0614
          ·
            have he : (⟨615, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 615 = i.val
              omega
            simpa only [he] using bucket0615
    ·
      by_cases h620 : i.val < 620
      ·
        by_cases h618 : i.val < 618
        ·
          by_cases h617 : i.val < 617
          ·
            have he : (⟨616, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 616 = i.val
              omega
            simpa only [he] using bucket0616
          ·
            have he : (⟨617, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 617 = i.val
              omega
            simpa only [he] using bucket0617
        ·
          by_cases h619 : i.val < 619
          ·
            have he : (⟨618, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 618 = i.val
              omega
            simpa only [he] using bucket0618
          ·
            have he : (⟨619, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 619 = i.val
              omega
            simpa only [he] using bucket0619
      ·
        by_cases h622 : i.val < 622
        ·
          by_cases h621 : i.val < 621
          ·
            have he : (⟨620, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 620 = i.val
              omega
            simpa only [he] using bucket0620
          ·
            have he : (⟨621, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 621 = i.val
              omega
            simpa only [he] using bucket0621
        ·
          by_cases h623 : i.val < 623
          ·
            have he : (⟨622, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 622 = i.val
              omega
            simpa only [he] using bucket0622
          ·
            have he : (⟨623, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 623 = i.val
              omega
            simpa only [he] using bucket0623
  ·
    by_cases h632 : i.val < 632
    ·
      by_cases h628 : i.val < 628
      ·
        by_cases h626 : i.val < 626
        ·
          by_cases h625 : i.val < 625
          ·
            have he : (⟨624, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 624 = i.val
              omega
            simpa only [he] using bucket0624
          ·
            have he : (⟨625, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 625 = i.val
              omega
            simpa only [he] using bucket0625
        ·
          by_cases h627 : i.val < 627
          ·
            have he : (⟨626, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 626 = i.val
              omega
            simpa only [he] using bucket0626
          ·
            have he : (⟨627, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 627 = i.val
              omega
            simpa only [he] using bucket0627
      ·
        by_cases h630 : i.val < 630
        ·
          by_cases h629 : i.val < 629
          ·
            have he : (⟨628, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 628 = i.val
              omega
            simpa only [he] using bucket0628
          ·
            have he : (⟨629, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 629 = i.val
              omega
            simpa only [he] using bucket0629
        ·
          by_cases h631 : i.val < 631
          ·
            have he : (⟨630, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 630 = i.val
              omega
            simpa only [he] using bucket0630
          ·
            have he : (⟨631, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 631 = i.val
              omega
            simpa only [he] using bucket0631
    ·
      by_cases h636 : i.val < 636
      ·
        by_cases h634 : i.val < 634
        ·
          by_cases h633 : i.val < 633
          ·
            have he : (⟨632, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 632 = i.val
              omega
            simpa only [he] using bucket0632
          ·
            have he : (⟨633, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 633 = i.val
              omega
            simpa only [he] using bucket0633
        ·
          by_cases h635 : i.val < 635
          ·
            have he : (⟨634, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 634 = i.val
              omega
            simpa only [he] using bucket0634
          ·
            have he : (⟨635, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 635 = i.val
              omega
            simpa only [he] using bucket0635
      ·
        by_cases h638 : i.val < 638
        ·
          by_cases h637 : i.val < 637
          ·
            have he : (⟨636, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 636 = i.val
              omega
            simpa only [he] using bucket0636
          ·
            have he : (⟨637, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 637 = i.val
              omega
            simpa only [he] using bucket0637
        ·
          by_cases h639 : i.val < 639
          ·
            have he : (⟨638, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 638 = i.val
              omega
            simpa only [he] using bucket0638
          ·
            have he : (⟨639, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 639 = i.val
              omega
            simpa only [he] using bucket0639

private theorem bucketGroup0020 (i : Fin 1069)
    (hlo : 640 ≤ i.val) (hhi : i.val < 672) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
  have hi_bound := i.isLt
  by_cases h656 : i.val < 656
  ·
    by_cases h648 : i.val < 648
    ·
      by_cases h644 : i.val < 644
      ·
        by_cases h642 : i.val < 642
        ·
          by_cases h641 : i.val < 641
          ·
            have he : (⟨640, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 640 = i.val
              omega
            simpa only [he] using bucket0640
          ·
            have he : (⟨641, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 641 = i.val
              omega
            simpa only [he] using bucket0641
        ·
          by_cases h643 : i.val < 643
          ·
            have he : (⟨642, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 642 = i.val
              omega
            simpa only [he] using bucket0642
          ·
            have he : (⟨643, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 643 = i.val
              omega
            simpa only [he] using bucket0643
      ·
        by_cases h646 : i.val < 646
        ·
          by_cases h645 : i.val < 645
          ·
            have he : (⟨644, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 644 = i.val
              omega
            simpa only [he] using bucket0644
          ·
            have he : (⟨645, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 645 = i.val
              omega
            simpa only [he] using bucket0645
        ·
          by_cases h647 : i.val < 647
          ·
            have he : (⟨646, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 646 = i.val
              omega
            simpa only [he] using bucket0646
          ·
            have he : (⟨647, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 647 = i.val
              omega
            simpa only [he] using bucket0647
    ·
      by_cases h652 : i.val < 652
      ·
        by_cases h650 : i.val < 650
        ·
          by_cases h649 : i.val < 649
          ·
            have he : (⟨648, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 648 = i.val
              omega
            simpa only [he] using bucket0648
          ·
            have he : (⟨649, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 649 = i.val
              omega
            simpa only [he] using bucket0649
        ·
          by_cases h651 : i.val < 651
          ·
            have he : (⟨650, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 650 = i.val
              omega
            simpa only [he] using bucket0650
          ·
            have he : (⟨651, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 651 = i.val
              omega
            simpa only [he] using bucket0651
      ·
        by_cases h654 : i.val < 654
        ·
          by_cases h653 : i.val < 653
          ·
            have he : (⟨652, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 652 = i.val
              omega
            simpa only [he] using bucket0652
          ·
            have he : (⟨653, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 653 = i.val
              omega
            simpa only [he] using bucket0653
        ·
          by_cases h655 : i.val < 655
          ·
            have he : (⟨654, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 654 = i.val
              omega
            simpa only [he] using bucket0654
          ·
            have he : (⟨655, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 655 = i.val
              omega
            simpa only [he] using bucket0655
  ·
    by_cases h664 : i.val < 664
    ·
      by_cases h660 : i.val < 660
      ·
        by_cases h658 : i.val < 658
        ·
          by_cases h657 : i.val < 657
          ·
            have he : (⟨656, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 656 = i.val
              omega
            simpa only [he] using bucket0656
          ·
            have he : (⟨657, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 657 = i.val
              omega
            simpa only [he] using bucket0657
        ·
          by_cases h659 : i.val < 659
          ·
            have he : (⟨658, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 658 = i.val
              omega
            simpa only [he] using bucket0658
          ·
            have he : (⟨659, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 659 = i.val
              omega
            simpa only [he] using bucket0659
      ·
        by_cases h662 : i.val < 662
        ·
          by_cases h661 : i.val < 661
          ·
            have he : (⟨660, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 660 = i.val
              omega
            simpa only [he] using bucket0660
          ·
            have he : (⟨661, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 661 = i.val
              omega
            simpa only [he] using bucket0661
        ·
          by_cases h663 : i.val < 663
          ·
            have he : (⟨662, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 662 = i.val
              omega
            simpa only [he] using bucket0662
          ·
            have he : (⟨663, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 663 = i.val
              omega
            simpa only [he] using bucket0663
    ·
      by_cases h668 : i.val < 668
      ·
        by_cases h666 : i.val < 666
        ·
          by_cases h665 : i.val < 665
          ·
            have he : (⟨664, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 664 = i.val
              omega
            simpa only [he] using bucket0664
          ·
            have he : (⟨665, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 665 = i.val
              omega
            simpa only [he] using bucket0665
        ·
          by_cases h667 : i.val < 667
          ·
            have he : (⟨666, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 666 = i.val
              omega
            simpa only [he] using bucket0666
          ·
            have he : (⟨667, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 667 = i.val
              omega
            simpa only [he] using bucket0667
      ·
        by_cases h670 : i.val < 670
        ·
          by_cases h669 : i.val < 669
          ·
            have he : (⟨668, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 668 = i.val
              omega
            simpa only [he] using bucket0668
          ·
            have he : (⟨669, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 669 = i.val
              omega
            simpa only [he] using bucket0669
        ·
          by_cases h671 : i.val < 671
          ·
            have he : (⟨670, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 670 = i.val
              omega
            simpa only [he] using bucket0670
          ·
            have he : (⟨671, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 671 = i.val
              omega
            simpa only [he] using bucket0671

private theorem bucketGroup0021 (i : Fin 1069)
    (hlo : 672 ≤ i.val) (hhi : i.val < 704) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
  have hi_bound := i.isLt
  by_cases h688 : i.val < 688
  ·
    by_cases h680 : i.val < 680
    ·
      by_cases h676 : i.val < 676
      ·
        by_cases h674 : i.val < 674
        ·
          by_cases h673 : i.val < 673
          ·
            have he : (⟨672, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 672 = i.val
              omega
            simpa only [he] using bucket0672
          ·
            have he : (⟨673, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 673 = i.val
              omega
            simpa only [he] using bucket0673
        ·
          by_cases h675 : i.val < 675
          ·
            have he : (⟨674, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 674 = i.val
              omega
            simpa only [he] using bucket0674
          ·
            have he : (⟨675, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 675 = i.val
              omega
            simpa only [he] using bucket0675
      ·
        by_cases h678 : i.val < 678
        ·
          by_cases h677 : i.val < 677
          ·
            have he : (⟨676, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 676 = i.val
              omega
            simpa only [he] using bucket0676
          ·
            have he : (⟨677, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 677 = i.val
              omega
            simpa only [he] using bucket0677
        ·
          by_cases h679 : i.val < 679
          ·
            have he : (⟨678, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 678 = i.val
              omega
            simpa only [he] using bucket0678
          ·
            have he : (⟨679, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 679 = i.val
              omega
            simpa only [he] using bucket0679
    ·
      by_cases h684 : i.val < 684
      ·
        by_cases h682 : i.val < 682
        ·
          by_cases h681 : i.val < 681
          ·
            have he : (⟨680, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 680 = i.val
              omega
            simpa only [he] using bucket0680
          ·
            have he : (⟨681, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 681 = i.val
              omega
            simpa only [he] using bucket0681
        ·
          by_cases h683 : i.val < 683
          ·
            have he : (⟨682, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 682 = i.val
              omega
            simpa only [he] using bucket0682
          ·
            have he : (⟨683, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 683 = i.val
              omega
            simpa only [he] using bucket0683
      ·
        by_cases h686 : i.val < 686
        ·
          by_cases h685 : i.val < 685
          ·
            have he : (⟨684, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 684 = i.val
              omega
            simpa only [he] using bucket0684
          ·
            have he : (⟨685, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 685 = i.val
              omega
            simpa only [he] using bucket0685
        ·
          by_cases h687 : i.val < 687
          ·
            have he : (⟨686, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 686 = i.val
              omega
            simpa only [he] using bucket0686
          ·
            have he : (⟨687, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 687 = i.val
              omega
            simpa only [he] using bucket0687
  ·
    by_cases h696 : i.val < 696
    ·
      by_cases h692 : i.val < 692
      ·
        by_cases h690 : i.val < 690
        ·
          by_cases h689 : i.val < 689
          ·
            have he : (⟨688, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 688 = i.val
              omega
            simpa only [he] using bucket0688
          ·
            have he : (⟨689, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 689 = i.val
              omega
            simpa only [he] using bucket0689
        ·
          by_cases h691 : i.val < 691
          ·
            have he : (⟨690, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 690 = i.val
              omega
            simpa only [he] using bucket0690
          ·
            have he : (⟨691, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 691 = i.val
              omega
            simpa only [he] using bucket0691
      ·
        by_cases h694 : i.val < 694
        ·
          by_cases h693 : i.val < 693
          ·
            have he : (⟨692, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 692 = i.val
              omega
            simpa only [he] using bucket0692
          ·
            have he : (⟨693, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 693 = i.val
              omega
            simpa only [he] using bucket0693
        ·
          by_cases h695 : i.val < 695
          ·
            have he : (⟨694, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 694 = i.val
              omega
            simpa only [he] using bucket0694
          ·
            have he : (⟨695, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 695 = i.val
              omega
            simpa only [he] using bucket0695
    ·
      by_cases h700 : i.val < 700
      ·
        by_cases h698 : i.val < 698
        ·
          by_cases h697 : i.val < 697
          ·
            have he : (⟨696, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 696 = i.val
              omega
            simpa only [he] using bucket0696
          ·
            have he : (⟨697, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 697 = i.val
              omega
            simpa only [he] using bucket0697
        ·
          by_cases h699 : i.val < 699
          ·
            have he : (⟨698, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 698 = i.val
              omega
            simpa only [he] using bucket0698
          ·
            have he : (⟨699, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 699 = i.val
              omega
            simpa only [he] using bucket0699
      ·
        by_cases h702 : i.val < 702
        ·
          by_cases h701 : i.val < 701
          ·
            have he : (⟨700, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 700 = i.val
              omega
            simpa only [he] using bucket0700
          ·
            have he : (⟨701, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 701 = i.val
              omega
            simpa only [he] using bucket0701
        ·
          by_cases h703 : i.val < 703
          ·
            have he : (⟨702, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 702 = i.val
              omega
            simpa only [he] using bucket0702
          ·
            have he : (⟨703, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 703 = i.val
              omega
            simpa only [he] using bucket0703

private theorem bucketGroup0022 (i : Fin 1069)
    (hlo : 704 ≤ i.val) (hhi : i.val < 736) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
  have hi_bound := i.isLt
  by_cases h720 : i.val < 720
  ·
    by_cases h712 : i.val < 712
    ·
      by_cases h708 : i.val < 708
      ·
        by_cases h706 : i.val < 706
        ·
          by_cases h705 : i.val < 705
          ·
            have he : (⟨704, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 704 = i.val
              omega
            simpa only [he] using bucket0704
          ·
            have he : (⟨705, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 705 = i.val
              omega
            simpa only [he] using bucket0705
        ·
          by_cases h707 : i.val < 707
          ·
            have he : (⟨706, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 706 = i.val
              omega
            simpa only [he] using bucket0706
          ·
            have he : (⟨707, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 707 = i.val
              omega
            simpa only [he] using bucket0707
      ·
        by_cases h710 : i.val < 710
        ·
          by_cases h709 : i.val < 709
          ·
            have he : (⟨708, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 708 = i.val
              omega
            simpa only [he] using bucket0708
          ·
            have he : (⟨709, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 709 = i.val
              omega
            simpa only [he] using bucket0709
        ·
          by_cases h711 : i.val < 711
          ·
            have he : (⟨710, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 710 = i.val
              omega
            simpa only [he] using bucket0710
          ·
            have he : (⟨711, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 711 = i.val
              omega
            simpa only [he] using bucket0711
    ·
      by_cases h716 : i.val < 716
      ·
        by_cases h714 : i.val < 714
        ·
          by_cases h713 : i.val < 713
          ·
            have he : (⟨712, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 712 = i.val
              omega
            simpa only [he] using bucket0712
          ·
            have he : (⟨713, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 713 = i.val
              omega
            simpa only [he] using bucket0713
        ·
          by_cases h715 : i.val < 715
          ·
            have he : (⟨714, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 714 = i.val
              omega
            simpa only [he] using bucket0714
          ·
            have he : (⟨715, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 715 = i.val
              omega
            simpa only [he] using bucket0715
      ·
        by_cases h718 : i.val < 718
        ·
          by_cases h717 : i.val < 717
          ·
            have he : (⟨716, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 716 = i.val
              omega
            simpa only [he] using bucket0716
          ·
            have he : (⟨717, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 717 = i.val
              omega
            simpa only [he] using bucket0717
        ·
          by_cases h719 : i.val < 719
          ·
            have he : (⟨718, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 718 = i.val
              omega
            simpa only [he] using bucket0718
          ·
            have he : (⟨719, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 719 = i.val
              omega
            simpa only [he] using bucket0719
  ·
    by_cases h728 : i.val < 728
    ·
      by_cases h724 : i.val < 724
      ·
        by_cases h722 : i.val < 722
        ·
          by_cases h721 : i.val < 721
          ·
            have he : (⟨720, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 720 = i.val
              omega
            simpa only [he] using bucket0720
          ·
            have he : (⟨721, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 721 = i.val
              omega
            simpa only [he] using bucket0721
        ·
          by_cases h723 : i.val < 723
          ·
            have he : (⟨722, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 722 = i.val
              omega
            simpa only [he] using bucket0722
          ·
            have he : (⟨723, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 723 = i.val
              omega
            simpa only [he] using bucket0723
      ·
        by_cases h726 : i.val < 726
        ·
          by_cases h725 : i.val < 725
          ·
            have he : (⟨724, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 724 = i.val
              omega
            simpa only [he] using bucket0724
          ·
            have he : (⟨725, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 725 = i.val
              omega
            simpa only [he] using bucket0725
        ·
          by_cases h727 : i.val < 727
          ·
            have he : (⟨726, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 726 = i.val
              omega
            simpa only [he] using bucket0726
          ·
            have he : (⟨727, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 727 = i.val
              omega
            simpa only [he] using bucket0727
    ·
      by_cases h732 : i.val < 732
      ·
        by_cases h730 : i.val < 730
        ·
          by_cases h729 : i.val < 729
          ·
            have he : (⟨728, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 728 = i.val
              omega
            simpa only [he] using bucket0728
          ·
            have he : (⟨729, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 729 = i.val
              omega
            simpa only [he] using bucket0729
        ·
          by_cases h731 : i.val < 731
          ·
            have he : (⟨730, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 730 = i.val
              omega
            simpa only [he] using bucket0730
          ·
            have he : (⟨731, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 731 = i.val
              omega
            simpa only [he] using bucket0731
      ·
        by_cases h734 : i.val < 734
        ·
          by_cases h733 : i.val < 733
          ·
            have he : (⟨732, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 732 = i.val
              omega
            simpa only [he] using bucket0732
          ·
            have he : (⟨733, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 733 = i.val
              omega
            simpa only [he] using bucket0733
        ·
          by_cases h735 : i.val < 735
          ·
            have he : (⟨734, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 734 = i.val
              omega
            simpa only [he] using bucket0734
          ·
            have he : (⟨735, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 735 = i.val
              omega
            simpa only [he] using bucket0735

private theorem bucketGroup0023 (i : Fin 1069)
    (hlo : 736 ≤ i.val) (hhi : i.val < 768) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
  have hi_bound := i.isLt
  by_cases h752 : i.val < 752
  ·
    by_cases h744 : i.val < 744
    ·
      by_cases h740 : i.val < 740
      ·
        by_cases h738 : i.val < 738
        ·
          by_cases h737 : i.val < 737
          ·
            have he : (⟨736, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 736 = i.val
              omega
            simpa only [he] using bucket0736
          ·
            have he : (⟨737, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 737 = i.val
              omega
            simpa only [he] using bucket0737
        ·
          by_cases h739 : i.val < 739
          ·
            have he : (⟨738, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 738 = i.val
              omega
            simpa only [he] using bucket0738
          ·
            have he : (⟨739, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 739 = i.val
              omega
            simpa only [he] using bucket0739
      ·
        by_cases h742 : i.val < 742
        ·
          by_cases h741 : i.val < 741
          ·
            have he : (⟨740, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 740 = i.val
              omega
            simpa only [he] using bucket0740
          ·
            have he : (⟨741, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 741 = i.val
              omega
            simpa only [he] using bucket0741
        ·
          by_cases h743 : i.val < 743
          ·
            have he : (⟨742, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 742 = i.val
              omega
            simpa only [he] using bucket0742
          ·
            have he : (⟨743, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 743 = i.val
              omega
            simpa only [he] using bucket0743
    ·
      by_cases h748 : i.val < 748
      ·
        by_cases h746 : i.val < 746
        ·
          by_cases h745 : i.val < 745
          ·
            have he : (⟨744, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 744 = i.val
              omega
            simpa only [he] using bucket0744
          ·
            have he : (⟨745, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 745 = i.val
              omega
            simpa only [he] using bucket0745
        ·
          by_cases h747 : i.val < 747
          ·
            have he : (⟨746, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 746 = i.val
              omega
            simpa only [he] using bucket0746
          ·
            have he : (⟨747, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 747 = i.val
              omega
            simpa only [he] using bucket0747
      ·
        by_cases h750 : i.val < 750
        ·
          by_cases h749 : i.val < 749
          ·
            have he : (⟨748, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 748 = i.val
              omega
            simpa only [he] using bucket0748
          ·
            have he : (⟨749, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 749 = i.val
              omega
            simpa only [he] using bucket0749
        ·
          by_cases h751 : i.val < 751
          ·
            have he : (⟨750, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 750 = i.val
              omega
            simpa only [he] using bucket0750
          ·
            have he : (⟨751, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 751 = i.val
              omega
            simpa only [he] using bucket0751
  ·
    by_cases h760 : i.val < 760
    ·
      by_cases h756 : i.val < 756
      ·
        by_cases h754 : i.val < 754
        ·
          by_cases h753 : i.val < 753
          ·
            have he : (⟨752, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 752 = i.val
              omega
            simpa only [he] using bucket0752
          ·
            have he : (⟨753, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 753 = i.val
              omega
            simpa only [he] using bucket0753
        ·
          by_cases h755 : i.val < 755
          ·
            have he : (⟨754, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 754 = i.val
              omega
            simpa only [he] using bucket0754
          ·
            have he : (⟨755, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 755 = i.val
              omega
            simpa only [he] using bucket0755
      ·
        by_cases h758 : i.val < 758
        ·
          by_cases h757 : i.val < 757
          ·
            have he : (⟨756, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 756 = i.val
              omega
            simpa only [he] using bucket0756
          ·
            have he : (⟨757, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 757 = i.val
              omega
            simpa only [he] using bucket0757
        ·
          by_cases h759 : i.val < 759
          ·
            have he : (⟨758, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 758 = i.val
              omega
            simpa only [he] using bucket0758
          ·
            have he : (⟨759, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 759 = i.val
              omega
            simpa only [he] using bucket0759
    ·
      by_cases h764 : i.val < 764
      ·
        by_cases h762 : i.val < 762
        ·
          by_cases h761 : i.val < 761
          ·
            have he : (⟨760, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 760 = i.val
              omega
            simpa only [he] using bucket0760
          ·
            have he : (⟨761, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 761 = i.val
              omega
            simpa only [he] using bucket0761
        ·
          by_cases h763 : i.val < 763
          ·
            have he : (⟨762, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 762 = i.val
              omega
            simpa only [he] using bucket0762
          ·
            have he : (⟨763, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 763 = i.val
              omega
            simpa only [he] using bucket0763
      ·
        by_cases h766 : i.val < 766
        ·
          by_cases h765 : i.val < 765
          ·
            have he : (⟨764, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 764 = i.val
              omega
            simpa only [he] using bucket0764
          ·
            have he : (⟨765, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 765 = i.val
              omega
            simpa only [he] using bucket0765
        ·
          by_cases h767 : i.val < 767
          ·
            have he : (⟨766, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 766 = i.val
              omega
            simpa only [he] using bucket0766
          ·
            have he : (⟨767, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 767 = i.val
              omega
            simpa only [he] using bucket0767

private theorem bucketGroup0024 (i : Fin 1069)
    (hlo : 768 ≤ i.val) (hhi : i.val < 800) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
  have hi_bound := i.isLt
  by_cases h784 : i.val < 784
  ·
    by_cases h776 : i.val < 776
    ·
      by_cases h772 : i.val < 772
      ·
        by_cases h770 : i.val < 770
        ·
          by_cases h769 : i.val < 769
          ·
            have he : (⟨768, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 768 = i.val
              omega
            simpa only [he] using bucket0768
          ·
            have he : (⟨769, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 769 = i.val
              omega
            simpa only [he] using bucket0769
        ·
          by_cases h771 : i.val < 771
          ·
            have he : (⟨770, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 770 = i.val
              omega
            simpa only [he] using bucket0770
          ·
            have he : (⟨771, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 771 = i.val
              omega
            simpa only [he] using bucket0771
      ·
        by_cases h774 : i.val < 774
        ·
          by_cases h773 : i.val < 773
          ·
            have he : (⟨772, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 772 = i.val
              omega
            simpa only [he] using bucket0772
          ·
            have he : (⟨773, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 773 = i.val
              omega
            simpa only [he] using bucket0773
        ·
          by_cases h775 : i.val < 775
          ·
            have he : (⟨774, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 774 = i.val
              omega
            simpa only [he] using bucket0774
          ·
            have he : (⟨775, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 775 = i.val
              omega
            simpa only [he] using bucket0775
    ·
      by_cases h780 : i.val < 780
      ·
        by_cases h778 : i.val < 778
        ·
          by_cases h777 : i.val < 777
          ·
            have he : (⟨776, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 776 = i.val
              omega
            simpa only [he] using bucket0776
          ·
            have he : (⟨777, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 777 = i.val
              omega
            simpa only [he] using bucket0777
        ·
          by_cases h779 : i.val < 779
          ·
            have he : (⟨778, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 778 = i.val
              omega
            simpa only [he] using bucket0778
          ·
            have he : (⟨779, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 779 = i.val
              omega
            simpa only [he] using bucket0779
      ·
        by_cases h782 : i.val < 782
        ·
          by_cases h781 : i.val < 781
          ·
            have he : (⟨780, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 780 = i.val
              omega
            simpa only [he] using bucket0780
          ·
            have he : (⟨781, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 781 = i.val
              omega
            simpa only [he] using bucket0781
        ·
          by_cases h783 : i.val < 783
          ·
            have he : (⟨782, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 782 = i.val
              omega
            simpa only [he] using bucket0782
          ·
            have he : (⟨783, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 783 = i.val
              omega
            simpa only [he] using bucket0783
  ·
    by_cases h792 : i.val < 792
    ·
      by_cases h788 : i.val < 788
      ·
        by_cases h786 : i.val < 786
        ·
          by_cases h785 : i.val < 785
          ·
            have he : (⟨784, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 784 = i.val
              omega
            simpa only [he] using bucket0784
          ·
            have he : (⟨785, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 785 = i.val
              omega
            simpa only [he] using bucket0785
        ·
          by_cases h787 : i.val < 787
          ·
            have he : (⟨786, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 786 = i.val
              omega
            simpa only [he] using bucket0786
          ·
            have he : (⟨787, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 787 = i.val
              omega
            simpa only [he] using bucket0787
      ·
        by_cases h790 : i.val < 790
        ·
          by_cases h789 : i.val < 789
          ·
            have he : (⟨788, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 788 = i.val
              omega
            simpa only [he] using bucket0788
          ·
            have he : (⟨789, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 789 = i.val
              omega
            simpa only [he] using bucket0789
        ·
          by_cases h791 : i.val < 791
          ·
            have he : (⟨790, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 790 = i.val
              omega
            simpa only [he] using bucket0790
          ·
            have he : (⟨791, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 791 = i.val
              omega
            simpa only [he] using bucket0791
    ·
      by_cases h796 : i.val < 796
      ·
        by_cases h794 : i.val < 794
        ·
          by_cases h793 : i.val < 793
          ·
            have he : (⟨792, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 792 = i.val
              omega
            simpa only [he] using bucket0792
          ·
            have he : (⟨793, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 793 = i.val
              omega
            simpa only [he] using bucket0793
        ·
          by_cases h795 : i.val < 795
          ·
            have he : (⟨794, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 794 = i.val
              omega
            simpa only [he] using bucket0794
          ·
            have he : (⟨795, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 795 = i.val
              omega
            simpa only [he] using bucket0795
      ·
        by_cases h798 : i.val < 798
        ·
          by_cases h797 : i.val < 797
          ·
            have he : (⟨796, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 796 = i.val
              omega
            simpa only [he] using bucket0796
          ·
            have he : (⟨797, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 797 = i.val
              omega
            simpa only [he] using bucket0797
        ·
          by_cases h799 : i.val < 799
          ·
            have he : (⟨798, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 798 = i.val
              omega
            simpa only [he] using bucket0798
          ·
            have he : (⟨799, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 799 = i.val
              omega
            simpa only [he] using bucket0799

private theorem bucketGroup0025 (i : Fin 1069)
    (hlo : 800 ≤ i.val) (hhi : i.val < 832) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
  have hi_bound := i.isLt
  by_cases h816 : i.val < 816
  ·
    by_cases h808 : i.val < 808
    ·
      by_cases h804 : i.val < 804
      ·
        by_cases h802 : i.val < 802
        ·
          by_cases h801 : i.val < 801
          ·
            have he : (⟨800, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 800 = i.val
              omega
            simpa only [he] using bucket0800
          ·
            have he : (⟨801, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 801 = i.val
              omega
            simpa only [he] using bucket0801
        ·
          by_cases h803 : i.val < 803
          ·
            have he : (⟨802, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 802 = i.val
              omega
            simpa only [he] using bucket0802
          ·
            have he : (⟨803, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 803 = i.val
              omega
            simpa only [he] using bucket0803
      ·
        by_cases h806 : i.val < 806
        ·
          by_cases h805 : i.val < 805
          ·
            have he : (⟨804, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 804 = i.val
              omega
            simpa only [he] using bucket0804
          ·
            have he : (⟨805, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 805 = i.val
              omega
            simpa only [he] using bucket0805
        ·
          by_cases h807 : i.val < 807
          ·
            have he : (⟨806, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 806 = i.val
              omega
            simpa only [he] using bucket0806
          ·
            have he : (⟨807, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 807 = i.val
              omega
            simpa only [he] using bucket0807
    ·
      by_cases h812 : i.val < 812
      ·
        by_cases h810 : i.val < 810
        ·
          by_cases h809 : i.val < 809
          ·
            have he : (⟨808, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 808 = i.val
              omega
            simpa only [he] using bucket0808
          ·
            have he : (⟨809, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 809 = i.val
              omega
            simpa only [he] using bucket0809
        ·
          by_cases h811 : i.val < 811
          ·
            have he : (⟨810, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 810 = i.val
              omega
            simpa only [he] using bucket0810
          ·
            have he : (⟨811, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 811 = i.val
              omega
            simpa only [he] using bucket0811
      ·
        by_cases h814 : i.val < 814
        ·
          by_cases h813 : i.val < 813
          ·
            have he : (⟨812, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 812 = i.val
              omega
            simpa only [he] using bucket0812
          ·
            have he : (⟨813, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 813 = i.val
              omega
            simpa only [he] using bucket0813
        ·
          by_cases h815 : i.val < 815
          ·
            have he : (⟨814, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 814 = i.val
              omega
            simpa only [he] using bucket0814
          ·
            have he : (⟨815, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 815 = i.val
              omega
            simpa only [he] using bucket0815
  ·
    by_cases h824 : i.val < 824
    ·
      by_cases h820 : i.val < 820
      ·
        by_cases h818 : i.val < 818
        ·
          by_cases h817 : i.val < 817
          ·
            have he : (⟨816, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 816 = i.val
              omega
            simpa only [he] using bucket0816
          ·
            have he : (⟨817, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 817 = i.val
              omega
            simpa only [he] using bucket0817
        ·
          by_cases h819 : i.val < 819
          ·
            have he : (⟨818, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 818 = i.val
              omega
            simpa only [he] using bucket0818
          ·
            have he : (⟨819, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 819 = i.val
              omega
            simpa only [he] using bucket0819
      ·
        by_cases h822 : i.val < 822
        ·
          by_cases h821 : i.val < 821
          ·
            have he : (⟨820, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 820 = i.val
              omega
            simpa only [he] using bucket0820
          ·
            have he : (⟨821, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 821 = i.val
              omega
            simpa only [he] using bucket0821
        ·
          by_cases h823 : i.val < 823
          ·
            have he : (⟨822, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 822 = i.val
              omega
            simpa only [he] using bucket0822
          ·
            have he : (⟨823, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 823 = i.val
              omega
            simpa only [he] using bucket0823
    ·
      by_cases h828 : i.val < 828
      ·
        by_cases h826 : i.val < 826
        ·
          by_cases h825 : i.val < 825
          ·
            have he : (⟨824, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 824 = i.val
              omega
            simpa only [he] using bucket0824
          ·
            have he : (⟨825, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 825 = i.val
              omega
            simpa only [he] using bucket0825
        ·
          by_cases h827 : i.val < 827
          ·
            have he : (⟨826, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 826 = i.val
              omega
            simpa only [he] using bucket0826
          ·
            have he : (⟨827, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 827 = i.val
              omega
            simpa only [he] using bucket0827
      ·
        by_cases h830 : i.val < 830
        ·
          by_cases h829 : i.val < 829
          ·
            have he : (⟨828, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 828 = i.val
              omega
            simpa only [he] using bucket0828
          ·
            have he : (⟨829, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 829 = i.val
              omega
            simpa only [he] using bucket0829
        ·
          by_cases h831 : i.val < 831
          ·
            have he : (⟨830, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 830 = i.val
              omega
            simpa only [he] using bucket0830
          ·
            have he : (⟨831, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 831 = i.val
              omega
            simpa only [he] using bucket0831

private theorem bucketGroup0026 (i : Fin 1069)
    (hlo : 832 ≤ i.val) (hhi : i.val < 864) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
  have hi_bound := i.isLt
  by_cases h848 : i.val < 848
  ·
    by_cases h840 : i.val < 840
    ·
      by_cases h836 : i.val < 836
      ·
        by_cases h834 : i.val < 834
        ·
          by_cases h833 : i.val < 833
          ·
            have he : (⟨832, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 832 = i.val
              omega
            simpa only [he] using bucket0832
          ·
            have he : (⟨833, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 833 = i.val
              omega
            simpa only [he] using bucket0833
        ·
          by_cases h835 : i.val < 835
          ·
            have he : (⟨834, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 834 = i.val
              omega
            simpa only [he] using bucket0834
          ·
            have he : (⟨835, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 835 = i.val
              omega
            simpa only [he] using bucket0835
      ·
        by_cases h838 : i.val < 838
        ·
          by_cases h837 : i.val < 837
          ·
            have he : (⟨836, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 836 = i.val
              omega
            simpa only [he] using bucket0836
          ·
            have he : (⟨837, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 837 = i.val
              omega
            simpa only [he] using bucket0837
        ·
          by_cases h839 : i.val < 839
          ·
            have he : (⟨838, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 838 = i.val
              omega
            simpa only [he] using bucket0838
          ·
            have he : (⟨839, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 839 = i.val
              omega
            simpa only [he] using bucket0839
    ·
      by_cases h844 : i.val < 844
      ·
        by_cases h842 : i.val < 842
        ·
          by_cases h841 : i.val < 841
          ·
            have he : (⟨840, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 840 = i.val
              omega
            simpa only [he] using bucket0840
          ·
            have he : (⟨841, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 841 = i.val
              omega
            simpa only [he] using bucket0841
        ·
          by_cases h843 : i.val < 843
          ·
            have he : (⟨842, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 842 = i.val
              omega
            simpa only [he] using bucket0842
          ·
            have he : (⟨843, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 843 = i.val
              omega
            simpa only [he] using bucket0843
      ·
        by_cases h846 : i.val < 846
        ·
          by_cases h845 : i.val < 845
          ·
            have he : (⟨844, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 844 = i.val
              omega
            simpa only [he] using bucket0844
          ·
            have he : (⟨845, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 845 = i.val
              omega
            simpa only [he] using bucket0845
        ·
          by_cases h847 : i.val < 847
          ·
            have he : (⟨846, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 846 = i.val
              omega
            simpa only [he] using bucket0846
          ·
            have he : (⟨847, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 847 = i.val
              omega
            simpa only [he] using bucket0847
  ·
    by_cases h856 : i.val < 856
    ·
      by_cases h852 : i.val < 852
      ·
        by_cases h850 : i.val < 850
        ·
          by_cases h849 : i.val < 849
          ·
            have he : (⟨848, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 848 = i.val
              omega
            simpa only [he] using bucket0848
          ·
            have he : (⟨849, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 849 = i.val
              omega
            simpa only [he] using bucket0849
        ·
          by_cases h851 : i.val < 851
          ·
            have he : (⟨850, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 850 = i.val
              omega
            simpa only [he] using bucket0850
          ·
            have he : (⟨851, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 851 = i.val
              omega
            simpa only [he] using bucket0851
      ·
        by_cases h854 : i.val < 854
        ·
          by_cases h853 : i.val < 853
          ·
            have he : (⟨852, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 852 = i.val
              omega
            simpa only [he] using bucket0852
          ·
            have he : (⟨853, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 853 = i.val
              omega
            simpa only [he] using bucket0853
        ·
          by_cases h855 : i.val < 855
          ·
            have he : (⟨854, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 854 = i.val
              omega
            simpa only [he] using bucket0854
          ·
            have he : (⟨855, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 855 = i.val
              omega
            simpa only [he] using bucket0855
    ·
      by_cases h860 : i.val < 860
      ·
        by_cases h858 : i.val < 858
        ·
          by_cases h857 : i.val < 857
          ·
            have he : (⟨856, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 856 = i.val
              omega
            simpa only [he] using bucket0856
          ·
            have he : (⟨857, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 857 = i.val
              omega
            simpa only [he] using bucket0857
        ·
          by_cases h859 : i.val < 859
          ·
            have he : (⟨858, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 858 = i.val
              omega
            simpa only [he] using bucket0858
          ·
            have he : (⟨859, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 859 = i.val
              omega
            simpa only [he] using bucket0859
      ·
        by_cases h862 : i.val < 862
        ·
          by_cases h861 : i.val < 861
          ·
            have he : (⟨860, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 860 = i.val
              omega
            simpa only [he] using bucket0860
          ·
            have he : (⟨861, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 861 = i.val
              omega
            simpa only [he] using bucket0861
        ·
          by_cases h863 : i.val < 863
          ·
            have he : (⟨862, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 862 = i.val
              omega
            simpa only [he] using bucket0862
          ·
            have he : (⟨863, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 863 = i.val
              omega
            simpa only [he] using bucket0863

private theorem bucketGroup0027 (i : Fin 1069)
    (hlo : 864 ≤ i.val) (hhi : i.val < 896) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
  have hi_bound := i.isLt
  by_cases h880 : i.val < 880
  ·
    by_cases h872 : i.val < 872
    ·
      by_cases h868 : i.val < 868
      ·
        by_cases h866 : i.val < 866
        ·
          by_cases h865 : i.val < 865
          ·
            have he : (⟨864, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 864 = i.val
              omega
            simpa only [he] using bucket0864
          ·
            have he : (⟨865, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 865 = i.val
              omega
            simpa only [he] using bucket0865
        ·
          by_cases h867 : i.val < 867
          ·
            have he : (⟨866, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 866 = i.val
              omega
            simpa only [he] using bucket0866
          ·
            have he : (⟨867, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 867 = i.val
              omega
            simpa only [he] using bucket0867
      ·
        by_cases h870 : i.val < 870
        ·
          by_cases h869 : i.val < 869
          ·
            have he : (⟨868, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 868 = i.val
              omega
            simpa only [he] using bucket0868
          ·
            have he : (⟨869, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 869 = i.val
              omega
            simpa only [he] using bucket0869
        ·
          by_cases h871 : i.val < 871
          ·
            have he : (⟨870, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 870 = i.val
              omega
            simpa only [he] using bucket0870
          ·
            have he : (⟨871, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 871 = i.val
              omega
            simpa only [he] using bucket0871
    ·
      by_cases h876 : i.val < 876
      ·
        by_cases h874 : i.val < 874
        ·
          by_cases h873 : i.val < 873
          ·
            have he : (⟨872, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 872 = i.val
              omega
            simpa only [he] using bucket0872
          ·
            have he : (⟨873, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 873 = i.val
              omega
            simpa only [he] using bucket0873
        ·
          by_cases h875 : i.val < 875
          ·
            have he : (⟨874, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 874 = i.val
              omega
            simpa only [he] using bucket0874
          ·
            have he : (⟨875, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 875 = i.val
              omega
            simpa only [he] using bucket0875
      ·
        by_cases h878 : i.val < 878
        ·
          by_cases h877 : i.val < 877
          ·
            have he : (⟨876, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 876 = i.val
              omega
            simpa only [he] using bucket0876
          ·
            have he : (⟨877, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 877 = i.val
              omega
            simpa only [he] using bucket0877
        ·
          by_cases h879 : i.val < 879
          ·
            have he : (⟨878, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 878 = i.val
              omega
            simpa only [he] using bucket0878
          ·
            have he : (⟨879, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 879 = i.val
              omega
            simpa only [he] using bucket0879
  ·
    by_cases h888 : i.val < 888
    ·
      by_cases h884 : i.val < 884
      ·
        by_cases h882 : i.val < 882
        ·
          by_cases h881 : i.val < 881
          ·
            have he : (⟨880, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 880 = i.val
              omega
            simpa only [he] using bucket0880
          ·
            have he : (⟨881, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 881 = i.val
              omega
            simpa only [he] using bucket0881
        ·
          by_cases h883 : i.val < 883
          ·
            have he : (⟨882, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 882 = i.val
              omega
            simpa only [he] using bucket0882
          ·
            have he : (⟨883, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 883 = i.val
              omega
            simpa only [he] using bucket0883
      ·
        by_cases h886 : i.val < 886
        ·
          by_cases h885 : i.val < 885
          ·
            have he : (⟨884, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 884 = i.val
              omega
            simpa only [he] using bucket0884
          ·
            have he : (⟨885, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 885 = i.val
              omega
            simpa only [he] using bucket0885
        ·
          by_cases h887 : i.val < 887
          ·
            have he : (⟨886, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 886 = i.val
              omega
            simpa only [he] using bucket0886
          ·
            have he : (⟨887, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 887 = i.val
              omega
            simpa only [he] using bucket0887
    ·
      by_cases h892 : i.val < 892
      ·
        by_cases h890 : i.val < 890
        ·
          by_cases h889 : i.val < 889
          ·
            have he : (⟨888, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 888 = i.val
              omega
            simpa only [he] using bucket0888
          ·
            have he : (⟨889, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 889 = i.val
              omega
            simpa only [he] using bucket0889
        ·
          by_cases h891 : i.val < 891
          ·
            have he : (⟨890, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 890 = i.val
              omega
            simpa only [he] using bucket0890
          ·
            have he : (⟨891, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 891 = i.val
              omega
            simpa only [he] using bucket0891
      ·
        by_cases h894 : i.val < 894
        ·
          by_cases h893 : i.val < 893
          ·
            have he : (⟨892, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 892 = i.val
              omega
            simpa only [he] using bucket0892
          ·
            have he : (⟨893, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 893 = i.val
              omega
            simpa only [he] using bucket0893
        ·
          by_cases h895 : i.val < 895
          ·
            have he : (⟨894, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 894 = i.val
              omega
            simpa only [he] using bucket0894
          ·
            have he : (⟨895, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 895 = i.val
              omega
            simpa only [he] using bucket0895

private theorem bucketGroup0028 (i : Fin 1069)
    (hlo : 896 ≤ i.val) (hhi : i.val < 928) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
  have hi_bound := i.isLt
  by_cases h912 : i.val < 912
  ·
    by_cases h904 : i.val < 904
    ·
      by_cases h900 : i.val < 900
      ·
        by_cases h898 : i.val < 898
        ·
          by_cases h897 : i.val < 897
          ·
            have he : (⟨896, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 896 = i.val
              omega
            simpa only [he] using bucket0896
          ·
            have he : (⟨897, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 897 = i.val
              omega
            simpa only [he] using bucket0897
        ·
          by_cases h899 : i.val < 899
          ·
            have he : (⟨898, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 898 = i.val
              omega
            simpa only [he] using bucket0898
          ·
            have he : (⟨899, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 899 = i.val
              omega
            simpa only [he] using bucket0899
      ·
        by_cases h902 : i.val < 902
        ·
          by_cases h901 : i.val < 901
          ·
            have he : (⟨900, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 900 = i.val
              omega
            simpa only [he] using bucket0900
          ·
            have he : (⟨901, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 901 = i.val
              omega
            simpa only [he] using bucket0901
        ·
          by_cases h903 : i.val < 903
          ·
            have he : (⟨902, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 902 = i.val
              omega
            simpa only [he] using bucket0902
          ·
            have he : (⟨903, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 903 = i.val
              omega
            simpa only [he] using bucket0903
    ·
      by_cases h908 : i.val < 908
      ·
        by_cases h906 : i.val < 906
        ·
          by_cases h905 : i.val < 905
          ·
            have he : (⟨904, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 904 = i.val
              omega
            simpa only [he] using bucket0904
          ·
            have he : (⟨905, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 905 = i.val
              omega
            simpa only [he] using bucket0905
        ·
          by_cases h907 : i.val < 907
          ·
            have he : (⟨906, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 906 = i.val
              omega
            simpa only [he] using bucket0906
          ·
            have he : (⟨907, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 907 = i.val
              omega
            simpa only [he] using bucket0907
      ·
        by_cases h910 : i.val < 910
        ·
          by_cases h909 : i.val < 909
          ·
            have he : (⟨908, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 908 = i.val
              omega
            simpa only [he] using bucket0908
          ·
            have he : (⟨909, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 909 = i.val
              omega
            simpa only [he] using bucket0909
        ·
          by_cases h911 : i.val < 911
          ·
            have he : (⟨910, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 910 = i.val
              omega
            simpa only [he] using bucket0910
          ·
            have he : (⟨911, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 911 = i.val
              omega
            simpa only [he] using bucket0911
  ·
    by_cases h920 : i.val < 920
    ·
      by_cases h916 : i.val < 916
      ·
        by_cases h914 : i.val < 914
        ·
          by_cases h913 : i.val < 913
          ·
            have he : (⟨912, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 912 = i.val
              omega
            simpa only [he] using bucket0912
          ·
            have he : (⟨913, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 913 = i.val
              omega
            simpa only [he] using bucket0913
        ·
          by_cases h915 : i.val < 915
          ·
            have he : (⟨914, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 914 = i.val
              omega
            simpa only [he] using bucket0914
          ·
            have he : (⟨915, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 915 = i.val
              omega
            simpa only [he] using bucket0915
      ·
        by_cases h918 : i.val < 918
        ·
          by_cases h917 : i.val < 917
          ·
            have he : (⟨916, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 916 = i.val
              omega
            simpa only [he] using bucket0916
          ·
            have he : (⟨917, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 917 = i.val
              omega
            simpa only [he] using bucket0917
        ·
          by_cases h919 : i.val < 919
          ·
            have he : (⟨918, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 918 = i.val
              omega
            simpa only [he] using bucket0918
          ·
            have he : (⟨919, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 919 = i.val
              omega
            simpa only [he] using bucket0919
    ·
      by_cases h924 : i.val < 924
      ·
        by_cases h922 : i.val < 922
        ·
          by_cases h921 : i.val < 921
          ·
            have he : (⟨920, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 920 = i.val
              omega
            simpa only [he] using bucket0920
          ·
            have he : (⟨921, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 921 = i.val
              omega
            simpa only [he] using bucket0921
        ·
          by_cases h923 : i.val < 923
          ·
            have he : (⟨922, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 922 = i.val
              omega
            simpa only [he] using bucket0922
          ·
            have he : (⟨923, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 923 = i.val
              omega
            simpa only [he] using bucket0923
      ·
        by_cases h926 : i.val < 926
        ·
          by_cases h925 : i.val < 925
          ·
            have he : (⟨924, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 924 = i.val
              omega
            simpa only [he] using bucket0924
          ·
            have he : (⟨925, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 925 = i.val
              omega
            simpa only [he] using bucket0925
        ·
          by_cases h927 : i.val < 927
          ·
            have he : (⟨926, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 926 = i.val
              omega
            simpa only [he] using bucket0926
          ·
            have he : (⟨927, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 927 = i.val
              omega
            simpa only [he] using bucket0927

private theorem bucketGroup0029 (i : Fin 1069)
    (hlo : 928 ≤ i.val) (hhi : i.val < 960) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
  have hi_bound := i.isLt
  by_cases h944 : i.val < 944
  ·
    by_cases h936 : i.val < 936
    ·
      by_cases h932 : i.val < 932
      ·
        by_cases h930 : i.val < 930
        ·
          by_cases h929 : i.val < 929
          ·
            have he : (⟨928, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 928 = i.val
              omega
            simpa only [he] using bucket0928
          ·
            have he : (⟨929, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 929 = i.val
              omega
            simpa only [he] using bucket0929
        ·
          by_cases h931 : i.val < 931
          ·
            have he : (⟨930, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 930 = i.val
              omega
            simpa only [he] using bucket0930
          ·
            have he : (⟨931, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 931 = i.val
              omega
            simpa only [he] using bucket0931
      ·
        by_cases h934 : i.val < 934
        ·
          by_cases h933 : i.val < 933
          ·
            have he : (⟨932, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 932 = i.val
              omega
            simpa only [he] using bucket0932
          ·
            have he : (⟨933, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 933 = i.val
              omega
            simpa only [he] using bucket0933
        ·
          by_cases h935 : i.val < 935
          ·
            have he : (⟨934, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 934 = i.val
              omega
            simpa only [he] using bucket0934
          ·
            have he : (⟨935, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 935 = i.val
              omega
            simpa only [he] using bucket0935
    ·
      by_cases h940 : i.val < 940
      ·
        by_cases h938 : i.val < 938
        ·
          by_cases h937 : i.val < 937
          ·
            have he : (⟨936, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 936 = i.val
              omega
            simpa only [he] using bucket0936
          ·
            have he : (⟨937, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 937 = i.val
              omega
            simpa only [he] using bucket0937
        ·
          by_cases h939 : i.val < 939
          ·
            have he : (⟨938, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 938 = i.val
              omega
            simpa only [he] using bucket0938
          ·
            have he : (⟨939, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 939 = i.val
              omega
            simpa only [he] using bucket0939
      ·
        by_cases h942 : i.val < 942
        ·
          by_cases h941 : i.val < 941
          ·
            have he : (⟨940, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 940 = i.val
              omega
            simpa only [he] using bucket0940
          ·
            have he : (⟨941, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 941 = i.val
              omega
            simpa only [he] using bucket0941
        ·
          by_cases h943 : i.val < 943
          ·
            have he : (⟨942, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 942 = i.val
              omega
            simpa only [he] using bucket0942
          ·
            have he : (⟨943, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 943 = i.val
              omega
            simpa only [he] using bucket0943
  ·
    by_cases h952 : i.val < 952
    ·
      by_cases h948 : i.val < 948
      ·
        by_cases h946 : i.val < 946
        ·
          by_cases h945 : i.val < 945
          ·
            have he : (⟨944, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 944 = i.val
              omega
            simpa only [he] using bucket0944
          ·
            have he : (⟨945, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 945 = i.val
              omega
            simpa only [he] using bucket0945
        ·
          by_cases h947 : i.val < 947
          ·
            have he : (⟨946, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 946 = i.val
              omega
            simpa only [he] using bucket0946
          ·
            have he : (⟨947, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 947 = i.val
              omega
            simpa only [he] using bucket0947
      ·
        by_cases h950 : i.val < 950
        ·
          by_cases h949 : i.val < 949
          ·
            have he : (⟨948, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 948 = i.val
              omega
            simpa only [he] using bucket0948
          ·
            have he : (⟨949, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 949 = i.val
              omega
            simpa only [he] using bucket0949
        ·
          by_cases h951 : i.val < 951
          ·
            have he : (⟨950, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 950 = i.val
              omega
            simpa only [he] using bucket0950
          ·
            have he : (⟨951, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 951 = i.val
              omega
            simpa only [he] using bucket0951
    ·
      by_cases h956 : i.val < 956
      ·
        by_cases h954 : i.val < 954
        ·
          by_cases h953 : i.val < 953
          ·
            have he : (⟨952, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 952 = i.val
              omega
            simpa only [he] using bucket0952
          ·
            have he : (⟨953, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 953 = i.val
              omega
            simpa only [he] using bucket0953
        ·
          by_cases h955 : i.val < 955
          ·
            have he : (⟨954, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 954 = i.val
              omega
            simpa only [he] using bucket0954
          ·
            have he : (⟨955, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 955 = i.val
              omega
            simpa only [he] using bucket0955
      ·
        by_cases h958 : i.val < 958
        ·
          by_cases h957 : i.val < 957
          ·
            have he : (⟨956, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 956 = i.val
              omega
            simpa only [he] using bucket0956
          ·
            have he : (⟨957, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 957 = i.val
              omega
            simpa only [he] using bucket0957
        ·
          by_cases h959 : i.val < 959
          ·
            have he : (⟨958, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 958 = i.val
              omega
            simpa only [he] using bucket0958
          ·
            have he : (⟨959, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 959 = i.val
              omega
            simpa only [he] using bucket0959

private theorem bucketGroup0030 (i : Fin 1069)
    (hlo : 960 ≤ i.val) (hhi : i.val < 992) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
  have hi_bound := i.isLt
  by_cases h976 : i.val < 976
  ·
    by_cases h968 : i.val < 968
    ·
      by_cases h964 : i.val < 964
      ·
        by_cases h962 : i.val < 962
        ·
          by_cases h961 : i.val < 961
          ·
            have he : (⟨960, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 960 = i.val
              omega
            simpa only [he] using bucket0960
          ·
            have he : (⟨961, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 961 = i.val
              omega
            simpa only [he] using bucket0961
        ·
          by_cases h963 : i.val < 963
          ·
            have he : (⟨962, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 962 = i.val
              omega
            simpa only [he] using bucket0962
          ·
            have he : (⟨963, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 963 = i.val
              omega
            simpa only [he] using bucket0963
      ·
        by_cases h966 : i.val < 966
        ·
          by_cases h965 : i.val < 965
          ·
            have he : (⟨964, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 964 = i.val
              omega
            simpa only [he] using bucket0964
          ·
            have he : (⟨965, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 965 = i.val
              omega
            simpa only [he] using bucket0965
        ·
          by_cases h967 : i.val < 967
          ·
            have he : (⟨966, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 966 = i.val
              omega
            simpa only [he] using bucket0966
          ·
            have he : (⟨967, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 967 = i.val
              omega
            simpa only [he] using bucket0967
    ·
      by_cases h972 : i.val < 972
      ·
        by_cases h970 : i.val < 970
        ·
          by_cases h969 : i.val < 969
          ·
            have he : (⟨968, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 968 = i.val
              omega
            simpa only [he] using bucket0968
          ·
            have he : (⟨969, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 969 = i.val
              omega
            simpa only [he] using bucket0969
        ·
          by_cases h971 : i.val < 971
          ·
            have he : (⟨970, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 970 = i.val
              omega
            simpa only [he] using bucket0970
          ·
            have he : (⟨971, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 971 = i.val
              omega
            simpa only [he] using bucket0971
      ·
        by_cases h974 : i.val < 974
        ·
          by_cases h973 : i.val < 973
          ·
            have he : (⟨972, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 972 = i.val
              omega
            simpa only [he] using bucket0972
          ·
            have he : (⟨973, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 973 = i.val
              omega
            simpa only [he] using bucket0973
        ·
          by_cases h975 : i.val < 975
          ·
            have he : (⟨974, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 974 = i.val
              omega
            simpa only [he] using bucket0974
          ·
            have he : (⟨975, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 975 = i.val
              omega
            simpa only [he] using bucket0975
  ·
    by_cases h984 : i.val < 984
    ·
      by_cases h980 : i.val < 980
      ·
        by_cases h978 : i.val < 978
        ·
          by_cases h977 : i.val < 977
          ·
            have he : (⟨976, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 976 = i.val
              omega
            simpa only [he] using bucket0976
          ·
            have he : (⟨977, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 977 = i.val
              omega
            simpa only [he] using bucket0977
        ·
          by_cases h979 : i.val < 979
          ·
            have he : (⟨978, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 978 = i.val
              omega
            simpa only [he] using bucket0978
          ·
            have he : (⟨979, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 979 = i.val
              omega
            simpa only [he] using bucket0979
      ·
        by_cases h982 : i.val < 982
        ·
          by_cases h981 : i.val < 981
          ·
            have he : (⟨980, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 980 = i.val
              omega
            simpa only [he] using bucket0980
          ·
            have he : (⟨981, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 981 = i.val
              omega
            simpa only [he] using bucket0981
        ·
          by_cases h983 : i.val < 983
          ·
            have he : (⟨982, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 982 = i.val
              omega
            simpa only [he] using bucket0982
          ·
            have he : (⟨983, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 983 = i.val
              omega
            simpa only [he] using bucket0983
    ·
      by_cases h988 : i.val < 988
      ·
        by_cases h986 : i.val < 986
        ·
          by_cases h985 : i.val < 985
          ·
            have he : (⟨984, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 984 = i.val
              omega
            simpa only [he] using bucket0984
          ·
            have he : (⟨985, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 985 = i.val
              omega
            simpa only [he] using bucket0985
        ·
          by_cases h987 : i.val < 987
          ·
            have he : (⟨986, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 986 = i.val
              omega
            simpa only [he] using bucket0986
          ·
            have he : (⟨987, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 987 = i.val
              omega
            simpa only [he] using bucket0987
      ·
        by_cases h990 : i.val < 990
        ·
          by_cases h989 : i.val < 989
          ·
            have he : (⟨988, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 988 = i.val
              omega
            simpa only [he] using bucket0988
          ·
            have he : (⟨989, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 989 = i.val
              omega
            simpa only [he] using bucket0989
        ·
          by_cases h991 : i.val < 991
          ·
            have he : (⟨990, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 990 = i.val
              omega
            simpa only [he] using bucket0990
          ·
            have he : (⟨991, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 991 = i.val
              omega
            simpa only [he] using bucket0991

private theorem bucketGroup0031 (i : Fin 1069)
    (hlo : 992 ≤ i.val) (hhi : i.val < 1024) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
  have hi_bound := i.isLt
  by_cases h1008 : i.val < 1008
  ·
    by_cases h1000 : i.val < 1000
    ·
      by_cases h996 : i.val < 996
      ·
        by_cases h994 : i.val < 994
        ·
          by_cases h993 : i.val < 993
          ·
            have he : (⟨992, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 992 = i.val
              omega
            simpa only [he] using bucket0992
          ·
            have he : (⟨993, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 993 = i.val
              omega
            simpa only [he] using bucket0993
        ·
          by_cases h995 : i.val < 995
          ·
            have he : (⟨994, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 994 = i.val
              omega
            simpa only [he] using bucket0994
          ·
            have he : (⟨995, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 995 = i.val
              omega
            simpa only [he] using bucket0995
      ·
        by_cases h998 : i.val < 998
        ·
          by_cases h997 : i.val < 997
          ·
            have he : (⟨996, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 996 = i.val
              omega
            simpa only [he] using bucket0996
          ·
            have he : (⟨997, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 997 = i.val
              omega
            simpa only [he] using bucket0997
        ·
          by_cases h999 : i.val < 999
          ·
            have he : (⟨998, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 998 = i.val
              omega
            simpa only [he] using bucket0998
          ·
            have he : (⟨999, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 999 = i.val
              omega
            simpa only [he] using bucket0999
    ·
      by_cases h1004 : i.val < 1004
      ·
        by_cases h1002 : i.val < 1002
        ·
          by_cases h1001 : i.val < 1001
          ·
            have he : (⟨1000, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1000 = i.val
              omega
            simpa only [he] using bucket1000
          ·
            have he : (⟨1001, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1001 = i.val
              omega
            simpa only [he] using bucket1001
        ·
          by_cases h1003 : i.val < 1003
          ·
            have he : (⟨1002, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1002 = i.val
              omega
            simpa only [he] using bucket1002
          ·
            have he : (⟨1003, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1003 = i.val
              omega
            simpa only [he] using bucket1003
      ·
        by_cases h1006 : i.val < 1006
        ·
          by_cases h1005 : i.val < 1005
          ·
            have he : (⟨1004, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1004 = i.val
              omega
            simpa only [he] using bucket1004
          ·
            have he : (⟨1005, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1005 = i.val
              omega
            simpa only [he] using bucket1005
        ·
          by_cases h1007 : i.val < 1007
          ·
            have he : (⟨1006, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1006 = i.val
              omega
            simpa only [he] using bucket1006
          ·
            have he : (⟨1007, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1007 = i.val
              omega
            simpa only [he] using bucket1007
  ·
    by_cases h1016 : i.val < 1016
    ·
      by_cases h1012 : i.val < 1012
      ·
        by_cases h1010 : i.val < 1010
        ·
          by_cases h1009 : i.val < 1009
          ·
            have he : (⟨1008, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1008 = i.val
              omega
            simpa only [he] using bucket1008
          ·
            have he : (⟨1009, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1009 = i.val
              omega
            simpa only [he] using bucket1009
        ·
          by_cases h1011 : i.val < 1011
          ·
            have he : (⟨1010, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1010 = i.val
              omega
            simpa only [he] using bucket1010
          ·
            have he : (⟨1011, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1011 = i.val
              omega
            simpa only [he] using bucket1011
      ·
        by_cases h1014 : i.val < 1014
        ·
          by_cases h1013 : i.val < 1013
          ·
            have he : (⟨1012, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1012 = i.val
              omega
            simpa only [he] using bucket1012
          ·
            have he : (⟨1013, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1013 = i.val
              omega
            simpa only [he] using bucket1013
        ·
          by_cases h1015 : i.val < 1015
          ·
            have he : (⟨1014, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1014 = i.val
              omega
            simpa only [he] using bucket1014
          ·
            have he : (⟨1015, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1015 = i.val
              omega
            simpa only [he] using bucket1015
    ·
      by_cases h1020 : i.val < 1020
      ·
        by_cases h1018 : i.val < 1018
        ·
          by_cases h1017 : i.val < 1017
          ·
            have he : (⟨1016, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1016 = i.val
              omega
            simpa only [he] using bucket1016
          ·
            have he : (⟨1017, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1017 = i.val
              omega
            simpa only [he] using bucket1017
        ·
          by_cases h1019 : i.val < 1019
          ·
            have he : (⟨1018, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1018 = i.val
              omega
            simpa only [he] using bucket1018
          ·
            have he : (⟨1019, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1019 = i.val
              omega
            simpa only [he] using bucket1019
      ·
        by_cases h1022 : i.val < 1022
        ·
          by_cases h1021 : i.val < 1021
          ·
            have he : (⟨1020, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1020 = i.val
              omega
            simpa only [he] using bucket1020
          ·
            have he : (⟨1021, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1021 = i.val
              omega
            simpa only [he] using bucket1021
        ·
          by_cases h1023 : i.val < 1023
          ·
            have he : (⟨1022, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1022 = i.val
              omega
            simpa only [he] using bucket1022
          ·
            have he : (⟨1023, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1023 = i.val
              omega
            simpa only [he] using bucket1023

private theorem bucketGroup0032 (i : Fin 1069)
    (hlo : 1024 ≤ i.val) (hhi : i.val < 1056) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
  have hi_bound := i.isLt
  by_cases h1040 : i.val < 1040
  ·
    by_cases h1032 : i.val < 1032
    ·
      by_cases h1028 : i.val < 1028
      ·
        by_cases h1026 : i.val < 1026
        ·
          by_cases h1025 : i.val < 1025
          ·
            have he : (⟨1024, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1024 = i.val
              omega
            simpa only [he] using bucket1024
          ·
            have he : (⟨1025, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1025 = i.val
              omega
            simpa only [he] using bucket1025
        ·
          by_cases h1027 : i.val < 1027
          ·
            have he : (⟨1026, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1026 = i.val
              omega
            simpa only [he] using bucket1026
          ·
            have he : (⟨1027, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1027 = i.val
              omega
            simpa only [he] using bucket1027
      ·
        by_cases h1030 : i.val < 1030
        ·
          by_cases h1029 : i.val < 1029
          ·
            have he : (⟨1028, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1028 = i.val
              omega
            simpa only [he] using bucket1028
          ·
            have he : (⟨1029, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1029 = i.val
              omega
            simpa only [he] using bucket1029
        ·
          by_cases h1031 : i.val < 1031
          ·
            have he : (⟨1030, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1030 = i.val
              omega
            simpa only [he] using bucket1030
          ·
            have he : (⟨1031, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1031 = i.val
              omega
            simpa only [he] using bucket1031
    ·
      by_cases h1036 : i.val < 1036
      ·
        by_cases h1034 : i.val < 1034
        ·
          by_cases h1033 : i.val < 1033
          ·
            have he : (⟨1032, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1032 = i.val
              omega
            simpa only [he] using bucket1032
          ·
            have he : (⟨1033, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1033 = i.val
              omega
            simpa only [he] using bucket1033
        ·
          by_cases h1035 : i.val < 1035
          ·
            have he : (⟨1034, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1034 = i.val
              omega
            simpa only [he] using bucket1034
          ·
            have he : (⟨1035, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1035 = i.val
              omega
            simpa only [he] using bucket1035
      ·
        by_cases h1038 : i.val < 1038
        ·
          by_cases h1037 : i.val < 1037
          ·
            have he : (⟨1036, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1036 = i.val
              omega
            simpa only [he] using bucket1036
          ·
            have he : (⟨1037, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1037 = i.val
              omega
            simpa only [he] using bucket1037
        ·
          by_cases h1039 : i.val < 1039
          ·
            have he : (⟨1038, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1038 = i.val
              omega
            simpa only [he] using bucket1038
          ·
            have he : (⟨1039, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1039 = i.val
              omega
            simpa only [he] using bucket1039
  ·
    by_cases h1048 : i.val < 1048
    ·
      by_cases h1044 : i.val < 1044
      ·
        by_cases h1042 : i.val < 1042
        ·
          by_cases h1041 : i.val < 1041
          ·
            have he : (⟨1040, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1040 = i.val
              omega
            simpa only [he] using bucket1040
          ·
            have he : (⟨1041, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1041 = i.val
              omega
            simpa only [he] using bucket1041
        ·
          by_cases h1043 : i.val < 1043
          ·
            have he : (⟨1042, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1042 = i.val
              omega
            simpa only [he] using bucket1042
          ·
            have he : (⟨1043, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1043 = i.val
              omega
            simpa only [he] using bucket1043
      ·
        by_cases h1046 : i.val < 1046
        ·
          by_cases h1045 : i.val < 1045
          ·
            have he : (⟨1044, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1044 = i.val
              omega
            simpa only [he] using bucket1044
          ·
            have he : (⟨1045, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1045 = i.val
              omega
            simpa only [he] using bucket1045
        ·
          by_cases h1047 : i.val < 1047
          ·
            have he : (⟨1046, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1046 = i.val
              omega
            simpa only [he] using bucket1046
          ·
            have he : (⟨1047, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1047 = i.val
              omega
            simpa only [he] using bucket1047
    ·
      by_cases h1052 : i.val < 1052
      ·
        by_cases h1050 : i.val < 1050
        ·
          by_cases h1049 : i.val < 1049
          ·
            have he : (⟨1048, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1048 = i.val
              omega
            simpa only [he] using bucket1048
          ·
            have he : (⟨1049, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1049 = i.val
              omega
            simpa only [he] using bucket1049
        ·
          by_cases h1051 : i.val < 1051
          ·
            have he : (⟨1050, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1050 = i.val
              omega
            simpa only [he] using bucket1050
          ·
            have he : (⟨1051, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1051 = i.val
              omega
            simpa only [he] using bucket1051
      ·
        by_cases h1054 : i.val < 1054
        ·
          by_cases h1053 : i.val < 1053
          ·
            have he : (⟨1052, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1052 = i.val
              omega
            simpa only [he] using bucket1052
          ·
            have he : (⟨1053, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1053 = i.val
              omega
            simpa only [he] using bucket1053
        ·
          by_cases h1055 : i.val < 1055
          ·
            have he : (⟨1054, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1054 = i.val
              omega
            simpa only [he] using bucket1054
          ·
            have he : (⟨1055, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1055 = i.val
              omega
            simpa only [he] using bucket1055

private theorem bucketGroup0033 (i : Fin 1069)
    (hlo : 1056 ≤ i.val) (hhi : i.val < 1069) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
  have hi_bound := i.isLt
  by_cases h1062 : i.val < 1062
  ·
    by_cases h1059 : i.val < 1059
    ·
      by_cases h1057 : i.val < 1057
      ·
        have he : (⟨1056, by decide⟩ : Fin 1069) = i := by
          apply Fin.ext
          change 1056 = i.val
          omega
        simpa only [he] using bucket1056
      ·
        by_cases h1058 : i.val < 1058
        ·
          have he : (⟨1057, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1057 = i.val
            omega
          simpa only [he] using bucket1057
        ·
          have he : (⟨1058, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1058 = i.val
            omega
          simpa only [he] using bucket1058
    ·
      by_cases h1060 : i.val < 1060
      ·
        have he : (⟨1059, by decide⟩ : Fin 1069) = i := by
          apply Fin.ext
          change 1059 = i.val
          omega
        simpa only [he] using bucket1059
      ·
        by_cases h1061 : i.val < 1061
        ·
          have he : (⟨1060, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1060 = i.val
            omega
          simpa only [he] using bucket1060
        ·
          have he : (⟨1061, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1061 = i.val
            omega
          simpa only [he] using bucket1061
  ·
    by_cases h1065 : i.val < 1065
    ·
      by_cases h1063 : i.val < 1063
      ·
        have he : (⟨1062, by decide⟩ : Fin 1069) = i := by
          apply Fin.ext
          change 1062 = i.val
          omega
        simpa only [he] using bucket1062
      ·
        by_cases h1064 : i.val < 1064
        ·
          have he : (⟨1063, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1063 = i.val
            omega
          simpa only [he] using bucket1063
        ·
          have he : (⟨1064, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1064 = i.val
            omega
          simpa only [he] using bucket1064
    ·
      by_cases h1067 : i.val < 1067
      ·
        by_cases h1066 : i.val < 1066
        ·
          have he : (⟨1065, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1065 = i.val
            omega
          simpa only [he] using bucket1065
        ·
          have he : (⟨1066, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1066 = i.val
            omega
          simpa only [he] using bucket1066
      ·
        by_cases h1068 : i.val < 1068
        ·
          have he : (⟨1067, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1067 = i.val
            omega
          simpa only [he] using bucket1067
        ·
          have he : (⟨1068, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1068 = i.val
            omega
          simpa only [he] using bucket1068

private theorem anchoredFaces_self : ∀ i : Fin 1069,
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
  intro i
  have hi_bound := i.isLt
  by_cases h544 : i.val < 544
  ·
    by_cases h256 : i.val < 256
    ·
      by_cases h128 : i.val < 128
      ·
        by_cases h64 : i.val < 64
        ·
          by_cases h32 : i.val < 32
          ·
            exact bucketGroup0000 i (by omega) (by omega)
          ·
            exact bucketGroup0001 i (by omega) (by omega)
        ·
          by_cases h96 : i.val < 96
          ·
            exact bucketGroup0002 i (by omega) (by omega)
          ·
            exact bucketGroup0003 i (by omega) (by omega)
      ·
        by_cases h192 : i.val < 192
        ·
          by_cases h160 : i.val < 160
          ·
            exact bucketGroup0004 i (by omega) (by omega)
          ·
            exact bucketGroup0005 i (by omega) (by omega)
        ·
          by_cases h224 : i.val < 224
          ·
            exact bucketGroup0006 i (by omega) (by omega)
          ·
            exact bucketGroup0007 i (by omega) (by omega)
    ·
      by_cases h384 : i.val < 384
      ·
        by_cases h320 : i.val < 320
        ·
          by_cases h288 : i.val < 288
          ·
            exact bucketGroup0008 i (by omega) (by omega)
          ·
            exact bucketGroup0009 i (by omega) (by omega)
        ·
          by_cases h352 : i.val < 352
          ·
            exact bucketGroup0010 i (by omega) (by omega)
          ·
            exact bucketGroup0011 i (by omega) (by omega)
      ·
        by_cases h448 : i.val < 448
        ·
          by_cases h416 : i.val < 416
          ·
            exact bucketGroup0012 i (by omega) (by omega)
          ·
            exact bucketGroup0013 i (by omega) (by omega)
        ·
          by_cases h480 : i.val < 480
          ·
            exact bucketGroup0014 i (by omega) (by omega)
          ·
            by_cases h512 : i.val < 512
            ·
              exact bucketGroup0015 i (by omega) (by omega)
            ·
              exact bucketGroup0016 i (by omega) (by omega)
  ·
    by_cases h800 : i.val < 800
    ·
      by_cases h672 : i.val < 672
      ·
        by_cases h608 : i.val < 608
        ·
          by_cases h576 : i.val < 576
          ·
            exact bucketGroup0017 i (by omega) (by omega)
          ·
            exact bucketGroup0018 i (by omega) (by omega)
        ·
          by_cases h640 : i.val < 640
          ·
            exact bucketGroup0019 i (by omega) (by omega)
          ·
            exact bucketGroup0020 i (by omega) (by omega)
      ·
        by_cases h736 : i.val < 736
        ·
          by_cases h704 : i.val < 704
          ·
            exact bucketGroup0021 i (by omega) (by omega)
          ·
            exact bucketGroup0022 i (by omega) (by omega)
        ·
          by_cases h768 : i.val < 768
          ·
            exact bucketGroup0023 i (by omega) (by omega)
          ·
            exact bucketGroup0024 i (by omega) (by omega)
    ·
      by_cases h928 : i.val < 928
      ·
        by_cases h864 : i.val < 864
        ·
          by_cases h832 : i.val < 832
          ·
            exact bucketGroup0025 i (by omega) (by omega)
          ·
            exact bucketGroup0026 i (by omega) (by omega)
        ·
          by_cases h896 : i.val < 896
          ·
            exact bucketGroup0027 i (by omega) (by omega)
          ·
            exact bucketGroup0028 i (by omega) (by omega)
      ·
        by_cases h992 : i.val < 992
        ·
          by_cases h960 : i.val < 960
          ·
            exact bucketGroup0029 i (by omega) (by omega)
          ·
            exact bucketGroup0030 i (by omega) (by omega)
        ·
          by_cases h1024 : i.val < 1024
          ·
            exact bucketGroup0031 i (by omega) (by omega)
          ·
            by_cases h1056 : i.val < 1056
            ·
              exact bucketGroup0032 i (by omega) (by omega)
            ·
              exact bucketGroup0033 i (by omega) (by omega)

private def previousRank (i : Fin 1069) : Fin 5 :=
  ⟨(faceRank i).val - 1, by have h := (faceRank i).isLt; omega⟩

private def lowerCandidates (i : Fin 1069) : Finset (Fin 1069) :=
  (faceMask i).biUnion (anchoredFaces (previousRank i))

private def lowerComputed (i : Fin 1069) : Finset (Fin 1069) :=
  (lowerCandidates i).filter
    (fun j => (faceRank j).val + 1 = (faceRank i).val ∧ faceMask j ⊆ faceMask i)

private theorem lower0000 : lowerComputed (⟨0, by decide⟩ : Fin 1069) = lowerFacets (⟨0, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0001 : lowerComputed (⟨1, by decide⟩ : Fin 1069) = lowerFacets (⟨1, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0002 : lowerComputed (⟨2, by decide⟩ : Fin 1069) = lowerFacets (⟨2, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0003 : lowerComputed (⟨3, by decide⟩ : Fin 1069) = lowerFacets (⟨3, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0004 : lowerComputed (⟨4, by decide⟩ : Fin 1069) = lowerFacets (⟨4, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0005 : lowerComputed (⟨5, by decide⟩ : Fin 1069) = lowerFacets (⟨5, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0006 : lowerComputed (⟨6, by decide⟩ : Fin 1069) = lowerFacets (⟨6, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0007 : lowerComputed (⟨7, by decide⟩ : Fin 1069) = lowerFacets (⟨7, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0008 : lowerComputed (⟨8, by decide⟩ : Fin 1069) = lowerFacets (⟨8, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0009 : lowerComputed (⟨9, by decide⟩ : Fin 1069) = lowerFacets (⟨9, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0010 : lowerComputed (⟨10, by decide⟩ : Fin 1069) = lowerFacets (⟨10, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0011 : lowerComputed (⟨11, by decide⟩ : Fin 1069) = lowerFacets (⟨11, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0012 : lowerComputed (⟨12, by decide⟩ : Fin 1069) = lowerFacets (⟨12, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0013 : lowerComputed (⟨13, by decide⟩ : Fin 1069) = lowerFacets (⟨13, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0014 : lowerComputed (⟨14, by decide⟩ : Fin 1069) = lowerFacets (⟨14, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0015 : lowerComputed (⟨15, by decide⟩ : Fin 1069) = lowerFacets (⟨15, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0016 : lowerComputed (⟨16, by decide⟩ : Fin 1069) = lowerFacets (⟨16, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0017 : lowerComputed (⟨17, by decide⟩ : Fin 1069) = lowerFacets (⟨17, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0018 : lowerComputed (⟨18, by decide⟩ : Fin 1069) = lowerFacets (⟨18, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0019 : lowerComputed (⟨19, by decide⟩ : Fin 1069) = lowerFacets (⟨19, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0020 : lowerComputed (⟨20, by decide⟩ : Fin 1069) = lowerFacets (⟨20, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0021 : lowerComputed (⟨21, by decide⟩ : Fin 1069) = lowerFacets (⟨21, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0022 : lowerComputed (⟨22, by decide⟩ : Fin 1069) = lowerFacets (⟨22, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0023 : lowerComputed (⟨23, by decide⟩ : Fin 1069) = lowerFacets (⟨23, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0024 : lowerComputed (⟨24, by decide⟩ : Fin 1069) = lowerFacets (⟨24, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0025 : lowerComputed (⟨25, by decide⟩ : Fin 1069) = lowerFacets (⟨25, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0026 : lowerComputed (⟨26, by decide⟩ : Fin 1069) = lowerFacets (⟨26, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0027 : lowerComputed (⟨27, by decide⟩ : Fin 1069) = lowerFacets (⟨27, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0028 : lowerComputed (⟨28, by decide⟩ : Fin 1069) = lowerFacets (⟨28, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0029 : lowerComputed (⟨29, by decide⟩ : Fin 1069) = lowerFacets (⟨29, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0030 : lowerComputed (⟨30, by decide⟩ : Fin 1069) = lowerFacets (⟨30, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0031 : lowerComputed (⟨31, by decide⟩ : Fin 1069) = lowerFacets (⟨31, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0032 : lowerComputed (⟨32, by decide⟩ : Fin 1069) = lowerFacets (⟨32, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0033 : lowerComputed (⟨33, by decide⟩ : Fin 1069) = lowerFacets (⟨33, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0034 : lowerComputed (⟨34, by decide⟩ : Fin 1069) = lowerFacets (⟨34, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0035 : lowerComputed (⟨35, by decide⟩ : Fin 1069) = lowerFacets (⟨35, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0036 : lowerComputed (⟨36, by decide⟩ : Fin 1069) = lowerFacets (⟨36, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0037 : lowerComputed (⟨37, by decide⟩ : Fin 1069) = lowerFacets (⟨37, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0038 : lowerComputed (⟨38, by decide⟩ : Fin 1069) = lowerFacets (⟨38, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0039 : lowerComputed (⟨39, by decide⟩ : Fin 1069) = lowerFacets (⟨39, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0040 : lowerComputed (⟨40, by decide⟩ : Fin 1069) = lowerFacets (⟨40, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0041 : lowerComputed (⟨41, by decide⟩ : Fin 1069) = lowerFacets (⟨41, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0042 : lowerComputed (⟨42, by decide⟩ : Fin 1069) = lowerFacets (⟨42, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0043 : lowerComputed (⟨43, by decide⟩ : Fin 1069) = lowerFacets (⟨43, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0044 : lowerComputed (⟨44, by decide⟩ : Fin 1069) = lowerFacets (⟨44, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0045 : lowerComputed (⟨45, by decide⟩ : Fin 1069) = lowerFacets (⟨45, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0046 : lowerComputed (⟨46, by decide⟩ : Fin 1069) = lowerFacets (⟨46, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0047 : lowerComputed (⟨47, by decide⟩ : Fin 1069) = lowerFacets (⟨47, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0048 : lowerComputed (⟨48, by decide⟩ : Fin 1069) = lowerFacets (⟨48, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0049 : lowerComputed (⟨49, by decide⟩ : Fin 1069) = lowerFacets (⟨49, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0050 : lowerComputed (⟨50, by decide⟩ : Fin 1069) = lowerFacets (⟨50, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0051 : lowerComputed (⟨51, by decide⟩ : Fin 1069) = lowerFacets (⟨51, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0052 : lowerComputed (⟨52, by decide⟩ : Fin 1069) = lowerFacets (⟨52, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0053 : lowerComputed (⟨53, by decide⟩ : Fin 1069) = lowerFacets (⟨53, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0054 : lowerComputed (⟨54, by decide⟩ : Fin 1069) = lowerFacets (⟨54, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0055 : lowerComputed (⟨55, by decide⟩ : Fin 1069) = lowerFacets (⟨55, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0056 : lowerComputed (⟨56, by decide⟩ : Fin 1069) = lowerFacets (⟨56, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0057 : lowerComputed (⟨57, by decide⟩ : Fin 1069) = lowerFacets (⟨57, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0058 : lowerComputed (⟨58, by decide⟩ : Fin 1069) = lowerFacets (⟨58, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0059 : lowerComputed (⟨59, by decide⟩ : Fin 1069) = lowerFacets (⟨59, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0060 : lowerComputed (⟨60, by decide⟩ : Fin 1069) = lowerFacets (⟨60, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0061 : lowerComputed (⟨61, by decide⟩ : Fin 1069) = lowerFacets (⟨61, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0062 : lowerComputed (⟨62, by decide⟩ : Fin 1069) = lowerFacets (⟨62, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0063 : lowerComputed (⟨63, by decide⟩ : Fin 1069) = lowerFacets (⟨63, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0064 : lowerComputed (⟨64, by decide⟩ : Fin 1069) = lowerFacets (⟨64, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0065 : lowerComputed (⟨65, by decide⟩ : Fin 1069) = lowerFacets (⟨65, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0066 : lowerComputed (⟨66, by decide⟩ : Fin 1069) = lowerFacets (⟨66, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0067 : lowerComputed (⟨67, by decide⟩ : Fin 1069) = lowerFacets (⟨67, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0068 : lowerComputed (⟨68, by decide⟩ : Fin 1069) = lowerFacets (⟨68, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0069 : lowerComputed (⟨69, by decide⟩ : Fin 1069) = lowerFacets (⟨69, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0070 : lowerComputed (⟨70, by decide⟩ : Fin 1069) = lowerFacets (⟨70, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0071 : lowerComputed (⟨71, by decide⟩ : Fin 1069) = lowerFacets (⟨71, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0072 : lowerComputed (⟨72, by decide⟩ : Fin 1069) = lowerFacets (⟨72, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0073 : lowerComputed (⟨73, by decide⟩ : Fin 1069) = lowerFacets (⟨73, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0074 : lowerComputed (⟨74, by decide⟩ : Fin 1069) = lowerFacets (⟨74, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0075 : lowerComputed (⟨75, by decide⟩ : Fin 1069) = lowerFacets (⟨75, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0076 : lowerComputed (⟨76, by decide⟩ : Fin 1069) = lowerFacets (⟨76, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0077 : lowerComputed (⟨77, by decide⟩ : Fin 1069) = lowerFacets (⟨77, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0078 : lowerComputed (⟨78, by decide⟩ : Fin 1069) = lowerFacets (⟨78, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0079 : lowerComputed (⟨79, by decide⟩ : Fin 1069) = lowerFacets (⟨79, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0080 : lowerComputed (⟨80, by decide⟩ : Fin 1069) = lowerFacets (⟨80, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0081 : lowerComputed (⟨81, by decide⟩ : Fin 1069) = lowerFacets (⟨81, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0082 : lowerComputed (⟨82, by decide⟩ : Fin 1069) = lowerFacets (⟨82, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0083 : lowerComputed (⟨83, by decide⟩ : Fin 1069) = lowerFacets (⟨83, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0084 : lowerComputed (⟨84, by decide⟩ : Fin 1069) = lowerFacets (⟨84, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0085 : lowerComputed (⟨85, by decide⟩ : Fin 1069) = lowerFacets (⟨85, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0086 : lowerComputed (⟨86, by decide⟩ : Fin 1069) = lowerFacets (⟨86, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0087 : lowerComputed (⟨87, by decide⟩ : Fin 1069) = lowerFacets (⟨87, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0088 : lowerComputed (⟨88, by decide⟩ : Fin 1069) = lowerFacets (⟨88, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0089 : lowerComputed (⟨89, by decide⟩ : Fin 1069) = lowerFacets (⟨89, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0090 : lowerComputed (⟨90, by decide⟩ : Fin 1069) = lowerFacets (⟨90, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0091 : lowerComputed (⟨91, by decide⟩ : Fin 1069) = lowerFacets (⟨91, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0092 : lowerComputed (⟨92, by decide⟩ : Fin 1069) = lowerFacets (⟨92, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0093 : lowerComputed (⟨93, by decide⟩ : Fin 1069) = lowerFacets (⟨93, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0094 : lowerComputed (⟨94, by decide⟩ : Fin 1069) = lowerFacets (⟨94, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0095 : lowerComputed (⟨95, by decide⟩ : Fin 1069) = lowerFacets (⟨95, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0096 : lowerComputed (⟨96, by decide⟩ : Fin 1069) = lowerFacets (⟨96, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0097 : lowerComputed (⟨97, by decide⟩ : Fin 1069) = lowerFacets (⟨97, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0098 : lowerComputed (⟨98, by decide⟩ : Fin 1069) = lowerFacets (⟨98, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0099 : lowerComputed (⟨99, by decide⟩ : Fin 1069) = lowerFacets (⟨99, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0100 : lowerComputed (⟨100, by decide⟩ : Fin 1069) = lowerFacets (⟨100, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0101 : lowerComputed (⟨101, by decide⟩ : Fin 1069) = lowerFacets (⟨101, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0102 : lowerComputed (⟨102, by decide⟩ : Fin 1069) = lowerFacets (⟨102, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0103 : lowerComputed (⟨103, by decide⟩ : Fin 1069) = lowerFacets (⟨103, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0104 : lowerComputed (⟨104, by decide⟩ : Fin 1069) = lowerFacets (⟨104, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0105 : lowerComputed (⟨105, by decide⟩ : Fin 1069) = lowerFacets (⟨105, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0106 : lowerComputed (⟨106, by decide⟩ : Fin 1069) = lowerFacets (⟨106, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0107 : lowerComputed (⟨107, by decide⟩ : Fin 1069) = lowerFacets (⟨107, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0108 : lowerComputed (⟨108, by decide⟩ : Fin 1069) = lowerFacets (⟨108, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0109 : lowerComputed (⟨109, by decide⟩ : Fin 1069) = lowerFacets (⟨109, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0110 : lowerComputed (⟨110, by decide⟩ : Fin 1069) = lowerFacets (⟨110, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0111 : lowerComputed (⟨111, by decide⟩ : Fin 1069) = lowerFacets (⟨111, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0112 : lowerComputed (⟨112, by decide⟩ : Fin 1069) = lowerFacets (⟨112, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0113 : lowerComputed (⟨113, by decide⟩ : Fin 1069) = lowerFacets (⟨113, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0114 : lowerComputed (⟨114, by decide⟩ : Fin 1069) = lowerFacets (⟨114, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0115 : lowerComputed (⟨115, by decide⟩ : Fin 1069) = lowerFacets (⟨115, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0116 : lowerComputed (⟨116, by decide⟩ : Fin 1069) = lowerFacets (⟨116, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0117 : lowerComputed (⟨117, by decide⟩ : Fin 1069) = lowerFacets (⟨117, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0118 : lowerComputed (⟨118, by decide⟩ : Fin 1069) = lowerFacets (⟨118, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0119 : lowerComputed (⟨119, by decide⟩ : Fin 1069) = lowerFacets (⟨119, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0120 : lowerComputed (⟨120, by decide⟩ : Fin 1069) = lowerFacets (⟨120, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0121 : lowerComputed (⟨121, by decide⟩ : Fin 1069) = lowerFacets (⟨121, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0122 : lowerComputed (⟨122, by decide⟩ : Fin 1069) = lowerFacets (⟨122, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0123 : lowerComputed (⟨123, by decide⟩ : Fin 1069) = lowerFacets (⟨123, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0124 : lowerComputed (⟨124, by decide⟩ : Fin 1069) = lowerFacets (⟨124, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0125 : lowerComputed (⟨125, by decide⟩ : Fin 1069) = lowerFacets (⟨125, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0126 : lowerComputed (⟨126, by decide⟩ : Fin 1069) = lowerFacets (⟨126, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0127 : lowerComputed (⟨127, by decide⟩ : Fin 1069) = lowerFacets (⟨127, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0128 : lowerComputed (⟨128, by decide⟩ : Fin 1069) = lowerFacets (⟨128, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0129 : lowerComputed (⟨129, by decide⟩ : Fin 1069) = lowerFacets (⟨129, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0130 : lowerComputed (⟨130, by decide⟩ : Fin 1069) = lowerFacets (⟨130, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0131 : lowerComputed (⟨131, by decide⟩ : Fin 1069) = lowerFacets (⟨131, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0132 : lowerComputed (⟨132, by decide⟩ : Fin 1069) = lowerFacets (⟨132, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0133 : lowerComputed (⟨133, by decide⟩ : Fin 1069) = lowerFacets (⟨133, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0134 : lowerComputed (⟨134, by decide⟩ : Fin 1069) = lowerFacets (⟨134, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0135 : lowerComputed (⟨135, by decide⟩ : Fin 1069) = lowerFacets (⟨135, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0136 : lowerComputed (⟨136, by decide⟩ : Fin 1069) = lowerFacets (⟨136, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0137 : lowerComputed (⟨137, by decide⟩ : Fin 1069) = lowerFacets (⟨137, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0138 : lowerComputed (⟨138, by decide⟩ : Fin 1069) = lowerFacets (⟨138, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0139 : lowerComputed (⟨139, by decide⟩ : Fin 1069) = lowerFacets (⟨139, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0140 : lowerComputed (⟨140, by decide⟩ : Fin 1069) = lowerFacets (⟨140, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0141 : lowerComputed (⟨141, by decide⟩ : Fin 1069) = lowerFacets (⟨141, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0142 : lowerComputed (⟨142, by decide⟩ : Fin 1069) = lowerFacets (⟨142, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0143 : lowerComputed (⟨143, by decide⟩ : Fin 1069) = lowerFacets (⟨143, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0144 : lowerComputed (⟨144, by decide⟩ : Fin 1069) = lowerFacets (⟨144, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0145 : lowerComputed (⟨145, by decide⟩ : Fin 1069) = lowerFacets (⟨145, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0146 : lowerComputed (⟨146, by decide⟩ : Fin 1069) = lowerFacets (⟨146, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0147 : lowerComputed (⟨147, by decide⟩ : Fin 1069) = lowerFacets (⟨147, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0148 : lowerComputed (⟨148, by decide⟩ : Fin 1069) = lowerFacets (⟨148, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0149 : lowerComputed (⟨149, by decide⟩ : Fin 1069) = lowerFacets (⟨149, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0150 : lowerComputed (⟨150, by decide⟩ : Fin 1069) = lowerFacets (⟨150, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0151 : lowerComputed (⟨151, by decide⟩ : Fin 1069) = lowerFacets (⟨151, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0152 : lowerComputed (⟨152, by decide⟩ : Fin 1069) = lowerFacets (⟨152, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0153 : lowerComputed (⟨153, by decide⟩ : Fin 1069) = lowerFacets (⟨153, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0154 : lowerComputed (⟨154, by decide⟩ : Fin 1069) = lowerFacets (⟨154, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0155 : lowerComputed (⟨155, by decide⟩ : Fin 1069) = lowerFacets (⟨155, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0156 : lowerComputed (⟨156, by decide⟩ : Fin 1069) = lowerFacets (⟨156, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0157 : lowerComputed (⟨157, by decide⟩ : Fin 1069) = lowerFacets (⟨157, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0158 : lowerComputed (⟨158, by decide⟩ : Fin 1069) = lowerFacets (⟨158, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0159 : lowerComputed (⟨159, by decide⟩ : Fin 1069) = lowerFacets (⟨159, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0160 : lowerComputed (⟨160, by decide⟩ : Fin 1069) = lowerFacets (⟨160, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0161 : lowerComputed (⟨161, by decide⟩ : Fin 1069) = lowerFacets (⟨161, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0162 : lowerComputed (⟨162, by decide⟩ : Fin 1069) = lowerFacets (⟨162, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0163 : lowerComputed (⟨163, by decide⟩ : Fin 1069) = lowerFacets (⟨163, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0164 : lowerComputed (⟨164, by decide⟩ : Fin 1069) = lowerFacets (⟨164, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0165 : lowerComputed (⟨165, by decide⟩ : Fin 1069) = lowerFacets (⟨165, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0166 : lowerComputed (⟨166, by decide⟩ : Fin 1069) = lowerFacets (⟨166, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0167 : lowerComputed (⟨167, by decide⟩ : Fin 1069) = lowerFacets (⟨167, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0168 : lowerComputed (⟨168, by decide⟩ : Fin 1069) = lowerFacets (⟨168, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0169 : lowerComputed (⟨169, by decide⟩ : Fin 1069) = lowerFacets (⟨169, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0170 : lowerComputed (⟨170, by decide⟩ : Fin 1069) = lowerFacets (⟨170, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0171 : lowerComputed (⟨171, by decide⟩ : Fin 1069) = lowerFacets (⟨171, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0172 : lowerComputed (⟨172, by decide⟩ : Fin 1069) = lowerFacets (⟨172, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0173 : lowerComputed (⟨173, by decide⟩ : Fin 1069) = lowerFacets (⟨173, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0174 : lowerComputed (⟨174, by decide⟩ : Fin 1069) = lowerFacets (⟨174, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0175 : lowerComputed (⟨175, by decide⟩ : Fin 1069) = lowerFacets (⟨175, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0176 : lowerComputed (⟨176, by decide⟩ : Fin 1069) = lowerFacets (⟨176, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0177 : lowerComputed (⟨177, by decide⟩ : Fin 1069) = lowerFacets (⟨177, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0178 : lowerComputed (⟨178, by decide⟩ : Fin 1069) = lowerFacets (⟨178, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0179 : lowerComputed (⟨179, by decide⟩ : Fin 1069) = lowerFacets (⟨179, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0180 : lowerComputed (⟨180, by decide⟩ : Fin 1069) = lowerFacets (⟨180, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0181 : lowerComputed (⟨181, by decide⟩ : Fin 1069) = lowerFacets (⟨181, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0182 : lowerComputed (⟨182, by decide⟩ : Fin 1069) = lowerFacets (⟨182, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0183 : lowerComputed (⟨183, by decide⟩ : Fin 1069) = lowerFacets (⟨183, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0184 : lowerComputed (⟨184, by decide⟩ : Fin 1069) = lowerFacets (⟨184, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0185 : lowerComputed (⟨185, by decide⟩ : Fin 1069) = lowerFacets (⟨185, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0186 : lowerComputed (⟨186, by decide⟩ : Fin 1069) = lowerFacets (⟨186, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0187 : lowerComputed (⟨187, by decide⟩ : Fin 1069) = lowerFacets (⟨187, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0188 : lowerComputed (⟨188, by decide⟩ : Fin 1069) = lowerFacets (⟨188, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0189 : lowerComputed (⟨189, by decide⟩ : Fin 1069) = lowerFacets (⟨189, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0190 : lowerComputed (⟨190, by decide⟩ : Fin 1069) = lowerFacets (⟨190, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0191 : lowerComputed (⟨191, by decide⟩ : Fin 1069) = lowerFacets (⟨191, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0192 : lowerComputed (⟨192, by decide⟩ : Fin 1069) = lowerFacets (⟨192, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0193 : lowerComputed (⟨193, by decide⟩ : Fin 1069) = lowerFacets (⟨193, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0194 : lowerComputed (⟨194, by decide⟩ : Fin 1069) = lowerFacets (⟨194, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0195 : lowerComputed (⟨195, by decide⟩ : Fin 1069) = lowerFacets (⟨195, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0196 : lowerComputed (⟨196, by decide⟩ : Fin 1069) = lowerFacets (⟨196, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0197 : lowerComputed (⟨197, by decide⟩ : Fin 1069) = lowerFacets (⟨197, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0198 : lowerComputed (⟨198, by decide⟩ : Fin 1069) = lowerFacets (⟨198, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0199 : lowerComputed (⟨199, by decide⟩ : Fin 1069) = lowerFacets (⟨199, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0200 : lowerComputed (⟨200, by decide⟩ : Fin 1069) = lowerFacets (⟨200, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0201 : lowerComputed (⟨201, by decide⟩ : Fin 1069) = lowerFacets (⟨201, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0202 : lowerComputed (⟨202, by decide⟩ : Fin 1069) = lowerFacets (⟨202, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0203 : lowerComputed (⟨203, by decide⟩ : Fin 1069) = lowerFacets (⟨203, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0204 : lowerComputed (⟨204, by decide⟩ : Fin 1069) = lowerFacets (⟨204, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0205 : lowerComputed (⟨205, by decide⟩ : Fin 1069) = lowerFacets (⟨205, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0206 : lowerComputed (⟨206, by decide⟩ : Fin 1069) = lowerFacets (⟨206, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0207 : lowerComputed (⟨207, by decide⟩ : Fin 1069) = lowerFacets (⟨207, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0208 : lowerComputed (⟨208, by decide⟩ : Fin 1069) = lowerFacets (⟨208, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0209 : lowerComputed (⟨209, by decide⟩ : Fin 1069) = lowerFacets (⟨209, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0210 : lowerComputed (⟨210, by decide⟩ : Fin 1069) = lowerFacets (⟨210, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0211 : lowerComputed (⟨211, by decide⟩ : Fin 1069) = lowerFacets (⟨211, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0212 : lowerComputed (⟨212, by decide⟩ : Fin 1069) = lowerFacets (⟨212, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0213 : lowerComputed (⟨213, by decide⟩ : Fin 1069) = lowerFacets (⟨213, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0214 : lowerComputed (⟨214, by decide⟩ : Fin 1069) = lowerFacets (⟨214, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0215 : lowerComputed (⟨215, by decide⟩ : Fin 1069) = lowerFacets (⟨215, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0216 : lowerComputed (⟨216, by decide⟩ : Fin 1069) = lowerFacets (⟨216, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0217 : lowerComputed (⟨217, by decide⟩ : Fin 1069) = lowerFacets (⟨217, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0218 : lowerComputed (⟨218, by decide⟩ : Fin 1069) = lowerFacets (⟨218, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0219 : lowerComputed (⟨219, by decide⟩ : Fin 1069) = lowerFacets (⟨219, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0220 : lowerComputed (⟨220, by decide⟩ : Fin 1069) = lowerFacets (⟨220, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0221 : lowerComputed (⟨221, by decide⟩ : Fin 1069) = lowerFacets (⟨221, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0222 : lowerComputed (⟨222, by decide⟩ : Fin 1069) = lowerFacets (⟨222, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0223 : lowerComputed (⟨223, by decide⟩ : Fin 1069) = lowerFacets (⟨223, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0224 : lowerComputed (⟨224, by decide⟩ : Fin 1069) = lowerFacets (⟨224, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0225 : lowerComputed (⟨225, by decide⟩ : Fin 1069) = lowerFacets (⟨225, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0226 : lowerComputed (⟨226, by decide⟩ : Fin 1069) = lowerFacets (⟨226, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0227 : lowerComputed (⟨227, by decide⟩ : Fin 1069) = lowerFacets (⟨227, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0228 : lowerComputed (⟨228, by decide⟩ : Fin 1069) = lowerFacets (⟨228, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0229 : lowerComputed (⟨229, by decide⟩ : Fin 1069) = lowerFacets (⟨229, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0230 : lowerComputed (⟨230, by decide⟩ : Fin 1069) = lowerFacets (⟨230, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0231 : lowerComputed (⟨231, by decide⟩ : Fin 1069) = lowerFacets (⟨231, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0232 : lowerComputed (⟨232, by decide⟩ : Fin 1069) = lowerFacets (⟨232, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0233 : lowerComputed (⟨233, by decide⟩ : Fin 1069) = lowerFacets (⟨233, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0234 : lowerComputed (⟨234, by decide⟩ : Fin 1069) = lowerFacets (⟨234, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0235 : lowerComputed (⟨235, by decide⟩ : Fin 1069) = lowerFacets (⟨235, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0236 : lowerComputed (⟨236, by decide⟩ : Fin 1069) = lowerFacets (⟨236, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0237 : lowerComputed (⟨237, by decide⟩ : Fin 1069) = lowerFacets (⟨237, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0238 : lowerComputed (⟨238, by decide⟩ : Fin 1069) = lowerFacets (⟨238, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0239 : lowerComputed (⟨239, by decide⟩ : Fin 1069) = lowerFacets (⟨239, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0240 : lowerComputed (⟨240, by decide⟩ : Fin 1069) = lowerFacets (⟨240, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0241 : lowerComputed (⟨241, by decide⟩ : Fin 1069) = lowerFacets (⟨241, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0242 : lowerComputed (⟨242, by decide⟩ : Fin 1069) = lowerFacets (⟨242, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0243 : lowerComputed (⟨243, by decide⟩ : Fin 1069) = lowerFacets (⟨243, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0244 : lowerComputed (⟨244, by decide⟩ : Fin 1069) = lowerFacets (⟨244, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0245 : lowerComputed (⟨245, by decide⟩ : Fin 1069) = lowerFacets (⟨245, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0246 : lowerComputed (⟨246, by decide⟩ : Fin 1069) = lowerFacets (⟨246, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0247 : lowerComputed (⟨247, by decide⟩ : Fin 1069) = lowerFacets (⟨247, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0248 : lowerComputed (⟨248, by decide⟩ : Fin 1069) = lowerFacets (⟨248, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0249 : lowerComputed (⟨249, by decide⟩ : Fin 1069) = lowerFacets (⟨249, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0250 : lowerComputed (⟨250, by decide⟩ : Fin 1069) = lowerFacets (⟨250, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0251 : lowerComputed (⟨251, by decide⟩ : Fin 1069) = lowerFacets (⟨251, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0252 : lowerComputed (⟨252, by decide⟩ : Fin 1069) = lowerFacets (⟨252, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0253 : lowerComputed (⟨253, by decide⟩ : Fin 1069) = lowerFacets (⟨253, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0254 : lowerComputed (⟨254, by decide⟩ : Fin 1069) = lowerFacets (⟨254, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0255 : lowerComputed (⟨255, by decide⟩ : Fin 1069) = lowerFacets (⟨255, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0256 : lowerComputed (⟨256, by decide⟩ : Fin 1069) = lowerFacets (⟨256, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0257 : lowerComputed (⟨257, by decide⟩ : Fin 1069) = lowerFacets (⟨257, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0258 : lowerComputed (⟨258, by decide⟩ : Fin 1069) = lowerFacets (⟨258, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0259 : lowerComputed (⟨259, by decide⟩ : Fin 1069) = lowerFacets (⟨259, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0260 : lowerComputed (⟨260, by decide⟩ : Fin 1069) = lowerFacets (⟨260, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0261 : lowerComputed (⟨261, by decide⟩ : Fin 1069) = lowerFacets (⟨261, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0262 : lowerComputed (⟨262, by decide⟩ : Fin 1069) = lowerFacets (⟨262, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0263 : lowerComputed (⟨263, by decide⟩ : Fin 1069) = lowerFacets (⟨263, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0264 : lowerComputed (⟨264, by decide⟩ : Fin 1069) = lowerFacets (⟨264, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0265 : lowerComputed (⟨265, by decide⟩ : Fin 1069) = lowerFacets (⟨265, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0266 : lowerComputed (⟨266, by decide⟩ : Fin 1069) = lowerFacets (⟨266, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0267 : lowerComputed (⟨267, by decide⟩ : Fin 1069) = lowerFacets (⟨267, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0268 : lowerComputed (⟨268, by decide⟩ : Fin 1069) = lowerFacets (⟨268, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0269 : lowerComputed (⟨269, by decide⟩ : Fin 1069) = lowerFacets (⟨269, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0270 : lowerComputed (⟨270, by decide⟩ : Fin 1069) = lowerFacets (⟨270, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0271 : lowerComputed (⟨271, by decide⟩ : Fin 1069) = lowerFacets (⟨271, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0272 : lowerComputed (⟨272, by decide⟩ : Fin 1069) = lowerFacets (⟨272, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0273 : lowerComputed (⟨273, by decide⟩ : Fin 1069) = lowerFacets (⟨273, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0274 : lowerComputed (⟨274, by decide⟩ : Fin 1069) = lowerFacets (⟨274, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0275 : lowerComputed (⟨275, by decide⟩ : Fin 1069) = lowerFacets (⟨275, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0276 : lowerComputed (⟨276, by decide⟩ : Fin 1069) = lowerFacets (⟨276, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0277 : lowerComputed (⟨277, by decide⟩ : Fin 1069) = lowerFacets (⟨277, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0278 : lowerComputed (⟨278, by decide⟩ : Fin 1069) = lowerFacets (⟨278, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0279 : lowerComputed (⟨279, by decide⟩ : Fin 1069) = lowerFacets (⟨279, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0280 : lowerComputed (⟨280, by decide⟩ : Fin 1069) = lowerFacets (⟨280, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0281 : lowerComputed (⟨281, by decide⟩ : Fin 1069) = lowerFacets (⟨281, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0282 : lowerComputed (⟨282, by decide⟩ : Fin 1069) = lowerFacets (⟨282, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0283 : lowerComputed (⟨283, by decide⟩ : Fin 1069) = lowerFacets (⟨283, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0284 : lowerComputed (⟨284, by decide⟩ : Fin 1069) = lowerFacets (⟨284, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0285 : lowerComputed (⟨285, by decide⟩ : Fin 1069) = lowerFacets (⟨285, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0286 : lowerComputed (⟨286, by decide⟩ : Fin 1069) = lowerFacets (⟨286, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0287 : lowerComputed (⟨287, by decide⟩ : Fin 1069) = lowerFacets (⟨287, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0288 : lowerComputed (⟨288, by decide⟩ : Fin 1069) = lowerFacets (⟨288, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0289 : lowerComputed (⟨289, by decide⟩ : Fin 1069) = lowerFacets (⟨289, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0290 : lowerComputed (⟨290, by decide⟩ : Fin 1069) = lowerFacets (⟨290, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0291 : lowerComputed (⟨291, by decide⟩ : Fin 1069) = lowerFacets (⟨291, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0292 : lowerComputed (⟨292, by decide⟩ : Fin 1069) = lowerFacets (⟨292, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0293 : lowerComputed (⟨293, by decide⟩ : Fin 1069) = lowerFacets (⟨293, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0294 : lowerComputed (⟨294, by decide⟩ : Fin 1069) = lowerFacets (⟨294, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0295 : lowerComputed (⟨295, by decide⟩ : Fin 1069) = lowerFacets (⟨295, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0296 : lowerComputed (⟨296, by decide⟩ : Fin 1069) = lowerFacets (⟨296, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0297 : lowerComputed (⟨297, by decide⟩ : Fin 1069) = lowerFacets (⟨297, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0298 : lowerComputed (⟨298, by decide⟩ : Fin 1069) = lowerFacets (⟨298, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0299 : lowerComputed (⟨299, by decide⟩ : Fin 1069) = lowerFacets (⟨299, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0300 : lowerComputed (⟨300, by decide⟩ : Fin 1069) = lowerFacets (⟨300, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0301 : lowerComputed (⟨301, by decide⟩ : Fin 1069) = lowerFacets (⟨301, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0302 : lowerComputed (⟨302, by decide⟩ : Fin 1069) = lowerFacets (⟨302, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0303 : lowerComputed (⟨303, by decide⟩ : Fin 1069) = lowerFacets (⟨303, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0304 : lowerComputed (⟨304, by decide⟩ : Fin 1069) = lowerFacets (⟨304, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0305 : lowerComputed (⟨305, by decide⟩ : Fin 1069) = lowerFacets (⟨305, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0306 : lowerComputed (⟨306, by decide⟩ : Fin 1069) = lowerFacets (⟨306, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0307 : lowerComputed (⟨307, by decide⟩ : Fin 1069) = lowerFacets (⟨307, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0308 : lowerComputed (⟨308, by decide⟩ : Fin 1069) = lowerFacets (⟨308, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0309 : lowerComputed (⟨309, by decide⟩ : Fin 1069) = lowerFacets (⟨309, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0310 : lowerComputed (⟨310, by decide⟩ : Fin 1069) = lowerFacets (⟨310, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0311 : lowerComputed (⟨311, by decide⟩ : Fin 1069) = lowerFacets (⟨311, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0312 : lowerComputed (⟨312, by decide⟩ : Fin 1069) = lowerFacets (⟨312, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0313 : lowerComputed (⟨313, by decide⟩ : Fin 1069) = lowerFacets (⟨313, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0314 : lowerComputed (⟨314, by decide⟩ : Fin 1069) = lowerFacets (⟨314, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0315 : lowerComputed (⟨315, by decide⟩ : Fin 1069) = lowerFacets (⟨315, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0316 : lowerComputed (⟨316, by decide⟩ : Fin 1069) = lowerFacets (⟨316, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0317 : lowerComputed (⟨317, by decide⟩ : Fin 1069) = lowerFacets (⟨317, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0318 : lowerComputed (⟨318, by decide⟩ : Fin 1069) = lowerFacets (⟨318, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0319 : lowerComputed (⟨319, by decide⟩ : Fin 1069) = lowerFacets (⟨319, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0320 : lowerComputed (⟨320, by decide⟩ : Fin 1069) = lowerFacets (⟨320, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0321 : lowerComputed (⟨321, by decide⟩ : Fin 1069) = lowerFacets (⟨321, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0322 : lowerComputed (⟨322, by decide⟩ : Fin 1069) = lowerFacets (⟨322, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0323 : lowerComputed (⟨323, by decide⟩ : Fin 1069) = lowerFacets (⟨323, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0324 : lowerComputed (⟨324, by decide⟩ : Fin 1069) = lowerFacets (⟨324, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0325 : lowerComputed (⟨325, by decide⟩ : Fin 1069) = lowerFacets (⟨325, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0326 : lowerComputed (⟨326, by decide⟩ : Fin 1069) = lowerFacets (⟨326, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0327 : lowerComputed (⟨327, by decide⟩ : Fin 1069) = lowerFacets (⟨327, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0328 : lowerComputed (⟨328, by decide⟩ : Fin 1069) = lowerFacets (⟨328, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0329 : lowerComputed (⟨329, by decide⟩ : Fin 1069) = lowerFacets (⟨329, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0330 : lowerComputed (⟨330, by decide⟩ : Fin 1069) = lowerFacets (⟨330, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0331 : lowerComputed (⟨331, by decide⟩ : Fin 1069) = lowerFacets (⟨331, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0332 : lowerComputed (⟨332, by decide⟩ : Fin 1069) = lowerFacets (⟨332, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0333 : lowerComputed (⟨333, by decide⟩ : Fin 1069) = lowerFacets (⟨333, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0334 : lowerComputed (⟨334, by decide⟩ : Fin 1069) = lowerFacets (⟨334, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0335 : lowerComputed (⟨335, by decide⟩ : Fin 1069) = lowerFacets (⟨335, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0336 : lowerComputed (⟨336, by decide⟩ : Fin 1069) = lowerFacets (⟨336, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0337 : lowerComputed (⟨337, by decide⟩ : Fin 1069) = lowerFacets (⟨337, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0338 : lowerComputed (⟨338, by decide⟩ : Fin 1069) = lowerFacets (⟨338, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0339 : lowerComputed (⟨339, by decide⟩ : Fin 1069) = lowerFacets (⟨339, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0340 : lowerComputed (⟨340, by decide⟩ : Fin 1069) = lowerFacets (⟨340, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0341 : lowerComputed (⟨341, by decide⟩ : Fin 1069) = lowerFacets (⟨341, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0342 : lowerComputed (⟨342, by decide⟩ : Fin 1069) = lowerFacets (⟨342, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0343 : lowerComputed (⟨343, by decide⟩ : Fin 1069) = lowerFacets (⟨343, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0344 : lowerComputed (⟨344, by decide⟩ : Fin 1069) = lowerFacets (⟨344, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0345 : lowerComputed (⟨345, by decide⟩ : Fin 1069) = lowerFacets (⟨345, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0346 : lowerComputed (⟨346, by decide⟩ : Fin 1069) = lowerFacets (⟨346, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0347 : lowerComputed (⟨347, by decide⟩ : Fin 1069) = lowerFacets (⟨347, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0348 : lowerComputed (⟨348, by decide⟩ : Fin 1069) = lowerFacets (⟨348, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0349 : lowerComputed (⟨349, by decide⟩ : Fin 1069) = lowerFacets (⟨349, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0350 : lowerComputed (⟨350, by decide⟩ : Fin 1069) = lowerFacets (⟨350, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0351 : lowerComputed (⟨351, by decide⟩ : Fin 1069) = lowerFacets (⟨351, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0352 : lowerComputed (⟨352, by decide⟩ : Fin 1069) = lowerFacets (⟨352, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0353 : lowerComputed (⟨353, by decide⟩ : Fin 1069) = lowerFacets (⟨353, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0354 : lowerComputed (⟨354, by decide⟩ : Fin 1069) = lowerFacets (⟨354, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0355 : lowerComputed (⟨355, by decide⟩ : Fin 1069) = lowerFacets (⟨355, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0356 : lowerComputed (⟨356, by decide⟩ : Fin 1069) = lowerFacets (⟨356, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0357 : lowerComputed (⟨357, by decide⟩ : Fin 1069) = lowerFacets (⟨357, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0358 : lowerComputed (⟨358, by decide⟩ : Fin 1069) = lowerFacets (⟨358, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0359 : lowerComputed (⟨359, by decide⟩ : Fin 1069) = lowerFacets (⟨359, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0360 : lowerComputed (⟨360, by decide⟩ : Fin 1069) = lowerFacets (⟨360, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0361 : lowerComputed (⟨361, by decide⟩ : Fin 1069) = lowerFacets (⟨361, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0362 : lowerComputed (⟨362, by decide⟩ : Fin 1069) = lowerFacets (⟨362, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0363 : lowerComputed (⟨363, by decide⟩ : Fin 1069) = lowerFacets (⟨363, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0364 : lowerComputed (⟨364, by decide⟩ : Fin 1069) = lowerFacets (⟨364, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0365 : lowerComputed (⟨365, by decide⟩ : Fin 1069) = lowerFacets (⟨365, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0366 : lowerComputed (⟨366, by decide⟩ : Fin 1069) = lowerFacets (⟨366, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0367 : lowerComputed (⟨367, by decide⟩ : Fin 1069) = lowerFacets (⟨367, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0368 : lowerComputed (⟨368, by decide⟩ : Fin 1069) = lowerFacets (⟨368, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0369 : lowerComputed (⟨369, by decide⟩ : Fin 1069) = lowerFacets (⟨369, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0370 : lowerComputed (⟨370, by decide⟩ : Fin 1069) = lowerFacets (⟨370, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0371 : lowerComputed (⟨371, by decide⟩ : Fin 1069) = lowerFacets (⟨371, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0372 : lowerComputed (⟨372, by decide⟩ : Fin 1069) = lowerFacets (⟨372, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0373 : lowerComputed (⟨373, by decide⟩ : Fin 1069) = lowerFacets (⟨373, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0374 : lowerComputed (⟨374, by decide⟩ : Fin 1069) = lowerFacets (⟨374, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0375 : lowerComputed (⟨375, by decide⟩ : Fin 1069) = lowerFacets (⟨375, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0376 : lowerComputed (⟨376, by decide⟩ : Fin 1069) = lowerFacets (⟨376, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0377 : lowerComputed (⟨377, by decide⟩ : Fin 1069) = lowerFacets (⟨377, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0378 : lowerComputed (⟨378, by decide⟩ : Fin 1069) = lowerFacets (⟨378, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0379 : lowerComputed (⟨379, by decide⟩ : Fin 1069) = lowerFacets (⟨379, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0380 : lowerComputed (⟨380, by decide⟩ : Fin 1069) = lowerFacets (⟨380, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0381 : lowerComputed (⟨381, by decide⟩ : Fin 1069) = lowerFacets (⟨381, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0382 : lowerComputed (⟨382, by decide⟩ : Fin 1069) = lowerFacets (⟨382, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0383 : lowerComputed (⟨383, by decide⟩ : Fin 1069) = lowerFacets (⟨383, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0384 : lowerComputed (⟨384, by decide⟩ : Fin 1069) = lowerFacets (⟨384, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0385 : lowerComputed (⟨385, by decide⟩ : Fin 1069) = lowerFacets (⟨385, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0386 : lowerComputed (⟨386, by decide⟩ : Fin 1069) = lowerFacets (⟨386, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0387 : lowerComputed (⟨387, by decide⟩ : Fin 1069) = lowerFacets (⟨387, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0388 : lowerComputed (⟨388, by decide⟩ : Fin 1069) = lowerFacets (⟨388, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0389 : lowerComputed (⟨389, by decide⟩ : Fin 1069) = lowerFacets (⟨389, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0390 : lowerComputed (⟨390, by decide⟩ : Fin 1069) = lowerFacets (⟨390, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0391 : lowerComputed (⟨391, by decide⟩ : Fin 1069) = lowerFacets (⟨391, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0392 : lowerComputed (⟨392, by decide⟩ : Fin 1069) = lowerFacets (⟨392, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0393 : lowerComputed (⟨393, by decide⟩ : Fin 1069) = lowerFacets (⟨393, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0394 : lowerComputed (⟨394, by decide⟩ : Fin 1069) = lowerFacets (⟨394, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0395 : lowerComputed (⟨395, by decide⟩ : Fin 1069) = lowerFacets (⟨395, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0396 : lowerComputed (⟨396, by decide⟩ : Fin 1069) = lowerFacets (⟨396, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0397 : lowerComputed (⟨397, by decide⟩ : Fin 1069) = lowerFacets (⟨397, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0398 : lowerComputed (⟨398, by decide⟩ : Fin 1069) = lowerFacets (⟨398, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0399 : lowerComputed (⟨399, by decide⟩ : Fin 1069) = lowerFacets (⟨399, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0400 : lowerComputed (⟨400, by decide⟩ : Fin 1069) = lowerFacets (⟨400, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0401 : lowerComputed (⟨401, by decide⟩ : Fin 1069) = lowerFacets (⟨401, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0402 : lowerComputed (⟨402, by decide⟩ : Fin 1069) = lowerFacets (⟨402, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0403 : lowerComputed (⟨403, by decide⟩ : Fin 1069) = lowerFacets (⟨403, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0404 : lowerComputed (⟨404, by decide⟩ : Fin 1069) = lowerFacets (⟨404, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0405 : lowerComputed (⟨405, by decide⟩ : Fin 1069) = lowerFacets (⟨405, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0406 : lowerComputed (⟨406, by decide⟩ : Fin 1069) = lowerFacets (⟨406, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0407 : lowerComputed (⟨407, by decide⟩ : Fin 1069) = lowerFacets (⟨407, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0408 : lowerComputed (⟨408, by decide⟩ : Fin 1069) = lowerFacets (⟨408, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0409 : lowerComputed (⟨409, by decide⟩ : Fin 1069) = lowerFacets (⟨409, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0410 : lowerComputed (⟨410, by decide⟩ : Fin 1069) = lowerFacets (⟨410, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0411 : lowerComputed (⟨411, by decide⟩ : Fin 1069) = lowerFacets (⟨411, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0412 : lowerComputed (⟨412, by decide⟩ : Fin 1069) = lowerFacets (⟨412, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0413 : lowerComputed (⟨413, by decide⟩ : Fin 1069) = lowerFacets (⟨413, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0414 : lowerComputed (⟨414, by decide⟩ : Fin 1069) = lowerFacets (⟨414, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0415 : lowerComputed (⟨415, by decide⟩ : Fin 1069) = lowerFacets (⟨415, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0416 : lowerComputed (⟨416, by decide⟩ : Fin 1069) = lowerFacets (⟨416, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0417 : lowerComputed (⟨417, by decide⟩ : Fin 1069) = lowerFacets (⟨417, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0418 : lowerComputed (⟨418, by decide⟩ : Fin 1069) = lowerFacets (⟨418, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0419 : lowerComputed (⟨419, by decide⟩ : Fin 1069) = lowerFacets (⟨419, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0420 : lowerComputed (⟨420, by decide⟩ : Fin 1069) = lowerFacets (⟨420, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0421 : lowerComputed (⟨421, by decide⟩ : Fin 1069) = lowerFacets (⟨421, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0422 : lowerComputed (⟨422, by decide⟩ : Fin 1069) = lowerFacets (⟨422, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0423 : lowerComputed (⟨423, by decide⟩ : Fin 1069) = lowerFacets (⟨423, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0424 : lowerComputed (⟨424, by decide⟩ : Fin 1069) = lowerFacets (⟨424, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0425 : lowerComputed (⟨425, by decide⟩ : Fin 1069) = lowerFacets (⟨425, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0426 : lowerComputed (⟨426, by decide⟩ : Fin 1069) = lowerFacets (⟨426, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0427 : lowerComputed (⟨427, by decide⟩ : Fin 1069) = lowerFacets (⟨427, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0428 : lowerComputed (⟨428, by decide⟩ : Fin 1069) = lowerFacets (⟨428, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0429 : lowerComputed (⟨429, by decide⟩ : Fin 1069) = lowerFacets (⟨429, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0430 : lowerComputed (⟨430, by decide⟩ : Fin 1069) = lowerFacets (⟨430, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0431 : lowerComputed (⟨431, by decide⟩ : Fin 1069) = lowerFacets (⟨431, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0432 : lowerComputed (⟨432, by decide⟩ : Fin 1069) = lowerFacets (⟨432, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0433 : lowerComputed (⟨433, by decide⟩ : Fin 1069) = lowerFacets (⟨433, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0434 : lowerComputed (⟨434, by decide⟩ : Fin 1069) = lowerFacets (⟨434, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0435 : lowerComputed (⟨435, by decide⟩ : Fin 1069) = lowerFacets (⟨435, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0436 : lowerComputed (⟨436, by decide⟩ : Fin 1069) = lowerFacets (⟨436, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0437 : lowerComputed (⟨437, by decide⟩ : Fin 1069) = lowerFacets (⟨437, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0438 : lowerComputed (⟨438, by decide⟩ : Fin 1069) = lowerFacets (⟨438, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0439 : lowerComputed (⟨439, by decide⟩ : Fin 1069) = lowerFacets (⟨439, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0440 : lowerComputed (⟨440, by decide⟩ : Fin 1069) = lowerFacets (⟨440, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0441 : lowerComputed (⟨441, by decide⟩ : Fin 1069) = lowerFacets (⟨441, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0442 : lowerComputed (⟨442, by decide⟩ : Fin 1069) = lowerFacets (⟨442, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0443 : lowerComputed (⟨443, by decide⟩ : Fin 1069) = lowerFacets (⟨443, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0444 : lowerComputed (⟨444, by decide⟩ : Fin 1069) = lowerFacets (⟨444, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0445 : lowerComputed (⟨445, by decide⟩ : Fin 1069) = lowerFacets (⟨445, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0446 : lowerComputed (⟨446, by decide⟩ : Fin 1069) = lowerFacets (⟨446, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0447 : lowerComputed (⟨447, by decide⟩ : Fin 1069) = lowerFacets (⟨447, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0448 : lowerComputed (⟨448, by decide⟩ : Fin 1069) = lowerFacets (⟨448, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0449 : lowerComputed (⟨449, by decide⟩ : Fin 1069) = lowerFacets (⟨449, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0450 : lowerComputed (⟨450, by decide⟩ : Fin 1069) = lowerFacets (⟨450, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0451 : lowerComputed (⟨451, by decide⟩ : Fin 1069) = lowerFacets (⟨451, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0452 : lowerComputed (⟨452, by decide⟩ : Fin 1069) = lowerFacets (⟨452, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0453 : lowerComputed (⟨453, by decide⟩ : Fin 1069) = lowerFacets (⟨453, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0454 : lowerComputed (⟨454, by decide⟩ : Fin 1069) = lowerFacets (⟨454, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0455 : lowerComputed (⟨455, by decide⟩ : Fin 1069) = lowerFacets (⟨455, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0456 : lowerComputed (⟨456, by decide⟩ : Fin 1069) = lowerFacets (⟨456, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0457 : lowerComputed (⟨457, by decide⟩ : Fin 1069) = lowerFacets (⟨457, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0458 : lowerComputed (⟨458, by decide⟩ : Fin 1069) = lowerFacets (⟨458, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0459 : lowerComputed (⟨459, by decide⟩ : Fin 1069) = lowerFacets (⟨459, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0460 : lowerComputed (⟨460, by decide⟩ : Fin 1069) = lowerFacets (⟨460, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0461 : lowerComputed (⟨461, by decide⟩ : Fin 1069) = lowerFacets (⟨461, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0462 : lowerComputed (⟨462, by decide⟩ : Fin 1069) = lowerFacets (⟨462, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0463 : lowerComputed (⟨463, by decide⟩ : Fin 1069) = lowerFacets (⟨463, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0464 : lowerComputed (⟨464, by decide⟩ : Fin 1069) = lowerFacets (⟨464, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0465 : lowerComputed (⟨465, by decide⟩ : Fin 1069) = lowerFacets (⟨465, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0466 : lowerComputed (⟨466, by decide⟩ : Fin 1069) = lowerFacets (⟨466, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0467 : lowerComputed (⟨467, by decide⟩ : Fin 1069) = lowerFacets (⟨467, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0468 : lowerComputed (⟨468, by decide⟩ : Fin 1069) = lowerFacets (⟨468, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0469 : lowerComputed (⟨469, by decide⟩ : Fin 1069) = lowerFacets (⟨469, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0470 : lowerComputed (⟨470, by decide⟩ : Fin 1069) = lowerFacets (⟨470, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0471 : lowerComputed (⟨471, by decide⟩ : Fin 1069) = lowerFacets (⟨471, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0472 : lowerComputed (⟨472, by decide⟩ : Fin 1069) = lowerFacets (⟨472, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0473 : lowerComputed (⟨473, by decide⟩ : Fin 1069) = lowerFacets (⟨473, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0474 : lowerComputed (⟨474, by decide⟩ : Fin 1069) = lowerFacets (⟨474, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0475 : lowerComputed (⟨475, by decide⟩ : Fin 1069) = lowerFacets (⟨475, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0476 : lowerComputed (⟨476, by decide⟩ : Fin 1069) = lowerFacets (⟨476, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0477 : lowerComputed (⟨477, by decide⟩ : Fin 1069) = lowerFacets (⟨477, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0478 : lowerComputed (⟨478, by decide⟩ : Fin 1069) = lowerFacets (⟨478, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0479 : lowerComputed (⟨479, by decide⟩ : Fin 1069) = lowerFacets (⟨479, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0480 : lowerComputed (⟨480, by decide⟩ : Fin 1069) = lowerFacets (⟨480, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0481 : lowerComputed (⟨481, by decide⟩ : Fin 1069) = lowerFacets (⟨481, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0482 : lowerComputed (⟨482, by decide⟩ : Fin 1069) = lowerFacets (⟨482, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0483 : lowerComputed (⟨483, by decide⟩ : Fin 1069) = lowerFacets (⟨483, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0484 : lowerComputed (⟨484, by decide⟩ : Fin 1069) = lowerFacets (⟨484, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0485 : lowerComputed (⟨485, by decide⟩ : Fin 1069) = lowerFacets (⟨485, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0486 : lowerComputed (⟨486, by decide⟩ : Fin 1069) = lowerFacets (⟨486, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0487 : lowerComputed (⟨487, by decide⟩ : Fin 1069) = lowerFacets (⟨487, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0488 : lowerComputed (⟨488, by decide⟩ : Fin 1069) = lowerFacets (⟨488, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0489 : lowerComputed (⟨489, by decide⟩ : Fin 1069) = lowerFacets (⟨489, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0490 : lowerComputed (⟨490, by decide⟩ : Fin 1069) = lowerFacets (⟨490, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0491 : lowerComputed (⟨491, by decide⟩ : Fin 1069) = lowerFacets (⟨491, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0492 : lowerComputed (⟨492, by decide⟩ : Fin 1069) = lowerFacets (⟨492, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0493 : lowerComputed (⟨493, by decide⟩ : Fin 1069) = lowerFacets (⟨493, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0494 : lowerComputed (⟨494, by decide⟩ : Fin 1069) = lowerFacets (⟨494, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0495 : lowerComputed (⟨495, by decide⟩ : Fin 1069) = lowerFacets (⟨495, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0496 : lowerComputed (⟨496, by decide⟩ : Fin 1069) = lowerFacets (⟨496, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0497 : lowerComputed (⟨497, by decide⟩ : Fin 1069) = lowerFacets (⟨497, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0498 : lowerComputed (⟨498, by decide⟩ : Fin 1069) = lowerFacets (⟨498, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0499 : lowerComputed (⟨499, by decide⟩ : Fin 1069) = lowerFacets (⟨499, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0500 : lowerComputed (⟨500, by decide⟩ : Fin 1069) = lowerFacets (⟨500, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0501 : lowerComputed (⟨501, by decide⟩ : Fin 1069) = lowerFacets (⟨501, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0502 : lowerComputed (⟨502, by decide⟩ : Fin 1069) = lowerFacets (⟨502, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0503 : lowerComputed (⟨503, by decide⟩ : Fin 1069) = lowerFacets (⟨503, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0504 : lowerComputed (⟨504, by decide⟩ : Fin 1069) = lowerFacets (⟨504, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0505 : lowerComputed (⟨505, by decide⟩ : Fin 1069) = lowerFacets (⟨505, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0506 : lowerComputed (⟨506, by decide⟩ : Fin 1069) = lowerFacets (⟨506, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0507 : lowerComputed (⟨507, by decide⟩ : Fin 1069) = lowerFacets (⟨507, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0508 : lowerComputed (⟨508, by decide⟩ : Fin 1069) = lowerFacets (⟨508, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0509 : lowerComputed (⟨509, by decide⟩ : Fin 1069) = lowerFacets (⟨509, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0510 : lowerComputed (⟨510, by decide⟩ : Fin 1069) = lowerFacets (⟨510, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0511 : lowerComputed (⟨511, by decide⟩ : Fin 1069) = lowerFacets (⟨511, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0512 : lowerComputed (⟨512, by decide⟩ : Fin 1069) = lowerFacets (⟨512, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0513 : lowerComputed (⟨513, by decide⟩ : Fin 1069) = lowerFacets (⟨513, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0514 : lowerComputed (⟨514, by decide⟩ : Fin 1069) = lowerFacets (⟨514, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0515 : lowerComputed (⟨515, by decide⟩ : Fin 1069) = lowerFacets (⟨515, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0516 : lowerComputed (⟨516, by decide⟩ : Fin 1069) = lowerFacets (⟨516, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0517 : lowerComputed (⟨517, by decide⟩ : Fin 1069) = lowerFacets (⟨517, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0518 : lowerComputed (⟨518, by decide⟩ : Fin 1069) = lowerFacets (⟨518, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0519 : lowerComputed (⟨519, by decide⟩ : Fin 1069) = lowerFacets (⟨519, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0520 : lowerComputed (⟨520, by decide⟩ : Fin 1069) = lowerFacets (⟨520, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0521 : lowerComputed (⟨521, by decide⟩ : Fin 1069) = lowerFacets (⟨521, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0522 : lowerComputed (⟨522, by decide⟩ : Fin 1069) = lowerFacets (⟨522, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0523 : lowerComputed (⟨523, by decide⟩ : Fin 1069) = lowerFacets (⟨523, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0524 : lowerComputed (⟨524, by decide⟩ : Fin 1069) = lowerFacets (⟨524, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0525 : lowerComputed (⟨525, by decide⟩ : Fin 1069) = lowerFacets (⟨525, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0526 : lowerComputed (⟨526, by decide⟩ : Fin 1069) = lowerFacets (⟨526, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0527 : lowerComputed (⟨527, by decide⟩ : Fin 1069) = lowerFacets (⟨527, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0528 : lowerComputed (⟨528, by decide⟩ : Fin 1069) = lowerFacets (⟨528, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0529 : lowerComputed (⟨529, by decide⟩ : Fin 1069) = lowerFacets (⟨529, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0530 : lowerComputed (⟨530, by decide⟩ : Fin 1069) = lowerFacets (⟨530, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0531 : lowerComputed (⟨531, by decide⟩ : Fin 1069) = lowerFacets (⟨531, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0532 : lowerComputed (⟨532, by decide⟩ : Fin 1069) = lowerFacets (⟨532, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0533 : lowerComputed (⟨533, by decide⟩ : Fin 1069) = lowerFacets (⟨533, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0534 : lowerComputed (⟨534, by decide⟩ : Fin 1069) = lowerFacets (⟨534, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0535 : lowerComputed (⟨535, by decide⟩ : Fin 1069) = lowerFacets (⟨535, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0536 : lowerComputed (⟨536, by decide⟩ : Fin 1069) = lowerFacets (⟨536, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0537 : lowerComputed (⟨537, by decide⟩ : Fin 1069) = lowerFacets (⟨537, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0538 : lowerComputed (⟨538, by decide⟩ : Fin 1069) = lowerFacets (⟨538, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0539 : lowerComputed (⟨539, by decide⟩ : Fin 1069) = lowerFacets (⟨539, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0540 : lowerComputed (⟨540, by decide⟩ : Fin 1069) = lowerFacets (⟨540, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0541 : lowerComputed (⟨541, by decide⟩ : Fin 1069) = lowerFacets (⟨541, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0542 : lowerComputed (⟨542, by decide⟩ : Fin 1069) = lowerFacets (⟨542, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0543 : lowerComputed (⟨543, by decide⟩ : Fin 1069) = lowerFacets (⟨543, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0544 : lowerComputed (⟨544, by decide⟩ : Fin 1069) = lowerFacets (⟨544, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0545 : lowerComputed (⟨545, by decide⟩ : Fin 1069) = lowerFacets (⟨545, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0546 : lowerComputed (⟨546, by decide⟩ : Fin 1069) = lowerFacets (⟨546, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0547 : lowerComputed (⟨547, by decide⟩ : Fin 1069) = lowerFacets (⟨547, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0548 : lowerComputed (⟨548, by decide⟩ : Fin 1069) = lowerFacets (⟨548, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0549 : lowerComputed (⟨549, by decide⟩ : Fin 1069) = lowerFacets (⟨549, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0550 : lowerComputed (⟨550, by decide⟩ : Fin 1069) = lowerFacets (⟨550, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0551 : lowerComputed (⟨551, by decide⟩ : Fin 1069) = lowerFacets (⟨551, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0552 : lowerComputed (⟨552, by decide⟩ : Fin 1069) = lowerFacets (⟨552, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0553 : lowerComputed (⟨553, by decide⟩ : Fin 1069) = lowerFacets (⟨553, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0554 : lowerComputed (⟨554, by decide⟩ : Fin 1069) = lowerFacets (⟨554, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0555 : lowerComputed (⟨555, by decide⟩ : Fin 1069) = lowerFacets (⟨555, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0556 : lowerComputed (⟨556, by decide⟩ : Fin 1069) = lowerFacets (⟨556, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0557 : lowerComputed (⟨557, by decide⟩ : Fin 1069) = lowerFacets (⟨557, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0558 : lowerComputed (⟨558, by decide⟩ : Fin 1069) = lowerFacets (⟨558, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0559 : lowerComputed (⟨559, by decide⟩ : Fin 1069) = lowerFacets (⟨559, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0560 : lowerComputed (⟨560, by decide⟩ : Fin 1069) = lowerFacets (⟨560, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0561 : lowerComputed (⟨561, by decide⟩ : Fin 1069) = lowerFacets (⟨561, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0562 : lowerComputed (⟨562, by decide⟩ : Fin 1069) = lowerFacets (⟨562, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0563 : lowerComputed (⟨563, by decide⟩ : Fin 1069) = lowerFacets (⟨563, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0564 : lowerComputed (⟨564, by decide⟩ : Fin 1069) = lowerFacets (⟨564, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0565 : lowerComputed (⟨565, by decide⟩ : Fin 1069) = lowerFacets (⟨565, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0566 : lowerComputed (⟨566, by decide⟩ : Fin 1069) = lowerFacets (⟨566, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0567 : lowerComputed (⟨567, by decide⟩ : Fin 1069) = lowerFacets (⟨567, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0568 : lowerComputed (⟨568, by decide⟩ : Fin 1069) = lowerFacets (⟨568, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0569 : lowerComputed (⟨569, by decide⟩ : Fin 1069) = lowerFacets (⟨569, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0570 : lowerComputed (⟨570, by decide⟩ : Fin 1069) = lowerFacets (⟨570, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0571 : lowerComputed (⟨571, by decide⟩ : Fin 1069) = lowerFacets (⟨571, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0572 : lowerComputed (⟨572, by decide⟩ : Fin 1069) = lowerFacets (⟨572, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0573 : lowerComputed (⟨573, by decide⟩ : Fin 1069) = lowerFacets (⟨573, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0574 : lowerComputed (⟨574, by decide⟩ : Fin 1069) = lowerFacets (⟨574, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0575 : lowerComputed (⟨575, by decide⟩ : Fin 1069) = lowerFacets (⟨575, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0576 : lowerComputed (⟨576, by decide⟩ : Fin 1069) = lowerFacets (⟨576, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0577 : lowerComputed (⟨577, by decide⟩ : Fin 1069) = lowerFacets (⟨577, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0578 : lowerComputed (⟨578, by decide⟩ : Fin 1069) = lowerFacets (⟨578, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0579 : lowerComputed (⟨579, by decide⟩ : Fin 1069) = lowerFacets (⟨579, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0580 : lowerComputed (⟨580, by decide⟩ : Fin 1069) = lowerFacets (⟨580, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0581 : lowerComputed (⟨581, by decide⟩ : Fin 1069) = lowerFacets (⟨581, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0582 : lowerComputed (⟨582, by decide⟩ : Fin 1069) = lowerFacets (⟨582, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0583 : lowerComputed (⟨583, by decide⟩ : Fin 1069) = lowerFacets (⟨583, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0584 : lowerComputed (⟨584, by decide⟩ : Fin 1069) = lowerFacets (⟨584, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0585 : lowerComputed (⟨585, by decide⟩ : Fin 1069) = lowerFacets (⟨585, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0586 : lowerComputed (⟨586, by decide⟩ : Fin 1069) = lowerFacets (⟨586, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0587 : lowerComputed (⟨587, by decide⟩ : Fin 1069) = lowerFacets (⟨587, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0588 : lowerComputed (⟨588, by decide⟩ : Fin 1069) = lowerFacets (⟨588, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0589 : lowerComputed (⟨589, by decide⟩ : Fin 1069) = lowerFacets (⟨589, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0590 : lowerComputed (⟨590, by decide⟩ : Fin 1069) = lowerFacets (⟨590, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0591 : lowerComputed (⟨591, by decide⟩ : Fin 1069) = lowerFacets (⟨591, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0592 : lowerComputed (⟨592, by decide⟩ : Fin 1069) = lowerFacets (⟨592, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0593 : lowerComputed (⟨593, by decide⟩ : Fin 1069) = lowerFacets (⟨593, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0594 : lowerComputed (⟨594, by decide⟩ : Fin 1069) = lowerFacets (⟨594, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0595 : lowerComputed (⟨595, by decide⟩ : Fin 1069) = lowerFacets (⟨595, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0596 : lowerComputed (⟨596, by decide⟩ : Fin 1069) = lowerFacets (⟨596, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0597 : lowerComputed (⟨597, by decide⟩ : Fin 1069) = lowerFacets (⟨597, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0598 : lowerComputed (⟨598, by decide⟩ : Fin 1069) = lowerFacets (⟨598, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0599 : lowerComputed (⟨599, by decide⟩ : Fin 1069) = lowerFacets (⟨599, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0600 : lowerComputed (⟨600, by decide⟩ : Fin 1069) = lowerFacets (⟨600, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0601 : lowerComputed (⟨601, by decide⟩ : Fin 1069) = lowerFacets (⟨601, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0602 : lowerComputed (⟨602, by decide⟩ : Fin 1069) = lowerFacets (⟨602, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0603 : lowerComputed (⟨603, by decide⟩ : Fin 1069) = lowerFacets (⟨603, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0604 : lowerComputed (⟨604, by decide⟩ : Fin 1069) = lowerFacets (⟨604, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0605 : lowerComputed (⟨605, by decide⟩ : Fin 1069) = lowerFacets (⟨605, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0606 : lowerComputed (⟨606, by decide⟩ : Fin 1069) = lowerFacets (⟨606, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0607 : lowerComputed (⟨607, by decide⟩ : Fin 1069) = lowerFacets (⟨607, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0608 : lowerComputed (⟨608, by decide⟩ : Fin 1069) = lowerFacets (⟨608, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0609 : lowerComputed (⟨609, by decide⟩ : Fin 1069) = lowerFacets (⟨609, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0610 : lowerComputed (⟨610, by decide⟩ : Fin 1069) = lowerFacets (⟨610, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0611 : lowerComputed (⟨611, by decide⟩ : Fin 1069) = lowerFacets (⟨611, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0612 : lowerComputed (⟨612, by decide⟩ : Fin 1069) = lowerFacets (⟨612, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0613 : lowerComputed (⟨613, by decide⟩ : Fin 1069) = lowerFacets (⟨613, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0614 : lowerComputed (⟨614, by decide⟩ : Fin 1069) = lowerFacets (⟨614, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0615 : lowerComputed (⟨615, by decide⟩ : Fin 1069) = lowerFacets (⟨615, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0616 : lowerComputed (⟨616, by decide⟩ : Fin 1069) = lowerFacets (⟨616, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0617 : lowerComputed (⟨617, by decide⟩ : Fin 1069) = lowerFacets (⟨617, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0618 : lowerComputed (⟨618, by decide⟩ : Fin 1069) = lowerFacets (⟨618, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0619 : lowerComputed (⟨619, by decide⟩ : Fin 1069) = lowerFacets (⟨619, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0620 : lowerComputed (⟨620, by decide⟩ : Fin 1069) = lowerFacets (⟨620, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0621 : lowerComputed (⟨621, by decide⟩ : Fin 1069) = lowerFacets (⟨621, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0622 : lowerComputed (⟨622, by decide⟩ : Fin 1069) = lowerFacets (⟨622, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0623 : lowerComputed (⟨623, by decide⟩ : Fin 1069) = lowerFacets (⟨623, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0624 : lowerComputed (⟨624, by decide⟩ : Fin 1069) = lowerFacets (⟨624, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0625 : lowerComputed (⟨625, by decide⟩ : Fin 1069) = lowerFacets (⟨625, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0626 : lowerComputed (⟨626, by decide⟩ : Fin 1069) = lowerFacets (⟨626, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0627 : lowerComputed (⟨627, by decide⟩ : Fin 1069) = lowerFacets (⟨627, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0628 : lowerComputed (⟨628, by decide⟩ : Fin 1069) = lowerFacets (⟨628, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0629 : lowerComputed (⟨629, by decide⟩ : Fin 1069) = lowerFacets (⟨629, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0630 : lowerComputed (⟨630, by decide⟩ : Fin 1069) = lowerFacets (⟨630, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0631 : lowerComputed (⟨631, by decide⟩ : Fin 1069) = lowerFacets (⟨631, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0632 : lowerComputed (⟨632, by decide⟩ : Fin 1069) = lowerFacets (⟨632, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0633 : lowerComputed (⟨633, by decide⟩ : Fin 1069) = lowerFacets (⟨633, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0634 : lowerComputed (⟨634, by decide⟩ : Fin 1069) = lowerFacets (⟨634, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0635 : lowerComputed (⟨635, by decide⟩ : Fin 1069) = lowerFacets (⟨635, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0636 : lowerComputed (⟨636, by decide⟩ : Fin 1069) = lowerFacets (⟨636, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0637 : lowerComputed (⟨637, by decide⟩ : Fin 1069) = lowerFacets (⟨637, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0638 : lowerComputed (⟨638, by decide⟩ : Fin 1069) = lowerFacets (⟨638, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0639 : lowerComputed (⟨639, by decide⟩ : Fin 1069) = lowerFacets (⟨639, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0640 : lowerComputed (⟨640, by decide⟩ : Fin 1069) = lowerFacets (⟨640, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0641 : lowerComputed (⟨641, by decide⟩ : Fin 1069) = lowerFacets (⟨641, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0642 : lowerComputed (⟨642, by decide⟩ : Fin 1069) = lowerFacets (⟨642, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0643 : lowerComputed (⟨643, by decide⟩ : Fin 1069) = lowerFacets (⟨643, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0644 : lowerComputed (⟨644, by decide⟩ : Fin 1069) = lowerFacets (⟨644, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0645 : lowerComputed (⟨645, by decide⟩ : Fin 1069) = lowerFacets (⟨645, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0646 : lowerComputed (⟨646, by decide⟩ : Fin 1069) = lowerFacets (⟨646, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0647 : lowerComputed (⟨647, by decide⟩ : Fin 1069) = lowerFacets (⟨647, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0648 : lowerComputed (⟨648, by decide⟩ : Fin 1069) = lowerFacets (⟨648, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0649 : lowerComputed (⟨649, by decide⟩ : Fin 1069) = lowerFacets (⟨649, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0650 : lowerComputed (⟨650, by decide⟩ : Fin 1069) = lowerFacets (⟨650, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0651 : lowerComputed (⟨651, by decide⟩ : Fin 1069) = lowerFacets (⟨651, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0652 : lowerComputed (⟨652, by decide⟩ : Fin 1069) = lowerFacets (⟨652, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0653 : lowerComputed (⟨653, by decide⟩ : Fin 1069) = lowerFacets (⟨653, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0654 : lowerComputed (⟨654, by decide⟩ : Fin 1069) = lowerFacets (⟨654, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0655 : lowerComputed (⟨655, by decide⟩ : Fin 1069) = lowerFacets (⟨655, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0656 : lowerComputed (⟨656, by decide⟩ : Fin 1069) = lowerFacets (⟨656, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0657 : lowerComputed (⟨657, by decide⟩ : Fin 1069) = lowerFacets (⟨657, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0658 : lowerComputed (⟨658, by decide⟩ : Fin 1069) = lowerFacets (⟨658, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0659 : lowerComputed (⟨659, by decide⟩ : Fin 1069) = lowerFacets (⟨659, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0660 : lowerComputed (⟨660, by decide⟩ : Fin 1069) = lowerFacets (⟨660, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0661 : lowerComputed (⟨661, by decide⟩ : Fin 1069) = lowerFacets (⟨661, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0662 : lowerComputed (⟨662, by decide⟩ : Fin 1069) = lowerFacets (⟨662, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0663 : lowerComputed (⟨663, by decide⟩ : Fin 1069) = lowerFacets (⟨663, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0664 : lowerComputed (⟨664, by decide⟩ : Fin 1069) = lowerFacets (⟨664, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0665 : lowerComputed (⟨665, by decide⟩ : Fin 1069) = lowerFacets (⟨665, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0666 : lowerComputed (⟨666, by decide⟩ : Fin 1069) = lowerFacets (⟨666, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0667 : lowerComputed (⟨667, by decide⟩ : Fin 1069) = lowerFacets (⟨667, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0668 : lowerComputed (⟨668, by decide⟩ : Fin 1069) = lowerFacets (⟨668, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0669 : lowerComputed (⟨669, by decide⟩ : Fin 1069) = lowerFacets (⟨669, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0670 : lowerComputed (⟨670, by decide⟩ : Fin 1069) = lowerFacets (⟨670, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0671 : lowerComputed (⟨671, by decide⟩ : Fin 1069) = lowerFacets (⟨671, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0672 : lowerComputed (⟨672, by decide⟩ : Fin 1069) = lowerFacets (⟨672, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0673 : lowerComputed (⟨673, by decide⟩ : Fin 1069) = lowerFacets (⟨673, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0674 : lowerComputed (⟨674, by decide⟩ : Fin 1069) = lowerFacets (⟨674, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0675 : lowerComputed (⟨675, by decide⟩ : Fin 1069) = lowerFacets (⟨675, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0676 : lowerComputed (⟨676, by decide⟩ : Fin 1069) = lowerFacets (⟨676, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0677 : lowerComputed (⟨677, by decide⟩ : Fin 1069) = lowerFacets (⟨677, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0678 : lowerComputed (⟨678, by decide⟩ : Fin 1069) = lowerFacets (⟨678, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0679 : lowerComputed (⟨679, by decide⟩ : Fin 1069) = lowerFacets (⟨679, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0680 : lowerComputed (⟨680, by decide⟩ : Fin 1069) = lowerFacets (⟨680, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0681 : lowerComputed (⟨681, by decide⟩ : Fin 1069) = lowerFacets (⟨681, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0682 : lowerComputed (⟨682, by decide⟩ : Fin 1069) = lowerFacets (⟨682, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0683 : lowerComputed (⟨683, by decide⟩ : Fin 1069) = lowerFacets (⟨683, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0684 : lowerComputed (⟨684, by decide⟩ : Fin 1069) = lowerFacets (⟨684, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0685 : lowerComputed (⟨685, by decide⟩ : Fin 1069) = lowerFacets (⟨685, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0686 : lowerComputed (⟨686, by decide⟩ : Fin 1069) = lowerFacets (⟨686, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0687 : lowerComputed (⟨687, by decide⟩ : Fin 1069) = lowerFacets (⟨687, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0688 : lowerComputed (⟨688, by decide⟩ : Fin 1069) = lowerFacets (⟨688, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0689 : lowerComputed (⟨689, by decide⟩ : Fin 1069) = lowerFacets (⟨689, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0690 : lowerComputed (⟨690, by decide⟩ : Fin 1069) = lowerFacets (⟨690, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0691 : lowerComputed (⟨691, by decide⟩ : Fin 1069) = lowerFacets (⟨691, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0692 : lowerComputed (⟨692, by decide⟩ : Fin 1069) = lowerFacets (⟨692, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0693 : lowerComputed (⟨693, by decide⟩ : Fin 1069) = lowerFacets (⟨693, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0694 : lowerComputed (⟨694, by decide⟩ : Fin 1069) = lowerFacets (⟨694, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0695 : lowerComputed (⟨695, by decide⟩ : Fin 1069) = lowerFacets (⟨695, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0696 : lowerComputed (⟨696, by decide⟩ : Fin 1069) = lowerFacets (⟨696, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0697 : lowerComputed (⟨697, by decide⟩ : Fin 1069) = lowerFacets (⟨697, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0698 : lowerComputed (⟨698, by decide⟩ : Fin 1069) = lowerFacets (⟨698, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0699 : lowerComputed (⟨699, by decide⟩ : Fin 1069) = lowerFacets (⟨699, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0700 : lowerComputed (⟨700, by decide⟩ : Fin 1069) = lowerFacets (⟨700, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0701 : lowerComputed (⟨701, by decide⟩ : Fin 1069) = lowerFacets (⟨701, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0702 : lowerComputed (⟨702, by decide⟩ : Fin 1069) = lowerFacets (⟨702, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0703 : lowerComputed (⟨703, by decide⟩ : Fin 1069) = lowerFacets (⟨703, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0704 : lowerComputed (⟨704, by decide⟩ : Fin 1069) = lowerFacets (⟨704, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0705 : lowerComputed (⟨705, by decide⟩ : Fin 1069) = lowerFacets (⟨705, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0706 : lowerComputed (⟨706, by decide⟩ : Fin 1069) = lowerFacets (⟨706, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0707 : lowerComputed (⟨707, by decide⟩ : Fin 1069) = lowerFacets (⟨707, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0708 : lowerComputed (⟨708, by decide⟩ : Fin 1069) = lowerFacets (⟨708, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0709 : lowerComputed (⟨709, by decide⟩ : Fin 1069) = lowerFacets (⟨709, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0710 : lowerComputed (⟨710, by decide⟩ : Fin 1069) = lowerFacets (⟨710, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0711 : lowerComputed (⟨711, by decide⟩ : Fin 1069) = lowerFacets (⟨711, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0712 : lowerComputed (⟨712, by decide⟩ : Fin 1069) = lowerFacets (⟨712, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0713 : lowerComputed (⟨713, by decide⟩ : Fin 1069) = lowerFacets (⟨713, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0714 : lowerComputed (⟨714, by decide⟩ : Fin 1069) = lowerFacets (⟨714, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0715 : lowerComputed (⟨715, by decide⟩ : Fin 1069) = lowerFacets (⟨715, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0716 : lowerComputed (⟨716, by decide⟩ : Fin 1069) = lowerFacets (⟨716, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0717 : lowerComputed (⟨717, by decide⟩ : Fin 1069) = lowerFacets (⟨717, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0718 : lowerComputed (⟨718, by decide⟩ : Fin 1069) = lowerFacets (⟨718, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0719 : lowerComputed (⟨719, by decide⟩ : Fin 1069) = lowerFacets (⟨719, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0720 : lowerComputed (⟨720, by decide⟩ : Fin 1069) = lowerFacets (⟨720, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0721 : lowerComputed (⟨721, by decide⟩ : Fin 1069) = lowerFacets (⟨721, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0722 : lowerComputed (⟨722, by decide⟩ : Fin 1069) = lowerFacets (⟨722, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0723 : lowerComputed (⟨723, by decide⟩ : Fin 1069) = lowerFacets (⟨723, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0724 : lowerComputed (⟨724, by decide⟩ : Fin 1069) = lowerFacets (⟨724, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0725 : lowerComputed (⟨725, by decide⟩ : Fin 1069) = lowerFacets (⟨725, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0726 : lowerComputed (⟨726, by decide⟩ : Fin 1069) = lowerFacets (⟨726, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0727 : lowerComputed (⟨727, by decide⟩ : Fin 1069) = lowerFacets (⟨727, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0728 : lowerComputed (⟨728, by decide⟩ : Fin 1069) = lowerFacets (⟨728, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0729 : lowerComputed (⟨729, by decide⟩ : Fin 1069) = lowerFacets (⟨729, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0730 : lowerComputed (⟨730, by decide⟩ : Fin 1069) = lowerFacets (⟨730, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0731 : lowerComputed (⟨731, by decide⟩ : Fin 1069) = lowerFacets (⟨731, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0732 : lowerComputed (⟨732, by decide⟩ : Fin 1069) = lowerFacets (⟨732, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0733 : lowerComputed (⟨733, by decide⟩ : Fin 1069) = lowerFacets (⟨733, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0734 : lowerComputed (⟨734, by decide⟩ : Fin 1069) = lowerFacets (⟨734, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0735 : lowerComputed (⟨735, by decide⟩ : Fin 1069) = lowerFacets (⟨735, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0736 : lowerComputed (⟨736, by decide⟩ : Fin 1069) = lowerFacets (⟨736, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0737 : lowerComputed (⟨737, by decide⟩ : Fin 1069) = lowerFacets (⟨737, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0738 : lowerComputed (⟨738, by decide⟩ : Fin 1069) = lowerFacets (⟨738, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0739 : lowerComputed (⟨739, by decide⟩ : Fin 1069) = lowerFacets (⟨739, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0740 : lowerComputed (⟨740, by decide⟩ : Fin 1069) = lowerFacets (⟨740, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0741 : lowerComputed (⟨741, by decide⟩ : Fin 1069) = lowerFacets (⟨741, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0742 : lowerComputed (⟨742, by decide⟩ : Fin 1069) = lowerFacets (⟨742, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0743 : lowerComputed (⟨743, by decide⟩ : Fin 1069) = lowerFacets (⟨743, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0744 : lowerComputed (⟨744, by decide⟩ : Fin 1069) = lowerFacets (⟨744, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0745 : lowerComputed (⟨745, by decide⟩ : Fin 1069) = lowerFacets (⟨745, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0746 : lowerComputed (⟨746, by decide⟩ : Fin 1069) = lowerFacets (⟨746, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0747 : lowerComputed (⟨747, by decide⟩ : Fin 1069) = lowerFacets (⟨747, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0748 : lowerComputed (⟨748, by decide⟩ : Fin 1069) = lowerFacets (⟨748, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0749 : lowerComputed (⟨749, by decide⟩ : Fin 1069) = lowerFacets (⟨749, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0750 : lowerComputed (⟨750, by decide⟩ : Fin 1069) = lowerFacets (⟨750, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0751 : lowerComputed (⟨751, by decide⟩ : Fin 1069) = lowerFacets (⟨751, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0752 : lowerComputed (⟨752, by decide⟩ : Fin 1069) = lowerFacets (⟨752, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0753 : lowerComputed (⟨753, by decide⟩ : Fin 1069) = lowerFacets (⟨753, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0754 : lowerComputed (⟨754, by decide⟩ : Fin 1069) = lowerFacets (⟨754, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0755 : lowerComputed (⟨755, by decide⟩ : Fin 1069) = lowerFacets (⟨755, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0756 : lowerComputed (⟨756, by decide⟩ : Fin 1069) = lowerFacets (⟨756, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0757 : lowerComputed (⟨757, by decide⟩ : Fin 1069) = lowerFacets (⟨757, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0758 : lowerComputed (⟨758, by decide⟩ : Fin 1069) = lowerFacets (⟨758, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0759 : lowerComputed (⟨759, by decide⟩ : Fin 1069) = lowerFacets (⟨759, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0760 : lowerComputed (⟨760, by decide⟩ : Fin 1069) = lowerFacets (⟨760, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0761 : lowerComputed (⟨761, by decide⟩ : Fin 1069) = lowerFacets (⟨761, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0762 : lowerComputed (⟨762, by decide⟩ : Fin 1069) = lowerFacets (⟨762, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0763 : lowerComputed (⟨763, by decide⟩ : Fin 1069) = lowerFacets (⟨763, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0764 : lowerComputed (⟨764, by decide⟩ : Fin 1069) = lowerFacets (⟨764, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0765 : lowerComputed (⟨765, by decide⟩ : Fin 1069) = lowerFacets (⟨765, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0766 : lowerComputed (⟨766, by decide⟩ : Fin 1069) = lowerFacets (⟨766, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0767 : lowerComputed (⟨767, by decide⟩ : Fin 1069) = lowerFacets (⟨767, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0768 : lowerComputed (⟨768, by decide⟩ : Fin 1069) = lowerFacets (⟨768, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0769 : lowerComputed (⟨769, by decide⟩ : Fin 1069) = lowerFacets (⟨769, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0770 : lowerComputed (⟨770, by decide⟩ : Fin 1069) = lowerFacets (⟨770, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0771 : lowerComputed (⟨771, by decide⟩ : Fin 1069) = lowerFacets (⟨771, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0772 : lowerComputed (⟨772, by decide⟩ : Fin 1069) = lowerFacets (⟨772, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0773 : lowerComputed (⟨773, by decide⟩ : Fin 1069) = lowerFacets (⟨773, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0774 : lowerComputed (⟨774, by decide⟩ : Fin 1069) = lowerFacets (⟨774, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0775 : lowerComputed (⟨775, by decide⟩ : Fin 1069) = lowerFacets (⟨775, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0776 : lowerComputed (⟨776, by decide⟩ : Fin 1069) = lowerFacets (⟨776, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0777 : lowerComputed (⟨777, by decide⟩ : Fin 1069) = lowerFacets (⟨777, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0778 : lowerComputed (⟨778, by decide⟩ : Fin 1069) = lowerFacets (⟨778, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0779 : lowerComputed (⟨779, by decide⟩ : Fin 1069) = lowerFacets (⟨779, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0780 : lowerComputed (⟨780, by decide⟩ : Fin 1069) = lowerFacets (⟨780, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0781 : lowerComputed (⟨781, by decide⟩ : Fin 1069) = lowerFacets (⟨781, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0782 : lowerComputed (⟨782, by decide⟩ : Fin 1069) = lowerFacets (⟨782, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0783 : lowerComputed (⟨783, by decide⟩ : Fin 1069) = lowerFacets (⟨783, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0784 : lowerComputed (⟨784, by decide⟩ : Fin 1069) = lowerFacets (⟨784, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0785 : lowerComputed (⟨785, by decide⟩ : Fin 1069) = lowerFacets (⟨785, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0786 : lowerComputed (⟨786, by decide⟩ : Fin 1069) = lowerFacets (⟨786, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0787 : lowerComputed (⟨787, by decide⟩ : Fin 1069) = lowerFacets (⟨787, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0788 : lowerComputed (⟨788, by decide⟩ : Fin 1069) = lowerFacets (⟨788, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0789 : lowerComputed (⟨789, by decide⟩ : Fin 1069) = lowerFacets (⟨789, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0790 : lowerComputed (⟨790, by decide⟩ : Fin 1069) = lowerFacets (⟨790, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0791 : lowerComputed (⟨791, by decide⟩ : Fin 1069) = lowerFacets (⟨791, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0792 : lowerComputed (⟨792, by decide⟩ : Fin 1069) = lowerFacets (⟨792, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0793 : lowerComputed (⟨793, by decide⟩ : Fin 1069) = lowerFacets (⟨793, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0794 : lowerComputed (⟨794, by decide⟩ : Fin 1069) = lowerFacets (⟨794, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0795 : lowerComputed (⟨795, by decide⟩ : Fin 1069) = lowerFacets (⟨795, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0796 : lowerComputed (⟨796, by decide⟩ : Fin 1069) = lowerFacets (⟨796, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0797 : lowerComputed (⟨797, by decide⟩ : Fin 1069) = lowerFacets (⟨797, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0798 : lowerComputed (⟨798, by decide⟩ : Fin 1069) = lowerFacets (⟨798, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0799 : lowerComputed (⟨799, by decide⟩ : Fin 1069) = lowerFacets (⟨799, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0800 : lowerComputed (⟨800, by decide⟩ : Fin 1069) = lowerFacets (⟨800, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0801 : lowerComputed (⟨801, by decide⟩ : Fin 1069) = lowerFacets (⟨801, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0802 : lowerComputed (⟨802, by decide⟩ : Fin 1069) = lowerFacets (⟨802, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0803 : lowerComputed (⟨803, by decide⟩ : Fin 1069) = lowerFacets (⟨803, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0804 : lowerComputed (⟨804, by decide⟩ : Fin 1069) = lowerFacets (⟨804, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0805 : lowerComputed (⟨805, by decide⟩ : Fin 1069) = lowerFacets (⟨805, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0806 : lowerComputed (⟨806, by decide⟩ : Fin 1069) = lowerFacets (⟨806, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0807 : lowerComputed (⟨807, by decide⟩ : Fin 1069) = lowerFacets (⟨807, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0808 : lowerComputed (⟨808, by decide⟩ : Fin 1069) = lowerFacets (⟨808, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0809 : lowerComputed (⟨809, by decide⟩ : Fin 1069) = lowerFacets (⟨809, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0810 : lowerComputed (⟨810, by decide⟩ : Fin 1069) = lowerFacets (⟨810, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0811 : lowerComputed (⟨811, by decide⟩ : Fin 1069) = lowerFacets (⟨811, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0812 : lowerComputed (⟨812, by decide⟩ : Fin 1069) = lowerFacets (⟨812, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0813 : lowerComputed (⟨813, by decide⟩ : Fin 1069) = lowerFacets (⟨813, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0814 : lowerComputed (⟨814, by decide⟩ : Fin 1069) = lowerFacets (⟨814, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0815 : lowerComputed (⟨815, by decide⟩ : Fin 1069) = lowerFacets (⟨815, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0816 : lowerComputed (⟨816, by decide⟩ : Fin 1069) = lowerFacets (⟨816, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0817 : lowerComputed (⟨817, by decide⟩ : Fin 1069) = lowerFacets (⟨817, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0818 : lowerComputed (⟨818, by decide⟩ : Fin 1069) = lowerFacets (⟨818, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0819 : lowerComputed (⟨819, by decide⟩ : Fin 1069) = lowerFacets (⟨819, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0820 : lowerComputed (⟨820, by decide⟩ : Fin 1069) = lowerFacets (⟨820, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0821 : lowerComputed (⟨821, by decide⟩ : Fin 1069) = lowerFacets (⟨821, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0822 : lowerComputed (⟨822, by decide⟩ : Fin 1069) = lowerFacets (⟨822, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0823 : lowerComputed (⟨823, by decide⟩ : Fin 1069) = lowerFacets (⟨823, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0824 : lowerComputed (⟨824, by decide⟩ : Fin 1069) = lowerFacets (⟨824, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0825 : lowerComputed (⟨825, by decide⟩ : Fin 1069) = lowerFacets (⟨825, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0826 : lowerComputed (⟨826, by decide⟩ : Fin 1069) = lowerFacets (⟨826, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0827 : lowerComputed (⟨827, by decide⟩ : Fin 1069) = lowerFacets (⟨827, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0828 : lowerComputed (⟨828, by decide⟩ : Fin 1069) = lowerFacets (⟨828, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0829 : lowerComputed (⟨829, by decide⟩ : Fin 1069) = lowerFacets (⟨829, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0830 : lowerComputed (⟨830, by decide⟩ : Fin 1069) = lowerFacets (⟨830, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0831 : lowerComputed (⟨831, by decide⟩ : Fin 1069) = lowerFacets (⟨831, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0832 : lowerComputed (⟨832, by decide⟩ : Fin 1069) = lowerFacets (⟨832, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0833 : lowerComputed (⟨833, by decide⟩ : Fin 1069) = lowerFacets (⟨833, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0834 : lowerComputed (⟨834, by decide⟩ : Fin 1069) = lowerFacets (⟨834, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0835 : lowerComputed (⟨835, by decide⟩ : Fin 1069) = lowerFacets (⟨835, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0836 : lowerComputed (⟨836, by decide⟩ : Fin 1069) = lowerFacets (⟨836, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0837 : lowerComputed (⟨837, by decide⟩ : Fin 1069) = lowerFacets (⟨837, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0838 : lowerComputed (⟨838, by decide⟩ : Fin 1069) = lowerFacets (⟨838, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0839 : lowerComputed (⟨839, by decide⟩ : Fin 1069) = lowerFacets (⟨839, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0840 : lowerComputed (⟨840, by decide⟩ : Fin 1069) = lowerFacets (⟨840, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0841 : lowerComputed (⟨841, by decide⟩ : Fin 1069) = lowerFacets (⟨841, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0842 : lowerComputed (⟨842, by decide⟩ : Fin 1069) = lowerFacets (⟨842, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0843 : lowerComputed (⟨843, by decide⟩ : Fin 1069) = lowerFacets (⟨843, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0844 : lowerComputed (⟨844, by decide⟩ : Fin 1069) = lowerFacets (⟨844, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0845 : lowerComputed (⟨845, by decide⟩ : Fin 1069) = lowerFacets (⟨845, by decide⟩ : Fin 1069) := by
  decide +kernel

end CubicalIndecomposability
