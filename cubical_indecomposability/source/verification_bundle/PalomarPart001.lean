module
public import verification_bundle.PalomarPart000
import all verification_bundle.PalomarPart000
public import foundation_bundle
public import incidence_bundle
public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
@[expose] public section

noncomputable section

/-!
# Consolidated verification sources

Generated only to avoid repeatedly loading the same pinned Mathlib files.
Public theorem statements and proofs preserve their original content.
See VerificationBundle.sources.json for exact source ranges, hashes, and private
helper alpha-renamings, topological source order, and scope adjustments.
-/

/- Original source: CubicalIndecomposability/FaceDataChecks/LowerFacets.lean -/
section VerificationSource000





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

theorem bundle_a018773121_bucketGroup0011 (i : Fin 1069)
    (hlo : 352 ≤ i.val) (hhi : i.val < 384) :
    i ∈ bundle_a018773121_anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bundle_a018773121_bucket0352
          ·
            have he : (⟨353, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 353 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0353
        ·
          by_cases h355 : i.val < 355
          ·
            have he : (⟨354, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 354 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0354
          ·
            have he : (⟨355, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 355 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0355
      ·
        by_cases h358 : i.val < 358
        ·
          by_cases h357 : i.val < 357
          ·
            have he : (⟨356, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 356 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0356
          ·
            have he : (⟨357, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 357 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0357
        ·
          by_cases h359 : i.val < 359
          ·
            have he : (⟨358, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 358 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0358
          ·
            have he : (⟨359, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 359 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0359
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
            simpa only [he] using bundle_a018773121_bucket0360
          ·
            have he : (⟨361, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 361 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0361
        ·
          by_cases h363 : i.val < 363
          ·
            have he : (⟨362, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 362 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0362
          ·
            have he : (⟨363, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 363 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0363
      ·
        by_cases h366 : i.val < 366
        ·
          by_cases h365 : i.val < 365
          ·
            have he : (⟨364, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 364 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0364
          ·
            have he : (⟨365, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 365 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0365
        ·
          by_cases h367 : i.val < 367
          ·
            have he : (⟨366, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 366 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0366
          ·
            have he : (⟨367, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 367 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0367
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
            simpa only [he] using bundle_a018773121_bucket0368
          ·
            have he : (⟨369, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 369 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0369
        ·
          by_cases h371 : i.val < 371
          ·
            have he : (⟨370, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 370 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0370
          ·
            have he : (⟨371, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 371 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0371
      ·
        by_cases h374 : i.val < 374
        ·
          by_cases h373 : i.val < 373
          ·
            have he : (⟨372, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 372 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0372
          ·
            have he : (⟨373, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 373 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0373
        ·
          by_cases h375 : i.val < 375
          ·
            have he : (⟨374, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 374 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0374
          ·
            have he : (⟨375, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 375 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0375
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
            simpa only [he] using bundle_a018773121_bucket0376
          ·
            have he : (⟨377, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 377 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0377
        ·
          by_cases h379 : i.val < 379
          ·
            have he : (⟨378, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 378 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0378
          ·
            have he : (⟨379, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 379 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0379
      ·
        by_cases h382 : i.val < 382
        ·
          by_cases h381 : i.val < 381
          ·
            have he : (⟨380, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 380 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0380
          ·
            have he : (⟨381, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 381 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0381
        ·
          by_cases h383 : i.val < 383
          ·
            have he : (⟨382, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 382 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0382
          ·
            have he : (⟨383, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 383 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0383

theorem bundle_a018773121_bucketGroup0012 (i : Fin 1069)
    (hlo : 384 ≤ i.val) (hhi : i.val < 416) :
    i ∈ bundle_a018773121_anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bundle_a018773121_bucket0384
          ·
            have he : (⟨385, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 385 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0385
        ·
          by_cases h387 : i.val < 387
          ·
            have he : (⟨386, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 386 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0386
          ·
            have he : (⟨387, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 387 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0387
      ·
        by_cases h390 : i.val < 390
        ·
          by_cases h389 : i.val < 389
          ·
            have he : (⟨388, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 388 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0388
          ·
            have he : (⟨389, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 389 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0389
        ·
          by_cases h391 : i.val < 391
          ·
            have he : (⟨390, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 390 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0390
          ·
            have he : (⟨391, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 391 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0391
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
            simpa only [he] using bundle_a018773121_bucket0392
          ·
            have he : (⟨393, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 393 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0393
        ·
          by_cases h395 : i.val < 395
          ·
            have he : (⟨394, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 394 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0394
          ·
            have he : (⟨395, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 395 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0395
      ·
        by_cases h398 : i.val < 398
        ·
          by_cases h397 : i.val < 397
          ·
            have he : (⟨396, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 396 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0396
          ·
            have he : (⟨397, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 397 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0397
        ·
          by_cases h399 : i.val < 399
          ·
            have he : (⟨398, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 398 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0398
          ·
            have he : (⟨399, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 399 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0399
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
            simpa only [he] using bundle_a018773121_bucket0400
          ·
            have he : (⟨401, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 401 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0401
        ·
          by_cases h403 : i.val < 403
          ·
            have he : (⟨402, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 402 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0402
          ·
            have he : (⟨403, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 403 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0403
      ·
        by_cases h406 : i.val < 406
        ·
          by_cases h405 : i.val < 405
          ·
            have he : (⟨404, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 404 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0404
          ·
            have he : (⟨405, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 405 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0405
        ·
          by_cases h407 : i.val < 407
          ·
            have he : (⟨406, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 406 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0406
          ·
            have he : (⟨407, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 407 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0407
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
            simpa only [he] using bundle_a018773121_bucket0408
          ·
            have he : (⟨409, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 409 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0409
        ·
          by_cases h411 : i.val < 411
          ·
            have he : (⟨410, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 410 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0410
          ·
            have he : (⟨411, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 411 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0411
      ·
        by_cases h414 : i.val < 414
        ·
          by_cases h413 : i.val < 413
          ·
            have he : (⟨412, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 412 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0412
          ·
            have he : (⟨413, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 413 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0413
        ·
          by_cases h415 : i.val < 415
          ·
            have he : (⟨414, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 414 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0414
          ·
            have he : (⟨415, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 415 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0415

theorem bundle_a018773121_bucketGroup0013 (i : Fin 1069)
    (hlo : 416 ≤ i.val) (hhi : i.val < 448) :
    i ∈ bundle_a018773121_anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bundle_a018773121_bucket0416
          ·
            have he : (⟨417, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 417 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0417
        ·
          by_cases h419 : i.val < 419
          ·
            have he : (⟨418, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 418 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0418
          ·
            have he : (⟨419, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 419 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0419
      ·
        by_cases h422 : i.val < 422
        ·
          by_cases h421 : i.val < 421
          ·
            have he : (⟨420, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 420 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0420
          ·
            have he : (⟨421, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 421 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0421
        ·
          by_cases h423 : i.val < 423
          ·
            have he : (⟨422, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 422 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0422
          ·
            have he : (⟨423, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 423 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0423
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
            simpa only [he] using bundle_a018773121_bucket0424
          ·
            have he : (⟨425, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 425 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0425
        ·
          by_cases h427 : i.val < 427
          ·
            have he : (⟨426, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 426 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0426
          ·
            have he : (⟨427, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 427 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0427
      ·
        by_cases h430 : i.val < 430
        ·
          by_cases h429 : i.val < 429
          ·
            have he : (⟨428, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 428 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0428
          ·
            have he : (⟨429, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 429 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0429
        ·
          by_cases h431 : i.val < 431
          ·
            have he : (⟨430, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 430 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0430
          ·
            have he : (⟨431, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 431 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0431
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
            simpa only [he] using bundle_a018773121_bucket0432
          ·
            have he : (⟨433, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 433 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0433
        ·
          by_cases h435 : i.val < 435
          ·
            have he : (⟨434, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 434 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0434
          ·
            have he : (⟨435, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 435 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0435
      ·
        by_cases h438 : i.val < 438
        ·
          by_cases h437 : i.val < 437
          ·
            have he : (⟨436, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 436 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0436
          ·
            have he : (⟨437, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 437 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0437
        ·
          by_cases h439 : i.val < 439
          ·
            have he : (⟨438, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 438 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0438
          ·
            have he : (⟨439, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 439 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0439
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
            simpa only [he] using bundle_a018773121_bucket0440
          ·
            have he : (⟨441, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 441 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0441
        ·
          by_cases h443 : i.val < 443
          ·
            have he : (⟨442, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 442 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0442
          ·
            have he : (⟨443, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 443 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0443
      ·
        by_cases h446 : i.val < 446
        ·
          by_cases h445 : i.val < 445
          ·
            have he : (⟨444, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 444 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0444
          ·
            have he : (⟨445, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 445 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0445
        ·
          by_cases h447 : i.val < 447
          ·
            have he : (⟨446, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 446 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0446
          ·
            have he : (⟨447, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 447 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0447

theorem bundle_a018773121_bucketGroup0014 (i : Fin 1069)
    (hlo : 448 ≤ i.val) (hhi : i.val < 480) :
    i ∈ bundle_a018773121_anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bundle_a018773121_bucket0448
          ·
            have he : (⟨449, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 449 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0449
        ·
          by_cases h451 : i.val < 451
          ·
            have he : (⟨450, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 450 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0450
          ·
            have he : (⟨451, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 451 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0451
      ·
        by_cases h454 : i.val < 454
        ·
          by_cases h453 : i.val < 453
          ·
            have he : (⟨452, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 452 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0452
          ·
            have he : (⟨453, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 453 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0453
        ·
          by_cases h455 : i.val < 455
          ·
            have he : (⟨454, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 454 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0454
          ·
            have he : (⟨455, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 455 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0455
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
            simpa only [he] using bundle_a018773121_bucket0456
          ·
            have he : (⟨457, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 457 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0457
        ·
          by_cases h459 : i.val < 459
          ·
            have he : (⟨458, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 458 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0458
          ·
            have he : (⟨459, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 459 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0459
      ·
        by_cases h462 : i.val < 462
        ·
          by_cases h461 : i.val < 461
          ·
            have he : (⟨460, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 460 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0460
          ·
            have he : (⟨461, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 461 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0461
        ·
          by_cases h463 : i.val < 463
          ·
            have he : (⟨462, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 462 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0462
          ·
            have he : (⟨463, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 463 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0463
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
            simpa only [he] using bundle_a018773121_bucket0464
          ·
            have he : (⟨465, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 465 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0465
        ·
          by_cases h467 : i.val < 467
          ·
            have he : (⟨466, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 466 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0466
          ·
            have he : (⟨467, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 467 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0467
      ·
        by_cases h470 : i.val < 470
        ·
          by_cases h469 : i.val < 469
          ·
            have he : (⟨468, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 468 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0468
          ·
            have he : (⟨469, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 469 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0469
        ·
          by_cases h471 : i.val < 471
          ·
            have he : (⟨470, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 470 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0470
          ·
            have he : (⟨471, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 471 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0471
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
            simpa only [he] using bundle_a018773121_bucket0472
          ·
            have he : (⟨473, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 473 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0473
        ·
          by_cases h475 : i.val < 475
          ·
            have he : (⟨474, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 474 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0474
          ·
            have he : (⟨475, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 475 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0475
      ·
        by_cases h478 : i.val < 478
        ·
          by_cases h477 : i.val < 477
          ·
            have he : (⟨476, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 476 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0476
          ·
            have he : (⟨477, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 477 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0477
        ·
          by_cases h479 : i.val < 479
          ·
            have he : (⟨478, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 478 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0478
          ·
            have he : (⟨479, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 479 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0479

theorem bundle_a018773121_bucketGroup0015 (i : Fin 1069)
    (hlo : 480 ≤ i.val) (hhi : i.val < 512) :
    i ∈ bundle_a018773121_anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bundle_a018773121_bucket0480
          ·
            have he : (⟨481, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 481 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0481
        ·
          by_cases h483 : i.val < 483
          ·
            have he : (⟨482, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 482 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0482
          ·
            have he : (⟨483, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 483 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0483
      ·
        by_cases h486 : i.val < 486
        ·
          by_cases h485 : i.val < 485
          ·
            have he : (⟨484, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 484 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0484
          ·
            have he : (⟨485, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 485 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0485
        ·
          by_cases h487 : i.val < 487
          ·
            have he : (⟨486, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 486 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0486
          ·
            have he : (⟨487, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 487 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0487
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
            simpa only [he] using bundle_a018773121_bucket0488
          ·
            have he : (⟨489, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 489 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0489
        ·
          by_cases h491 : i.val < 491
          ·
            have he : (⟨490, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 490 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0490
          ·
            have he : (⟨491, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 491 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0491
      ·
        by_cases h494 : i.val < 494
        ·
          by_cases h493 : i.val < 493
          ·
            have he : (⟨492, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 492 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0492
          ·
            have he : (⟨493, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 493 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0493
        ·
          by_cases h495 : i.val < 495
          ·
            have he : (⟨494, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 494 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0494
          ·
            have he : (⟨495, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 495 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0495
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
            simpa only [he] using bundle_a018773121_bucket0496
          ·
            have he : (⟨497, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 497 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0497
        ·
          by_cases h499 : i.val < 499
          ·
            have he : (⟨498, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 498 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0498
          ·
            have he : (⟨499, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 499 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0499
      ·
        by_cases h502 : i.val < 502
        ·
          by_cases h501 : i.val < 501
          ·
            have he : (⟨500, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 500 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0500
          ·
            have he : (⟨501, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 501 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0501
        ·
          by_cases h503 : i.val < 503
          ·
            have he : (⟨502, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 502 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0502
          ·
            have he : (⟨503, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 503 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0503
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
            simpa only [he] using bundle_a018773121_bucket0504
          ·
            have he : (⟨505, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 505 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0505
        ·
          by_cases h507 : i.val < 507
          ·
            have he : (⟨506, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 506 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0506
          ·
            have he : (⟨507, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 507 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0507
      ·
        by_cases h510 : i.val < 510
        ·
          by_cases h509 : i.val < 509
          ·
            have he : (⟨508, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 508 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0508
          ·
            have he : (⟨509, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 509 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0509
        ·
          by_cases h511 : i.val < 511
          ·
            have he : (⟨510, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 510 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0510
          ·
            have he : (⟨511, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 511 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0511

theorem bundle_a018773121_bucketGroup0016 (i : Fin 1069)
    (hlo : 512 ≤ i.val) (hhi : i.val < 544) :
    i ∈ bundle_a018773121_anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bundle_a018773121_bucket0512
          ·
            have he : (⟨513, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 513 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0513
        ·
          by_cases h515 : i.val < 515
          ·
            have he : (⟨514, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 514 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0514
          ·
            have he : (⟨515, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 515 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0515
      ·
        by_cases h518 : i.val < 518
        ·
          by_cases h517 : i.val < 517
          ·
            have he : (⟨516, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 516 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0516
          ·
            have he : (⟨517, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 517 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0517
        ·
          by_cases h519 : i.val < 519
          ·
            have he : (⟨518, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 518 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0518
          ·
            have he : (⟨519, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 519 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0519
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
            simpa only [he] using bundle_a018773121_bucket0520
          ·
            have he : (⟨521, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 521 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0521
        ·
          by_cases h523 : i.val < 523
          ·
            have he : (⟨522, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 522 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0522
          ·
            have he : (⟨523, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 523 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0523
      ·
        by_cases h526 : i.val < 526
        ·
          by_cases h525 : i.val < 525
          ·
            have he : (⟨524, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 524 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0524
          ·
            have he : (⟨525, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 525 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0525
        ·
          by_cases h527 : i.val < 527
          ·
            have he : (⟨526, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 526 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0526
          ·
            have he : (⟨527, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 527 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0527
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
            simpa only [he] using bundle_a018773121_bucket0528
          ·
            have he : (⟨529, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 529 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0529
        ·
          by_cases h531 : i.val < 531
          ·
            have he : (⟨530, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 530 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0530
          ·
            have he : (⟨531, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 531 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0531
      ·
        by_cases h534 : i.val < 534
        ·
          by_cases h533 : i.val < 533
          ·
            have he : (⟨532, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 532 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0532
          ·
            have he : (⟨533, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 533 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0533
        ·
          by_cases h535 : i.val < 535
          ·
            have he : (⟨534, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 534 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0534
          ·
            have he : (⟨535, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 535 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0535
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
            simpa only [he] using bundle_a018773121_bucket0536
          ·
            have he : (⟨537, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 537 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0537
        ·
          by_cases h539 : i.val < 539
          ·
            have he : (⟨538, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 538 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0538
          ·
            have he : (⟨539, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 539 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0539
      ·
        by_cases h542 : i.val < 542
        ·
          by_cases h541 : i.val < 541
          ·
            have he : (⟨540, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 540 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0540
          ·
            have he : (⟨541, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 541 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0541
        ·
          by_cases h543 : i.val < 543
          ·
            have he : (⟨542, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 542 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0542
          ·
            have he : (⟨543, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 543 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0543

theorem bundle_a018773121_bucketGroup0017 (i : Fin 1069)
    (hlo : 544 ≤ i.val) (hhi : i.val < 576) :
    i ∈ bundle_a018773121_anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bundle_a018773121_bucket0544
          ·
            have he : (⟨545, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 545 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0545
        ·
          by_cases h547 : i.val < 547
          ·
            have he : (⟨546, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 546 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0546
          ·
            have he : (⟨547, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 547 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0547
      ·
        by_cases h550 : i.val < 550
        ·
          by_cases h549 : i.val < 549
          ·
            have he : (⟨548, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 548 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0548
          ·
            have he : (⟨549, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 549 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0549
        ·
          by_cases h551 : i.val < 551
          ·
            have he : (⟨550, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 550 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0550
          ·
            have he : (⟨551, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 551 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0551
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
            simpa only [he] using bundle_a018773121_bucket0552
          ·
            have he : (⟨553, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 553 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0553
        ·
          by_cases h555 : i.val < 555
          ·
            have he : (⟨554, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 554 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0554
          ·
            have he : (⟨555, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 555 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0555
      ·
        by_cases h558 : i.val < 558
        ·
          by_cases h557 : i.val < 557
          ·
            have he : (⟨556, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 556 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0556
          ·
            have he : (⟨557, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 557 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0557
        ·
          by_cases h559 : i.val < 559
          ·
            have he : (⟨558, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 558 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0558
          ·
            have he : (⟨559, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 559 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0559
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
            simpa only [he] using bundle_a018773121_bucket0560
          ·
            have he : (⟨561, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 561 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0561
        ·
          by_cases h563 : i.val < 563
          ·
            have he : (⟨562, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 562 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0562
          ·
            have he : (⟨563, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 563 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0563
      ·
        by_cases h566 : i.val < 566
        ·
          by_cases h565 : i.val < 565
          ·
            have he : (⟨564, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 564 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0564
          ·
            have he : (⟨565, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 565 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0565
        ·
          by_cases h567 : i.val < 567
          ·
            have he : (⟨566, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 566 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0566
          ·
            have he : (⟨567, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 567 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0567
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
            simpa only [he] using bundle_a018773121_bucket0568
          ·
            have he : (⟨569, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 569 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0569
        ·
          by_cases h571 : i.val < 571
          ·
            have he : (⟨570, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 570 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0570
          ·
            have he : (⟨571, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 571 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0571
      ·
        by_cases h574 : i.val < 574
        ·
          by_cases h573 : i.val < 573
          ·
            have he : (⟨572, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 572 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0572
          ·
            have he : (⟨573, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 573 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0573
        ·
          by_cases h575 : i.val < 575
          ·
            have he : (⟨574, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 574 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0574
          ·
            have he : (⟨575, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 575 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0575

theorem bundle_a018773121_bucketGroup0018 (i : Fin 1069)
    (hlo : 576 ≤ i.val) (hhi : i.val < 608) :
    i ∈ bundle_a018773121_anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bundle_a018773121_bucket0576
          ·
            have he : (⟨577, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 577 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0577
        ·
          by_cases h579 : i.val < 579
          ·
            have he : (⟨578, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 578 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0578
          ·
            have he : (⟨579, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 579 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0579
      ·
        by_cases h582 : i.val < 582
        ·
          by_cases h581 : i.val < 581
          ·
            have he : (⟨580, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 580 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0580
          ·
            have he : (⟨581, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 581 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0581
        ·
          by_cases h583 : i.val < 583
          ·
            have he : (⟨582, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 582 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0582
          ·
            have he : (⟨583, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 583 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0583
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
            simpa only [he] using bundle_a018773121_bucket0584
          ·
            have he : (⟨585, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 585 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0585
        ·
          by_cases h587 : i.val < 587
          ·
            have he : (⟨586, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 586 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0586
          ·
            have he : (⟨587, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 587 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0587
      ·
        by_cases h590 : i.val < 590
        ·
          by_cases h589 : i.val < 589
          ·
            have he : (⟨588, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 588 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0588
          ·
            have he : (⟨589, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 589 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0589
        ·
          by_cases h591 : i.val < 591
          ·
            have he : (⟨590, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 590 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0590
          ·
            have he : (⟨591, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 591 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0591
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
            simpa only [he] using bundle_a018773121_bucket0592
          ·
            have he : (⟨593, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 593 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0593
        ·
          by_cases h595 : i.val < 595
          ·
            have he : (⟨594, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 594 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0594
          ·
            have he : (⟨595, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 595 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0595
      ·
        by_cases h598 : i.val < 598
        ·
          by_cases h597 : i.val < 597
          ·
            have he : (⟨596, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 596 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0596
          ·
            have he : (⟨597, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 597 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0597
        ·
          by_cases h599 : i.val < 599
          ·
            have he : (⟨598, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 598 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0598
          ·
            have he : (⟨599, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 599 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0599
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
            simpa only [he] using bundle_a018773121_bucket0600
          ·
            have he : (⟨601, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 601 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0601
        ·
          by_cases h603 : i.val < 603
          ·
            have he : (⟨602, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 602 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0602
          ·
            have he : (⟨603, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 603 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0603
      ·
        by_cases h606 : i.val < 606
        ·
          by_cases h605 : i.val < 605
          ·
            have he : (⟨604, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 604 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0604
          ·
            have he : (⟨605, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 605 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0605
        ·
          by_cases h607 : i.val < 607
          ·
            have he : (⟨606, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 606 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0606
          ·
            have he : (⟨607, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 607 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0607

theorem bundle_a018773121_bucketGroup0019 (i : Fin 1069)
    (hlo : 608 ≤ i.val) (hhi : i.val < 640) :
    i ∈ bundle_a018773121_anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bundle_a018773121_bucket0608
          ·
            have he : (⟨609, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 609 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0609
        ·
          by_cases h611 : i.val < 611
          ·
            have he : (⟨610, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 610 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0610
          ·
            have he : (⟨611, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 611 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0611
      ·
        by_cases h614 : i.val < 614
        ·
          by_cases h613 : i.val < 613
          ·
            have he : (⟨612, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 612 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0612
          ·
            have he : (⟨613, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 613 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0613
        ·
          by_cases h615 : i.val < 615
          ·
            have he : (⟨614, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 614 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0614
          ·
            have he : (⟨615, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 615 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0615
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
            simpa only [he] using bundle_a018773121_bucket0616
          ·
            have he : (⟨617, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 617 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0617
        ·
          by_cases h619 : i.val < 619
          ·
            have he : (⟨618, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 618 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0618
          ·
            have he : (⟨619, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 619 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0619
      ·
        by_cases h622 : i.val < 622
        ·
          by_cases h621 : i.val < 621
          ·
            have he : (⟨620, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 620 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0620
          ·
            have he : (⟨621, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 621 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0621
        ·
          by_cases h623 : i.val < 623
          ·
            have he : (⟨622, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 622 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0622
          ·
            have he : (⟨623, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 623 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0623
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
            simpa only [he] using bundle_a018773121_bucket0624
          ·
            have he : (⟨625, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 625 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0625
        ·
          by_cases h627 : i.val < 627
          ·
            have he : (⟨626, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 626 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0626
          ·
            have he : (⟨627, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 627 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0627
      ·
        by_cases h630 : i.val < 630
        ·
          by_cases h629 : i.val < 629
          ·
            have he : (⟨628, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 628 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0628
          ·
            have he : (⟨629, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 629 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0629
        ·
          by_cases h631 : i.val < 631
          ·
            have he : (⟨630, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 630 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0630
          ·
            have he : (⟨631, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 631 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0631
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
            simpa only [he] using bundle_a018773121_bucket0632
          ·
            have he : (⟨633, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 633 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0633
        ·
          by_cases h635 : i.val < 635
          ·
            have he : (⟨634, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 634 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0634
          ·
            have he : (⟨635, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 635 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0635
      ·
        by_cases h638 : i.val < 638
        ·
          by_cases h637 : i.val < 637
          ·
            have he : (⟨636, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 636 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0636
          ·
            have he : (⟨637, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 637 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0637
        ·
          by_cases h639 : i.val < 639
          ·
            have he : (⟨638, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 638 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0638
          ·
            have he : (⟨639, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 639 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0639

theorem bundle_a018773121_bucketGroup0020 (i : Fin 1069)
    (hlo : 640 ≤ i.val) (hhi : i.val < 672) :
    i ∈ bundle_a018773121_anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bundle_a018773121_bucket0640
          ·
            have he : (⟨641, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 641 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0641
        ·
          by_cases h643 : i.val < 643
          ·
            have he : (⟨642, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 642 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0642
          ·
            have he : (⟨643, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 643 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0643
      ·
        by_cases h646 : i.val < 646
        ·
          by_cases h645 : i.val < 645
          ·
            have he : (⟨644, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 644 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0644
          ·
            have he : (⟨645, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 645 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0645
        ·
          by_cases h647 : i.val < 647
          ·
            have he : (⟨646, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 646 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0646
          ·
            have he : (⟨647, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 647 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0647
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
            simpa only [he] using bundle_a018773121_bucket0648
          ·
            have he : (⟨649, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 649 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0649
        ·
          by_cases h651 : i.val < 651
          ·
            have he : (⟨650, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 650 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0650
          ·
            have he : (⟨651, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 651 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0651
      ·
        by_cases h654 : i.val < 654
        ·
          by_cases h653 : i.val < 653
          ·
            have he : (⟨652, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 652 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0652
          ·
            have he : (⟨653, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 653 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0653
        ·
          by_cases h655 : i.val < 655
          ·
            have he : (⟨654, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 654 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0654
          ·
            have he : (⟨655, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 655 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0655
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
            simpa only [he] using bundle_a018773121_bucket0656
          ·
            have he : (⟨657, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 657 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0657
        ·
          by_cases h659 : i.val < 659
          ·
            have he : (⟨658, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 658 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0658
          ·
            have he : (⟨659, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 659 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0659
      ·
        by_cases h662 : i.val < 662
        ·
          by_cases h661 : i.val < 661
          ·
            have he : (⟨660, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 660 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0660
          ·
            have he : (⟨661, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 661 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0661
        ·
          by_cases h663 : i.val < 663
          ·
            have he : (⟨662, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 662 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0662
          ·
            have he : (⟨663, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 663 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0663
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
            simpa only [he] using bundle_a018773121_bucket0664
          ·
            have he : (⟨665, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 665 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0665
        ·
          by_cases h667 : i.val < 667
          ·
            have he : (⟨666, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 666 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0666
          ·
            have he : (⟨667, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 667 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0667
      ·
        by_cases h670 : i.val < 670
        ·
          by_cases h669 : i.val < 669
          ·
            have he : (⟨668, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 668 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0668
          ·
            have he : (⟨669, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 669 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0669
        ·
          by_cases h671 : i.val < 671
          ·
            have he : (⟨670, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 670 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0670
          ·
            have he : (⟨671, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 671 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0671

theorem bundle_a018773121_bucketGroup0021 (i : Fin 1069)
    (hlo : 672 ≤ i.val) (hhi : i.val < 704) :
    i ∈ bundle_a018773121_anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bundle_a018773121_bucket0672
          ·
            have he : (⟨673, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 673 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0673
        ·
          by_cases h675 : i.val < 675
          ·
            have he : (⟨674, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 674 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0674
          ·
            have he : (⟨675, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 675 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0675
      ·
        by_cases h678 : i.val < 678
        ·
          by_cases h677 : i.val < 677
          ·
            have he : (⟨676, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 676 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0676
          ·
            have he : (⟨677, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 677 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0677
        ·
          by_cases h679 : i.val < 679
          ·
            have he : (⟨678, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 678 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0678
          ·
            have he : (⟨679, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 679 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0679
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
            simpa only [he] using bundle_a018773121_bucket0680
          ·
            have he : (⟨681, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 681 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0681
        ·
          by_cases h683 : i.val < 683
          ·
            have he : (⟨682, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 682 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0682
          ·
            have he : (⟨683, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 683 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0683
      ·
        by_cases h686 : i.val < 686
        ·
          by_cases h685 : i.val < 685
          ·
            have he : (⟨684, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 684 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0684
          ·
            have he : (⟨685, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 685 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0685
        ·
          by_cases h687 : i.val < 687
          ·
            have he : (⟨686, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 686 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0686
          ·
            have he : (⟨687, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 687 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0687
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
            simpa only [he] using bundle_a018773121_bucket0688
          ·
            have he : (⟨689, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 689 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0689
        ·
          by_cases h691 : i.val < 691
          ·
            have he : (⟨690, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 690 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0690
          ·
            have he : (⟨691, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 691 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0691
      ·
        by_cases h694 : i.val < 694
        ·
          by_cases h693 : i.val < 693
          ·
            have he : (⟨692, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 692 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0692
          ·
            have he : (⟨693, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 693 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0693
        ·
          by_cases h695 : i.val < 695
          ·
            have he : (⟨694, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 694 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0694
          ·
            have he : (⟨695, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 695 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0695
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
            simpa only [he] using bundle_a018773121_bucket0696
          ·
            have he : (⟨697, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 697 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0697
        ·
          by_cases h699 : i.val < 699
          ·
            have he : (⟨698, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 698 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0698
          ·
            have he : (⟨699, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 699 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0699
      ·
        by_cases h702 : i.val < 702
        ·
          by_cases h701 : i.val < 701
          ·
            have he : (⟨700, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 700 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0700
          ·
            have he : (⟨701, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 701 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0701
        ·
          by_cases h703 : i.val < 703
          ·
            have he : (⟨702, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 702 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0702
          ·
            have he : (⟨703, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 703 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0703

theorem bundle_a018773121_bucketGroup0022 (i : Fin 1069)
    (hlo : 704 ≤ i.val) (hhi : i.val < 736) :
    i ∈ bundle_a018773121_anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bundle_a018773121_bucket0704
          ·
            have he : (⟨705, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 705 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0705
        ·
          by_cases h707 : i.val < 707
          ·
            have he : (⟨706, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 706 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0706
          ·
            have he : (⟨707, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 707 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0707
      ·
        by_cases h710 : i.val < 710
        ·
          by_cases h709 : i.val < 709
          ·
            have he : (⟨708, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 708 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0708
          ·
            have he : (⟨709, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 709 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0709
        ·
          by_cases h711 : i.val < 711
          ·
            have he : (⟨710, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 710 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0710
          ·
            have he : (⟨711, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 711 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0711
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
            simpa only [he] using bundle_a018773121_bucket0712
          ·
            have he : (⟨713, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 713 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0713
        ·
          by_cases h715 : i.val < 715
          ·
            have he : (⟨714, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 714 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0714
          ·
            have he : (⟨715, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 715 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0715
      ·
        by_cases h718 : i.val < 718
        ·
          by_cases h717 : i.val < 717
          ·
            have he : (⟨716, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 716 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0716
          ·
            have he : (⟨717, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 717 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0717
        ·
          by_cases h719 : i.val < 719
          ·
            have he : (⟨718, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 718 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0718
          ·
            have he : (⟨719, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 719 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0719
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
            simpa only [he] using bundle_a018773121_bucket0720
          ·
            have he : (⟨721, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 721 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0721
        ·
          by_cases h723 : i.val < 723
          ·
            have he : (⟨722, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 722 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0722
          ·
            have he : (⟨723, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 723 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0723
      ·
        by_cases h726 : i.val < 726
        ·
          by_cases h725 : i.val < 725
          ·
            have he : (⟨724, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 724 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0724
          ·
            have he : (⟨725, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 725 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0725
        ·
          by_cases h727 : i.val < 727
          ·
            have he : (⟨726, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 726 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0726
          ·
            have he : (⟨727, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 727 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0727
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
            simpa only [he] using bundle_a018773121_bucket0728
          ·
            have he : (⟨729, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 729 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0729
        ·
          by_cases h731 : i.val < 731
          ·
            have he : (⟨730, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 730 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0730
          ·
            have he : (⟨731, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 731 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0731
      ·
        by_cases h734 : i.val < 734
        ·
          by_cases h733 : i.val < 733
          ·
            have he : (⟨732, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 732 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0732
          ·
            have he : (⟨733, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 733 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0733
        ·
          by_cases h735 : i.val < 735
          ·
            have he : (⟨734, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 734 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0734
          ·
            have he : (⟨735, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 735 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0735

theorem bundle_a018773121_bucketGroup0023 (i : Fin 1069)
    (hlo : 736 ≤ i.val) (hhi : i.val < 768) :
    i ∈ bundle_a018773121_anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bundle_a018773121_bucket0736
          ·
            have he : (⟨737, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 737 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0737
        ·
          by_cases h739 : i.val < 739
          ·
            have he : (⟨738, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 738 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0738
          ·
            have he : (⟨739, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 739 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0739
      ·
        by_cases h742 : i.val < 742
        ·
          by_cases h741 : i.val < 741
          ·
            have he : (⟨740, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 740 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0740
          ·
            have he : (⟨741, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 741 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0741
        ·
          by_cases h743 : i.val < 743
          ·
            have he : (⟨742, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 742 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0742
          ·
            have he : (⟨743, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 743 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0743
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
            simpa only [he] using bundle_a018773121_bucket0744
          ·
            have he : (⟨745, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 745 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0745
        ·
          by_cases h747 : i.val < 747
          ·
            have he : (⟨746, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 746 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0746
          ·
            have he : (⟨747, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 747 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0747
      ·
        by_cases h750 : i.val < 750
        ·
          by_cases h749 : i.val < 749
          ·
            have he : (⟨748, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 748 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0748
          ·
            have he : (⟨749, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 749 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0749
        ·
          by_cases h751 : i.val < 751
          ·
            have he : (⟨750, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 750 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0750
          ·
            have he : (⟨751, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 751 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0751
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
            simpa only [he] using bundle_a018773121_bucket0752
          ·
            have he : (⟨753, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 753 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0753
        ·
          by_cases h755 : i.val < 755
          ·
            have he : (⟨754, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 754 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0754
          ·
            have he : (⟨755, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 755 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0755
      ·
        by_cases h758 : i.val < 758
        ·
          by_cases h757 : i.val < 757
          ·
            have he : (⟨756, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 756 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0756
          ·
            have he : (⟨757, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 757 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0757
        ·
          by_cases h759 : i.val < 759
          ·
            have he : (⟨758, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 758 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0758
          ·
            have he : (⟨759, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 759 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0759
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
            simpa only [he] using bundle_a018773121_bucket0760
          ·
            have he : (⟨761, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 761 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0761
        ·
          by_cases h763 : i.val < 763
          ·
            have he : (⟨762, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 762 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0762
          ·
            have he : (⟨763, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 763 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0763
      ·
        by_cases h766 : i.val < 766
        ·
          by_cases h765 : i.val < 765
          ·
            have he : (⟨764, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 764 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0764
          ·
            have he : (⟨765, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 765 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0765
        ·
          by_cases h767 : i.val < 767
          ·
            have he : (⟨766, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 766 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0766
          ·
            have he : (⟨767, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 767 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0767

theorem bundle_a018773121_bucketGroup0024 (i : Fin 1069)
    (hlo : 768 ≤ i.val) (hhi : i.val < 800) :
    i ∈ bundle_a018773121_anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bundle_a018773121_bucket0768
          ·
            have he : (⟨769, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 769 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0769
        ·
          by_cases h771 : i.val < 771
          ·
            have he : (⟨770, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 770 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0770
          ·
            have he : (⟨771, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 771 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0771
      ·
        by_cases h774 : i.val < 774
        ·
          by_cases h773 : i.val < 773
          ·
            have he : (⟨772, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 772 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0772
          ·
            have he : (⟨773, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 773 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0773
        ·
          by_cases h775 : i.val < 775
          ·
            have he : (⟨774, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 774 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0774
          ·
            have he : (⟨775, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 775 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0775
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
            simpa only [he] using bundle_a018773121_bucket0776
          ·
            have he : (⟨777, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 777 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0777
        ·
          by_cases h779 : i.val < 779
          ·
            have he : (⟨778, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 778 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0778
          ·
            have he : (⟨779, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 779 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0779
      ·
        by_cases h782 : i.val < 782
        ·
          by_cases h781 : i.val < 781
          ·
            have he : (⟨780, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 780 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0780
          ·
            have he : (⟨781, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 781 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0781
        ·
          by_cases h783 : i.val < 783
          ·
            have he : (⟨782, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 782 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0782
          ·
            have he : (⟨783, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 783 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0783
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
            simpa only [he] using bundle_a018773121_bucket0784
          ·
            have he : (⟨785, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 785 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0785
        ·
          by_cases h787 : i.val < 787
          ·
            have he : (⟨786, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 786 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0786
          ·
            have he : (⟨787, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 787 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0787
      ·
        by_cases h790 : i.val < 790
        ·
          by_cases h789 : i.val < 789
          ·
            have he : (⟨788, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 788 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0788
          ·
            have he : (⟨789, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 789 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0789
        ·
          by_cases h791 : i.val < 791
          ·
            have he : (⟨790, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 790 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0790
          ·
            have he : (⟨791, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 791 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0791
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
            simpa only [he] using bundle_a018773121_bucket0792
          ·
            have he : (⟨793, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 793 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0793
        ·
          by_cases h795 : i.val < 795
          ·
            have he : (⟨794, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 794 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0794
          ·
            have he : (⟨795, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 795 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0795
      ·
        by_cases h798 : i.val < 798
        ·
          by_cases h797 : i.val < 797
          ·
            have he : (⟨796, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 796 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0796
          ·
            have he : (⟨797, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 797 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0797
        ·
          by_cases h799 : i.val < 799
          ·
            have he : (⟨798, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 798 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0798
          ·
            have he : (⟨799, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 799 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0799

theorem bundle_a018773121_bucketGroup0025 (i : Fin 1069)
    (hlo : 800 ≤ i.val) (hhi : i.val < 832) :
    i ∈ bundle_a018773121_anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bundle_a018773121_bucket0800
          ·
            have he : (⟨801, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 801 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0801
        ·
          by_cases h803 : i.val < 803
          ·
            have he : (⟨802, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 802 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0802
          ·
            have he : (⟨803, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 803 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0803
      ·
        by_cases h806 : i.val < 806
        ·
          by_cases h805 : i.val < 805
          ·
            have he : (⟨804, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 804 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0804
          ·
            have he : (⟨805, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 805 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0805
        ·
          by_cases h807 : i.val < 807
          ·
            have he : (⟨806, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 806 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0806
          ·
            have he : (⟨807, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 807 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0807
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
            simpa only [he] using bundle_a018773121_bucket0808
          ·
            have he : (⟨809, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 809 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0809
        ·
          by_cases h811 : i.val < 811
          ·
            have he : (⟨810, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 810 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0810
          ·
            have he : (⟨811, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 811 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0811
      ·
        by_cases h814 : i.val < 814
        ·
          by_cases h813 : i.val < 813
          ·
            have he : (⟨812, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 812 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0812
          ·
            have he : (⟨813, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 813 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0813
        ·
          by_cases h815 : i.val < 815
          ·
            have he : (⟨814, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 814 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0814
          ·
            have he : (⟨815, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 815 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0815
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
            simpa only [he] using bundle_a018773121_bucket0816
          ·
            have he : (⟨817, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 817 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0817
        ·
          by_cases h819 : i.val < 819
          ·
            have he : (⟨818, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 818 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0818
          ·
            have he : (⟨819, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 819 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0819
      ·
        by_cases h822 : i.val < 822
        ·
          by_cases h821 : i.val < 821
          ·
            have he : (⟨820, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 820 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0820
          ·
            have he : (⟨821, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 821 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0821
        ·
          by_cases h823 : i.val < 823
          ·
            have he : (⟨822, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 822 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0822
          ·
            have he : (⟨823, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 823 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0823
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
            simpa only [he] using bundle_a018773121_bucket0824
          ·
            have he : (⟨825, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 825 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0825
        ·
          by_cases h827 : i.val < 827
          ·
            have he : (⟨826, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 826 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0826
          ·
            have he : (⟨827, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 827 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0827
      ·
        by_cases h830 : i.val < 830
        ·
          by_cases h829 : i.val < 829
          ·
            have he : (⟨828, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 828 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0828
          ·
            have he : (⟨829, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 829 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0829
        ·
          by_cases h831 : i.val < 831
          ·
            have he : (⟨830, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 830 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0830
          ·
            have he : (⟨831, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 831 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0831

theorem bundle_a018773121_bucketGroup0026 (i : Fin 1069)
    (hlo : 832 ≤ i.val) (hhi : i.val < 864) :
    i ∈ bundle_a018773121_anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bundle_a018773121_bucket0832
          ·
            have he : (⟨833, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 833 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0833
        ·
          by_cases h835 : i.val < 835
          ·
            have he : (⟨834, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 834 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0834
          ·
            have he : (⟨835, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 835 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0835
      ·
        by_cases h838 : i.val < 838
        ·
          by_cases h837 : i.val < 837
          ·
            have he : (⟨836, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 836 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0836
          ·
            have he : (⟨837, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 837 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0837
        ·
          by_cases h839 : i.val < 839
          ·
            have he : (⟨838, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 838 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0838
          ·
            have he : (⟨839, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 839 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0839
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
            simpa only [he] using bundle_a018773121_bucket0840
          ·
            have he : (⟨841, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 841 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0841
        ·
          by_cases h843 : i.val < 843
          ·
            have he : (⟨842, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 842 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0842
          ·
            have he : (⟨843, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 843 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0843
      ·
        by_cases h846 : i.val < 846
        ·
          by_cases h845 : i.val < 845
          ·
            have he : (⟨844, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 844 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0844
          ·
            have he : (⟨845, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 845 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0845
        ·
          by_cases h847 : i.val < 847
          ·
            have he : (⟨846, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 846 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0846
          ·
            have he : (⟨847, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 847 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0847
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
            simpa only [he] using bundle_a018773121_bucket0848
          ·
            have he : (⟨849, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 849 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0849
        ·
          by_cases h851 : i.val < 851
          ·
            have he : (⟨850, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 850 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0850
          ·
            have he : (⟨851, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 851 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0851
      ·
        by_cases h854 : i.val < 854
        ·
          by_cases h853 : i.val < 853
          ·
            have he : (⟨852, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 852 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0852
          ·
            have he : (⟨853, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 853 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0853
        ·
          by_cases h855 : i.val < 855
          ·
            have he : (⟨854, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 854 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0854
          ·
            have he : (⟨855, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 855 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0855
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
            simpa only [he] using bundle_a018773121_bucket0856
          ·
            have he : (⟨857, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 857 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0857
        ·
          by_cases h859 : i.val < 859
          ·
            have he : (⟨858, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 858 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0858
          ·
            have he : (⟨859, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 859 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0859
      ·
        by_cases h862 : i.val < 862
        ·
          by_cases h861 : i.val < 861
          ·
            have he : (⟨860, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 860 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0860
          ·
            have he : (⟨861, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 861 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0861
        ·
          by_cases h863 : i.val < 863
          ·
            have he : (⟨862, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 862 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0862
          ·
            have he : (⟨863, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 863 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0863

theorem bundle_a018773121_bucketGroup0027 (i : Fin 1069)
    (hlo : 864 ≤ i.val) (hhi : i.val < 896) :
    i ∈ bundle_a018773121_anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bundle_a018773121_bucket0864
          ·
            have he : (⟨865, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 865 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0865
        ·
          by_cases h867 : i.val < 867
          ·
            have he : (⟨866, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 866 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0866
          ·
            have he : (⟨867, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 867 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0867
      ·
        by_cases h870 : i.val < 870
        ·
          by_cases h869 : i.val < 869
          ·
            have he : (⟨868, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 868 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0868
          ·
            have he : (⟨869, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 869 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0869
        ·
          by_cases h871 : i.val < 871
          ·
            have he : (⟨870, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 870 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0870
          ·
            have he : (⟨871, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 871 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0871
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
            simpa only [he] using bundle_a018773121_bucket0872
          ·
            have he : (⟨873, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 873 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0873
        ·
          by_cases h875 : i.val < 875
          ·
            have he : (⟨874, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 874 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0874
          ·
            have he : (⟨875, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 875 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0875
      ·
        by_cases h878 : i.val < 878
        ·
          by_cases h877 : i.val < 877
          ·
            have he : (⟨876, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 876 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0876
          ·
            have he : (⟨877, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 877 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0877
        ·
          by_cases h879 : i.val < 879
          ·
            have he : (⟨878, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 878 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0878
          ·
            have he : (⟨879, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 879 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0879
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
            simpa only [he] using bundle_a018773121_bucket0880
          ·
            have he : (⟨881, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 881 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0881
        ·
          by_cases h883 : i.val < 883
          ·
            have he : (⟨882, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 882 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0882
          ·
            have he : (⟨883, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 883 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0883
      ·
        by_cases h886 : i.val < 886
        ·
          by_cases h885 : i.val < 885
          ·
            have he : (⟨884, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 884 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0884
          ·
            have he : (⟨885, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 885 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0885
        ·
          by_cases h887 : i.val < 887
          ·
            have he : (⟨886, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 886 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0886
          ·
            have he : (⟨887, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 887 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0887
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
            simpa only [he] using bundle_a018773121_bucket0888
          ·
            have he : (⟨889, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 889 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0889
        ·
          by_cases h891 : i.val < 891
          ·
            have he : (⟨890, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 890 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0890
          ·
            have he : (⟨891, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 891 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0891
      ·
        by_cases h894 : i.val < 894
        ·
          by_cases h893 : i.val < 893
          ·
            have he : (⟨892, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 892 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0892
          ·
            have he : (⟨893, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 893 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0893
        ·
          by_cases h895 : i.val < 895
          ·
            have he : (⟨894, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 894 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0894
          ·
            have he : (⟨895, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 895 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0895

theorem bundle_a018773121_bucketGroup0028 (i : Fin 1069)
    (hlo : 896 ≤ i.val) (hhi : i.val < 928) :
    i ∈ bundle_a018773121_anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bundle_a018773121_bucket0896
          ·
            have he : (⟨897, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 897 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0897
        ·
          by_cases h899 : i.val < 899
          ·
            have he : (⟨898, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 898 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0898
          ·
            have he : (⟨899, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 899 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0899
      ·
        by_cases h902 : i.val < 902
        ·
          by_cases h901 : i.val < 901
          ·
            have he : (⟨900, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 900 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0900
          ·
            have he : (⟨901, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 901 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0901
        ·
          by_cases h903 : i.val < 903
          ·
            have he : (⟨902, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 902 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0902
          ·
            have he : (⟨903, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 903 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0903
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
            simpa only [he] using bundle_a018773121_bucket0904
          ·
            have he : (⟨905, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 905 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0905
        ·
          by_cases h907 : i.val < 907
          ·
            have he : (⟨906, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 906 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0906
          ·
            have he : (⟨907, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 907 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0907
      ·
        by_cases h910 : i.val < 910
        ·
          by_cases h909 : i.val < 909
          ·
            have he : (⟨908, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 908 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0908
          ·
            have he : (⟨909, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 909 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0909
        ·
          by_cases h911 : i.val < 911
          ·
            have he : (⟨910, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 910 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0910
          ·
            have he : (⟨911, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 911 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0911
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
            simpa only [he] using bundle_a018773121_bucket0912
          ·
            have he : (⟨913, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 913 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0913
        ·
          by_cases h915 : i.val < 915
          ·
            have he : (⟨914, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 914 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0914
          ·
            have he : (⟨915, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 915 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0915
      ·
        by_cases h918 : i.val < 918
        ·
          by_cases h917 : i.val < 917
          ·
            have he : (⟨916, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 916 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0916
          ·
            have he : (⟨917, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 917 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0917
        ·
          by_cases h919 : i.val < 919
          ·
            have he : (⟨918, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 918 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0918
          ·
            have he : (⟨919, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 919 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0919
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
            simpa only [he] using bundle_a018773121_bucket0920
          ·
            have he : (⟨921, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 921 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0921
        ·
          by_cases h923 : i.val < 923
          ·
            have he : (⟨922, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 922 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0922
          ·
            have he : (⟨923, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 923 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0923
      ·
        by_cases h926 : i.val < 926
        ·
          by_cases h925 : i.val < 925
          ·
            have he : (⟨924, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 924 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0924
          ·
            have he : (⟨925, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 925 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0925
        ·
          by_cases h927 : i.val < 927
          ·
            have he : (⟨926, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 926 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0926
          ·
            have he : (⟨927, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 927 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0927

theorem bundle_a018773121_bucketGroup0029 (i : Fin 1069)
    (hlo : 928 ≤ i.val) (hhi : i.val < 960) :
    i ∈ bundle_a018773121_anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bundle_a018773121_bucket0928
          ·
            have he : (⟨929, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 929 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0929
        ·
          by_cases h931 : i.val < 931
          ·
            have he : (⟨930, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 930 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0930
          ·
            have he : (⟨931, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 931 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0931
      ·
        by_cases h934 : i.val < 934
        ·
          by_cases h933 : i.val < 933
          ·
            have he : (⟨932, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 932 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0932
          ·
            have he : (⟨933, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 933 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0933
        ·
          by_cases h935 : i.val < 935
          ·
            have he : (⟨934, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 934 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0934
          ·
            have he : (⟨935, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 935 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0935
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
            simpa only [he] using bundle_a018773121_bucket0936
          ·
            have he : (⟨937, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 937 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0937
        ·
          by_cases h939 : i.val < 939
          ·
            have he : (⟨938, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 938 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0938
          ·
            have he : (⟨939, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 939 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0939
      ·
        by_cases h942 : i.val < 942
        ·
          by_cases h941 : i.val < 941
          ·
            have he : (⟨940, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 940 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0940
          ·
            have he : (⟨941, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 941 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0941
        ·
          by_cases h943 : i.val < 943
          ·
            have he : (⟨942, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 942 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0942
          ·
            have he : (⟨943, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 943 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0943
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
            simpa only [he] using bundle_a018773121_bucket0944
          ·
            have he : (⟨945, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 945 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0945
        ·
          by_cases h947 : i.val < 947
          ·
            have he : (⟨946, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 946 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0946
          ·
            have he : (⟨947, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 947 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0947
      ·
        by_cases h950 : i.val < 950
        ·
          by_cases h949 : i.val < 949
          ·
            have he : (⟨948, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 948 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0948
          ·
            have he : (⟨949, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 949 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0949
        ·
          by_cases h951 : i.val < 951
          ·
            have he : (⟨950, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 950 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0950
          ·
            have he : (⟨951, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 951 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0951
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
            simpa only [he] using bundle_a018773121_bucket0952
          ·
            have he : (⟨953, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 953 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0953
        ·
          by_cases h955 : i.val < 955
          ·
            have he : (⟨954, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 954 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0954
          ·
            have he : (⟨955, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 955 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0955
      ·
        by_cases h958 : i.val < 958
        ·
          by_cases h957 : i.val < 957
          ·
            have he : (⟨956, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 956 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0956
          ·
            have he : (⟨957, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 957 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0957
        ·
          by_cases h959 : i.val < 959
          ·
            have he : (⟨958, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 958 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0958
          ·
            have he : (⟨959, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 959 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0959

theorem bundle_a018773121_bucketGroup0030 (i : Fin 1069)
    (hlo : 960 ≤ i.val) (hhi : i.val < 992) :
    i ∈ bundle_a018773121_anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bundle_a018773121_bucket0960
          ·
            have he : (⟨961, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 961 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0961
        ·
          by_cases h963 : i.val < 963
          ·
            have he : (⟨962, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 962 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0962
          ·
            have he : (⟨963, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 963 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0963
      ·
        by_cases h966 : i.val < 966
        ·
          by_cases h965 : i.val < 965
          ·
            have he : (⟨964, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 964 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0964
          ·
            have he : (⟨965, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 965 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0965
        ·
          by_cases h967 : i.val < 967
          ·
            have he : (⟨966, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 966 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0966
          ·
            have he : (⟨967, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 967 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0967
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
            simpa only [he] using bundle_a018773121_bucket0968
          ·
            have he : (⟨969, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 969 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0969
        ·
          by_cases h971 : i.val < 971
          ·
            have he : (⟨970, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 970 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0970
          ·
            have he : (⟨971, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 971 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0971
      ·
        by_cases h974 : i.val < 974
        ·
          by_cases h973 : i.val < 973
          ·
            have he : (⟨972, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 972 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0972
          ·
            have he : (⟨973, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 973 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0973
        ·
          by_cases h975 : i.val < 975
          ·
            have he : (⟨974, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 974 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0974
          ·
            have he : (⟨975, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 975 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0975
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
            simpa only [he] using bundle_a018773121_bucket0976
          ·
            have he : (⟨977, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 977 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0977
        ·
          by_cases h979 : i.val < 979
          ·
            have he : (⟨978, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 978 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0978
          ·
            have he : (⟨979, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 979 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0979
      ·
        by_cases h982 : i.val < 982
        ·
          by_cases h981 : i.val < 981
          ·
            have he : (⟨980, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 980 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0980
          ·
            have he : (⟨981, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 981 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0981
        ·
          by_cases h983 : i.val < 983
          ·
            have he : (⟨982, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 982 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0982
          ·
            have he : (⟨983, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 983 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0983
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
            simpa only [he] using bundle_a018773121_bucket0984
          ·
            have he : (⟨985, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 985 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0985
        ·
          by_cases h987 : i.val < 987
          ·
            have he : (⟨986, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 986 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0986
          ·
            have he : (⟨987, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 987 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0987
      ·
        by_cases h990 : i.val < 990
        ·
          by_cases h989 : i.val < 989
          ·
            have he : (⟨988, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 988 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0988
          ·
            have he : (⟨989, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 989 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0989
        ·
          by_cases h991 : i.val < 991
          ·
            have he : (⟨990, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 990 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0990
          ·
            have he : (⟨991, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 991 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0991

theorem bundle_a018773121_bucketGroup0031 (i : Fin 1069)
    (hlo : 992 ≤ i.val) (hhi : i.val < 1024) :
    i ∈ bundle_a018773121_anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bundle_a018773121_bucket0992
          ·
            have he : (⟨993, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 993 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0993
        ·
          by_cases h995 : i.val < 995
          ·
            have he : (⟨994, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 994 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0994
          ·
            have he : (⟨995, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 995 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0995
      ·
        by_cases h998 : i.val < 998
        ·
          by_cases h997 : i.val < 997
          ·
            have he : (⟨996, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 996 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0996
          ·
            have he : (⟨997, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 997 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0997
        ·
          by_cases h999 : i.val < 999
          ·
            have he : (⟨998, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 998 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0998
          ·
            have he : (⟨999, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 999 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket0999
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
            simpa only [he] using bundle_a018773121_bucket1000
          ·
            have he : (⟨1001, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1001 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1001
        ·
          by_cases h1003 : i.val < 1003
          ·
            have he : (⟨1002, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1002 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1002
          ·
            have he : (⟨1003, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1003 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1003
      ·
        by_cases h1006 : i.val < 1006
        ·
          by_cases h1005 : i.val < 1005
          ·
            have he : (⟨1004, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1004 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1004
          ·
            have he : (⟨1005, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1005 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1005
        ·
          by_cases h1007 : i.val < 1007
          ·
            have he : (⟨1006, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1006 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1006
          ·
            have he : (⟨1007, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1007 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1007
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
            simpa only [he] using bundle_a018773121_bucket1008
          ·
            have he : (⟨1009, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1009 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1009
        ·
          by_cases h1011 : i.val < 1011
          ·
            have he : (⟨1010, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1010 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1010
          ·
            have he : (⟨1011, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1011 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1011
      ·
        by_cases h1014 : i.val < 1014
        ·
          by_cases h1013 : i.val < 1013
          ·
            have he : (⟨1012, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1012 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1012
          ·
            have he : (⟨1013, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1013 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1013
        ·
          by_cases h1015 : i.val < 1015
          ·
            have he : (⟨1014, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1014 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1014
          ·
            have he : (⟨1015, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1015 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1015
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
            simpa only [he] using bundle_a018773121_bucket1016
          ·
            have he : (⟨1017, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1017 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1017
        ·
          by_cases h1019 : i.val < 1019
          ·
            have he : (⟨1018, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1018 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1018
          ·
            have he : (⟨1019, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1019 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1019
      ·
        by_cases h1022 : i.val < 1022
        ·
          by_cases h1021 : i.val < 1021
          ·
            have he : (⟨1020, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1020 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1020
          ·
            have he : (⟨1021, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1021 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1021
        ·
          by_cases h1023 : i.val < 1023
          ·
            have he : (⟨1022, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1022 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1022
          ·
            have he : (⟨1023, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1023 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1023

theorem bundle_a018773121_bucketGroup0032 (i : Fin 1069)
    (hlo : 1024 ≤ i.val) (hhi : i.val < 1056) :
    i ∈ bundle_a018773121_anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bundle_a018773121_bucket1024
          ·
            have he : (⟨1025, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1025 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1025
        ·
          by_cases h1027 : i.val < 1027
          ·
            have he : (⟨1026, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1026 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1026
          ·
            have he : (⟨1027, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1027 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1027
      ·
        by_cases h1030 : i.val < 1030
        ·
          by_cases h1029 : i.val < 1029
          ·
            have he : (⟨1028, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1028 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1028
          ·
            have he : (⟨1029, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1029 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1029
        ·
          by_cases h1031 : i.val < 1031
          ·
            have he : (⟨1030, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1030 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1030
          ·
            have he : (⟨1031, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1031 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1031
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
            simpa only [he] using bundle_a018773121_bucket1032
          ·
            have he : (⟨1033, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1033 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1033
        ·
          by_cases h1035 : i.val < 1035
          ·
            have he : (⟨1034, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1034 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1034
          ·
            have he : (⟨1035, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1035 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1035
      ·
        by_cases h1038 : i.val < 1038
        ·
          by_cases h1037 : i.val < 1037
          ·
            have he : (⟨1036, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1036 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1036
          ·
            have he : (⟨1037, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1037 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1037
        ·
          by_cases h1039 : i.val < 1039
          ·
            have he : (⟨1038, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1038 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1038
          ·
            have he : (⟨1039, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1039 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1039
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
            simpa only [he] using bundle_a018773121_bucket1040
          ·
            have he : (⟨1041, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1041 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1041
        ·
          by_cases h1043 : i.val < 1043
          ·
            have he : (⟨1042, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1042 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1042
          ·
            have he : (⟨1043, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1043 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1043
      ·
        by_cases h1046 : i.val < 1046
        ·
          by_cases h1045 : i.val < 1045
          ·
            have he : (⟨1044, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1044 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1044
          ·
            have he : (⟨1045, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1045 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1045
        ·
          by_cases h1047 : i.val < 1047
          ·
            have he : (⟨1046, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1046 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1046
          ·
            have he : (⟨1047, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1047 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1047
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
            simpa only [he] using bundle_a018773121_bucket1048
          ·
            have he : (⟨1049, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1049 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1049
        ·
          by_cases h1051 : i.val < 1051
          ·
            have he : (⟨1050, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1050 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1050
          ·
            have he : (⟨1051, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1051 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1051
      ·
        by_cases h1054 : i.val < 1054
        ·
          by_cases h1053 : i.val < 1053
          ·
            have he : (⟨1052, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1052 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1052
          ·
            have he : (⟨1053, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1053 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1053
        ·
          by_cases h1055 : i.val < 1055
          ·
            have he : (⟨1054, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1054 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1054
          ·
            have he : (⟨1055, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1055 = i.val
              omega
            simpa only [he] using bundle_a018773121_bucket1055

theorem bundle_a018773121_bucketGroup0033 (i : Fin 1069)
    (hlo : 1056 ≤ i.val) (hhi : i.val < 1069) :
    i ∈ bundle_a018773121_anchoredFaces (faceRank i) (faceAnchor i) := by
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
        simpa only [he] using bundle_a018773121_bucket1056
      ·
        by_cases h1058 : i.val < 1058
        ·
          have he : (⟨1057, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1057 = i.val
            omega
          simpa only [he] using bundle_a018773121_bucket1057
        ·
          have he : (⟨1058, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1058 = i.val
            omega
          simpa only [he] using bundle_a018773121_bucket1058
    ·
      by_cases h1060 : i.val < 1060
      ·
        have he : (⟨1059, by decide⟩ : Fin 1069) = i := by
          apply Fin.ext
          change 1059 = i.val
          omega
        simpa only [he] using bundle_a018773121_bucket1059
      ·
        by_cases h1061 : i.val < 1061
        ·
          have he : (⟨1060, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1060 = i.val
            omega
          simpa only [he] using bundle_a018773121_bucket1060
        ·
          have he : (⟨1061, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1061 = i.val
            omega
          simpa only [he] using bundle_a018773121_bucket1061
  ·
    by_cases h1065 : i.val < 1065
    ·
      by_cases h1063 : i.val < 1063
      ·
        have he : (⟨1062, by decide⟩ : Fin 1069) = i := by
          apply Fin.ext
          change 1062 = i.val
          omega
        simpa only [he] using bundle_a018773121_bucket1062
      ·
        by_cases h1064 : i.val < 1064
        ·
          have he : (⟨1063, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1063 = i.val
            omega
          simpa only [he] using bundle_a018773121_bucket1063
        ·
          have he : (⟨1064, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1064 = i.val
            omega
          simpa only [he] using bundle_a018773121_bucket1064
    ·
      by_cases h1067 : i.val < 1067
      ·
        by_cases h1066 : i.val < 1066
        ·
          have he : (⟨1065, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1065 = i.val
            omega
          simpa only [he] using bundle_a018773121_bucket1065
        ·
          have he : (⟨1066, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1066 = i.val
            omega
          simpa only [he] using bundle_a018773121_bucket1066
      ·
        by_cases h1068 : i.val < 1068
        ·
          have he : (⟨1067, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1067 = i.val
            omega
          simpa only [he] using bundle_a018773121_bucket1067
        ·
          have he : (⟨1068, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1068 = i.val
            omega
          simpa only [he] using bundle_a018773121_bucket1068

theorem bundle_a018773121_anchoredFaces_self : ∀ i : Fin 1069,
    i ∈ bundle_a018773121_anchoredFaces (faceRank i) (faceAnchor i) := by
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
            exact bundle_a018773121_bucketGroup0000 i (by omega) (by omega)
          ·
            exact bundle_a018773121_bucketGroup0001 i (by omega) (by omega)
        ·
          by_cases h96 : i.val < 96
          ·
            exact bundle_a018773121_bucketGroup0002 i (by omega) (by omega)
          ·
            exact bundle_a018773121_bucketGroup0003 i (by omega) (by omega)
      ·
        by_cases h192 : i.val < 192
        ·
          by_cases h160 : i.val < 160
          ·
            exact bundle_a018773121_bucketGroup0004 i (by omega) (by omega)
          ·
            exact bundle_a018773121_bucketGroup0005 i (by omega) (by omega)
        ·
          by_cases h224 : i.val < 224
          ·
            exact bundle_a018773121_bucketGroup0006 i (by omega) (by omega)
          ·
            exact bundle_a018773121_bucketGroup0007 i (by omega) (by omega)
    ·
      by_cases h384 : i.val < 384
      ·
        by_cases h320 : i.val < 320
        ·
          by_cases h288 : i.val < 288
          ·
            exact bundle_a018773121_bucketGroup0008 i (by omega) (by omega)
          ·
            exact bundle_a018773121_bucketGroup0009 i (by omega) (by omega)
        ·
          by_cases h352 : i.val < 352
          ·
            exact bundle_a018773121_bucketGroup0010 i (by omega) (by omega)
          ·
            exact bundle_a018773121_bucketGroup0011 i (by omega) (by omega)
      ·
        by_cases h448 : i.val < 448
        ·
          by_cases h416 : i.val < 416
          ·
            exact bundle_a018773121_bucketGroup0012 i (by omega) (by omega)
          ·
            exact bundle_a018773121_bucketGroup0013 i (by omega) (by omega)
        ·
          by_cases h480 : i.val < 480
          ·
            exact bundle_a018773121_bucketGroup0014 i (by omega) (by omega)
          ·
            by_cases h512 : i.val < 512
            ·
              exact bundle_a018773121_bucketGroup0015 i (by omega) (by omega)
            ·
              exact bundle_a018773121_bucketGroup0016 i (by omega) (by omega)
  ·
    by_cases h800 : i.val < 800
    ·
      by_cases h672 : i.val < 672
      ·
        by_cases h608 : i.val < 608
        ·
          by_cases h576 : i.val < 576
          ·
            exact bundle_a018773121_bucketGroup0017 i (by omega) (by omega)
          ·
            exact bundle_a018773121_bucketGroup0018 i (by omega) (by omega)
        ·
          by_cases h640 : i.val < 640
          ·
            exact bundle_a018773121_bucketGroup0019 i (by omega) (by omega)
          ·
            exact bundle_a018773121_bucketGroup0020 i (by omega) (by omega)
      ·
        by_cases h736 : i.val < 736
        ·
          by_cases h704 : i.val < 704
          ·
            exact bundle_a018773121_bucketGroup0021 i (by omega) (by omega)
          ·
            exact bundle_a018773121_bucketGroup0022 i (by omega) (by omega)
        ·
          by_cases h768 : i.val < 768
          ·
            exact bundle_a018773121_bucketGroup0023 i (by omega) (by omega)
          ·
            exact bundle_a018773121_bucketGroup0024 i (by omega) (by omega)
    ·
      by_cases h928 : i.val < 928
      ·
        by_cases h864 : i.val < 864
        ·
          by_cases h832 : i.val < 832
          ·
            exact bundle_a018773121_bucketGroup0025 i (by omega) (by omega)
          ·
            exact bundle_a018773121_bucketGroup0026 i (by omega) (by omega)
        ·
          by_cases h896 : i.val < 896
          ·
            exact bundle_a018773121_bucketGroup0027 i (by omega) (by omega)
          ·
            exact bundle_a018773121_bucketGroup0028 i (by omega) (by omega)
      ·
        by_cases h992 : i.val < 992
        ·
          by_cases h960 : i.val < 960
          ·
            exact bundle_a018773121_bucketGroup0029 i (by omega) (by omega)
          ·
            exact bundle_a018773121_bucketGroup0030 i (by omega) (by omega)
        ·
          by_cases h1024 : i.val < 1024
          ·
            exact bundle_a018773121_bucketGroup0031 i (by omega) (by omega)
          ·
            by_cases h1056 : i.val < 1056
            ·
              exact bundle_a018773121_bucketGroup0032 i (by omega) (by omega)
            ·
              exact bundle_a018773121_bucketGroup0033 i (by omega) (by omega)

def bundle_a018773121_previousRank (i : Fin 1069) : Fin 5 :=
  ⟨(faceRank i).val - 1, by have h := (faceRank i).isLt; omega⟩

def bundle_a018773121_lowerCandidates (i : Fin 1069) : Finset (Fin 1069) :=
  (faceMask i).biUnion (bundle_a018773121_anchoredFaces (bundle_a018773121_previousRank i))

def bundle_a018773121_lowerComputed (i : Fin 1069) : Finset (Fin 1069) :=
  (bundle_a018773121_lowerCandidates i).filter
    (fun j => (faceRank j).val + 1 = (faceRank i).val ∧ faceMask j ⊆ faceMask i)

theorem bundle_a018773121_lower0000 : bundle_a018773121_lowerComputed (⟨0, by decide⟩ : Fin 1069) = lowerFacets (⟨0, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0001 : bundle_a018773121_lowerComputed (⟨1, by decide⟩ : Fin 1069) = lowerFacets (⟨1, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0002 : bundle_a018773121_lowerComputed (⟨2, by decide⟩ : Fin 1069) = lowerFacets (⟨2, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0003 : bundle_a018773121_lowerComputed (⟨3, by decide⟩ : Fin 1069) = lowerFacets (⟨3, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0004 : bundle_a018773121_lowerComputed (⟨4, by decide⟩ : Fin 1069) = lowerFacets (⟨4, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0005 : bundle_a018773121_lowerComputed (⟨5, by decide⟩ : Fin 1069) = lowerFacets (⟨5, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0006 : bundle_a018773121_lowerComputed (⟨6, by decide⟩ : Fin 1069) = lowerFacets (⟨6, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0007 : bundle_a018773121_lowerComputed (⟨7, by decide⟩ : Fin 1069) = lowerFacets (⟨7, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0008 : bundle_a018773121_lowerComputed (⟨8, by decide⟩ : Fin 1069) = lowerFacets (⟨8, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0009 : bundle_a018773121_lowerComputed (⟨9, by decide⟩ : Fin 1069) = lowerFacets (⟨9, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0010 : bundle_a018773121_lowerComputed (⟨10, by decide⟩ : Fin 1069) = lowerFacets (⟨10, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0011 : bundle_a018773121_lowerComputed (⟨11, by decide⟩ : Fin 1069) = lowerFacets (⟨11, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0012 : bundle_a018773121_lowerComputed (⟨12, by decide⟩ : Fin 1069) = lowerFacets (⟨12, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0013 : bundle_a018773121_lowerComputed (⟨13, by decide⟩ : Fin 1069) = lowerFacets (⟨13, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0014 : bundle_a018773121_lowerComputed (⟨14, by decide⟩ : Fin 1069) = lowerFacets (⟨14, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0015 : bundle_a018773121_lowerComputed (⟨15, by decide⟩ : Fin 1069) = lowerFacets (⟨15, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0016 : bundle_a018773121_lowerComputed (⟨16, by decide⟩ : Fin 1069) = lowerFacets (⟨16, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0017 : bundle_a018773121_lowerComputed (⟨17, by decide⟩ : Fin 1069) = lowerFacets (⟨17, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0018 : bundle_a018773121_lowerComputed (⟨18, by decide⟩ : Fin 1069) = lowerFacets (⟨18, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0019 : bundle_a018773121_lowerComputed (⟨19, by decide⟩ : Fin 1069) = lowerFacets (⟨19, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0020 : bundle_a018773121_lowerComputed (⟨20, by decide⟩ : Fin 1069) = lowerFacets (⟨20, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0021 : bundle_a018773121_lowerComputed (⟨21, by decide⟩ : Fin 1069) = lowerFacets (⟨21, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0022 : bundle_a018773121_lowerComputed (⟨22, by decide⟩ : Fin 1069) = lowerFacets (⟨22, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0023 : bundle_a018773121_lowerComputed (⟨23, by decide⟩ : Fin 1069) = lowerFacets (⟨23, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0024 : bundle_a018773121_lowerComputed (⟨24, by decide⟩ : Fin 1069) = lowerFacets (⟨24, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0025 : bundle_a018773121_lowerComputed (⟨25, by decide⟩ : Fin 1069) = lowerFacets (⟨25, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0026 : bundle_a018773121_lowerComputed (⟨26, by decide⟩ : Fin 1069) = lowerFacets (⟨26, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0027 : bundle_a018773121_lowerComputed (⟨27, by decide⟩ : Fin 1069) = lowerFacets (⟨27, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0028 : bundle_a018773121_lowerComputed (⟨28, by decide⟩ : Fin 1069) = lowerFacets (⟨28, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0029 : bundle_a018773121_lowerComputed (⟨29, by decide⟩ : Fin 1069) = lowerFacets (⟨29, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0030 : bundle_a018773121_lowerComputed (⟨30, by decide⟩ : Fin 1069) = lowerFacets (⟨30, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0031 : bundle_a018773121_lowerComputed (⟨31, by decide⟩ : Fin 1069) = lowerFacets (⟨31, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0032 : bundle_a018773121_lowerComputed (⟨32, by decide⟩ : Fin 1069) = lowerFacets (⟨32, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0033 : bundle_a018773121_lowerComputed (⟨33, by decide⟩ : Fin 1069) = lowerFacets (⟨33, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0034 : bundle_a018773121_lowerComputed (⟨34, by decide⟩ : Fin 1069) = lowerFacets (⟨34, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0035 : bundle_a018773121_lowerComputed (⟨35, by decide⟩ : Fin 1069) = lowerFacets (⟨35, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0036 : bundle_a018773121_lowerComputed (⟨36, by decide⟩ : Fin 1069) = lowerFacets (⟨36, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0037 : bundle_a018773121_lowerComputed (⟨37, by decide⟩ : Fin 1069) = lowerFacets (⟨37, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0038 : bundle_a018773121_lowerComputed (⟨38, by decide⟩ : Fin 1069) = lowerFacets (⟨38, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0039 : bundle_a018773121_lowerComputed (⟨39, by decide⟩ : Fin 1069) = lowerFacets (⟨39, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0040 : bundle_a018773121_lowerComputed (⟨40, by decide⟩ : Fin 1069) = lowerFacets (⟨40, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0041 : bundle_a018773121_lowerComputed (⟨41, by decide⟩ : Fin 1069) = lowerFacets (⟨41, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0042 : bundle_a018773121_lowerComputed (⟨42, by decide⟩ : Fin 1069) = lowerFacets (⟨42, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0043 : bundle_a018773121_lowerComputed (⟨43, by decide⟩ : Fin 1069) = lowerFacets (⟨43, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0044 : bundle_a018773121_lowerComputed (⟨44, by decide⟩ : Fin 1069) = lowerFacets (⟨44, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0045 : bundle_a018773121_lowerComputed (⟨45, by decide⟩ : Fin 1069) = lowerFacets (⟨45, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0046 : bundle_a018773121_lowerComputed (⟨46, by decide⟩ : Fin 1069) = lowerFacets (⟨46, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0047 : bundle_a018773121_lowerComputed (⟨47, by decide⟩ : Fin 1069) = lowerFacets (⟨47, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0048 : bundle_a018773121_lowerComputed (⟨48, by decide⟩ : Fin 1069) = lowerFacets (⟨48, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0049 : bundle_a018773121_lowerComputed (⟨49, by decide⟩ : Fin 1069) = lowerFacets (⟨49, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0050 : bundle_a018773121_lowerComputed (⟨50, by decide⟩ : Fin 1069) = lowerFacets (⟨50, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0051 : bundle_a018773121_lowerComputed (⟨51, by decide⟩ : Fin 1069) = lowerFacets (⟨51, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0052 : bundle_a018773121_lowerComputed (⟨52, by decide⟩ : Fin 1069) = lowerFacets (⟨52, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0053 : bundle_a018773121_lowerComputed (⟨53, by decide⟩ : Fin 1069) = lowerFacets (⟨53, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0054 : bundle_a018773121_lowerComputed (⟨54, by decide⟩ : Fin 1069) = lowerFacets (⟨54, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0055 : bundle_a018773121_lowerComputed (⟨55, by decide⟩ : Fin 1069) = lowerFacets (⟨55, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0056 : bundle_a018773121_lowerComputed (⟨56, by decide⟩ : Fin 1069) = lowerFacets (⟨56, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0057 : bundle_a018773121_lowerComputed (⟨57, by decide⟩ : Fin 1069) = lowerFacets (⟨57, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0058 : bundle_a018773121_lowerComputed (⟨58, by decide⟩ : Fin 1069) = lowerFacets (⟨58, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0059 : bundle_a018773121_lowerComputed (⟨59, by decide⟩ : Fin 1069) = lowerFacets (⟨59, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0060 : bundle_a018773121_lowerComputed (⟨60, by decide⟩ : Fin 1069) = lowerFacets (⟨60, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0061 : bundle_a018773121_lowerComputed (⟨61, by decide⟩ : Fin 1069) = lowerFacets (⟨61, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0062 : bundle_a018773121_lowerComputed (⟨62, by decide⟩ : Fin 1069) = lowerFacets (⟨62, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0063 : bundle_a018773121_lowerComputed (⟨63, by decide⟩ : Fin 1069) = lowerFacets (⟨63, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0064 : bundle_a018773121_lowerComputed (⟨64, by decide⟩ : Fin 1069) = lowerFacets (⟨64, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0065 : bundle_a018773121_lowerComputed (⟨65, by decide⟩ : Fin 1069) = lowerFacets (⟨65, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0066 : bundle_a018773121_lowerComputed (⟨66, by decide⟩ : Fin 1069) = lowerFacets (⟨66, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0067 : bundle_a018773121_lowerComputed (⟨67, by decide⟩ : Fin 1069) = lowerFacets (⟨67, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0068 : bundle_a018773121_lowerComputed (⟨68, by decide⟩ : Fin 1069) = lowerFacets (⟨68, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0069 : bundle_a018773121_lowerComputed (⟨69, by decide⟩ : Fin 1069) = lowerFacets (⟨69, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0070 : bundle_a018773121_lowerComputed (⟨70, by decide⟩ : Fin 1069) = lowerFacets (⟨70, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0071 : bundle_a018773121_lowerComputed (⟨71, by decide⟩ : Fin 1069) = lowerFacets (⟨71, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0072 : bundle_a018773121_lowerComputed (⟨72, by decide⟩ : Fin 1069) = lowerFacets (⟨72, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0073 : bundle_a018773121_lowerComputed (⟨73, by decide⟩ : Fin 1069) = lowerFacets (⟨73, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0074 : bundle_a018773121_lowerComputed (⟨74, by decide⟩ : Fin 1069) = lowerFacets (⟨74, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0075 : bundle_a018773121_lowerComputed (⟨75, by decide⟩ : Fin 1069) = lowerFacets (⟨75, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0076 : bundle_a018773121_lowerComputed (⟨76, by decide⟩ : Fin 1069) = lowerFacets (⟨76, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0077 : bundle_a018773121_lowerComputed (⟨77, by decide⟩ : Fin 1069) = lowerFacets (⟨77, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0078 : bundle_a018773121_lowerComputed (⟨78, by decide⟩ : Fin 1069) = lowerFacets (⟨78, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0079 : bundle_a018773121_lowerComputed (⟨79, by decide⟩ : Fin 1069) = lowerFacets (⟨79, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0080 : bundle_a018773121_lowerComputed (⟨80, by decide⟩ : Fin 1069) = lowerFacets (⟨80, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0081 : bundle_a018773121_lowerComputed (⟨81, by decide⟩ : Fin 1069) = lowerFacets (⟨81, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0082 : bundle_a018773121_lowerComputed (⟨82, by decide⟩ : Fin 1069) = lowerFacets (⟨82, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0083 : bundle_a018773121_lowerComputed (⟨83, by decide⟩ : Fin 1069) = lowerFacets (⟨83, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0084 : bundle_a018773121_lowerComputed (⟨84, by decide⟩ : Fin 1069) = lowerFacets (⟨84, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0085 : bundle_a018773121_lowerComputed (⟨85, by decide⟩ : Fin 1069) = lowerFacets (⟨85, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0086 : bundle_a018773121_lowerComputed (⟨86, by decide⟩ : Fin 1069) = lowerFacets (⟨86, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0087 : bundle_a018773121_lowerComputed (⟨87, by decide⟩ : Fin 1069) = lowerFacets (⟨87, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0088 : bundle_a018773121_lowerComputed (⟨88, by decide⟩ : Fin 1069) = lowerFacets (⟨88, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0089 : bundle_a018773121_lowerComputed (⟨89, by decide⟩ : Fin 1069) = lowerFacets (⟨89, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0090 : bundle_a018773121_lowerComputed (⟨90, by decide⟩ : Fin 1069) = lowerFacets (⟨90, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0091 : bundle_a018773121_lowerComputed (⟨91, by decide⟩ : Fin 1069) = lowerFacets (⟨91, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0092 : bundle_a018773121_lowerComputed (⟨92, by decide⟩ : Fin 1069) = lowerFacets (⟨92, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0093 : bundle_a018773121_lowerComputed (⟨93, by decide⟩ : Fin 1069) = lowerFacets (⟨93, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0094 : bundle_a018773121_lowerComputed (⟨94, by decide⟩ : Fin 1069) = lowerFacets (⟨94, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0095 : bundle_a018773121_lowerComputed (⟨95, by decide⟩ : Fin 1069) = lowerFacets (⟨95, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0096 : bundle_a018773121_lowerComputed (⟨96, by decide⟩ : Fin 1069) = lowerFacets (⟨96, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0097 : bundle_a018773121_lowerComputed (⟨97, by decide⟩ : Fin 1069) = lowerFacets (⟨97, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0098 : bundle_a018773121_lowerComputed (⟨98, by decide⟩ : Fin 1069) = lowerFacets (⟨98, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0099 : bundle_a018773121_lowerComputed (⟨99, by decide⟩ : Fin 1069) = lowerFacets (⟨99, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0100 : bundle_a018773121_lowerComputed (⟨100, by decide⟩ : Fin 1069) = lowerFacets (⟨100, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0101 : bundle_a018773121_lowerComputed (⟨101, by decide⟩ : Fin 1069) = lowerFacets (⟨101, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0102 : bundle_a018773121_lowerComputed (⟨102, by decide⟩ : Fin 1069) = lowerFacets (⟨102, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0103 : bundle_a018773121_lowerComputed (⟨103, by decide⟩ : Fin 1069) = lowerFacets (⟨103, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0104 : bundle_a018773121_lowerComputed (⟨104, by decide⟩ : Fin 1069) = lowerFacets (⟨104, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0105 : bundle_a018773121_lowerComputed (⟨105, by decide⟩ : Fin 1069) = lowerFacets (⟨105, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0106 : bundle_a018773121_lowerComputed (⟨106, by decide⟩ : Fin 1069) = lowerFacets (⟨106, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0107 : bundle_a018773121_lowerComputed (⟨107, by decide⟩ : Fin 1069) = lowerFacets (⟨107, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0108 : bundle_a018773121_lowerComputed (⟨108, by decide⟩ : Fin 1069) = lowerFacets (⟨108, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0109 : bundle_a018773121_lowerComputed (⟨109, by decide⟩ : Fin 1069) = lowerFacets (⟨109, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0110 : bundle_a018773121_lowerComputed (⟨110, by decide⟩ : Fin 1069) = lowerFacets (⟨110, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0111 : bundle_a018773121_lowerComputed (⟨111, by decide⟩ : Fin 1069) = lowerFacets (⟨111, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0112 : bundle_a018773121_lowerComputed (⟨112, by decide⟩ : Fin 1069) = lowerFacets (⟨112, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0113 : bundle_a018773121_lowerComputed (⟨113, by decide⟩ : Fin 1069) = lowerFacets (⟨113, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0114 : bundle_a018773121_lowerComputed (⟨114, by decide⟩ : Fin 1069) = lowerFacets (⟨114, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0115 : bundle_a018773121_lowerComputed (⟨115, by decide⟩ : Fin 1069) = lowerFacets (⟨115, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0116 : bundle_a018773121_lowerComputed (⟨116, by decide⟩ : Fin 1069) = lowerFacets (⟨116, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0117 : bundle_a018773121_lowerComputed (⟨117, by decide⟩ : Fin 1069) = lowerFacets (⟨117, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0118 : bundle_a018773121_lowerComputed (⟨118, by decide⟩ : Fin 1069) = lowerFacets (⟨118, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0119 : bundle_a018773121_lowerComputed (⟨119, by decide⟩ : Fin 1069) = lowerFacets (⟨119, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0120 : bundle_a018773121_lowerComputed (⟨120, by decide⟩ : Fin 1069) = lowerFacets (⟨120, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0121 : bundle_a018773121_lowerComputed (⟨121, by decide⟩ : Fin 1069) = lowerFacets (⟨121, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0122 : bundle_a018773121_lowerComputed (⟨122, by decide⟩ : Fin 1069) = lowerFacets (⟨122, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0123 : bundle_a018773121_lowerComputed (⟨123, by decide⟩ : Fin 1069) = lowerFacets (⟨123, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0124 : bundle_a018773121_lowerComputed (⟨124, by decide⟩ : Fin 1069) = lowerFacets (⟨124, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0125 : bundle_a018773121_lowerComputed (⟨125, by decide⟩ : Fin 1069) = lowerFacets (⟨125, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0126 : bundle_a018773121_lowerComputed (⟨126, by decide⟩ : Fin 1069) = lowerFacets (⟨126, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0127 : bundle_a018773121_lowerComputed (⟨127, by decide⟩ : Fin 1069) = lowerFacets (⟨127, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0128 : bundle_a018773121_lowerComputed (⟨128, by decide⟩ : Fin 1069) = lowerFacets (⟨128, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0129 : bundle_a018773121_lowerComputed (⟨129, by decide⟩ : Fin 1069) = lowerFacets (⟨129, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0130 : bundle_a018773121_lowerComputed (⟨130, by decide⟩ : Fin 1069) = lowerFacets (⟨130, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0131 : bundle_a018773121_lowerComputed (⟨131, by decide⟩ : Fin 1069) = lowerFacets (⟨131, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0132 : bundle_a018773121_lowerComputed (⟨132, by decide⟩ : Fin 1069) = lowerFacets (⟨132, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0133 : bundle_a018773121_lowerComputed (⟨133, by decide⟩ : Fin 1069) = lowerFacets (⟨133, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0134 : bundle_a018773121_lowerComputed (⟨134, by decide⟩ : Fin 1069) = lowerFacets (⟨134, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0135 : bundle_a018773121_lowerComputed (⟨135, by decide⟩ : Fin 1069) = lowerFacets (⟨135, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0136 : bundle_a018773121_lowerComputed (⟨136, by decide⟩ : Fin 1069) = lowerFacets (⟨136, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0137 : bundle_a018773121_lowerComputed (⟨137, by decide⟩ : Fin 1069) = lowerFacets (⟨137, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0138 : bundle_a018773121_lowerComputed (⟨138, by decide⟩ : Fin 1069) = lowerFacets (⟨138, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0139 : bundle_a018773121_lowerComputed (⟨139, by decide⟩ : Fin 1069) = lowerFacets (⟨139, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0140 : bundle_a018773121_lowerComputed (⟨140, by decide⟩ : Fin 1069) = lowerFacets (⟨140, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0141 : bundle_a018773121_lowerComputed (⟨141, by decide⟩ : Fin 1069) = lowerFacets (⟨141, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0142 : bundle_a018773121_lowerComputed (⟨142, by decide⟩ : Fin 1069) = lowerFacets (⟨142, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0143 : bundle_a018773121_lowerComputed (⟨143, by decide⟩ : Fin 1069) = lowerFacets (⟨143, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0144 : bundle_a018773121_lowerComputed (⟨144, by decide⟩ : Fin 1069) = lowerFacets (⟨144, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0145 : bundle_a018773121_lowerComputed (⟨145, by decide⟩ : Fin 1069) = lowerFacets (⟨145, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0146 : bundle_a018773121_lowerComputed (⟨146, by decide⟩ : Fin 1069) = lowerFacets (⟨146, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0147 : bundle_a018773121_lowerComputed (⟨147, by decide⟩ : Fin 1069) = lowerFacets (⟨147, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0148 : bundle_a018773121_lowerComputed (⟨148, by decide⟩ : Fin 1069) = lowerFacets (⟨148, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0149 : bundle_a018773121_lowerComputed (⟨149, by decide⟩ : Fin 1069) = lowerFacets (⟨149, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0150 : bundle_a018773121_lowerComputed (⟨150, by decide⟩ : Fin 1069) = lowerFacets (⟨150, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0151 : bundle_a018773121_lowerComputed (⟨151, by decide⟩ : Fin 1069) = lowerFacets (⟨151, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0152 : bundle_a018773121_lowerComputed (⟨152, by decide⟩ : Fin 1069) = lowerFacets (⟨152, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0153 : bundle_a018773121_lowerComputed (⟨153, by decide⟩ : Fin 1069) = lowerFacets (⟨153, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0154 : bundle_a018773121_lowerComputed (⟨154, by decide⟩ : Fin 1069) = lowerFacets (⟨154, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0155 : bundle_a018773121_lowerComputed (⟨155, by decide⟩ : Fin 1069) = lowerFacets (⟨155, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0156 : bundle_a018773121_lowerComputed (⟨156, by decide⟩ : Fin 1069) = lowerFacets (⟨156, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0157 : bundle_a018773121_lowerComputed (⟨157, by decide⟩ : Fin 1069) = lowerFacets (⟨157, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0158 : bundle_a018773121_lowerComputed (⟨158, by decide⟩ : Fin 1069) = lowerFacets (⟨158, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0159 : bundle_a018773121_lowerComputed (⟨159, by decide⟩ : Fin 1069) = lowerFacets (⟨159, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0160 : bundle_a018773121_lowerComputed (⟨160, by decide⟩ : Fin 1069) = lowerFacets (⟨160, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0161 : bundle_a018773121_lowerComputed (⟨161, by decide⟩ : Fin 1069) = lowerFacets (⟨161, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0162 : bundle_a018773121_lowerComputed (⟨162, by decide⟩ : Fin 1069) = lowerFacets (⟨162, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0163 : bundle_a018773121_lowerComputed (⟨163, by decide⟩ : Fin 1069) = lowerFacets (⟨163, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0164 : bundle_a018773121_lowerComputed (⟨164, by decide⟩ : Fin 1069) = lowerFacets (⟨164, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0165 : bundle_a018773121_lowerComputed (⟨165, by decide⟩ : Fin 1069) = lowerFacets (⟨165, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0166 : bundle_a018773121_lowerComputed (⟨166, by decide⟩ : Fin 1069) = lowerFacets (⟨166, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0167 : bundle_a018773121_lowerComputed (⟨167, by decide⟩ : Fin 1069) = lowerFacets (⟨167, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0168 : bundle_a018773121_lowerComputed (⟨168, by decide⟩ : Fin 1069) = lowerFacets (⟨168, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0169 : bundle_a018773121_lowerComputed (⟨169, by decide⟩ : Fin 1069) = lowerFacets (⟨169, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0170 : bundle_a018773121_lowerComputed (⟨170, by decide⟩ : Fin 1069) = lowerFacets (⟨170, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0171 : bundle_a018773121_lowerComputed (⟨171, by decide⟩ : Fin 1069) = lowerFacets (⟨171, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0172 : bundle_a018773121_lowerComputed (⟨172, by decide⟩ : Fin 1069) = lowerFacets (⟨172, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0173 : bundle_a018773121_lowerComputed (⟨173, by decide⟩ : Fin 1069) = lowerFacets (⟨173, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0174 : bundle_a018773121_lowerComputed (⟨174, by decide⟩ : Fin 1069) = lowerFacets (⟨174, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0175 : bundle_a018773121_lowerComputed (⟨175, by decide⟩ : Fin 1069) = lowerFacets (⟨175, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0176 : bundle_a018773121_lowerComputed (⟨176, by decide⟩ : Fin 1069) = lowerFacets (⟨176, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0177 : bundle_a018773121_lowerComputed (⟨177, by decide⟩ : Fin 1069) = lowerFacets (⟨177, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0178 : bundle_a018773121_lowerComputed (⟨178, by decide⟩ : Fin 1069) = lowerFacets (⟨178, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0179 : bundle_a018773121_lowerComputed (⟨179, by decide⟩ : Fin 1069) = lowerFacets (⟨179, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0180 : bundle_a018773121_lowerComputed (⟨180, by decide⟩ : Fin 1069) = lowerFacets (⟨180, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0181 : bundle_a018773121_lowerComputed (⟨181, by decide⟩ : Fin 1069) = lowerFacets (⟨181, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0182 : bundle_a018773121_lowerComputed (⟨182, by decide⟩ : Fin 1069) = lowerFacets (⟨182, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0183 : bundle_a018773121_lowerComputed (⟨183, by decide⟩ : Fin 1069) = lowerFacets (⟨183, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0184 : bundle_a018773121_lowerComputed (⟨184, by decide⟩ : Fin 1069) = lowerFacets (⟨184, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0185 : bundle_a018773121_lowerComputed (⟨185, by decide⟩ : Fin 1069) = lowerFacets (⟨185, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0186 : bundle_a018773121_lowerComputed (⟨186, by decide⟩ : Fin 1069) = lowerFacets (⟨186, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0187 : bundle_a018773121_lowerComputed (⟨187, by decide⟩ : Fin 1069) = lowerFacets (⟨187, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0188 : bundle_a018773121_lowerComputed (⟨188, by decide⟩ : Fin 1069) = lowerFacets (⟨188, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0189 : bundle_a018773121_lowerComputed (⟨189, by decide⟩ : Fin 1069) = lowerFacets (⟨189, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0190 : bundle_a018773121_lowerComputed (⟨190, by decide⟩ : Fin 1069) = lowerFacets (⟨190, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0191 : bundle_a018773121_lowerComputed (⟨191, by decide⟩ : Fin 1069) = lowerFacets (⟨191, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0192 : bundle_a018773121_lowerComputed (⟨192, by decide⟩ : Fin 1069) = lowerFacets (⟨192, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0193 : bundle_a018773121_lowerComputed (⟨193, by decide⟩ : Fin 1069) = lowerFacets (⟨193, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0194 : bundle_a018773121_lowerComputed (⟨194, by decide⟩ : Fin 1069) = lowerFacets (⟨194, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0195 : bundle_a018773121_lowerComputed (⟨195, by decide⟩ : Fin 1069) = lowerFacets (⟨195, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0196 : bundle_a018773121_lowerComputed (⟨196, by decide⟩ : Fin 1069) = lowerFacets (⟨196, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0197 : bundle_a018773121_lowerComputed (⟨197, by decide⟩ : Fin 1069) = lowerFacets (⟨197, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0198 : bundle_a018773121_lowerComputed (⟨198, by decide⟩ : Fin 1069) = lowerFacets (⟨198, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0199 : bundle_a018773121_lowerComputed (⟨199, by decide⟩ : Fin 1069) = lowerFacets (⟨199, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0200 : bundle_a018773121_lowerComputed (⟨200, by decide⟩ : Fin 1069) = lowerFacets (⟨200, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0201 : bundle_a018773121_lowerComputed (⟨201, by decide⟩ : Fin 1069) = lowerFacets (⟨201, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0202 : bundle_a018773121_lowerComputed (⟨202, by decide⟩ : Fin 1069) = lowerFacets (⟨202, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0203 : bundle_a018773121_lowerComputed (⟨203, by decide⟩ : Fin 1069) = lowerFacets (⟨203, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0204 : bundle_a018773121_lowerComputed (⟨204, by decide⟩ : Fin 1069) = lowerFacets (⟨204, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0205 : bundle_a018773121_lowerComputed (⟨205, by decide⟩ : Fin 1069) = lowerFacets (⟨205, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0206 : bundle_a018773121_lowerComputed (⟨206, by decide⟩ : Fin 1069) = lowerFacets (⟨206, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0207 : bundle_a018773121_lowerComputed (⟨207, by decide⟩ : Fin 1069) = lowerFacets (⟨207, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0208 : bundle_a018773121_lowerComputed (⟨208, by decide⟩ : Fin 1069) = lowerFacets (⟨208, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0209 : bundle_a018773121_lowerComputed (⟨209, by decide⟩ : Fin 1069) = lowerFacets (⟨209, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0210 : bundle_a018773121_lowerComputed (⟨210, by decide⟩ : Fin 1069) = lowerFacets (⟨210, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0211 : bundle_a018773121_lowerComputed (⟨211, by decide⟩ : Fin 1069) = lowerFacets (⟨211, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0212 : bundle_a018773121_lowerComputed (⟨212, by decide⟩ : Fin 1069) = lowerFacets (⟨212, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0213 : bundle_a018773121_lowerComputed (⟨213, by decide⟩ : Fin 1069) = lowerFacets (⟨213, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0214 : bundle_a018773121_lowerComputed (⟨214, by decide⟩ : Fin 1069) = lowerFacets (⟨214, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0215 : bundle_a018773121_lowerComputed (⟨215, by decide⟩ : Fin 1069) = lowerFacets (⟨215, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0216 : bundle_a018773121_lowerComputed (⟨216, by decide⟩ : Fin 1069) = lowerFacets (⟨216, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0217 : bundle_a018773121_lowerComputed (⟨217, by decide⟩ : Fin 1069) = lowerFacets (⟨217, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0218 : bundle_a018773121_lowerComputed (⟨218, by decide⟩ : Fin 1069) = lowerFacets (⟨218, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0219 : bundle_a018773121_lowerComputed (⟨219, by decide⟩ : Fin 1069) = lowerFacets (⟨219, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0220 : bundle_a018773121_lowerComputed (⟨220, by decide⟩ : Fin 1069) = lowerFacets (⟨220, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0221 : bundle_a018773121_lowerComputed (⟨221, by decide⟩ : Fin 1069) = lowerFacets (⟨221, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0222 : bundle_a018773121_lowerComputed (⟨222, by decide⟩ : Fin 1069) = lowerFacets (⟨222, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0223 : bundle_a018773121_lowerComputed (⟨223, by decide⟩ : Fin 1069) = lowerFacets (⟨223, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0224 : bundle_a018773121_lowerComputed (⟨224, by decide⟩ : Fin 1069) = lowerFacets (⟨224, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0225 : bundle_a018773121_lowerComputed (⟨225, by decide⟩ : Fin 1069) = lowerFacets (⟨225, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0226 : bundle_a018773121_lowerComputed (⟨226, by decide⟩ : Fin 1069) = lowerFacets (⟨226, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0227 : bundle_a018773121_lowerComputed (⟨227, by decide⟩ : Fin 1069) = lowerFacets (⟨227, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0228 : bundle_a018773121_lowerComputed (⟨228, by decide⟩ : Fin 1069) = lowerFacets (⟨228, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0229 : bundle_a018773121_lowerComputed (⟨229, by decide⟩ : Fin 1069) = lowerFacets (⟨229, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0230 : bundle_a018773121_lowerComputed (⟨230, by decide⟩ : Fin 1069) = lowerFacets (⟨230, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0231 : bundle_a018773121_lowerComputed (⟨231, by decide⟩ : Fin 1069) = lowerFacets (⟨231, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0232 : bundle_a018773121_lowerComputed (⟨232, by decide⟩ : Fin 1069) = lowerFacets (⟨232, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0233 : bundle_a018773121_lowerComputed (⟨233, by decide⟩ : Fin 1069) = lowerFacets (⟨233, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0234 : bundle_a018773121_lowerComputed (⟨234, by decide⟩ : Fin 1069) = lowerFacets (⟨234, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0235 : bundle_a018773121_lowerComputed (⟨235, by decide⟩ : Fin 1069) = lowerFacets (⟨235, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0236 : bundle_a018773121_lowerComputed (⟨236, by decide⟩ : Fin 1069) = lowerFacets (⟨236, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0237 : bundle_a018773121_lowerComputed (⟨237, by decide⟩ : Fin 1069) = lowerFacets (⟨237, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0238 : bundle_a018773121_lowerComputed (⟨238, by decide⟩ : Fin 1069) = lowerFacets (⟨238, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0239 : bundle_a018773121_lowerComputed (⟨239, by decide⟩ : Fin 1069) = lowerFacets (⟨239, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0240 : bundle_a018773121_lowerComputed (⟨240, by decide⟩ : Fin 1069) = lowerFacets (⟨240, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0241 : bundle_a018773121_lowerComputed (⟨241, by decide⟩ : Fin 1069) = lowerFacets (⟨241, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0242 : bundle_a018773121_lowerComputed (⟨242, by decide⟩ : Fin 1069) = lowerFacets (⟨242, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0243 : bundle_a018773121_lowerComputed (⟨243, by decide⟩ : Fin 1069) = lowerFacets (⟨243, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0244 : bundle_a018773121_lowerComputed (⟨244, by decide⟩ : Fin 1069) = lowerFacets (⟨244, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0245 : bundle_a018773121_lowerComputed (⟨245, by decide⟩ : Fin 1069) = lowerFacets (⟨245, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0246 : bundle_a018773121_lowerComputed (⟨246, by decide⟩ : Fin 1069) = lowerFacets (⟨246, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0247 : bundle_a018773121_lowerComputed (⟨247, by decide⟩ : Fin 1069) = lowerFacets (⟨247, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0248 : bundle_a018773121_lowerComputed (⟨248, by decide⟩ : Fin 1069) = lowerFacets (⟨248, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0249 : bundle_a018773121_lowerComputed (⟨249, by decide⟩ : Fin 1069) = lowerFacets (⟨249, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0250 : bundle_a018773121_lowerComputed (⟨250, by decide⟩ : Fin 1069) = lowerFacets (⟨250, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0251 : bundle_a018773121_lowerComputed (⟨251, by decide⟩ : Fin 1069) = lowerFacets (⟨251, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0252 : bundle_a018773121_lowerComputed (⟨252, by decide⟩ : Fin 1069) = lowerFacets (⟨252, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0253 : bundle_a018773121_lowerComputed (⟨253, by decide⟩ : Fin 1069) = lowerFacets (⟨253, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0254 : bundle_a018773121_lowerComputed (⟨254, by decide⟩ : Fin 1069) = lowerFacets (⟨254, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0255 : bundle_a018773121_lowerComputed (⟨255, by decide⟩ : Fin 1069) = lowerFacets (⟨255, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0256 : bundle_a018773121_lowerComputed (⟨256, by decide⟩ : Fin 1069) = lowerFacets (⟨256, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0257 : bundle_a018773121_lowerComputed (⟨257, by decide⟩ : Fin 1069) = lowerFacets (⟨257, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0258 : bundle_a018773121_lowerComputed (⟨258, by decide⟩ : Fin 1069) = lowerFacets (⟨258, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0259 : bundle_a018773121_lowerComputed (⟨259, by decide⟩ : Fin 1069) = lowerFacets (⟨259, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0260 : bundle_a018773121_lowerComputed (⟨260, by decide⟩ : Fin 1069) = lowerFacets (⟨260, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0261 : bundle_a018773121_lowerComputed (⟨261, by decide⟩ : Fin 1069) = lowerFacets (⟨261, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0262 : bundle_a018773121_lowerComputed (⟨262, by decide⟩ : Fin 1069) = lowerFacets (⟨262, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0263 : bundle_a018773121_lowerComputed (⟨263, by decide⟩ : Fin 1069) = lowerFacets (⟨263, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0264 : bundle_a018773121_lowerComputed (⟨264, by decide⟩ : Fin 1069) = lowerFacets (⟨264, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0265 : bundle_a018773121_lowerComputed (⟨265, by decide⟩ : Fin 1069) = lowerFacets (⟨265, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0266 : bundle_a018773121_lowerComputed (⟨266, by decide⟩ : Fin 1069) = lowerFacets (⟨266, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0267 : bundle_a018773121_lowerComputed (⟨267, by decide⟩ : Fin 1069) = lowerFacets (⟨267, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0268 : bundle_a018773121_lowerComputed (⟨268, by decide⟩ : Fin 1069) = lowerFacets (⟨268, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0269 : bundle_a018773121_lowerComputed (⟨269, by decide⟩ : Fin 1069) = lowerFacets (⟨269, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0270 : bundle_a018773121_lowerComputed (⟨270, by decide⟩ : Fin 1069) = lowerFacets (⟨270, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0271 : bundle_a018773121_lowerComputed (⟨271, by decide⟩ : Fin 1069) = lowerFacets (⟨271, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0272 : bundle_a018773121_lowerComputed (⟨272, by decide⟩ : Fin 1069) = lowerFacets (⟨272, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0273 : bundle_a018773121_lowerComputed (⟨273, by decide⟩ : Fin 1069) = lowerFacets (⟨273, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0274 : bundle_a018773121_lowerComputed (⟨274, by decide⟩ : Fin 1069) = lowerFacets (⟨274, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0275 : bundle_a018773121_lowerComputed (⟨275, by decide⟩ : Fin 1069) = lowerFacets (⟨275, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0276 : bundle_a018773121_lowerComputed (⟨276, by decide⟩ : Fin 1069) = lowerFacets (⟨276, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0277 : bundle_a018773121_lowerComputed (⟨277, by decide⟩ : Fin 1069) = lowerFacets (⟨277, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0278 : bundle_a018773121_lowerComputed (⟨278, by decide⟩ : Fin 1069) = lowerFacets (⟨278, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0279 : bundle_a018773121_lowerComputed (⟨279, by decide⟩ : Fin 1069) = lowerFacets (⟨279, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0280 : bundle_a018773121_lowerComputed (⟨280, by decide⟩ : Fin 1069) = lowerFacets (⟨280, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0281 : bundle_a018773121_lowerComputed (⟨281, by decide⟩ : Fin 1069) = lowerFacets (⟨281, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0282 : bundle_a018773121_lowerComputed (⟨282, by decide⟩ : Fin 1069) = lowerFacets (⟨282, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0283 : bundle_a018773121_lowerComputed (⟨283, by decide⟩ : Fin 1069) = lowerFacets (⟨283, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0284 : bundle_a018773121_lowerComputed (⟨284, by decide⟩ : Fin 1069) = lowerFacets (⟨284, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0285 : bundle_a018773121_lowerComputed (⟨285, by decide⟩ : Fin 1069) = lowerFacets (⟨285, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0286 : bundle_a018773121_lowerComputed (⟨286, by decide⟩ : Fin 1069) = lowerFacets (⟨286, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0287 : bundle_a018773121_lowerComputed (⟨287, by decide⟩ : Fin 1069) = lowerFacets (⟨287, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0288 : bundle_a018773121_lowerComputed (⟨288, by decide⟩ : Fin 1069) = lowerFacets (⟨288, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0289 : bundle_a018773121_lowerComputed (⟨289, by decide⟩ : Fin 1069) = lowerFacets (⟨289, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0290 : bundle_a018773121_lowerComputed (⟨290, by decide⟩ : Fin 1069) = lowerFacets (⟨290, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0291 : bundle_a018773121_lowerComputed (⟨291, by decide⟩ : Fin 1069) = lowerFacets (⟨291, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0292 : bundle_a018773121_lowerComputed (⟨292, by decide⟩ : Fin 1069) = lowerFacets (⟨292, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0293 : bundle_a018773121_lowerComputed (⟨293, by decide⟩ : Fin 1069) = lowerFacets (⟨293, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0294 : bundle_a018773121_lowerComputed (⟨294, by decide⟩ : Fin 1069) = lowerFacets (⟨294, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0295 : bundle_a018773121_lowerComputed (⟨295, by decide⟩ : Fin 1069) = lowerFacets (⟨295, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0296 : bundle_a018773121_lowerComputed (⟨296, by decide⟩ : Fin 1069) = lowerFacets (⟨296, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0297 : bundle_a018773121_lowerComputed (⟨297, by decide⟩ : Fin 1069) = lowerFacets (⟨297, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0298 : bundle_a018773121_lowerComputed (⟨298, by decide⟩ : Fin 1069) = lowerFacets (⟨298, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0299 : bundle_a018773121_lowerComputed (⟨299, by decide⟩ : Fin 1069) = lowerFacets (⟨299, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0300 : bundle_a018773121_lowerComputed (⟨300, by decide⟩ : Fin 1069) = lowerFacets (⟨300, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0301 : bundle_a018773121_lowerComputed (⟨301, by decide⟩ : Fin 1069) = lowerFacets (⟨301, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0302 : bundle_a018773121_lowerComputed (⟨302, by decide⟩ : Fin 1069) = lowerFacets (⟨302, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0303 : bundle_a018773121_lowerComputed (⟨303, by decide⟩ : Fin 1069) = lowerFacets (⟨303, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0304 : bundle_a018773121_lowerComputed (⟨304, by decide⟩ : Fin 1069) = lowerFacets (⟨304, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0305 : bundle_a018773121_lowerComputed (⟨305, by decide⟩ : Fin 1069) = lowerFacets (⟨305, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0306 : bundle_a018773121_lowerComputed (⟨306, by decide⟩ : Fin 1069) = lowerFacets (⟨306, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0307 : bundle_a018773121_lowerComputed (⟨307, by decide⟩ : Fin 1069) = lowerFacets (⟨307, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0308 : bundle_a018773121_lowerComputed (⟨308, by decide⟩ : Fin 1069) = lowerFacets (⟨308, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0309 : bundle_a018773121_lowerComputed (⟨309, by decide⟩ : Fin 1069) = lowerFacets (⟨309, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0310 : bundle_a018773121_lowerComputed (⟨310, by decide⟩ : Fin 1069) = lowerFacets (⟨310, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0311 : bundle_a018773121_lowerComputed (⟨311, by decide⟩ : Fin 1069) = lowerFacets (⟨311, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0312 : bundle_a018773121_lowerComputed (⟨312, by decide⟩ : Fin 1069) = lowerFacets (⟨312, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0313 : bundle_a018773121_lowerComputed (⟨313, by decide⟩ : Fin 1069) = lowerFacets (⟨313, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0314 : bundle_a018773121_lowerComputed (⟨314, by decide⟩ : Fin 1069) = lowerFacets (⟨314, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0315 : bundle_a018773121_lowerComputed (⟨315, by decide⟩ : Fin 1069) = lowerFacets (⟨315, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0316 : bundle_a018773121_lowerComputed (⟨316, by decide⟩ : Fin 1069) = lowerFacets (⟨316, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0317 : bundle_a018773121_lowerComputed (⟨317, by decide⟩ : Fin 1069) = lowerFacets (⟨317, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0318 : bundle_a018773121_lowerComputed (⟨318, by decide⟩ : Fin 1069) = lowerFacets (⟨318, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0319 : bundle_a018773121_lowerComputed (⟨319, by decide⟩ : Fin 1069) = lowerFacets (⟨319, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0320 : bundle_a018773121_lowerComputed (⟨320, by decide⟩ : Fin 1069) = lowerFacets (⟨320, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0321 : bundle_a018773121_lowerComputed (⟨321, by decide⟩ : Fin 1069) = lowerFacets (⟨321, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0322 : bundle_a018773121_lowerComputed (⟨322, by decide⟩ : Fin 1069) = lowerFacets (⟨322, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0323 : bundle_a018773121_lowerComputed (⟨323, by decide⟩ : Fin 1069) = lowerFacets (⟨323, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0324 : bundle_a018773121_lowerComputed (⟨324, by decide⟩ : Fin 1069) = lowerFacets (⟨324, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0325 : bundle_a018773121_lowerComputed (⟨325, by decide⟩ : Fin 1069) = lowerFacets (⟨325, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0326 : bundle_a018773121_lowerComputed (⟨326, by decide⟩ : Fin 1069) = lowerFacets (⟨326, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0327 : bundle_a018773121_lowerComputed (⟨327, by decide⟩ : Fin 1069) = lowerFacets (⟨327, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0328 : bundle_a018773121_lowerComputed (⟨328, by decide⟩ : Fin 1069) = lowerFacets (⟨328, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0329 : bundle_a018773121_lowerComputed (⟨329, by decide⟩ : Fin 1069) = lowerFacets (⟨329, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0330 : bundle_a018773121_lowerComputed (⟨330, by decide⟩ : Fin 1069) = lowerFacets (⟨330, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0331 : bundle_a018773121_lowerComputed (⟨331, by decide⟩ : Fin 1069) = lowerFacets (⟨331, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0332 : bundle_a018773121_lowerComputed (⟨332, by decide⟩ : Fin 1069) = lowerFacets (⟨332, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0333 : bundle_a018773121_lowerComputed (⟨333, by decide⟩ : Fin 1069) = lowerFacets (⟨333, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0334 : bundle_a018773121_lowerComputed (⟨334, by decide⟩ : Fin 1069) = lowerFacets (⟨334, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0335 : bundle_a018773121_lowerComputed (⟨335, by decide⟩ : Fin 1069) = lowerFacets (⟨335, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0336 : bundle_a018773121_lowerComputed (⟨336, by decide⟩ : Fin 1069) = lowerFacets (⟨336, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0337 : bundle_a018773121_lowerComputed (⟨337, by decide⟩ : Fin 1069) = lowerFacets (⟨337, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0338 : bundle_a018773121_lowerComputed (⟨338, by decide⟩ : Fin 1069) = lowerFacets (⟨338, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0339 : bundle_a018773121_lowerComputed (⟨339, by decide⟩ : Fin 1069) = lowerFacets (⟨339, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0340 : bundle_a018773121_lowerComputed (⟨340, by decide⟩ : Fin 1069) = lowerFacets (⟨340, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0341 : bundle_a018773121_lowerComputed (⟨341, by decide⟩ : Fin 1069) = lowerFacets (⟨341, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0342 : bundle_a018773121_lowerComputed (⟨342, by decide⟩ : Fin 1069) = lowerFacets (⟨342, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0343 : bundle_a018773121_lowerComputed (⟨343, by decide⟩ : Fin 1069) = lowerFacets (⟨343, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0344 : bundle_a018773121_lowerComputed (⟨344, by decide⟩ : Fin 1069) = lowerFacets (⟨344, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0345 : bundle_a018773121_lowerComputed (⟨345, by decide⟩ : Fin 1069) = lowerFacets (⟨345, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0346 : bundle_a018773121_lowerComputed (⟨346, by decide⟩ : Fin 1069) = lowerFacets (⟨346, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0347 : bundle_a018773121_lowerComputed (⟨347, by decide⟩ : Fin 1069) = lowerFacets (⟨347, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0348 : bundle_a018773121_lowerComputed (⟨348, by decide⟩ : Fin 1069) = lowerFacets (⟨348, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0349 : bundle_a018773121_lowerComputed (⟨349, by decide⟩ : Fin 1069) = lowerFacets (⟨349, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0350 : bundle_a018773121_lowerComputed (⟨350, by decide⟩ : Fin 1069) = lowerFacets (⟨350, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0351 : bundle_a018773121_lowerComputed (⟨351, by decide⟩ : Fin 1069) = lowerFacets (⟨351, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0352 : bundle_a018773121_lowerComputed (⟨352, by decide⟩ : Fin 1069) = lowerFacets (⟨352, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0353 : bundle_a018773121_lowerComputed (⟨353, by decide⟩ : Fin 1069) = lowerFacets (⟨353, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0354 : bundle_a018773121_lowerComputed (⟨354, by decide⟩ : Fin 1069) = lowerFacets (⟨354, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0355 : bundle_a018773121_lowerComputed (⟨355, by decide⟩ : Fin 1069) = lowerFacets (⟨355, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0356 : bundle_a018773121_lowerComputed (⟨356, by decide⟩ : Fin 1069) = lowerFacets (⟨356, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0357 : bundle_a018773121_lowerComputed (⟨357, by decide⟩ : Fin 1069) = lowerFacets (⟨357, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0358 : bundle_a018773121_lowerComputed (⟨358, by decide⟩ : Fin 1069) = lowerFacets (⟨358, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0359 : bundle_a018773121_lowerComputed (⟨359, by decide⟩ : Fin 1069) = lowerFacets (⟨359, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0360 : bundle_a018773121_lowerComputed (⟨360, by decide⟩ : Fin 1069) = lowerFacets (⟨360, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0361 : bundle_a018773121_lowerComputed (⟨361, by decide⟩ : Fin 1069) = lowerFacets (⟨361, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0362 : bundle_a018773121_lowerComputed (⟨362, by decide⟩ : Fin 1069) = lowerFacets (⟨362, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0363 : bundle_a018773121_lowerComputed (⟨363, by decide⟩ : Fin 1069) = lowerFacets (⟨363, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0364 : bundle_a018773121_lowerComputed (⟨364, by decide⟩ : Fin 1069) = lowerFacets (⟨364, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0365 : bundle_a018773121_lowerComputed (⟨365, by decide⟩ : Fin 1069) = lowerFacets (⟨365, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0366 : bundle_a018773121_lowerComputed (⟨366, by decide⟩ : Fin 1069) = lowerFacets (⟨366, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0367 : bundle_a018773121_lowerComputed (⟨367, by decide⟩ : Fin 1069) = lowerFacets (⟨367, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0368 : bundle_a018773121_lowerComputed (⟨368, by decide⟩ : Fin 1069) = lowerFacets (⟨368, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0369 : bundle_a018773121_lowerComputed (⟨369, by decide⟩ : Fin 1069) = lowerFacets (⟨369, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0370 : bundle_a018773121_lowerComputed (⟨370, by decide⟩ : Fin 1069) = lowerFacets (⟨370, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0371 : bundle_a018773121_lowerComputed (⟨371, by decide⟩ : Fin 1069) = lowerFacets (⟨371, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0372 : bundle_a018773121_lowerComputed (⟨372, by decide⟩ : Fin 1069) = lowerFacets (⟨372, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0373 : bundle_a018773121_lowerComputed (⟨373, by decide⟩ : Fin 1069) = lowerFacets (⟨373, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0374 : bundle_a018773121_lowerComputed (⟨374, by decide⟩ : Fin 1069) = lowerFacets (⟨374, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0375 : bundle_a018773121_lowerComputed (⟨375, by decide⟩ : Fin 1069) = lowerFacets (⟨375, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0376 : bundle_a018773121_lowerComputed (⟨376, by decide⟩ : Fin 1069) = lowerFacets (⟨376, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0377 : bundle_a018773121_lowerComputed (⟨377, by decide⟩ : Fin 1069) = lowerFacets (⟨377, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0378 : bundle_a018773121_lowerComputed (⟨378, by decide⟩ : Fin 1069) = lowerFacets (⟨378, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0379 : bundle_a018773121_lowerComputed (⟨379, by decide⟩ : Fin 1069) = lowerFacets (⟨379, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0380 : bundle_a018773121_lowerComputed (⟨380, by decide⟩ : Fin 1069) = lowerFacets (⟨380, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0381 : bundle_a018773121_lowerComputed (⟨381, by decide⟩ : Fin 1069) = lowerFacets (⟨381, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0382 : bundle_a018773121_lowerComputed (⟨382, by decide⟩ : Fin 1069) = lowerFacets (⟨382, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0383 : bundle_a018773121_lowerComputed (⟨383, by decide⟩ : Fin 1069) = lowerFacets (⟨383, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0384 : bundle_a018773121_lowerComputed (⟨384, by decide⟩ : Fin 1069) = lowerFacets (⟨384, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0385 : bundle_a018773121_lowerComputed (⟨385, by decide⟩ : Fin 1069) = lowerFacets (⟨385, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0386 : bundle_a018773121_lowerComputed (⟨386, by decide⟩ : Fin 1069) = lowerFacets (⟨386, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0387 : bundle_a018773121_lowerComputed (⟨387, by decide⟩ : Fin 1069) = lowerFacets (⟨387, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0388 : bundle_a018773121_lowerComputed (⟨388, by decide⟩ : Fin 1069) = lowerFacets (⟨388, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0389 : bundle_a018773121_lowerComputed (⟨389, by decide⟩ : Fin 1069) = lowerFacets (⟨389, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0390 : bundle_a018773121_lowerComputed (⟨390, by decide⟩ : Fin 1069) = lowerFacets (⟨390, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0391 : bundle_a018773121_lowerComputed (⟨391, by decide⟩ : Fin 1069) = lowerFacets (⟨391, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0392 : bundle_a018773121_lowerComputed (⟨392, by decide⟩ : Fin 1069) = lowerFacets (⟨392, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0393 : bundle_a018773121_lowerComputed (⟨393, by decide⟩ : Fin 1069) = lowerFacets (⟨393, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0394 : bundle_a018773121_lowerComputed (⟨394, by decide⟩ : Fin 1069) = lowerFacets (⟨394, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0395 : bundle_a018773121_lowerComputed (⟨395, by decide⟩ : Fin 1069) = lowerFacets (⟨395, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0396 : bundle_a018773121_lowerComputed (⟨396, by decide⟩ : Fin 1069) = lowerFacets (⟨396, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0397 : bundle_a018773121_lowerComputed (⟨397, by decide⟩ : Fin 1069) = lowerFacets (⟨397, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0398 : bundle_a018773121_lowerComputed (⟨398, by decide⟩ : Fin 1069) = lowerFacets (⟨398, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0399 : bundle_a018773121_lowerComputed (⟨399, by decide⟩ : Fin 1069) = lowerFacets (⟨399, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0400 : bundle_a018773121_lowerComputed (⟨400, by decide⟩ : Fin 1069) = lowerFacets (⟨400, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0401 : bundle_a018773121_lowerComputed (⟨401, by decide⟩ : Fin 1069) = lowerFacets (⟨401, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0402 : bundle_a018773121_lowerComputed (⟨402, by decide⟩ : Fin 1069) = lowerFacets (⟨402, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0403 : bundle_a018773121_lowerComputed (⟨403, by decide⟩ : Fin 1069) = lowerFacets (⟨403, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0404 : bundle_a018773121_lowerComputed (⟨404, by decide⟩ : Fin 1069) = lowerFacets (⟨404, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0405 : bundle_a018773121_lowerComputed (⟨405, by decide⟩ : Fin 1069) = lowerFacets (⟨405, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0406 : bundle_a018773121_lowerComputed (⟨406, by decide⟩ : Fin 1069) = lowerFacets (⟨406, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0407 : bundle_a018773121_lowerComputed (⟨407, by decide⟩ : Fin 1069) = lowerFacets (⟨407, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0408 : bundle_a018773121_lowerComputed (⟨408, by decide⟩ : Fin 1069) = lowerFacets (⟨408, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0409 : bundle_a018773121_lowerComputed (⟨409, by decide⟩ : Fin 1069) = lowerFacets (⟨409, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0410 : bundle_a018773121_lowerComputed (⟨410, by decide⟩ : Fin 1069) = lowerFacets (⟨410, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0411 : bundle_a018773121_lowerComputed (⟨411, by decide⟩ : Fin 1069) = lowerFacets (⟨411, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0412 : bundle_a018773121_lowerComputed (⟨412, by decide⟩ : Fin 1069) = lowerFacets (⟨412, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0413 : bundle_a018773121_lowerComputed (⟨413, by decide⟩ : Fin 1069) = lowerFacets (⟨413, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0414 : bundle_a018773121_lowerComputed (⟨414, by decide⟩ : Fin 1069) = lowerFacets (⟨414, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0415 : bundle_a018773121_lowerComputed (⟨415, by decide⟩ : Fin 1069) = lowerFacets (⟨415, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0416 : bundle_a018773121_lowerComputed (⟨416, by decide⟩ : Fin 1069) = lowerFacets (⟨416, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0417 : bundle_a018773121_lowerComputed (⟨417, by decide⟩ : Fin 1069) = lowerFacets (⟨417, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0418 : bundle_a018773121_lowerComputed (⟨418, by decide⟩ : Fin 1069) = lowerFacets (⟨418, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0419 : bundle_a018773121_lowerComputed (⟨419, by decide⟩ : Fin 1069) = lowerFacets (⟨419, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0420 : bundle_a018773121_lowerComputed (⟨420, by decide⟩ : Fin 1069) = lowerFacets (⟨420, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0421 : bundle_a018773121_lowerComputed (⟨421, by decide⟩ : Fin 1069) = lowerFacets (⟨421, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0422 : bundle_a018773121_lowerComputed (⟨422, by decide⟩ : Fin 1069) = lowerFacets (⟨422, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0423 : bundle_a018773121_lowerComputed (⟨423, by decide⟩ : Fin 1069) = lowerFacets (⟨423, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0424 : bundle_a018773121_lowerComputed (⟨424, by decide⟩ : Fin 1069) = lowerFacets (⟨424, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0425 : bundle_a018773121_lowerComputed (⟨425, by decide⟩ : Fin 1069) = lowerFacets (⟨425, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0426 : bundle_a018773121_lowerComputed (⟨426, by decide⟩ : Fin 1069) = lowerFacets (⟨426, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0427 : bundle_a018773121_lowerComputed (⟨427, by decide⟩ : Fin 1069) = lowerFacets (⟨427, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0428 : bundle_a018773121_lowerComputed (⟨428, by decide⟩ : Fin 1069) = lowerFacets (⟨428, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0429 : bundle_a018773121_lowerComputed (⟨429, by decide⟩ : Fin 1069) = lowerFacets (⟨429, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0430 : bundle_a018773121_lowerComputed (⟨430, by decide⟩ : Fin 1069) = lowerFacets (⟨430, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0431 : bundle_a018773121_lowerComputed (⟨431, by decide⟩ : Fin 1069) = lowerFacets (⟨431, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0432 : bundle_a018773121_lowerComputed (⟨432, by decide⟩ : Fin 1069) = lowerFacets (⟨432, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0433 : bundle_a018773121_lowerComputed (⟨433, by decide⟩ : Fin 1069) = lowerFacets (⟨433, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0434 : bundle_a018773121_lowerComputed (⟨434, by decide⟩ : Fin 1069) = lowerFacets (⟨434, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0435 : bundle_a018773121_lowerComputed (⟨435, by decide⟩ : Fin 1069) = lowerFacets (⟨435, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0436 : bundle_a018773121_lowerComputed (⟨436, by decide⟩ : Fin 1069) = lowerFacets (⟨436, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0437 : bundle_a018773121_lowerComputed (⟨437, by decide⟩ : Fin 1069) = lowerFacets (⟨437, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0438 : bundle_a018773121_lowerComputed (⟨438, by decide⟩ : Fin 1069) = lowerFacets (⟨438, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0439 : bundle_a018773121_lowerComputed (⟨439, by decide⟩ : Fin 1069) = lowerFacets (⟨439, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0440 : bundle_a018773121_lowerComputed (⟨440, by decide⟩ : Fin 1069) = lowerFacets (⟨440, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0441 : bundle_a018773121_lowerComputed (⟨441, by decide⟩ : Fin 1069) = lowerFacets (⟨441, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0442 : bundle_a018773121_lowerComputed (⟨442, by decide⟩ : Fin 1069) = lowerFacets (⟨442, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0443 : bundle_a018773121_lowerComputed (⟨443, by decide⟩ : Fin 1069) = lowerFacets (⟨443, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0444 : bundle_a018773121_lowerComputed (⟨444, by decide⟩ : Fin 1069) = lowerFacets (⟨444, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0445 : bundle_a018773121_lowerComputed (⟨445, by decide⟩ : Fin 1069) = lowerFacets (⟨445, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0446 : bundle_a018773121_lowerComputed (⟨446, by decide⟩ : Fin 1069) = lowerFacets (⟨446, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0447 : bundle_a018773121_lowerComputed (⟨447, by decide⟩ : Fin 1069) = lowerFacets (⟨447, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0448 : bundle_a018773121_lowerComputed (⟨448, by decide⟩ : Fin 1069) = lowerFacets (⟨448, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0449 : bundle_a018773121_lowerComputed (⟨449, by decide⟩ : Fin 1069) = lowerFacets (⟨449, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0450 : bundle_a018773121_lowerComputed (⟨450, by decide⟩ : Fin 1069) = lowerFacets (⟨450, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0451 : bundle_a018773121_lowerComputed (⟨451, by decide⟩ : Fin 1069) = lowerFacets (⟨451, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0452 : bundle_a018773121_lowerComputed (⟨452, by decide⟩ : Fin 1069) = lowerFacets (⟨452, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0453 : bundle_a018773121_lowerComputed (⟨453, by decide⟩ : Fin 1069) = lowerFacets (⟨453, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0454 : bundle_a018773121_lowerComputed (⟨454, by decide⟩ : Fin 1069) = lowerFacets (⟨454, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0455 : bundle_a018773121_lowerComputed (⟨455, by decide⟩ : Fin 1069) = lowerFacets (⟨455, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0456 : bundle_a018773121_lowerComputed (⟨456, by decide⟩ : Fin 1069) = lowerFacets (⟨456, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0457 : bundle_a018773121_lowerComputed (⟨457, by decide⟩ : Fin 1069) = lowerFacets (⟨457, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0458 : bundle_a018773121_lowerComputed (⟨458, by decide⟩ : Fin 1069) = lowerFacets (⟨458, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0459 : bundle_a018773121_lowerComputed (⟨459, by decide⟩ : Fin 1069) = lowerFacets (⟨459, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0460 : bundle_a018773121_lowerComputed (⟨460, by decide⟩ : Fin 1069) = lowerFacets (⟨460, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0461 : bundle_a018773121_lowerComputed (⟨461, by decide⟩ : Fin 1069) = lowerFacets (⟨461, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0462 : bundle_a018773121_lowerComputed (⟨462, by decide⟩ : Fin 1069) = lowerFacets (⟨462, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0463 : bundle_a018773121_lowerComputed (⟨463, by decide⟩ : Fin 1069) = lowerFacets (⟨463, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0464 : bundle_a018773121_lowerComputed (⟨464, by decide⟩ : Fin 1069) = lowerFacets (⟨464, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0465 : bundle_a018773121_lowerComputed (⟨465, by decide⟩ : Fin 1069) = lowerFacets (⟨465, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0466 : bundle_a018773121_lowerComputed (⟨466, by decide⟩ : Fin 1069) = lowerFacets (⟨466, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0467 : bundle_a018773121_lowerComputed (⟨467, by decide⟩ : Fin 1069) = lowerFacets (⟨467, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0468 : bundle_a018773121_lowerComputed (⟨468, by decide⟩ : Fin 1069) = lowerFacets (⟨468, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0469 : bundle_a018773121_lowerComputed (⟨469, by decide⟩ : Fin 1069) = lowerFacets (⟨469, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0470 : bundle_a018773121_lowerComputed (⟨470, by decide⟩ : Fin 1069) = lowerFacets (⟨470, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0471 : bundle_a018773121_lowerComputed (⟨471, by decide⟩ : Fin 1069) = lowerFacets (⟨471, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0472 : bundle_a018773121_lowerComputed (⟨472, by decide⟩ : Fin 1069) = lowerFacets (⟨472, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0473 : bundle_a018773121_lowerComputed (⟨473, by decide⟩ : Fin 1069) = lowerFacets (⟨473, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0474 : bundle_a018773121_lowerComputed (⟨474, by decide⟩ : Fin 1069) = lowerFacets (⟨474, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0475 : bundle_a018773121_lowerComputed (⟨475, by decide⟩ : Fin 1069) = lowerFacets (⟨475, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0476 : bundle_a018773121_lowerComputed (⟨476, by decide⟩ : Fin 1069) = lowerFacets (⟨476, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0477 : bundle_a018773121_lowerComputed (⟨477, by decide⟩ : Fin 1069) = lowerFacets (⟨477, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0478 : bundle_a018773121_lowerComputed (⟨478, by decide⟩ : Fin 1069) = lowerFacets (⟨478, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0479 : bundle_a018773121_lowerComputed (⟨479, by decide⟩ : Fin 1069) = lowerFacets (⟨479, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0480 : bundle_a018773121_lowerComputed (⟨480, by decide⟩ : Fin 1069) = lowerFacets (⟨480, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0481 : bundle_a018773121_lowerComputed (⟨481, by decide⟩ : Fin 1069) = lowerFacets (⟨481, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0482 : bundle_a018773121_lowerComputed (⟨482, by decide⟩ : Fin 1069) = lowerFacets (⟨482, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0483 : bundle_a018773121_lowerComputed (⟨483, by decide⟩ : Fin 1069) = lowerFacets (⟨483, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0484 : bundle_a018773121_lowerComputed (⟨484, by decide⟩ : Fin 1069) = lowerFacets (⟨484, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0485 : bundle_a018773121_lowerComputed (⟨485, by decide⟩ : Fin 1069) = lowerFacets (⟨485, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0486 : bundle_a018773121_lowerComputed (⟨486, by decide⟩ : Fin 1069) = lowerFacets (⟨486, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0487 : bundle_a018773121_lowerComputed (⟨487, by decide⟩ : Fin 1069) = lowerFacets (⟨487, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0488 : bundle_a018773121_lowerComputed (⟨488, by decide⟩ : Fin 1069) = lowerFacets (⟨488, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0489 : bundle_a018773121_lowerComputed (⟨489, by decide⟩ : Fin 1069) = lowerFacets (⟨489, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0490 : bundle_a018773121_lowerComputed (⟨490, by decide⟩ : Fin 1069) = lowerFacets (⟨490, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0491 : bundle_a018773121_lowerComputed (⟨491, by decide⟩ : Fin 1069) = lowerFacets (⟨491, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0492 : bundle_a018773121_lowerComputed (⟨492, by decide⟩ : Fin 1069) = lowerFacets (⟨492, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0493 : bundle_a018773121_lowerComputed (⟨493, by decide⟩ : Fin 1069) = lowerFacets (⟨493, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0494 : bundle_a018773121_lowerComputed (⟨494, by decide⟩ : Fin 1069) = lowerFacets (⟨494, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0495 : bundle_a018773121_lowerComputed (⟨495, by decide⟩ : Fin 1069) = lowerFacets (⟨495, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0496 : bundle_a018773121_lowerComputed (⟨496, by decide⟩ : Fin 1069) = lowerFacets (⟨496, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0497 : bundle_a018773121_lowerComputed (⟨497, by decide⟩ : Fin 1069) = lowerFacets (⟨497, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0498 : bundle_a018773121_lowerComputed (⟨498, by decide⟩ : Fin 1069) = lowerFacets (⟨498, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0499 : bundle_a018773121_lowerComputed (⟨499, by decide⟩ : Fin 1069) = lowerFacets (⟨499, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0500 : bundle_a018773121_lowerComputed (⟨500, by decide⟩ : Fin 1069) = lowerFacets (⟨500, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0501 : bundle_a018773121_lowerComputed (⟨501, by decide⟩ : Fin 1069) = lowerFacets (⟨501, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0502 : bundle_a018773121_lowerComputed (⟨502, by decide⟩ : Fin 1069) = lowerFacets (⟨502, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0503 : bundle_a018773121_lowerComputed (⟨503, by decide⟩ : Fin 1069) = lowerFacets (⟨503, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0504 : bundle_a018773121_lowerComputed (⟨504, by decide⟩ : Fin 1069) = lowerFacets (⟨504, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0505 : bundle_a018773121_lowerComputed (⟨505, by decide⟩ : Fin 1069) = lowerFacets (⟨505, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0506 : bundle_a018773121_lowerComputed (⟨506, by decide⟩ : Fin 1069) = lowerFacets (⟨506, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0507 : bundle_a018773121_lowerComputed (⟨507, by decide⟩ : Fin 1069) = lowerFacets (⟨507, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0508 : bundle_a018773121_lowerComputed (⟨508, by decide⟩ : Fin 1069) = lowerFacets (⟨508, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0509 : bundle_a018773121_lowerComputed (⟨509, by decide⟩ : Fin 1069) = lowerFacets (⟨509, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0510 : bundle_a018773121_lowerComputed (⟨510, by decide⟩ : Fin 1069) = lowerFacets (⟨510, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0511 : bundle_a018773121_lowerComputed (⟨511, by decide⟩ : Fin 1069) = lowerFacets (⟨511, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0512 : bundle_a018773121_lowerComputed (⟨512, by decide⟩ : Fin 1069) = lowerFacets (⟨512, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0513 : bundle_a018773121_lowerComputed (⟨513, by decide⟩ : Fin 1069) = lowerFacets (⟨513, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0514 : bundle_a018773121_lowerComputed (⟨514, by decide⟩ : Fin 1069) = lowerFacets (⟨514, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0515 : bundle_a018773121_lowerComputed (⟨515, by decide⟩ : Fin 1069) = lowerFacets (⟨515, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0516 : bundle_a018773121_lowerComputed (⟨516, by decide⟩ : Fin 1069) = lowerFacets (⟨516, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0517 : bundle_a018773121_lowerComputed (⟨517, by decide⟩ : Fin 1069) = lowerFacets (⟨517, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0518 : bundle_a018773121_lowerComputed (⟨518, by decide⟩ : Fin 1069) = lowerFacets (⟨518, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0519 : bundle_a018773121_lowerComputed (⟨519, by decide⟩ : Fin 1069) = lowerFacets (⟨519, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0520 : bundle_a018773121_lowerComputed (⟨520, by decide⟩ : Fin 1069) = lowerFacets (⟨520, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0521 : bundle_a018773121_lowerComputed (⟨521, by decide⟩ : Fin 1069) = lowerFacets (⟨521, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0522 : bundle_a018773121_lowerComputed (⟨522, by decide⟩ : Fin 1069) = lowerFacets (⟨522, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0523 : bundle_a018773121_lowerComputed (⟨523, by decide⟩ : Fin 1069) = lowerFacets (⟨523, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0524 : bundle_a018773121_lowerComputed (⟨524, by decide⟩ : Fin 1069) = lowerFacets (⟨524, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0525 : bundle_a018773121_lowerComputed (⟨525, by decide⟩ : Fin 1069) = lowerFacets (⟨525, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0526 : bundle_a018773121_lowerComputed (⟨526, by decide⟩ : Fin 1069) = lowerFacets (⟨526, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0527 : bundle_a018773121_lowerComputed (⟨527, by decide⟩ : Fin 1069) = lowerFacets (⟨527, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0528 : bundle_a018773121_lowerComputed (⟨528, by decide⟩ : Fin 1069) = lowerFacets (⟨528, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0529 : bundle_a018773121_lowerComputed (⟨529, by decide⟩ : Fin 1069) = lowerFacets (⟨529, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0530 : bundle_a018773121_lowerComputed (⟨530, by decide⟩ : Fin 1069) = lowerFacets (⟨530, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0531 : bundle_a018773121_lowerComputed (⟨531, by decide⟩ : Fin 1069) = lowerFacets (⟨531, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0532 : bundle_a018773121_lowerComputed (⟨532, by decide⟩ : Fin 1069) = lowerFacets (⟨532, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0533 : bundle_a018773121_lowerComputed (⟨533, by decide⟩ : Fin 1069) = lowerFacets (⟨533, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0534 : bundle_a018773121_lowerComputed (⟨534, by decide⟩ : Fin 1069) = lowerFacets (⟨534, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0535 : bundle_a018773121_lowerComputed (⟨535, by decide⟩ : Fin 1069) = lowerFacets (⟨535, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0536 : bundle_a018773121_lowerComputed (⟨536, by decide⟩ : Fin 1069) = lowerFacets (⟨536, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0537 : bundle_a018773121_lowerComputed (⟨537, by decide⟩ : Fin 1069) = lowerFacets (⟨537, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0538 : bundle_a018773121_lowerComputed (⟨538, by decide⟩ : Fin 1069) = lowerFacets (⟨538, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0539 : bundle_a018773121_lowerComputed (⟨539, by decide⟩ : Fin 1069) = lowerFacets (⟨539, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0540 : bundle_a018773121_lowerComputed (⟨540, by decide⟩ : Fin 1069) = lowerFacets (⟨540, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0541 : bundle_a018773121_lowerComputed (⟨541, by decide⟩ : Fin 1069) = lowerFacets (⟨541, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0542 : bundle_a018773121_lowerComputed (⟨542, by decide⟩ : Fin 1069) = lowerFacets (⟨542, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0543 : bundle_a018773121_lowerComputed (⟨543, by decide⟩ : Fin 1069) = lowerFacets (⟨543, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0544 : bundle_a018773121_lowerComputed (⟨544, by decide⟩ : Fin 1069) = lowerFacets (⟨544, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0545 : bundle_a018773121_lowerComputed (⟨545, by decide⟩ : Fin 1069) = lowerFacets (⟨545, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0546 : bundle_a018773121_lowerComputed (⟨546, by decide⟩ : Fin 1069) = lowerFacets (⟨546, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0547 : bundle_a018773121_lowerComputed (⟨547, by decide⟩ : Fin 1069) = lowerFacets (⟨547, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0548 : bundle_a018773121_lowerComputed (⟨548, by decide⟩ : Fin 1069) = lowerFacets (⟨548, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0549 : bundle_a018773121_lowerComputed (⟨549, by decide⟩ : Fin 1069) = lowerFacets (⟨549, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0550 : bundle_a018773121_lowerComputed (⟨550, by decide⟩ : Fin 1069) = lowerFacets (⟨550, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0551 : bundle_a018773121_lowerComputed (⟨551, by decide⟩ : Fin 1069) = lowerFacets (⟨551, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0552 : bundle_a018773121_lowerComputed (⟨552, by decide⟩ : Fin 1069) = lowerFacets (⟨552, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0553 : bundle_a018773121_lowerComputed (⟨553, by decide⟩ : Fin 1069) = lowerFacets (⟨553, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0554 : bundle_a018773121_lowerComputed (⟨554, by decide⟩ : Fin 1069) = lowerFacets (⟨554, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0555 : bundle_a018773121_lowerComputed (⟨555, by decide⟩ : Fin 1069) = lowerFacets (⟨555, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0556 : bundle_a018773121_lowerComputed (⟨556, by decide⟩ : Fin 1069) = lowerFacets (⟨556, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0557 : bundle_a018773121_lowerComputed (⟨557, by decide⟩ : Fin 1069) = lowerFacets (⟨557, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0558 : bundle_a018773121_lowerComputed (⟨558, by decide⟩ : Fin 1069) = lowerFacets (⟨558, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0559 : bundle_a018773121_lowerComputed (⟨559, by decide⟩ : Fin 1069) = lowerFacets (⟨559, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0560 : bundle_a018773121_lowerComputed (⟨560, by decide⟩ : Fin 1069) = lowerFacets (⟨560, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0561 : bundle_a018773121_lowerComputed (⟨561, by decide⟩ : Fin 1069) = lowerFacets (⟨561, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0562 : bundle_a018773121_lowerComputed (⟨562, by decide⟩ : Fin 1069) = lowerFacets (⟨562, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0563 : bundle_a018773121_lowerComputed (⟨563, by decide⟩ : Fin 1069) = lowerFacets (⟨563, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0564 : bundle_a018773121_lowerComputed (⟨564, by decide⟩ : Fin 1069) = lowerFacets (⟨564, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0565 : bundle_a018773121_lowerComputed (⟨565, by decide⟩ : Fin 1069) = lowerFacets (⟨565, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0566 : bundle_a018773121_lowerComputed (⟨566, by decide⟩ : Fin 1069) = lowerFacets (⟨566, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0567 : bundle_a018773121_lowerComputed (⟨567, by decide⟩ : Fin 1069) = lowerFacets (⟨567, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0568 : bundle_a018773121_lowerComputed (⟨568, by decide⟩ : Fin 1069) = lowerFacets (⟨568, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0569 : bundle_a018773121_lowerComputed (⟨569, by decide⟩ : Fin 1069) = lowerFacets (⟨569, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0570 : bundle_a018773121_lowerComputed (⟨570, by decide⟩ : Fin 1069) = lowerFacets (⟨570, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0571 : bundle_a018773121_lowerComputed (⟨571, by decide⟩ : Fin 1069) = lowerFacets (⟨571, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0572 : bundle_a018773121_lowerComputed (⟨572, by decide⟩ : Fin 1069) = lowerFacets (⟨572, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0573 : bundle_a018773121_lowerComputed (⟨573, by decide⟩ : Fin 1069) = lowerFacets (⟨573, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0574 : bundle_a018773121_lowerComputed (⟨574, by decide⟩ : Fin 1069) = lowerFacets (⟨574, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0575 : bundle_a018773121_lowerComputed (⟨575, by decide⟩ : Fin 1069) = lowerFacets (⟨575, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0576 : bundle_a018773121_lowerComputed (⟨576, by decide⟩ : Fin 1069) = lowerFacets (⟨576, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0577 : bundle_a018773121_lowerComputed (⟨577, by decide⟩ : Fin 1069) = lowerFacets (⟨577, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0578 : bundle_a018773121_lowerComputed (⟨578, by decide⟩ : Fin 1069) = lowerFacets (⟨578, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0579 : bundle_a018773121_lowerComputed (⟨579, by decide⟩ : Fin 1069) = lowerFacets (⟨579, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0580 : bundle_a018773121_lowerComputed (⟨580, by decide⟩ : Fin 1069) = lowerFacets (⟨580, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0581 : bundle_a018773121_lowerComputed (⟨581, by decide⟩ : Fin 1069) = lowerFacets (⟨581, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0582 : bundle_a018773121_lowerComputed (⟨582, by decide⟩ : Fin 1069) = lowerFacets (⟨582, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0583 : bundle_a018773121_lowerComputed (⟨583, by decide⟩ : Fin 1069) = lowerFacets (⟨583, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0584 : bundle_a018773121_lowerComputed (⟨584, by decide⟩ : Fin 1069) = lowerFacets (⟨584, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0585 : bundle_a018773121_lowerComputed (⟨585, by decide⟩ : Fin 1069) = lowerFacets (⟨585, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0586 : bundle_a018773121_lowerComputed (⟨586, by decide⟩ : Fin 1069) = lowerFacets (⟨586, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0587 : bundle_a018773121_lowerComputed (⟨587, by decide⟩ : Fin 1069) = lowerFacets (⟨587, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0588 : bundle_a018773121_lowerComputed (⟨588, by decide⟩ : Fin 1069) = lowerFacets (⟨588, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0589 : bundle_a018773121_lowerComputed (⟨589, by decide⟩ : Fin 1069) = lowerFacets (⟨589, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0590 : bundle_a018773121_lowerComputed (⟨590, by decide⟩ : Fin 1069) = lowerFacets (⟨590, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0591 : bundle_a018773121_lowerComputed (⟨591, by decide⟩ : Fin 1069) = lowerFacets (⟨591, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0592 : bundle_a018773121_lowerComputed (⟨592, by decide⟩ : Fin 1069) = lowerFacets (⟨592, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0593 : bundle_a018773121_lowerComputed (⟨593, by decide⟩ : Fin 1069) = lowerFacets (⟨593, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0594 : bundle_a018773121_lowerComputed (⟨594, by decide⟩ : Fin 1069) = lowerFacets (⟨594, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0595 : bundle_a018773121_lowerComputed (⟨595, by decide⟩ : Fin 1069) = lowerFacets (⟨595, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0596 : bundle_a018773121_lowerComputed (⟨596, by decide⟩ : Fin 1069) = lowerFacets (⟨596, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0597 : bundle_a018773121_lowerComputed (⟨597, by decide⟩ : Fin 1069) = lowerFacets (⟨597, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0598 : bundle_a018773121_lowerComputed (⟨598, by decide⟩ : Fin 1069) = lowerFacets (⟨598, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0599 : bundle_a018773121_lowerComputed (⟨599, by decide⟩ : Fin 1069) = lowerFacets (⟨599, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0600 : bundle_a018773121_lowerComputed (⟨600, by decide⟩ : Fin 1069) = lowerFacets (⟨600, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0601 : bundle_a018773121_lowerComputed (⟨601, by decide⟩ : Fin 1069) = lowerFacets (⟨601, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0602 : bundle_a018773121_lowerComputed (⟨602, by decide⟩ : Fin 1069) = lowerFacets (⟨602, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0603 : bundle_a018773121_lowerComputed (⟨603, by decide⟩ : Fin 1069) = lowerFacets (⟨603, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0604 : bundle_a018773121_lowerComputed (⟨604, by decide⟩ : Fin 1069) = lowerFacets (⟨604, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0605 : bundle_a018773121_lowerComputed (⟨605, by decide⟩ : Fin 1069) = lowerFacets (⟨605, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0606 : bundle_a018773121_lowerComputed (⟨606, by decide⟩ : Fin 1069) = lowerFacets (⟨606, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0607 : bundle_a018773121_lowerComputed (⟨607, by decide⟩ : Fin 1069) = lowerFacets (⟨607, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0608 : bundle_a018773121_lowerComputed (⟨608, by decide⟩ : Fin 1069) = lowerFacets (⟨608, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0609 : bundle_a018773121_lowerComputed (⟨609, by decide⟩ : Fin 1069) = lowerFacets (⟨609, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0610 : bundle_a018773121_lowerComputed (⟨610, by decide⟩ : Fin 1069) = lowerFacets (⟨610, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0611 : bundle_a018773121_lowerComputed (⟨611, by decide⟩ : Fin 1069) = lowerFacets (⟨611, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0612 : bundle_a018773121_lowerComputed (⟨612, by decide⟩ : Fin 1069) = lowerFacets (⟨612, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0613 : bundle_a018773121_lowerComputed (⟨613, by decide⟩ : Fin 1069) = lowerFacets (⟨613, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0614 : bundle_a018773121_lowerComputed (⟨614, by decide⟩ : Fin 1069) = lowerFacets (⟨614, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0615 : bundle_a018773121_lowerComputed (⟨615, by decide⟩ : Fin 1069) = lowerFacets (⟨615, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0616 : bundle_a018773121_lowerComputed (⟨616, by decide⟩ : Fin 1069) = lowerFacets (⟨616, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0617 : bundle_a018773121_lowerComputed (⟨617, by decide⟩ : Fin 1069) = lowerFacets (⟨617, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0618 : bundle_a018773121_lowerComputed (⟨618, by decide⟩ : Fin 1069) = lowerFacets (⟨618, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0619 : bundle_a018773121_lowerComputed (⟨619, by decide⟩ : Fin 1069) = lowerFacets (⟨619, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0620 : bundle_a018773121_lowerComputed (⟨620, by decide⟩ : Fin 1069) = lowerFacets (⟨620, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0621 : bundle_a018773121_lowerComputed (⟨621, by decide⟩ : Fin 1069) = lowerFacets (⟨621, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0622 : bundle_a018773121_lowerComputed (⟨622, by decide⟩ : Fin 1069) = lowerFacets (⟨622, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0623 : bundle_a018773121_lowerComputed (⟨623, by decide⟩ : Fin 1069) = lowerFacets (⟨623, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0624 : bundle_a018773121_lowerComputed (⟨624, by decide⟩ : Fin 1069) = lowerFacets (⟨624, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0625 : bundle_a018773121_lowerComputed (⟨625, by decide⟩ : Fin 1069) = lowerFacets (⟨625, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0626 : bundle_a018773121_lowerComputed (⟨626, by decide⟩ : Fin 1069) = lowerFacets (⟨626, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0627 : bundle_a018773121_lowerComputed (⟨627, by decide⟩ : Fin 1069) = lowerFacets (⟨627, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0628 : bundle_a018773121_lowerComputed (⟨628, by decide⟩ : Fin 1069) = lowerFacets (⟨628, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0629 : bundle_a018773121_lowerComputed (⟨629, by decide⟩ : Fin 1069) = lowerFacets (⟨629, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0630 : bundle_a018773121_lowerComputed (⟨630, by decide⟩ : Fin 1069) = lowerFacets (⟨630, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0631 : bundle_a018773121_lowerComputed (⟨631, by decide⟩ : Fin 1069) = lowerFacets (⟨631, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0632 : bundle_a018773121_lowerComputed (⟨632, by decide⟩ : Fin 1069) = lowerFacets (⟨632, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0633 : bundle_a018773121_lowerComputed (⟨633, by decide⟩ : Fin 1069) = lowerFacets (⟨633, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0634 : bundle_a018773121_lowerComputed (⟨634, by decide⟩ : Fin 1069) = lowerFacets (⟨634, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0635 : bundle_a018773121_lowerComputed (⟨635, by decide⟩ : Fin 1069) = lowerFacets (⟨635, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0636 : bundle_a018773121_lowerComputed (⟨636, by decide⟩ : Fin 1069) = lowerFacets (⟨636, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0637 : bundle_a018773121_lowerComputed (⟨637, by decide⟩ : Fin 1069) = lowerFacets (⟨637, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0638 : bundle_a018773121_lowerComputed (⟨638, by decide⟩ : Fin 1069) = lowerFacets (⟨638, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0639 : bundle_a018773121_lowerComputed (⟨639, by decide⟩ : Fin 1069) = lowerFacets (⟨639, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0640 : bundle_a018773121_lowerComputed (⟨640, by decide⟩ : Fin 1069) = lowerFacets (⟨640, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0641 : bundle_a018773121_lowerComputed (⟨641, by decide⟩ : Fin 1069) = lowerFacets (⟨641, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0642 : bundle_a018773121_lowerComputed (⟨642, by decide⟩ : Fin 1069) = lowerFacets (⟨642, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0643 : bundle_a018773121_lowerComputed (⟨643, by decide⟩ : Fin 1069) = lowerFacets (⟨643, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0644 : bundle_a018773121_lowerComputed (⟨644, by decide⟩ : Fin 1069) = lowerFacets (⟨644, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0645 : bundle_a018773121_lowerComputed (⟨645, by decide⟩ : Fin 1069) = lowerFacets (⟨645, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0646 : bundle_a018773121_lowerComputed (⟨646, by decide⟩ : Fin 1069) = lowerFacets (⟨646, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0647 : bundle_a018773121_lowerComputed (⟨647, by decide⟩ : Fin 1069) = lowerFacets (⟨647, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0648 : bundle_a018773121_lowerComputed (⟨648, by decide⟩ : Fin 1069) = lowerFacets (⟨648, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0649 : bundle_a018773121_lowerComputed (⟨649, by decide⟩ : Fin 1069) = lowerFacets (⟨649, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0650 : bundle_a018773121_lowerComputed (⟨650, by decide⟩ : Fin 1069) = lowerFacets (⟨650, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0651 : bundle_a018773121_lowerComputed (⟨651, by decide⟩ : Fin 1069) = lowerFacets (⟨651, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0652 : bundle_a018773121_lowerComputed (⟨652, by decide⟩ : Fin 1069) = lowerFacets (⟨652, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0653 : bundle_a018773121_lowerComputed (⟨653, by decide⟩ : Fin 1069) = lowerFacets (⟨653, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0654 : bundle_a018773121_lowerComputed (⟨654, by decide⟩ : Fin 1069) = lowerFacets (⟨654, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0655 : bundle_a018773121_lowerComputed (⟨655, by decide⟩ : Fin 1069) = lowerFacets (⟨655, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0656 : bundle_a018773121_lowerComputed (⟨656, by decide⟩ : Fin 1069) = lowerFacets (⟨656, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0657 : bundle_a018773121_lowerComputed (⟨657, by decide⟩ : Fin 1069) = lowerFacets (⟨657, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0658 : bundle_a018773121_lowerComputed (⟨658, by decide⟩ : Fin 1069) = lowerFacets (⟨658, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0659 : bundle_a018773121_lowerComputed (⟨659, by decide⟩ : Fin 1069) = lowerFacets (⟨659, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0660 : bundle_a018773121_lowerComputed (⟨660, by decide⟩ : Fin 1069) = lowerFacets (⟨660, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0661 : bundle_a018773121_lowerComputed (⟨661, by decide⟩ : Fin 1069) = lowerFacets (⟨661, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0662 : bundle_a018773121_lowerComputed (⟨662, by decide⟩ : Fin 1069) = lowerFacets (⟨662, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0663 : bundle_a018773121_lowerComputed (⟨663, by decide⟩ : Fin 1069) = lowerFacets (⟨663, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0664 : bundle_a018773121_lowerComputed (⟨664, by decide⟩ : Fin 1069) = lowerFacets (⟨664, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0665 : bundle_a018773121_lowerComputed (⟨665, by decide⟩ : Fin 1069) = lowerFacets (⟨665, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0666 : bundle_a018773121_lowerComputed (⟨666, by decide⟩ : Fin 1069) = lowerFacets (⟨666, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0667 : bundle_a018773121_lowerComputed (⟨667, by decide⟩ : Fin 1069) = lowerFacets (⟨667, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0668 : bundle_a018773121_lowerComputed (⟨668, by decide⟩ : Fin 1069) = lowerFacets (⟨668, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0669 : bundle_a018773121_lowerComputed (⟨669, by decide⟩ : Fin 1069) = lowerFacets (⟨669, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0670 : bundle_a018773121_lowerComputed (⟨670, by decide⟩ : Fin 1069) = lowerFacets (⟨670, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0671 : bundle_a018773121_lowerComputed (⟨671, by decide⟩ : Fin 1069) = lowerFacets (⟨671, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0672 : bundle_a018773121_lowerComputed (⟨672, by decide⟩ : Fin 1069) = lowerFacets (⟨672, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0673 : bundle_a018773121_lowerComputed (⟨673, by decide⟩ : Fin 1069) = lowerFacets (⟨673, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0674 : bundle_a018773121_lowerComputed (⟨674, by decide⟩ : Fin 1069) = lowerFacets (⟨674, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0675 : bundle_a018773121_lowerComputed (⟨675, by decide⟩ : Fin 1069) = lowerFacets (⟨675, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0676 : bundle_a018773121_lowerComputed (⟨676, by decide⟩ : Fin 1069) = lowerFacets (⟨676, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0677 : bundle_a018773121_lowerComputed (⟨677, by decide⟩ : Fin 1069) = lowerFacets (⟨677, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0678 : bundle_a018773121_lowerComputed (⟨678, by decide⟩ : Fin 1069) = lowerFacets (⟨678, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0679 : bundle_a018773121_lowerComputed (⟨679, by decide⟩ : Fin 1069) = lowerFacets (⟨679, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0680 : bundle_a018773121_lowerComputed (⟨680, by decide⟩ : Fin 1069) = lowerFacets (⟨680, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0681 : bundle_a018773121_lowerComputed (⟨681, by decide⟩ : Fin 1069) = lowerFacets (⟨681, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0682 : bundle_a018773121_lowerComputed (⟨682, by decide⟩ : Fin 1069) = lowerFacets (⟨682, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0683 : bundle_a018773121_lowerComputed (⟨683, by decide⟩ : Fin 1069) = lowerFacets (⟨683, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0684 : bundle_a018773121_lowerComputed (⟨684, by decide⟩ : Fin 1069) = lowerFacets (⟨684, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0685 : bundle_a018773121_lowerComputed (⟨685, by decide⟩ : Fin 1069) = lowerFacets (⟨685, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0686 : bundle_a018773121_lowerComputed (⟨686, by decide⟩ : Fin 1069) = lowerFacets (⟨686, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0687 : bundle_a018773121_lowerComputed (⟨687, by decide⟩ : Fin 1069) = lowerFacets (⟨687, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0688 : bundle_a018773121_lowerComputed (⟨688, by decide⟩ : Fin 1069) = lowerFacets (⟨688, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0689 : bundle_a018773121_lowerComputed (⟨689, by decide⟩ : Fin 1069) = lowerFacets (⟨689, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0690 : bundle_a018773121_lowerComputed (⟨690, by decide⟩ : Fin 1069) = lowerFacets (⟨690, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0691 : bundle_a018773121_lowerComputed (⟨691, by decide⟩ : Fin 1069) = lowerFacets (⟨691, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0692 : bundle_a018773121_lowerComputed (⟨692, by decide⟩ : Fin 1069) = lowerFacets (⟨692, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0693 : bundle_a018773121_lowerComputed (⟨693, by decide⟩ : Fin 1069) = lowerFacets (⟨693, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0694 : bundle_a018773121_lowerComputed (⟨694, by decide⟩ : Fin 1069) = lowerFacets (⟨694, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0695 : bundle_a018773121_lowerComputed (⟨695, by decide⟩ : Fin 1069) = lowerFacets (⟨695, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0696 : bundle_a018773121_lowerComputed (⟨696, by decide⟩ : Fin 1069) = lowerFacets (⟨696, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0697 : bundle_a018773121_lowerComputed (⟨697, by decide⟩ : Fin 1069) = lowerFacets (⟨697, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0698 : bundle_a018773121_lowerComputed (⟨698, by decide⟩ : Fin 1069) = lowerFacets (⟨698, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0699 : bundle_a018773121_lowerComputed (⟨699, by decide⟩ : Fin 1069) = lowerFacets (⟨699, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0700 : bundle_a018773121_lowerComputed (⟨700, by decide⟩ : Fin 1069) = lowerFacets (⟨700, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0701 : bundle_a018773121_lowerComputed (⟨701, by decide⟩ : Fin 1069) = lowerFacets (⟨701, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0702 : bundle_a018773121_lowerComputed (⟨702, by decide⟩ : Fin 1069) = lowerFacets (⟨702, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0703 : bundle_a018773121_lowerComputed (⟨703, by decide⟩ : Fin 1069) = lowerFacets (⟨703, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0704 : bundle_a018773121_lowerComputed (⟨704, by decide⟩ : Fin 1069) = lowerFacets (⟨704, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0705 : bundle_a018773121_lowerComputed (⟨705, by decide⟩ : Fin 1069) = lowerFacets (⟨705, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0706 : bundle_a018773121_lowerComputed (⟨706, by decide⟩ : Fin 1069) = lowerFacets (⟨706, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0707 : bundle_a018773121_lowerComputed (⟨707, by decide⟩ : Fin 1069) = lowerFacets (⟨707, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0708 : bundle_a018773121_lowerComputed (⟨708, by decide⟩ : Fin 1069) = lowerFacets (⟨708, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0709 : bundle_a018773121_lowerComputed (⟨709, by decide⟩ : Fin 1069) = lowerFacets (⟨709, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0710 : bundle_a018773121_lowerComputed (⟨710, by decide⟩ : Fin 1069) = lowerFacets (⟨710, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0711 : bundle_a018773121_lowerComputed (⟨711, by decide⟩ : Fin 1069) = lowerFacets (⟨711, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0712 : bundle_a018773121_lowerComputed (⟨712, by decide⟩ : Fin 1069) = lowerFacets (⟨712, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0713 : bundle_a018773121_lowerComputed (⟨713, by decide⟩ : Fin 1069) = lowerFacets (⟨713, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0714 : bundle_a018773121_lowerComputed (⟨714, by decide⟩ : Fin 1069) = lowerFacets (⟨714, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0715 : bundle_a018773121_lowerComputed (⟨715, by decide⟩ : Fin 1069) = lowerFacets (⟨715, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0716 : bundle_a018773121_lowerComputed (⟨716, by decide⟩ : Fin 1069) = lowerFacets (⟨716, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0717 : bundle_a018773121_lowerComputed (⟨717, by decide⟩ : Fin 1069) = lowerFacets (⟨717, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0718 : bundle_a018773121_lowerComputed (⟨718, by decide⟩ : Fin 1069) = lowerFacets (⟨718, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0719 : bundle_a018773121_lowerComputed (⟨719, by decide⟩ : Fin 1069) = lowerFacets (⟨719, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0720 : bundle_a018773121_lowerComputed (⟨720, by decide⟩ : Fin 1069) = lowerFacets (⟨720, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0721 : bundle_a018773121_lowerComputed (⟨721, by decide⟩ : Fin 1069) = lowerFacets (⟨721, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0722 : bundle_a018773121_lowerComputed (⟨722, by decide⟩ : Fin 1069) = lowerFacets (⟨722, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0723 : bundle_a018773121_lowerComputed (⟨723, by decide⟩ : Fin 1069) = lowerFacets (⟨723, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0724 : bundle_a018773121_lowerComputed (⟨724, by decide⟩ : Fin 1069) = lowerFacets (⟨724, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0725 : bundle_a018773121_lowerComputed (⟨725, by decide⟩ : Fin 1069) = lowerFacets (⟨725, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0726 : bundle_a018773121_lowerComputed (⟨726, by decide⟩ : Fin 1069) = lowerFacets (⟨726, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0727 : bundle_a018773121_lowerComputed (⟨727, by decide⟩ : Fin 1069) = lowerFacets (⟨727, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0728 : bundle_a018773121_lowerComputed (⟨728, by decide⟩ : Fin 1069) = lowerFacets (⟨728, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0729 : bundle_a018773121_lowerComputed (⟨729, by decide⟩ : Fin 1069) = lowerFacets (⟨729, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0730 : bundle_a018773121_lowerComputed (⟨730, by decide⟩ : Fin 1069) = lowerFacets (⟨730, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0731 : bundle_a018773121_lowerComputed (⟨731, by decide⟩ : Fin 1069) = lowerFacets (⟨731, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0732 : bundle_a018773121_lowerComputed (⟨732, by decide⟩ : Fin 1069) = lowerFacets (⟨732, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0733 : bundle_a018773121_lowerComputed (⟨733, by decide⟩ : Fin 1069) = lowerFacets (⟨733, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0734 : bundle_a018773121_lowerComputed (⟨734, by decide⟩ : Fin 1069) = lowerFacets (⟨734, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0735 : bundle_a018773121_lowerComputed (⟨735, by decide⟩ : Fin 1069) = lowerFacets (⟨735, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0736 : bundle_a018773121_lowerComputed (⟨736, by decide⟩ : Fin 1069) = lowerFacets (⟨736, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0737 : bundle_a018773121_lowerComputed (⟨737, by decide⟩ : Fin 1069) = lowerFacets (⟨737, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0738 : bundle_a018773121_lowerComputed (⟨738, by decide⟩ : Fin 1069) = lowerFacets (⟨738, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0739 : bundle_a018773121_lowerComputed (⟨739, by decide⟩ : Fin 1069) = lowerFacets (⟨739, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0740 : bundle_a018773121_lowerComputed (⟨740, by decide⟩ : Fin 1069) = lowerFacets (⟨740, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0741 : bundle_a018773121_lowerComputed (⟨741, by decide⟩ : Fin 1069) = lowerFacets (⟨741, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0742 : bundle_a018773121_lowerComputed (⟨742, by decide⟩ : Fin 1069) = lowerFacets (⟨742, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0743 : bundle_a018773121_lowerComputed (⟨743, by decide⟩ : Fin 1069) = lowerFacets (⟨743, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0744 : bundle_a018773121_lowerComputed (⟨744, by decide⟩ : Fin 1069) = lowerFacets (⟨744, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0745 : bundle_a018773121_lowerComputed (⟨745, by decide⟩ : Fin 1069) = lowerFacets (⟨745, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0746 : bundle_a018773121_lowerComputed (⟨746, by decide⟩ : Fin 1069) = lowerFacets (⟨746, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0747 : bundle_a018773121_lowerComputed (⟨747, by decide⟩ : Fin 1069) = lowerFacets (⟨747, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0748 : bundle_a018773121_lowerComputed (⟨748, by decide⟩ : Fin 1069) = lowerFacets (⟨748, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0749 : bundle_a018773121_lowerComputed (⟨749, by decide⟩ : Fin 1069) = lowerFacets (⟨749, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0750 : bundle_a018773121_lowerComputed (⟨750, by decide⟩ : Fin 1069) = lowerFacets (⟨750, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0751 : bundle_a018773121_lowerComputed (⟨751, by decide⟩ : Fin 1069) = lowerFacets (⟨751, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0752 : bundle_a018773121_lowerComputed (⟨752, by decide⟩ : Fin 1069) = lowerFacets (⟨752, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0753 : bundle_a018773121_lowerComputed (⟨753, by decide⟩ : Fin 1069) = lowerFacets (⟨753, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0754 : bundle_a018773121_lowerComputed (⟨754, by decide⟩ : Fin 1069) = lowerFacets (⟨754, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0755 : bundle_a018773121_lowerComputed (⟨755, by decide⟩ : Fin 1069) = lowerFacets (⟨755, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0756 : bundle_a018773121_lowerComputed (⟨756, by decide⟩ : Fin 1069) = lowerFacets (⟨756, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0757 : bundle_a018773121_lowerComputed (⟨757, by decide⟩ : Fin 1069) = lowerFacets (⟨757, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0758 : bundle_a018773121_lowerComputed (⟨758, by decide⟩ : Fin 1069) = lowerFacets (⟨758, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0759 : bundle_a018773121_lowerComputed (⟨759, by decide⟩ : Fin 1069) = lowerFacets (⟨759, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0760 : bundle_a018773121_lowerComputed (⟨760, by decide⟩ : Fin 1069) = lowerFacets (⟨760, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0761 : bundle_a018773121_lowerComputed (⟨761, by decide⟩ : Fin 1069) = lowerFacets (⟨761, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0762 : bundle_a018773121_lowerComputed (⟨762, by decide⟩ : Fin 1069) = lowerFacets (⟨762, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0763 : bundle_a018773121_lowerComputed (⟨763, by decide⟩ : Fin 1069) = lowerFacets (⟨763, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0764 : bundle_a018773121_lowerComputed (⟨764, by decide⟩ : Fin 1069) = lowerFacets (⟨764, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0765 : bundle_a018773121_lowerComputed (⟨765, by decide⟩ : Fin 1069) = lowerFacets (⟨765, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0766 : bundle_a018773121_lowerComputed (⟨766, by decide⟩ : Fin 1069) = lowerFacets (⟨766, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0767 : bundle_a018773121_lowerComputed (⟨767, by decide⟩ : Fin 1069) = lowerFacets (⟨767, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0768 : bundle_a018773121_lowerComputed (⟨768, by decide⟩ : Fin 1069) = lowerFacets (⟨768, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0769 : bundle_a018773121_lowerComputed (⟨769, by decide⟩ : Fin 1069) = lowerFacets (⟨769, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0770 : bundle_a018773121_lowerComputed (⟨770, by decide⟩ : Fin 1069) = lowerFacets (⟨770, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0771 : bundle_a018773121_lowerComputed (⟨771, by decide⟩ : Fin 1069) = lowerFacets (⟨771, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0772 : bundle_a018773121_lowerComputed (⟨772, by decide⟩ : Fin 1069) = lowerFacets (⟨772, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0773 : bundle_a018773121_lowerComputed (⟨773, by decide⟩ : Fin 1069) = lowerFacets (⟨773, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0774 : bundle_a018773121_lowerComputed (⟨774, by decide⟩ : Fin 1069) = lowerFacets (⟨774, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0775 : bundle_a018773121_lowerComputed (⟨775, by decide⟩ : Fin 1069) = lowerFacets (⟨775, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0776 : bundle_a018773121_lowerComputed (⟨776, by decide⟩ : Fin 1069) = lowerFacets (⟨776, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0777 : bundle_a018773121_lowerComputed (⟨777, by decide⟩ : Fin 1069) = lowerFacets (⟨777, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0778 : bundle_a018773121_lowerComputed (⟨778, by decide⟩ : Fin 1069) = lowerFacets (⟨778, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0779 : bundle_a018773121_lowerComputed (⟨779, by decide⟩ : Fin 1069) = lowerFacets (⟨779, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0780 : bundle_a018773121_lowerComputed (⟨780, by decide⟩ : Fin 1069) = lowerFacets (⟨780, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0781 : bundle_a018773121_lowerComputed (⟨781, by decide⟩ : Fin 1069) = lowerFacets (⟨781, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0782 : bundle_a018773121_lowerComputed (⟨782, by decide⟩ : Fin 1069) = lowerFacets (⟨782, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0783 : bundle_a018773121_lowerComputed (⟨783, by decide⟩ : Fin 1069) = lowerFacets (⟨783, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0784 : bundle_a018773121_lowerComputed (⟨784, by decide⟩ : Fin 1069) = lowerFacets (⟨784, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0785 : bundle_a018773121_lowerComputed (⟨785, by decide⟩ : Fin 1069) = lowerFacets (⟨785, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0786 : bundle_a018773121_lowerComputed (⟨786, by decide⟩ : Fin 1069) = lowerFacets (⟨786, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0787 : bundle_a018773121_lowerComputed (⟨787, by decide⟩ : Fin 1069) = lowerFacets (⟨787, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0788 : bundle_a018773121_lowerComputed (⟨788, by decide⟩ : Fin 1069) = lowerFacets (⟨788, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0789 : bundle_a018773121_lowerComputed (⟨789, by decide⟩ : Fin 1069) = lowerFacets (⟨789, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0790 : bundle_a018773121_lowerComputed (⟨790, by decide⟩ : Fin 1069) = lowerFacets (⟨790, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0791 : bundle_a018773121_lowerComputed (⟨791, by decide⟩ : Fin 1069) = lowerFacets (⟨791, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0792 : bundle_a018773121_lowerComputed (⟨792, by decide⟩ : Fin 1069) = lowerFacets (⟨792, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0793 : bundle_a018773121_lowerComputed (⟨793, by decide⟩ : Fin 1069) = lowerFacets (⟨793, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0794 : bundle_a018773121_lowerComputed (⟨794, by decide⟩ : Fin 1069) = lowerFacets (⟨794, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0795 : bundle_a018773121_lowerComputed (⟨795, by decide⟩ : Fin 1069) = lowerFacets (⟨795, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0796 : bundle_a018773121_lowerComputed (⟨796, by decide⟩ : Fin 1069) = lowerFacets (⟨796, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0797 : bundle_a018773121_lowerComputed (⟨797, by decide⟩ : Fin 1069) = lowerFacets (⟨797, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0798 : bundle_a018773121_lowerComputed (⟨798, by decide⟩ : Fin 1069) = lowerFacets (⟨798, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0799 : bundle_a018773121_lowerComputed (⟨799, by decide⟩ : Fin 1069) = lowerFacets (⟨799, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0800 : bundle_a018773121_lowerComputed (⟨800, by decide⟩ : Fin 1069) = lowerFacets (⟨800, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0801 : bundle_a018773121_lowerComputed (⟨801, by decide⟩ : Fin 1069) = lowerFacets (⟨801, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0802 : bundle_a018773121_lowerComputed (⟨802, by decide⟩ : Fin 1069) = lowerFacets (⟨802, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0803 : bundle_a018773121_lowerComputed (⟨803, by decide⟩ : Fin 1069) = lowerFacets (⟨803, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0804 : bundle_a018773121_lowerComputed (⟨804, by decide⟩ : Fin 1069) = lowerFacets (⟨804, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0805 : bundle_a018773121_lowerComputed (⟨805, by decide⟩ : Fin 1069) = lowerFacets (⟨805, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0806 : bundle_a018773121_lowerComputed (⟨806, by decide⟩ : Fin 1069) = lowerFacets (⟨806, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0807 : bundle_a018773121_lowerComputed (⟨807, by decide⟩ : Fin 1069) = lowerFacets (⟨807, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0808 : bundle_a018773121_lowerComputed (⟨808, by decide⟩ : Fin 1069) = lowerFacets (⟨808, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0809 : bundle_a018773121_lowerComputed (⟨809, by decide⟩ : Fin 1069) = lowerFacets (⟨809, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0810 : bundle_a018773121_lowerComputed (⟨810, by decide⟩ : Fin 1069) = lowerFacets (⟨810, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0811 : bundle_a018773121_lowerComputed (⟨811, by decide⟩ : Fin 1069) = lowerFacets (⟨811, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0812 : bundle_a018773121_lowerComputed (⟨812, by decide⟩ : Fin 1069) = lowerFacets (⟨812, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0813 : bundle_a018773121_lowerComputed (⟨813, by decide⟩ : Fin 1069) = lowerFacets (⟨813, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0814 : bundle_a018773121_lowerComputed (⟨814, by decide⟩ : Fin 1069) = lowerFacets (⟨814, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0815 : bundle_a018773121_lowerComputed (⟨815, by decide⟩ : Fin 1069) = lowerFacets (⟨815, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0816 : bundle_a018773121_lowerComputed (⟨816, by decide⟩ : Fin 1069) = lowerFacets (⟨816, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0817 : bundle_a018773121_lowerComputed (⟨817, by decide⟩ : Fin 1069) = lowerFacets (⟨817, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0818 : bundle_a018773121_lowerComputed (⟨818, by decide⟩ : Fin 1069) = lowerFacets (⟨818, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0819 : bundle_a018773121_lowerComputed (⟨819, by decide⟩ : Fin 1069) = lowerFacets (⟨819, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0820 : bundle_a018773121_lowerComputed (⟨820, by decide⟩ : Fin 1069) = lowerFacets (⟨820, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0821 : bundle_a018773121_lowerComputed (⟨821, by decide⟩ : Fin 1069) = lowerFacets (⟨821, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0822 : bundle_a018773121_lowerComputed (⟨822, by decide⟩ : Fin 1069) = lowerFacets (⟨822, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0823 : bundle_a018773121_lowerComputed (⟨823, by decide⟩ : Fin 1069) = lowerFacets (⟨823, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0824 : bundle_a018773121_lowerComputed (⟨824, by decide⟩ : Fin 1069) = lowerFacets (⟨824, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0825 : bundle_a018773121_lowerComputed (⟨825, by decide⟩ : Fin 1069) = lowerFacets (⟨825, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0826 : bundle_a018773121_lowerComputed (⟨826, by decide⟩ : Fin 1069) = lowerFacets (⟨826, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0827 : bundle_a018773121_lowerComputed (⟨827, by decide⟩ : Fin 1069) = lowerFacets (⟨827, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0828 : bundle_a018773121_lowerComputed (⟨828, by decide⟩ : Fin 1069) = lowerFacets (⟨828, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0829 : bundle_a018773121_lowerComputed (⟨829, by decide⟩ : Fin 1069) = lowerFacets (⟨829, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0830 : bundle_a018773121_lowerComputed (⟨830, by decide⟩ : Fin 1069) = lowerFacets (⟨830, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0831 : bundle_a018773121_lowerComputed (⟨831, by decide⟩ : Fin 1069) = lowerFacets (⟨831, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0832 : bundle_a018773121_lowerComputed (⟨832, by decide⟩ : Fin 1069) = lowerFacets (⟨832, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0833 : bundle_a018773121_lowerComputed (⟨833, by decide⟩ : Fin 1069) = lowerFacets (⟨833, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0834 : bundle_a018773121_lowerComputed (⟨834, by decide⟩ : Fin 1069) = lowerFacets (⟨834, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0835 : bundle_a018773121_lowerComputed (⟨835, by decide⟩ : Fin 1069) = lowerFacets (⟨835, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0836 : bundle_a018773121_lowerComputed (⟨836, by decide⟩ : Fin 1069) = lowerFacets (⟨836, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0837 : bundle_a018773121_lowerComputed (⟨837, by decide⟩ : Fin 1069) = lowerFacets (⟨837, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0838 : bundle_a018773121_lowerComputed (⟨838, by decide⟩ : Fin 1069) = lowerFacets (⟨838, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0839 : bundle_a018773121_lowerComputed (⟨839, by decide⟩ : Fin 1069) = lowerFacets (⟨839, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0840 : bundle_a018773121_lowerComputed (⟨840, by decide⟩ : Fin 1069) = lowerFacets (⟨840, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0841 : bundle_a018773121_lowerComputed (⟨841, by decide⟩ : Fin 1069) = lowerFacets (⟨841, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0842 : bundle_a018773121_lowerComputed (⟨842, by decide⟩ : Fin 1069) = lowerFacets (⟨842, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0843 : bundle_a018773121_lowerComputed (⟨843, by decide⟩ : Fin 1069) = lowerFacets (⟨843, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0844 : bundle_a018773121_lowerComputed (⟨844, by decide⟩ : Fin 1069) = lowerFacets (⟨844, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_a018773121_lower0845 : bundle_a018773121_lowerComputed (⟨845, by decide⟩ : Fin 1069) = lowerFacets (⟨845, by decide⟩ : Fin 1069) := by
  decide +kernel

end CubicalIndecomposability
end VerificationSource000

/- Original source: CubicalIndecomposability/FaceDataChecks/Supports.lean -/

end -- global noncomputable section
end -- global public section
