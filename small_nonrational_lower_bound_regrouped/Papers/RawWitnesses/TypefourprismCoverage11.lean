module
prelude
public import Papers.RawWitnesses.TypefourprismData
public import Papers.IntegerFacetRawCoverage

/-! Small ordinary kernel checks for Appendix B type four_prism. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.Typefourprism
open Papers.RationalWitnesses.Raw

/- Explicit witnesses for Boolean masks 352 through 383.
The first Boolean is vertex label 0; all ten coordinates are exhausted. -/

theorem coverage_mask_0352 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0353 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0354 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨7, by decide +kernel⟩)))

theorem coverage_mask_0355 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0356 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨3, by decide +kernel⟩)))

theorem coverage_mask_0357 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0358 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨3, by decide +kernel⟩)))

theorem coverage_mask_0359 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0360 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨13, by decide +kernel⟩)))

theorem coverage_mask_0361 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0362 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨7, by decide +kernel⟩)))

theorem coverage_mask_0363 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0364 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨3, by decide +kernel⟩)))

theorem coverage_mask_0365 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0366 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨3, by decide +kernel⟩)))

theorem coverage_mask_0367 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0368 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨4, by decide +kernel⟩)))

theorem coverage_mask_0369 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0370 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨4, by decide +kernel⟩)))

theorem coverage_mask_0371 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0372 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨3, by decide +kernel⟩)))

theorem coverage_mask_0373 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0374 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨4, by decide +kernel⟩)))

theorem coverage_mask_0375 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0376 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨4, by decide +kernel⟩)))

theorem coverage_mask_0377 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0378 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨4, by decide +kernel⟩)))

theorem coverage_mask_0379 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0380 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨3, by decide +kernel⟩)))

theorem coverage_mask_0381 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0382 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨4, by decide +kernel⟩)))

theorem coverage_mask_0383 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_chunk_11 :
    ∀ tail : VertexMask 5, Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true tail))))) :=
  (forallMask_succ (n := 4) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true tail))))))
    (forallMask_succ (n := 3) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false tail)))))))
    (forallMask_succ (n := 2) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0352)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0353))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0354)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0355)))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0356)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0357))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0358)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0359))))
    (forallMask_succ (n := 2) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0360)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0361))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0362)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0363)))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0364)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0365))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0366)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0367)))))
    (forallMask_succ (n := 3) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true tail)))))))
    (forallMask_succ (n := 2) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0368)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0369))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0370)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0371)))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0372)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0373))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0374)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0375))))
    (forallMask_succ (n := 2) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0376)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0377))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0378)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0379)))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0380)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0381))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0382)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0383))))))

end Papers.RationalWitnesses.RawWitnesses.Typefourprism
