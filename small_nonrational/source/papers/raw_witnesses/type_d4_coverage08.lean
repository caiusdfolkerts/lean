module
prelude
public import Papers.RawWitnesses.TypeD4Data
public import Papers.IntegerFacetRawCoverage

/-! Small ordinary kernel checks for Appendix B type D4. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.TypeD4
open Papers.RationalWitnesses.Raw

/- Explicit witnesses for Boolean masks 256 through 287.
The first Boolean is vertex label 0; all ten coordinates are exhausted. -/

theorem coverage_mask_0256 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0257 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0258 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0259 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0260 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0261 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0262 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0263 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨16, by decide +kernel⟩)))

theorem coverage_mask_0264 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0265 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0266 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0267 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨1, by decide +kernel⟩)))

theorem coverage_mask_0268 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0269 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨1, by decide +kernel⟩)))

theorem coverage_mask_0270 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨21, by decide +kernel⟩)))

theorem coverage_mask_0271 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨1, by decide +kernel⟩)))

theorem coverage_mask_0272 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0273 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0274 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0275 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨16, by decide +kernel⟩)))

theorem coverage_mask_0276 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0277 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨16, by decide +kernel⟩)))

theorem coverage_mask_0278 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨20, by decide +kernel⟩)))

theorem coverage_mask_0279 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inl ⟨10, by decide +kernel⟩

theorem coverage_mask_0280 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0281 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨1, by decide +kernel⟩)))

theorem coverage_mask_0282 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨14, by decide +kernel⟩)))

theorem coverage_mask_0283 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨1, by decide +kernel⟩)))

theorem coverage_mask_0284 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨21, by decide +kernel⟩)))

theorem coverage_mask_0285 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨1, by decide +kernel⟩)))

theorem coverage_mask_0286 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨14, by decide +kernel⟩)))

theorem coverage_mask_0287 :
    Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨1, by decide +kernel⟩)))

theorem coverage_chunk_08 :
    ∀ tail : VertexMask 5, Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false tail))))) :=
  (forallMask_succ (n := 4) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false tail))))))
    (forallMask_succ (n := 3) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false tail)))))))
    (forallMask_succ (n := 2) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0256)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0257))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0258)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0259)))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0260)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0261))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0262)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0263))))
    (forallMask_succ (n := 2) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0264)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0265))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0266)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0267)))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0268)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0269))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0270)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0271)))))
    (forallMask_succ (n := 3) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true tail)))))))
    (forallMask_succ (n := 2) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0272)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0273))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0274)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0275)))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0276)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0277))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0278)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0279))))
    (forallMask_succ (n := 2) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0280)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0281))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0282)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0283)))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0284)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0285))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0286)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0287))))))

end Papers.RationalWitnesses.RawWitnesses.TypeD4
