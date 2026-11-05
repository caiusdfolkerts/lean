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

/- Explicit witnesses for Boolean masks 160 through 191.
The first Boolean is vertex label 0; all ten coordinates are exhausted. -/

theorem coverage_mask_0160 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0161 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0162 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0163 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0164 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0165 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0166 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨7, by decide +kernel⟩)))

theorem coverage_mask_0167 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0168 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0169 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0170 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨7, by decide +kernel⟩)))

theorem coverage_mask_0171 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0172 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨14, by decide +kernel⟩)))

theorem coverage_mask_0173 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0174 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inl ⟨10, by decide +kernel⟩

theorem coverage_mask_0175 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0176 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0177 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0178 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨5, by decide +kernel⟩)))

theorem coverage_mask_0179 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0180 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨5, by decide +kernel⟩)))

theorem coverage_mask_0181 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0182 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨5, by decide +kernel⟩)))

theorem coverage_mask_0183 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0184 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨5, by decide +kernel⟩)))

theorem coverage_mask_0185 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0186 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨5, by decide +kernel⟩)))

theorem coverage_mask_0187 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0188 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨5, by decide +kernel⟩)))

theorem coverage_mask_0189 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0190 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨5, by decide +kernel⟩)))

theorem coverage_mask_0191 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_chunk_05 :
    ∀ tail : VertexMask 5, Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true tail))))) :=
  (forallMask_succ (n := 4) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true tail))))))
    (forallMask_succ (n := 3) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false tail)))))))
    (forallMask_succ (n := 2) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0160)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0161))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0162)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0163)))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0164)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0165))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0166)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0167))))
    (forallMask_succ (n := 2) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0168)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0169))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0170)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0171)))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0172)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0173))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0174)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0175)))))
    (forallMask_succ (n := 3) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true tail)))))))
    (forallMask_succ (n := 2) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0176)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0177))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0178)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0179)))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0180)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0181))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0182)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0183))))
    (forallMask_succ (n := 2) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0184)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0185))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0186)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0187)))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0188)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0189))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0190)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0191))))))

end Papers.RationalWitnesses.RawWitnesses.Typefourprism
