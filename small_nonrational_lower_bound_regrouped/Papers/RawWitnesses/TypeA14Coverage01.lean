module
prelude
public import Papers.RawWitnesses.TypeA14Data
public import Papers.IntegerFacetRawCoverage

/-! Small ordinary kernel checks for Appendix B type A14. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.TypeA14
open Papers.RationalWitnesses.Raw

/- Explicit witnesses for Boolean masks 32 through 63.
The first Boolean is vertex label 0; all ten coordinates are exhausted. -/

theorem coverage_mask_0032 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0033 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0034 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0035 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0036 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0037 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0038 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0039 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨7, by decide +kernel⟩)))

theorem coverage_mask_0040 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0041 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0042 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0043 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0044 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0045 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0046 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0047 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0048 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0049 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0050 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0051 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨16, by decide +kernel⟩)))

theorem coverage_mask_0052 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0053 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨11, by decide +kernel⟩)))

theorem coverage_mask_0054 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨18, by decide +kernel⟩)))

theorem coverage_mask_0055 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨7, by decide +kernel⟩)))

theorem coverage_mask_0056 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0057 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0058 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0059 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0060 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0061 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0062 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0063 :
    Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_chunk_01 :
    ∀ tail : VertexMask 5, Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true tail))))) :=
  (forallMask_succ (n := 4) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true tail))))))
    (forallMask_succ (n := 3) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false tail)))))))
    (forallMask_succ (n := 2) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0032)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0033))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0034)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0035)))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0036)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0037))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0038)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0039))))
    (forallMask_succ (n := 2) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0040)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0041))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0042)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0043)))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0044)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0045))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0046)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0047)))))
    (forallMask_succ (n := 3) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true tail)))))))
    (forallMask_succ (n := 2) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0048)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0049))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0050)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0051)))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0052)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0053))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0054)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0055))))
    (forallMask_succ (n := 2) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0056)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0057))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0058)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0059)))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0060)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0061))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0062)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0063))))))

end Papers.RationalWitnesses.RawWitnesses.TypeA14
