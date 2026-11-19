module
prelude
public import Papers.RawWitnesses.Type53Data
public import Papers.IntegerFacetRawCoverage

/-! Small ordinary kernel checks for Appendix B type 53. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.Type53
open Papers.RationalWitnesses.Raw

/- Explicit witnesses for Boolean masks 800 through 831.
The first Boolean is vertex label 0; all ten coordinates are exhausted. -/

theorem coverage_mask_0800 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inl (by decide +kernel))

theorem coverage_mask_0801 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0802 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0803 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0804 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0805 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0806 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0807 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0808 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0809 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0810 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0811 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0812 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0813 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0814 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0815 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0816 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨0, by decide +kernel⟩)))

theorem coverage_mask_0817 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨1, by decide +kernel⟩)))

theorem coverage_mask_0818 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨1, by decide +kernel⟩)))

theorem coverage_mask_0819 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨1, by decide +kernel⟩)))

theorem coverage_mask_0820 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨1, by decide +kernel⟩)))

theorem coverage_mask_0821 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨1, by decide +kernel⟩)))

theorem coverage_mask_0822 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨1, by decide +kernel⟩)))

theorem coverage_mask_0823 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨1, by decide +kernel⟩)))

theorem coverage_mask_0824 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨1, by decide +kernel⟩)))

theorem coverage_mask_0825 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨1, by decide +kernel⟩)))

theorem coverage_mask_0826 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨1, by decide +kernel⟩)))

theorem coverage_mask_0827 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨1, by decide +kernel⟩)))

theorem coverage_mask_0828 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨1, by decide +kernel⟩)))

theorem coverage_mask_0829 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨1, by decide +kernel⟩)))

theorem coverage_mask_0830 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨1, by decide +kernel⟩)))

theorem coverage_mask_0831 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨1, by decide +kernel⟩)))

theorem coverage_chunk_25 :
    ∀ tail : VertexMask 5, Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true tail))))) :=
  (forallMask_succ (n := 4) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true tail))))))
    (forallMask_succ (n := 3) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false tail)))))))
    (forallMask_succ (n := 2) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0800)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0801))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0802)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0803)))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0804)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0805))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0806)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0807))))
    (forallMask_succ (n := 2) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0808)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0809))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0810)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0811)))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0812)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0813))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0814)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0815)))))
    (forallMask_succ (n := 3) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true tail)))))))
    (forallMask_succ (n := 2) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0816)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0817))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0818)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0819)))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0820)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0821))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0822)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0823))))
    (forallMask_succ (n := 2) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0824)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0825))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0826)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0827)))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0828)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0829))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0830)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0831))))))

end Papers.RationalWitnesses.RawWitnesses.Type53
