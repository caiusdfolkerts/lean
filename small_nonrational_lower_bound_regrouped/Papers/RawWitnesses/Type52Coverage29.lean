module
prelude
public import Papers.RawWitnesses.Type52Data
public import Papers.IntegerFacetRawCoverage

/-! Small ordinary kernel checks for Appendix B type 52. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.Type52
open Papers.RationalWitnesses.Raw

/- Explicit witnesses for Boolean masks 928 through 959.
The first Boolean is vertex label 0; all ten coordinates are exhausted. -/

theorem coverage_mask_0928 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨8, by decide +kernel⟩)))

theorem coverage_mask_0929 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨3, by decide +kernel⟩)))

theorem coverage_mask_0930 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨0, by decide +kernel⟩)))

theorem coverage_mask_0931 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨0, by decide +kernel⟩)))

theorem coverage_mask_0932 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0933 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0934 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨0, by decide +kernel⟩)))

theorem coverage_mask_0935 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨0, by decide +kernel⟩)))

theorem coverage_mask_0936 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨8, by decide +kernel⟩)))

theorem coverage_mask_0937 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨3, by decide +kernel⟩)))

theorem coverage_mask_0938 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨0, by decide +kernel⟩)))

theorem coverage_mask_0939 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨0, by decide +kernel⟩)))

theorem coverage_mask_0940 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0941 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0942 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨0, by decide +kernel⟩)))

theorem coverage_mask_0943 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨0, by decide +kernel⟩)))

theorem coverage_mask_0944 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨8, by decide +kernel⟩)))

theorem coverage_mask_0945 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨3, by decide +kernel⟩)))

theorem coverage_mask_0946 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨0, by decide +kernel⟩)))

theorem coverage_mask_0947 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨0, by decide +kernel⟩)))

theorem coverage_mask_0948 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0949 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨2, by decide +kernel⟩)))

theorem coverage_mask_0950 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨0, by decide +kernel⟩)))

theorem coverage_mask_0951 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨0, by decide +kernel⟩)))

theorem coverage_mask_0952 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨1, by decide +kernel⟩)))

theorem coverage_mask_0953 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨1, by decide +kernel⟩)))

theorem coverage_mask_0954 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨0, by decide +kernel⟩)))

theorem coverage_mask_0955 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨0, by decide +kernel⟩)))

theorem coverage_mask_0956 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨1, by decide +kernel⟩)))

theorem coverage_mask_0957 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨1, by decide +kernel⟩)))

theorem coverage_mask_0958 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨0, by decide +kernel⟩)))

theorem coverage_mask_0959 :
    Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (fun i => Fin.elim0 i))))))))))) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨0, by decide +kernel⟩)))

theorem coverage_chunk_29 :
    ∀ tail : VertexMask 5, Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true tail))))) :=
  (forallMask_succ (n := 4) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true tail))))))
    (forallMask_succ (n := 3) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false tail)))))))
    (forallMask_succ (n := 2) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0928)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0929))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0930)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0931)))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0932)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0933))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0934)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0935))))
    (forallMask_succ (n := 2) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0936)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0937))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0938)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0939)))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0940)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0941))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0942)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0943)))))
    (forallMask_succ (n := 3) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true tail)))))))
    (forallMask_succ (n := 2) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0944)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0945))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0946)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0947)))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0948)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0949))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0950)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0951))))
    (forallMask_succ (n := 2) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0952)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0953))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0954)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0955)))
    (forallMask_succ (n := 1) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true tail)))))))))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases false tail))))))))))) coverage_mask_0956)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true tail))))))))))) coverage_mask_0957))
    (forallMask_succ (n := 0) (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false tail))))))))))) coverage_mask_0958)
    (forallMask_zero (fun tail => Covered certificate (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases false (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true (Fin.cases true tail))))))))))) coverage_mask_0959))))))

end Papers.RationalWitnesses.RawWitnesses.Type52
