module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Exterior cochains and alternating multilinear cochains

For a finite free module, the determinant pairing identifies the exterior
power of its dual with the actual module of alternating multilinear forms.
The comparison below uses Mathlib's independently defined exterior powers,
alternating maps and perfect dual pairing.  Its evaluation formulas record
the normalization in every degree, including degree zero.
-/

@[expose] public section
noncomputable section

namespace PaperVerification.ExteriorAlternatingCochains

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Free R M] [Module.Finite R M]

/-- The determinant pairing followed by the universal property of the
exterior power, in the direction from exterior cochains to alternating forms. -/
def cochainEquiv (q : ℕ) :
    (⋀[R]^q (Module.Dual R M)) ≃ₗ[R] AlternatingMap R M R (Fin q) :=
  (LinearEquiv.ofBijective (exteriorPower.pairingDual R M q)
    (exteriorPower.bijective_pairingDual R M q)).trans
      exteriorPower.alternatingMapLinearEquiv.symm

/-- The comparison is the original exterior pairing on every tuple. -/
theorem cochainEquiv_apply (q : ℕ) (ω : ⋀[R]^q (Module.Dual R M))
    (v : Fin q → M) :
    cochainEquiv R M q ω v = exteriorPower.pairingDual R M q ω
      (exteriorPower.ιMulti R q v) := by
  change exteriorPower.alternatingMapLinearEquiv.symm
    (exteriorPower.pairingDual R M q ω) v = _
  exact exteriorPower.alternatingMapLinearEquiv_symm_apply _ _

/-- A wedge of one-cochains evaluates by the usual determinant, with no
factorial normalization or sign left implicit. -/
theorem cochainEquiv_wedge (q : ℕ) (α : Fin q → Module.Dual R M)
    (v : Fin q → M) :
    cochainEquiv R M q (exteriorPower.ιMulti R q α) v =
      Matrix.det (Matrix.of (fun i j ↦ α j (v i))) := by
  rw [cochainEquiv_apply, exteriorPower.pairingDual_ιMulti_ιMulti]

/-- Every alternating cochain comes from exactly one exterior cochain. -/
theorem existsUnique_exterior_cochain (q : ℕ) (F : AlternatingMap R M R (Fin q)) :
    ∃! ω : ⋀[R]^q (Module.Dual R M),
      ∀ v, exteriorPower.pairingDual R M q ω (exteriorPower.ιMulti R q v) = F v := by
  refine ⟨(cochainEquiv R M q).symm F, ?_, ?_⟩
  · intro v
    rw [← cochainEquiv_apply, LinearEquiv.apply_symm_apply]
  · intro ω hω
    apply (cochainEquiv R M q).injective
    ext v
    rw [cochainEquiv_apply, hω]
    exact congrArg (fun F : AlternatingMap R M R (Fin q) ↦ F v)
      ((cochainEquiv R M q).apply_symm_apply F).symm

/-- Equality of exterior cochains can be checked on actual tuples of vectors. -/
theorem cochain_ext (q : ℕ) (ω η : ⋀[R]^q (Module.Dual R M))
    (h : ∀ v, exteriorPower.pairingDual R M q ω (exteriorPower.ιMulti R q v) =
      exteriorPower.pairingDual R M q η (exteriorPower.ιMulti R q v)) : ω = η := by
  apply (cochainEquiv R M q).injective
  ext v
  simpa only [cochainEquiv_apply] using h v

end PaperVerification.ExteriorAlternatingCochains
