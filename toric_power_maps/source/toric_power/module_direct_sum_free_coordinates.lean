module

public import ToricPower.ModuleDirectSumColimit
public import Mathlib.Data.Finsupp.ToDFinsupp

/-!
# Shared literal basis coordinates of unrestricted sums of complexes

A specified free basis in every coefficient complex gives the actual
sigma-indexed basis of their unrestricted direct sum. The canonical
complex inclusions and differential have their exact coordinate formulas.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.ModuleDirectSum

variable (R : Type) [CommRing R] {U : Type}
  (K : U → CochainComplex (ModuleCat.{0} R) ℕ)
  (I : U → ℕ → Type)
  (e : ∀ u q, (K u).X q ≃ₗ[R] (I u q →₀ R))

/-- Actual sigma-basis coordinates of the full direct-sum complex. -/
def complexCoordinates (q : ℕ) :
    (complex R K).X q ≃ₗ[R] ((Σ u : U, I u q) →₀ R) :=
  (DFinsupp.mapRange.linearEquiv (fun u : U => e u q)).trans
    (sigmaFinsuppLequivDFinsupp R).symm

@[simp]
theorem complexCoordinates_apply (q : ℕ) (v : Π₀ u : U, ↑((K u).X q))
    (u : U) (i : I u q) :
    complexCoordinates R K I e q v ⟨u, i⟩ = e u q (v u) i := rfl

/-- A sigma-basis vector is the canonical inclusion of the actual
basis vector in its coefficient complex. -/
theorem complexCoordinates_inclusion_generator (q : ℕ) (u : U) (i : I u q) (r : R) :
    complexCoordinates R K I e q
      ((complexInclusion R K u).f q ((e u q).symm (Finsupp.single i r))) =
      Finsupp.single ⟨u, i⟩ r := by
  apply (sigmaFinsuppLequivDFinsupp R).injective
  change (sigmaFinsuppLequivDFinsupp R)
      ((sigmaFinsuppLequivDFinsupp R).symm
        (DFinsupp.mapRange (fun v : U => e v q) (fun v => map_zero (e v q))
          (DFinsupp.single u ((e u q).symm (Finsupp.single i r))))) = _
  rw [LinearEquiv.apply_symm_apply, DFinsupp.mapRange_single,
    LinearEquiv.apply_symm_apply]
  exact (sigmaFinsuppEquivDFinsupp_single (⟨u, i⟩ : Σ v : U, I v q) r).symm

/-- The inverse coordinates recover the genuine complex inclusion. -/
theorem complexCoordinates_symm_single (q : ℕ) (u : U) (i : I u q) (r : R) :
    (complexCoordinates R K I e q).symm (Finsupp.single ⟨u, i⟩ r) =
      (complexInclusion R K u).f q ((e u q).symm (Finsupp.single i r)) := by
  apply (complexCoordinates R K I e q).injective
  rw [LinearEquiv.apply_symm_apply, complexCoordinates_inclusion_generator]

/-- The same canonical inclusion in literal dependent-finitely-supported coordinates. -/
theorem complexCoordinates_symm_single_dfinsupp (q : ℕ) (u : U) (i : I u q) (r : R) :
    (complexCoordinates R K I e q).symm (Finsupp.single ⟨u, i⟩ r) =
      DFinsupp.single u ((e u q).symm (Finsupp.single i r)) := by
  change (DFinsupp.mapRange.linearEquiv (fun v => e v q)).symm
      (sigmaFinsuppEquivDFinsupp (Finsupp.single ⟨u,i⟩ r)) = _
  rw [sigmaFinsuppEquivDFinsupp_single,DFinsupp.mapRange.linearEquiv_symm]
  simp only [DFinsupp.mapRange.linearEquiv_apply,DFinsupp.mapRange_single]

end ToricPower.ModuleDirectSum
