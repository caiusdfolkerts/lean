module

public import ToricPower.ModuleDirectSumFreeCoordinates

/-!
# Literal basis coordinates of unrestricted sums of complexes

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

/-- The actual differential stays in the original summand. -/
theorem complex_d_inclusion (q t : ℕ) (u : U) (v : (K u).X q) :
    (complex R K).d q t ((complexInclusion R K u).f q v) =
      (complexInclusion R K u).f t ((K u).d q t v) := by
  exact ConcreteCategory.congr_hom ((complexInclusion R K u).comm q t) v

/-- Its coefficient in the same summand is the original differential. -/
theorem complexCoordinates_d_generator_same (q t : ℕ) (u : U)
    (i : I u q) (j : I u t) (r : R) :
    complexCoordinates R K I e t
      ((complex R K).d q t
        ((complexCoordinates R K I e q).symm (Finsupp.single ⟨u, i⟩ r))) ⟨u, j⟩ =
      e u t ((K u).d q t ((e u q).symm (Finsupp.single i r))) j := by
  rw [complexCoordinates_symm_single, complex_d_inclusion, complexCoordinates_apply]
  change e u t ((DFinsupp.single (β := fun v : U => ↑((K v).X t)) u ((K u).d q t
    ((e u q).symm (Finsupp.single i r)))) u) j = _
  rw [DFinsupp.single_eq_same]

/-- There is no differential coefficient in any other summand. -/
theorem complexCoordinates_d_generator_ne (q t : ℕ) (u v : U) (different : u ≠ v)
    (i : I u q) (j : I v t) (r : R) :
    complexCoordinates R K I e t
      ((complex R K).d q t
        ((complexCoordinates R K I e q).symm (Finsupp.single ⟨u, i⟩ r))) ⟨v, j⟩ = 0 := by
  rw [complexCoordinates_symm_single, complex_d_inclusion, complexCoordinates_apply]
  change e v t ((DFinsupp.single (β := fun w : U => ↑((K w).X t)) u ((K u).d q t
    ((e u q).symm (Finsupp.single i r)))) v) j = 0
  rw [DFinsupp.single_eq_of_ne different.symm, map_zero, Finsupp.zero_apply]

end ToricPower.ModuleDirectSum
