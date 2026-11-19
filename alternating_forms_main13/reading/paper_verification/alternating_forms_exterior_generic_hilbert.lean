module

public import PaperVerification.AlternatingFormsOrbitExterior
public import PaperVerification.AlternatingFormsOrbitGenericity
public import PaperVerification.AlternatingFormsExteriorTransport
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Dimension.Free
import Lean.Elab.Tactic.Omega

/-!
# One principal open certificate for the complete exterior Hilbert function

The relation matrices used here are matrices of the actual wedge maps.
Their ranges are identified with the degree pieces of the actual generated
ideal.  The finite collection of rank certificates is then combined into a
single polynomial.  Degrees zero and one and degrees above the ambient
dimension are included explicitly, so the conclusion quantifies over every
natural degree.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial Module
open scoped BigOperators Classical

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
  [FiniteDimensional K M]

theorem exteriorDegreeRelations_eq_orbitRange (f g : ⋀[K]^2 M) (q : ℕ) :
    exteriorDegreeRelations f g (2 + q) = (orbitExteriorRelationMap f g q).range := by
  rw [exteriorDegreeRelations_eq_images, orbitExteriorRelationMap, LinearMap.range_coprod]

theorem exteriorQuotientDegree_finrank_add_orbitRange (f g : ⋀[K]^2 M) (q : ℕ) :
    Module.finrank K (ExteriorQuotientDegree f g (2 + q)) +
      Module.finrank K (orbitExteriorRelationMap f g q).range =
        Module.finrank K (⋀[K]^(2 + q) M) := by
  have he := (Submodule.quotEquivOfEq
    (exteriorDegreeRelations f g (2+q)) (orbitExteriorRelationMap f g q).range
    (exteriorDegreeRelations_eq_orbitRange f g q)).finrank_eq
  change Module.finrank K (ExteriorQuotientDegree f g (2+q)) = _ at he
  rw [he]
  exact Submodule.finrank_quotient_add_finrank (orbitExteriorRelationMap f g q).range

theorem exteriorQuotientDegree_finrank_eq_iff_orbitRange_finrank_eq
    (f g f' g' : ⋀[K]^2 M) (q : ℕ) :
    Module.finrank K (ExteriorQuotientDegree f g (2 + q)) =
        Module.finrank K (ExteriorQuotientDegree f' g' (2 + q)) ↔
      Module.finrank K (orbitExteriorRelationMap f g q).range =
        Module.finrank K (orbitExteriorRelationMap f' g' q).range := by
  have h := exteriorQuotientDegree_finrank_add_orbitRange f g q
  have h' := exteriorQuotientDegree_finrank_add_orbitRange f' g' q
  omega

theorem exteriorQuotientDegree_finrank_eq_low (f g f' g' : ⋀[K]^2 M)
    (d : ℕ) (hd : d < 2) :
    Module.finrank K (ExteriorQuotientDegree f g d) =
      Module.finrank K (ExteriorQuotientDegree f' g' d) := by
  exact ((exteriorDegreeRelations f g d).quotEquivOfEqBot
    (exteriorDegreeRelations_eq_bot f g hd)).finrank_eq.trans
      ((exteriorDegreeRelations f' g' d).quotEquivOfEqBot
        (exteriorDegreeRelations_eq_bot f' g' hd)).finrank_eq.symm

theorem exteriorQuotientDegree_finrank_eq_zero_high (f g : ⋀[K]^2 M)
    (d : ℕ) (hd : Module.finrank K M < d) :
    Module.finrank K (ExteriorQuotientDegree f g d) = 0 := by
  have h := Submodule.finrank_quotient_add_finrank (exteriorDegreeRelations f g d)
  rw [exteriorPower.finrank_eq, Nat.choose_eq_zero_of_lt hd] at h
  change Module.finrank K (ExteriorQuotientDegree f g d) + _ = 0 at h
  omega

section Certificates

variable {I σ : Type*} [Fintype I] [Fintype σ] [Infinite K]
    (b₂ : Basis I K (⋀[K]^2 M))

/-- A constant complete Hilbert function on a nonempty principal part of a
dominant polynomial parametrization gives one nonempty principal open in the
full coefficient space with that same complete Hilbert function. -/
theorem exteriorHilbert_principal_certificate_of_dominant
    (p : (I ⊕ I) → MvPolynomial σ K) (v : σ → K)
    (hJ : (TauCeti.jacobiMatrixAt p v).mulVec.Surjective)
    (g : MvPolynomial σ K) (hg : g ≠ 0) (base : (I ⊕ I) → K)
    (hparam : ∀ x : σ → K, eval x g ≠ 0 → ∀ d : ℕ,
      Module.finrank K (ExteriorQuotientDegree
        (orbitFormsFromCoordinates b₂ (fun i => eval x (p i))).1
        (orbitFormsFromCoordinates b₂ (fun i => eval x (p i))).2 d) =
      Module.finrank K (ExteriorQuotientDegree
        (orbitFormsFromCoordinates b₂ base).1 (orbitFormsFromCoordinates b₂ base).2 d)) :
    ∃ Q : MvPolynomial (I ⊕ I) K, eval base Q ≠ 0 ∧
      ∀ y : (I ⊕ I) → K, eval y Q ≠ 0 → ∀ d : ℕ,
        Module.finrank K (ExteriorQuotientDegree
          (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 d) =
        Module.finrank K (ExteriorQuotientDegree
          (orbitFormsFromCoordinates b₂ base).1 (orbitFormsFromCoordinates b₂ base).2 d) := by
  let n := Module.finrank K M
  let P (d : Fin (n + 1)) (y : (I ⊕ I) → K) : Prop :=
    Module.finrank K (ExteriorQuotientDegree
      (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 (2 + d.val)) =
    Module.finrank K (ExteriorQuotientDegree
      (orbitFormsFromCoordinates b₂ base).1 (orbitFormsFromCoordinates b₂ base).2 (2 + d.val))
  have hdegree (d : Fin (n + 1)) :
      ∃ Q : MvPolynomial (I ⊕ I) K, eval base Q ≠ 0 ∧
        ∀ y : (I ⊕ I) → K, eval y Q ≠ 0 → P d y := by
    let A := orbitRelationPolynomialMatrix d.val b₂
      (Module.finBasis K (⋀[K]^d.val M)) (Module.finBasis K (⋀[K]^(2 + d.val) M))
    have hrank (x : σ → K) (hx : eval x g ≠ 0) :
        (A.map (eval (fun i => eval x (p i)))).rank = (A.map (eval base)).rank := by
      simp only [A, orbitRelationPolynomialMatrix_eval, LinearMap.rank_toMatrix]
      exact (exteriorQuotientDegree_finrank_eq_iff_orbitRange_finrank_eq _ _ _ _ d.val).mp
        (hparam x hx (2 + d.val))
    obtain ⟨Q, hbase, hQ⟩ :=
      polynomialMatrix_generic_rank_from_orbit A hJ hg base hrank
    refine ⟨Q, hbase, ?_⟩
    intro y hy
    apply (exteriorQuotientDegree_finrank_eq_iff_orbitRange_finrank_eq _ _ _ _ d.val).mpr
    have h := hQ y hy
    simpa only [A, orbitRelationPolynomialMatrix_eval, LinearMap.rank_toMatrix] using h
  obtain ⟨Q, hbase, hQ⟩ := exists_simultaneous_principal_certificate base P hdegree
  refine ⟨Q, hbase, ?_⟩
  intro y hy d
  by_cases hlow : d < 2
  · exact exteriorQuotientDegree_finrank_eq_low _ _ _ _ d hlow
  · by_cases hhigh : n < d
    · rw [exteriorQuotientDegree_finrank_eq_zero_high _ _ d hhigh,
        exteriorQuotientDegree_finrank_eq_zero_high _ _ d hhigh]
    · let i : Fin (n + 1) := ⟨d - 2, by omega⟩
      have h := hQ y hy i
      change Module.finrank K (ExteriorQuotientDegree
        (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 (2 + (d - 2))) =
        Module.finrank K (ExteriorQuotientDegree
          (orbitFormsFromCoordinates b₂ base).1 (orbitFormsFromCoordinates b₂ base).2
            (2 + (d - 2))) at h
      have hd : 2 + (d - 2) = d := by omega
      exact (congrArg (fun r => Module.finrank K (ExteriorQuotientDegree
        (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 r)) hd).symm.trans
          (h.trans (congrArg (fun r => Module.finrank K (ExteriorQuotientDegree
            (orbitFormsFromCoordinates b₂ base).1 (orbitFormsFromCoordinates b₂ base).2 r)) hd))

/-- In the single-orbit case, actual exterior transport supplies the Hilbert
function hypothesis in the preceding theorem.  An invertible change of the
two generators is allowed through equality of their quadratic spans. -/
theorem exteriorHilbert_principal_certificate_of_dominant_orbit
    (p : (I ⊕ I) → MvPolynomial σ K) (v : σ → K)
    (hJ : (TauCeti.jacobiMatrixAt p v).mulVec.Surjective)
    (g : MvPolynomial σ K) (hg : g ≠ 0) (base : (I ⊕ I) → K)
    (horbit : ∀ x : σ → K, eval x g ≠ 0 → ∃ e : M ≃ₗ[K] M,
      Submodule.span K
        ({exteriorPower.map 2 e.toLinearMap (orbitFormsFromCoordinates b₂ base).1,
          exteriorPower.map 2 e.toLinearMap (orbitFormsFromCoordinates b₂ base).2} :
            Set (⋀[K]^2 M)) =
      Submodule.span K
        ({(orbitFormsFromCoordinates b₂ (fun i => eval x (p i))).1,
          (orbitFormsFromCoordinates b₂ (fun i => eval x (p i))).2} : Set (⋀[K]^2 M))) :
    ∃ Q : MvPolynomial (I ⊕ I) K, eval base Q ≠ 0 ∧
      ∀ y : (I ⊕ I) → K, eval y Q ≠ 0 → ∀ d : ℕ,
        Module.finrank K (ExteriorQuotientDegree
          (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 d) =
        Module.finrank K (ExteriorQuotientDegree
          (orbitFormsFromCoordinates b₂ base).1 (orbitFormsFromCoordinates b₂ base).2 d) := by
  apply exteriorHilbert_principal_certificate_of_dominant b₂ p v hJ g hg base
  intro x hx d
  obtain ⟨e, he⟩ := horbit x hx
  exact (exteriorQuotientDegree_finrank_eq_of_pencilEquiv e _ _ _ _ he d).symm

end Certificates

end PaperVerification.AlternatingForms
