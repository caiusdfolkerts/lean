import cubical.generic_vertex_splitting
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Basis.Bilinear

/-!
# Complete graphs as rigidity bases

A complete graph on `d` orthonormal basis vectors is infinitesimally rigid
in dimension `d`. A complete graph on these vectors and the origin is
also rigid. Both statements use the full Euclidean-motion definition.
-/

namespace Cubical.Rigidity

open Module
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Skew-adjointness can be checked on a basis. -/
theorem isSkew_of_basis {ι : Type*} (b : Module.Basis ι ℝ E) (A : E →ₗ[ℝ] E)
    (h : ∀ i j, ⟪A (b i), b j⟫_ℝ = -⟪b i, A (b j)⟫_ℝ) : IsSkew A := by
  let B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ := (innerₛₗ ℝ).comp A
  let C : E →ₗ[ℝ] E →ₗ[ℝ] ℝ := -(innerₛₗ ℝ).compl₂ A
  have he : B = C := LinearMap.ext_basis b b h
  intro x y
  exact congrArg (fun f : E →ₗ[ℝ] E →ₗ[ℝ] ℝ => f x y) he

/-- The complete graph on an orthonormal basis is infinitesimally rigid,
including its translation component normal to the basis simplex. -/
theorem isRigid_complete_basis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) : IsRigid (⊤ : SimpleGraph ι) b := by
  intro u hu
  let t : E := b.repr.symm (WithLp.toLp 2 (fun i => ⟪b i, u i⟫_ℝ))
  have ht : ∀ i, ⟪b i, t⟫_ℝ = ⟪b i, u i⟫_ℝ := by
    intro i
    rw [← b.repr_apply_apply]
    simp [t]
  let r : ι → E := fun i => u i - t
  have hdiag : ∀ i, ⟪b i, r i⟫_ℝ = 0 := by
    intro i
    simp only [r, inner_sub_right, ht, sub_self]
  let A : E →ₗ[ℝ] E := b.toBasis.constr ℝ r
  have hAb : ∀ i, A (b i) = r i := fun i => b.toBasis.constr_basis ℝ r i
  have hskew : IsSkew A := by
    apply isSkew_of_basis b.toBasis A
    intro i j
    change ⟪A (b i), b j⟫_ℝ = -⟪b i, A (b j)⟫_ℝ
    rw [hAb, hAb]
    have hdist : ⟪b i - b j, r i - r j⟫_ℝ = 0 := by
      have hr : r i - r j = u i - u j := by dsimp [r]; abel
      rw [hr]
      by_cases hij : i = j
      · simp [hij]
      · exact hu i j hij
    simp only [inner_sub_left, inner_sub_right, hdiag] at hdist
    have hcomm := real_inner_comm (r i) (b j)
    linarith
  refine ⟨t, A, hskew, ?_⟩
  intro i
  rw [hAb]
  dsimp [r]
  abel

/-- The placement obtained by adjoining the origin to a basis. -/
def basisWithOrigin {ι : Type*} (b : ι → E) : Option ι → E
  | none => 0
  | some i => b i

/-- The complete graph on a basis and the origin is infinitesimally rigid. -/
theorem isRigid_complete_basisWithOrigin {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ E) :
    IsRigid (⊤ : SimpleGraph (Option ι)) (basisWithOrigin b) := by
  intro u hu
  let t := u none
  let r : ι → E := fun i => u (some i) - t
  have hdiag : ∀ i, ⟪b i, r i⟫_ℝ = 0 := by
    intro i
    have h := hu (some i) none (Option.some_ne_none i)
    simpa only [basisWithOrigin, sub_zero] using h
  let A : E →ₗ[ℝ] E := b.constr ℝ r
  have hAb : ∀ i, A (b i) = r i := fun i => b.constr_basis ℝ r i
  have hskew : IsSkew A := by
    apply isSkew_of_basis b A
    intro i j
    rw [hAb, hAb]
    have hdist : ⟪b i - b j, r i - r j⟫_ℝ = 0 := by
      have hr : r i - r j = u (some i) - u (some j) := by dsimp [r]; abel
      rw [hr]
      by_cases hij : i = j
      · simp [hij]
      · exact hu (some i) (some j) (by simpa using hij)
    simp only [inner_sub_left, inner_sub_right, hdiag] at hdist
    have hcomm := real_inner_comm (r i) (b j)
    linarith
  refine ⟨t, A, hskew, ?_⟩
  intro i
  cases i with
  | none => simp [basisWithOrigin, t]
  | some i =>
    simp only [basisWithOrigin, hAb]
    dsimp [r]
    abel

/-- A complete graph with as many vertices as the ambient dimension is
generically rigid. -/
theorem genericallyRigid_complete_of_card_eq_dim {V : Type*} [Fintype V]
    [FiniteDimensional ℝ E] (hcard : Fintype.card V = finrank ℝ E) :
    GenericallyRigid (⊤ : SimpleGraph V) E := by
  let e : V ≃ Fin (finrank ℝ E) := Fintype.equivOfCardEq (by simpa using hcard)
  have hG : GenericallyRigid (⊤ : SimpleGraph (Fin (finrank ℝ E))) E :=
    ⟨stdOrthonormalBasis ℝ E, isRigid_complete_basis _⟩
  have h := (genericallyRigid_comap_iff _ e).mpr hG
  have he : (⊤ : SimpleGraph (Fin (finrank ℝ E))).comap e = ⊤ := by
    ext a b
    simp [e.injective.ne_iff]
  rwa [he] at h

/-- A complete graph with `dim E + 1` vertices is generically rigid. -/
theorem genericallyRigid_complete_of_card_eq_dim_add_one {V : Type*} [Fintype V]
    [FiniteDimensional ℝ E] (hcard : Fintype.card V = finrank ℝ E + 1) :
    GenericallyRigid (⊤ : SimpleGraph V) E := by
  let e : V ≃ Option (Fin (finrank ℝ E)) := Fintype.equivOfCardEq (by simpa using hcard)
  have hG : GenericallyRigid (⊤ : SimpleGraph (Option (Fin (finrank ℝ E)))) E :=
    ⟨basisWithOrigin (Module.finBasis ℝ E), isRigid_complete_basisWithOrigin _⟩
  have h := (genericallyRigid_comap_iff _ e).mpr hG
  have he : (⊤ : SimpleGraph (Option (Fin (finrank ℝ E)))).comap e = ⊤ := by
    ext a b
    simp [e.injective.ne_iff]
  rwa [he] at h

end Cubical.Rigidity
