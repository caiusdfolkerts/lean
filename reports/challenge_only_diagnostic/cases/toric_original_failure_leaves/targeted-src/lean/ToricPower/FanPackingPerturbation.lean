module

public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Separation
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega

/-!
# Integral perturbations and separated cone attachments

The relative fan-completion construction attaches rays close to a
selected old ray. Integral lifts can be moved towards that ray by adding
a sufficiently large positive integral multiple of its generator. A
single threshold works for every member of the finite separating family.

The second lemma records the exact geometric consequence of strict
positivity: adjoining such generators does not change the intersection
with a cone lying on the opposite side of the separating hyperplane.
-/

@[expose] public noncomputable section

namespace ToricPower.FanPacking

variable {N : Type*} [AddCommGroup N]

/-- One integral translation works simultaneously for a finite family
of integral separators and every specified lift, and remains valid for
every larger translation parameter. -/
theorem exists_uniform_positive_translation
    (forms : Finset (N →+ ℤ)) (vectors : Finset N) (a : N)
    (positive : ∀ m ∈ forms, 0 < m a) :
    ∃ threshold : ℕ, ∀ M ≥ threshold, ∀ m ∈ forms, ∀ v ∈ vectors,
      0 < m (v + M • a) := by
  classical
  let bound := (forms.product vectors).sup (fun p => (-(p.1 p.2)).toNat)
  refine ⟨bound + 1, ?_⟩
  intro M large m hm v hv
  have lower : (-(m v)).toNat ≤ bound :=
    Finset.le_sup (s := forms.product vectors) (b := (m,v))
      (f := fun p : (N →+ ℤ) × N => (-(p.1 p.2)).toNat)
      (Finset.mem_product.mpr ⟨hm,hv⟩)
  have value : -(m v) ≤ (bound : ℤ) := by
    exact (Int.self_le_toNat _).trans (Int.ofNat_le.mpr lower)
  have large' : (bound : ℤ) + 1 ≤ (M : ℤ) := by exact_mod_cast large
  have positive' : 1 ≤ m a := by have := positive m hm; omega
  have nonnegative : 0 ≤ (M : ℤ) := Int.ofNat_nonneg M
  have result : 0 < m v + (M : ℤ) * m a := by nlinarith
  simpa only [map_add, map_nsmul, nsmul_eq_mul] using result

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Strict positivity on every generator implies nonnegativity on its
cone, with equality only at the origin. No independence is needed. -/
theorem hull_nonnegative_and_zero
    (form : V →ₗ[ℝ] ℝ) (generators : Set V)
    (positive : ∀ v ∈ generators, 0 < form v)
    {x : V} (member : x ∈ PointedCone.hull ℝ generators) :
    0 ≤ form x ∧ (form x = 0 → x = 0) := by
  refine Submodule.span_induction
    (p := fun x _ => 0 ≤ form x ∧ (form x = 0 → x = 0)) ?_ ?_ ?_ ?_ member
  · intro v hv
    exact ⟨(positive v hv).le, fun zero => False.elim ((positive v hv).ne' zero)⟩
  · simp only [map_zero, le_refl, implies_true, and_self]
  · intro x y hx hy px py
    constructor
    · simpa only [map_add] using add_nonneg px.1 py.1
    · intro zero
      have parts := (add_eq_zero_iff_of_nonneg px.1 py.1).mp
        (show form x + form y = 0 by simpa only [map_add] using zero)
      rw [px.2 parts.1, py.2 parts.2, add_zero]
  · intro r x hx px
    constructor
    · change 0 ≤ form ((r : ℝ) • x)
      rw [map_smul, smul_eq_mul]
      exact mul_nonneg r.property px.1
    · intro zero
      have product : (r : ℝ) * form x = 0 := by
        change form ((r : ℝ) • x) = 0 at zero
        simpa only [map_smul, smul_eq_mul] using zero
      rcases mul_eq_zero.mp product with scalarZero | valueZero
      · have : r = 0 := Subtype.ext scalarZero
        simp only [this, zero_smul]
      · simp only [px.2 valueZero, smul_zero]

/-- A strictly positive new cone cannot contribute to an intersection
across a separating hyperplane. This is the precise attachment identity
used when packing a ray without changing any old cone. -/
theorem adjoining_positive_generators_inf
    (old opposite : PointedCone ℝ V) (form : V →ₗ[ℝ] ℝ)
    (nonnegative : ∀ x ∈ old, 0 ≤ form x)
    (nonpositive : ∀ x ∈ opposite, form x ≤ 0)
    (generators : Set V) (positive : ∀ v ∈ generators, 0 < form v) :
    (old ⊔ PointedCone.hull ℝ generators) ⊓ opposite = old ⊓ opposite := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y,hy,z,hz,sum⟩ := Submodule.mem_sup.mp hx.1
    have newPart := hull_nonnegative_and_zero form generators positive hz
    have zero : form z = 0 := by
      have total := nonpositive x hx.2
      have first := nonnegative y hy
      rw [← sum, map_add] at total
      linarith [newPart.1]
    have zZero := newPart.2 zero
    have same : y = x := by simpa only [zZero,add_zero] using sum
    exact ⟨same ▸ hy, hx.2⟩
  · exact inf_le_inf_right _ le_sup_left

end ToricPower.FanPacking
end
