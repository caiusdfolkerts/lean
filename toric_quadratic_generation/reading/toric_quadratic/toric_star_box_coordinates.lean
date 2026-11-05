module
public import PaperVerification.ToricIntegralBasis
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
@[expose] public section
/-!
# Integral basis changes and normal heights in a star-subdivision chart

The basis in equation (10) is constructed as an integral transvection.
The height formula and the displacement bounds are then consequences of
its actual vectors, including all tangent directions left unchanged.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

section BasisShear

variable {R E ι : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    [Fintype ι] [DecidableEq ι]

/-- The normal-coordinate functional of the integral shear. -/
def starShearFunctional (b : Module.Basis ι R E) (I : Finset ι) (j : ι) :
    E →ₗ[R] R := -∑ i ∈ I.erase j, b.coord i

theorem starShearFunctional_basis (b : Module.Basis ι R E)
    (I : Finset ι) (j k : ι) :
    starShearFunctional b I j (b k) = if k ∈ I.erase j then -1 else 0 := by
  simp [starShearFunctional, Module.Basis.coord_apply, Module.Basis.repr_self_apply,
    Finsupp.single_apply]
  split_ifs <;> simp

theorem starShearFunctional_pivot (b : Module.Basis ι R E)
    (I : Finset ι) (j : ι) : starShearFunctional b I j (b j) = 0 := by
  simp [starShearFunctional_basis]

/-- The genuine integral basis whose normal vectors are `e_j` and
`e_l-e_j`, with every other direction unchanged. -/
def starShearBasis (b : Module.Basis ι R E) (I : Finset ι) (j : ι) :
    Module.Basis ι R E :=
  b.map (LinearEquiv.transvection (starShearFunctional_pivot b I j))

theorem starShearBasis_apply (b : Module.Basis ι R E)
    (I : Finset ι) (j k : ι) :
    starShearBasis b I j k = if k ∈ I.erase j then b k - b j else b k := by
  simp only [starShearBasis, Module.Basis.map_apply,
    LinearEquiv.transvection.apply, starShearFunctional_basis]
  split_ifs <;> simp [sub_eq_add_neg]

@[simp] theorem starShearBasis_pivot (b : Module.Basis ι R E)
    (I : Finset ι) (j : ι) : starShearBasis b I j j = b j := by
  simp [starShearBasis_apply]

theorem starShearBasis_tangent (b : Module.Basis ι R E)
    (I : Finset ι) (j k : ι) (hk : k ∉ I) :
    starShearBasis b I j k = b k := by
  rw [starShearBasis_apply, if_neg (fun h => hk (Finset.mem_of_mem_erase h))]

/-- The complete box-coordinate sum after the shear. -/
theorem sum_smul_starShearBasis (b : Module.Basis ι R E)
    (I : Finset ι) (j : ι) (a : ι → R) :
    (∑ k, a k • starShearBasis b I j k) =
      (∑ k, a k • b k) - (∑ k ∈ I.erase j, a k) • b j := by
  calc
    (∑ k, a k • starShearBasis b I j k) =
        ∑ k, (a k • b k - (if k ∈ I.erase j then a k else 0) • b j) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [starShearBasis_apply]
      split_ifs <;> simp [smul_sub]
    _ = (∑ k, a k • b k) - (∑ k ∈ I.erase j, a k) • b j := by
      simp only [Finset.sum_sub_distrib, ← Finset.sum_smul, Finset.sum_ite_mem_eq]

/-- All old coordinates of a shifted box, including the special pivot
height, as an exact algebraic identity. -/
theorem coord_shifted_star_box (b : Module.Basis ι R E)
    (I : Finset ι) (j i : ι) (t : R) (a : ι → R) :
    b.coord i (t • b j + ∑ k, a k • starShearBasis b I j k) =
      a i + (if i = j then t - ∑ k ∈ I.erase j, a k else 0) := by
  rw [sum_smul_starShearBasis]
  simp only [map_add, map_sub, map_smul, map_sum,
    Module.Basis.coord_apply, Module.Basis.repr_self_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst i
    simp
    ring
  · simp [hij, Ne.symm hij]

/-- The sum of the old normal heights is precisely `t+a_j`. -/
theorem sum_normal_coords_shifted_star_box (b : Module.Basis ι R E)
    (I : Finset ι) (j : ι) (hj : j ∈ I) (t : R) (a : ι → R) :
    (∑ i ∈ I, b.coord i (t • b j + ∑ k, a k • starShearBasis b I j k)) =
      t + a j := by
  simp only [coord_shifted_star_box, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', if_pos hj]
  rw [← Finset.add_sum_erase I a hj]
  ring

end BasisShear

/-- Extending the integral star-chart basis to the reals gives exactly the
same vectors as performing the real shear. Thus the geometric coordinates
come from a full basis of the ambient integer lattice. -/
theorem integralBasisReal_starShearBasis {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) (j : Fin n) :
    integralBasisReal (starShearBasis b I j) =
      starShearBasis (integralBasisReal b) I j := by
  apply Module.Basis.eq_of_apply_eq
  intro k
  rw [integralBasisReal_apply, starShearBasis_apply, starShearBasis_apply]
  split_ifs
  · simp only [map_sub, integralBasisReal_apply]
  · exact (integralBasisReal_apply b k).symm

/-- The new normal heights of every point of a side-`w` shifted box are
nonnegative if the shift is at least `w(q-1)`. Their total lies in
`[t,t+w]`. These are exactly the height bounds used in Section 6.2. -/
theorem shifted_star_box_normal_heights {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (Ambient n))
    (I : Finset (Fin n)) (j : Fin n) (hj : j ∈ I)
    (w t : ℝ) (hw : 0 ≤ w) (ht : w * (I.card - 1 : ℕ) ≤ t)
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ w) :
    (∀ i ∈ I, 0 ≤ b.coord i
      (t • b j + ∑ k, a k • starShearBasis b I j k)) ∧
    t ≤ (∑ i ∈ I, b.coord i
      (t • b j + ∑ k, a k • starShearBasis b I j k)) ∧
    (∑ i ∈ I, b.coord i
      (t • b j + ∑ k, a k • starShearBasis b I j k)) ≤ t + w := by
  have hsum : (∑ k ∈ I.erase j, a k) ≤ w * (I.card - 1 : ℕ) := by
    calc
      (∑ k ∈ I.erase j, a k) ≤ ∑ _k ∈ I.erase j, w :=
        Finset.sum_le_sum (fun k _ => (ha k).2)
      _ = w * (I.card - 1 : ℕ) := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hj]
        ring
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [coord_shifted_star_box]
    by_cases hij : i = j
    · rw [if_pos hij]
      have h := (ha i).1
      linarith
    · rw [if_neg hij, add_zero]
      exact (ha i).1
  · rw [sum_normal_coords_shifted_star_box b I j hj]
    exact le_add_of_nonneg_right (ha j).1
  · rw [sum_normal_coords_shifted_star_box b I j hj]
    exact add_le_add le_rfl (ha j).2

end PaperVerification.ToricGeometry
