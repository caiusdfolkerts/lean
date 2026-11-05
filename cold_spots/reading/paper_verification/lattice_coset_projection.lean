module

public import PaperVerification.FiniteProjectionTransfer
public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.Abel
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Gaussian convergence and projection for genuine lattice cosets

Convergence is derived from discreteness of the integer submodule. The proof
compares a Gaussian to a convergent inverse power series on the lattice; the
possible point of zero distance is a finite exceptional set. The final theorem
therefore has no analytic summability hypotheses.

The coordinate point sets use the Euclidean `WithLp 2` structure explicitly, so
the norm used in the convergence theorem is exactly the sum-of-squares metric
used in `sqDist` throughout the project.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open Filter

/-- A quantitative Gaussian tail estimate, obtained from a single term of the
exponential power series. -/
theorem gaussian_le_inverse_power (α t : ℝ) (hα : 0 < α) (ht : 0 < t) (m : ℕ) :
    Real.exp (-α * t ^ 2) ≤
      (Nat.factorial m : ℝ) / α ^ m * t⁻¹ ^ (2 * m) := by
  have hp := Real.pow_div_factorial_le_exp (x := α * t ^ 2)
    (mul_nonneg hα.le (sq_nonneg t)) m
  have hpos : 0 < (α * t ^ 2) ^ m / (Nat.factorial m : ℝ) := by positivity
  calc
    Real.exp (-α * t ^ 2) = (Real.exp (α * t ^ 2))⁻¹ := by
      rw [neg_mul, Real.exp_neg]
    _ ≤ ((α * t ^ 2) ^ m / (Nat.factorial m : ℝ))⁻¹ := inv_anti₀ hpos hp
    _ = (Nat.factorial m : ℝ) / α ^ m * t⁻¹ ^ (2 * m) := by
      simp only [inv_div, mul_pow, ← pow_mul, div_eq_mul_inv, mul_inv_rev, inv_pow, inv_inv]
      ring

/-- Every Gaussian series on a discrete integer submodule of a finite
real normed space converges. Full rank is unnecessary for convergence. -/
theorem summable_gaussian_zlattice
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L]
    (α : ℝ) (hα : 0 < α) (x : E) :
    Summable (fun z : L => Real.exp (-α * ‖(z : E) - x‖ ^ 2)) := by
  let m : ℕ := Module.finrank ℤ L + 1
  have hm : Module.finrank ℤ L < 2 * m := by dsimp [m]; omega
  have hs := (ZLattice.summable_norm_sub_inv_pow L (2 * m) hm x).mul_left
    ((Nat.factorial m : ℝ) / α ^ m)
  apply Summable.of_norm_bounded_eventually hs
  have hfinite : {z : L | (z : E) = x}.Finite := Set.Subsingleton.finite (by
    intro a ha b hb
    exact Subtype.ext (ha.trans hb.symm))
  filter_upwards [hfinite.compl_mem_cofinite] with z hz
  have hz' : (z : E) ≠ x := hz
  have hnorm : 0 < ‖(z : E) - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz')
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact gaussian_le_inverse_power α ‖(z : E) - x‖ hα hnorm m

/-- A literal lattice coset, expressed in the coordinate convention used by the
paper. Its underlying lattice carries the Euclidean norm. -/
def euclideanLatticeCoset {n : ℕ}
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) : Set (Fin n → ℝ) :=
  {x | WithLp.toLp 2 x - a ∈ L}

def euclideanLatticeCosetEquiv {n : ℕ}
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) : L ≃ euclideanLatticeCoset L a where
  toFun z := ⟨WithLp.ofLp (z.val + a), by
    change WithLp.toLp 2 (WithLp.ofLp (z.val + a)) - a ∈ L
    simpa only [WithLp.toLp_ofLp, add_sub_cancel_right] using z.property⟩
  invFun x := ⟨WithLp.toLp 2 x.val - a, x.property⟩
  left_inv z := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp

theorem euclideanLatticeCoset_nonempty {n : ℕ}
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) : (euclideanLatticeCoset L a).Nonempty :=
  ⟨(euclideanLatticeCosetEquiv L a 0).val,
    (euclideanLatticeCosetEquiv L a 0).property⟩

theorem sqDist_euclideanLatticeCosetEquiv {n : ℕ}
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) (z : L) (x : Fin n → ℝ) :
    sqDist (euclideanLatticeCosetEquiv L a z).val x =
      ‖(z : EuclideanSpace ℝ (Fin n)) - (WithLp.toLp 2 x - a)‖ ^ 2 := by
  rw [sqDist_eq_euclidean_norm_sq]
  change ‖WithLp.toLp 2 (WithLp.ofLp (z.val + a)) - WithLp.toLp 2 x‖ ^ 2 = _
  rw [WithLp.toLp_ofLp]
  have heq : z.val + a - WithLp.toLp 2 x = z.val - (WithLp.toLp 2 x - a) := by abel
  rw [heq]

/-- Convergence on every actual Euclidean lattice coset, at every positive
parameter and every real point. -/
theorem summable_gaussian_euclideanLatticeCoset {n : ℕ}
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    (a : EuclideanSpace ℝ (Fin n)) (α : ℝ) (hα : 0 < α) (x : Fin n → ℝ) :
    Summable (fun z : euclideanLatticeCoset L a => Real.exp (-α * sqDist z.val x)) := by
  let e := euclideanLatticeCosetEquiv L a
  have hs := summable_gaussian_zlattice L α hα (WithLp.toLp 2 x - a)
  have hs' : Summable (fun z : L => Real.exp (-α * sqDist (e z).val x)) := by
    simpa only [e, sqDist_euclideanLatticeCosetEquiv] using hs
  exact (e.summable_iff
    (f := fun z : euclideanLatticeCoset L a => Real.exp (-α * sqDist z.val x))).mp hs'

/-- Distinct cosets of an additive lattice are disjoint. -/
theorem euclideanLatticeCoset_pairwise_disjoint {n : ℕ} {G : Type*}
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (a : G → EuclideanSpace ℝ (Fin n))
    (ha : Pairwise (fun g g' => a g - a g' ∉ L)) :
    Pairwise (fun g g' => Disjoint
      (euclideanLatticeCoset L (a g)) (euclideanLatticeCoset L (a g'))) := by
  intro g g' hne
  apply Set.disjoint_left.mpr
  intro x hx hx'
  apply ha hne
  have hm := L.sub_mem hx' hx
  convert hm using 1
  abel

/-- Projection transfer for genuine lattice cosets. Discreteness discharges all
series-convergence obligations. This is the full finite-glue form of Proposition
6.1 in orthogonal Euclidean coordinates, and includes both its minimum value and
its exact geometric equality set. -/
theorem lattice_coset_projection_transfer {h w : ℕ} {G : Type*}
    [Fintype G] [Nonempty G]
    (N : Submodule ℤ (EuclideanSpace ℝ (Fin h))) [DiscreteTopology N]
    (F : Submodule ℤ (EuclideanSpace ℝ (Fin w))) [DiscreteTopology F]
    (a : G → EuclideanSpace ℝ (Fin h)) (b : G → EuclideanSpace ℝ (Fin w))
    (ha : Pairwise (fun g g' => a g - a g' ∉ N))
    (t₀ : Fin w → ℝ) (c : ℝ → ℝ)
    (hfibre : ∀ α : ℝ, 0 < α → ∀ g,
      setGaussian (euclideanLatticeCoset F (b g)) α t₀ = c α)
    (K : Set (Fin (h + w) → ℝ))
    (hK : ∀ α : ℝ, 0 < α → ∀ z,
      IsColdSpot (orthogonalGlue (fun g => euclideanLatticeCoset N (a g))
        (fun g => euclideanLatticeCoset F (b g))) α z ↔ z ∈ K)
    (hmeet : ∃ x₀ : Fin h → ℝ, Fin.append x₀ t₀ ∈ K) :
    (∀ α : ℝ, 0 < α → ∀ x : Fin h → ℝ,
      IsColdSpot (⋃ g, euclideanLatticeCoset N (a g)) α x ↔ Fin.append x t₀ ∈ K) ∧
    (∀ α : ℝ, 0 < α →
      sInf (Set.range (setGaussian (⋃ g, euclideanLatticeCoset N (a g)) α)) =
        sInf (Set.range (setGaussian (orthogonalGlue
          (fun g => euclideanLatticeCoset N (a g))
          (fun g => euclideanLatticeCoset F (b g))) α)) / c α) ∧
    ((∀ z, z ∈ K ↔ IsDeepHole (orthogonalGlue
      (fun g => euclideanLatticeCoset N (a g))
      (fun g => euclideanLatticeCoset F (b g))) z) →
      ∀ x : Fin h → ℝ,
        IsDeepHole (⋃ g, euclideanLatticeCoset N (a g)) x ↔ Fin.append x t₀ ∈ K) := by
  apply finite_profile_projection_transfer
    (fun g => euclideanLatticeCoset N (a g)) (fun g => euclideanLatticeCoset F (b g))
    (euclideanLatticeCoset_pairwise_disjoint N a ha)
    (fun g => euclideanLatticeCoset_nonempty N (a g))
    (fun g => euclideanLatticeCoset_nonempty F (b g)) t₀ c
  · intro α hα x g
    exact summable_gaussian_euclideanLatticeCoset N (a g) α hα x
  · intro α hα g
    exact summable_gaussian_euclideanLatticeCoset F (b g) α hα t₀
  · exact hfibre
  · exact hK
  · exact hmeet

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.summable_gaussian_zlattice
#print axioms PaperVerification.ColdSpots.summable_gaussian_euclideanLatticeCoset
#print axioms PaperVerification.ColdSpots.lattice_coset_projection_transfer

