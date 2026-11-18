module

public import Recovery.Unimodular.GraphicSectionRing.Height
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# The literal real difference polytope and all-degree integer decomposition

The inequalities here are in ordinary real coordinate space.  Finiteness of
its lattice points follows from actual metric boundedness.  Integer
decomposition is proved for every positive degree, including lower-dimensional
and degenerate difference polytopes.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators Pointwise

namespace Unimodular.GraphicSectionRing

abbrev RealLattice (n : ℕ) := Fin n → ℝ

def latticeCast {n : ℕ} (x : Lattice n) : RealLattice n := fun i => x i

def realAnchored {n : ℕ} (x : RealLattice n) : Coordinate n → ℝ
  | none => 0
  | some i => x i

def realDifference {n : ℕ} (x : RealLattice n) (a b : Coordinate n) : ℝ :=
  realAnchored x a - realAnchored x b

/-- The actual closed real set cut out by the integral difference inequalities. -/
def body {n : ℕ} (C : Set (Constraint n)) : Set (RealLattice n) :=
  {x | ∀ c ∈ C, realDifference x c.left c.right ≤ (c.bound : ℝ)}

theorem realDifference_cast {n : ℕ} (x : Lattice n) (a b : Coordinate n) :
    realDifference (latticeCast x) a b = (difference x a b : ℝ) := by
  cases a <;> cases b <;> simp [realDifference, realAnchored, latticeCast, difference, anchored]

theorem realDifference_smul {n : ℕ} (r : ℝ) (x : RealLattice n) (a b : Coordinate n) :
    realDifference (r • x) a b = r * realDifference x a b := by
  cases a <;> cases b <;>
    simp [realDifference, realAnchored, Pi.smul_apply, smul_eq_mul, mul_sub]

theorem latticeCast_mem_body {n : ℕ} {C : Set (Constraint n)} {x : Lattice n} :
    latticeCast x ∈ body C ↔ Satisfies C x := by
  constructor
  · intro h c hc
    have hi := h c hc
    rw [realDifference_cast] at hi
    exact_mod_cast hi
  · intro h c hc
    rw [realDifference_cast]
    exact_mod_cast h c hc

theorem scaled_inequalities_of_mem_dilate {n k : ℕ} {C : Set (Constraint n)}
    {m : Lattice n} (hm : latticeCast m ∈ (k : ℝ) • body C) :
    ∀ c ∈ C, difference m c.left c.right ≤ (k : ℤ) * c.bound := by
  obtain ⟨x, hx, heq⟩ := Set.mem_smul_set.mp hm
  intro c hc
  have hd := congrArg (fun y => realDifference y c.left c.right) heq
  rw [realDifference_smul, realDifference_cast] at hd
  have hi := mul_le_mul_of_nonneg_left (hx c hc) (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  rw [hd] at hi
  exact_mod_cast hi

/-- Full integer decomposition for the actual real polytope, with no bound on
its dimension, the dilation degree, the number of inequalities or its volume. -/
theorem integer_decomposition {n k : ℕ} (hk : 0 < k) {C : Set (Constraint n)}
    (m : Lattice n) (hm : latticeCast m ∈ (k : ℝ) • body C) :
    ∃ v : Fin k → Lattice n, (∀ r, latticeCast (v r) ∈ body C) ∧ ∑ r, v r = m := by
  refine ⟨balanced m, ?_, balanced_sum hk m⟩
  intro r
  exact latticeCast_mem_body.mpr (balanced_satisfies hk m
    (scaled_inequalities_of_mem_dilate hm) r)

/-- Boundedness is used only to make the variable set finite; it is not an
extra normality or triangulation hypothesis. -/
theorem finite_lattice_points {n : ℕ} {C : Set (Constraint n)}
    (hC : Bornology.IsBounded (body C)) : {x : Lattice n | Satisfies C x}.Finite := by
  obtain ⟨R, hR⟩ := hC.subset_closedBall (0 : RealLattice n)
  obtain ⟨N, hN⟩ := exists_nat_gt R
  apply (Set.Finite.pi (fun _ : Fin n => Set.finite_Icc (-(N : ℤ)) (N : ℤ))).subset
  intro x hx i _
  have hxR : ‖latticeCast x‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hR (latticeCast_mem_body.mpr hx)
  have hi : |(x i : ℝ)| ≤ (N : ℝ) :=
    (norm_le_pi_norm (latticeCast x) i).trans (hxR.trans hN.le)
  have hib := abs_le.mp hi
  constructor
  · exact_mod_cast hib.1
  · exact_mod_cast hib.2

#print axioms integer_decomposition
#print axioms finite_lattice_points

end Unimodular.GraphicSectionRing
#check Unimodular.GraphicSectionRing.integer_decomposition
