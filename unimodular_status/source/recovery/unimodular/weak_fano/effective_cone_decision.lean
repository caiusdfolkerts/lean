module

public import Mathlib.Geometry.Convex.Cone.Pointed
public import Unimodular
public import TauCeti.Geometry.Convex.Cone.Alternative
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Interval

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace Unimodular.EffectiveConeDecision

variable {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]

def intPair (z x : Lattice n) : ℤ := ∑ i, z i * x i

def augmented (u : E → Lattice n) (x : Lattice n) : Option E → Lattice n :=
  fun j => j.elim (-x) u

def primalAt (u : E → Lattice n) (x : Lattice n) (k : ℕ) : Prop :=
  ∃ c ∈ Fintype.piFinset (fun _ : Option E => Finset.range (k + 1)),
    0 < c none ∧ ∑ j, c j • augmented u x j = 0

def dualAt (u : E → Lattice n) (x : Lattice n) (k : ℕ) : Prop :=
  ∃ z ∈ Fintype.piFinset (fun _ : Fin n => Finset.Icc (-(k : ℤ)) (k : ℤ)),
    (∀ e, 0 ≤ intPair z (u e)) ∧ intPair z x < 0

instance (u : E → Lattice n) (x : Lattice n) (k : ℕ) :
    Decidable (primalAt u x k) := by unfold primalAt; infer_instance
instance (u : E → Lattice n) (x : Lattice n) (k : ℕ) :
    Decidable (dualAt u x k) := by unfold dualAt; infer_instance

/-- Every integer additive functional is its finite integer coordinate vector. -/
theorem additive_eq_intPair (f : Lattice n →+ ℤ) (x : Lattice n) :
    f x = intPair (fun i => f (Pi.single i 1)) x := by
  have hx : x = ∑ i, x i • Pi.single i (1 : ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  change f.toIntLinearMap x = intPair (fun i => f (Pi.single i 1)) x
  conv_lhs => rw [hx, map_sum]
  simp only [map_smul, smul_eq_mul, intPair, AddMonoidHom.coe_toIntLinearMap]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/-- Integer Tucker supplies a certificate on one of the two sides. Every
certificate occurs in a finite box, so the dovetailed search is total. -/
theorem exists_certificate (u : E → Lattice n) (x : Lattice n) :
    ∃ k, primalAt u x k ∨ dualAt u x k := by
  obtain ⟨c, f, hsum, hf, hpos⟩ :=
    TauCeti.exists_nat_sum_nsmul_eq_zero_and_forall_coeff_add_dual_pos (augmented u x)
  by_cases hc : 0 < c none
  · let k := ∑ j, c j
    refine ⟨k, Or.inl ⟨c, ?_, hc, hsum⟩⟩
    apply Fintype.mem_piFinset.2
    intro j
    apply Finset.mem_range.2
    have hj : c j ≤ k := Finset.single_le_sum (fun i _ => Nat.zero_le (c i)) (Finset.mem_univ j)
    omega
  · have hc0 : c none = 0 := by omega
    let z : Lattice n := fun i => f (Pi.single i 1)
    let k : ℕ := ∑ i, (z i).natAbs
    refine ⟨k, Or.inr ⟨z, ?_, ?_, ?_⟩⟩
    · apply Fintype.mem_piFinset.2
      intro i
      apply Finset.mem_Icc.2
      have hi : (z i).natAbs ≤ k :=
        Finset.single_le_sum (fun j _ => Nat.zero_le ((z j).natAbs)) (Finset.mem_univ i)
      have hi' : |z i| ≤ (k : ℤ) := by
        rw [← Int.natCast_natAbs]
        exact_mod_cast hi
      exact abs_le.1 hi'
    · intro e
      have he := hf (some e)
      change 0 ≤ f (u e) at he
      rw [additive_eq_intPair f (u e)] at he
      exact he
    · have he := hpos none
      simp only [augmented, Option.elim_none, hc0, Nat.cast_zero, zero_add, map_neg] at he
      rw [additive_eq_intPair] at he
      change 0 < -intPair z x at he
      exact neg_pos.mp he

/-- Total executable natural search over explicitly finite arithmetic tests. -/
def searchBound (u : E → Lattice n) (x : Lattice n) : ℕ :=
  Nat.find (exists_certificate u x)

/-- This Boolean is computed only from the finite integral input. -/
def contains (u : E → Lattice n) (x : Lattice n) : Bool :=
  decide (primalAt u x (searchBound u x))

noncomputable section

private def castHom : Lattice n →+ Ambient n where
  toFun := embed
  map_zero' := by ext i; simp [embed]
  map_add' x y := by ext i; simp [embed]

private def dualReal (z : Lattice n) : Ambient n →ₗ[ℝ] ℝ where
  toFun y := ∑ i, (z i : ℝ) * y i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.mul_sum, mul_left_comm]

private theorem dualReal_embed (z x : Lattice n) :
    dualReal z (embed x) = (intPair z x : ℝ) := by
  simp [dualReal, intPair, embed]

/-- A positive-denominator integer representation is a genuine real conic representation. -/
theorem primal_sound (u : E → Lattice n) (x : Lattice n) (k : ℕ)
    (h : primalAt u x k) : embed x ∈ PointedCone.hull ℝ (Set.range (fun e => embed (u e))) := by
  obtain ⟨c, hbox, hc, hsum⟩ := h
  have hZ : ∑ e, c (some e) • u e = c none • x := by
    have he : -(c none • x) + (∑ e, c (some e) • u e) = 0 := by
      simpa only [Fintype.sum_option, augmented, Option.elim_none, Option.elim_some,
        smul_neg] using hsum
    have he' := congrArg (fun y : Lattice n => c none • x + y) he
    simpa only [add_neg_cancel_left, add_zero] using he'
  have hR : ∑ e, (c (some e) : ℝ) • embed (u e) = (c none : ℝ) • embed x := by
    simpa only [map_sum, map_nsmul, castHom, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk, Nat.cast_smul_eq_nsmul] using congrArg (castHom (n := n)) hZ
  let C := PointedCone.hull ℝ (Set.range (fun e => embed (u e)))
  have hm : (c none : ℝ) • embed x ∈ C := by
    rw [← hR]
    exact C.sum_mem (fun e _ => C.smul_mem (Nat.cast_nonneg _)
      (PointedCone.subset_hull ⟨e, rfl⟩))
  have hcp : (0 : ℝ) < c none := by exact_mod_cast hc
  have hi := C.smul_mem (inv_nonneg.2 hcp.le) hm
  simpa only [smul_smul, inv_mul_cancel₀ hcp.ne', one_smul] using hi

/-- Nonnegativity on generators extends to their actual real cone. -/
theorem nonneg_on_hull (u : E → Lattice n) (f : Ambient n →ₗ[ℝ] ℝ)
    (hu : ∀ e, 0 ≤ f (embed (u e))) :
    ∀ x ∈ PointedCone.hull ℝ (Set.range (fun e => embed (u e))), 0 ≤ f x := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨e, rfl⟩ := hy
    exact hu e
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_nonneg hx hy
  | smul a x _ hx =>
    rw [← Nonneg.coe_smul, map_smul, smul_eq_mul]
    exact mul_nonneg a.property hx

/-- The dual certificate excludes literal real cone membership. -/
theorem dual_sound (u : E → Lattice n) (x : Lattice n) (k : ℕ)
    (h : dualAt u x k) : embed x ∉ PointedCone.hull ℝ (Set.range (fun e => embed (u e))) := by
  obtain ⟨z, hz, hu, hx⟩ := h
  intro hm
  have hn := nonneg_on_hull u (dualReal z)
    (fun e => by rw [dualReal_embed]; exact_mod_cast hu e) _ hm
  rw [dualReal_embed] at hn
  have hn' : 0 ≤ intPair z x := by exact_mod_cast hn
  omega

/-- Exact correctness for all finite integer vector families, including
nonsimplicial cones, zero vectors, nonpointed cones, and nonspanning families. -/
theorem contains_iff (u : E → Lattice n) (x : Lattice n) :
    contains u x = true ↔ embed x ∈ PointedCone.hull ℝ (Set.range (fun e => embed (u e))) := by
  simp only [contains, decide_eq_true_eq]
  constructor
  · exact primal_sound u x _
  · intro hx
    rcases Nat.find_spec (exists_certificate u x) with hp | hd
    · exact hp
    · exact False.elim (dual_sound u x _ hd hx)

end
end Unimodular.EffectiveConeDecision

#print axioms Unimodular.EffectiveConeDecision.contains
#print axioms Unimodular.EffectiveConeDecision.contains_iff
#check Unimodular.EffectiveConeDecision.contains_iff
