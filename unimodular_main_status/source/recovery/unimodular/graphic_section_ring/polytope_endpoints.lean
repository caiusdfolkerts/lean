module
public import Recovery.Unimodular.GraphicSectionRing.InitialIdeal
public import Recovery.Unimodular.GraphicSectionRing.Polytope
public import Recovery.Unimodular.GraphicSectionRing.CoordinateInvariance
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators MonomialOrder Pointwise

namespace Unimodular.GraphicSectionRing

/-- Closure under the actual lower and upper integral midpoint operations. -/
def BalancedClosed {n : ℕ} {σ : Type*} (p : σ → Lattice n) : Prop :=
  ∀ a b, ∃ l u, p l = lower (p a) (p b) ∧ p u = upper (p a) (p b)

/-- The initial-ideal proof is independent of the chosen labels of the actual
lattice points. The balancing closure is proved from the defining inequalities
in the paper-level endpoint below. -/
theorem balancedClosed_initialIdeal {n : ℕ} {σ : Type*} (p : σ → Lattice n)
    (hp : Function.Injective p) (hb : BalancedClosed p)
    (K : Type*) [CommRing K] [Nontrivial K] (base : MonomialOrder σ) :
    initialIdeal (WeightedOrder.refine (monomialWeight p) base) (toricIdeal p K) =
      quadraticMonomialIdeal p K := by
  classical
  apply le_antisymm (initialIdeal_le_quadratic hp K base)
  apply Ideal.span_le.mpr
  rintro _ ⟨v, ⟨a, b, hab, rfl⟩, rfl⟩
  obtain ⟨l, u, hl, hu⟩ := hb a b
  let q : MvPolynomial σ K := MvPolynomial.monomial (pairExponent a b) 1 -
    MvPolynomial.monomial (pairExponent l u) 1
  have hdeg : toricDegree p (pairExponent l u) = toricDegree p (pairExponent a b) := by
    simp only [pairExponent, map_add, toricDegree_single]
    apply Prod.ext
    · rfl
    · change p l + p u = p a + p b
      rw [hl, hu]
      exact lower_add_upper _ _
  have hker : q ∈ toricIdeal p K := by
    change toricMap p K q = 0
    simp only [q, map_sub, toricMap_monomial, hdeg, sub_self]
  have hwt : monomialWeight p (pairExponent l u) < monomialWeight p (pairExponent a b) := by
    apply (Nat.cast_lt (α := ℤ)).mp
    simpa only [pairExponent, map_add, monomialWeight_single, Nat.cast_add,
      Int.toNat_of_nonneg (height_nonneg _), hl, hu] using height_balance_lt (p a) (p b) hab
  let m := WeightedOrder.refine (monomialWeight p) base
  have hlt : m.degree (MvPolynomial.monomial (pairExponent l u) (1 : K)) ≺[m]
      m.degree (MvPolynomial.monomial (pairExponent a b) (1 : K)) := by
    simpa only [m.degree_monomial, if_neg (one_ne_zero : (1 : K) ≠ 0)] using
      WeightedOrder.lt_of_weight_lt (monomialWeight p) base hwt
  have hlead : m.leadingTerm q = MvPolynomial.monomial (pairExponent a b) 1 :=
    (m.leadingTerm_sub_of_lt hlt).trans (m.leadingTerm_monomial _ _)
  exact Ideal.subset_span ⟨q, hker, hlead⟩

set_option maxHeartbeats 800000 in
/-- Every finite injectively labelled balanced configuration admits a genuine
well-founded additive monomial order with the stated initial ideal. -/
theorem exists_balancedClosed_initialIdeal {n : ℕ} {σ : Type} [Finite σ]
    (p : σ → Lattice n) (hp : Function.Injective p) (hb : BalancedClosed p)
    (K : Type*) [CommRing K] [Nontrivial K] :
    ∃ m : MonomialOrder.{0,0} σ,
      initialIdeal m (toricIdeal p K) = quadraticMonomialIdeal p K := by
  classical
  letI := Fintype.ofFinite σ
  let ord : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  have wf : @WellFoundedGT σ ord.toLT :=
    InvImage.wf (Fintype.equivFin σ) (inferInstance : WellFoundedGT (Fin (Fintype.card σ)))
  let base : MonomialOrder.{0,0} σ := @MonomialOrder.lex σ ord wf
  exact ⟨WeightedOrder.refine (monomialWeight p) base, balancedClosed_initialIdeal p hp hb K base⟩

/-- Lattice points of any bounded real set are finite; no full-dimensionality
or interior point is required. -/
theorem finite_lattice_points_of_bounded {n : ℕ} (P : Set (RealLattice n))
    (hP : Bornology.IsBounded P) : {x : Lattice n | latticeCast x ∈ P}.Finite := by
  obtain ⟨R, hR⟩ := hP.subset_closedBall (0 : RealLattice n)
  obtain ⟨N, hN⟩ := exists_nat_gt R
  apply (Set.Finite.pi (fun _ : Fin n => Set.finite_Icc (-(N : ℤ)) (N : ℤ))).subset
  intro x hx i _
  have hxR : ‖latticeCast x‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hR hx
  have hi : |(x i : ℝ)| ≤ (N : ℝ) :=
    (norm_le_pi_norm (latticeCast x) i).trans (hxR.trans hN.le)
  have hib := abs_le.mp hi
  constructor
  · exact_mod_cast hib.1
  · exact_mod_cast hib.2

abbrev LatticePoint {n : ℕ} (P : Set (RealLattice n)) :=
  {x : Lattice n // latticeCast x ∈ P}

/-- The full lattice-point initial-ideal clause, on the original variables and
original toric kernel, after an arbitrary integral coordinate change.

Only the lattice-point consequence of the real inequality presentation is
needed for this conclusion. Every real presentation by the paper's integral
difference inequalities supplies this hypothesis by evaluation at lattice
points. The theorem is therefore slightly stronger than the polytope clause;
it does not assume a lattice basis, nonempty interior or any normality result
in addition to the displayed coordinate change and the actual inequalities. -/
theorem bounded_graphic_lattice_point_initial_ideal {n d : ℕ}
    (P : Set (RealLattice n)) (hbounded : Bornology.IsBounded P)
    (e : Lattice n ≃ₗ[ℤ] Lattice d) (C : Set (Constraint d))
    (hP : ∀ x : Lattice n, latticeCast x ∈ P ↔ Satisfies C (e x))
    (K : Type*) [CommRing K] [Nontrivial K] :
    ∃ m : MonomialOrder.{0,0} (LatticePoint P),
      initialIdeal m (toricIdeal (Subtype.val : LatticePoint P → Lattice n) K) =
        quadraticMonomialIdeal (e ∘ (Subtype.val : LatticePoint P → Lattice n)) K ∧
      ∀ v ∈ forbiddenExponents (e ∘ (Subtype.val : LatticePoint P → Lattice n)),
        v.degree = 2 ∧ ∀ i, v i ≤ 1 := by
  classical
  letI : Fintype (LatticePoint P) := (finite_lattice_points_of_bounded P hbounded).fintype
  let p : LatticePoint P → Lattice d := e ∘ Subtype.val
  have hp : Function.Injective p := e.injective.comp Subtype.val_injective
  have hb : BalancedClosed p := by
    intro a b
    have ha := (hP a.val).mp a.property
    have hb := (hP b.val).mp b.property
    let l : LatticePoint P := ⟨e.symm (lower (e a.val) (e b.val)),
      (hP _).mpr (by simpa only [e.apply_symm_apply] using lower_satisfies ha hb)⟩
    let u : LatticePoint P := ⟨e.symm (upper (e a.val) (e b.val)),
      (hP _).mpr (by simpa only [e.apply_symm_apply] using upper_satisfies ha hb)⟩
    exact ⟨l, u, e.apply_symm_apply _, e.apply_symm_apply _⟩
  obtain ⟨m, hm⟩ := exists_balancedClosed_initialIdeal p hp hb K
  have hideal : toricIdeal p K = toricIdeal (Subtype.val : LatticePoint P → Lattice n) K :=
    toricIdeal_integralLinearEquiv Subtype.val e K
  refine ⟨m, ?_, ?_⟩
  · rw [← hideal]
    exact hm
  · exact fun v hv => forbiddenExponents_squarefree_quadratic p hv

/-- Direct bounded-body specialization; the actual metric hypothesis proves
finiteness of the variable set, rather than assuming it as an extra premise. -/
theorem bounded_difference_initial_ideal {n : ℕ} (C : Set (Constraint n))
    (hC : Bornology.IsBounded (body C)) (K : Type*) [CommRing K] [Nontrivial K] :
    ∃ m : MonomialOrder.{0,0} (LatticePoint (body C)),
      initialIdeal m (toricIdeal (Subtype.val : LatticePoint (body C) → Lattice n) K) =
        quadraticMonomialIdeal Subtype.val K := by
  obtain ⟨m, hm, _⟩ := bounded_graphic_lattice_point_initial_ideal (body C) hC
    (LinearEquiv.refl ℤ (Lattice n)) C (fun _ => latticeCast_mem_body) K
  exact ⟨m, hm⟩

/-- The integer-decomposition statement uses the literal real polytope and
its actual dilations, for every positive degree and every dimension. -/
theorem graphic_polytope_integer_decomposition {n k : ℕ} (P : Set (RealLattice n))
    (C : Set (Constraint n)) (hP : P = body C) (hk : 0 < k)
    (x : Lattice n) (hx : latticeCast x ∈ (k : ℝ) • P) :
    ∃ v : Fin k → Lattice n, (∀ i, latticeCast (v i) ∈ P) ∧ ∑ i, v i = x := by
  subst P
  exact integer_decomposition hk x hx

end Unimodular.GraphicSectionRing
#print axioms Unimodular.GraphicSectionRing.balancedClosed_initialIdeal
#print axioms Unimodular.GraphicSectionRing.bounded_graphic_lattice_point_initial_ideal
#print axioms Unimodular.GraphicSectionRing.bounded_difference_initial_ideal
#print axioms Unimodular.GraphicSectionRing.graphic_polytope_integer_decomposition
#check Unimodular.GraphicSectionRing.bounded_graphic_lattice_point_initial_ideal
