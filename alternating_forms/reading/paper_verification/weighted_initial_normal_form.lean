module

public import PaperVerification.WeightedInitialBasis
public import PaperVerification.FilteredBasisNormalForm

/-!
# The actual normal form of a lifted initial-quotient basis

The polynomial normal form is the finite expansion in the already proved
basis, using the same homogeneous representatives. Its weight bound and
its top coefficients follow from bounded lifts of every initial relation.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

namespace PaperVerification.WeightedInitialFiber

open MvPolynomial
open PaperVerification.FilteredBasisTransfer

-- Use the proved basis through its public type and application theorem.
-- Unfolding its bounded-lifting construction during unrelated coercion
-- inference expands a large proof term without changing the mathematics.
attribute [local irreducible] liftedInitialBasis

variable {K σ E : Type*} [Field K]
local notation "P" => MvPolynomial σ K

variable (Q : Ideal P) (w : σ → ℕ)
  (v : E → P) (degree : E → ℕ)
  (hv : ∀ e,(v e).IsWeightedHomogeneous w (degree e))
  (B₀ : Module.Basis E K (P⧸initialIdeal Q w))
  (hB₀ : ∀ e,B₀ e=Ideal.Quotient.mk _ (v e))

def liftedNormalForm
    (Q : Ideal P) (w : σ → ℕ) (v : E → P) (degree : E → ℕ)
    (hv : ∀ e,(v e).IsWeightedHomogeneous w (degree e))
    (B₀ : Module.Basis E K (P⧸initialIdeal Q w))
    (hB₀ : ∀ e,B₀ e=Ideal.Quotient.mk _ (v e)) : P →ₗ[K] P := by
  exact normalRepresentative (K := K) (M := P) (Q := P⧸Q) (E := E)
    (Ideal.Quotient.mkₐ K Q).toLinearMap v
    (liftedInitialBasis (K := K) (σ := σ) (E := E) Q w v degree hv B₀ hB₀)

@[simp] theorem liftedNormalForm_apply
    (Q : Ideal P) (w : σ → ℕ) (v : E → P) (degree : E → ℕ)
    (hv : ∀ e, (v e).IsWeightedHomogeneous w (degree e))
    (B₀ : Module.Basis E K (P ⧸ initialIdeal Q w))
    (hB₀ : ∀ e, B₀ e = Ideal.Quotient.mk _ (v e))
    (p : P) :
    liftedNormalForm (K := K) (σ := σ) (E := E) Q w v degree hv B₀ hB₀ p=
      ((liftedInitialBasis (K := K) (σ := σ) (E := E) Q w v degree hv B₀ hB₀).repr
        ((Ideal.Quotient.mkₐ K Q).toLinearMap p)).sum (fun e c => c • v e) := by
  unfold liftedNormalForm
  exact normalRepresentative_apply
    (Ideal.Quotient.mkₐ K Q).toLinearMap v
    (liftedInitialBasis (K := K) (σ := σ) (E := E) Q w v degree hv B₀ hB₀) p

theorem liftedNormalForm_bound
    (Q : Ideal P) (w : σ → ℕ) (v : E → P) (degree : E → ℕ)
    (hv : ∀ e, (v e).IsWeightedHomogeneous w (degree e))
    (B₀ : Module.Basis E K (P ⧸ initialIdeal Q w))
    (hB₀ : ∀ e, B₀ e = Ideal.Quotient.mk _ (v e))
    (p : P) (d : ℕ) (hp : WeightBound (K := K) w d p) :
    WeightBound (K := K) w d (liftedNormalForm (K := K) (σ := σ) (E := E) Q w v degree hv B₀ hB₀ p) := by
  apply (monomialBasis_bound_iff w d _).mp
  unfold liftedNormalForm
  apply normalRepresentative_bound (K := K) (M := P) (Q := P⧸Q)
    (Q₀ := P⧸initialIdeal Q w) (I := σ →₀ ℕ) (E := E) (basisMonomials σ K) (Finsupp.weight w)
    (Ideal.Quotient.mkₐ K Q).toLinearMap v
    (liftedInitialBasis (K := K) (σ := σ) (E := E) Q w v degree hv B₀ hB₀)
    (Ideal.Quotient.mkₐ K (initialIdeal Q w)).toLinearMap
    (Ideal.Quotient.mkₐ_surjective K (initialIdeal Q w)) ?_ degree
    (fun e => (monomialBasis_homogeneous_iff w (degree e) (v e)).mpr (hv e))
    B₀ hB₀ (liftedInitialBasis_apply (K := K) (σ := σ) (E := E) Q w v degree hv B₀ hB₀) p d
    ((monomialBasis_bound_iff w d p).mpr hp)
  intro x hx e
  obtain ⟨a,ha,hb,ht⟩ := initial_component_lift Q w x
    (Ideal.Quotient.eq_zero_iff_mem.mp hx) e
  exact ⟨a,Ideal.Quotient.eq_zero_iff_mem.mpr ha,
    (monomialBasis_bound_iff w e a).mpr hb,
    by simpa only [monomialBasis_component] using ht⟩

theorem lifted_coefficient_eq_zero_of_weight_lt
    (Q : Ideal P) (w : σ → ℕ) (v : E → P) (degree : E → ℕ)
    (hv : ∀ e, (v e).IsWeightedHomogeneous w (degree e))
    (B₀ : Module.Basis E K (P ⧸ initialIdeal Q w))
    (hB₀ : ∀ e, B₀ e = Ideal.Quotient.mk _ (v e))
    (p : P) (d : ℕ)
    (hp : WeightBound (K := K) w d p) (e : E) (he : d<degree e) :
    (liftedInitialBasis (K := K) (σ := σ) (E := E) Q w v degree hv B₀ hB₀).repr
      ((Ideal.Quotient.mkₐ K Q).toLinearMap p) e=0 := by
  apply coefficient_eq_zero_of_bound (K := K) (M := P) (Q := P⧸Q)
    (Q₀ := P⧸initialIdeal Q w) (I := σ →₀ ℕ) (E := E) (basisMonomials σ K) (Finsupp.weight w)
    (Ideal.Quotient.mkₐ K Q).toLinearMap v
    (liftedInitialBasis (K := K) (σ := σ) (E := E) Q w v degree hv B₀ hB₀)
    (Ideal.Quotient.mkₐ K (initialIdeal Q w)).toLinearMap degree
    (fun i => (monomialBasis_homogeneous_iff w (degree i) (v i)).mpr (hv i))
    B₀ hB₀ p d
  · exact (monomialBasis_bound_iff w d _).mpr
      (liftedNormalForm_bound (K := K) (σ := σ) (E := E) Q w v degree hv B₀ hB₀ p d hp)
  · exact he

theorem lifted_top_coefficient
    (Q : Ideal P) (w : σ → ℕ) (v : E → P) (degree : E → ℕ)
    (hv : ∀ e, (v e).IsWeightedHomogeneous w (degree e))
    (B₀ : Module.Basis E K (P ⧸ initialIdeal Q w))
    (hB₀ : ∀ e, B₀ e = Ideal.Quotient.mk _ (v e))
    (p : P) (d : ℕ) (hp : WeightBound (K := K) w d p)
    (e : E) (he : degree e=d) :
    (liftedInitialBasis (K := K) (σ := σ) (E := E) Q w v degree hv B₀ hB₀).repr
      ((Ideal.Quotient.mkₐ K Q).toLinearMap p) e=
        B₀.repr ((Ideal.Quotient.mkₐ K (initialIdeal Q w)).toLinearMap
          (weightedHomogeneousComponent w d p)) e := by
  simpa only [monomialBasis_component] using
    top_coefficient_eq (K := K) (M := P) (Q := P⧸Q)
    (Q₀ := P⧸initialIdeal Q w) (I := σ →₀ ℕ) (E := E) (basisMonomials σ K) (Finsupp.weight w)
    (Ideal.Quotient.mkₐ K Q).toLinearMap v
    (liftedInitialBasis (K := K) (σ := σ) (E := E) Q w v degree hv B₀ hB₀)
    (Ideal.Quotient.mkₐ K (initialIdeal Q w)).toLinearMap
    (by
      intro x hx r hb
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [monomialBasis_component]
      exact component_mem_initialIdeal Q w x
        (Ideal.Quotient.eq_zero_iff_mem.mp hx) r
        ((monomialBasis_bound_iff w r x).mp hb))
    degree (fun i => (monomialBasis_homogeneous_iff w (degree i) (v i)).mpr (hv i))
    B₀ hB₀ (liftedInitialBasis_apply (K := K) (σ := σ) (E := E) Q w v degree hv B₀ hB₀) p d
    ((monomialBasis_bound_iff w d p).mpr hp)
    ((monomialBasis_bound_iff w d _).mpr
      (liftedNormalForm_bound (K := K) (σ := σ) (E := E) Q w v degree hv B₀ hB₀ p d hp)) e he

end PaperVerification.WeightedInitialFiber
