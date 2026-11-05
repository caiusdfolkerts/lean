module

public import PaperVerification.WeightedInitialFiber
public import PaperVerification.FilteredBasisTransfer
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Lifting a full homogeneous basis through the actual initial ideal

The special-fiber kernel identity supplies an actual bounded relation for
every component of every initial relation. Thus a homogeneous basis of the
initial quotient lifts to the same representatives in the original quotient.
The index type may be infinite, and neither finite dimension nor preservation
of a chosen basis under arbitrary flat specialization is assumed.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.WeightedInitialFiber

open MvPolynomial

variable {K σ E : Type*} [Field K]
local notation "P" => MvPolynomial σ K

/-- Every component of an element of the full conventional initial ideal
has a bounded lift in the actual original ideal. The lift is obtained from
the proved Rees kernel coefficient identity. -/
theorem initial_component_lift (Q : Ideal P) (w : σ → ℕ)
    (p : P) (hp : p∈initialIdeal Q w) (d : ℕ) :
    ∃ a∈Q,WeightBound w d a ∧
      weightedHomogeneousComponent w d a=weightedHomogeneousComponent w d p := by
  have hp0 : specialMap Q w p=0 := initialIdeal_le_specialKernel Q w hp
  change fiberMap Q w (reesCover Q w (Polynomial.C p))=0 at hp0
  have hspan : reesCover Q w (Polynomial.C p)∈
      Ideal.span ({reesParameter Q w} : Set (reesAlgebra Q w)) :=
    Ideal.Quotient.eq_zero_iff_mem.mp hp0
  obtain ⟨a,ha⟩ := Ideal.mem_span_singleton'.mp hspan
  obtain ⟨g,hg⟩ := reesCover_surjective Q w a
  let H : Polynomial P := Polynomial.C p-Polynomial.X*g
  have hcover : reesCover Q w H=0 := by
    change reesCover Q w (Polynomial.C p-Polynomial.X*g)=0
    rw [map_sub,map_mul]
    change reesCover Q w (Polynomial.C p)-reesParameter Q w*reesCover Q w g=0
    rw [hg,mul_comm (reesParameter Q w) a,ha,sub_self]
  have hH : reesMap Q w H=0 := congrArg Subtype.val hcover
  have hconstant : H.coeff 0=p := by
    simp only [H,Polynomial.coeff_sub,Polynomial.coeff_C_zero,
      Polynomial.coeff_X_mul_zero,sub_zero]
  refine ⟨coefficientLift w H d,coefficientLift_mem_of_reesMap_zero Q w H hH d,
    coefficientLift_bound w H d,?_⟩
  rw [coefficientLift_top,hconstant]

theorem initialIdeal_component_mem (Q : Ideal P) (w : σ → ℕ)
    (p : P) (hp : p∈initialIdeal Q w) (d : ℕ) :
    weightedHomogeneousComponent w d p∈initialIdeal Q w := by
  obtain ⟨a,ha,hb,ht⟩ := initial_component_lift Q w p hp d
  rw [←ht]
  exact component_mem_initialIdeal Q w a ha d hb

theorem monomialBasis_component (w : σ → ℕ) (d : ℕ) (p : P) :
    Fermion.BasisFiltered.component (basisMonomials σ K) (Finsupp.weight w) d p=
      weightedHomogeneousComponent w d p := by
  ext a
  change (basisMonomials σ K).repr
    (Fermion.BasisFiltered.component (basisMonomials σ K) (Finsupp.weight w) d p) a=_
  rw [Fermion.BasisFiltered.repr_component,coeff_weightedHomogeneousComponent]
  rfl

theorem monomialBasis_bound_iff (w : σ → ℕ) (d : ℕ) (p : P) :
    Fermion.BasisFiltered.Bound (basisMonomials σ K) (Finsupp.weight w) d p ↔
      WeightBound w d p := Iff.rfl

theorem monomialBasis_homogeneous_iff (w : σ → ℕ) (d : ℕ) (p : P) :
    Fermion.BasisFiltered.Homogeneous (basisMonomials σ K) (Finsupp.weight w) d p ↔
      p.IsWeightedHomogeneous w d := Iff.rfl

/-- A complete homogeneous initial-quotient basis yields a complete basis
of the original quotient with the very same polynomial representatives. -/
def liftedInitialBasis (Q : Ideal P) (w : σ → ℕ)
    (v : E → P) (degree : E → ℕ)
    (hv : ∀ e,(v e).IsWeightedHomogeneous w (degree e))
    (B₀ : Module.Basis E K (P⧸initialIdeal Q w))
    (hB₀ : ∀ e,B₀ e=Ideal.Quotient.mk _ (v e)) :
    Module.Basis E K (P⧸Q) :=
  FilteredBasisTransfer.basis (basisMonomials σ K) (Finsupp.weight w)
    (Ideal.Quotient.mkₐ K Q).toLinearMap
    (Ideal.Quotient.mkₐ K (initialIdeal Q w)).toLinearMap
    (Ideal.Quotient.mkₐ_surjective K Q)
    (Ideal.Quotient.mkₐ_surjective K (initialIdeal Q w))
    (by
      intro p hp d hb
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [monomialBasis_component]
      exact component_mem_initialIdeal Q w p
        (Ideal.Quotient.eq_zero_iff_mem.mp hp) d hb)
    (by
      intro p hp d
      obtain ⟨a,ha,hb,ht⟩ := initial_component_lift Q w p
        (Ideal.Quotient.eq_zero_iff_mem.mp hp) d
      exact ⟨a,Ideal.Quotient.eq_zero_iff_mem.mpr ha,hb,
        by simpa only [monomialBasis_component] using ht⟩)
    v degree (fun e => (monomialBasis_homogeneous_iff w (degree e) (v e)).mpr (hv e))
    B₀ hB₀

@[simp] theorem liftedInitialBasis_apply (Q : Ideal P) (w : σ → ℕ)
    (v : E → P) (degree : E → ℕ)
    (hv : ∀ e,(v e).IsWeightedHomogeneous w (degree e))
    (B₀ : Module.Basis E K (P⧸initialIdeal Q w))
    (hB₀ : ∀ e,B₀ e=Ideal.Quotient.mk _ (v e)) (e : E) :
    liftedInitialBasis Q w v degree hv B₀ hB₀ e=Ideal.Quotient.mk Q (v e) := by
  exact FilteredBasisTransfer.basis_apply _ _ _ _ _ _ _ _ _ _ _ _ _ e

end PaperVerification.WeightedInitialFiber
