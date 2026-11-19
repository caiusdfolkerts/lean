module

public import PaperVerification.WeightedInitialBasis
public import PaperVerification.FermionWeightedLeading
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Tactic.Ring

/-!
# Primality descends from an actual weighted initial ideal

Every nonzero original quotient class admits a bounded representative whose
highest bounded component survives in the actual initial quotient.  The proof
repeatedly subtracts a bounded original relation supplied by the established
Rees-kernel lifting theorem, decreasing a natural-number bound.  The top
component of a product is the product of the top components.  Consequently a
prime actual initial ideal forces the original ideal itself to be prime.

The final general lemma states saturation in its ordinary ideal-power form.
It rules out irrelevant-supported torsion when applied to a homogeneous prime
ideal which does not contain the irrelevant ideal.  No primality or saturation
of the original ideal is assumed in the weighted theorem.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.WeightedInitialFiber

open MvPolynomial
open scoped BigOperators

variable {K σ : Type*} [Field K]
local notation "P" => MvPolynomial σ K

/-- Lift an initial component as an actual bounded original relation. -/
theorem top_component_lift (Q : Ideal P) (w : σ → ℕ)
    (p : P) (d : ℕ)
    (hp : weightedHomogeneousComponent w d p∈initialIdeal Q w) :
    ∃ a∈Q,WeightBound w d a ∧
      weightedHomogeneousComponent w d a=weightedHomogeneousComponent w d p := by
  obtain ⟨a,ha,hb,ht⟩ := initial_component_lift Q w
    (weightedHomogeneousComponent w d p) hp d
  refine ⟨a,ha,hb,?_⟩
  simpa only [weightedHomogeneousComponent_eq_self
    (weightedHomogeneousComponent_isWeightedHomogeneous d p)] using ht

/-- Natural-number descent gives a genuine representative with surviving top
component for every nonzero original quotient class. -/
theorem bounded_representative_top_not_mem_initialIdeal
    (Q : Ideal P) (w : σ → ℕ) (d : ℕ) (p : P)
    (hp : WeightBound w d p) (hne : p∉Q) :
    ∃ (e : ℕ) (r : P), e≤d ∧ r-p∈Q ∧ WeightBound w e r ∧
      weightedHomogeneousComponent w e r∉initialIdeal Q w := by
  classical
  induction d generalizing p with
  | zero =>
      refine ⟨0,p,le_rfl,?_,hp,?_⟩
      · simpa only [sub_self] using Q.zero_mem
      · intro ht
        obtain ⟨a,ha,hb,he⟩ := top_component_lift Q w p 0 ht
        have hp0 : weightedHomogeneousComponent w 0 p=p := by
          simpa only [Nat.zero_add,Finset.sum_range_one] using
            sum_components_of_bound w p 0 hp
        have ha0 : weightedHomogeneousComponent w 0 a=a := by
          simpa only [Nat.zero_add,Finset.sum_range_one] using
            sum_components_of_bound w a 0 hb
        have hap : a=p := by simpa only [ha0,hp0] using he
        exact hne (hap ▸ ha)
  | succ d ih =>
      by_cases ht : weightedHomogeneousComponent w (d+1) p∈initialIdeal Q w
      · obtain ⟨a,ha,hb,he⟩ := top_component_lift Q w p (d+1) ht
        have hsub : Fermion.Filtered.Bound w (d+1) (p-a) :=
          Fermion.Filtered.bound_sub w hp hb
        have htop : weightedHomogeneousComponent w (d+1) (p-a)=0 := by
          rw [map_sub,he,sub_self]
        have hs := Fermion.Filtered.strict_of_bound_component_zero w hsub htop
        have hb' : WeightBound w d (p-a) := by
          intro m hm
          exact Nat.lt_succ_iff.mp (hs m hm)
        have hne' : p-a∉Q := by
          intro h
          exact hne (by simpa only [sub_add_cancel] using Q.add_mem h ha)
        obtain ⟨e,r,hed,hr,hrb,hrt⟩ := ih (p-a) hb' hne'
        refine ⟨e,r,hed.trans (Nat.le_succ d),?_,hrb,hrt⟩
        convert Q.sub_mem hr ha using 1 <;> ring
      · exact ⟨d+1,p,le_rfl,by simpa only [sub_self] using Q.zero_mem,hp,ht⟩

/-- A prime conventional weighted initial ideal makes the original ideal
prime, for arbitrary nonnegative weights and any variable type. -/
theorem isPrime_of_initialIdeal_isPrime (Q : Ideal P) (w : σ → ℕ)
    (hprime : (initialIdeal Q w).IsPrime) : Q.IsPrime := by
  classical
  refine ⟨?_,?_⟩
  · intro hQ
    have h1 : (1 : P)∈Q := by rw [hQ]; trivial
    have hb : WeightBound w 0 (1 : P) :=
      fun m hm ↦ (isWeightedHomogeneous_one K w hm).le
    have ht := component_mem_initialIdeal Q w 1 h1 0 hb
    rw [weightedHomogeneousComponent_eq_self (isWeightedHomogeneous_one K w)] at ht
    exact hprime.one_notMem ht
  · intro p q hpq
    by_cases hp : p∈Q
    · exact Or.inl hp
    by_cases hq : q∈Q
    · exact Or.inr hq
    obtain ⟨a,r,ha,hr,hrb,hrt⟩ := bounded_representative_top_not_mem_initialIdeal
      Q w (weightedTotalDegree w p) p (weightBound_total w p) hp
    obtain ⟨b,s,hb,hs,hsb,hst⟩ := bounded_representative_top_not_mem_initialIdeal
      Q w (weightedTotalDegree w q) q (weightBound_total w q) hq
    have hrs : r*s∈Q := by
      convert Q.add_mem (Q.add_mem (Q.mul_mem_right s hr) (Q.mul_mem_left p hs)) hpq
        using 1 <;> ring
    have hmul := component_mem_initialIdeal Q w (r*s) hrs (a+b)
      (Fermion.Filtered.bound_mul w hrb hsb)
    rw [Fermion.Filtered.component_mul_top w hrb hsb] at hmul
    exact False.elim ((hprime.mul_notMem hrt hst) hmul)

section Saturation

variable {R : Type*} [CommRing R]

/-- The ordinary saturation condition `Q : J^∞ = Q`, stated with ideal powers
so that no auxiliary saturation convention or finiteness premise is hidden. -/
def IsSaturatedWithRespectTo (Q J : Ideal R) : Prop :=
  ∀ f : R, (∃ m : ℕ, ∀ g∈J^m,g*f∈Q) ↔ f∈Q

/-- A prime ideal not containing J is saturated with respect to J. -/
theorem isSaturatedWithRespectTo_of_isPrime (Q J : Ideal R)
    (hprime : Q.IsPrime) (hJ : ¬J≤Q) : IsSaturatedWithRespectTo Q J := by
  classical
  have hex : ∃ x : R,x∈J ∧ x∉Q := by
    by_contra h
    apply hJ
    intro x hx
    by_contra hxQ
    exact h ⟨x,hx,hxQ⟩
  obtain ⟨x,hx,hxQ⟩ := hex
  intro f
  constructor
  · rintro ⟨m,hm⟩
    have hp := hm (x^m) (Ideal.pow_mem_pow hx m)
    rcases hprime.mem_or_mem hp with hpow | hf
    · exact False.elim (hxQ (hprime.mem_of_pow_mem m hpow))
    · exact hf
  · intro hf
    exact ⟨0,fun g _ ↦ Q.mul_mem_left g hf⟩

end Saturation
end PaperVerification.WeightedInitialFiber
