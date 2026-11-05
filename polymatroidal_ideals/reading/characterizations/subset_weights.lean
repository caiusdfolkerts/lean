import Characterizations.LowerBases
import CommAlg.IntegralClosure.Ideal

/-! # Literal subset-degree valuations and integral closure -/
noncomputable section
namespace Characterizations
open Classical CommAlg CommAlg.Polymatroid Finset MvPolynomial
variable {V : Type*} [Fintype V] [DecidableEq V]

def subsetWeight (U : Finset V) : V → ℤ := fun v => if v ∈ U then 1 else 0

theorem weight_subsetWeight (U : Finset V) (a : Exponent V) :
    Finsupp.weight (subsetWeight U) a = (subsetSum a U : ℤ) := by
  rw [Finsupp.weight_eq_sum]
  simp only [subsetWeight, nsmul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem]
  simp [subsetSum]

variable {k : Type*} [CommRing k]

theorem subsetWeight_nonnegative (U : Finset V) (f : MvPolynomial V k) :
    Weight.Bound (subsetWeight U) 0 f := by
  intro a _
  rw [weight_subsetWeight]
  positivity

theorem subsetWeight_bound_of_mem (B : Family V) {f : MvPolynomial V k}
    (hf : f ∈ monomialIdeal k B) (U : Finset V) :
    Weight.Bound (subsetWeight U) (lowerRank B U : ℤ) f := by
  intro a ha
  obtain ⟨b, hb, hba⟩ := (mem_monomialIdeal_iff B f).mp hf a (Finsupp.mem_support_iff.mpr ha)
  rw [weight_subsetWeight]
  exact_mod_cast (lowerRank_le hb U).trans (Finset.sum_le_sum (fun i _ => hba i))

theorem subsetWeight_bound_of_integral [IsDomain k] (B : Family V) {f : MvPolynomial V k}
    (hf : IntegralOverIdeal (monomialIdeal k B) f) (U : Finset V) :
    Weight.Bound (subsetWeight U) (lowerRank B U : ℤ) f :=
  Weight.bound_of_integral (RingHom.id _) (subsetWeight U) (subsetWeight_nonnegative U)
    (monomialIdeal k B) (lowerRank B U : ℤ)
    (fun _ h => subsetWeight_bound_of_mem B h U) hf

theorem integral_mem_canonicalLowerBases [IsDomain k] {B : Family V} (hB : B.Nonempty)
    (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d) {f : MvPolynomial V k}
    (hf : IntegralOverIdeal (monomialIdeal k B) f) :
    f ∈ monomialIdeal k (lowerBaseFamily (lowerRank B) d) := by
  apply (mem_monomialIdeal_iff _ f).mpr
  intro a ha
  apply (contains_canonicalLowerBases_iff hB hl hd a).mpr
  intro U
  have h := subsetWeight_bound_of_integral B hf U a (Finsupp.mem_support_iff.mp ha)
  rw [weight_subsetWeight] at h
  exact_mod_cast h

theorem polymatroidal_integrallyClosed [IsDomain k] {B : Family V} (hB : B.Nonempty)
    (hp : IsPolymatroidal B) : IsIntegrallyClosedIdeal (monomialIdeal k B) := by
  obtain ⟨d, hd⟩ := hp.1
  intro f hf
  apply (mem_monomialIdeal_iff _ f).mpr
  intro a ha
  apply (contains_iff_canonical_lower B hB d hd hp a).mpr
  intro U
  have h := subsetWeight_bound_of_integral B hf U a (Finsupp.mem_support_iff.mp ha)
  rw [weight_subsetWeight] at h
  exact_mod_cast h

end Characterizations
