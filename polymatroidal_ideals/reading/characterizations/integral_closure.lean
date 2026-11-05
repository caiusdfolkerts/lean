import Characterizations.MonomialIntegrality
import Characterizations.SubsetWeights
import Characterizations.Projection

/-! # Theorem 2.11: exact integral closure and the integral-closure characterization -/

noncomputable section
namespace Characterizations
universe u
open Classical CommAlg CommAlg.Polymatroid Finset MvPolynomial
variable {V : Type u} [Fintype V] [DecidableEq V]

theorem canonicalLowerBase_mem_convexHull {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d)
    {a : Exponent V} (ha : a ∈ lowerBaseFamily (lowerRank B) d) :
    realExponent a ∈ convexHull ℝ (realExponent '' (B : Set (Exponent V))) := by
  rw [convexHull_generators_eq_lowerRankPolytope hB hanti hl hd]
  obtain ⟨hdeg, hlo⟩ := (mem_lowerBaseFamily _ _ a).mp ha
  refine ⟨fun i => Nat.cast_nonneg _, ?_, ?_⟩
  · rw [realSubsetSum_exponent, subsetSum_univ, hdeg]
  · intro U
    rw [realSubsetSum_exponent]
    exact_mod_cast hlo U

variable {k : Type*} [CommRing k] [IsDomain k]

theorem mem_canonicalLowerBases_integral {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d)
    {f : MvPolynomial V k} (hf : f ∈ monomialIdeal k (lowerBaseFamily (lowerRank B) d)) :
    IntegralOverIdeal (monomialIdeal k B) f := by
  apply integralOverIdeal_of_span_generators
    ((fun a : Exponent V => monomial a (1 : k)) ''
      (lowerBaseFamily (lowerRank B) d : Set (Exponent V))) ?_ hf
  rintro y ⟨a, ha, rfl⟩
  exact monomial_power_mem_of_convexHull k B a
    (canonicalLowerBase_mem_convexHull hB hanti hl hd ha)

/-- Every polynomial is integral over the original ideal exactly when it lies
in the full integer-base ideal. Both directions use ordinary monic equations. -/
theorem integralOverIdeal_iff_mem_canonicalLowerBases {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d)
    (f : MvPolynomial V k) :
    IntegralOverIdeal (monomialIdeal k B) f ↔
      f ∈ monomialIdeal k (lowerBaseFamily (lowerRank B) d) :=
  ⟨integral_mem_canonicalLowerBases hB hl hd,
    mem_canonicalLowerBases_integral hB hanti hl hd⟩

theorem integralClosure_set_eq {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d) :
    {f : MvPolynomial V k | IntegralOverIdeal (monomialIdeal k B) f} =
      (monomialIdeal k (lowerBaseFamily (lowerRank B) d) : Set (MvPolynomial V k)) := by
  ext f
  exact integralOverIdeal_iff_mem_canonicalLowerBases hB hanti hl hd f

/-- The full characterization, without assuming equigeneration separately. -/
theorem polymatroidal_iff_integrallyClosed_localEquigenerated {B : Family V}
    (hB : B.Nonempty) (hanti : Antichain B) :
    IsPolymatroidal B ↔ IsIntegrallyClosedIdeal (monomialIdeal k B) ∧
      LocallyEquigenerated B := by
  constructor
  · intro hp
    exact ⟨polymatroidal_integrallyClosed hB hp, polymatroidal_locallyEquigenerated hp⟩
  · rintro ⟨hc, hl⟩
    obtain ⟨d, hd⟩ := hl Finset.univ
    rw [localize_univ_of_antichain hanti] at hd
    have hcontains : ∀ a, Contains B a ↔ Contains (lowerBaseFamily (lowerRank B) d) a := by
      intro a
      rw [← monomial_mem_iff (k := k), ← monomial_mem_iff (k := k)]
      constructor
      · intro ha
        exact (integralOverIdeal_iff_mem_canonicalLowerBases hB hanti hl hd _).mp
          (integralOverIdeal_of_mem ha)
      · intro ha
        exact hc _ ((integralOverIdeal_iff_mem_canonicalLowerBases hB hanti hl hd _).mpr ha)
    have he := family_eq_of_contains_iff hanti
      (lowerBaseFamily_equigenerated (lowerRank B) d).antichain hcontains
    rw [he]
    exact canonicalLowerBases_polymatroidal hB hl hd

end Characterizations
