import Characterizations.Regularity
import Characterizations.Strands.FiniteLength

/-! # Proposition 4.1 with the actual integral closure and actual finite-length quotient -/
noncomputable section
namespace Characterizations
open Classical CommAlg CommAlg.Polymatroid Finset
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

theorem thickening_zero (B : Family V) : thickening B 0 = B := by
  ext a
  constructor
  · intro ha
    obtain ⟨⟨b,c⟩,hbc,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hb,hc⟩ := Finset.mem_product.mp hbc
    have hc0 : c = 0 := (Finsupp.degree_eq_zero_iff c).mp ((mem_degreeFamily 0 c).mp hc)
    simpa only [hc0,add_zero] using hb
  · intro ha
    exact Finset.mem_image.mpr ⟨(a,0),Finset.mem_product.mpr ⟨ha,by simp⟩,by simp⟩

theorem minimal_local_closure_finiteLength {B : Family V} (hB : B.Nonempty) {d : ℕ}
    (hd : Equigenerated B d)
    (hloc : ∀ U : Finset V, U ⊂ Finset.univ → IsPolymatroidal (localize B U)) :
    IsPolymatroidal (lowerBaseFamily (lowerRank B) d) ∧
      monomialIdeal k B ≤ monomialIdeal k (lowerBaseFamily (lowerRank B) d) ∧
      ({f : MvPolynomial V k | IntegralOverIdeal (monomialIdeal k B) f} =
        (monomialIdeal k (lowerBaseFamily (lowerRank B) d) : Set (MvPolynomial V k))) ∧
      IsFiniteLength (MvPolynomial V k)
        (Strands.idealDifferenceQuotient (k := k) B (lowerBaseFamily (lowerRank B) d)) := by
  have hl := locallyEquigenerated_of_proper_polymatroidal hd hloc
  refine ⟨canonicalLowerBases_polymatroidal hB hl hd,?_,
    integralClosure_set_eq hB hd.antichain hl hd,?_⟩
  · apply Ideal.span_mono
    rintro f ⟨a,ha,rfl⟩
    exact ⟨a,subset_lowerBaseFamily hd ha,rfl⟩
  · apply Strands.idealDifferenceQuotient_finiteLength
    have he : {a : Exponent V | Contains (lowerBaseFamily (lowerRank B) d) a ∧ ¬Contains B a} =
        holeSet B := by
      ext a
      simp only [Set.mem_setOf_eq,contains_canonicalLowerBases_iff hB hl hd,holeSet]
    rw [he]
    exact holeSet_finite hB hd hloc

/-- The "in particular" statement in4.1, including the integrally closed case
where the least power and regularity difference are both zero. -/
theorem least_polymatroidal_power_eq_regularity_difference {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d)
    (hloc : ∀ U : Finset V, U ⊂ Finset.univ → IsPolymatroidal (localize B U)) :
    ∃ r : ℕ, IsTorRegularity (k := k) B r ∧
      IsLeast {q : ℕ | IsPolymatroidal (thickening B q)} (r-d) := by
  by_cases hclosed : B = lowerBaseFamily (lowerRank B) d
  · have hl := locallyEquigenerated_of_proper_polymatroidal hd hloc
    have hp : IsPolymatroidal B := by
      conv_rhs => rw [hclosed]
      exact canonicalLowerBases_polymatroidal hB hl hd
    refine ⟨d,polymatroidal_torRegularity hB hd hp,?_⟩
    simp only [Nat.sub_self]
    exact ⟨by simpa only [Set.mem_setOf_eq,thickening_zero] using hp,fun _ _ => Nat.zero_le _⟩
  · obtain ⟨t,ht,hmax,hdt,hreg,hq⟩ := minimal_local_obstruction (k := k) hB hd hloc hclosed
    exact ⟨t+1,hreg,hq⟩

end Characterizations
