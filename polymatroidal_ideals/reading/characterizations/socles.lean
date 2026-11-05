import Characterizations.Projection
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-! # Actual quotient socles and the local-socle characterization

The socle is the subspace of the actual quotient ring annihilated by every
variable. Concentration means that every such class has a homogeneous
representative of the specified degree. The equivalence with the monomial
test is proved, rather than used as a definition of the socle.
-/

noncomputable section
namespace Characterizations
open CommAlg.Polymatroid MvPolynomial
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {k : Type*} [CommRing k] [Nontrivial k]

def quotientSocle (I : Ideal (MvPolynomial V k)) : Set (MvPolynomial V k ⧸ I) :=
  {q | ∀ i : V, Ideal.Quotient.mk I (X i) * q = 0}

def SocleConcentrated (I : Ideal (MvPolynomial V k)) (d : ℕ) : Prop :=
  ∀ q ∈ quotientSocle I, ∃ f : MvPolynomial V k,
    f.IsHomogeneous d ∧ Ideal.Quotient.mk I f = q

theorem monomial_quotientSocle_iff (B : Family V) (a : Exponent V) :
    Ideal.Quotient.mk (monomialIdeal k B) (monomial a (1 : k)) ∈
      quotientSocle (monomialIdeal k B) ↔
      ∀ i : V, Contains B (a + Finsupp.single i 1) := by
  simp only [quotientSocle, Set.mem_setOf_eq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem]
  have he : ∀ i : V, (X i : MvPolynomial V k) * monomial a 1 =
      monomial (a + Finsupp.single i 1) 1 := by
    intro i
    rw [X, monomial_mul]
    simp [add_comm]
  simp only [he, monomial_mem_iff]

/-- A complete bridge from the actual quotient socle to monomial degrees. -/
theorem socleConcentrated_iff (B : Family V) (d : ℕ) :
    SocleConcentrated (monomialIdeal k B) d ↔
      ∀ a : Exponent V, ¬ Contains B a →
        (∀ i : V, Contains B (a + Finsupp.single i 1)) → a.degree = d := by
  classical
  constructor
  · intro h a ha hsoc
    obtain ⟨f, hf, heq⟩ := h _ ((monomial_quotientSocle_iff B a).mpr hsoc)
    have hmem := Ideal.Quotient.eq.mp heq
    have ha0 : (f - monomial a 1).coeff a = 0 := by
      by_contra hn
      exact ha ((mem_monomialIdeal_iff B _).mp hmem a (mem_support_iff.mpr hn))
    have hfa : f.coeff a ≠ 0 := by
      simp only [coeff_sub, coeff_monomial, ↓reduceIte] at ha0
      intro hz
      rw [hz] at ha0
      simpa using ha0
    simpa only [← Finsupp.degree_apply] using
      (hf.degree_eq_sum_deg_support (mem_support_iff.mpr hfa)).symm
  · intro h q hq
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
    have hvar : ∀ i : V, X i * f ∈ monomialIdeal k B := by
      intro i
      exact Ideal.Quotient.eq_zero_iff_mem.mp (by
        rw [map_mul]
        exact hq i)
    have hdegree : ∀ a ∈ f.support, ¬ Contains B a → a.degree = d := by
      intro a ha hout
      apply h a hout
      intro i
      apply (mem_monomialIdeal_iff B _).mp (hvar i)
      rw [add_comm a]
      exact mem_support_iff.mpr (by simpa using mem_support_iff.mp ha)
    refine ⟨homogeneousComponent d f, homogeneousComponent_isHomogeneous d f, ?_⟩
    apply Ideal.Quotient.eq.mpr
    apply (mem_monomialIdeal_iff B _).mpr
    intro a ha
    by_contra hout
    have hn := mem_support_iff.mp ha
    have hfa : f.coeff a ≠ 0 := by
      intro hz
      simp [coeff_sub, coeff_homogeneousComponent, hz] at hn
    have hd := hdegree a (mem_support_iff.mpr hfa) hout
    simp [coeff_sub, coeff_homogeneousComponent, hd] at hn

theorem polymatroidal_monomial_socle_degree {B : Family V} (hBne : B.Nonempty)
    (hB : IsPolymatroidal B) {d : ℕ} (hdeg : Equigenerated B d)
    {a : Exponent V} (hout : ¬ Contains B a)
    (hsoc : ∀ i : V, Contains B (a + Finsupp.single i 1)) : a.degree + 1 = d := by
  classical
  have hrep := contains_iff_canonical_lower B hBne d hdeg hB
  have hbad : ¬ LowerFeasible (lowerRank B) a := fun h => hout ((hrep a).mpr h)
  simp only [LowerFeasible, not_forall, not_le] at hbad
  obtain ⟨U, hU⟩ := hbad
  have hUtop : U = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    by_contra hi
    have h := (hrep _).mp (hsoc i) U
    have he : subsetSum (a + Finsupp.single i 1) U = subsetSum a U := by
      simp [subsetSum, Finset.sum_add_distrib, Finsupp.single_apply, hi]
    rw [he] at h
    omega
  have htop : lowerRank B Finset.univ = d := by
    obtain ⟨b, hb, he⟩ := lowerRank_attained hBne Finset.univ
    simpa only [subsetSum_univ, hdeg b hb] using he.symm
  rw [hUtop, subsetSum_univ, htop] at hU
  have hne : Nonempty V := by
    by_contra hn
    haveI : IsEmpty V := not_nonempty_iff.mp hn
    have he : (Finset.univ : Finset V) = ∅ := Finset.univ_eq_empty
    rw [he, lowerRank_empty] at htop
    omega
  let i : V := Classical.choice hne
  obtain ⟨b, hb, hba⟩ := hsoc i
  have hlo := degree_mono hba
  simp only [map_add, Finsupp.degree_single, hdeg b hb] at hlo
  omega

theorem polymatroidal_socleConcentrated {B : Family V} (hBne : B.Nonempty)
    (hB : IsPolymatroidal B) {d : ℕ} (hdeg : Equigenerated B d) :
    SocleConcentrated (monomialIdeal k B) (d - 1) := by
  rw [socleConcentrated_iff]
  intro a ha hs
  have h := polymatroidal_monomial_socle_degree hBne hB hdeg ha hs
  omega

end Characterizations
