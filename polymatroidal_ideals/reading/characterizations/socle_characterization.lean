import Characterizations.Socles

/-! The full local-socle characterization, in the actual retained-variable quotient rings. -/
noncomputable section
namespace Characterizations
open CommAlg.Polymatroid MvPolynomial
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem localFamily_degree_of_locallyEquigenerated {B : Family V} (hB : B.Nonempty)
    (hl : LocallyEquigenerated B) (U : Finset V) :
    Equigenerated (localFamily B U) (lowerRank B U) := by
  intro a ha
  have he : extendExponent U a ∈ localize B U := by
    rw [localize_eq_extend_localFamily]
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  simpa only [extendExponent_degree] using localize_degree hB hl he

theorem restrict_add_single (U : Finset V) (a : Exponent V) (i : U) :
    restrictExponent U (a + Finsupp.single i.val 1) =
      restrictExponent U a + Finsupp.single i 1 := by
  ext j
  simp only [restrictExponent_apply, Finsupp.add_apply, Finsupp.single_apply]
  have he : i.val = j.val ↔ i = j := Subtype.ext_iff.symm
  simp only [he]

theorem restrict_degree_of_supported {U : Finset V} {a : Exponent V}
    (ha : project U a = a) : (restrictExponent U a).degree = a.degree := by
  rw [← extendExponent_degree U, extend_restrict, ha]

variable (k : Type*) [CommRing k] [Nontrivial k]

/-- Corollary 2.7, with ordinary polynomial quotient socles, including zero
socles and every nonzero monomial ideal. The field hypothesis can be weakened
to an arbitrary nontrivial commutative coefficient ring. -/
theorem polymatroidal_iff_local_socles {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) :
    IsPolymatroidal B ↔ LocallyEquigenerated B ∧
      ∀ U : Finset V, monomialIdeal k (localFamily B U) ≠ ⊤ →
        SocleConcentrated (monomialIdeal k (localFamily B U)) (lowerRank B U - 1) := by
  constructor
  · intro hp
    refine ⟨polymatroidal_locallyEquigenerated hp, ?_⟩
    intro U _
    exact polymatroidal_socleConcentrated (localFamily_nonempty hB U)
      (localFamily_polymatroidal hp U) (localFamily_equigenerated hp U)
  · rintro ⟨hl, hsoc⟩
    apply polymatroidal_of_local_socles hB hanti hl
    intro U a ha hout hmul
    have hout' : ¬ Contains (localFamily B U) (restrictExponent U a) :=
      fun h => hout ((contains_localize_iff B U a).mpr h)
    have hmul' : ∀ i : U, Contains (localFamily B U)
        (restrictExponent U a + Finsupp.single i 1) := by
      intro i
      rw [← restrict_add_single]
      exact (contains_localize_iff B U _).mp (hmul i i.property)
    have hproper : monomialIdeal k (localFamily B U) ≠ ⊤ := by
      intro he
      apply hout'
      apply (monomial_mem_iff (k := k) _ _).mp
      rw [he]
      trivial
    have hd := (socleConcentrated_iff (localFamily B U) (lowerRank B U - 1)).mp
      (hsoc U hproper) _ hout' hmul'
    have hpos : 0 < lowerRank B U := by
      by_contra hn
      have hr : lowerRank B U = 0 := Nat.eq_zero_of_not_pos hn
      obtain ⟨b, hb⟩ := localFamily_nonempty hB U
      have hb0 : b = 0 := (Finsupp.degree_eq_zero_iff b).mp
        ((localFamily_degree_of_locallyEquigenerated hB hl U b hb).trans hr)
      exact hout' ⟨b, hb, by simp [hb0]⟩
    rw [restrict_degree_of_supported ha] at hd
    omega

end Characterizations
