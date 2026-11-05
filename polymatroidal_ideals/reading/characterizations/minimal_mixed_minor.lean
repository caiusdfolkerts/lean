import Characterizations.MixedMinors
import Characterizations.SupportedFamilies

/-! # A smallest non-polymatroidal mixed coordinate minor -/
noncomputable section
namespace Characterizations
open Classical CommAlg.Polymatroid Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem restriction_univ (B : Family V) : restriction B Finset.univ = B := by
  ext a
  simp

theorem mixedMinor_univ {B : Family V} (hB : Antichain B) :
    mixedMinor B Finset.univ Finset.univ = B := by
  rw [mixedMinor,restriction_univ,localize_univ_of_antichain hB]

theorem exists_minimal_bad_mixedMinor {B : Family V} (hB : B.Nonempty) (hanti : Antichain B)
    (hn : ¬ IsPolymatroidal B) :
    ∃ A U : Finset V, U ⊆ A ∧ (mixedMinor B A U).Nonempty ∧
      ¬ IsPolymatroidal (mixedMinor B A U) ∧
      (∀ W : Finset V, W ⊂ U → IsPolymatroidal (localize (mixedMinor B A U) W)) ∧
      (∀ W : Finset V, W ⊂ U → (restriction (mixedMinor B A U) W).Nonempty →
        IsPolymatroidal (restriction (mixedMinor B A U) W)) := by
  let bad : Finset (Finset V × Finset V) := Finset.univ.filter (fun p =>
    p.2 ⊆ p.1 ∧ (mixedMinor B p.1 p.2).Nonempty ∧ ¬IsPolymatroidal (mixedMinor B p.1 p.2))
  have hb : bad.Nonempty := by
    refine ⟨(Finset.univ,Finset.univ),Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_,?_⟩⟩
    · exact le_rfl
    · simpa only [mixedMinor_univ hanti] using hB
    · simpa only [mixedMinor_univ hanti] using hn
  obtain ⟨⟨A,U⟩,hp,hmin⟩ := bad.exists_minimalFor (fun p => p.2.card) hb
  obtain ⟨hUA,hL,hbad⟩ := (Finset.mem_filter.mp hp).2
  refine ⟨A,U,hUA,hL,hbad,?_,?_⟩
  · intro W hWU
    by_contra hnW
    have he : localize (mixedMinor B A U) W = mixedMinor B A W := by
      rw [localize_mixedMinor,Finset.inter_eq_right.mpr hWU.subset]
    have hnew : (A,W) ∈ bad := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,hWU.subset.trans hUA,?_,?_⟩
      · rw [← he]
        exact localize_nonempty hL W
      · rwa [← he]
    have hc := hmin hnew (Finset.card_le_card hWU.subset)
    change U.card ≤ W.card at hc
    have hc' := Finset.card_lt_card hWU
    omega
  · intro W hWU hR
    by_contra hnW
    have hWA : W ⊆ A ∩ (W ∪ Uᶜ) := by
      intro i hi
      exact Finset.mem_inter.mpr ⟨hUA (hWU.subset hi),Finset.mem_union_left _ hi⟩
    have he := restriction_mixedMinor B hUA hWU.subset
    have hnew : (A ∩ (W ∪ Uᶜ),W) ∈ bad := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,hWA,?_,?_⟩
      · rwa [← he]
      · rwa [← he]
    have hc := hmin hnew (Finset.card_le_card hWU.subset)
    change U.card ≤ W.card at hc
    have hc' := Finset.card_lt_card hWU
    omega

/-- A missing integral generator in a restriction-minimal obstruction uses
every retained variable. This is the degree-versus-dimension step in 4.2. -/
theorem missing_base_full_support {L : Family V} (hL : L.Nonempty)
    (hl : LocallyEquigenerated L) {e : ℕ} (he : Equigenerated L e) (U : Finset V)
    (hs : ∀ b ∈ L, project U b = b)
    (hrest : ∀ W : Finset V, W ⊂ U → (restriction L W).Nonempty →
      IsPolymatroidal (restriction L W))
    {a : Exponent V} (ha : a ∈ lowerBaseFamily (lowerRank L) e) (hout : ¬Contains L a) :
    a.support = U := by
  have haU := lowerBase_supported hL he U hs ha
  have hsub := (project_eq_self_iff_support_subset a U).mp haU
  by_contra hne
  have hproper : a.support ⊂ U := hsub.ssubset_of_ne hne
  have haA : project a.support a = a := (project_eq_self_iff_support_subset _ _).mpr le_rfl
  have hlo := ((mem_lowerBaseFamily _ _ _).mp ha).2
  have hsumzero : subsetSum a a.supportᶜ = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact Finsupp.notMem_support_iff.mp (Finset.mem_compl.mp hi)
  have hrzero : lowerRank L a.supportᶜ = 0 := Nat.eq_zero_of_le_zero (hsumzero ▸ hlo a.supportᶜ)
  obtain ⟨b,hb,hmin⟩ := lowerRank_attained hL a.supportᶜ
  have hbA : project a.support b = b := supported_of_subsetSum_compl_zero (hmin.trans hrzero)
  have hK : (restriction L a.support).Nonempty := ⟨b,mem_restriction.mpr ⟨hb,hbA⟩⟩
  have hpK := hrest a.support hproper hK
  have hdegK := restriction_equigenerated he a.support
  have hfeas : LowerFeasible (lowerRank (restriction L a.support)) a := by
    intro W
    rw [lowerRank_supported_inter hK a.support (fun c hc => (mem_restriction.mp hc).2),
      restriction_lowerRank hl hK Finset.inter_subset_right]
    have hh := hlo ((W ∩ a.support) ∪ a.supportᶜ)
    have hsum : subsetSum a ((W ∩ a.support) ∪ a.supportᶜ) = subsetSum a W := by
      rw [subsetSum_supported_inter haA]
      have hset : ((W ∩ a.support) ∪ a.supportᶜ) ∩ a.support = W ∩ a.support := by
        ext i
        simp only [Finset.mem_inter,Finset.mem_union,Finset.mem_compl]
        tauto
      rw [hset,← subsetSum_supported_inter haA W]
    rwa [hsum] at hh
  have hcontains := (contains_iff_canonical_lower _ hK e hdegK hpK a).mpr hfeas
  obtain ⟨c,hc,hca⟩ := hcontains
  exact hout ⟨c,restriction_subset L a.support hc,hca⟩

theorem degree_ge_support_card (a : Exponent V) : a.support.card ≤ a.degree := by
  calc
    a.support.card = ∑ i ∈ a.support, 1 := by simp
    _ ≤ subsetSum a a.support := Finset.sum_le_sum (fun i hi =>
      Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))
    _ ≤ a.degree := by
      simpa only [degree_project] using degree_mono (project_le a.support a)

end Characterizations
