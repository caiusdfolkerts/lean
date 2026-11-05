import Characterizations.MinimalMixedMinor
import Characterizations.Strands.SocleTor
import Characterizations.Strands.DeletedBetti

/-! # Every failure has a genuine nonlinear Tor class in the degree-bounded range -/
noncomputable section
namespace Characterizations
open Classical CommAlg.Polymatroid CommAlg.Koszul CommAlg.Simplicial Finset
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

theorem betti_restriction_sameambient (B : Family V) (U : Finset V) (a : Exponent V)
    (ha : project U a = a) (i : ℕ) :
    bettiNumber (k := k) (restriction B U) a i = bettiNumber (k := k) B a i := by
  have hfaces : koszulFaces (restriction B U) a = koszulFaces B a := by
    funext s
    apply propext
    change (faceExponent s ≤ a ∧ Contains (restriction B U) (a-faceExponent s)) ↔ _
    rw [contains_restriction]
    have hs := supported_of_le ha (tsub_le_self : a-faceExponent s ≤ a)
    rw [hs]
    rfl
  rw [Strands.bettiNumber_eq_face_homology_finrank,Strands.bettiNumber_eq_face_homology_finrank,
    Strands.chainComplex_congr (koszulFaces_downward _ _) (koszulFaces_downward _ _) hfaces]

theorem relative_socle_above_missing_base {L : Family V} (hL : L.Nonempty)
    (U : Finset V) (hs : ∀ c ∈ L, project U c = c)
    (hloc : ∀ W : Finset V, W ⊂ U → IsPolymatroidal (localize L W))
    {a : Exponent V} (ha : LowerFeasible (lowerRank L) a)
    (has : project U a = a) (hout : ¬Contains L a) :
    ∃ b, a ≤ b ∧ project U b = b ∧ ¬Contains L b ∧
      ∀ i ∈ U, Contains L (b+Finsupp.single i 1) := by
  apply exists_socle_above L U a has hout
  intro i hi
  have hgood := lowerFeasible_project_mem hL ha (U.erase i)
    (hloc _ (Finset.erase_ssubset hi))
  obtain ⟨c,hc,hca⟩ := (contains_localize L (U.erase i) _).mp hgood
  refine ⟨c i,c,hc,?_⟩
  intro j
  by_cases hji : j = i
  · subst j; simp
  · by_cases hjU : j ∈ U
    · have hjE : j ∈ U.erase i := Finset.mem_erase.mpr ⟨hji,hjU⟩
      have hh := hca j
      simpa only [project_apply,if_pos hjE,Finsupp.add_apply,Finsupp.single_apply,
        if_neg (Ne.symm hji),add_zero] using hh
    · have hz := congrArg (fun x : Exponent V => x j) (hs c hc)
      simp only [project_apply,if_neg hjU] at hz
      rw [← hz]
      exact Nat.zero_le _

/-- The obstruction underlying Theorems4.2 and4.9. All Betti numbers are the
actual numerical dimensions of the derived Tor components in the ambient ring;
the exhibited degree is supported on the retained localization coordinates. -/
theorem exists_low_nonlinear_localization {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) (hl : LocallyEquigenerated B) (hn : ¬IsPolymatroidal B) :
    ∃ (U : Finset V) (e i : ℕ) (a : Exponent V),
      Equigenerated (localize B U) e ∧ lowerRank B U = e ∧ 2 ≤ U.card ∧
      1 ≤ i ∧ i ≤ e-1 ∧ i ≤ U.card-1 ∧ a.support ⊆ U ∧
      e+i < a.degree ∧ bettiNumber (k := k) (localize B U) a i ≠ 0 := by
  obtain ⟨A,U,hUA,hL,hnL,hloc,hrest⟩ := exists_minimal_bad_mixedMinor hB hanti hn
  let L := mixedMinor B A U
  have hantiL : Antichain L := localize_antichain _ _
  have hlL : LocallyEquigenerated L := mixedMinor_locallyEquigenerated hl A U
  obtain ⟨e,he⟩ := hlL Finset.univ
  rw [localize_univ_of_antichain hantiL] at he
  have hs : ∀ c ∈ L, project U c = c := fun c hc => localize_supported hc
  have hcard : 2 ≤ U.card := by
    by_contra h
    exact hnL (supported_equigenerated_polymatroidal_card_le_one he U hs (by omega))
  have hnot : ¬ lowerBaseFamily (lowerRank L) e ⊆ L := by
    intro h
    have hEq : L = lowerBaseFamily (lowerRank L) e :=
      Finset.Subset.antisymm (subset_lowerBaseFamily he) h
    apply hnL
    change IsPolymatroidal L
    rw [hEq]
    exact canonicalLowerBases_polymatroidal hL hlL he
  obtain ⟨a,haJ,haL⟩ := Finset.not_subset.mp hnot
  obtain ⟨hade,hafeas⟩ := (mem_lowerBaseFamily _ _ _).mp haJ
  have hout : ¬Contains L a := fun h => haL ((he.mem_iff_contains hade).mpr h)
  have hsupp : a.support = U := missing_base_full_support hL hlL he U hs hrest haJ hout
  have hUe : U.card ≤ e := by simpa only [hsupp,hade] using degree_ge_support_card a
  have has : project U a = a := lowerBase_supported hL he U hs haJ
  obtain ⟨b,hab,hbs,hbout,hmul⟩ := relative_socle_above_missing_base hL U hs hloc hafeas has hout
  let α := b+faceExponent U
  have hα : project U α = α := by
    dsimp [α]
    rw [project_add,hbs]
    congr 1
    ext j
    simp only [project_apply,faceExponent_apply]
    split_ifs <;> rfl
  have hβ : bettiNumber (k := k) L α (U.card-1) = 1 :=
    Strands.relative_socle_bettiNumber_eq_one L b U
      ((project_eq_self_iff_support_subset b U).mp hbs) hbout hmul _ (by omega)
  have hαdegree : e+(U.card-1) < α.degree := by
    have hdeg := degree_mono hab
    rw [hade] at hdeg
    dsimp [α]
    rw [map_add,Strands.degree_faceExponent]
    omega
  let T := U ∪ Aᶜ
  have hUT : U ⊆ T := Finset.subset_union_left
  have hTdegree : lowerRank B T = e := by
    have h := mixedMinor_lowerRank hl hL hUA (Finset.Subset.refl U)
    rw [lowerRank_on_support hL he U hs] at h
    exact h.symm
  have hTgen : Equigenerated (localize B T) e := by
    intro c hc
    exact (localize_degree hB hl hc).trans hTdegree
  have hLeq : L = restriction (localize B T) U := localize_restriction B hUA
  have hβT : bettiNumber (k := k) (localize B T) α (U.card-1) = 1 := by
    rw [hLeq,betti_restriction_sameambient _ U α hα] at hβ
    exact hβ
  refine ⟨T,e,U.card-1,α,hTgen,hTdegree,?_,by omega,by omega,?_,?_,hαdegree,?_⟩
  · exact hcard.trans (Finset.card_le_card hUT)
  · have h := Finset.card_le_card hUT
    omega
  · exact ((project_eq_self_iff_support_subset α U).mp hα).trans hUT
  · rw [hβT]
    exact one_ne_zero

end Characterizations
