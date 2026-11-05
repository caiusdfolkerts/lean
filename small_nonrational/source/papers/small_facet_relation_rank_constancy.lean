module
public import Papers.FourPolygonRank

@[expose] public section
noncomputable section

open Matrix Module Set
open scoped BigOperators

namespace Papers.RationalityTen.ChirotopeDensity

/-- The geometric span facts for the polygon faces of a three-dimensional
facet. The same finite supports may be used with different realizations. -/
structure FacetPolygonSpans {n r : ℕ} (p : Fin n → Fin r → ℝ)
    (F : Finset (Fin n)) (L : Finset (Finset (Fin n))) : Prop where
  facet_rank : subsetRank p F = 4
  subset : ∀ S ∈ L, S ⊆ F
  polygon_rank : ∀ S ∈ L, subsetRank p S = 3
  pair_rank : ∀ S ∈ L, ∀ T ∈ L, S ≠ T → subsetRank p (S ∪ T) = 4

theorem polygonRelationSpan_empty_family {n r : ℕ} (p : Fin n → Fin r → ℝ) :
    polygonRelationSpan p ∅ = ⊥ := by
  exact Finset.sup_empty

theorem polygonRelationSpan_insert_family {n r : ℕ} (p : Fin n → Fin r → ℝ)
    (S : Finset (Fin n)) (L : Finset (Finset (Fin n))) :
    polygonRelationSpan p (insert S L) = globalRelationSpace p S ⊔ polygonRelationSpan p L := by
  classical
  exact Finset.sup_insert

theorem polygonRelationSpan_singleton_family {n r : ℕ} (p : Fin n → Fin r → ℝ)
    (S : Finset (Fin n)) : polygonRelationSpan p {S} = globalRelationSpace p S := by
  exact Finset.sup_singleton

theorem polygonRelationSpan_pair_family {n r : ℕ} (p : Fin n → Fin r → ℝ)
    (S T : Finset (Fin n)) :
    polygonRelationSpan p {S,T} = globalRelationSpace p S ⊔ globalRelationSpace p T := by
  rw [polygonRelationSpan_insert_family, polygonRelationSpan_singleton_family]

theorem polygonRelationSpan_triple_family {n r : ℕ} (p : Fin n → Fin r → ℝ)
    (S T U : Finset (Fin n)) :
    polygonRelationSpan p {S,T,U} =
      globalRelationSpace p S ⊔ globalRelationSpace p T ⊔ globalRelationSpace p U := by
  rw [polygonRelationSpan_insert_family, polygonRelationSpan_pair_family, sup_assoc]

theorem polygonRelationSpan_four_family {n r : ℕ} (p : Fin n → Fin r → ℝ)
    (S T U V : Finset (Fin n)) :
    polygonRelationSpan p {S,T,U,V} = globalRelationSpace p S ⊔ globalRelationSpace p T ⊔
      globalRelationSpace p U ⊔ globalRelationSpace p V := by
  rw [polygonRelationSpan_insert_family, polygonRelationSpan_triple_family]
  simp only [sup_assoc]

theorem globalRelationSpace_finrank_eq_of_rank_eq {n r s : ℕ}
    (p : Fin n → Fin r → ℝ) (q : Fin n → Fin s → ℝ)
    (S : Finset (Fin n)) (h : subsetRank p S = subsetRank q S) :
    finrank ℝ ↥(globalRelationSpace p S) = finrank ℝ ↥(globalRelationSpace q S) := by
  have hp := globalRelationSpace_finrank p S
  have hq := globalRelationSpace_finrank q S
  omega

/-- With at most three polygon supports, the relation rank is combinatorial
without any bound on the number of vertices of the containing facet. -/
theorem at_most_three_polygon_rank_constancy {n r s : ℕ}
    (p : Fin n → Fin r → ℝ) (q : Fin n → Fin s → ℝ)
    (hpsmall : ∀ W : Finset (Fin n), W.card ≤ 3 →
      LinearIndependent ℝ (fun i : W => p i.val))
    (hqsmall : ∀ W : Finset (Fin n), W.card ≤ 3 →
      LinearIndependent ℝ (fun i : W => q i.val))
    (F : Finset (Fin n)) (L : Finset (Finset (Fin n)))
    (hp : FacetPolygonSpans p F L) (hq : FacetPolygonSpans q F L)
    (hinter : ∀ S ∈ L, ∀ T ∈ L, S ≠ T → (S ∩ T).card ≤ 2)
    (hcard : L.card ≤ 3) :
    finrank ℝ ↥(polygonRelationSpan p L) = finrank ℝ ↥(polygonRelationSpan q L) := by
  classical
  have hcases : L.card = 0 ∨ L.card = 1 ∨ L.card = 2 ∨ L.card = 3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · have hL : L = ∅ := Finset.card_eq_zero.mp h0
    rw [hL, polygonRelationSpan_empty_family, polygonRelationSpan_empty_family]
  · obtain ⟨S, rfl⟩ := Finset.card_eq_one.mp h1
    have hpS := hp.polygon_rank S (by simp)
    have hqS := hq.polygon_rank S (by simp)
    rw [polygonRelationSpan_singleton_family, polygonRelationSpan_singleton_family]
    exact globalRelationSpace_finrank_eq_of_rank_eq p q S (hpS.trans hqS.symm)
  · obtain ⟨S, T, hST, rfl⟩ := Finset.card_eq_two.mp h2
    have hpS := hp.polygon_rank S (by simp)
    have hpT := hp.polygon_rank T (by simp)
    have hqS := hq.polygon_rank S (by simp)
    have hqT := hq.polygon_rank T (by simp)
    have hSTi := hinter S (by simp) T (by simp) hST
    have hdp := globalRelationSpace_sup_finrank_of_small_inter p hpsmall S T (by omega)
    have hdq := globalRelationSpace_sup_finrank_of_small_inter q hqsmall S T (by omega)
    have hs := globalRelationSpace_finrank_eq_of_rank_eq p q S (hpS.trans hqS.symm)
    have ht := globalRelationSpace_finrank_eq_of_rank_eq p q T (hpT.trans hqT.symm)
    rw [polygonRelationSpan_pair_family, polygonRelationSpan_pair_family,
      hdp, hdq, hs, ht]
  · obtain ⟨S, T, U, hST, hSU, hTU, rfl⟩ := Finset.card_eq_three.mp h3
    have hdP := three_polygon_relation_dimension p hpsmall S T U
      (hp.polygon_rank S (by simp)) (hp.polygon_rank T (by simp))
      (hp.polygon_rank U (by simp)) (hp.pair_rank S (by simp) T (by simp) hST)
      (hinter S (by simp) T (by simp) hST)
      (hinter S (by simp) U (by simp) hSU)
      (hinter T (by simp) U (by simp) hTU)
    have hdQ := three_polygon_relation_dimension q hqsmall S T U
      (hq.polygon_rank S (by simp)) (hq.polygon_rank T (by simp))
      (hq.polygon_rank U (by simp)) (hq.pair_rank S (by simp) T (by simp) hST)
      (hinter S (by simp) T (by simp) hST)
      (hinter S (by simp) U (by simp) hSU)
      (hinter T (by simp) U (by simp) hTU)
    rw [polygonRelationSpan_triple_family, polygonRelationSpan_triple_family]
    omega

/-- The polygon-relation rank of a facet with at most seven vertices is
independent of its realization. The degree/Euler consequence needed here is
stated explicitly as the polygon excess bound; the geometric adapter proves
that bound for actual three-dimensional facets. -/
theorem small_facet_polygon_rank_constancy {n r s : ℕ}
    (p : Fin n → Fin r → ℝ) (q : Fin n → Fin s → ℝ)
    (hpsmall : ∀ W : Finset (Fin n), W.card ≤ 3 →
      LinearIndependent ℝ (fun i : W => p i.val))
    (hqsmall : ∀ W : Finset (Fin n), W.card ≤ 3 →
      LinearIndependent ℝ (fun i : W => q i.val))
    (F : Finset (Fin n)) (L : Finset (Finset (Fin n)))
    (hF : F.card ≤ 7) (hp : FacetPolygonSpans p F L) (hq : FacetPolygonSpans q F L)
    (hsize : ∀ S ∈ L, 4 ≤ S.card)
    (hinter : ∀ S ∈ L, ∀ T ∈ L, S ≠ T → (S ∩ T).card ≤ 2)
    (hbudget : ∑ S ∈ L, (S.card - 3) ≤ 4) :
    finrank ℝ ↥(polygonRelationSpan p L) = finrank ℝ ↥(polygonRelationSpan q L) := by
  classical
  have hcard : L.card ≤ 4 := by
    have hle : L.card ≤ ∑ S ∈ L, (S.card - 3) := by
      calc
        L.card = ∑ S ∈ L, 1 := by simp
        _ ≤ ∑ S ∈ L, (S.card - 3) := Finset.sum_le_sum (fun S hS => by
          have h := hsize S hS
          omega)
    omega
  have hcases : L.card = 0 ∨ L.card = 1 ∨ L.card = 2 ∨ L.card = 3 ∨ L.card = 4 := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4
  · have hL : L = ∅ := Finset.card_eq_zero.mp h0
    rw [hL, polygonRelationSpan_empty_family, polygonRelationSpan_empty_family]
  · obtain ⟨S, rfl⟩ := Finset.card_eq_one.mp h1
    have hpS := hp.polygon_rank S (by simp)
    have hqS := hq.polygon_rank S (by simp)
    rw [polygonRelationSpan_singleton_family, polygonRelationSpan_singleton_family]
    exact globalRelationSpace_finrank_eq_of_rank_eq p q S (hpS.trans hqS.symm)
  · obtain ⟨S, T, hST, rfl⟩ := Finset.card_eq_two.mp h2
    have hpS := hp.polygon_rank S (by simp)
    have hpT := hp.polygon_rank T (by simp)
    have hqS := hq.polygon_rank S (by simp)
    have hqT := hq.polygon_rank T (by simp)
    have hSTi := hinter S (by simp) T (by simp) hST
    have hdp := globalRelationSpace_sup_finrank_of_small_inter p hpsmall S T (by omega)
    have hdq := globalRelationSpace_sup_finrank_of_small_inter q hqsmall S T (by omega)
    have hs := globalRelationSpace_finrank_eq_of_rank_eq p q S (hpS.trans hqS.symm)
    have ht := globalRelationSpace_finrank_eq_of_rank_eq p q T (hpT.trans hqT.symm)
    rw [polygonRelationSpan_pair_family, polygonRelationSpan_pair_family,
      hdp, hdq, hs, ht]
  · obtain ⟨S, T, U, hST, hSU, hTU, rfl⟩ := Finset.card_eq_three.mp h3
    have hdP := three_polygon_relation_dimension p hpsmall S T U
      (hp.polygon_rank S (by simp)) (hp.polygon_rank T (by simp))
      (hp.polygon_rank U (by simp)) (hp.pair_rank S (by simp) T (by simp) hST)
      (hinter S (by simp) T (by simp) hST)
      (hinter S (by simp) U (by simp) hSU)
      (hinter T (by simp) U (by simp) hTU)
    have hdQ := three_polygon_relation_dimension q hqsmall S T U
      (hq.polygon_rank S (by simp)) (hq.polygon_rank T (by simp))
      (hq.polygon_rank U (by simp)) (hq.pair_rank S (by simp) T (by simp) hST)
      (hinter S (by simp) T (by simp) hST)
      (hinter S (by simp) U (by simp) hSU)
      (hinter T (by simp) U (by simp) hTU)
    rw [polygonRelationSpan_triple_family, polygonRelationSpan_triple_family]
    omega
  · obtain ⟨S, T, U, V, hST, hSU, hSV, hTU, hTV, hUV, rfl⟩ := Finset.card_eq_four.mp h4
    have hSmin := hsize S (by simp)
    have hTmin := hsize T (by simp)
    have hUmin := hsize U (by simp)
    have hVmin := hsize V (by simp)
    have hbudget' : (S.card - 3) + (T.card - 3) + (U.card - 3) + (V.card - 3) ≤ 4 := by
      simpa [hST, hSU, hSV, hTU, hTV, hUV, add_assoc] using hbudget
    have hSc : S.card = 4 := by omega
    have hTc : T.card = 4 := by omega
    have hUc : U.card = 4 := by omega
    have hVc : V.card = 4 := by omega
    have hdP := four_quadrilateral_relation_rank_three p hpsmall F S T U V hF
      hp.facet_rank (hp.subset S (by simp)) (hp.subset T (by simp))
      (hp.subset U (by simp)) (hp.subset V (by simp)) hSc hTc hUc hVc
      (hp.polygon_rank S (by simp)) (hp.polygon_rank T (by simp))
      (hp.polygon_rank U (by simp)) (hp.polygon_rank V (by simp))
      (hp.pair_rank S (by simp) T (by simp) hST)
      (hp.pair_rank S (by simp) U (by simp) hSU)
      (hinter S (by simp) T (by simp) hST) (hinter S (by simp) U (by simp) hSU)
      (hinter S (by simp) V (by simp) hSV) (hinter T (by simp) U (by simp) hTU)
      (hinter T (by simp) V (by simp) hTV) (hinter U (by simp) V (by simp) hUV)
    have hdQ := four_quadrilateral_relation_rank_three q hqsmall F S T U V hF
      hq.facet_rank (hq.subset S (by simp)) (hq.subset T (by simp))
      (hq.subset U (by simp)) (hq.subset V (by simp)) hSc hTc hUc hVc
      (hq.polygon_rank S (by simp)) (hq.polygon_rank T (by simp))
      (hq.polygon_rank U (by simp)) (hq.polygon_rank V (by simp))
      (hq.pair_rank S (by simp) T (by simp) hST)
      (hq.pair_rank S (by simp) U (by simp) hSU)
      (hinter S (by simp) T (by simp) hST) (hinter S (by simp) U (by simp) hSU)
      (hinter S (by simp) V (by simp) hSV) (hinter T (by simp) U (by simp) hTU)
      (hinter T (by simp) V (by simp) hTV) (hinter U (by simp) V (by simp) hUV)
    rw [polygonRelationSpan_four_family, polygonRelationSpan_four_family]
    exact hdP.trans hdQ.symm

/-- Triangle faces contribute the zero relation space and can be removed
from the finite polygon family without changing its span. -/
theorem polygonRelationSpan_filter_nontriangles {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (L : Finset (Finset (Fin n)))
    (hsize : ∀ S ∈ L, 3 ≤ S.card)
    (hrank : ∀ S ∈ L, subsetRank p S = 3) :
    polygonRelationSpan p (L.filter fun S => 4 ≤ S.card) = polygonRelationSpan p L := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro S hS
    exact globalRelationSpace_le_polygonRelationSpan p (Finset.mem_filter.mp hS).1
  · apply Finset.sup_le
    intro S hS
    by_cases hs : 4 ≤ S.card
    · exact globalRelationSpace_le_polygonRelationSpan p (Finset.mem_filter.mpr ⟨hS, hs⟩)
    · have hcard : S.card = 3 := by have h := hsize S hS; omega
      have hd := globalRelationSpace_finrank p S
      have hbot : globalRelationSpace p S = ⊥ := by
        apply Submodule.finrank_eq_zero.mp
        rw [hrank S hS, hcard] at hd
        omega
      rw [hbot]
      exact bot_le

/-- Fewer than four nonsimplicial polygons cannot change local relation rank,
even in an arbitrarily large facet. -/
theorem few_nonsimplicial_polygon_rank_constancy {n r s : ℕ}
    (p : Fin n → Fin r → ℝ) (q : Fin n → Fin s → ℝ)
    (hpsmall : ∀ W : Finset (Fin n), W.card ≤ 3 →
      LinearIndependent ℝ (fun i : W => p i.val))
    (hqsmall : ∀ W : Finset (Fin n), W.card ≤ 3 →
      LinearIndependent ℝ (fun i : W => q i.val))
    (F : Finset (Fin n)) (L : Finset (Finset (Fin n)))
    (hp : FacetPolygonSpans p F L) (hq : FacetPolygonSpans q F L)
    (hsize : ∀ S ∈ L, 3 ≤ S.card)
    (hinter : ∀ S ∈ L, ∀ T ∈ L, S ≠ T → (S ∩ T).card ≤ 2)
    (hcard : (L.filter fun S => 4 ≤ S.card).card ≤ 3) :
    finrank ℝ ↥(polygonRelationSpan p L) = finrank ℝ ↥(polygonRelationSpan q L) := by
  classical
  let L' := L.filter fun S => 4 ≤ S.card
  have hsub : L' ⊆ L := Finset.filter_subset _ _
  have hp' : FacetPolygonSpans p F L' :=
    ⟨hp.facet_rank, fun S hS => hp.subset S (hsub hS),
      fun S hS => hp.polygon_rank S (hsub hS),
      fun S hS T hT => hp.pair_rank S (hsub hS) T (hsub hT)⟩
  have hq' : FacetPolygonSpans q F L' :=
    ⟨hq.facet_rank, fun S hS => hq.subset S (hsub hS),
      fun S hS => hq.polygon_rank S (hsub hS),
      fun S hS T hT => hq.pair_rank S (hsub hS) T (hsub hT)⟩
  have h := at_most_three_polygon_rank_constancy p q hpsmall hqsmall F L' hp' hq'
    (fun S hS T hT => hinter S (hsub hS) T (hsub hT)) hcard
  rw [polygonRelationSpan_filter_nontriangles p L hsize hp.polygon_rank,
    polygonRelationSpan_filter_nontriangles q L hsize hq.polygon_rank] at h
  exact h

/-- Version for the complete polygon-face family, including triangles. -/
theorem small_facet_all_polygon_rank_constancy {n r s : ℕ}
    (p : Fin n → Fin r → ℝ) (q : Fin n → Fin s → ℝ)
    (hpsmall : ∀ W : Finset (Fin n), W.card ≤ 3 →
      LinearIndependent ℝ (fun i : W => p i.val))
    (hqsmall : ∀ W : Finset (Fin n), W.card ≤ 3 →
      LinearIndependent ℝ (fun i : W => q i.val))
    (F : Finset (Fin n)) (L : Finset (Finset (Fin n)))
    (hF : F.card ≤ 7) (hp : FacetPolygonSpans p F L) (hq : FacetPolygonSpans q F L)
    (hsize : ∀ S ∈ L, 3 ≤ S.card)
    (hinter : ∀ S ∈ L, ∀ T ∈ L, S ≠ T → (S ∩ T).card ≤ 2)
    (hbudget : ∑ S ∈ L, (S.card - 3) ≤ 4) :
    finrank ℝ ↥(polygonRelationSpan p L) = finrank ℝ ↥(polygonRelationSpan q L) := by
  classical
  let L' := L.filter fun S => 4 ≤ S.card
  have hsub : L' ⊆ L := Finset.filter_subset _ _
  have hp' : FacetPolygonSpans p F L' :=
    ⟨hp.facet_rank, fun S hS => hp.subset S (hsub hS),
      fun S hS => hp.polygon_rank S (hsub hS),
      fun S hS T hT => hp.pair_rank S (hsub hS) T (hsub hT)⟩
  have hq' : FacetPolygonSpans q F L' :=
    ⟨hq.facet_rank, fun S hS => hq.subset S (hsub hS),
      fun S hS => hq.polygon_rank S (hsub hS),
      fun S hS T hT => hq.pair_rank S (hsub hS) T (hsub hT)⟩
  have hb : ∑ S ∈ L', (S.card - 3) ≤ 4 := by
    have hle : ∑ S ∈ L', (S.card - 3) ≤ ∑ S ∈ L, (S.card - 3) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    exact hle.trans hbudget
  have h := small_facet_polygon_rank_constancy p q hpsmall hqsmall F L' hF hp' hq'
    (fun S hS => (Finset.mem_filter.mp hS).2)
    (fun S hS T hT => hinter S (hsub hS) T (hsub hT)) hb
  rw [polygonRelationSpan_filter_nontriangles p L hsize hp.polygon_rank,
    polygonRelationSpan_filter_nontriangles q L hsize hq.polygon_rank] at h
  exact h

#print axioms small_facet_polygon_rank_constancy

end Papers.RationalityTen.ChirotopeDensity
