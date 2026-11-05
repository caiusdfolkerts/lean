module
public import Papers.PolygonTripleRank

@[expose] public section
noncomputable section

open Matrix Module Set
open scoped BigOperators

namespace Papers.RationalityTen.ChirotopeDensity

/-- Four quadrilateral faces cannot have total relation rank at most two:
that would force three disjoint pairs of intersection labels inside one
four-label quadrilateral. -/
theorem four_quadrilateral_relation_rank_ge_three {n r : ℕ}
    (p : Fin n → Fin r → ℝ)
    (hsmall : ∀ W : Finset (Fin n), W.card ≤ 3 →
      LinearIndependent ℝ (fun i : W => p i.val))
    (S T U V : Finset (Fin n))
    (hSc : S.card = 4) (hTc : T.card = 4) (hUc : U.card = 4) (hVc : V.card = 4)
    (hS : subsetRank p S = 3) (hT : subsetRank p T = 3)
    (hU : subsetRank p U = 3) (hV : subsetRank p V = 3)
    (hSTrank : subsetRank p (S ∪ T) = 4) (hSUrank : subsetRank p (S ∪ U) = 4)
    (hST : (S ∩ T).card ≤ 2) (hSU : (S ∩ U).card ≤ 2)
    (hSV : (S ∩ V).card ≤ 2) (hTU : (T ∩ U).card ≤ 2)
    (hTV : (T ∩ V).card ≤ 2) (hUV : (U ∩ V).card ≤ 2) :
    3 ≤ finrank ℝ ↥(globalRelationSpace p S ⊔ globalRelationSpace p T ⊔
      globalRelationSpace p U ⊔ globalRelationSpace p V) := by
  classical
  let M := globalRelationSpace p S ⊔ globalRelationSpace p T ⊔
    globalRelationSpace p U ⊔ globalRelationSpace p V
  by_contra h
  change ¬ 3 ≤ finrank ℝ M at h
  have hM : finrank ℝ M ≤ 2 := by omega
  have hSm : globalRelationSpace p S ≤ M :=
    (le_sup_left : globalRelationSpace p S ≤ globalRelationSpace p S ⊔
      globalRelationSpace p T).trans (le_sup_left.trans le_sup_left)
  have hTm : globalRelationSpace p T ≤ M :=
    (le_sup_right : globalRelationSpace p T ≤ globalRelationSpace p S ⊔
      globalRelationSpace p T).trans (le_sup_left.trans le_sup_left)
  have hUm : globalRelationSpace p U ≤ M := le_sup_right.trans le_sup_left
  have hVm : globalRelationSpace p V ≤ M := le_sup_right
  have hSTU := three_polygon_relation_dimension p hsmall S T U
    hS hT hU hSTrank hST hSU hTU
  have hSTV := three_polygon_relation_dimension p hsmall S T V
    hS hT hV hSTrank hST hSV hTV
  have hSUV := three_polygon_relation_dimension p hsmall S U V
    hS hU hV hSUrank hSU hSV hUV
  have hSTUle : finrank ℝ ↥(globalRelationSpace p S ⊔ globalRelationSpace p T ⊔
      globalRelationSpace p U) ≤ 2 :=
    (Submodule.finrank_mono (sup_le (sup_le hSm hTm) hUm)).trans hM
  have hSTVle : finrank ℝ ↥(globalRelationSpace p S ⊔ globalRelationSpace p T ⊔
      globalRelationSpace p V) ≤ 2 :=
    (Submodule.finrank_mono (sup_le (sup_le hSm hTm) hVm)).trans hM
  have hSUVle : finrank ℝ ↥(globalRelationSpace p S ⊔ globalRelationSpace p U ⊔
      globalRelationSpace p V) ≤ 2 :=
    (Submodule.finrank_mono (sup_le (sup_le hSm hUm) hVm)).trans hM
  have hbSTU : ThreePolygonBand S T U := by
    by_contra hb
    rw [if_neg hb] at hSTU
    omega
  have hbSTV : ThreePolygonBand S T V := by
    by_contra hb
    rw [if_neg hb] at hSTV
    omega
  have hbSUV : ThreePolygonBand S U V := by
    by_contra hb
    rw [if_neg hb] at hSUV
    omega
  have hAB : ((S ∩ T) ∪ (S ∩ U)).card = 4 := by
    simpa only [← Finset.inter_union_distrib_left] using hbSTU.1
  have hAC : ((S ∩ T) ∪ (S ∩ V)).card = 4 := by
    simpa only [← Finset.inter_union_distrib_left] using hbSTV.1
  have hBC : ((S ∩ U) ∪ (S ∩ V)).card = 4 := by
    simpa only [← Finset.inter_union_distrib_left] using hbSUV.1
  have hc := (three_pair_unions_four (S ∩ T) (S ∩ U) (S ∩ V)
    hST hSU hSV hAB hAC hBC).2.2.2.2.2.2
  have hsubset : (S ∩ T) ∪ (S ∩ U) ∪ (S ∩ V) ⊆ S := by
    intro i hi
    simp only [Finset.mem_union, Finset.mem_inter] at hi
    tauto
  have hle := Finset.card_le_card hsubset
  omega

/-- The only four-polygon case on at most seven vertices has rank exactly
three, since the full homogeneous relation space has dimension at most three. -/
theorem four_quadrilateral_relation_rank_three {n r : ℕ}
    (p : Fin n → Fin r → ℝ)
    (hsmall : ∀ W : Finset (Fin n), W.card ≤ 3 →
      LinearIndependent ℝ (fun i : W => p i.val))
    (F S T U V : Finset (Fin n)) (hFcard : F.card ≤ 7) (hFrank : subsetRank p F = 4)
    (hSF : S ⊆ F) (hTF : T ⊆ F) (hUF : U ⊆ F) (hVF : V ⊆ F)
    (hSc : S.card = 4) (hTc : T.card = 4) (hUc : U.card = 4) (hVc : V.card = 4)
    (hS : subsetRank p S = 3) (hT : subsetRank p T = 3)
    (hU : subsetRank p U = 3) (hV : subsetRank p V = 3)
    (hSTrank : subsetRank p (S ∪ T) = 4) (hSUrank : subsetRank p (S ∪ U) = 4)
    (hST : (S ∩ T).card ≤ 2) (hSU : (S ∩ U).card ≤ 2)
    (hSV : (S ∩ V).card ≤ 2) (hTU : (T ∩ U).card ≤ 2)
    (hTV : (T ∩ V).card ≤ 2) (hUV : (U ∩ V).card ≤ 2) :
    finrank ℝ ↥(globalRelationSpace p S ⊔ globalRelationSpace p T ⊔
      globalRelationSpace p U ⊔ globalRelationSpace p V) = 3 := by
  have hlo := four_quadrilateral_relation_rank_ge_three p hsmall S T U V
    hSc hTc hUc hVc hS hT hU hV hSTrank hSUrank hST hSU hSV hTU hTV hUV
  have hle : globalRelationSpace p S ⊔ globalRelationSpace p T ⊔
      globalRelationSpace p U ⊔ globalRelationSpace p V ≤ globalRelationSpace p F :=
    sup_le (sup_le (sup_le (globalRelationSpace_mono p hSF)
      (globalRelationSpace_mono p hTF)) (globalRelationSpace_mono p hUF))
      (globalRelationSpace_mono p hVF)
  have hhi := Submodule.finrank_mono hle
  have hd := globalRelationSpace_finrank p F
  omega

#print axioms four_quadrilateral_relation_rank_three

end Papers.RationalityTen.ChirotopeDensity
