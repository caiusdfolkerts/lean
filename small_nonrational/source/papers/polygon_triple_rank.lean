module
public import Papers.PolygonSpaceCancellation
public import Papers.ThreePolygonSupportCounts
public import Mathlib.Tactic.Tauto

@[expose] public section
noncomputable section

open Matrix Module Set
open scoped BigOperators

namespace Papers.RationalityTen.ChirotopeDensity

/-- The coordinate span is monotone in its finite labelled support. -/
theorem subsetRank_mono_labels {n r : ℕ} (p : Fin n → Fin r → ℝ)
    {S T : Finset (Fin n)} (hST : S ⊆ T) : subsetRank p S ≤ subsetRank p T := by
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨i, hST hi, rfl⟩

/-- Three independent labels give the required lower bound on every larger
labelled coordinate span. -/
theorem three_le_subsetRank {n r : ℕ} (p : Fin n → Fin r → ℝ)
    (hsmall : ∀ S : Finset (Fin n), S.card ≤ 3 →
      LinearIndependent ℝ (fun i : S => p i.val))
    (S : Finset (Fin n)) (hS : 3 ≤ S.card) : 3 ≤ subsetRank p S := by
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq hS
  have h := subsetRank_mono_labels p hTS
  rw [subsetRank_of_independent p T (hsmall T (by omega)), hT] at h
  exact h

/-- Four labels in a polygon span its entire homogeneous plane and carry
exactly one relation. -/
theorem four_polygon_relation_finrank {n r : ℕ}
    (p : Fin n → Fin r → ℝ)
    (hsmall : ∀ S : Finset (Fin n), S.card ≤ 3 →
      LinearIndependent ℝ (fun i : S => p i.val))
    (S T : Finset (Fin n)) (hTS : T ⊆ S) (hS : subsetRank p S = 3)
    (hT : T.card = 4) :
    subsetRank p T = 3 ∧ finrank ℝ ↥(globalRelationSpace p T) = 1 ∧
    Submodule.span ℝ (p '' (↑T : Set (Fin n))) =
      Submodule.span ℝ (p '' (↑S : Set (Fin n))) := by
  have hlo := three_le_subsetRank p hsmall T (by omega)
  have hhi := subsetRank_mono_labels p hTS
  have hr : subsetRank p T = 3 := by omega
  have hd := globalRelationSpace_finrank p T
  refine ⟨hr, by omega, ?_⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_mono
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨i, hTS hi, rfl⟩
  · exact hr.trans hS.symm

/-- A vector in the sum of two supported relation spaces has no coefficients
outside their union. -/
theorem globalRelationSpace_sup_le_union {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (S T : Finset (Fin n)) :
    globalRelationSpace p S ⊔ globalRelationSpace p T ≤
      globalRelationSpace p (S ∪ T) := by
  exact sup_le (globalRelationSpace_mono p Finset.subset_union_left)
    (globalRelationSpace_mono p Finset.subset_union_right)

/-- Thus the possible defect in adding a third polygon is supported on its
intersections with the first two. -/
theorem three_relation_intersection_le {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (S T U : Finset (Fin n)) :
    (globalRelationSpace p S ⊔ globalRelationSpace p T) ⊓ globalRelationSpace p U ≤
      globalRelationSpace p (U ∩ (S ∪ T)) := by
  intro w hw
  have h : w ∈ globalRelationSpace p (S ∪ T) ⊓ globalRelationSpace p U :=
    ⟨globalRelationSpace_sup_le_union p S T hw.1, hw.2⟩
  rw [globalRelationSpace_inter_support, Finset.inter_comm] at h
  exact h

/-- If any one of three polygon relations has fewer than four available
cancellation labels, the third relation space adds its full dimension. -/
theorem three_relation_intersection_eq_bot_of_small_overlap {n r : ℕ}
    (p : Fin n → Fin r → ℝ)
    (hsmall : ∀ S : Finset (Fin n), S.card ≤ 3 →
      LinearIndependent ℝ (fun i : S => p i.val))
    (S T U : Finset (Fin n))
    (hTU : (T ∩ U).card ≤ 3)
    (hS : (S ∩ (T ∪ U)).card ≤ 3) :
    (globalRelationSpace p S ⊔ globalRelationSpace p T) ⊓ globalRelationSpace p U = ⊥ := by
  apply le_bot_iff.mp
  intro w hw
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hw.1
  have hsum : u + v + -w = 0 := by rw [huv, add_neg_cancel]
  have hu' := relation_support_of_three_cancellation p S T U u v (-w)
    hu hv (Submodule.neg_mem _ hw.2) hsum
  have hbot := globalRelationSpace_eq_bot_of_independent p _ (hsmall _ hS)
  rw [hbot] at hu'
  have hu0 : u = 0 := hu'
  have hvw : v = w := by simpa only [hu0, zero_add] using huv
  have hv' : w ∈ globalRelationSpace p T := hvw ▸ hv
  exact (globalRelationSpace_disjoint_of_small_inter p hsmall T U hTU).eq_bot ▸
    (show w ∈ globalRelationSpace p T ⊓ globalRelationSpace p U from ⟨hv', hw.2⟩)

/-- Span commutes with the union of two finite labelled supports. -/
theorem span_label_union {n r : ℕ} (p : Fin n → Fin r → ℝ)
    (S T : Finset (Fin n)) :
    Submodule.span ℝ (p '' (↑(S ∪ T) : Set (Fin n))) =
      Submodule.span ℝ (p '' (↑S : Set (Fin n))) ⊔
        Submodule.span ℝ (p '' (↑T : Set (Fin n))) := by
  have hs : p '' (↑(S ∪ T) : Set (Fin n)) =
      p '' (↑S : Set (Fin n)) ∪ p '' (↑T : Set (Fin n)) := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      rcases Finset.mem_union.mp hi with hi | hi
      · exact Or.inl ⟨i, hi, rfl⟩
      · exact Or.inr ⟨i, hi, rfl⟩
    · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
      · exact ⟨i, Finset.mem_union_left T hi, rfl⟩
      · exact ⟨i, Finset.mem_union_right S hi, rfl⟩
  rw [hs, Submodule.span_union]

/-- Replacing each polygon by a spanning four-label subset does not change
the rank of their union. -/
theorem subsetRank_union_of_spanning_subsets {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (S T S' T' : Finset (Fin n))
    (hS : Submodule.span ℝ (p '' (↑S' : Set (Fin n))) =
      Submodule.span ℝ (p '' (↑S : Set (Fin n))))
    (hT : Submodule.span ℝ (p '' (↑T' : Set (Fin n))) =
      Submodule.span ℝ (p '' (↑T : Set (Fin n)))) :
    subsetRank p (S' ∪ T') = subsetRank p (S ∪ T) := by
  unfold subsetRank
  rw [span_label_union, span_label_union, hS, hT]

/-- In a three-face prism band, the two four-point circuit spaces fill the
entire two-dimensional relation space on the six shared labels. Consequently
the third circuit is their one-dimensional overlap. -/
theorem three_relation_intersection_eq_of_prism_support {n r : ℕ}
    (p : Fin n → Fin r → ℝ)
    (hsmall : ∀ V : Finset (Fin n), V.card ≤ 3 →
      LinearIndependent ℝ (fun i : V => p i.val))
    (S T U : Finset (Fin n))
    (hS : subsetRank p S = 3) (hT : subsetRank p T = 3)
    (hU : subsetRank p U = 3) (hSTrank : subsetRank p (S ∪ T) = 4)
    (hST : (S ∩ T).card ≤ 2) (hSU : (S ∩ U).card ≤ 2)
    (hTU : (T ∩ U).card ≤ 2)
    (h1 : (S ∩ (T ∪ U)).card = 4)
    (h2 : (T ∩ (S ∪ U)).card = 4)
    (h3 : (U ∩ (S ∪ T)).card = 4) :
    (globalRelationSpace p S ⊔ globalRelationSpace p T) ⊓ globalRelationSpace p U =
      globalRelationSpace p (U ∩ (S ∪ T)) := by
  classical
  let S' := S ∩ (T ∪ U)
  let T' := T ∩ (S ∪ U)
  let U' := U ∩ (S ∪ T)
  have hS' := four_polygon_relation_finrank p hsmall S S' Finset.inter_subset_left hS h1
  have hT' := four_polygon_relation_finrank p hsmall T T' Finset.inter_subset_left hT h2
  have hU' := four_polygon_relation_finrank p hsmall U U' Finset.inter_subset_left hU h3
  have hST' : (S' ∩ T').card ≤ 3 := by
    apply (Finset.card_le_card ?_).trans (show (S ∩ T).card ≤ 3 by omega)
    intro i hi
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hi).1).1,
       (Finset.mem_inter.mp (Finset.mem_inter.mp hi).2).1⟩
  have hdim : finrank ℝ ↥(globalRelationSpace p S' ⊔ globalRelationSpace p T') = 2 := by
    rw [globalRelationSpace_sup_finrank_of_small_inter p hsmall S' T' hST',
      hS'.2.1, hT'.2.1]
  have hSTr : subsetRank p (S' ∪ T') = 4 :=
    (subsetRank_union_of_spanning_subsets p S T S' T' hS'.2.2 hT'.2.2).trans hSTrank
  have hAB : ((S ∩ T) ∪ (S ∩ U)).card = 4 := by
    simpa only [← Finset.inter_union_distrib_left] using h1
  have hAC : ((S ∩ T) ∪ (T ∩ U)).card = 4 := by
    simpa only [Finset.inter_union_distrib_left, Finset.inter_comm T S] using h2
  have hBC : ((S ∩ U) ∪ (T ∩ U)).card = 4 := by
    simpa only [Finset.inter_union_distrib_left, Finset.inter_comm U S,
      Finset.inter_comm U T] using h3
  have hcount := three_pair_unions_four (S ∩ T) (S ∩ U) (T ∩ U)
    hST hSU hTU hAB hAC hBC
  have hunion : S' ∪ T' = (S ∩ T) ∪ (S ∩ U) ∪ (T ∩ U) := by
    ext i
    simp only [S', T', Finset.mem_union, Finset.mem_inter]
    tauto
  have hcard : (S' ∪ T').card = 6 := by
    rw [hunion]
    exact hcount.2.2.2.2.2.2
  have hfull : globalRelationSpace p S' ⊔ globalRelationSpace p T' =
      globalRelationSpace p (S' ∪ T') := by
    apply Submodule.eq_of_le_of_finrank_eq (globalRelationSpace_sup_le_union p S' T')
    have h := globalRelationSpace_finrank p (S' ∪ T')
    omega
  have hUsub : U' ⊆ S' ∪ T' := by
    intro i hi
    simp only [S', T', U', Finset.mem_union, Finset.mem_inter] at hi ⊢
    tauto
  apply le_antisymm (three_relation_intersection_le p S T U)
  intro w hw
  constructor
  · have hw' : w ∈ globalRelationSpace p (S' ∪ T') :=
      globalRelationSpace_mono p hUsub hw
    rw [← hfull] at hw'
    exact (sup_le_sup
      (globalRelationSpace_mono p (show S' ⊆ S from Finset.inter_subset_left))
      (globalRelationSpace_mono p (show T' ⊆ T from Finset.inter_subset_left))) hw'
  · exact globalRelationSpace_mono p Finset.inter_subset_left hw

/-- The combinatorial prism-band condition for three polygon supports. -/
def ThreePolygonBand {n : ℕ} (S T U : Finset (Fin n)) : Prop :=
  (S ∩ (T ∪ U)).card = 4 ∧ (T ∩ (S ∪ U)).card = 4 ∧
    (U ∩ (S ∪ T)).card = 4

instance instDecidableThreePolygonBand {n : ℕ} (S T U : Finset (Fin n)) :
    Decidable (ThreePolygonBand S T U) := by
  unfold ThreePolygonBand
  infer_instance

/-- The only possible relation-space defect for three polygon faces is one
line, and its occurrence is decided entirely by their labelled supports. -/
theorem three_relation_intersection_finrank {n r : ℕ}
    (p : Fin n → Fin r → ℝ)
    (hsmall : ∀ V : Finset (Fin n), V.card ≤ 3 →
      LinearIndependent ℝ (fun i : V => p i.val))
    (S T U : Finset (Fin n))
    (hS : subsetRank p S = 3) (hT : subsetRank p T = 3)
    (hU : subsetRank p U = 3) (hSTrank : subsetRank p (S ∪ T) = 4)
    (hST : (S ∩ T).card ≤ 2) (hSU : (S ∩ U).card ≤ 2)
    (hTU : (T ∩ U).card ≤ 2) :
    finrank ℝ ↥((globalRelationSpace p S ⊔ globalRelationSpace p T) ⊓
      globalRelationSpace p U) = if ThreePolygonBand S T U then 1 else 0 := by
  classical
  have hcap : ∀ A B D : Finset (Fin n), (A ∩ B).card ≤ 2 →
      (A ∩ D).card ≤ 2 → (A ∩ (B ∪ D)).card ≤ 4 := by
    intro A B D hAB hAD
    rw [Finset.inter_union_distrib_left]
    have h := Finset.card_union_le (A ∩ B) (A ∩ D)
    omega
  by_cases hb : ThreePolygonBand S T U
  · rw [if_pos hb, three_relation_intersection_eq_of_prism_support p hsmall S T U
      hS hT hU hSTrank hST hSU hTU hb.1 hb.2.1 hb.2.2]
    exact (four_polygon_relation_finrank p hsmall U _ Finset.inter_subset_left
      hU hb.2.2).2.1
  · rw [if_neg hb]
    have hbot : (globalRelationSpace p S ⊔ globalRelationSpace p T) ⊓
        globalRelationSpace p U = ⊥ := by
      by_cases h1 : (S ∩ (T ∪ U)).card = 4
      · by_cases h2 : (T ∩ (S ∪ U)).card = 4
        · have h3 : (U ∩ (S ∪ T)).card ≤ 3 := by
            have hle := hcap U S T (by simpa only [Finset.inter_comm] using hSU)
              (by simpa only [Finset.inter_comm] using hTU)
            have hne : (U ∩ (S ∪ T)).card ≠ 4 := fun h => hb ⟨h1, h2, h⟩
            omega
          apply le_bot_iff.mp
          exact (three_relation_intersection_le p S T U).trans
            (globalRelationSpace_eq_bot_of_independent p _ (hsmall _ h3)).le
        · have h2' : (T ∩ (S ∪ U)).card ≤ 3 := by
            have hle := hcap T S U (by simpa only [Finset.inter_comm] using hST) hTU
            omega
          have h := three_relation_intersection_eq_bot_of_small_overlap p hsmall T S U
            (by omega) h2'
          simpa only [sup_comm] using h
      · have h1' : (S ∩ (T ∪ U)).card ≤ 3 := by
          have hle := hcap S T U hST hSU
          omega
        exact three_relation_intersection_eq_bot_of_small_overlap p hsmall S T U
          (by omega) h1'
    rw [hbot, finrank_bot]

/-- Complete three-polygon dimension formula. Every quantity on the right
is combinatorial, so the formula proves realization independence. -/
theorem three_polygon_relation_dimension {n r : ℕ}
    (p : Fin n → Fin r → ℝ)
    (hsmall : ∀ V : Finset (Fin n), V.card ≤ 3 →
      LinearIndependent ℝ (fun i : V => p i.val))
    (S T U : Finset (Fin n))
    (hS : subsetRank p S = 3) (hT : subsetRank p T = 3)
    (hU : subsetRank p U = 3) (hSTrank : subsetRank p (S ∪ T) = 4)
    (hST : (S ∩ T).card ≤ 2) (hSU : (S ∩ U).card ≤ 2)
    (hTU : (T ∩ U).card ≤ 2) :
    finrank ℝ ↥(globalRelationSpace p S ⊔ globalRelationSpace p T ⊔
      globalRelationSpace p U) + 9 + (if ThreePolygonBand S T U then 1 else 0) =
      S.card + T.card + U.card := by
  classical
  have hd := Submodule.finrank_sup_add_finrank_inf_eq
    (globalRelationSpace p S ⊔ globalRelationSpace p T) (globalRelationSpace p U)
  rw [three_relation_intersection_finrank p hsmall S T U hS hT hU hSTrank hST hSU hTU,
    globalRelationSpace_sup_finrank_of_small_inter p hsmall S T (by omega)] at hd
  have h1 := globalRelationSpace_finrank p S
  have h2 := globalRelationSpace_finrank p T
  have h3 := globalRelationSpace_finrank p U
  rw [hS] at h1
  rw [hT] at h2
  rw [hU] at h3
  omega

#print axioms three_relation_intersection_eq_bot_of_small_overlap

end Papers.RationalityTen.ChirotopeDensity
