module
public import Papers.RationalityTenPolygonRelationRanks

@[expose] public section
noncomputable section

open Matrix Module Set
open scoped BigOperators

namespace Papers.RationalityTen.ChirotopeDensity

/-- Intersecting actual relation spaces is exactly intersecting their labelled
supports. No generic realization assumption is involved. -/
theorem globalRelationSpace_inter_support {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (S T : Finset (Fin n)) :
    globalRelationSpace p S ⊓ globalRelationSpace p T =
      globalRelationSpace p (S ∩ T) := by
  ext v
  constructor
  · rintro ⟨hS, hT⟩
    obtain ⟨hSv, hp⟩ := (mem_globalRelationSpace_iff p S v).mp hS
    obtain ⟨hTv, _⟩ := (mem_globalRelationSpace_iff p T v).mp hT
    apply (mem_globalRelationSpace_iff p (S ∩ T) v).mpr
    refine ⟨?_, hp⟩
    intro i hi
    by_cases hSi : i ∈ S
    · exact hTv i (fun hTi => hi (Finset.mem_inter.mpr ⟨hSi, hTi⟩))
    · exact hSv i hSi
  · intro hv
    exact ⟨globalRelationSpace_mono p Finset.inter_subset_left hv,
      globalRelationSpace_mono p Finset.inter_subset_right hv⟩

/-- An independent labelled set has no nonzero homogeneous relation. -/
theorem globalRelationSpace_eq_bot_of_independent {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (S : Finset (Fin n))
    (hS : LinearIndependent ℝ (fun i : S => p i.val)) :
    globalRelationSpace p S = ⊥ := by
  apply Submodule.finrank_eq_zero.mp
  have h := globalRelationSpace_finrank p S
  rw [subsetRank_of_independent p S hS] at h
  omega

/-- Relation spaces on two polygon faces are disjoint, since their common
labels contain at most three independent points. -/
theorem globalRelationSpace_disjoint_of_small_inter {n r : ℕ}
    (p : Fin n → Fin r → ℝ)
    (hsmall : ∀ S : Finset (Fin n), S.card ≤ 3 →
      LinearIndependent ℝ (fun i : S => p i.val))
    (S T : Finset (Fin n)) (hST : (S ∩ T).card ≤ 3) :
    Disjoint (globalRelationSpace p S) (globalRelationSpace p T) := by
  rw [disjoint_iff, globalRelationSpace_inter_support]
  exact globalRelationSpace_eq_bot_of_independent p _ (hsmall _ hST)

/-- Hence two polygon relation spaces have the sum of their dimensions. -/
theorem globalRelationSpace_sup_finrank_of_small_inter {n r : ℕ}
    (p : Fin n → Fin r → ℝ)
    (hsmall : ∀ S : Finset (Fin n), S.card ≤ 3 →
      LinearIndependent ℝ (fun i : S => p i.val))
    (S T : Finset (Fin n)) (hST : (S ∩ T).card ≤ 3) :
    finrank ℝ ↥(globalRelationSpace p S ⊔ globalRelationSpace p T) =
      finrank ℝ ↥(globalRelationSpace p S) + finrank ℝ ↥(globalRelationSpace p T) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (globalRelationSpace p S) (globalRelationSpace p T)
  rw [(globalRelationSpace_disjoint_of_small_inter p hsmall S T hST).eq_bot,
    finrank_bot, add_zero] at h
  exact h

/-- A nonzero relation among extreme-point labels uses at least four labels. -/
theorem four_le_card_of_nonzero_relation {n r : ℕ}
    (p : Fin n → Fin r → ℝ)
    (hsmall : ∀ S : Finset (Fin n), S.card ≤ 3 →
      LinearIndependent ℝ (fun i : S => p i.val))
    (S : Finset (Fin n)) (v : Fin n → ℝ)
    (hv : v ∈ globalRelationSpace p S) (hv0 : v ≠ 0) : 4 ≤ S.card := by
  by_contra h
  have hS : S.card ≤ 3 := by omega
  have hbot := globalRelationSpace_eq_bot_of_independent p S (hsmall S hS)
  rw [hbot] at hv
  exact hv0 hv

/-- In a cancellation among three supported relations, each relation is
supported on the intersections with the other two polygons. -/
theorem relation_support_of_three_cancellation {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (S T U : Finset (Fin n))
    (u v w : Fin n → ℝ)
    (hu : u ∈ globalRelationSpace p S)
    (hv : v ∈ globalRelationSpace p T)
    (hw : w ∈ globalRelationSpace p U)
    (hsum : u + v + w = 0) :
    u ∈ globalRelationSpace p (S ∩ (T ∪ U)) := by
  obtain ⟨huS, hup⟩ := (mem_globalRelationSpace_iff p S u).mp hu
  obtain ⟨hvT, _⟩ := (mem_globalRelationSpace_iff p T v).mp hv
  obtain ⟨hwU, _⟩ := (mem_globalRelationSpace_iff p U w).mp hw
  apply (mem_globalRelationSpace_iff p _ u).mpr
  refine ⟨?_, hup⟩
  intro i hi
  by_cases hSi : i ∈ S
  · have hTi : i ∉ T := fun h => hi (Finset.mem_inter.mpr
      ⟨hSi, Finset.mem_union_left U h⟩)
    have hUi : i ∉ U := fun h => hi (Finset.mem_inter.mpr
      ⟨hSi, Finset.mem_union_right T h⟩)
    have h := congrFun hsum i
    simpa only [Pi.add_apply, Pi.zero_apply, hvT i hTi, hwU i hUi,
      add_zero] using h
  · exact huS i hSi

/-- With polygon intersections of size at most two, a nonzero three-polygon
cancellation forces exactly four intersection labels on each polygon. -/
theorem four_intersection_labels_of_three_cancellation {n r : ℕ}
    (p : Fin n → Fin r → ℝ)
    (hsmall : ∀ S : Finset (Fin n), S.card ≤ 3 →
      LinearIndependent ℝ (fun i : S => p i.val))
    (S T U : Finset (Fin n))
    (hST : (S ∩ T).card ≤ 2) (hSU : (S ∩ U).card ≤ 2)
    (u v w : Fin n → ℝ)
    (hu : u ∈ globalRelationSpace p S)
    (hv : v ∈ globalRelationSpace p T)
    (hw : w ∈ globalRelationSpace p U)
    (hu0 : u ≠ 0) (hsum : u + v + w = 0) :
    (S ∩ (T ∪ U)).card = 4 := by
  have hlo := four_le_card_of_nonzero_relation p hsmall _ u
    (relation_support_of_three_cancellation p S T U u v w hu hv hw hsum) hu0
  have hhi : (S ∩ (T ∪ U)).card ≤ (S ∩ T).card + (S ∩ U).card := by
    rw [Finset.inter_union_distrib_left]
    exact Finset.card_union_le _ _
  omega

#print axioms four_intersection_labels_of_three_cancellation

end Papers.RationalityTen.ChirotopeDensity
