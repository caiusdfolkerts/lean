module

public import Recovery.Unimodular.NativePort.A3SupportGluing

@[expose] public section

/-! UNVERIFIED until the exact native compiler run succeeds.
Actual A3 projectivity equivalence and labelled fan counts.
All input rays, cones, and strict support inequalities are geometric. -/

/- Exact current draft body: A3LocalSupports. -/
section Projectivity_A3LocalSupports



/-! UNVERIFIED. The six literal square signs construct local support
points on every actual full cone. The final theorem uses the checked
finite gluing argument to obtain an actual normal polytope. -/

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Unimodular.A3LocalSupports

open TypeAFanGeometry A3CanonicalSigns A3SquareCones A3MaximalPresentations
open A3ProjectiveNecessity A3RegularFanCount SquareSubdivision
open A3SupportForms A3SignPatterns LocalSupportGluing NormalFanSupport StrictSupportNormalFan
open TauCeti.Toric

attribute [local instance] Classical.propDecidable

abbrev Labels := Fin 4 ≃ Vertex 3

def labelEdge (e : Labels) (a b : Fin 4) (hab : a ≠ b) : Edge 3 :=
  ⟨(e a,e b),e.injective.ne hab⟩

def matrixHeight (H : Edge 3 → ℝ) (e : Labels) : A3FacetSupports.HeightMatrix :=
  fun a b => if hab : a ≠ b then H (labelEdge e a b hab) else 0

theorem matrixHeight_ne (H : Edge 3 → ℝ) (e : Labels) (a b : Fin 4) (hab : a ≠ b) :
    matrixHeight H e a b = H (labelEdge e a b hab) := dif_pos hab

def cornerAt (e : Labels) (j : Fin 4) : Edge 3 :=
  labelEdge e (A3FacetCharts.squarePairs j).1 (A3FacetCharts.squarePairs j).2
    (by fin_cases j <;> decide)

theorem matrixHeight_corner (H : Edge 3 → ℝ) (e : Labels) (j : Fin 4) :
    matrixHeight H e (A3FacetSupports.squarePairs j).1 (A3FacetSupports.squarePairs j).2 =
      H (cornerAt e j) := by
  apply matrixHeight_ne

/-- A crossing root of a square cut is one of its four actual corners. -/
theorem square_crossing_corner (e : Labels) (r : Edge 3)
    (hr : rootRay r ∈ cutFace (A3FacetCharts.squareCut e)) :
    ∃ j : Fin 4, r = cornerAt e j := by
  obtain ⟨⟨p,q⟩,hpq⟩ := r
  obtain ⟨a,rfl⟩ := e.surjective p
  obtain ⟨b,rfl⟩ := e.surjective q
  have hc := (root_mem_cutFace_iff (A3FacetCharts.squareCut e) hpq).mp hr
  have hp := hc.1
  have hq := hc.2
  fin_cases a <;> fin_cases b <;>
    norm_num [A3FacetCharts.squareCut,e.injective.eq_iff] at hp <;>
    norm_num [A3FacetCharts.squareCut,e.injective.eq_iff] at hq
  all_goals first
    | exact ⟨0,Subtype.ext rfl⟩
    | exact ⟨1,Subtype.ext rfl⟩
    | exact ⟨2,Subtype.ext rfl⟩
    | exact ⟨3,Subtype.ext rfl⟩

def SupportsOnCut (H : Edge 3 → ℝ) (C : PointedCone ℝ (Ambient 3))
    (S : Finset (Vertex 3)) (p : Module.Dual ℝ (Ambient 3)) : Prop :=
  C ≤ cutCone S ∧
    (∀ r, rootRay r ∈ C → p (rootRay r) = H r) ∧
    (∀ r, rootRay r ∈ cutFace S → rootRay r ∉ C → p (rootRay r) < H r)

theorem cellCone_le_cutCone (e : Labels) (s : Key) :
    cellCone e s ≤ cutCone (A3FacetCharts.squareCut e) := by
  rw [cutCone_eq_hull_cutFace]
  exact Submodule.span_mono (cellSet_subset_facet e s)

theorem square_triangle_support (H : Edge 3 → ℝ) (e : Labels) (k : Fin 4)
    (hdelta : 0 < A3FacetSupports.alternatingSign k *
      A3FacetSupports.squareDefect (matrixHeight H e)) :
    SupportsOnCut H (cellCone e (triangle k)) (A3FacetCharts.squareCut e)
      (A3FacetSupports.squarePoint e k (matrixHeight H e)) := by
  refine ⟨cellCone_le_cutCone e _,?_,?_⟩
  · intro r hr
    have hf : rootRay r ∈ cutFace (A3FacetCharts.squareCut e) :=
      (root_mem_cutFace_iff _ r.property).mpr
        ((root_mem_cutCone_iff _ r.property).mp (cellCone_le_cutCone e _ hr))
    obtain ⟨j,rfl⟩ := square_crossing_corner e r hf
    have hj : j ≠ k := (mem_triangle k j).mp ((corner_mem_cellCone e _ j).mp hr)
    have he := A3FacetSupports.squarePoint_on_corner e (matrixHeight H e) k j hj
    rw [matrixHeight_corner] at he
    exact he
  · intro r hf hr
    obtain ⟨j,rfl⟩ := square_crossing_corner e r hf
    have hj : j = k := by
      by_contra hne
      exact hr ((corner_mem_cellCone e _ j).mpr ((mem_triangle k j).mpr hne))
    subst j
    have he := A3FacetSupports.squarePoint_missing_strict e (matrixHeight H e) k hdelta
    rw [matrixHeight_corner] at he
    exact he

theorem square_whole_support (H : Edge 3 → ℝ) (e : Labels)
    (hdelta : A3FacetSupports.squareDefect (matrixHeight H e) = 0) :
    SupportsOnCut H (cellCone e Finset.univ) (A3FacetCharts.squareCut e)
      (A3FacetSupports.squarePoint e 0 (matrixHeight H e)) := by
  refine ⟨cellCone_le_cutCone e _,?_,?_⟩
  · intro r hr
    have hf : rootRay r ∈ cutFace (A3FacetCharts.squareCut e) :=
      (root_mem_cutFace_iff _ r.property).mpr
        ((root_mem_cutCone_iff _ r.property).mp (cellCone_le_cutCone e _ hr))
    obtain ⟨j,rfl⟩ := square_crossing_corner e r hf
    have he := A3FacetSupports.squarePoint_whole e (matrixHeight H e) hdelta j
    rw [matrixHeight_corner] at he
    exact he
  · intro r hf hr
    obtain ⟨j,rfl⟩ := square_crossing_corner e r hf
    exact (hr ((corner_mem_cellCone e Finset.univ j).mpr (Finset.mem_univ j))).elim

theorem singleton_support (H : Edge 3 → ℝ) (e : Labels) :
    SupportsOnCut H (cutCone (A3FacetCharts.singletonCut e)) (A3FacetCharts.singletonCut e)
      (A3FacetSupports.singletonPoint e (matrixHeight H e)) := by
  refine ⟨le_refl _,?_,?_⟩
  · intro r hr
    obtain ⟨⟨p,q⟩,hpq⟩ := r
    obtain ⟨a,rfl⟩ := e.surjective p
    obtain ⟨b,rfl⟩ := e.surjective q
    obtain ⟨ha,hb⟩ := (root_mem_cutCone_iff (A3FacetCharts.singletonCut e) hpq).mp hr
    have ha0 : a = 0 := by simpa [A3FacetCharts.singletonCut,e.injective.eq_iff] using ha
    subst a
    have hb0 : b ≠ 0 := fun h => hpq (congrArg e h.symm)
    have he := A3FacetSupports.singletonPoint_on_root e (matrixHeight H e) b hb0
    rw [matrixHeight_ne H e 0 b (Ne.symm hb0)] at he
    exact he
  · intro r hf hr
    exact (hr ((root_mem_cutCone_iff _ r.property).mpr
      ((root_mem_cutFace_iff _ r.property).mp hf))).elim

theorem triple_support (H : Edge 3 → ℝ) (e : Labels) :
    SupportsOnCut H (cutCone (A3FacetCharts.tripleCut e)) (A3FacetCharts.tripleCut e)
      (A3FacetSupports.triplePoint e (matrixHeight H e)) := by
  refine ⟨le_refl _,?_,?_⟩
  · intro r hr
    obtain ⟨⟨p,q⟩,hpq⟩ := r
    obtain ⟨a,rfl⟩ := e.surjective p
    obtain ⟨b,rfl⟩ := e.surjective q
    obtain ⟨ha,hb⟩ := (root_mem_cutCone_iff (A3FacetCharts.tripleCut e) hpq).mp hr
    have hb3 : b = 3 := by
      fin_cases b <;> simp_all [A3FacetCharts.tripleCut,e.injective.eq_iff]
    subst b
    have ha3 : a ≠ 3 := fun h => hpq (congrArg e h)
    have he := A3FacetSupports.triplePoint_on_root e (matrixHeight H e) a ha3
    rw [matrixHeight_ne H e a 3 ha3] at he
    exact he
  · intro r hf hr
    exact (hr ((root_mem_cutCone_iff _ r.property).mpr
      ((root_mem_cutFace_iff _ r.property).mp hf))).elim

def HasPrescribedSigns (Φ : CompleteRootFan) (H : Edge 3 → ℝ) : Prop :=
  ∀ i : Fin 6, SignType.sign (A3FacetSupports.squareDefect (matrixHeight H (labels i))) =
    choiceSignEquiv (squareChoice Φ i)

theorem square_maximal_support (Φ : CompleteRootFan) (H : Edge 3 → ℝ)
    (hH : HasPrescribedSigns Φ H) (i : Fin 6) (s : Key)
    (hs : s ∈ maximalKeys (squareChoice Φ i)) :
    ∃ p, SupportsOnCut H (cellCone (labels i) s) (A3FacetCharts.squareCut (labels i)) p := by
  have hsign := hH i
  cases hc : squareChoice Φ i with
  | none =>
    rw [hc] at hs hsign
    have he : s = Finset.univ := by simpa only [maximalKeys,Finset.mem_singleton] using hs
    subst s
    change SignType.sign _ = 0 at hsign
    exact ⟨_,square_whole_support H (labels i) (sign_eq_zero_iff.mp hsign)⟩
  | some b =>
    cases b
    · rw [hc] at hs hsign
      change SignType.sign _ = 1 at hsign
      have hp := sign_eq_one_iff.mp hsign
      simp only [maximalKeys,Finset.mem_insert,Finset.mem_singleton] at hs
      rcases hs with rfl | rfl
      all_goals refine ⟨_,square_triangle_support H (labels i) _ ?_⟩
      all_goals simpa [A3FacetSupports.alternatingSign] using hp
    · rw [hc] at hs hsign
      change SignType.sign _ = -1 at hsign
      have hn := sign_eq_neg_one_iff.mp hsign
      simp only [maximalKeys,Finset.mem_insert,Finset.mem_singleton] at hs
      rcases hs with rfl | rfl
      all_goals refine ⟨_,square_triangle_support H (labels i) _ ?_⟩
      all_goals simpa [A3FacetSupports.alternatingSign] using neg_pos.mpr hn

/-- No full cone is omitted: the actual exhaustive geometric presentation
supplies its support point in one of the preceding three cases. -/
theorem localSupportData_exists (Φ : CompleteRootFan) (H : Edge 3 → ℝ)
    (hH : HasPrescribedSigns Φ H) : Nonempty (LocalSupportData Φ.val H) := by
  have hex : ∀ C : FullCone Φ.val, ∃ S p, SupportsOnCut H C.val.val S p := by
    intro C
    rcases full_cone_presentation Φ C with ⟨i,s,hs,he⟩ | ⟨e,he⟩ | ⟨e,he⟩
    · obtain ⟨p,hp⟩ := square_maximal_support Φ H hH i s hs
      exact ⟨_,p,he.symm ▸ hp⟩
    · exact ⟨_,_,he.symm ▸ singleton_support H e⟩
    · exact ⟨_,_,he.symm ▸ triple_support H e⟩
  choose S p hp using hex
  exact ⟨{
    cut := S
    point := p
    cone_le := fun C => (hp C).1
    on_ray := fun C => (hp C).2.1
    off_ray_in_cut := fun C => (hp C).2.2 }⟩

def edgeHeight (h : Heights) (r : Edge 3) : ℝ := h (edgeEquiv.symm r)

theorem matrixHeight_canonical (h : Heights) (i : Fin 6) :
    matrixHeight (edgeHeight h) (labels i) = localHeightMatrix h i := by
  funext a b
  by_cases hab : a = b
  · subst b
    simp [matrixHeight,localHeightMatrix,height]
  · rw [matrixHeight,dif_pos hab,localHeightMatrix,height,
      dif_pos ((order_bijective i).1.ne hab)]
    apply congrArg h
    apply edgeEquiv.injective
    rw [Equiv.apply_symm_apply]
    rfl

theorem prescribedSigns_of_forms (Φ : CompleteRootFan) (h : Heights)
    (hh : ∀ i, SignType.sign (forms h i) = a3SignEquiv Φ i) :
    HasPrescribedSigns Φ (edgeHeight h) := by
  intro i
  rw [matrixHeight_canonical]
  have hsign := hh i
  rw [← ordered_square_defect h i] at hsign
  exact hsign

/-- The converse is an actual finite normal-polytope construction, with
all original fan cones included. Integral sign heights are used before
one integral common height shift; no assumed projectivity test occurs. -/
theorem normalFan_of_admissible (Φ : CompleteRootFan)
    (ha : Admissible (fun i => coefficientSigns i * a3SignEquiv Φ i)) :
    HasPolytopeNormalFan Φ.val := by
  obtain ⟨h,hh⟩ := (exists_integral_heights_with_sign_iff (a3SignEquiv Φ)).mpr ha
  obtain ⟨d⟩ := localSupportData_exists Φ (edgeHeight (fun e => (h e : ℝ)))
    (prescribedSigns_of_forms Φ _ hh)
  exact LocalSupportGluing.hasPolytopeNormalFan Φ.property.1 Φ.property.2 d

#print axioms square_triangle_support
#print axioms singleton_support
#print axioms triple_support
#print axioms localSupportData_exists
#print axioms normalFan_of_admissible

end Unimodular.A3LocalSupports
end

end Projectivity_A3LocalSupports

/- Exact current draft body: A3ProjectiveCounts. -/
section Projectivity_A3ProjectiveCounts



/-! UNVERIFIED. Cardinalities are transported through a bijection from
actual complete fans, after proving geometric projectivity and geometric
regularity equivalent to the corresponding sign predicates. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Unimodular.A3ProjectiveCounts

open TypeAFanGeometry A3FacetCharts A3FanChoices A3CanonicalSigns A3RegularFanCount
open A3SupportForms A3SignPatterns A3LocalSupports A3ProjectiveNecessity
open SubdivisionTriangulations NormalFanSupport TauCeti.Toric

/-- The unique relation's coefficient signs orient the six coordinates.
This is an actual equivalence, so it does not identify labelled fans. -/
def normalizedSignEquiv : CompleteRootFan ≃ (Fin 6 → SignType) :=
  a3SignEquiv.trans (reorient coefficientSigns coefficientSigns_ne_zero)

/-- The complete projectivity criterion is derived in both directions from
an actual finite normal polytope, not adopted as a definition. -/
theorem normalFan_iff_admissible (Φ : CompleteRootFan) :
    HasPolytopeNormalFan Φ.val ↔ Admissible (normalizedSignEquiv Φ) :=
  ⟨admissible_of_normalFan Φ,normalFan_of_admissible Φ⟩

/-- Every actual cell is a simplex precisely when each of the six square
facets has been split. The eight triangles carry no extra condition. -/
theorem regular_iff_noZero_raw (Φ : CompleteRootFan) :
    Φ.val.IsRegular ↔ NoZero (a3SignEquiv Φ) := by
  rw [fan_isRegular_iff_cut_triangulations (by decide) Φ.val Φ.property.1 Φ.property.2]
  constructor
  · intro h i
    rw [a3SignEquiv_apply,choiceSign_nonzero]
    exact (square_facet_isTriangulation_iff (labels i) _).mp (h (indexedCut i))
  · intro h S
    by_cases hs : S.val.card = 2
    · obtain ⟨i,hi⟩ := squareCutIndexEquiv.surjective (⟨S,hs⟩ : SquareCut)
      have he : indexedCut i = S := congrArg Subtype.val hi
      subst S
      apply (square_facet_isTriangulation_iff (labels i) _).mpr
      exact (choiceSign_nonzero _).mp (h i)
    · apply (cut_isTriangulation_iff S _).mpr
      simp [ChoiceIsSplit,choiceOption,hs]

theorem regular_iff_noZero (Φ : CompleteRootFan) :
    Φ.val.IsRegular ↔ NoZero (normalizedSignEquiv Φ) := by
  rw [regular_iff_noZero_raw]
  exact (noZero_reorient_iff coefficientSigns coefficientSigns_ne_zero (a3SignEquiv Φ)).symm

def projectiveFanEquiv :
    {Φ : CompleteRootFan // HasPolytopeNormalFan Φ.val} ≃
      {s : Fin 6 → SignType // Admissible s} :=
  Equiv.subtypeEquiv normalizedSignEquiv normalFan_iff_admissible

def projectiveRegularFanEquiv :
    {Φ : CompleteRootFan // HasPolytopeNormalFan Φ.val ∧ Φ.val.IsRegular} ≃
      {s : Fin 6 → SignType // Admissible s ∧ NoZero s} :=
  Equiv.subtypeEquiv normalizedSignEquiv (fun Φ =>
    and_congr (normalFan_iff_admissible Φ) (regular_iff_noZero Φ))

def nonprojectiveRegularFanEquiv :
    {Φ : CompleteRootFan // Φ.val.IsRegular ∧ ¬HasPolytopeNormalFan Φ.val} ≃
      {s : Fin 6 → SignType // NoZero s ∧ ¬Admissible s} :=
  Equiv.subtypeEquiv normalizedSignEquiv (fun Φ =>
    and_congr (regular_iff_noZero Φ) (not_congr (normalFan_iff_admissible Φ)))

/-- The 603 counted objects are actual labelled complete fans on all
original twelve roots with a finite normal-polytope witness. -/
theorem a3_projective_fan_count :
    Nat.card {Φ : CompleteRootFan // HasPolytopeNormalFan Φ.val} = 603 := by
  rw [Nat.card_congr projectiveFanEquiv,Nat.card_eq_fintype_card]
  exact six_admissible_pattern_count

theorem a3_projective_regular_fan_count :
    Nat.card {Φ : CompleteRootFan // HasPolytopeNormalFan Φ.val ∧ Φ.val.IsRegular} = 62 := by
  rw [Nat.card_congr projectiveRegularFanEquiv,Nat.card_eq_fintype_card]
  exact six_admissible_noZero_pattern_count

theorem six_nonadmissible_noZero_count :
    Fintype.card {s : Fin 6 → SignType // NoZero s ∧ ¬Admissible s} = 2 := by decide

/-- Exactly two actual smooth labelled fans are nonprojective. -/
theorem a3_nonprojective_regular_fan_count :
    Nat.card {Φ : CompleteRootFan // Φ.val.IsRegular ∧ ¬HasPolytopeNormalFan Φ.val} = 2 := by
  rw [Nat.card_congr nonprojectiveRegularFanEquiv,Nat.card_eq_fintype_card]
  exact six_nonadmissible_noZero_count

/-- The two exceptions have all six signed terms pointing in the same
direction, as asserted in the paper. -/
theorem noZero_nonadmissible_iff : ∀ s : Fin 6 → SignType,
    NoZero s → (¬Admissible s ↔ (∀ i, s i = 1) ∨ (∀ i, s i = -1)) := by decide

theorem smooth_exceptions_exact (Φ : CompleteRootFan) (hreg : Φ.val.IsRegular) :
    ¬HasPolytopeNormalFan Φ.val ↔
      (∀ i, coefficientSigns i * a3SignEquiv Φ i = 1) ∨
        (∀ i, coefficientSigns i * a3SignEquiv Φ i = -1) := by
  rw [normalFan_iff_admissible]
  exact noZero_nonadmissible_iff (normalizedSignEquiv Φ) ((regular_iff_noZero Φ).mp hreg)

#print axioms normalFan_iff_admissible
#print axioms regular_iff_noZero
#print axioms projectiveFanEquiv
#print axioms a3_projective_fan_count
#print axioms a3_projective_regular_fan_count
#print axioms a3_nonprojective_regular_fan_count
#print axioms smooth_exceptions_exact

end Unimodular.A3ProjectiveCounts
end

end Projectivity_A3ProjectiveCounts

#check "UNIMODULAR_A3_PROJECTIVITY_EOF_V2"
