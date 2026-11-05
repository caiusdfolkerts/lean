module

public import Recovery.Unimodular.NativePort.A3IntegralProjectivity
public import Unimodular.FanFaithfulness

@[expose] public section

/-! UNVERIFIED until the exact native compiler run succeeds.
Actual nonprojective single-square primitive replacement.
All input rays, cones, and strict support inequalities are geometric. -/

/- Exact current draft body: A3PrimitiveReplacement. -/
section Projectivity_A3PrimitiveReplacement



/-! UNVERIFIED. The paper's one-square example consists of actual complete
fans. It is nonprojective after splitting precisely one square. The change
is Graver-primitive for the genuine boundary/degree equation map: all fans
using only the two endpoint cone sets are proved to be endpoints, and the
checked universal Graver path then supplies the direct primitive move. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Unimodular.A3PrimitiveReplacement

open TypeAFanGeometry A3FacetCharts A3CanonicalSigns A3SquareCones A3LocalSupports
open A3ProjectiveNecessity A3ProjectiveCounts A3RegularFanCount SquareSubdivision
open A3SupportForms A3SignPatterns NormalFanSupport TauCeti.Toric

/-- The canonical unrefined face fan, constructed through the actual
fan/subdivision equivalence and leaving every square whole. -/
def seed : CompleteRootFan := a3SignEquiv.symm (fun _ => 0)

/-- Split precisely one actual square in one of its two possible ways. -/
def singleSplit (i : Fin 6) (b : Bool) : CompleteRootFan :=
  a3SignEquiv.symm (fun j => if j = i then choiceSignEquiv (some b) else 0)

@[simp] theorem squareChoice_seed (j : Fin 6) : squareChoice seed j = none := by
  apply choiceSignEquiv.injective
  change a3SignEquiv seed j = 0
  simp only [seed,Equiv.apply_symm_apply]

@[simp] theorem squareChoice_singleSplit (i j : Fin 6) (b : Bool) :
    squareChoice (singleSplit i b) j = if j = i then some b else none := by
  apply choiceSignEquiv.injective
  change a3SignEquiv (singleSplit i b) j = choiceSignEquiv _
  rw [singleSplit,Equiv.apply_symm_apply]
  by_cases hj : j = i <;> simp [hj,choiceSignEquiv]

theorem singleSplit_ne_seed (i : Fin 6) (b : Bool) : singleSplit i b ≠ seed := by
  intro h
  have he := congrArg (fun Φ => squareChoice Φ i) h
  simp only [squareChoice_singleSplit,ite_true,squareChoice_seed] at he
  cases he

theorem seed_projective : HasPolytopeNormalFan seed.val := by
  apply (normalFan_iff_admissible seed).mpr
  left
  intro i
  change coefficientSigns i * a3SignEquiv seed i = 0
  simp only [seed,Equiv.apply_symm_apply,mul_zero]

theorem singleton_pattern_nonadmissible : ∀ (i : Fin 6) (b : Bool),
    ¬Admissible (fun j => coefficientSigns j *
      (if j = i then choiceSignEquiv (some b) else 0)) := by decide

/-- Either diagonal split of any one square is nonprojective when the
other five squares remain whole. -/
theorem singleSplit_nonprojective (i : Fin 6) (b : Bool) :
    ¬HasPolytopeNormalFan (singleSplit i b).val := by
  rw [normalFan_iff_admissible]
  change ¬Admissible (fun j => coefficientSigns j * a3SignEquiv (singleSplit i b) j)
  rw [singleSplit,Equiv.apply_symm_apply]
  exact singleton_pattern_nonadmissible i b

/-- A cell of one actual fan whose cone belongs to another actual fan is
also a cell of the latter's cut subdivision. The intrinsic normalized
root-polytope section recovers precisely the original cell. -/
theorem catalogue_of_cone_mem (Φ Θ : CompleteRootFan) (i : Fin 6) (s : Key)
    (hs : s ∈ catalogue (squareChoice Θ i))
    (hcone : cellCone (labels i) s ∈ Φ.val.cones) :
    s ∈ catalogue (squareChoice Φ i) := by
  let D := fanCutSubdivisions Θ.val Θ.property.1 Θ.property.2
  have hcell : cellSet (labels i) s ∈ (D.subdivision (indexedCut i)).cells :=
    (facet_cell_iff (labels i) _ s).mpr hs
  have hroot : rootCell (cellCone (labels i) s) = cellSet (labels i) s :=
    D.rootCell_hull hcell
  have hcell' : rootCell (cellCone (labels i) s) ∈
      ((fanCutSubdivisions Φ.val Φ.property.1 Φ.property.2).subdivision (indexedCut i)).cells :=
    ⟨cellCone (labels i) s,hcone,cellCone_le_cutCone (labels i) s,rfl⟩
  rw [hroot] at hcell'
  exact (facet_cell_iff (labels i) _ s).mp hcell'

theorem catalogue_sub_endpoint_union (Φ Ψ Θ : CompleteRootFan)
    (huse : ∀ C ∈ Θ.val.cones, C ∈ Φ.val.cones ∨ C ∈ Ψ.val.cones) (i : Fin 6) :
    ∀ s ∈ catalogue (squareChoice Θ i),
      s ∈ catalogue (squareChoice Φ i) ∨ s ∈ catalogue (squareChoice Ψ i) := by
  intro s hs
  let D := fanCutSubdivisions Θ.val Θ.property.1 Θ.property.2
  have hcell : cellSet (labels i) s ∈ (D.subdivision (indexedCut i)).cells :=
    (facet_cell_iff (labels i) _ s).mpr hs
  have hmem : cellCone (labels i) s ∈ D.toFan.cones := ⟨indexedCut i,_,hcell,rfl⟩
  have hmem' : cellCone (labels i) s ∈ Θ.val.cones := by
    simpa only [D,toFan_fanCutSubdivisions (by decide) Θ.val Θ.property.1 Θ.property.2] using hmem
  rcases huse _ hmem' with hΦ | hΨ
  · exact Or.inl (catalogue_of_cone_mem Φ Θ i s hs hΦ)
  · exact Or.inr (catalogue_of_cone_mem Ψ Θ i s hs hΨ)

theorem none_catalogue_rigid : ∀ c : Option Bool,
    (∀ s ∈ catalogue c, s ∈ catalogue none) → c = none := by decide

theorem one_split_catalogue_rigid : ∀ (b : Bool) (c : Option Bool),
    (∀ s ∈ catalogue c, s ∈ catalogue none ∨ s ∈ catalogue (some b)) →
      c = none ∨ c = some b := by decide

/-- There is no third complete fan using only cones from these endpoints.
This uses the actual cell catalogue, not a premise about possible paths. -/
theorem only_endpoint_fans (i : Fin 6) (b : Bool) (Θ : CompleteRootFan)
    (huse : ∀ C ∈ Θ.val.cones, C ∈ seed.val.cones ∨ C ∈ (singleSplit i b).val.cones) :
    Θ = seed ∨ Θ = singleSplit i b := by
  classical
  have hcat := catalogue_sub_endpoint_union seed (singleSplit i b) Θ huse
  have hother (j : Fin 6) (hj : j ≠ i) : squareChoice Θ j = none := by
    apply none_catalogue_rigid
    intro s hs
    have h := hcat j s hs
    simpa only [squareChoice_seed,squareChoice_singleSplit,if_neg hj,or_self] using h
  have hi : squareChoice Θ i = none ∨ squareChoice Θ i = some b := by
    apply one_split_catalogue_rigid
    intro s hs
    simpa only [squareChoice_seed,squareChoice_singleSplit,ite_true] using hcat i s hs
  rcases hi with hi | hi
  · left
    apply a3SignEquiv.injective
    funext j
    change choiceSignEquiv (squareChoice Θ j) = choiceSignEquiv (squareChoice seed j)
    rw [squareChoice_seed]
    by_cases hj : j = i
    · subst j
      rw [hi]
    · rw [hother j hj]
  · right
    apply a3SignEquiv.injective
    funext j
    change choiceSignEquiv (squareChoice Θ j) =
      choiceSignEquiv (squareChoice (singleSplit i b) j)
    rw [squareChoice_singleSplit]
    by_cases hj : j = i
    · subst j
      rw [if_pos rfl,hi]
    · rw [if_neg hj,hother j hj]

/-- The roots positively span because the actual seed fan is complete.
This checks the generic-direction theorem's precise hypothesis. -/
theorem roots_positive_span :
    PointedCone.hull ℝ (Set.range (fun e : Edge 3 =>
      FanBridge.standardEmbedding 3 (rootFamily 3 e))) = ⊤ := by
  apply top_unique
  intro x hx
  obtain ⟨C,hC,hxC⟩ := seed.val.isComplete_iff.mp seed.property.1 x
  rw [fan_cone_eq_hull_roots seed.val seed.property.2 hC] at hxC
  apply (Submodule.span_mono (s := coneRootSet C) (t := Set.range (fun e : Edge 3 =>
    FanBridge.standardEmbedding 3 (rootFamily 3 e))) ?_) hxC
  rintro y ⟨e,he,rfl⟩
  exact ⟨e,rfl⟩

/-- The single-square change is an actual Graver-primitive relation for
the entire boundary matrix and generic degree row, for every generic
choice of direction. No proper conformal subreplacement exists. -/
theorem singleSplit_primitive (i : Fin 6) (b : Bool) {w : Ambient 3}
    (hw : RayHyperplanes.GenericDirection (fun e : Edge 3 =>
      FanBridge.standardEmbedding 3 (rootFamily 3 e)) w) :
    Graver.Primitive (AllowedBlocks.equationMap (FanBridge.standardEmbedding 3)
      (rootFamily 3) w).ker
      (AllowedBlocks.indicator (FanBridge.standardEmbedding 3) (rootFamily 3) (singleSplit i b) -
        AllowedBlocks.indicator (FanBridge.standardEmbedding 3) (rootFamily 3) seed) := by
  classical
  let ι := FanBridge.standardEmbedding 3
  let u := rootFamily 3
  obtain ⟨G,hG,hpath⟩ := AllowedBlocks.theorem_1_1_all_cones ι u
    (FanBridge.standardEmbedding_isIntegralLattice 3)
    (fun e => realRoot_ne_zero e.property) roots_positive_span hw seed (singleSplit i b)
  let R : CompleteRootFan → CompleteRootFan → Prop := fun A B =>
    AllowedBlocks.indicator ι u B - AllowedBlocks.indicator ι u A ∈ G ∧
      (∀ C ∈ A.val.cones, C ∈ seed.val.cones ∨ C ∈ (singleSplit i b).val.cones) ∧
      (∀ C ∈ B.val.cones, C ∈ seed.val.cones ∨ C ∈ (singleSplit i b).val.cones)
  have hpath' : Relation.ReflTransGen R seed (singleSplit i b) := hpath
  have hcollapse : ∀ {A : CompleteRootFan}, Relation.ReflTransGen R seed A →
      A = seed ∨ R seed (singleSplit i b) := by
    intro A h
    induction h with
    | refl => exact Or.inl rfl
    | @tail A B hprev hstep ih =>
      rcases ih with he | hdirect
      · subst A
        rcases only_endpoint_fans i b B hstep.2.2 with hB | hB
        · exact Or.inl hB
        · exact Or.inr (hB ▸ hstep)
      · exact Or.inr hdirect
  have hdirect : R seed (singleSplit i b) :=
    (hcollapse hpath').resolve_left (singleSplit_ne_seed i b)
  exact (hG _).mp hdirect.1

/-- A fully geometric nonprojective fan is obtained from a projective
seed by one primitive integral replacement, with every one of the other
five square facets unchanged. -/
theorem one_square_nonprojective_primitive (i : Fin 6) (b : Bool) :
    HasPolytopeNormalFan seed.val ∧ ¬HasPolytopeNormalFan (singleSplit i b).val ∧
    (∀ j, squareChoice seed j = none) ∧
    squareChoice (singleSplit i b) i = some b ∧
    (∀ j, j ≠ i → squareChoice (singleSplit i b) j = none) ∧
    ∃ w : Ambient 3,
      RayHyperplanes.GenericDirection (fun e : Edge 3 =>
        FanBridge.standardEmbedding 3 (rootFamily 3 e)) w ∧
      Graver.Primitive (AllowedBlocks.equationMap (FanBridge.standardEmbedding 3)
        (rootFamily 3) w).ker
        (AllowedBlocks.indicator (FanBridge.standardEmbedding 3) (rootFamily 3) (singleSplit i b) -
          AllowedBlocks.indicator (FanBridge.standardEmbedding 3) (rootFamily 3) seed) := by
  obtain ⟨w,hw⟩ := (RayHyperplanes.genericDirection_dense
    (fun e : Edge 3 => FanBridge.standardEmbedding 3 (rootFamily 3 e))).nonempty
  exact ⟨seed_projective,singleSplit_nonprojective i b,squareChoice_seed,
    by simp,by intro j hj; simp [hj],w,hw,singleSplit_primitive i b hw⟩

#print axioms seed_projective
#print axioms singleSplit_nonprojective
#print axioms only_endpoint_fans
#print axioms roots_positive_span
#print axioms singleSplit_primitive
#print axioms one_square_nonprojective_primitive

end Unimodular.A3PrimitiveReplacement
end

end Projectivity_A3PrimitiveReplacement

/- Exact current draft body: A3ReplacementCones. -/
section Projectivity_A3ReplacementCones



/-! UNVERIFIED. The primitive example removes exactly the full cone over
one whole square and inserts exactly its two triangular full cones.
All other full cones agree literally, in the original ambient space. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Unimodular.A3ReplacementCones

open TypeAFanGeometry A3FacetCharts A3CanonicalSigns A3SquareCones A3MaximalPresentations
open A3ProjectiveNecessity A3PrimitiveReplacement A3RegularFanCount SquareSubdivision
open NormalFanSupport TauCeti.Toric

/-- Every triangular cut cone occurs in every complete root fan. -/
theorem singleton_cutCone_mem (Φ : CompleteRootFan) (e : Labels) :
    cutCone (singletonCut e) ∈ Φ.val.cones := by
  classical
  let S : ProperCut 3 := ⟨singletonCut e,⟨e 0,by simp [singletonCut]⟩,by
    intro h
    have hm : e 1 ∈ singletonCut e := h.symm ▸ Finset.mem_univ (e 1)
    simpa [singletonCut,e.injective.eq_iff] using hm⟩
  exact cutCone_mem_of_whole Φ S
    (singleton_whole_mem e ((fanCutSubdivisions Φ.val Φ.property.1 Φ.property.2).subdivision S))

theorem triple_cutCone_mem (Φ : CompleteRootFan) (e : Labels) :
    cutCone (tripleCut e) ∈ Φ.val.cones := by
  classical
  let S : ProperCut 3 := ⟨tripleCut e,⟨e 0,by simp [tripleCut]⟩,by
    intro h
    have hm : e 3 ∈ tripleCut e := h.symm ▸ Finset.mem_univ (e 3)
    simpa [tripleCut,e.injective.eq_iff] using hm⟩
  exact cutCone_mem_of_whole Φ S
    (triple_whole_mem e ((fanCutSubdivisions Φ.val Φ.property.1 Φ.property.2).subdivision S))

theorem whole_not_split_catalogue : ∀ b : Bool,
    (Finset.univ : Key) ∉ catalogue (some b) := by decide

theorem split_triangle_not_whole_catalogue : ∀ (b : Bool) (k : Fin 4),
    triangle k ∈ maximalKeys (some b) → triangle k ∉ catalogue none := by decide

theorem split_maximal_triangle : ∀ (b : Bool) (s : Key),
    s ∈ maximalKeys (some b) → ∃ k : Fin 4, s = triangle k := by decide

theorem whole_cone_not_singleSplit (i : Fin 6) (b : Bool) :
    cellCone (labels i) Finset.univ ∉ (singleSplit i b).val.cones := by
  intro h
  have hcat := catalogue_of_cone_mem (singleSplit i b) seed i Finset.univ
    (by rw [squareChoice_seed]; exact ⟨_,by simp [maximalKeys],faceKey_refl _⟩) h
  rw [squareChoice_singleSplit,if_pos rfl] at hcat
  exact whole_not_split_catalogue b hcat

theorem split_triangle_cone_not_seed (i : Fin 6) (b : Bool) (k : Fin 4)
    (hk : triangle k ∈ maximalKeys (some b)) :
    cellCone (labels i) (triangle k) ∉ seed.val.cones := by
  intro h
  have hcat := catalogue_of_cone_mem seed (singleSplit i b) i (triangle k)
    (by rw [squareChoice_singleSplit,if_pos rfl]; exact ⟨_,hk,faceKey_refl _⟩) h
  rw [squareChoice_seed] at hcat
  exact split_triangle_not_whole_catalogue b k hk hcat

/-- Exactly the original square's full cone is removed. -/
theorem removed_full_cone_iff (i : Fin 6) (b : Bool)
    (C : PointedCone ℝ (Ambient 3)) (hfull : Submodule.span ℝ (C : Set (Ambient 3)) = ⊤) :
    (C ∈ seed.val.cones ∧ C ∉ (singleSplit i b).val.cones) ↔
      C = cellCone (labels i) Finset.univ := by
  classical
  constructor
  · rintro ⟨hC,hnot⟩
    let D : FullCone seed.val := ⟨⟨C,hC⟩,hfull⟩
    rcases full_cone_presentation seed D with ⟨j,s,hs,he⟩ | ⟨e,he⟩ | ⟨e,he⟩
    · rw [squareChoice_seed] at hs
      have hs' : s = Finset.univ := by simpa only [maximalKeys,Finset.mem_singleton] using hs
      subst s
      by_cases hj : j = i
      · simpa only [hj] using he
      · exfalso
        apply hnot
        rw [show C = cellCone (labels j) Finset.univ from he]
        apply maximal_square_cone_mem
        simp [squareChoice_singleSplit,hj,maximalKeys]
    · change C = cutCone (singletonCut e) at he
      exact (hnot (he.symm ▸ singleton_cutCone_mem (singleSplit i b) e)).elim
    · change C = cutCone (tripleCut e) at he
      exact (hnot (he.symm ▸ triple_cutCone_mem (singleSplit i b) e)).elim
  · intro he
    subst C
    exact ⟨maximal_square_cone_mem seed i (by simp [maximalKeys]),whole_cone_not_singleSplit i b⟩

/-- Exactly the two triangles of the selected diagonal are inserted. -/
theorem inserted_full_cone_iff (i : Fin 6) (b : Bool)
    (C : PointedCone ℝ (Ambient 3)) (hfull : Submodule.span ℝ (C : Set (Ambient 3)) = ⊤) :
    (C ∈ (singleSplit i b).val.cones ∧ C ∉ seed.val.cones) ↔
      ∃ k : Fin 4, triangle k ∈ maximalKeys (some b) ∧ C = cellCone (labels i) (triangle k) := by
  classical
  constructor
  · rintro ⟨hC,hnot⟩
    let D : FullCone (singleSplit i b).val := ⟨⟨C,hC⟩,hfull⟩
    rcases full_cone_presentation (singleSplit i b) D with ⟨j,s,hs,he⟩ | ⟨e,he⟩ | ⟨e,he⟩
    · rw [squareChoice_singleSplit] at hs
      by_cases hj : j = i
      · subst j
        rw [if_pos rfl] at hs
        obtain ⟨k,hk⟩ := split_maximal_triangle b s hs
        subst s
        exact ⟨k,hs,he⟩
      · rw [if_neg hj] at hs
        have hs' : s = Finset.univ := by simpa only [maximalKeys,Finset.mem_singleton] using hs
        subst s
        change C = cellCone (labels j) Finset.univ at he
        exact (hnot (he.symm ▸ maximal_square_cone_mem seed j (by simp [maximalKeys]))).elim
    · change C = cutCone (singletonCut e) at he
      exact (hnot (he.symm ▸ singleton_cutCone_mem seed e)).elim
    · change C = cutCone (tripleCut e) at he
      exact (hnot (he.symm ▸ triple_cutCone_mem seed e)).elim
  · rintro ⟨k,hk,rfl⟩
    exact ⟨maximal_square_cone_mem (singleSplit i b) i
      (by simpa only [squareChoice_singleSplit,ite_true] using hk),
      split_triangle_cone_not_seed i b k hk⟩

#print axioms singleton_cutCone_mem
#print axioms triple_cutCone_mem
#print axioms removed_full_cone_iff
#print axioms inserted_full_cone_iff

end Unimodular.A3ReplacementCones
end

end Projectivity_A3ReplacementCones

#check "UNIMODULAR_A3_PRIMITIVE_REPLACEMENT_EOF_V3"
