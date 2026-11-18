module

public import Recovery.Unimodular.NativePort.A3ProjectiveNecessity
public import Unimodular.FiniteStrictPerturbation

@[expose] public section

/-! UNVERIFIED until the exact native compiler run succeeds.
Actual full-cone presentation and global height-shift gluing.
The actual A3 local-support instantiation remains separate. -/

/- Exact current draft body: LocalSupportGluing. -/
section SupportGluing_LocalSupportGluing



/-! UNVERIFIED. Local support points on the actual cut facets glue after
one positive integral shift of every root height. The missing off-facet
inequalities are proved by a finite strict perturbation; the resulting
normal polytope is obtained from the checked geometric support theorem. -/

set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Unimodular.LocalSupportGluing

open TypeAFanGeometry NormalFanSupport StrictSupportNormalFan TauCeti.Toric

variable {n : ℕ}

def rootRay (e : Edge n) : Ambient n := realRoot e.val.1 e.val.2

/-- These data only concern a point's own cut facet. They do not include
any inequalities at roots outside that facet, or a normal-fan assertion. -/
structure LocalSupportData (Φ : Fan (FanBridge.standardEmbedding n))
    (H : Edge n → ℝ) where
  cut : FullCone Φ → Finset (Vertex n)
  point : FullCone Φ → Module.Dual ℝ (Ambient n)
  cone_le : ∀ C, C.val.val ≤ cutCone (cut C)
  on_ray : ∀ C e, rootRay e ∈ C.val.val → point C (rootRay e) = H e
  off_ray_in_cut : ∀ C e, rootRay e ∈ cutFace (cut C) →
    rootRay e ∉ C.val.val → point C (rootRay e) < H e

variable {Φ : Fan (FanBridge.standardEmbedding n)} {H : Edge n → ℝ}

/-- Every omitted off-facet root has a strictly positive gap for the
canonical unit-height cut support. -/
theorem cut_gap_pos (S : Finset (Vertex n)) (e : Edge n)
    (he : rootRay e ∉ cutFace S) : 0 < 1 - cutFunctional S (rootRay e) := by
  have hle : cutFunctional S (rootRay e) ≤ 1 := cutFunctional_root_le_one S _ _
  have hne : cutFunctional S (rootRay e) ≠ 1 := by
    intro h
    exact he ⟨root_mem_rootPolytope e.property,h⟩
  exact sub_pos.mpr (lt_of_le_of_ne hle hne)

/-- A single positive natural-number shift of all heights repairs all
old inter-facet inequalities while preserving every new diagonal gap. -/
theorem exists_strictSupportData (d : LocalSupportData Φ H) :
    ∃ N : ℕ, 0 < N ∧ ∃ s : StrictSupportData Φ rootRay,
      s.height = fun e => H e + (N : ℝ) := by
  classical
  letI : Fintype (FullCone Φ) := Fintype.ofFinite _
  let K := {p : FullCone Φ × Edge n // rootRay p.2 ∉ cutFace (d.cut p.1)}
  letI : Fintype K := Fintype.ofFinite _
  let a : K → ℝ := fun p => 1 - cutFunctional (d.cut p.val.1) (rootRay p.val.2)
  let b : K → ℝ := fun p => H p.val.2 - d.point p.val.1 (rootRay p.val.2)
  obtain ⟨N,hN,hgap⟩ := FiniteStrictPerturbation.positive_for_all_large_nat_scales
    a b (fun p => cut_gap_pos _ _ p.property)
  refine ⟨N,hN,{
    height := fun e => H e + (N : ℝ)
    point := fun C => d.point C + (N : ℝ) • cutFunctional (d.cut C)
    on_ray := ?_
    off_ray := ?_ },rfl⟩
  · intro C e he
    have hc : cutFunctional (d.cut C) (rootRay e) = 1 :=
      (cutFunctional_root_eq_one_iff _ _ _).mpr
        ((root_mem_cutCone_iff _ e.property).mp (d.cone_le C he))
    change d.point C (rootRay e) + (N : ℝ) * cutFunctional (d.cut C) (rootRay e) = _
    rw [d.on_ray C e he,hc,mul_one]
  · intro C e he
    change d.point C (rootRay e) + (N : ℝ) * cutFunctional (d.cut C) (rootRay e) < _
    by_cases hf : rootRay e ∈ cutFace (d.cut C)
    · have hc : cutFunctional (d.cut C) (rootRay e) = 1 := hf.2
      rw [hc,mul_one]
      have hh := d.off_ray_in_cut C e hf he
      linarith
    · have hh := hgap N (le_refl N) (⟨(C,e),hf⟩ : K)
      change 0 < (N : ℝ) * (1-cutFunctional (d.cut C) (rootRay e)) +
        (H e-d.point C (rootRay e)) at hh
      nlinarith

/-- The geometric conclusion uses all cones of the actual complete fan.
Local facet data are converted into global inequalities by the theorem
above, and the normal-cone equality is then proved in NormalFanGeometry. -/
theorem hasPolytopeNormalFan (hcomplete : Φ.IsComplete)
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ)
    (d : LocalSupportData Φ H) : HasPolytopeNormalFan Φ := by
  obtain ⟨N,hN,s,hs⟩ := exists_strictSupportData d
  exact typeA_hasPolytopeNormalFan Φ hcomplete hrays s

#print axioms cut_gap_pos
#print axioms exists_strictSupportData
#print axioms hasPolytopeNormalFan

end Unimodular.LocalSupportGluing
end

end SupportGluing_LocalSupportGluing

/- Exact current draft body: A3MaximalPresentations. -/
section SupportGluing_A3MaximalPresentations



/-! UNVERIFIED. Every full cone of an actual complete A3 root fan is
presented by a genuine maximal square cell or a whole triangular facet.
The assertion is derived from the existing subdivision bijection and
maximality of full-dimensional fan cones. -/

set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set

namespace Unimodular.A3MaximalPresentations

open TypeAFanGeometry A3FacetCharts A3CanonicalSigns A3SquareCones
open A3ProjectiveNecessity A3RegularFanCount A3FanChoices SquareSubdivision
open VertexSubdivisionTransport NormalFanSupport TauCeti.Toric

/-- Every square-facet cell has an actual planar vertex key. -/
theorem square_cell_has_key (e : Labels)
    (D : VertexSubdivision (cutFace (squareCut e))) {F : Set (Ambient 3)}
    (hF : F ∈ D.cells) :
    ∃ s ∈ catalogue (squareFacetSubdivisionEquiv e D), F = cellSet e s := by
  let E := (Equiv.cast (congrArg (fun P : Set (Ambient 3) => VertexSubdivision P)
    (squareChart_image e).symm)) D
  let D' := pullback (squareChart e) (squareChart_injective e) E
  have hF' : F ∈ E.cells := (cast_cell_iff (squareChart_image e).symm D F).mpr hF
  rw [← map_pullback (squareChart e) (squareChart_injective e) E] at hF'
  obtain ⟨G,hG,hGF⟩ := hF'
  have he : D' = canonicalSubdivision (squareFacetSubdivisionEquiv e D) :=
    (squareSubdivisionEquiv.symm_apply_apply D').symm
  change G ∈ D'.cells at hG
  rw [he] at hG
  obtain ⟨s,hs,rfl⟩ := hG
  exact ⟨s,hs,hGF.symm⟩

/-- A full cone contained in an actual square cut is one of the displayed
maximal square cones; lower-dimensional cells cannot contribute extra cases. -/
theorem full_square_presentation (Φ : CompleteRootFan) (C : FullCone Φ.val)
    (i : Fin 6) (hcut : C.val.val ≤ cutCone (squareCut (labels i))) :
    ∃ s ∈ maximalKeys (squareChoice Φ i), C.val.val = cellCone (labels i) s := by
  let D := fanCutSubdivisions Φ.val Φ.property.1 Φ.property.2
  have hcell : rootCell C.val.val ∈ (D.subdivision (indexedCut i)).cells :=
    ⟨C.val.val,C.val.property,hcut,rfl⟩
  obtain ⟨t,⟨s,hs,hst⟩,he⟩ := square_cell_has_key (labels i) _ hcell
  refine ⟨s,hs,?_⟩
  apply (FanMaximalCones.full_iff_maximal Φ.val Φ.property.1 C.val.property).mp C.property
  · exact maximal_square_cone_mem Φ i hs
  · rw [← hull_rootCell Φ.val Φ.property.2 C.val.property,he]
    exact Submodule.span_mono (Set.image_mono (hull_mono hst.1))

/-- An affine image of an actual triangle admits no subdivision except
its own face complex, so its whole image is a cell. -/
theorem image_triangle_whole_mem {W : Type*} [AddCommGroup W] [Module ℝ W]
    (f : Plane →ᵃ[ℝ] W) (hf : Function.Injective f) (i : Fin 4)
    (D : VertexSubdivision (f '' hull (triangle i))) :
    f '' hull (triangle i) ∈ D.cells := by
  apply (pullback_cell_iff f hf D (hull (triangle i))).mp
  rw [triangle_subdivision_unique i (pullback f hf D)]
  exact ⟨triangle i,faceKey_refl _,rfl⟩

theorem singleton_whole_mem (e : Labels)
    (D : VertexSubdivision (cutFace (singletonCut e))) :
    cutFace (singletonCut e) ∈ D.cells := by
  let E := Equiv.cast (congrArg (fun P : Set (Ambient 3) => VertexSubdivision P)
    (singletonChart_image e).symm) D
  have h := image_triangle_whole_mem (singletonChart e) (singletonChart_injective e) 2 E
  have hc := (cast_cell_iff (singletonChart_image e).symm D _).mp h
  simpa only [singletonChart_image] using hc

theorem triple_whole_mem (e : Labels)
    (D : VertexSubdivision (cutFace (tripleCut e))) :
    cutFace (tripleCut e) ∈ D.cells := by
  let E := Equiv.cast (congrArg (fun P : Set (Ambient 3) => VertexSubdivision P)
    (tripleChart_image e).symm) D
  have h := image_triangle_whole_mem (tripleChart e) (tripleChart_injective e) 2 E
  have hc := (cast_cell_iff (tripleChart_image e).symm D _).mp h
  simpa only [tripleChart_image] using hc

/-- If a whole facet is a cell, its cone is an actual fan cone. -/
theorem cutCone_mem_of_whole (Φ : CompleteRootFan) (S : ProperCut 3)
    (hwhole : cutFace S.val ∈
      ((fanCutSubdivisions Φ.val Φ.property.1 Φ.property.2).subdivision S).cells) :
    cutCone S.val ∈ Φ.val.cones := by
  let D := fanCutSubdivisions Φ.val Φ.property.1 Φ.property.2
  have hmem : cutCone S.val ∈ D.toFan.cones :=
    ⟨S,cutFace S.val,hwhole,cutCone_eq_hull_cutFace S.val⟩
  simpa only [D,toFan_fanCutSubdivisions (by decide) Φ.val Φ.property.1 Φ.property.2] using hmem

/-- The exhaustive full-cone presentation includes nonsimplicial square
cones, all four possible omitted-corner triangles, and the eight fixed
triangular facets. It assumes no maximal-cone catalogue. -/
theorem full_cone_presentation (Φ : CompleteRootFan) (C : FullCone Φ.val) :
    (∃ i : Fin 6, ∃ s ∈ maximalKeys (squareChoice Φ i),
      C.val.val = cellCone (labels i) s) ∨
    (∃ e : Labels, C.val.val = cutCone (singletonCut e)) ∨
    (∃ e : Labels, C.val.val = cutCone (tripleCut e)) := by
  let S : ProperCut 3 := ⟨sources C.val.val,
    full_cone_cut_nontrivial (by decide) Φ.val Φ.property.2 C.val.property C.property⟩
  have hcut : C.val.val ≤ cutCone S.val := cone_le_cutCone Φ.val Φ.property.2 C.val.property
  by_cases hs : S.val.card = 2
  · obtain ⟨i,hi⟩ := squareCutIndexEquiv.surjective (⟨S,hs⟩ : SquareCut)
    have hei : squareCut (labels i) = S.val := congrArg (fun T : SquareCut => T.val.val) hi
    obtain ⟨s,hm,he⟩ := full_square_presentation Φ C i (hei.symm ▸ hcut)
    exact Or.inl ⟨i,s,hm,he⟩
  · rcases nonpairCut_forms S.val S.property.1 S.property.2 hs with ⟨e,he⟩ | ⟨e,he⟩
    · apply Or.inr ∘ Or.inl
      refine ⟨e,?_⟩
      have hwhole : cutFace S.val ∈
          ((fanCutSubdivisions Φ.val Φ.property.1 Φ.property.2).subdivision S).cells := by
        let D := (fanCutSubdivisions Φ.val Φ.property.1 Φ.property.2).subdivision S
        let E := Equiv.cast (congrArg (fun T => VertexSubdivision (cutFace T)) he) D
        have hh := singleton_whole_mem e E
        have hc := (cast_cell_iff (congrArg cutFace he) D (cutFace (singletonCut e))).mp hh
        simpa only [he] using hc
      have hmem := cutCone_mem_of_whole Φ S hwhole
      have heq := (FanMaximalCones.full_iff_maximal Φ.val Φ.property.1 C.val.property).mp
        C.property _ hmem hcut
      simpa only [he] using heq
    · apply Or.inr ∘ Or.inr
      refine ⟨e,?_⟩
      have hwhole : cutFace S.val ∈
          ((fanCutSubdivisions Φ.val Φ.property.1 Φ.property.2).subdivision S).cells := by
        let D := (fanCutSubdivisions Φ.val Φ.property.1 Φ.property.2).subdivision S
        let E := Equiv.cast (congrArg (fun T => VertexSubdivision (cutFace T)) he) D
        have hh := triple_whole_mem e E
        have hc := (cast_cell_iff (congrArg cutFace he) D (cutFace (tripleCut e))).mp hh
        simpa only [he] using hc
      have hmem := cutCone_mem_of_whole Φ S hwhole
      have heq := (FanMaximalCones.full_iff_maximal Φ.val Φ.property.1 C.val.property).mp
        C.property _ hmem hcut
      simpa only [he] using heq

#print axioms square_cell_has_key
#print axioms full_square_presentation
#print axioms image_triangle_whole_mem
#print axioms full_cone_presentation

end Unimodular.A3MaximalPresentations
end

end SupportGluing_A3MaximalPresentations

#check "UNIMODULAR_A3_SUPPORT_GLUING_EOF_V2"
