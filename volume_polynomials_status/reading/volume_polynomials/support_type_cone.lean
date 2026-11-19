module

public import VolumePolynomials.CommonSimplePolytopes
public import VolumePolynomials.OpenConeExtension

@[expose] public section
set_option autoImplicit false

/-!
# The full open cone of a simple support type

The cone remembers exactly the feasible active bases. Its definition imposes
strict inequalities only at feasible vertices, so it does not subdivide the
type by irrelevant intersections of exterior hyperplanes. It contains all
positive common-refinement approximants and is closed under addition and
positive scaling.
-/

noncomputable section
open Set Module
open scoped Topology Pointwise BigOperators

namespace VolumePolynomials.PolyhedralSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def typeRegion (l : ι → E →L[ℝ] ℝ) (F : Set (BasisIndex l)) : Set (ι → ℝ) :=
  {h | (∀ i, 0 < h i) ∧
    (∀ b ∈ F, ∀ i ∉ b.val, l i (vertexMap l b h) < h i) ∧
    feasibleBases l h ⊆ F}

theorem typeRegion_feasibleBases (l : ι → E →L[ℝ] ℝ) (F : Set (BasisIndex l))
    {h : ι → ℝ} (hh : h ∈ typeRegion l F) : feasibleBases l h = F := by
  first
  | apply Subset.antisymm hh.2.2
    intro b hb i
    by_cases hi : i ∈ b.val
    · exact (vertexMap_active l b h ⟨i, hi⟩).le
    · exact (hh.2.1 b hb i hi).le

theorem typeRegion_strict (l : ι → E →L[ℝ] ℝ) (F : Set (BasisIndex l))
    {h : ι → ℝ} (hh : h ∈ typeRegion l F) :
    ∀ b ∈ feasibleBases l h, ∀ i ∉ b.val, l i (vertexMap l b h) < h i := by
  first
  | rw [typeRegion_feasibleBases l F hh]
    exact hh.2.1

theorem isOpen_typeRegion (l : ι → E →L[ℝ] ℝ) (F : Set (BasisIndex l)) :
    IsOpen (typeRegion l F) := by
  first
  | classical
    have he : typeRegion l F = {h | ∀ i, 0 < h i} ∩
        (⋂ b : BasisIndex l, if b ∈ F then
          ⋂ i : ι, if i ∈ b.val then Set.univ
          else {h | l i (vertexMap l b h) < h i}
        else {h | b ∈ feasibleBases l h}ᶜ) := by
      ext h
      simp only [typeRegion, mem_ofPred_eq, mem_inter_iff, mem_iInter, Set.subset_def]
      constructor
      · rintro ⟨hp, hs, hf⟩
        refine ⟨hp, fun b => ?_⟩
        by_cases hb : b ∈ F
        · simp only [hb, ite_true, mem_iInter]
          intro i
          by_cases hi : i ∈ b.val
          · simp only [hi, ite_true, mem_univ]
          · simpa only [hi, ite_false, mem_ofPred_eq] using hs b hb i hi
        · simpa only [hb, ite_false, mem_compl_iff, mem_ofPred_eq] using mt (hf b) hb
      · rintro ⟨hp, hs⟩
        refine ⟨hp, ?_, ?_⟩
        · intro b hb i hi
          have hb' := hs b
          simp only [hb, ite_true, mem_iInter] at hb'
          simpa only [hi, ite_false, mem_ofPred_eq] using hb' i
        · intro b hb
          by_contra hnot
          have hn := hs b
          simpa only [hnot, ite_false, mem_compl_iff, mem_ofPred_eq, hb, not_true_eq_false] using hn
    rw [he]
    apply isOpen_positiveHeights.inter
    apply isOpen_iInter_of_finite
    intro b
    split_ifs
    · apply isOpen_iInter_of_finite
      intro i
      split_ifs
      · exact isOpen_univ
      · exact isOpen_lt ((l i).continuous.comp (vertexMap l b).continuous) (continuous_apply i)
    · exact (isClosed_feasibleBasis l b).isOpen_compl

theorem mem_typeRegion_self (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hg : Generic l h) (hp : ∀ i, 0 < h i) :
    h ∈ typeRegion l (feasibleBases l h) :=
  ⟨hp, strict_inactive_of_generic l h hg, Set.Subset.rfl⟩

theorem feasibleBases_smul (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    {r : ℝ} (hr : 0 < r) : feasibleBases l (r • h) = feasibleBases l h := by
  first
  | ext b
    change (∀ i, l i (vertexMap l b (r • h)) ≤ (r • h) i) ↔
      (∀ i, l i (vertexMap l b h) ≤ h i)
    simpa only [map_smul, Pi.smul_apply, smul_eq_mul, mul_le_mul_iff_of_pos_left hr]

theorem typeRegion_smul (l : ι → E →L[ℝ] ℝ) (F : Set (BasisIndex l))
    {h : ι → ℝ} (hh : h ∈ typeRegion l F) {r : ℝ} (hr : 0 < r) :
    r • h ∈ typeRegion l F := by
  first
  | refine ⟨fun i => mul_pos hr (hh.1 i), ?_, ?_⟩
    · intro b hb i hi
      simpa only [map_smul, Pi.smul_apply, smul_eq_mul] using
        mul_lt_mul_of_pos_left (hh.2.1 b hb i hi) hr
    · rw [feasibleBases_smul l h hr]
      exact hh.2.2

theorem typeRegion_add (l : ι → E →L[ℝ] ℝ) (F : Set (BasisIndex l))
    (h₀ : ι → ℝ) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {h k : ι → ℝ} (hh : h ∈ typeRegion l F) (hk : k ∈ typeRegion l F) :
    h + k ∈ typeRegion l F := by
  first
  | let Q := toBody l h₀ hp hc h hh.1
    let R := toBody l h₀ hp hc k hk.1
    have hvertex : ∀ b ∈ feasibleBases l k, vertexMap l b h ∈ Q := by
      intro b hb
      have hbh : b ∈ feasibleBases l h := by
        rw [typeRegion_feasibleBases l F hh, ← typeRegion_feasibleBases l F hk]
        exact hb
      exact hbh
    have hsimple := typeRegion_strict l F hk
    refine ⟨fun i => add_pos (hh.1 i) (hk.1 i), ?_, ?_⟩
    · intro b hb i hi
      have hbk : b ∈ feasibleBases l k := by rw [typeRegion_feasibleBases l F hk]; exact hb
      simpa only [one_smul] using refinement_vertex_strict_inactive l k hsimple Q h
        (fun x hx i => hx i) hvertex zero_lt_one b hbk i hi
    · have he := feasibleBases_minkowski_refinement l k hsimple R Q rfl h
        (fun x hx i => hx i) hvertex zero_lt_one
      simpa only [one_smul, typeRegion_feasibleBases l F hk] using he.subset

theorem body_add_of_typeRegion (l : ι → E →L[ℝ] ℝ) (F : Set (BasisIndex l))
    (h₀ : ι → ℝ) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {h k : ι → ℝ} (hh : h ∈ typeRegion l F) (hk : k ∈ typeRegion l F) :
    body l (h + k) = body l h + body l k := by
  first
  | let Q := toBody l h₀ hp hc h hh.1
    let R := toBody l h₀ hp hc k hk.1
    have hvertex : ∀ b ∈ feasibleBases l k, vertexMap l b h ∈ Q := by
      intro b hb
      rw [typeRegion_feasibleBases l F hk] at hb
      have hbh : b ∈ feasibleBases l h := by rw [typeRegion_feasibleBases l F hh]; exact hb
      exact hbh
    have he := minkowski_eq_halfspaces_of_refinement l k (typeRegion_strict l F hk)
      R Q rfl h (fun x hx i => hx i) hvertex zero_lt_one
    have hQ : (Q : Set E) = body l h := rfl
    have hR : (R : Set E) = body l k := rfl
    simpa only [one_smul, ConvexBody.coe_add, hQ, hR] using he.symm

def typeCone (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀)) : ConvexCone ℝ (ι → ℝ) where
  carrier := typeRegion l (feasibleBases l h₀)
  smul_mem' := by
    intro r hr h hh
    exact typeRegion_smul l _ hh hr
  add_mem' := by
    intro h hh k hk
    exact typeRegion_add l _ h₀ hp hc hh hk

theorem typeCone_isOpen (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀)) :
    IsOpen (typeCone l h₀ hp hc : Set (ι → ℝ)) := isOpen_typeRegion l _

theorem typeCone_nonempty (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀)) :
    (typeCone l h₀ hp hc : Set (ι → ℝ)).Nonempty :=
  ⟨h₀, mem_typeRegion_self l h₀ hg hp⟩

def coneBody (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (h : typeCone l h₀ hp hc) : ConvexBody E := toBody l h₀ hp hc h.val h.property.1

theorem coneBody_add (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (h k : typeCone l h₀ hp hc) :
    coneBody l h₀ hp hc ⟨h.val + k.val, (typeCone l h₀ hp hc).add_mem h.property k.property⟩ =
      coneBody l h₀ hp hc h + coneBody l h₀ hp hc k := by
  first
  | apply ConvexBody.ext
    exact body_add_of_typeRegion l _ h₀ hp hc h.property k.property

theorem coneBody_smul (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (h : typeCone l h₀ hp hc) {r : ℝ} (hr : 0 < r) :
    coneBody l h₀ hp hc ⟨r • h.val, (typeCone l h₀ hp hc).smul_mem hr h.property⟩ =
      r • coneBody l h₀ hp hc h := by
  first
  | apply ConvexBody.ext
    exact body_smul l h.val hr

namespace CommonRefinement

variable {κ : Type*} [Fintype κ] {K : κ → ConvexBody E} (D : CommonRefinement K)

def supportCone : ConvexCone ℝ (Fin D.facets.count → ℝ) :=
  typeCone D.facets.normal D.height D.height_pos (D.reference_eq ▸ D.reference.isCompact)

theorem supportCone_isOpen : IsOpen (D.supportCone : Set (Fin D.facets.count → ℝ)) :=
  typeCone_isOpen _ _ _ _

theorem supportCone_nonempty : (D.supportCone : Set (Fin D.facets.count → ℝ)).Nonempty :=
  typeCone_nonempty _ _ D.generic _ _

theorem approximantHeight_mem_supportCone (h0 : ∀ k, (0 : E) ∈ K k)
    {r : ℝ} (hr : 0 < r) (k : κ) : D.approximantHeight r k ∈ D.supportCone :=
  ⟨D.approximantHeight_pos h0 hr k, D.approximant_strict_inactive hr k,
    (D.approximant_feasibleBases hr k).subset⟩

end CommonRefinement
end VolumePolynomials.PolyhedralSupport
