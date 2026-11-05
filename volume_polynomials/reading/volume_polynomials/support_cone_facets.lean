module

public import VolumePolynomials.MixedSupportForm
public import VolumePolynomials.CenteredFacetFamily

@[expose] public section
set_option autoImplicit false

/-!
# Actual facets throughout the open support cone

Every defining height is the attained support value throughout the type cone.
Strict relative-interior facet points persist as a consequence of openness:
lower all the other heights by a small common amount. The fixed-kernel facet
bodies are therefore literal slices in a fixed hyperplane, and increasing a
different height gives actual set inclusion of these lower-dimensional bodies.
-/

noncomputable section
open Set Module Filter
open scoped Pointwise Topology BigOperators

namespace VolumePolynomials.PolyhedralSupport

open PolytopeGeometry OAI.Paper092

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_feasibleBasis_containing (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) (i : ι) :
    ∃ b : BasisIndex l, b ∈ feasibleBases l h₀ ∧ i ∈ b.val := by
  first
  | have hn : (body l h₀).Nonempty := ⟨0, fun i => by
      simpa only [map_zero] using (hp i).le⟩
    obtain ⟨b, hb, hmax⟩ := exists_maximizing_basis l h₀ hc hn (l i)
    obtain ⟨x, hxi, hxj⟩ := hf i
    have hx : x ∈ body l h₀ := by
      intro j
      by_cases hj : j = i
      · subst j
        exact hxi.le
      · exact (hxj j hj).le
    refine ⟨b, hb, ?_⟩
    by_contra hi
    have hstrict := strict_inactive_of_generic l h₀ hg b hb i hi
    have hbound := hmax x hx
    rw [hxi] at hbound
    exact (not_lt_of_ge hbound) hstrict

theorem bodyAtHeight_support (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) {h : ι → ℝ}
    (hh : h ∈ typeCone l h₀ hp hc) (i : ι) :
    SupportGeometry.support (bodyAtHeight l h₀ hp hc h : Set E) (l i) = h i := by
  first
  | obtain ⟨b, hb, hi⟩ := exists_feasibleBasis_containing l h₀ hg hp hc hf i
    have hbh : b ∈ feasibleBases l h := by
      rw [typeRegion_feasibleBases l _ hh]
      exact hb
    apply le_antisymm
    · apply SupportGeometry.support_le (bodyAtHeight l h₀ hp hc h).nonempty
      intro x hx
      rw [coe_bodyAtHeight l h₀ hp hc hh] at hx
      exact hx i
    · have hm : vertexMap l b h ∈ bodyAtHeight l h₀ hp hc h := by
        change vertexMap l b h ∈ (bodyAtHeight l h₀ hp hc h : Set E)
        rw [coe_bodyAtHeight l h₀ hp hc hh]
        exact hbh
      simpa only [vertexMap_active l b h ⟨i, hi⟩] using
        SupportGeometry.le_support (bodyAtHeight l h₀ hp hc h).isCompact (l i) hm

theorem typeCone_strictFacets (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) {h : ι → ℝ}
    (hh : h ∈ typeCone l h₀ hp hc) : StrictFacets l h := by
  first
  | intro i
    let q : ι → ℝ := fun j => if j = i then 0 else 1
    obtain ⟨ε, hε, hh'⟩ := OpenConeExtension.exists_pos_sub_mem
      (typeCone l h₀ hp hc) (typeCone_isOpen l h₀ hp hc) hh q
    obtain ⟨b, hb, hi⟩ := exists_feasibleBasis_containing l h₀ hg hp hc hf i
    have hbh : b ∈ feasibleBases l (h - ε • q) := by
      rw [typeRegion_feasibleBases l _ hh']
      exact hb
    refine ⟨vertexMap l b (h - ε • q), ?_, ?_⟩
    · rw [vertexMap_active l b _ ⟨i, hi⟩]
      simp only [Pi.sub_apply, Pi.smul_apply, q, if_pos rfl, ite_true, smul_zero, sub_zero]
    · intro j hji
      have hj := hbh j
      simp only [Pi.sub_apply, Pi.smul_apply, q, if_neg hji, smul_eq_mul, mul_one] at hj
      linarith

theorem kernelBody_bodyAtHeight_mem_iff (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) {h : ι → ℝ}
    (hh : h ∈ typeCone l h₀ hp hc) (i : ι) (v : E) (hv : l i v = 1)
    (z : LinearMap.ker (l i).toLinearMap) :
    z ∈ kernelBody (bodyAtHeight l h₀ hp hc h) (l i) v hv ↔
      h i • v + (z : E) ∈ body l h := by
  first
  | change z ∈ LinearFrame.kernelPart (l i) v hv ''
      (l i).toExposed (bodyAtHeight l h₀ hp hc h : Set E) ↔ _
    rw [exposed_eq_support_level (bodyAtHeight l h₀ hp hc h).isCompact
      (bodyAtHeight l h₀ hp hc h).nonempty,
      bodyAtHeight_support l h₀ hg hp hc hf hh i,
      coe_bodyAtHeight l h₀ hp hc hh]
    constructor
    · rintro ⟨x, ⟨hx, hxi⟩, rfl⟩
      change h i • v + (x - l i x • v) ∈ body l h
      rw [hxi]
      rw [show h i • v + (x - h i • v) = x by abel]
      exact hx
    · intro hz
      refine ⟨h i • v + (z : E), ⟨hz, ?_⟩, ?_⟩
      · simp only [map_add, map_smul, smul_eq_mul, hv, mul_one,
          show l i (z : E) = 0 from z.property, add_zero]
      · apply Subtype.ext
        change h i • v + (z : E) - l i (h i • v + (z : E)) • v = (z : E)
        simp only [map_add, map_smul, smul_eq_mul, hv, mul_one,
          show l i (z : E) = 0 from z.property, add_zero]
        abel

/-- Raising any constraints while keeping the selected facet height fixed
enlarges its body in the same kernel coordinates. -/
theorem kernelBody_bodyAtHeight_mono (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) {h k : ι → ℝ}
    (hh : h ∈ typeCone l h₀ hp hc) (hk : k ∈ typeCone l h₀ hp hc)
    (hmono : ∀ j, h j ≤ k j) (i : ι) (hi : h i = k i)
    (v : E) (hv : l i v = 1) :
    kernelBody (bodyAtHeight l h₀ hp hc h) (l i) v hv ≤
      kernelBody (bodyAtHeight l h₀ hp hc k) (l i) v hv := by
  first
  | intro z hz
    rw [kernelBody_bodyAtHeight_mem_iff l h₀ hg hp hc hf hh i v hv] at hz
    rw [kernelBody_bodyAtHeight_mem_iff l h₀ hg hp hc hf hk i v hv, ← hi]
    exact fun j => (hz j).trans (hmono j)

theorem kernelBody_add (K L : ConvexBody E) (l : E →L[ℝ] ℝ)
    (v : E) (hv : l v = 1) :
    kernelBody (K + L) l v hv = kernelBody K l v hv + kernelBody L l v hv := by
  first
  | apply ConvexBody.ext
    change LinearFrame.kernelPart l v hv '' l.toExposed ((K : Set E) + (L : Set E)) = _
    rw [PolytopeFaces.exposed_add, Set.image_add (LinearFrame.kernelPart l v hv)]
    rfl

theorem kernelBody_smul (K : ConvexBody E) (l : E →L[ℝ] ℝ)
    (v : E) (hv : l v = 1) {r : ℝ} (hr : 0 < r) :
    kernelBody (r • K) l v hv = r • kernelBody K l v hv := by
  first
  | apply ConvexBody.ext
    change LinearFrame.kernelPart l v hv '' l.toExposed (r • (K : Set E)) = _
    rw [PolytopeFaces.exposed_smul l _ hr,
      Set.image_smul_comm (LinearFrame.kernelPart l v hv) r _
        (fun x => (LinearFrame.kernelPart l v hv).map_smul r x)]
    rfl

/-- The selected facet has nonempty interior in its own kernel, in every
ambient dimension. This is proved by the actual strict slice inequalities. -/
theorem kernelBody_bodyAtHeight_interior_nonempty
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) {h : ι → ℝ}
    (hh : h ∈ typeCone l h₀ hp hc) (i : ι) (v : E) (hv : l i v = 1) :
    (interior (kernelBody (bodyAtHeight l h₀ hp hc h) (l i) v hv :
      Set (LinearMap.ker (l i).toLinearMap))).Nonempty := by
  first
  | obtain ⟨x, hxi, hxj⟩ := typeCone_strictFacets l h₀ hg hp hc hf hh i
    let U : Set (LinearMap.ker (l i).toLinearMap) :=
      {z | ∀ j, j ≠ i → l j (h i • v + (z : E)) < h j}
    have hopen : IsOpen U := by
      simp only [U, Set.setOf_forall]
      exact isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun _ =>
        isOpen_lt ((l j).continuous.comp (continuous_const.add continuous_subtype_val))
          continuous_const
    have hsub : U ⊆ (kernelBody (bodyAtHeight l h₀ hp hc h) (l i) v hv :
        Set (LinearMap.ker (l i).toLinearMap)) := by
      intro z hz
      change z ∈ kernelBody (bodyAtHeight l h₀ hp hc h) (l i) v hv
      rw [kernelBody_bodyAtHeight_mem_iff l h₀ hg hp hc hf hh i v hv]
      intro j
      by_cases hji : j = i
      · subst j
        simp only [map_add, map_smul, smul_eq_mul, hv, mul_one,
          show l i (z : E) = 0 from z.property, add_zero, le_refl]
      · exact (hz j hji).le
    have hpoint : h i • v + ((LinearFrame.kernelPart (l i) v hv x :
        LinearMap.ker (l i).toLinearMap) : E) = x := by
      rw [LinearFrame.kernelPart_coe, hxi]
      abel
    refine ⟨LinearFrame.kernelPart (l i) v hv x, ?_⟩
    apply (hopen.subset_interior_iff.mpr hsub)
    intro j hji
    rw [hpoint]
    exact hxj j hji

theorem typeCone_sum_mem {κ : Type*} [Fintype κ] [Nonempty κ]
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (h : κ → ι → ℝ) (hh : ∀ j, h j ∈ typeCone l h₀ hp hc) :
    (∑ j, h j) ∈ typeCone l h₀ hp hc :=
  Finset.sum_induction_nonempty h (fun x => x ∈ typeCone l h₀ hp hc)
    (fun _ _ ha hb => (typeCone l h₀ hp hc).add_mem ha hb)
    Finset.univ_nonempty (fun j _ => hh j)

theorem bodyAtHeight_sum {κ : Type*} [Fintype κ] [Nonempty κ]
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (h : κ → ι → ℝ) (hh : ∀ j, h j ∈ typeCone l h₀ hp hc) :
    bodyAtHeight l h₀ hp hc (∑ j, h j) = ∑ j, bodyAtHeight l h₀ hp hc (h j) := by
  first
  | have he := Finset.sum_induction_nonempty
      (fun j => (h j, bodyAtHeight l h₀ hp hc (h j)))
      (fun p : (ι → ℝ) × ConvexBody E =>
        p.1 ∈ typeCone l h₀ hp hc ∧ bodyAtHeight l h₀ hp hc p.1 = p.2)
      (fun a b ha hb => ⟨(typeCone l h₀ hp hc).add_mem ha.1 hb.1,
        (bodyAtHeight_add l h₀ hp hc ha.1 hb.1).trans (congrArg₂ (· + ·) ha.2 hb.2)⟩)
      (Finset.univ_nonempty : (Finset.univ : Finset κ).Nonempty)
      (fun j _ => ⟨hh j, rfl⟩)
    rw [← prod_mk_sum] at he
    exact he.2

theorem bodyAtHeight_weighted_sum {κ : Type*} [Fintype κ] [Nonempty κ]
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (h : κ → ι → ℝ) (hh : ∀ j, h j ∈ typeCone l h₀ hp hc)
    (t : κ → ℝ) (ht : ∀ j, 0 < t j) :
    bodyAtHeight l h₀ hp hc (∑ j, t j • h j) =
      ∑ j, t j • bodyAtHeight l h₀ hp hc (h j) := by
  first
  | rw [bodyAtHeight_sum l h₀ hp hc _
      (fun j => (typeCone l h₀ hp hc).smul_mem (ht j) (hh j))]
    exact Finset.sum_congr rfl (fun j _ => bodyAtHeight_smul l h₀ hp hc (hh j) (ht j))

/-- The same, originally constructed normals form a genuine `FixedFacets`
family for every finite nonempty tuple from the type cone. This exposes the
already proved first-variation identity without choosing a new facet system. -/
def fixedFacetsOfCone {m : ℕ} {κ : Type*} [Fintype κ] [Nonempty κ]
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) (hn : ∀ i, l i ≠ 0)
    (hray : ∀ i j {c : ℝ}, 0 < c → l i = c • l j → i = j)
    (h : κ → Fin m → ℝ) (hh : ∀ j, h j ∈ typeCone l h₀ hp hc) :
    FixedFacets (fun j => (bodyAtHeight l h₀ hp hc (h j) : Set E)) where
  count := m
  normal := l
  normal_ne_zero := hn
  positive_ray_injective := hray
  body_eq t ht := by
    first
    | have hsupport (j : κ) (i : Fin m) :
          SupportGeometry.support (bodyAtHeight l h₀ hp hc (h j) : Set E) (l i) = h j i :=
        bodyAtHeight_support l h₀ hg hp hc hf (hh j) i
      simp only [hsupport]
      have hs := typeCone_sum_mem l h₀ hp hc (fun j => t j • h j)
        (fun j => (typeCone l h₀ hp hc).smul_mem (ht j) (hh j))
      have he := congrArg (fun K : ConvexBody E => (K : Set E))
        (bodyAtHeight_weighted_sum l h₀ hp hc h hh t ht)
      rw [coe_bodyAtHeight l h₀ hp hc hs, coe_sum_body] at he
      simpa only [ConvexBody.coe_smul, body, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul] using he.symm
  strict_face_point := by
    first
    | have hsupport (j : κ) (i : Fin m) :
          SupportGeometry.support (bodyAtHeight l h₀ hp hc (h j) : Set E) (l i) = h j i :=
        bodyAtHeight_support l h₀ hg hp hc hf (hh j) i
      have hs := typeCone_sum_mem l h₀ hp hc h hh
      have hf' := typeCone_strictFacets l h₀ hg hp hc hf hs
      simpa only [hsupport, StrictFacets, Finset.sum_apply] using hf'

end VolumePolynomials.PolyhedralSupport
