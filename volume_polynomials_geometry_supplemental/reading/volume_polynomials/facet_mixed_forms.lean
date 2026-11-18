module

public import VolumePolynomials.MixedSupportConnectivity

@[expose] public section
set_option autoImplicit false

/-! # Actual lower-dimensional mixed forms in fixed facet coordinates

Each kernel facet map is Minkowski additive on the genuine upper support
cone. Its actual mixed volumes therefore have finite multilinear extensions
on the same real height space. Their positivity and symmetry are proved
from the genuine kernel bodies; no lower-dimensional inequality is assumed
in these constructions.
-/

noncomputable section
open Set MeasureTheory Module LinearMap
open scoped Pointwise BigOperators

namespace VolumePolynomials.PolyhedralSupport

open PolytopeGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  {m : ℕ}

def facetHeightValue
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (i : Fin m) (v : E) (hv : l i v = 1) {n : ℕ}
    (H : Fin n → Fin m → ℝ) : ℝ :=
  mixedVolume (kernelMeasure (l i))
    (fun j => kernelBody (bodyAtHeight l h₀ hp hc (H j)) (l i) v hv)

theorem facetBody_tuple_update
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (i : Fin m) (v : E) (hv : l i v = 1) {n : ℕ}
    (H : Fin n → Fin m → ℝ) (j : Fin n) (a : Fin m → ℝ) :
    (fun k => kernelBody (bodyAtHeight l h₀ hp hc (Function.update H j a k)) (l i) v hv) =
      Function.update (fun k => kernelBody (bodyAtHeight l h₀ hp hc (H k)) (l i) v hv) j
        (kernelBody (bodyAtHeight l h₀ hp hc a) (l i) v hv) := by
  first
  | funext k
    by_cases hkj : k = j <;> simp [hkj]

theorem facetHeightValue_isMultilinearOnCone
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (i : Fin m) (v : E) (hv : l i v = 1) (n : ℕ) :
    OpenConeModuleExtension.IsMultilinearOnCone (typeCone l h₀ hp hc)
      (facetHeightValue l h₀ hp hc i v hv (n := n)) where
  add H hH j a ha b hb := by
    first
    | simp only [facetHeightValue, facetBody_tuple_update]
      rw [bodyAtHeight_add l h₀ hp hc ha hb, kernelBody_add, mixedVolume_add]
  smul H hH j r hr a ha := by
    first
    | simp only [facetHeightValue, facetBody_tuple_update]
      rw [bodyAtHeight_smul l h₀ hp hc ha hr, kernelBody_smul _ _ _ _ hr,
        mixedVolume_smul (kernelMeasure (l i)) _ _ _ hr.le]
      rfl

def facetMultilinearVolume
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (i : Fin m) (v : E) (hv : l i v = 1) (n : ℕ) :
    MultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℝ :=
  OpenConeModuleExtension.multilinearExtension (typeCone l h₀ hp hc)
    (typeCone_isOpen l h₀ hp hc) (typeCone_nonempty l h₀ hg hp hc)
    (facetHeightValue l h₀ hp hc i v hv)
    (facetHeightValue_isMultilinearOnCone l h₀ hp hc i v hv n)

theorem facetMultilinearVolume_eq
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (i : Fin m) (v : E) (hv : l i v = 1) {n : ℕ}
    (H : Fin n → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc) :
    facetMultilinearVolume l h₀ hg hp hc i v hv n H =
      mixedVolume (kernelMeasure (l i))
        (fun j => kernelBody (bodyAtHeight l h₀ hp hc (H j)) (l i) v hv) :=
  OpenConeModuleExtension.multilinearExtension_eq _ _ _ _ _ H hH

theorem facetMultilinearVolume_nonnegative
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (i : Fin m) (v : E) (hv : l i v = 1) {n : ℕ}
    (H : Fin n → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc) :
    0 ≤ facetMultilinearVolume l h₀ hg hp hc i v hv n H := by
  first
  | rw [facetMultilinearVolume_eq l h₀ hg hp hc i v hv H hH]
    exact mixedVolume_nonnegative _ _

theorem facetMultilinearVolume_positive
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀)
    (i : Fin m) (v : E) (hv : l i v = 1) {n : ℕ}
    (hdim : finrank ℝ E = n + 1)
    (H : Fin n → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc) :
    0 < facetMultilinearVolume l h₀ hg hp hc i v hv n H := by
  first
  | have href : h₀ ∈ typeCone l h₀ hp hc := mem_typeRegion_self l h₀ hg hp
    have hkdim : finrank ℝ (LinearMap.ker (l i).toLinearMap) = n := by
      first
      | have he := LinearFrame.finrank_kernel_add_one (l i) v hv
        rw [hdim] at he
        omega
    apply OpenConeModuleExtension.positive_of_nonnegative_on_cone
      (typeCone l h₀ hp hc) (typeCone_isOpen l h₀ hp hc)
      (facetMultilinearVolume l h₀ hg hp hc i v hv n)
      (facetMultilinearVolume_nonnegative l h₀ hg hp hc i v hv) href _ H hH
    rw [facetMultilinearVolume_eq l h₀ hg hp hc i v hv _ (fun _ => href),
      mixedVolume_diagonal (kernelMeasure (l i)) hkdim]
    let Q := kernelBody (bodyAtHeight l h₀ hp hc h₀) (l i) v hv
    have hQint : (interior (Q : Set (LinearMap.ker (l i).toLinearMap))).Nonempty :=
      kernelBody_bodyAtHeight_interior_nonempty l h₀ hg hp hc hf href i v hv
    exact ENNReal.toReal_pos
      (Measure.measure_pos_of_nonempty_interior (kernelMeasure (l i)) hQint).ne'
      (Q.isCompact.measure_ne_top (μ := kernelMeasure (l i)))

theorem facetMultilinearVolume_reindex
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (i : Fin m) (v : E) (hv : l i v = 1) {n : ℕ}
    (H : Fin n → Fin m → ℝ) (e : Equiv.Perm (Fin n)) :
    facetMultilinearVolume l h₀ hg hp hc i v hv n (fun j => H (e j)) =
      facetMultilinearVolume l h₀ hg hp hc i v hv n H := by
  first
  | let F := facetMultilinearVolume l h₀ hg hp hc i v hv n
    have he : F.domDomCongr e = F := by
      first
      | apply OpenConeModuleExtension.multilinearMap_ext_of_eq_on_cone
          (typeCone l h₀ hp hc) (typeCone_isOpen l h₀ hp hc)
          (typeCone_nonempty l h₀ hg hp hc)
        intro x hx
        change facetMultilinearVolume l h₀ hg hp hc i v hv n (fun j => x (e j)) = _
        rw [facetMultilinearVolume_eq l h₀ hg hp hc i v hv _ (fun j => hx (e j)),
          facetMultilinearVolume_eq l h₀ hg hp hc i v hv _ hx]
        exact mixedVolume_reindex (kernelMeasure (l i))
          (fun j : Fin n => kernelBody (bodyAtHeight l h₀ hp hc (x j)) (l i) v hv) e
    exact congrArg (fun G : MultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℝ => G H) he

def facetMixedForm
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (i : Fin m) (v : E) (hv : l i v = 1) {n : ℕ}
    (H : Fin n → Fin m → ℝ) : LinearMap.BilinForm ℝ (Fin m → ℝ) :=
  firstTwoForm (facetMultilinearVolume l h₀ hg hp hc i v hv (n + 2)) H

theorem facetMixedForm_eq
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (i : Fin m) (v : E) (hv : l i v = 1) {n : ℕ}
    (H : Fin n → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc)
    {x y : Fin m → ℝ} (hx : x ∈ typeCone l h₀ hp hc) (hy : y ∈ typeCone l h₀ hp hc) :
    facetMixedForm l h₀ hg hp hc i v hv H x y =
      mixedVolume (kernelMeasure (l i))
        (Fin.cons (kernelBody (bodyAtHeight l h₀ hp hc x) (l i) v hv)
          (Fin.cons (kernelBody (bodyAtHeight l h₀ hp hc y) (l i) v hv)
            (fun j => kernelBody (bodyAtHeight l h₀ hp hc (H j)) (l i) v hv))) := by
  first
  | change facetMultilinearVolume l h₀ hg hp hc i v hv _ (Fin.cons x (Fin.cons y H)) = _
    rw [facetMultilinearVolume_eq l h₀ hg hp hc i v hv _
      (fun j => Fin.cases hx (fun k => Fin.cases hy hH k) j)]
    apply congrArg (mixedVolume (kernelMeasure (l i)))
    funext j
    exact Fin.cases rfl (fun k => Fin.cases rfl (fun _ => rfl) k) j

theorem facetMixedForm_symmetric
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (i : Fin m) (v : E) (hv : l i v = 1) {n : ℕ}
    (H : Fin n → Fin m → ℝ) (x y : Fin m → ℝ) :
    facetMixedForm l h₀ hg hp hc i v hv H x y =
      facetMixedForm l h₀ hg hp hc i v hv H y x := by
  first
  | have he := facetMultilinearVolume_reindex l h₀ hg hp hc i v hv
      (Fin.cons x (Fin.cons y H)) (Equiv.swap (0 : Fin (n + 2)) 1)
    change facetMultilinearVolume l h₀ hg hp hc i v hv _
      ((Matrix.vecCons x (Matrix.vecCons y H)) ∘ Equiv.swap 0 1) = _ at he
    rw [Matrix.cons_cons_comp_swap_zero_one] at he
    exact he.symm

theorem facetMixedForm_positive
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀)
    (i : Fin m) (v : E) (hv : l i v = 1) {n : ℕ}
    (hdim : finrank ℝ E = n + 3)
    (H : Fin n → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc)
    {x y : Fin m → ℝ} (hx : x ∈ typeCone l h₀ hp hc) (hy : y ∈ typeCone l h₀ hp hc) :
    0 < facetMixedForm l h₀ hg hp hc i v hv H x y :=
  facetMultilinearVolume_positive l h₀ hg hp hc hf i v hv hdim
    (Fin.cons x (Fin.cons y H)) (fun j => Fin.cases hx (fun k => Fin.cases hy hH k) j)

end VolumePolynomials.PolyhedralSupport
