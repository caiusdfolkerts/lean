module

public import VolumePolynomials.FacetMixedForms

@[expose] public section
set_option autoImplicit false

/-! # The exact facet identities for the mixed-support Bochner argument

The fixed background begins with one genuine support vector `h`. Symmetry
of actual mixed volume moves that argument into the support slot of the
first-variation formula. Extending the resulting identity from the open
support cone gives a bilinear identity on every real height direction.
The coordinate form of the same formula identifies each actual matrix row.
-/

noncomputable section
open Set MeasureTheory Module Matrix LinearMap
open scoped Pointwise BigOperators

namespace VolumePolynomials.PolyhedralSupport

open PolytopeGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  {m n : ℕ}

theorem facetMixedValue_cons_eq
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (H : Fin n → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc)
    (i : Fin m) (v : E) (hv : l i v = 1)
    {x h : Fin m → ℝ} (hx : x ∈ typeCone l h₀ hp hc) (hh : h ∈ typeCone l h₀ hp hc) :
    facetMixedValue l h₀ hp hc (Fin.cons h H) x i v hv =
      facetMixedForm l h₀ hg hp hc i v hv H x h := by
  first
  | rw [facetMixedForm_eq l h₀ hg hp hc i v hv H hH hx hh]
    unfold facetMixedValue
    congr 1
    funext j
    exact Fin.cases rfl (fun k => Fin.cases rfl (fun _ => rfl) k) j

theorem mixedSupportForm_row_facetMixedForm
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) (hn : ∀ i, l i ≠ 0)
    (hray : ∀ i j {c : ℝ}, 0 < c → l i = c • l j → i = j)
    (H : Fin n → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc)
    {h : Fin m → ℝ} (hh : h ∈ typeCone l h₀ hp hc)
    (v : Fin m → E) (hv : ∀ i, l i (v i) = 1) (i : Fin m) (x : Fin m → ℝ) :
    ((n + 3 : ℕ) : ℝ) * mixedSupportForm volume l h₀ hg hp hc
        (coneTuple l h₀ hp hc (Fin.cons h H)) (Pi.single i 1) x =
      facetFrameFactor (l i) (v i) (hv i) * facetMixedForm l h₀ hg hp hc i (v i) (hv i) H x h := by
  first
  | have hon (y : Fin m → ℝ) (hy : y ∈ typeCone l h₀ hp hc) :
        ((n + 3 : ℕ) : ℝ) * mixedSupportForm volume l h₀ hg hp hc
          (coneTuple l h₀ hp hc (Fin.cons h H)) (Pi.single i 1) y =
        facetFrameFactor (l i) (v i) (hv i) * facetMixedForm l h₀ hg hp hc i (v i) (hv i) H y h := by
      first
      | have he := mixedSupportForm_coordinate_facet l h₀ hg hp hc hf hn hray
          (Fin.cons h H) (fun j => Fin.cases hh hH j) v hv i hy
        rw [facetMixedValue_cons_eq l h₀ hg hp hc H hH i (v i) (hv i) hy hh] at he
        exact he
    obtain ⟨a, ha, b, hb, rfl⟩ := OpenConeExtension.exists_difference
      (typeCone l h₀ hp hc) (typeCone_isOpen l h₀ hp hc)
      (typeCone_nonempty l h₀ hg hp hc) x
    rw [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.sub_left, mul_sub, mul_sub, hon a ha, hon b hb]

theorem mixedSupportMatrix_row_facetMixedForm
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) (hn : ∀ i, l i ≠ 0)
    (hray : ∀ i j {c : ℝ}, 0 < c → l i = c • l j → i = j)
    (H : Fin n → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc)
    {h : Fin m → ℝ} (hh : h ∈ typeCone l h₀ hp hc)
    (v : Fin m → E) (hv : ∀ i, l i (v i) = 1) (i : Fin m) (x : Fin m → ℝ) :
    ((n + 3 : ℕ) : ℝ) *
        (mixedSupportMatrix volume l h₀ hg hp hc (coneTuple l h₀ hp hc (Fin.cons h H)) *ᵥ x) i =
      facetFrameFactor (l i) (v i) (hv i) * facetMixedForm l h₀ hg hp hc i (v i) (hv i) H x h := by
  first
  | simpa only [mixedSupportForm_eq_dotProduct, single_one_dotProduct] using
      mixedSupportForm_row_facetMixedForm l h₀ hg hp hc hf hn hray H hH hh v hv i x

theorem mixedSupportForm_facet_bilinear_identity
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) (hn : ∀ i, l i ≠ 0)
    (hray : ∀ i j {c : ℝ}, 0 < c → l i = c • l j → i = j)
    (H : Fin n → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc)
    {h : Fin m → ℝ} (hh : h ∈ typeCone l h₀ hp hc)
    (v : Fin m → E) (hv : ∀ i, l i (v i) = 1) (x y : Fin m → ℝ) :
    ((n + 3 : ℕ) : ℝ) * mixedSupportForm volume l h₀ hg hp hc
        (coneTuple l h₀ hp hc (Fin.cons h H)) x y =
      ∑ i, facetFrameFactor (l i) (v i) (hv i) * h i *
        facetMixedForm l h₀ hg hp hc i (v i) (hv i) H x y := by
  first
  | let B := mixedSupportForm volume l h₀ hg hp hc (coneTuple l h₀ hp hc (Fin.cons h H))
    let L : Fin m → LinearMap.BilinForm ℝ (Fin m → ℝ) :=
      fun i => facetMixedForm l h₀ hg hp hc i (v i) (hv i) H
    let α : Fin m → ℝ := fun i => facetFrameFactor (l i) (v i) (hv i)
    have heq : (((n + 3 : ℕ) : ℝ) • B) = ∑ i, (α i * h i) • L i := by
      first
      | apply bilinear_ext_of_eq_on_cone (typeCone l h₀ hp hc)
          (typeCone_isOpen l h₀ hp hc) (typeCone_nonempty l h₀ hg hp hc)
        intro a ha b hb
        change ((n + 3 : ℕ) : ℝ) * B a b = _
        have hF : MultilinearDiagonal.PermutationSymmetric
            (supportMultilinearVolume volume l h₀ hg hp hc (n + 3)) :=
          supportMultilinearVolume_reindex volume l h₀ hg hp hc
        have hrotate := hF.rotate_first_three a b h H
        have hfirst := supportMultilinearVolume_firstTwoForm volume l h₀ hg hp hc
          (Fin.cons h H) (fun j => Fin.cases hh hH j)
        have hsecond := supportMultilinearVolume_firstTwoForm volume l h₀ hg hp hc
          (Fin.cons b H) (fun j => Fin.cases hb hH j)
        have hswap : B a b = mixedSupportForm volume l h₀ hg hp hc
            (coneTuple l h₀ hp hc (Fin.cons b H)) h a := by
          dsimp only [B]
          unfold coneTuple
          rw [← hfirst, ← hsecond]
          exact hrotate
        rw [hswap, mixedSupportForm_facet_on_cone l h₀ hg hp hc hf hn hray
          (Fin.cons b H) (fun j => Fin.cases hb hH j) v hv hh ha]
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [facetMixedValue_cons_eq l h₀ hg hp hc H hH i (v i) (hv i) ha hb]
    have he := congrArg (fun G : LinearMap.BilinForm ℝ (Fin m → ℝ) => G x y) heq
    simpa only [B, L, α, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using he

end VolumePolynomials.PolyhedralSupport
