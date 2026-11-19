module

public import VolumePolynomials.SupportConeFacets
public import VolumePolynomials.MixedVolumeMonotonicity

@[expose] public section
set_option autoImplicit false

/-!
# Facet coordinates and the sign of the genuine mixed-support operator

The first-variation identity identifies every row of the symmetric form with
an actual lower-dimensional mixed volume. Increasing a distinct support
height enlarges the corresponding fixed-hyperplane slice, so monotonicity of
actual mixed volume proves every off-diagonal matrix entry nonnegative.
This avoids assuming a ridge formula or an abstract operator representation.
-/

noncomputable section
open Set MeasureTheory Module Matrix LinearMap
open scoped Pointwise BigOperators Topology

namespace VolumePolynomials.PolyhedralSupport

open PolytopeGeometry OAI.Paper092

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  {m d : ℕ}

private theorem map_finCons {α β : Type*} {n : ℕ}
    (f : α → β) (a : α) (s : Fin n → α) :
    (fun j : Fin (n + 1) => f ((Fin.cons a s : Fin (n + 1) → α) j)) =
      (Fin.cons (f a) (fun j : Fin n => f (s j)) : Fin (n + 1) → β) := by
  funext j
  exact Fin.cases rfl (fun _ => rfl) j

private theorem kernelBody_finCons (a : ConvexBody E) (s : Fin d → ConvexBody E)
    (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1) :
    (fun j : Fin (d + 1) =>
      kernelBody ((Fin.cons a s : Fin (d + 1) → ConvexBody E) j) l v hv) =
      (Fin.cons (kernelBody a l v hv) (fun j : Fin d => kernelBody (s j) l v hv) :
        Fin (d + 1) → ConvexBody (LinearMap.ker l.toLinearMap)) := by
  funext j
  exact Fin.cases rfl (fun _ => rfl) j

def coneTuple (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (H : Fin d → Fin m → ℝ) : Fin d → ConvexBody E :=
  fun j => bodyAtHeight l h₀ hp hc (H j)

def facetMixedValue (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (H : Fin d → Fin m → ℝ) (y : Fin m → ℝ)
    (i : Fin m) (v : E) (hv : l i v = 1) : ℝ :=
  mixedVolume (kernelMeasure (l i))
    (Fin.cons (kernelBody (bodyAtHeight l h₀ hp hc y) (l i) v hv)
      (fun j => kernelBody (bodyAtHeight l h₀ hp hc (H j)) (l i) v hv))

theorem mixedSupportForm_facet_on_cone
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) (hn : ∀ i, l i ≠ 0)
    (hray : ∀ i j {c : ℝ}, 0 < c → l i = c • l j → i = j)
    (H : Fin d → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc)
    (v : Fin m → E) (hv : ∀ i, l i (v i) = 1)
    {x y : Fin m → ℝ} (hx : x ∈ typeCone l h₀ hp hc)
    (hy : y ∈ typeCone l h₀ hp hc) :
    ((d + 2 : ℕ) : ℝ) *
      mixedSupportForm volume l h₀ hg hp hc (coneTuple l h₀ hp hc H) x y =
      ∑ i, facetFrameFactor (l i) (v i) (hv i) * x i *
        facetMixedValue l h₀ hp hc H y i (v i) (hv i) := by
  first
  | let G : Fin (d + 1) → Fin m → ℝ := Fin.cons y H
    have hG : ∀ j, G j ∈ typeCone l h₀ hp hc :=
      fun j => Fin.cases hy hH j
    let K : Fin (d + 1) → ConvexBody E := fun j => bodyAtHeight l h₀ hp hc (G j)
    let D := fixedFacetsOfCone l h₀ hg hp hc hf hn hray G hG
    have hK0 : ∀ j, (0 : E) ∈ K j := by
      intro j
      change (0 : E) ∈ (K j : Set E)
      rw [show (K j : Set E) = body l (G j) from coe_bodyAtHeight l h₀ hp hc (hG j)]
      exact fun i => by simpa only [map_zero] using ((hG j).1 i).le
    have hsum : (∑ j, (K j : Set E)) = body l (∑ j, G j) := by
      rw [← coe_sum_body, ← bodyAtHeight_sum l h₀ hp hc G hG,
        coe_bodyAtHeight l h₀ hp hc (typeCone_sum_mem l h₀ hp hc G hG)]
    have hKint : (0 : E) ∈ interior (∑ j, (K j : Set E)) := by
      rw [hsum]
      exact zero_mem_interior_body l _ (typeCone_sum_mem l h₀ hp hc G hG).1
    have he := mixedVolume_facet_identity K D hK0 hKint v hv
      (bodyAtHeight l h₀ hp hc x)
    have hsupport (i : Fin m) :
        SupportGeometry.support (bodyAtHeight l h₀ hp hc x : Set E) (l i) = x i :=
      bodyAtHeight_support l h₀ hg hp hc hf hx i
    rw [mixedSupportForm_eq_value volume l h₀ hg hp hc _ hx hy]
    unfold mixedSupportValue coneTuple facetMixedValue
    have hadd : d + 1 + 1 = d + 2 := by omega
    simp only [D, fixedFacetsOfCone, K, G, coneTuple, mixedSupportValue,
      hsupport, facetMixedValue, map_finCons, kernelBody_finCons, hadd] at he
    convert he using 1 <;> rfl

/-- The facet formula extends in its first argument to every real height
direction, not just those that define a convex body. -/
theorem mixedSupportForm_facet
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) (hn : ∀ i, l i ≠ 0)
    (hray : ∀ i j {c : ℝ}, 0 < c → l i = c • l j → i = j)
    (H : Fin d → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc)
    (v : Fin m → E) (hv : ∀ i, l i (v i) = 1)
    (x : Fin m → ℝ) {y : Fin m → ℝ} (hy : y ∈ typeCone l h₀ hp hc) :
    ((d + 2 : ℕ) : ℝ) *
      mixedSupportForm volume l h₀ hg hp hc (coneTuple l h₀ hp hc H) x y =
      ∑ i, facetFrameFactor (l i) (v i) (hv i) * x i *
        facetMixedValue l h₀ hp hc H y i (v i) (hv i) := by
  first
  | obtain ⟨a, ha, b, hb, rfl⟩ := OpenConeExtension.exists_difference
      (typeCone l h₀ hp hc) (typeCone_isOpen l h₀ hp hc)
      (typeCone_nonempty l h₀ hg hp hc) x
    have hfa := mixedSupportForm_facet_on_cone l h₀ hg hp hc hf hn hray H hH v hv ha hy
    have hfb := mixedSupportForm_facet_on_cone l h₀ hg hp hc hf hn hray H hH v hv hb hy
    rw [LinearMap.BilinForm.sub_left, mul_sub, hfa, hfb, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply]
    ring

theorem mixedSupportForm_coordinate_facet
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) (hn : ∀ i, l i ≠ 0)
    (hray : ∀ i j {c : ℝ}, 0 < c → l i = c • l j → i = j)
    (H : Fin d → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc)
    (v : Fin m → E) (hv : ∀ i, l i (v i) = 1)
    (i : Fin m) {y : Fin m → ℝ} (hy : y ∈ typeCone l h₀ hp hc) :
    ((d + 2 : ℕ) : ℝ) *
      mixedSupportForm volume l h₀ hg hp hc (coneTuple l h₀ hp hc H) (Pi.single i 1) y =
      facetFrameFactor (l i) (v i) (hv i) *
        facetMixedValue l h₀ hp hc H y i (v i) (hv i) := by
  first
  | simpa only [Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] using
      mixedSupportForm_facet l h₀ hg hp hc hf hn hray H hH v hv (Pi.single i 1) hy

/-- Every off-diagonal entry of the actual symmetric mixed-support matrix is
nonnegative. The proof uses inclusion of genuine fixed-kernel facet bodies. -/
theorem mixedSupportMatrix_offdiag_nonnegative
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) (hn : ∀ i, l i ≠ 0)
    (hray : ∀ i j {c : ℝ}, 0 < c → l i = c • l j → i = j)
    (H : Fin d → Fin m → ℝ) (hH : ∀ k, H k ∈ typeCone l h₀ hp hc)
    (hdim : finrank ℝ E = d + 2) (v : Fin m → E) (hv : ∀ i, l i (v i) = 1)
    (i j : Fin m) (hij : i ≠ j) :
    0 ≤ mixedSupportMatrix volume l h₀ hg hp hc (coneTuple l h₀ hp hc H) i j := by
  first
  | have href : h₀ ∈ typeCone l h₀ hp hc := mem_typeRegion_self l h₀ hg hp
    obtain ⟨ε, hε, hplus⟩ := OpenConeExtension.exists_pos_sub_mem
      (typeCone l h₀ hp hc) (typeCone_isOpen l h₀ hp hc) href (-(Pi.single j 1))
    rw [smul_neg, sub_neg_eq_add] at hplus
    have hle : kernelBody (bodyAtHeight l h₀ hp hc h₀) (l i) (v i) (hv i) ≤
        kernelBody (bodyAtHeight l h₀ hp hc (h₀ + ε • Pi.single j 1)) (l i) (v i) (hv i) := by
      apply kernelBody_bodyAtHeight_mono l h₀ hg hp hc hf href hplus
      · intro k
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact le_add_of_nonneg_right (mul_nonneg hε.le (by
          by_cases hk : k = j <;> simp [Pi.single_apply, hk]))
      · simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hij,
          smul_zero, add_zero]
    have hkdim : finrank ℝ (LinearMap.ker (l i).toLinearMap) = d + 1 := by
      have he := LinearFrame.finrank_kernel_add_one (l i) (v i) (hv i)
      rw [hdim] at he
      omega
    letI : Nontrivial (LinearMap.ker (l i).toLinearMap) :=
      Module.nontrivial_of_finrank_eq_succ hkdim
    have hmono : facetMixedValue l h₀ hp hc H h₀ i (v i) (hv i) ≤
        facetMixedValue l h₀ hp hc H (h₀ + ε • Pi.single j 1) i (v i) (hv i) :=
      mixedVolume_mono_first_all (kernelMeasure (l i)) _ hkdim _ _ hle
    have hf0 := mixedSupportForm_coordinate_facet l h₀ hg hp hc hf hn hray H hH v hv i href
    have hf1 := mixedSupportForm_coordinate_facet l h₀ hg hp hc hf hn hray H hH v hv i hplus
    have hscaled := mul_le_mul_of_nonneg_left hmono (facetFrameFactor_nonneg (l i) (v i) (hv i))
    rw [← hf0, ← hf1, LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right] at hscaled
    change 0 ≤ mixedSupportForm volume l h₀ hg hp hc (coneTuple l h₀ hp hc H)
      (Pi.single i 1) (Pi.single j 1)
    have hdimpos : (0 : ℝ) < ((d + 2 : ℕ) : ℝ) := by positivity
    have hs := Iff.mp (mul_le_mul_iff_of_pos_left hdimpos) hscaled
    have hz : 0 ≤ ε * mixedSupportForm volume l h₀ hg hp hc
        (coneTuple l h₀ hp hc H) (Pi.single i 1) (Pi.single j 1) := by linarith
    exact nonneg_of_mul_nonneg_right hz hε

end VolumePolynomials.PolyhedralSupport
