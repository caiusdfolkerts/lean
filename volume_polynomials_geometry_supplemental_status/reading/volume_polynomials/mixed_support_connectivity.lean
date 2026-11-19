module

public import VolumePolynomials.MixedSupportOperator
public import VolumePolynomials.DiagonalSupportHyperbolicity
public import VolumePolynomials.MatrixGraphFromHyperbolicity

@[expose] public section
set_option autoImplicit false

/-! # Connectivity of the genuine mixed-support operator

Every cone background contains a positive scalar multiple of the reference
in the Minkowski sense. Expanding the actual multilinear extension gives a
positive lower comparison with the diagonal-background matrix. The latter
has positive image on the reference heights, and Brunn--Minkowski supplies
its one-positive-direction inequality. Thus the positive-entry graph is
connected without a separately assumed facet-adjacency theorem.
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

theorem facetFrameFactor_pos (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1) :
    0 < facetFrameFactor l v hv := by
  first
  | letI : MeasureSpace (LinearMap.ker l.toLinearMap) := ⟨kernelMeasure l⟩
    letI : Measure.IsAddHaarMeasure (volume : Measure (LinearMap.ker l.toLinearMap)) :=
      kernelMeasure_isAddHaarMeasure l
    change 0 < (LinearFrame.volumeFactor (LinearFrame.continuousEquiv l v hv) : ℝ)
    exact_mod_cast LinearFrame.volumeFactor_pos (LinearFrame.continuousEquiv l v hv)

theorem diagonal_mixedSupportMatrix_image_pos
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) (hn : ∀ i, l i ≠ 0)
    (hray : ∀ i j {c : ℝ}, 0 < c → l i = c • l j → i = j)
    (hdim : finrank ℝ E = n + 2)
    (v : Fin m → E) (hv : ∀ i, l i (v i) = 1) (i : Fin m) :
    0 < (mixedSupportMatrix volume l h₀ hg hp hc
      (fun _ : Fin n => bodyAtHeight l h₀ hp hc h₀) *ᵥ h₀) i := by
  first
  | have href : h₀ ∈ typeCone l h₀ hp hc := mem_typeRegion_self l h₀ hg hp
    have hkdim : finrank ℝ (LinearMap.ker (l i).toLinearMap) = n + 1 := by
      have he := LinearFrame.finrank_kernel_add_one (l i) (v i) (hv i)
      rw [hdim] at he
      omega
    let Q := kernelBody (bodyAtHeight l h₀ hp hc h₀) (l i) (v i) (hv i)
    have hQint : (interior (Q : Set (LinearMap.ker (l i).toLinearMap))).Nonempty :=
      kernelBody_bodyAtHeight_interior_nonempty l h₀ hg hp hc hf href i (v i) (hv i)
    have hQpos : 0 < (kernelMeasure (l i)).real (Q : Set _) := by
      exact ENNReal.toReal_pos
        (Measure.measure_pos_of_nonempty_interior (kernelMeasure (l i)) hQint).ne'
        (Q.isCompact.measure_ne_top (μ := kernelMeasure (l i)))
    have hlow : 0 < facetMixedValue l h₀ hp hc (fun _ : Fin n => h₀) h₀ i (v i) (hv i) := by
      unfold facetMixedValue
      rw [MultilinearDiagonal.cons_const, mixedVolume_diagonal (kernelMeasure (l i)) hkdim]
      exact hQpos
    have he := mixedSupportForm_coordinate_facet l h₀ hg hp hc hf hn hray
      (fun _ : Fin n => h₀) (fun _ => href) v hv i href
    have hprod : 0 < facetFrameFactor (l i) (v i) (hv i) *
        facetMixedValue l h₀ hp hc (fun _ : Fin n => h₀) h₀ i (v i) (hv i) :=
      mul_pos (facetFrameFactor_pos (l i) (v i) (hv i)) hlow
    rw [← he, mixedSupportForm_eq_dotProduct, single_one_dotProduct] at hprod
    exact (mul_pos_iff_of_pos_left (by positivity : (0 : ℝ) < ((n + 2 : ℕ) : ℝ))).mp hprod

theorem exists_positive_mixedSupportMatrix_domination
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) (hn : ∀ i, l i ≠ 0)
    (hray : ∀ i j {c : ℝ}, 0 < c → l i = c • l j → i = j)
    (hdim : finrank ℝ E = n + 2)
    (H : Fin n → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc)
    (v : Fin m → E) (hv : ∀ i, l i (v i) = 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ i j, i ≠ j →
      c * mixedSupportMatrix volume l h₀ hg hp hc
        (fun _ : Fin n => bodyAtHeight l h₀ hp hc h₀) i j ≤
      mixedSupportMatrix volume l h₀ hg hp hc (coneTuple l h₀ hp hc H) i j := by
  first
  | let C := typeCone l h₀ hp hc
    have href : h₀ ∈ C := mem_typeRegion_self l h₀ hg hp
    obtain ⟨ε, hε, hG⟩ := OpenConeExtension.exists_pos_sub_all C
      (typeCone_isOpen l h₀ hp hc) H hH h₀
    let G : Fin n → Fin m → ℝ := fun k => H k - ε • h₀
    have hscale : ε • h₀ ∈ C := C.smul_mem hε href
    refine ⟨ε ^ n, pow_pos hε n, ?_⟩
    intro i j hij
    let F := ((supportMultilinearVolume volume l h₀ hg hp hc (n + 2)).curryLeft
      (Pi.single i 1)).curryLeft (Pi.single j 1)
    have hF (L : Fin n → Fin m → ℝ) (hL : ∀ k, L k ∈ C) :
        F L = mixedSupportMatrix volume l h₀ hg hp hc (coneTuple l h₀ hp hc L) i j := by
      exact congrArg (fun B : LinearMap.BilinForm ℝ (Fin m → ℝ) => B (Pi.single i 1) (Pi.single j 1))
        (supportMultilinearVolume_firstTwoForm volume l h₀ hg hp hc L hL)
    have hFnonneg (L : Fin n → Fin m → ℝ) (hL : ∀ k, L k ∈ C) : 0 ≤ F L := by
      rw [hF L hL]
      exact mixedSupportMatrix_offdiag_nonnegative l h₀ hg hp hc hf hn hray
        L hL hdim v hv i j hij
    have hdecomp : H = (fun _ : Fin n => ε • h₀) + G := by
      funext k
      change H k = ε • h₀ + (H k - ε • h₀)
      abel
    have hterm (s : Finset (Fin n)) :
        0 ≤ F (s.piecewise (fun _ => ε • h₀) G) := by
      apply hFnonneg
      intro k
      by_cases hk : k ∈ s
      · simpa only [Finset.piecewise, hk, if_true] using hscale
      · simpa only [Finset.piecewise, hk, if_false, G] using hG k
    have hsingle : F (fun _ : Fin n => ε • h₀) ≤ F H := by
      rw [hdecomp, F.map_add_univ]
      have h := Finset.single_le_sum (s := Finset.univ)
        (f := fun s : Finset (Fin n) => F (s.piecewise (fun _ => ε • h₀) G))
        (fun s _ => hterm s) (Finset.mem_univ (Finset.univ : Finset (Fin n)))
      simpa only [Finset.piecewise_univ] using h
    have hhom : F (fun _ : Fin n => ε • h₀) = ε ^ n * F (fun _ => h₀) := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using
        F.map_smul_univ (fun _ : Fin n => ε) (fun _ => h₀)
    rw [hhom, hF H hH, hF (fun _ => h₀) (fun _ => href)] at hsingle
    exact hsingle

/-- Positive-entry connectivity for the actual mixed-support matrix, with
every geometric and Brunn--Minkowski input discharged. -/
theorem mixedSupportMatrix_positive_graph_connected
    (l : Fin m → E →L[ℝ] ℝ) (h₀ : Fin m → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hf : StrictFacets l h₀) (hn : ∀ i, l i ≠ 0)
    (hray : ∀ i j {c : ℝ}, 0 < c → l i = c • l j → i = j)
    (hdim : finrank ℝ E = n + 2)
    (H : Fin n → Fin m → ℝ) (hH : ∀ j, H j ∈ typeCone l h₀ hp hc)
    (v : Fin m → E) (hv : ∀ i, l i (v i) = 1) :
    ∀ i j, Relation.ReflTransGen
      (MatrixPositiveEdge (mixedSupportMatrix volume l h₀ hg hp hc
        (coneTuple l h₀ hp hc H))) i j := by
  first
  | let B := mixedSupportMatrix volume l h₀ hg hp hc
      (fun _ : Fin n => bodyAtHeight l h₀ hp hc h₀)
    have href : h₀ ∈ typeCone l h₀ hp hc := mem_typeRegion_self l h₀ hg hp
    have hconn : ∀ i j, Relation.ReflTransGen (MatrixPositiveEdge B) i j := by
      apply matrix_positive_graph_connected_of_reverse_cauchy_schwarz B
        (mixedSupportMatrix_symmetric volume l h₀ hg hp hc _)
        (mixedSupportMatrix_offdiag_nonnegative l h₀ hg hp hc hf hn hray
          (fun _ : Fin n => h₀) (fun _ => href) hdim v hv) h₀ hp
        (diagonal_mixedSupportMatrix_image_pos l h₀ hg hp hc hf hn hray hdim v hv)
      intro x y hy
      have hy' : 0 ≤ mixedSupportForm volume l h₀ hg hp hc
          (fun _ : Fin n => bodyAtHeight l h₀ hp hc h₀) y y := by
        simpa only [mixedSupportForm_eq_dotProduct] using hy
      have he := diagonal_mixedSupportForm_reverse_cauchy_schwarz
        volume l h₀ hg hp hc hdim x y hy'
      simpa only [mixedSupportForm_eq_dotProduct] using he
    obtain ⟨c, hcpos, hdom⟩ := exists_positive_mixedSupportMatrix_domination
      l h₀ hg hp hc hf hn hray hdim H hH v hv
    exact matrix_positive_graph_connected_of_dominates _ B hcpos hdom hconn

end VolumePolynomials.PolyhedralSupport
