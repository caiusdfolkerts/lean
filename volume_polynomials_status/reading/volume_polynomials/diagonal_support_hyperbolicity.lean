module

public import VolumePolynomials.MultilinearDiagonalDerivatives
public import VolumePolynomials.HaarBrunnMinkowski
public import VolumePolynomials.RootConcavitySecondDerivative
public import VolumePolynomials.HyperbolicForm

@[expose] public section
set_option autoImplicit false

/-! # Diagonal-background hyperbolicity from actual Brunn--Minkowski

The function along each real support direction is the diagonal of the
constructed multilinear volume extension. On an actual open interval it is
the genuine volume of the corresponding convex body. Brunn--Minkowski gives
root concavity, and the genuine first and second derivatives give the
reference reverse Cauchy--Schwarz inequality. No Alexandrov--Fenchel result
is used in this diagonal-background step.
-/

noncomputable section
open Set MeasureTheory Module Filter LinearMap
open scoped Pointwise Topology BigOperators

namespace VolumePolynomials.PolyhedralSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem rootVolume_concave_typeCone
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (hdim : finrank ℝ E ≠ 0) :
    ConcaveOn ℝ (typeCone l h₀ hp hc : Set (ι → ℝ))
      (fun h => μ.real (body l h) ^ ((finrank ℝ E : ℝ)⁻¹)) := by
  first
  | apply concaveOn_iff_forall_pos.mpr
    refine ⟨(typeCone l h₀ hp hc).convex, ?_⟩
    intro h hh k hk a b ha hb hab
    have hah : a • h ∈ typeCone l h₀ hp hc := (typeCone l h₀ hp hc).smul_mem ha hh
    have hbk : b • k ∈ typeCone l h₀ hp hc := (typeCone l h₀ hp hc).smul_mem hb hk
    have hsum : a • h + b • k ∈ typeCone l h₀ hp hc :=
      (typeCone l h₀ hp hc).add_mem hah hbk
    have h := haar_brunn_minkowski μ hdim
      (bodyAtHeight l h₀ hp hc h) (bodyAtHeight l h₀ hp hc k) ha.le hb.le
    rw [← bodyAtHeight_smul l h₀ hp hc hh ha,
      ← bodyAtHeight_smul l h₀ hp hc hk hb,
      ← bodyAtHeight_add l h₀ hp hc hah hbk] at h
    simpa only [coe_bodyAtHeight l h₀ hp hc hh,
      coe_bodyAtHeight l h₀ hp hc hk, coe_bodyAtHeight l h₀ hp hc hsum,
      smul_eq_mul] using h

theorem realVolume_body_pos
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {h : ι → ℝ} (hh : h ∈ typeCone l h₀ hp hc) : 0 < μ.real (body l h) := by
  first
  | have hpos := Measure.measure_pos_of_nonempty_interior μ
      ⟨0, zero_mem_interior_body l h hh.1⟩
    have hfin := (isCompact_body_of_positive_reference l h₀ hp hc h).measure_ne_top (μ := μ)
    exact ENNReal.toReal_pos hpos.ne' hfin

/-- The diagonal mixed-support form obeys the reference inequality on every
real direction, including directions which are not support functions. -/
theorem diagonal_mixedSupportForm_reference_inequality
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {n : ℕ} (hdim : finrank ℝ E = n + 2) (x : ι → ℝ) :
    let B := mixedSupportForm μ l h₀ hg hp hc
      (fun _ : Fin n => bodyAtHeight l h₀ hp hc h₀)
    B x x * B h₀ h₀ ≤ B x h₀ ^ 2 := by
  first
  | let C := typeCone l h₀ hp hc
    let F := supportMultilinearVolume μ l h₀ hg hp hc (n + 2)
    let B := mixedSupportForm μ l h₀ hg hp hc
      (fun _ : Fin n => bodyAtHeight l h₀ hp hc h₀)
    have href : h₀ ∈ C := mem_typeRegion_self l h₀ hg hp
    have hsym : MultilinearDiagonal.PermutationSymmetric F :=
      fun H e => supportMultilinearVolume_reindex μ l h₀ hg hp hc H e
    have hform : firstTwoForm F (fun _ : Fin n => h₀) = B :=
      supportMultilinearVolume_firstTwoForm μ l h₀ hg hp hc _ (fun _ => href)
    have hpair (a b : ι → ℝ) :
        F (Fin.cons a (Fin.cons b (fun _ : Fin n => h₀))) = B a b :=
      congrArg (fun T : LinearMap.BilinForm ℝ (ι → ℝ) => T a b) hform
    let f : ℝ → ℝ := fun t => F (fun _ => h₀ + t • x)
    let f' : ℝ → ℝ := fun t => ((n + 2 : ℕ) : ℝ) * F (Fin.cons x (fun _ => h₀ + t • x))
    have hnear : ∀ᶠ t : ℝ in 𝓝 0, h₀ + t • x ∈ C := by
      have ht : Tendsto (fun t : ℝ => h₀ + t • x) (𝓝 0) (𝓝 h₀) := by
        have hcurve : Continuous (fun t : ℝ => h₀ + t • x) :=
          continuous_const.add (continuous_id.smul continuous_const)
        simpa only [zero_smul, add_zero] using
          hcurve.tendsto (0 : ℝ)
      exact ht.eventually ((typeCone_isOpen l h₀ hp hc).mem_nhds href)
    obtain ⟨ε, hε, hs⟩ := Metric.eventually_nhds_iff.mp hnear
    have hmem (t : ℝ) (ht : t ∈ Ioo (-ε) ε) : h₀ + t • x ∈ C := by
      apply hs
      rw [Real.dist_eq, sub_zero]
      exact abs_lt.mpr ht
    have hvol (t : ℝ) (ht : t ∈ Ioo (-ε) ε) : f t = μ.real (body l (h₀ + t • x)) :=
      supportMultilinearVolume_diagonal μ l h₀ hg hp hc hdim (hmem t ht)
    have hpos (t : ℝ) (ht : t ∈ Ioo (-ε) ε) : 0 < f t := by
      rw [hvol t ht]
      exact realVolume_body_pos μ l h₀ hp hc (hmem t ht)
    have hd (t : ℝ) (_ht : t ∈ Ioo (-ε) ε) : HasDerivAt f (f' t) t :=
      MultilinearDiagonal.hasDerivAt_diagonal F hsym h₀ x t
    have hd' : HasDerivAt f'
        (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1) * B x x) 0 := by
      simpa only [zero_smul, add_zero, hpair] using
        MultilinearDiagonal.hasDerivAt_first_diagonal_derivative F hsym h₀ x 0
    have hcroot : ConcaveOn ℝ (Ioo (-ε) ε)
        (fun t => f t ^ (((n + 2 : ℕ) : ℝ)⁻¹)) := by
      have hroot := rootVolume_concave_typeCone μ l h₀ hp hc (by rw [hdim]; omega)
      refine ⟨convex_Ioo _ _, ?_⟩
      intro s hs t ht a b ha hb hab
      have hst : a * s + b * t ∈ Ioo (-ε) ε :=
        (convex_Ioo (-ε) ε) hs ht ha hb hab
      have he : a • (h₀ + s • x) + b • (h₀ + t • x) = h₀ + (a * s + b * t) • x := by
        ext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        calc
          a * (h₀ i + s * x i) + b * (h₀ i + t * x i) =
              (a + b) * h₀ i + (a * s + b * t) * x i := by ring
          _ = _ := by rw [hab, one_mul]
      have hineq := hroot.2 (hmem s hs) (hmem t ht) ha hb hab
      rw [he, hdim] at hineq
      simpa only [smul_eq_mul, hvol s hs, hvol t ht, hvol _ hst] using hineq
    have hvalue : f 0 = B h₀ h₀ := by
      dsimp only [f]
      simp only [zero_smul, add_zero]
      simpa only [MultilinearDiagonal.cons_const] using hpair h₀ h₀
    have hfirst : f' 0 = ((n + 2 : ℕ) : ℝ) * B x h₀ := by
      dsimp only [f']
      simp only [zero_smul, add_zero]
      congr 1
      simpa only [MultilinearDiagonal.cons_const] using hpair x h₀
    have h := root_concavity_reference_inequality (d := n + 2) (by omega)
      hε hpos hd hd' hcroot hvalue hfirst
    simpa only [mul_comm] using h

theorem diagonal_mixedSupportForm_positive_reference
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {n : ℕ} (hdim : finrank ℝ E = n + 2) :
    0 < mixedSupportForm μ l h₀ hg hp hc
      (fun _ : Fin n => bodyAtHeight l h₀ hp hc h₀) h₀ h₀ := by
  first
  | have href : h₀ ∈ typeCone l h₀ hp hc := mem_typeRegion_self l h₀ hg hp
    rw [mixedSupportForm_eq_value μ l h₀ hg hp hc _ href href]
    unfold mixedSupportValue
    rw [MultilinearDiagonal.cons_const, MultilinearDiagonal.cons_const,
      mixedVolume_diagonal μ hdim, coe_bodyAtHeight l h₀ hp hc href]
    exact realVolume_body_pos μ l h₀ hp hc href

theorem diagonal_mixedSupportForm_reverse_cauchy_schwarz
    (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hg : Generic l h₀) (hp : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    {n : ℕ} (hdim : finrank ℝ E = n + 2) (x y : ι → ℝ)
    (hy : 0 ≤ mixedSupportForm μ l h₀ hg hp hc
      (fun _ : Fin n => bodyAtHeight l h₀ hp hc h₀) y y) :
    let B := mixedSupportForm μ l h₀ hg hp hc
      (fun _ : Fin n => bodyAtHeight l h₀ hp hc h₀)
    B x x * B y y ≤ B x y ^ 2 := by
  first
  | let B := mixedSupportForm μ l h₀ hg hp hc
      (fun _ : Fin n => bodyAtHeight l h₀ hp hc h₀)
    have hs := mixedSupportForm_symmetric μ l h₀ hg hp hc
      (fun _ : Fin n => bodyAtHeight l h₀ hp hc h₀)
    have hpB : 0 < B h₀ h₀ := diagonal_mixedSupportForm_positive_reference μ l h₀ hg hp hc hdim
    have hperp : ∀ z, B z h₀ = 0 → B z z ≤ 0 :=
      (bilinear_hyperplane_iff_reference_inequality B hs h₀ hpB).mpr
        (diagonal_mixedSupportForm_reference_inequality μ l h₀ hg hp hc hdim)
    exact bilinear_reverse_cauchy_schwarz B hs h₀ hperp x y hy

end VolumePolynomials.PolyhedralSupport
