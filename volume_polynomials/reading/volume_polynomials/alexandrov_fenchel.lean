module

public import VolumePolynomials.FacetBochnerStep
public import VolumePolynomials.FiniteHullInvariantTransfer
public import VolumePolynomials.PlanarMixedForm

@[expose] public section
set_option autoImplicit false

/-! # Alexandrov--Fenchel for actual compact convex bodies

The induction begins with the actual planar Brunn--Minkowski inequality.
The next dimension is proved on a constructed common simple support type
by the actual facet identities and the finite Bochner argument. Genuine
common-refinement approximants, independent translations, simplex
thickening, and finite-hull density remove every geometric restriction.

Mixed volume throughout is the normalized coefficient of the proved
Minkowski volume polynomial, with the specified actual Haar measure.
-/

noncomputable section
open Set Filter MeasureTheory Module Matrix LinearMap
open scoped Pointwise Topology BigOperators

namespace VolumePolynomials

open PolytopeGeometry PolyhedralSupport

universe u

def firstRepeatIndex (n : ℕ) : Fin (n + 2) → Fin (n + 2) :=
  Fin.cons 0 (Fin.cons 0 (fun i : Fin n => i.succ.succ))

def secondRepeatIndex (n : ℕ) : Fin (n + 2) → Fin (n + 2) :=
  Fin.cons 1 (Fin.cons 1 (fun i : Fin n => i.succ.succ))

section Tuple

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ] {n : ℕ}

def AFBodyTuple (K : Fin (n + 2) → ConvexBody E) : Prop :=
  mixedVolume μ (fun i => K (firstRepeatIndex n i)) *
      mixedVolume μ (fun i => K (secondRepeatIndex n i)) ≤ mixedVolume μ K ^ 2

theorem AFBodyTuple_cons (A B : ConvexBody E) (K : Fin n → ConvexBody E) :
    AFBodyTuple μ (Fin.cons A (Fin.cons B K)) ↔
      mixedVolume μ (Fin.cons A (Fin.cons A K)) *
        mixedVolume μ (Fin.cons B (Fin.cons B K)) ≤
      mixedVolume μ (Fin.cons A (Fin.cons B K)) ^ 2 := by
  first
  | have hfirst : (fun i : Fin (n + 2) =>
        (Fin.cons A (Fin.cons B K) : Fin (n + 2) → ConvexBody E) (firstRepeatIndex n i)) =
        (Fin.cons A (Fin.cons A K) : Fin (n + 2) → ConvexBody E) := by
      funext i
      exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i
    have hsecond : (fun i : Fin (n + 2) =>
        (Fin.cons A (Fin.cons B K) : Fin (n + 2) → ConvexBody E) (secondRepeatIndex n i)) =
        (Fin.cons B (Fin.cons B K) : Fin (n + 2) → ConvexBody E) := by
      funext i
      exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i
    simp only [AFBodyTuple, hfirst, hsecond]

theorem isClosed_afBodyTuples : IsClosed {K : Fin (n + 2) → ConvexBody E | AFBodyTuple μ K} := by
  first
  | apply isClosed_le
    · exact ((continuous_mixedVolume μ (n + 2)).comp
        (continuous_pi (fun i => continuous_apply (firstRepeatIndex n i)))).mul
        ((continuous_mixedVolume μ (n + 2)).comp
          (continuous_pi (fun i => continuous_apply (secondRepeatIndex n i))))
    · exact (continuous_mixedVolume μ (n + 2)).pow 2

theorem AFBodyTuple.translate {K : Fin (n + 2) → ConvexBody E}
    (hK : AFBodyTuple μ K) (v : Fin (n + 2) → E) :
    AFBodyTuple μ (fun i => translateBody (v i) (K i)) := by
  first
  | change mixedVolume μ (fun i => translateBody (v (firstRepeatIndex n i))
        (K (firstRepeatIndex n i))) *
      mixedVolume μ (fun i => translateBody (v (secondRepeatIndex n i))
        (K (secondRepeatIndex n i))) ≤
      mixedVolume μ (fun i => translateBody (v i) (K i)) ^ 2
    simpa only [AFBodyTuple, mixedVolume_translate] using hK

end Tuple

/-- The induction predicate has no restriction on the norm, Haar
normalization, or dimension of the individual convex bodies. -/
def AlexandrovFenchelDimension (n : ℕ) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ],
    finrank ℝ E = n + 2 → ∀ K : Fin (n + 2) → ConvexBody E, AFBodyTuple μ K

theorem alexandrovFenchelDimension_zero : AlexandrovFenchelDimension.{u} 0 := by
  first
  | intro E _ _ _ _ _ μ _ hdim K
    have hK : K = ![K 0, K 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hK]
    apply (AFBodyTuple_cons μ (K 0) (K 1) (fun i : Fin 0 => Fin.elim0 i)).mpr
    have hdiag (A : ConvexBody E) :
        mixedVolume μ (Fin.cons A (Fin.cons A (fun i : Fin 0 => Fin.elim0 i))) =
          μ.real (A : Set E) := by
      have he : Fin.cons A (Fin.cons A (fun i : Fin 0 => Fin.elim0 i)) =
          (fun _ : Fin 2 => A) := by
        funext i
        fin_cases i <;> rfl
      rw [he, mixedVolume_diagonal μ hdim]
    rw [hdiag, hdiag]
    exact PlanarMixedForm.minkowski_squared μ hdim (K 0) (K 1)

section DimensionStep

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  {n : ℕ}

theorem AFBodyTuple_commonRefinement
    (hIH : AlexandrovFenchelDimension.{u} n) (hdim : finrank ℝ E = n + 3)
    (K : Fin (n + 3) → ConvexBody E) (D : CommonRefinement K)
    (h0 : ∀ i, (0 : E) ∈ K i) {r : ℝ} (hr : 0 < r) :
    AFBodyTuple volume (D.approximant r) := by
  first
  | let l := D.facets.normal
    let h₀ := D.height
    have hc : IsCompact (body l h₀) := D.reference_eq ▸ D.reference.isCompact
    let G := D.approximantHeight r
    have hG : ∀ j, G j ∈ typeCone l h₀ D.height_pos hc :=
      D.approximantHeight_mem_supportCone h0 hr
    have hbody (j : Fin (n + 3)) :
        bodyAtHeight l h₀ D.height_pos hc (G j) = D.approximant r j := by
      apply ConvexBody.ext
      rw [coe_bodyAtHeight l h₀ D.height_pos hc (hG j), D.approximant_eq_halfspaces hr j]
    have hw : ∀ i, ∃ v : E, l i v = 1 := by
      intro i
      have hnot : ¬ ∀ x : E, l i x = 0 := by
        intro hz
        apply D.facets.normal_ne_zero i
        ext x
        exact hz x
      obtain ⟨x, hx⟩ := not_forall.mp hnot
      refine ⟨(l i x)⁻¹ • x, ?_⟩
      simp only [map_smul, smul_eq_mul, inv_mul_cancel₀ hx]
    choose v hv using hw
    let x := G 0
    let y := G 1
    let h := G 2
    let H : Fin n → Fin D.facets.count → ℝ := fun j => G j.succ.succ.succ
    have hx : x ∈ typeCone l h₀ D.height_pos hc := hG 0
    have hy : y ∈ typeCone l h₀ D.height_pos hc := hG 1
    have hh : h ∈ typeCone l h₀ D.height_pos hc := hG 2
    have hH : ∀ j, H j ∈ typeCone l h₀ D.height_pos hc := fun j => hG _
    have hlow : ∀ i (J : Fin n → ConvexBody (LinearMap.ker (l i).toLinearMap))
        (A B : ConvexBody (LinearMap.ker (l i).toLinearMap)),
        mixedVolume (kernelMeasure (l i)) (Fin.cons A (Fin.cons A J)) *
          mixedVolume (kernelMeasure (l i)) (Fin.cons B (Fin.cons B J)) ≤
        mixedVolume (kernelMeasure (l i)) (Fin.cons A (Fin.cons B J)) ^ 2 := by
      intro i J A B
      have hkdim : finrank ℝ (LinearMap.ker (l i).toLinearMap) = n + 2 := by
        have he := LinearFrame.finrank_kernel_add_one (l i) (v i) (hv i)
        rw [hdim] at he
        omega
      exact (AFBodyTuple_cons (kernelMeasure (l i)) A B J).mp
        (hIH _ (kernelMeasure (l i)) hkdim (Fin.cons A (Fin.cons B J)))
    let B := mixedSupportForm volume l h₀ D.generic D.height_pos hc
      (coneTuple l h₀ D.height_pos hc (Fin.cons h H))
    have hBnonneg : 0 ≤ B y y := by
      rw [mixedSupportForm_eq_value volume l h₀ D.generic D.height_pos hc _ hy hy]
      exact mixedVolume_nonnegative volume _
    have hi := mixedSupportForm_reverse_cauchy_schwarz_of_lower_dimension
      l h₀ D.generic D.height_pos hc D.strict_facets D.facets.normal_ne_zero
      D.facets.positive_ray_injective hdim H hH hh v hv hlow x y hBnonneg
    rw [mixedSupportForm_eq_value volume l h₀ D.generic D.height_pos hc _ hx hx,
      mixedSupportForm_eq_value volume l h₀ D.generic D.height_pos hc _ hy hy,
      mixedSupportForm_eq_value volume l h₀ D.generic D.height_pos hc _ hx hy] at hi
    have htuple : D.approximant r =
        Fin.cons (bodyAtHeight l h₀ D.height_pos hc x)
          (Fin.cons (bodyAtHeight l h₀ D.height_pos hc y)
            (coneTuple l h₀ D.height_pos hc (Fin.cons h H))) := by
      funext j
      refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun q => Fin.cases ?_ (fun s => ?_) q) k) j
      · exact (hbody 0).symm
      · exact (hbody 1).symm
      · exact (hbody 2).symm
      · exact (hbody s.succ.succ.succ).symm
    rw [htuple, AFBodyTuple_cons]
    exact hi

theorem AFBodyTuple_centered_finiteHull
    (hIH : AlexandrovFenchelDimension.{u} n) (hdim : finrank ℝ E = n + 3)
    (K : Fin (n + 3) → ConvexBody E)
    (hK : ∀ i, IsFiniteHull (K i : Set E)) (h0 : ∀ i, (0 : E) ∈ K i)
    (hint : (0 : E) ∈ interior (↑(∑ i, K i) : Set E)) : AFBodyTuple volume K := by
  first
  | obtain ⟨D⟩ := exists_commonRefinement K hK h0 hint
    have hlim : Tendsto D.approximant (𝓝[>] (0 : ℝ)) (𝓝 K) :=
      D.tendsto_approximant_zero.mono_left nhdsWithin_le_nhds
    apply (isClosed_afBodyTuples volume).mem_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact AFBodyTuple_commonRefinement hIH hdim K D h0 hr

end DimensionStep

theorem alexandrovFenchelDimension_succ {n : ℕ}
    (hIH : AlexandrovFenchelDimension.{u} n) : AlexandrovFenchelDimension.{u} (n + 1) := by
  first
  | intro E _ _ _ _ _ μ _ hdim K
    letI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hdim
    letI : MeasureSpace E := ⟨μ⟩
    letI : Measure.IsAddHaarMeasure (volume : Measure E) :=
      inferInstanceAs (Measure.IsAddHaarMeasure μ)
    exact all_bodyTuples_of_centered_finiteHull (by omega)
      {L : Fin (n + 3) → ConvexBody E | AFBodyTuple μ L}
      (isClosed_afBodyTuples μ)
      (fun L hL v => AFBodyTuple.translate μ hL v)
      (fun L hL h0 hint => AFBodyTuple_centered_finiteHull hIH hdim L hL h0 hint) K

theorem alexandrovFenchelDimension (n : ℕ) : AlexandrovFenchelDimension.{u} n := by
  first
  | induction n with
    | zero => exact alexandrovFenchelDimension_zero
    | succ n ih => exact alexandrovFenchelDimension_succ ih

/-- The full Alexandrov--Fenchel inequality for actual compact convex bodies,
in every ambient dimension at least two and for every actual Haar measure. -/
theorem mixedVolume_alexandrovFenchel
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {n : ℕ}
    (hdim : finrank ℝ E = n + 2) (K : Fin n → ConvexBody E) (A B : ConvexBody E) :
    mixedVolume μ (Fin.cons A (Fin.cons A K)) *
        mixedVolume μ (Fin.cons B (Fin.cons B K)) ≤
      mixedVolume μ (Fin.cons A (Fin.cons B K)) ^ 2 :=
  (AFBodyTuple_cons μ A B K).mp
    (alexandrovFenchelDimension n E μ hdim (Fin.cons A (Fin.cons B K)))

end VolumePolynomials
