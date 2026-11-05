module

public import Projection.ConvexHullRigidity
public import Projection.FullDimensionalReduction
public import VolumePolynomials.ProjectionMixedVolumeTransport

/-!
# Transporting the weak hull conclusion and recovering segment rigidity

The analytic work can be carried out in Euclidean coordinates. This file
transports its scalar mixed-volume conclusion through the actual positive
Haar conversion factor, then applies the convex-hull amplification in the
original normed space. No unit spheres or area measures in different norms
are identified.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace RankThreeProjection.Rigidity
open VolumePolynomials

section Algebra
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

/-- The precise weak conclusion needed from the analytic argument. It refers
only to actual convex hulls, translations, and actual mixed volumes. -/
def WeakHullReference {d : ℕ} (K : ConvexBody E) : Prop :=
  ∀ (A C : ConvexBody E) (a : ℝ), 0 < a →
    mixedVolume μ (Fin.cons A (Fin.cons A (fun _ : Fin d => K))) = a →
    mixedVolume μ (Fin.cons A (Fin.cons C (fun _ : Fin d => K))) = a →
    mixedVolume μ (Fin.cons C (Fin.cons C (fun _ : Fin d => K))) = a →
    ∃ t : E,
      mixedVolume μ (Fin.cons (joinBody A (translateBody t C))
        (Fin.cons K (fun _ : Fin d => K))) =
      mixedVolume μ (Fin.cons A (Fin.cons K (fun _ : Fin d => K)))

theorem mixedVolume_pair_translate_background {d : ℕ}
    (K A C : ConvexBody E) (p : E) :
    mixedVolume μ (Fin.cons A (Fin.cons C (fun _ : Fin d => translateBody p K))) =
      mixedVolume μ (Fin.cons A (Fin.cons C (fun _ : Fin d => K))) := by
  have h := mixedVolume_translate μ (Fin.cons A (Fin.cons C (fun _ : Fin d => K)))
    (Fin.cons 0 (Fin.cons 0 (fun _ : Fin d => p)))
  convert h using 1
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun _ => rfl) j) i <;>
    simp only [Fin.cons_zero, Fin.cons_succ, translateBody_zero]

theorem mixedVolume_translate_head {d : ℕ}
    (H : Fin d → ConvexBody E) (A : ConvexBody E) (p : E) :
    mixedVolume μ (Fin.cons (translateBody p A) H) =
      mixedVolume μ (Fin.cons A H) := by
  have h := mixedVolume_translate μ (Fin.cons A H) (Fin.cons p (fun _ => 0))
  convert h using 1
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => by simp only [Fin.cons_succ, translateBody_zero]) i

theorem mixedVolume_translate_second {d : ℕ}
    (H : Fin d → ConvexBody E) (A C : ConvexBody E) (p : E) :
    mixedVolume μ (Fin.cons A (Fin.cons (translateBody p C) H)) =
      mixedVolume μ (Fin.cons A (Fin.cons C H)) := by
  rw [PolyhedralSupport.mixedVolume_cons_cons_swap,
    mixedVolume_translate_head,
    PolyhedralSupport.mixedVolume_cons_cons_swap]

theorem supportContinuous_translate (p : E) (A : ConvexBody E)
    (u : NormalSphere E) :
    supportContinuous (translateBody p A) u = u.val p + supportContinuous A u := by
  rw [translateBody, supportContinuous_add, ContinuousMap.add_apply,
    supportContinuous_point]

theorem translateBody_join (p : E) (A C : ConvexBody E) :
    translateBody p (joinBody A C) = joinBody (translateBody p A) (translateBody p C) := by
  apply supportContinuous_injective
  ext u
  simp only [supportContinuous_translate, supportContinuous_join, ContinuousMap.sup_apply]
  exact add_max _ _ _

/-- It is enough for the analytic comparison to treat bodies containing the
origin. Arbitrary comparison bodies are translated, and the final translation
is adjusted exactly. -/
theorem weakHullReference_of_origin_comparisons {d : ℕ} (K : ConvexBody E)
    (h : ∀ (A C : ConvexBody E), (0 : E) ∈ A → (0 : E) ∈ C →
      ∀ (a : ℝ), 0 < a →
      mixedVolume μ (Fin.cons A (Fin.cons A (fun _ : Fin d => K))) = a →
      mixedVolume μ (Fin.cons A (Fin.cons C (fun _ : Fin d => K))) = a →
      mixedVolume μ (Fin.cons C (Fin.cons C (fun _ : Fin d => K))) = a →
      ∃ t : E,
        mixedVolume μ (Fin.cons (joinBody A (translateBody t C))
          (Fin.cons K (fun _ : Fin d => K))) =
        mixedVolume μ (Fin.cons A (Fin.cons K (fun _ : Fin d => K)))) :
    WeakHullReference μ (d := d) K := by
  intro A C a ha hAA hAC hCC
  obtain ⟨p, hp⟩ := A.nonempty
  obtain ⟨q, hq⟩ := C.nonempty
  let A₀ := translateBody (-p) A
  let C₀ := translateBody (-q) C
  have hA₀ : (0 : E) ∈ A₀ := zero_mem_translateBody_neg hp
  have hC₀ : (0 : E) ∈ C₀ := zero_mem_translateBody_neg hq
  obtain ⟨v, hv⟩ := h A₀ C₀ hA₀ hC₀ a ha
    (by simpa only [A₀, mixedVolume_translate_head, mixedVolume_translate_second] using hAA)
    (by simpa only [A₀, C₀, mixedVolume_translate_head, mixedVolume_translate_second] using hAC)
    (by simpa only [C₀, mixedVolume_translate_head, mixedVolume_translate_second] using hCC)
  refine ⟨p + v - q, ?_⟩
  have he : translateBody p (joinBody A₀ (translateBody v C₀)) =
      joinBody A (translateBody (p + v - q) C) := by
    rw [translateBody_join]
    simp only [A₀, C₀, translateBody_translate, add_neg_cancel, translateBody_zero,
      sub_eq_add_neg, add_assoc]
  rw [← he, mixedVolume_translate_head, hv, mixedVolume_translate_head]

theorem zero_mem_interior_translateBody_neg (K : ConvexBody E) (p : E)
    (hp : p ∈ interior (K : Set E)) :
    (0 : E) ∈ interior ((translateBody (-p) K : ConvexBody E) : Set E) := by
  apply mem_interior_iff_mem_nhds.mpr
  rw [coe_translateBody]
  have hzero : (0 : E) ∈ (-p) +ᵥ interior (K : Set E) :=
    ⟨p, hp, by simp⟩
  apply Filter.mem_of_superset ((isOpen_interior.vadd (-p)).mem_nhds hzero)
  rintro x ⟨y, hy, rfl⟩
  exact ⟨y, interior_subset hy, rfl⟩

/-- Translating the repeated body changes none of the weak conclusion. -/
theorem weakHullReference_of_translate {d : ℕ} (K : ConvexBody E) (p : E)
    (h : WeakHullReference μ (d := d) (translateBody p K)) :
    WeakHullReference μ (d := d) K := by
  intro A C a ha hAA hAC hCC
  obtain ⟨t, ht⟩ := h A C a ha
    (by simpa only [mixedVolume_pair_translate_background] using hAA)
    (by simpa only [mixedVolume_pair_translate_background] using hAC)
    (by simpa only [mixedVolume_pair_translate_background] using hCC)
  refine ⟨t, ?_⟩
  rw [mixedVolume_translate_second, mixedVolume_translate_second,
    mixedVolume_pair_translate_background, mixedVolume_pair_translate_background] at ht
  exact ht

end Algebra

section Frame
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
  (ν : Measure F) [Measure.IsAddHaarMeasure ν]

theorem mapBody_join (T : E →L[ℝ] F) (A C : ConvexBody E) :
    mapBody T (joinBody A C) = joinBody (mapBody T A) (mapBody T C) := by
  apply ConvexBody.ext
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, ha, c, hc, r, s, hr, hs, hrs, rfl⟩ := mem_convexJoin.mp hx
    apply mem_convexJoin.mpr
    exact ⟨T a, ⟨a, ha, rfl⟩, T c, ⟨c, hc, rfl⟩, r, s,
      hr, hs, hrs, by simp only [map_add, map_smul]⟩
  · intro hy
    obtain ⟨a, ⟨x, hx, rfl⟩, c, ⟨z, hz, rfl⟩, r, s, hr, hs, hrs, rfl⟩ :=
      mem_convexJoin.mp hy
    refine ⟨r • x + s • z, ?_, by simp only [map_add, map_smul]⟩
    exact mem_convexJoin.mpr ⟨x, hx, z, hz, r, s, hr, hs, hrs, rfl⟩

theorem mixedVolume_pair_frame {d : ℕ} (T : E ≃L[ℝ] F) (K A C : ConvexBody E) :
    mixedVolume μ (Fin.cons A (Fin.cons C (fun _ : Fin d => K))) =
      (mixedVolumeFrameFactor μ ν T : ℝ) *
        mixedVolume ν (Fin.cons (mapBody T.toContinuousLinearMap A)
          (Fin.cons (mapBody T.toContinuousLinearMap C)
            (fun _ : Fin d => mapBody T.toContinuousLinearMap K))) := by
  have h := mixedVolume_eq_frameFactor_mul μ ν T
    (Fin.cons A (Fin.cons C (fun _ : Fin d => K)))
  convert h using 1
  congr 2
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i

/-- Norm-independent transfer of the actual weak pairing conclusion. -/
theorem weakHullReference_of_frame {d : ℕ}
    (T : E ≃L[ℝ] F) (K : ConvexBody E)
    (h : WeakHullReference ν (d := d) (mapBody T.toContinuousLinearMap K)) :
    WeakHullReference μ (d := d) K := by
  intro A C a ha hAA hAC hCC
  let factor : ℝ := mixedVolumeFrameFactor μ ν T
  have hf : 0 < factor := NNReal.coe_pos.mpr (mixedVolumeFrameFactor_pos μ ν T)
  have heq (X Y : ConvexBody E)
      (hXY : mixedVolume μ (Fin.cons X (Fin.cons Y (fun _ : Fin d => K))) = a) :
      mixedVolume ν (Fin.cons (mapBody T.toContinuousLinearMap X)
        (Fin.cons (mapBody T.toContinuousLinearMap Y)
          (fun _ : Fin d => mapBody T.toContinuousLinearMap K))) = a / factor := by
    apply (eq_div_iff hf.ne').mpr
    rw [mul_comm]
    exact (mixedVolume_pair_frame μ ν T K X Y).symm.trans hXY
  obtain ⟨v, hv⟩ := h (mapBody T.toContinuousLinearMap A)
    (mapBody T.toContinuousLinearMap C) (a / factor) (div_pos ha hf)
    (heq A A hAA) (heq A C hAC) (heq C C hCC)
  refine ⟨T.symm v, ?_⟩
  rw [mixedVolume_pair_frame μ ν T K,
    mixedVolume_pair_frame μ ν T K, mapBody_join, mapBody_translate]
  simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
    using congrArg (fun x : ℝ => factor * x) hv

end Frame

section Strong
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

/-- The weak scalar pairing theorem suffices for exactly the strong segment
area statement used in Proposition 4.2. -/
theorem segmentAreaRigidity_of_weakHullReference {d : ℕ}
    (K : ConvexBody E) (hdim : finrank ℝ E = d + 2)
    (hK : 0 < volume.real (K : Set E))
    (hweak : WeakHullReference volume (d := d) K) :
    SegmentAreaRigidity K hdim := by
  intro A C a ha hAA hAC hCC
  obtain ⟨t, ht⟩ := hweak A C a ha hAA hAC hCC
  have hAC' : mixedVolume volume
      (Fin.cons A (Fin.cons (translateBody t C) (fun _ : Fin d => K))) = a := by
    rw [mixedVolume_translate_second]
    exact hAC
  have hCC' : mixedVolume volume
      (Fin.cons (translateBody t C)
        (Fin.cons (translateBody t C) (fun _ : Fin d => K))) = a := by
    rw [mixedVolume_translate_head, mixedVolume_translate_second]
    exact hCC
  have hKK : 0 < mixedVolume volume
      (Fin.cons K (Fin.cons K (fun _ : Fin d => K))) := by
    simpa only [MultilinearDiagonal.cons_const, mixedVolume_diagonal volume hdim] using hK
  have hstrong := support_equality_of_hull_reference_pairing volume
    (fun _ : Fin d => K) hdim A (translateBody t C) K a ha hAA hAC' hCC' hKK ht
  refine ⟨t, ?_⟩
  intro v
  filter_upwards [Measure.support_mem_ae
    (μ := mixedAreaMeasure volume (Fin.cons (centeredSegment v) (fun _ : Fin d => K)) hdim)]
    with u hu
  have he := hstrong (centeredSegment v) u hu
  rw [translateBody, supportContinuous_add, ContinuousMap.add_apply,
    supportContinuous_point] at he
  linarith

/-- Interior supplies the required positive actual volume. -/
theorem segmentAreaRigidity_of_weakHullReference_of_interior {d : ℕ}
    (K : ConvexBody E) (hdim : finrank ℝ E = d + 2)
    (hK : (interior (K : Set E)).Nonempty)
    (hweak : WeakHullReference volume (d := d) K) :
    SegmentAreaRigidity K hdim := by
  apply segmentAreaRigidity_of_weakHullReference K hdim _ hweak
  exact ENNReal.toReal_pos
    (Measure.measure_pos_of_nonempty_interior volume hK).ne' K.isCompact.measure_lt_top.ne

end Strong
end RankThreeProjection.Rigidity

