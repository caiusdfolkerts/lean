module

public import Projection.Topology
public import Projection.SegmentSeminorm
public import VolumePolynomials.ProjectionMixedVolumeTransport
public import Mathlib.MeasureTheory.Group.Prod

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace RankThreeProjection
open VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The shear fixes the hyperplane `{0} × E` pointwise. -/
def hyperplaneShear (v : E) : (ℝ × E) ≃L[ℝ] (ℝ × E) where
  toFun p := (p.1, p.2 - p.1 • v)
  invFun p := (p.1, p.2 + p.1 • v)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  map_add' p q := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, add_smul] <;> abel
  map_smul' r p := by
    ext <;> simp [smul_sub, smul_smul]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem hyperplaneShear_apply (v : E) (p : ℝ × E) :
    hyperplaneShear v p = (p.1, p.2 - p.1 • v) := rfl

def embedHyperplane (K : ConvexBody E) : ConvexBody (ℝ × E) :=
  mapBody (ContinuousLinearMap.inr ℝ ℝ E) K

@[simp] theorem shear_embedHyperplane (v : E) (K : ConvexBody E) :
    mapBody (hyperplaneShear v).toContinuousLinearMap (embedHyperplane K) =
      embedHyperplane K := by
  rw [embedHyperplane, mapBody_comp]
  congr 1
  apply ContinuousLinearMap.ext
  intro x
  change (0, x - (0 : ℝ) • v) = (0, x)
  simp

@[simp] theorem project_embedHyperplane (K : ConvexBody E) :
    mapBody (ContinuousLinearMap.snd ℝ ℝ E) (embedHyperplane K) = K := by
  rw [embedHyperplane, mapBody_comp]
  have he : (ContinuousLinearMap.snd ℝ ℝ E).comp
      (ContinuousLinearMap.inr ℝ ℝ E) = ContinuousLinearMap.id ℝ E := by ext; rfl
  rw [he]
  apply ConvexBody.ext
  exact Set.image_id _

theorem axisBody_eq_originSegment :
    (axisBody : ConvexBody (ℝ × E)) = originSegment (1, 0) := by
  apply ConvexBody.ext
  ext p
  change p ∈ Set.Icc (0 : ℝ) 1 ×ˢ ({0} : Set E) ↔
    p ∈ segment ℝ (0 : ℝ × E) (1, 0)
  rw [segment_eq_image]
  constructor
  · rintro ⟨hp, hp0⟩
    refine ⟨p.1, hp, ?_⟩
    ext <;> simpa using hp0.symm
  · rintro ⟨t, ht, rfl⟩
    simpa using ht

section Measure
variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

set_option backward.isDefEq.respectTransparency false in
/-- Fubini and translation invariance prove that the shear preserves the
actual product volume; no determinant value is assumed. -/
theorem hyperplaneShear_measurePreserving (v : E) :
    MeasurePreserving (hyperplaneShear v) volume volume := by
  have h := (MeasurePreserving.id (volume : Measure ℝ)).skew_product
    (g := fun t : ℝ => fun x : E => x - t • v)
    (by fun_prop) (Filter.Eventually.of_forall (fun t => by
      simpa only [sub_eq_add_neg] using
        (measurePreserving_add_right (volume : Measure E) (-(t • v))).map_eq))
  change MeasurePreserving (fun p : ℝ × E => (p.1, p.2 - p.1 • v))
    ((volume : Measure ℝ).prod (volume : Measure E))
    ((volume : Measure ℝ).prod (volume : Measure E))
  simpa only [id_eq] using h

theorem mixedVolume_translate_first {d : ℕ} (K : Fin d → ConvexBody E)
    (A : ConvexBody E) (v : E) :
    mixedVolume volume (Fin.cons (translateBody v A) K) =
      mixedVolume volume (Fin.cons A K) := by
  have h := mixedVolume_translate volume (Fin.cons A K) (Fin.cons v (fun _ => 0))
  convert h using 1
  congr 1
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  simp only [Fin.cons_succ, translateBody_zero]

theorem mixedVolume_first_smul {d : ℕ} (K : Fin d → ConvexBody E)
    (A : ConvexBody E) {r : ℝ} (hr : 0 ≤ r) :
    mixedVolume volume (Fin.cons (r • A) K) =
      r * mixedVolume volume (Fin.cons A K) := by
  simpa only [Fin.update_cons_zero] using
    mixedVolume_smul volume (Fin.cons A K) 0 A hr

/-- Centered and origin-based normal segments give the same extrusion. -/
theorem mixedVolume_centered_axis {d : ℕ} (K : Fin d → ConvexBody (ℝ × E)) :
    (d + 1 : ℝ) * mixedVolume volume (Fin.cons (centeredSegment (1, 0)) K) =
      mixedVolume volume (fun i => mapBody (ContinuousLinearMap.snd ℝ ℝ E) (K i)) := by
  rw [centered_eq_translate_origin, mixedVolume_translate_first,
    ← axisBody_eq_originSegment]
  exact mixedVolume_axis K

/-- The actual mixed volume with two marked segments and a body contained
in the coordinate hyperplane. The number `d` counts the repeated copies. -/
def hyperplanePair {d : ℕ} (K : ConvexBody E) (u v : ℝ × E) : ℝ :=
  mixedVolume volume (Fin.cons (centeredSegment u)
    (Fin.cons (centeredSegment v) (fun _ : Fin d => embedHyperplane K)))

theorem hyperplanePair_shear {d : ℕ} (K : ConvexBody E) (u v : ℝ × E) (a : E) :
    hyperplanePair (d := d) K (hyperplaneShear a u) (hyperplaneShear a v) =
      hyperplanePair (d := d) K u v := by
  have h := mixedVolume_map_measurePreserving volume volume (hyperplaneShear a)
    (hyperplaneShear_measurePreserving a)
    (Fin.cons (centeredSegment u)
      (Fin.cons (centeredSegment v) (fun _ : Fin d => embedHyperplane K)))
  unfold hyperplanePair
  convert h using 1
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.cons_zero, ContinuousLinearEquiv.coe_coe] using
      (map_centeredSegment (hyperplaneShear a).toContinuousLinearMap u).symm
  · refine Fin.cases ?_ (fun k => ?_) j
    · simpa only [Fin.cons_succ, Fin.cons_zero, ContinuousLinearEquiv.coe_coe] using
        (map_centeredSegment (hyperplaneShear a).toContinuousLinearMap v).symm
    · simpa only [Fin.cons_succ] using (shear_embedHyperplane a K).symm

theorem hyperplanePair_normal {d : ℕ} (K : ConvexBody E) (α β : ℝ) (b : E) :
    (d + 2 : ℝ) * hyperplanePair (d := d) K (α, 0) (β, b) =
      |α| * mixedVolume volume (Fin.cons (centeredSegment b) (fun _ : Fin d => K)) := by
  have he : (α, (0 : E)) = α • (1, (0 : E)) := by ext <;> simp
  rw [hyperplanePair, he, centeredSegment_abs_smul,
    mixedVolume_first_smul _ _ (abs_nonneg α)]
  rw [← mul_assoc, mul_comm (d + 2 : ℝ) |α|, mul_assoc,
    show (d + 2 : ℝ) = ((d + 1 : ℕ) + 1 : ℝ) by
      simp only [Nat.cast_add, Nat.cast_one]; ring,
    mixedVolume_centered_axis]
  congr 2
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact map_centeredSegment _ _
  · exact project_embedHyperplane K

/-- The shear calculation when the first normal component is nonzero. -/
theorem hyperplanePair_formula_of_ne_zero {d : ℕ} (K : ConvexBody E)
    (α β : ℝ) (a b : E) (hα : α ≠ 0) :
    (d + 2 : ℝ) * hyperplanePair (d := d) K (α, a) (β, b) =
      mixedVolume volume
        (Fin.cons (centeredSegment (α • b - β • a)) (fun _ : Fin d => K)) := by
  have hu : hyperplaneShear (α⁻¹ • a) (α, a) = (α, 0) := by
    simp [hyperplaneShear, smul_smul, hα]
  have hv : hyperplaneShear (α⁻¹ • a) (β, b) = (β, b - (β / α) • a) := by
    simp [hyperplaneShear, smul_smul, div_eq_mul_inv]
  rw [← hyperplanePair_shear K (α, a) (β, b) (α⁻¹ • a), hu, hv,
    hyperplanePair_normal]
  have he : α • b - β • a = α • (b - (β / α) • a) := by
    rw [smul_sub, smul_smul]
    congr 1
    field_simp
  rw [he, centeredSegment_abs_smul, mixedVolume_first_smul _ _ (abs_nonneg α)]

/-- The formula extends continuously to zero normal components. This
includes bodies and marks of every dimension. -/
theorem hyperplanePair_formula {d : ℕ} (K : ConvexBody E)
    (α β : ℝ) (a b : E) :
    (d + 2 : ℝ) * hyperplanePair (d := d) K (α, a) (β, b) =
      mixedVolume volume
        (Fin.cons (centeredSegment (α • b - β • a)) (fun _ : Fin d => K)) := by
  let f : ℝ → ℝ := fun t => (d + 2 : ℝ) * hyperplanePair (d := d) K (t, a) (β, b)
  let g : ℝ → ℝ := fun t => mixedVolume volume
    (Fin.cons (centeredSegment (t • b - β • a)) (fun _ : Fin d => K))
  have hf : Continuous f := by
    apply Continuous.const_mul
    apply (continuous_mixedVolume volume (d + 1 + 1)).comp
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_centeredSegment.comp (continuous_id.prodMk continuous_const)
    · exact continuous_const
  have hg : Continuous g := by
    apply (continuous_mixedVolume volume (d + 1)).comp
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_centeredSegment.comp (by fun_prop)
    · exact continuous_const
  have he : f = g := Continuous.ext_on (dense_compl_singleton (0 : ℝ)) hf hg (by
    intro t ht
    exact hyperplanePair_formula_of_ne_zero K t β a b ht)
  exact congrFun he α

/-- Lemma 5.1 in a product frame, with the paper's exact normalization. -/
theorem hyperplanePair_eq_seminorm {d : ℕ} [Nontrivial E]
    (K : ConvexBody E) (hdim : finrank ℝ E = d + 1) (u v : ℝ × E) :
    (d + 2 : ℝ) * (d + 1 : ℝ) * hyperplanePair (d := d) K u v =
      segmentMixedVolumeSeminorm volume (fun _ : Fin d => K) hdim
        (u.1 • v.2 - v.1 • u.2) := by
  rw [segmentMixedVolumeSeminorm_apply, ← hyperplanePair_formula K u.1 v.1 u.2 v.2]
  ring

end Measure
end RankThreeProjection
