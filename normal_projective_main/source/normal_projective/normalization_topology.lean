module
public import normal_projective.unit_normalization
public import Mathlib.Topology.Order
/-! # Continuity and invariance of the canonical normalization -/
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace NormalProjective.UnitNormalization
variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem presentation_ext {P Q : CanonicalModel.Presentation d ι}
    (hn : P.normal = Q.normal) (hh : P.support = Q.support) : P = Q := by
  cases P
  cases Q
  cases hn
  cases hh
  rfl

@[simp] theorem coefficients_smul (r : ℝ) (f : Space d →L[ℝ] ℝ) :
    coefficients (r • f) = r • coefficients f := by
  ext j
  rfl

theorem length_nonneg (f : Space d →L[ℝ] ℝ) : 0 ≤ length f :=
  Real.sqrt_nonneg _

theorem length_pos_smul (r : ℝ) (hr : 0 < r) (f : Space d →L[ℝ] ℝ) :
    length (r • f) = r * length f := by
  have hs : length (r • f) ^ 2 = (r * length f) ^ 2 := by
    rw [length_sq, mul_pow, length_sq]
    simp only [coefficients_smul, Pi.smul_apply, smul_eq_mul, mul_pow,
      Finset.mul_sum]
  have ha := length_nonneg (r • f)
  have hb := mul_nonneg hr.le (length_nonneg f)
  nlinarith

theorem unitRow_pos_smul (r : ℝ) (hr : 0 < r) (f : Space d →L[ℝ] ℝ) :
    unitRow (r • f) = unitRow f := by
  ext j
  simp only [unitRow, coefficients_smul, Pi.smul_apply, smul_eq_mul,
    length_pos_smul r hr, mul_div_mul_left _ _ (ne_of_gt hr)]

/-- Positive rescaling of displayed inequalities changes neither the carrier nor
the canonical labelled presentation. -/
theorem presentation_eq_of_positive_rows (p q : RegularData d ι) (r : ι → ℝ)
    (hr : ∀ i, 0 < r i)
    (hf : ∀ i, q.data.1 i = r i • p.data.1 i)
    (hh : ∀ i, q.data.2 i = r i * p.data.2 i) :
    presentation q = presentation p := by
  apply presentation_ext
  · funext i
    change unitRow (q.data.1 i) = unitRow (p.data.1 i)
    rw [hf, unitRow_pos_smul _ (hr i)]
  · funext i
    change q.data.2 i / length (q.data.1 i) = p.data.2 i / length (p.data.1 i)
    rw [hf, hh, length_pos_smul _ (hr i)]
    exact mul_div_mul_left _ _ (ne_of_gt (hr i))

theorem continuous_rowForm :
    Continuous (rowForm : Space d → (Space d →L[ℝ] ℝ)) := by
  unfold rowForm
  exact continuous_finsetSum _ (fun j _ => (continuous_apply j).smul continuous_const)

theorem continuous_coefficients :
    Continuous (coefficients : (Space d →L[ℝ] ℝ) → Space d) := by
  apply continuous_pi
  intro j
  exact continuous_id.clm_apply continuous_const

theorem continuous_length :
    Continuous (length : (Space d →L[ℝ] ℝ) → ℝ) := by
  unfold length
  apply Real.continuous_sqrt.comp
  exact continuous_finsetSum _ (fun j _ =>
    ((continuous_apply j).comp continuous_coefficients).pow 2)

theorem continuousAt_unitRow (f : Space d →L[ℝ] ℝ) (hf : f ≠ 0) :
    ContinuousAt unitRow f := by
  apply continuousAt_pi.mpr
  intro j
  exact ((continuous_apply j).comp continuous_coefficients).continuousAt.div
    continuous_length.continuousAt (ne_of_gt (length_pos f hf))

instance : TopologicalSpace (RegularData d ι) :=
  TopologicalSpace.induced RegularData.data inferInstance

theorem continuous_data : Continuous (RegularData.data : RegularData d ι →
    HalfspaceData ι (Space d)) := continuous_induced_dom

theorem continuous_presentation :
    Continuous (presentation : RegularData d ι → CanonicalModel.Presentation d ι) := by
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk
  · apply continuous_iff_continuousAt.mpr
    intro p
    apply continuousAt_pi.mpr
    intro i
    exact ContinuousAt.comp (f := fun q : RegularData d ι => q.data.1 i) (x := p)
      (continuousAt_unitRow _ (p.normal_ne_zero i))
      ((continuous_apply i).comp continuous_data.fst).continuousAt
  · apply continuous_pi
    intro i
    apply Continuous.div
    · exact (continuous_apply i).comp continuous_data.snd
    · exact continuous_length.comp ((continuous_apply i).comp continuous_data.fst)
    · exact fun p => ne_of_gt (length_pos _ (p.normal_ne_zero i))

theorem continuous_ofCanonical :
    Continuous (ofCanonical : CanonicalModel.Presentation d ι → RegularData d ι) := by
  apply continuous_induced_rng.mpr
  have hcoord : Continuous (fun P : CanonicalModel.Presentation d ι =>
      (P.normal, P.support)) := continuous_induced_dom
  have hn : Continuous (fun P : CanonicalModel.Presentation d ι =>
      fun i => rowForm (P.normal i)) := by
    apply continuous_pi
    intro i
    exact continuous_rowForm.comp ((continuous_apply i).comp hcoord.fst)
  exact hn.prodMk hcoord.snd

end NormalProjective.UnitNormalization

