module

public import mixed_volume.general.projected_forcing
public import mixed_volume.general.planar_restriction

/-! Every normalization test and base-polynomial identity is extracted from
the literal full signed-substitution cubic. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.GeneralTargetTests

open VolumePolynomials AutomatonWords GeneralLabels GeneralCalibration GeneralNormalization
open CanonicalGeometry GeneralTarget GeneralForcing PlanarRestriction
open Set
open scoped BigOperators Pointwise

variable {s m : ℕ}

@[simp] theorem ref_ne_deficit (r : Reference s) : (ref r : Label s m) ≠ deficitLabel := by
  simp [ref,deficitLabel]
@[simp] theorem axis_ne_deficit (i : Fin 3) : (axisLabel i : Label s m) ≠ deficitLabel := by
  exact ref_ne_deficit _
@[simp] theorem letter_ne_deficit (a : Fin s) : (letterLabel a : Label s m) ≠ deficitLabel := by
  exact ref_ne_deficit _
@[simp] theorem identity_ne_deficit : (identityLabel : Label s m) ≠ deficitLabel := by
  exact ref_ne_deficit _
@[simp] theorem state_ne_deficit (j : Fin m) : (stateLabel j : Label s m) ≠ deficitLabel := by
  simp [stateLabel,deficitLabel]
@[simp] theorem image_ne_deficit (a : Fin s) (j : Fin m) : (imageLabel a j : Label s m) ≠ deficitLabel := by
  simp [imageLabel,deficitLabel]

theorem unitWeight_deficit (i : Label s m) (hi : i ≠ deficitLabel) :
    unitWeight i deficitLabel = 0 := by simp [unitWeight,Pi.single_apply,Ne.symm hi]

theorem sumBody_triple (K : Label s m → Body 3) (i j k : Label s m) :
    sumBody K (unitWeight i + unitWeight j + unitWeight k) = K i + K j + K k := by
  rw [sumBody_add K (unitWeight i + unitWeight j) (unitWeight k)
    (fun l => add_nonneg (unitWeight_nonneg i l) (unitWeight_nonneg j l)) (unitWeight_nonneg k),
    sumBody_add K (unitWeight i) (unitWeight j) (unitWeight_nonneg i) (unitWeight_nonneg j)]
  simp only [sumBody_unit]

theorem _root_.MixedVolume.GeneralForcing.BaseSameVolume.pair {K L : Label s m → Body 3} (h : BaseSameVolume K L)
    (i j : Label s m) (hi : i ≠ deficitLabel) (hj : j ≠ deficitLabel) :
    bodyVolume (K i + K j) = bodyVolume (L i + L j) := by
  have hh := h (unitWeight i + unitWeight j)
    (fun k => add_nonneg (unitWeight_nonneg i k) (unitWeight_nonneg j k))
    (by simp only [Pi.add_apply,unitWeight_deficit i hi,unitWeight_deficit j hj,add_zero])
  simpa only [sumBody_add _ _ _ (unitWeight_nonneg i) (unitWeight_nonneg j),sumBody_unit] using hh

theorem _root_.MixedVolume.GeneralForcing.BaseSameVolume.triple {K L : Label s m → Body 3} (h : BaseSameVolume K L)
    (i j k : Label s m) (hi : i ≠ deficitLabel) (hj : j ≠ deficitLabel) (hk : k ≠ deficitLabel) :
    bodyVolume (K i + K j + K k) = bodyVolume (L i + L j + L k) := by
  have hh := h (unitWeight i + unitWeight j + unitWeight k)
    (fun l => add_nonneg (add_nonneg (unitWeight_nonneg i l) (unitWeight_nonneg j l)) (unitWeight_nonneg k l))
    (by simp only [Pi.add_apply,unitWeight_deficit i hi,unitWeight_deficit j hj,unitWeight_deficit k hk,add_zero])
  simpa only [sumBody_triple] using hh

theorem target_base {A : Data s m} {hs : 0 < s} {δ : Fin m → ℝ} {K : Label s m → Body 3}
    (h : RealizesTarget A hs δ K) : BaseSameVolume K (canonical A hs) := by
  intro w hw hz
  rw [← h w hw,targetPolynomial_eval,shiftWeight_zero_deficit δ w hz,indexedPolynomial_eval _ _ hw]

theorem target_tests {A : Data s m} {hs : 0 < s} {δ : Fin m → ℝ} {K : Label s m → Body 3}
    (h : RealizesTarget A hs δ K) : Tests hs K := by
  have hb := target_base h
  have hc := canonical_tests A hs
  constructor
  · intro r j
    rw [hb.pair _ _ (by simp) (by simp)]
    exact hc.segmentZero r j
  · rw [hb.triple _ _ _ (by simp) (by simp) (by simp)]
    exact hc.frameVolume
  · intro a
    rw [hb.triple _ _ _ (by simp) (by simp) (by simp)]
    exact hc.letterX a
  · intro a
    rw [hb.triple _ _ _ (by simp) (by simp) (by simp)]
    exact hc.letterY a
  · intro a
    rw [hb.triple _ _ _ (by simp) (by simp) (by simp)]
    exact hc.letterZ a
  · rw [hb.triple _ _ _ (by simp) (by simp) (by simp)]
    exact hc.identityX
  · rw [hb.triple _ _ _ (by simp) (by simp) (by simp)]
    exact hc.identityY
  · rw [hb.triple _ _ _ (by simp) (by simp) (by simp)]
    exact hc.identityZ
  · intro a
    rw [hb.triple _ _ _ (by simp) (by simp) (by simp)]
    exact hc.verticalPair a
  · intro a
    rw [hb.triple _ _ _ (by simp) (by simp) (by simp)]
    exact hc.horizontalPair a
  · intro j
    rw [hb.triple _ _ _ (by simp) (by simp) (by simp)]
    exact hc.statePlane j
  · intro a j
    rw [hb.triple _ _ _ (by simp) (by simp) (by simp)]
    exact hc.imagePlane a j
  · have hh := h (unitWeight deficitLabel + unitWeight (axisLabel 0) + unitWeight (axisLabel 2))
      (fun i => add_nonneg (add_nonneg (unitWeight_nonneg _ i) (unitWeight_nonneg _ i))
        (unitWeight_nonneg _ i))
    rw [target_deficit_plane,sumBody_triple] at hh
    exact hh.symm

/-- Starting with an entirely arbitrary realizing tuple, the full target
coefficient identity supplies all normalizations and canonical state bodies. -/
theorem normalize_target {A : Data s m} {hs : 0 < s} {δ : Fin m → ℝ} {K : Label s m → Body 3}
    (h : RealizesTarget A hs δ K) :
    ∃ L : Label s m → Body 3, RealizesTarget A hs δ L ∧ Calibrated L ∧
      ∃ t : Fin m → AutomatonWords.Plane, ∀ j,
        state L j = translateBody (t j) (AutomatonZonoids.stateBody A hs j) := by
  obtain ⟨L,hL,hcal⟩ := normalize_references hs K (target_tests h)
  have ht := h.of_sameVolume hL
  exact ⟨L,ht,hcal,states_forced A hs (target_base ht) hcal⟩

end MixedVolume.GeneralTargetTests

end
