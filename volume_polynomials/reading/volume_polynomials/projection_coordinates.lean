module

public import VolumePolynomials.HolonomyCoordinates
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp

@[expose] public section
noncomputable section

open MeasureTheory

namespace VolumePolynomials.Holonomy

abbrev ThreeSpace := Fin 3 → ℝ

def directionV : ThreeSpace := ![0, 1, 1]
def directionW : ThreeSpace := ![1, 1, 0]
def directionZ : ThreeSpace := ![1, (2 / 3 : ℝ), 1]

/-- Extract one coordinate, retaining the other two in their original order. -/
def coordinateExtract (i : Fin 3) : ThreeSpace ≃ₗ[ℝ] ℝ × Plane where
  toEquiv := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) i).toEquiv.trans
    (Equiv.prodCongr (Equiv.refl ℝ) (finTwoArrowEquiv ℝ))
  map_add' x y := by ext <;> rfl
  map_smul' c x := by ext <;> rfl

@[simp] theorem coordinateExtract_apply (i : Fin 3) (x : ThreeSpace) :
    coordinateExtract i x = (x i, (x (i.succAbove 0), x (i.succAbove 1))) := rfl

theorem coordinateExtract_measurePreserving (i : Fin 3) :
    MeasurePreserving (coordinateExtract i) volume volume := by
  first
  | have h₁ := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) i
    have h₂ : MeasurePreserving
        (Prod.map (id : ℝ → ℝ) (@MeasurableEquiv.finTwoArrow ℝ _)) volume volume :=
      (MeasurePreserving.id (volume : Measure ℝ)).prod (volume_preserving_finTwoArrow ℝ)
    exact h₂.comp h₁

/-- A shear that subtracts a fixed multiple of the extracted coordinate. -/
def projectionShear (u : Plane) : (ℝ × Plane) ≃ₗ[ℝ] ℝ × Plane where
  toFun p := (p.1, p.2 - p.1 • u)
  invFun p := (p.1, p.2 + p.1 • u)
  left_inv p := by simp
  right_inv p := by simp
  map_add' p q := by ext <;> dsimp <;> ring
  map_smul' c p := by ext <;> dsimp <;> ring

@[simp] theorem projectionShear_apply (u : Plane) (p : ℝ × Plane) :
    projectionShear u p = (p.1, p.2 - p.1 • u) := rfl

/-- Product-measure invariance of the shear follows directly from translation
invariance of each planar fiber.  No determinant convention across different
coordinate types is assumed. -/
theorem projectionShear_measurePreserving (u : Plane) :
    MeasurePreserving (projectionShear u) volume volume := by
  first
  | haveI : Measure.IsAddLeftInvariant (volume : Measure Plane) := by
      change Measure.IsAddLeftInvariant ((volume : Measure ℝ).prod (volume : Measure ℝ))
      infer_instance
    change MeasurePreserving (fun p : ℝ × Plane => (p.1, p.2 - p.1 • u)) volume volume
    simp only [Measure.volume_eq_prod ℝ Plane]
    have hm : Measurable
        (Function.uncurry (fun (t : ℝ) (p : Plane) => -(t • u) + p)) := by
      exact ((continuous_fst.smul continuous_const).neg.add continuous_snd).measurable
    have ht : ∀ᵐ t ∂(volume : Measure ℝ),
        Measure.map (fun p : Plane => -(t • u) + p) volume = volume :=
      Filter.Eventually.of_forall (fun t => map_add_left_eq_self (volume : Measure Plane) (-(t • u)))
    simpa only [id_eq, sub_eq_add_neg, add_comm] using
      (MeasurePreserving.id (volume : Measure ℝ)).skew_product hm ht

def projectionFrame (i : Fin 3) (u : Plane) : ThreeSpace ≃L[ℝ] ℝ × Plane :=
  ((coordinateExtract i).trans (projectionShear u)).toContinuousLinearEquiv

@[simp] theorem projectionFrame_apply (i : Fin 3) (u : Plane) (x : ThreeSpace) :
    projectionFrame i u x =
      (x i, (x (i.succAbove 0), x (i.succAbove 1)) - x i • u) := rfl

theorem projectionFrame_measurePreserving (i : Fin 3) (u : Plane) :
    MeasurePreserving (projectionFrame i u) volume volume :=
  (projectionShear_measurePreserving u).comp (coordinateExtract_measurePreserving i)

theorem transport01_measurePreserving : MeasurePreserving transport01 volume volume := by
  first
  | exact (MeasurePreserving.id (volume : Measure ℝ)).prod
      (Measure.measurePreserving_neg (volume : Measure ℝ))

theorem transport12_measurePreserving : MeasurePreserving transport12 volume volume := by
  first
  | exact (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
      (MeasurePreserving.id (volume : Measure ℝ))

@[simp] theorem area_transport01 (A : Set Plane) :
    volume.real (transport01 '' A) = volume.real A := by
  first
  | have h := transport01_measurePreserving.measure_preimage_emb
      transport01.toHomeomorph.measurableEmbedding (transport01 '' A)
    rw [Set.preimage_image_eq A transport01.injective] at h
    simpa only [measureReal_def] using congrArg ENNReal.toReal h.symm

@[simp] theorem area_transport12 (A : Set Plane) :
    volume.real (transport12 '' A) = volume.real A := by
  first
  | have h := transport12_measurePreserving.measure_preimage_emb
      transport12.toHomeomorph.measurableEmbedding (transport12 '' A)
    rw [Set.preimage_image_eq A transport12.injective] at h
    simpa only [measureReal_def] using congrArg ENNReal.toReal h.symm

def frameV : ThreeSpace ≃L[ℝ] ℝ × Plane := projectionFrame 2 (0, 1)
def frameW : ThreeSpace ≃L[ℝ] ℝ × Plane := projectionFrame 1 (1, 0)
def frameZ : ThreeSpace ≃L[ℝ] ℝ × Plane := projectionFrame 2 (1, (2 / 3 : ℝ))

@[simp] theorem frameV_apply (x : ThreeSpace) :
    frameV x = (x 2, (x 0, x 1 - x 2)) := by
  first
  | simp [frameV, projectionFrame_apply,
      show (2 : Fin 3).succAbove (1 : Fin 2) = 1 by decide]

@[simp] theorem frameW_apply (x : ThreeSpace) :
    frameW x = (x 1, (x 0 - x 1, x 2)) := by
  first
  | simp [frameW, projectionFrame_apply]

@[simp] theorem frameZ_apply (x : ThreeSpace) :
    frameZ x = (x 2, (x 0 - x 2, x 1 - (2 / 3 : ℝ) * x 2)) := by
  first
  | simp [frameZ, projectionFrame_apply, mul_comm,
      show (2 : Fin 3).succAbove (1 : Fin 2) = 1 by decide]

theorem frameV_measurePreserving : MeasurePreserving frameV volume volume :=
  projectionFrame_measurePreserving 2 (0, 1)

theorem frameW_measurePreserving : MeasurePreserving frameW volume volume :=
  projectionFrame_measurePreserving 1 (1, 0)

theorem frameZ_measurePreserving : MeasurePreserving frameZ volume volume :=
  projectionFrame_measurePreserving 2 (1, (2 / 3 : ℝ))

@[simp] theorem frameV_direction : frameV directionV = (1, 0) := by
  first
  | norm_num [frameV_apply, directionV]

@[simp] theorem frameW_direction : frameW directionW = (1, 0) := by
  first
  | norm_num [frameW_apply, directionW]

@[simp] theorem frameZ_direction : frameZ directionZ = (1, 0) := by
  first
  | norm_num [frameZ_apply, directionZ]

def projectionV : ThreeSpace →L[ℝ] Plane :=
  (ContinuousLinearMap.snd ℝ ℝ Plane).comp frameV.toContinuousLinearMap

def projectionW : ThreeSpace →L[ℝ] Plane :=
  (ContinuousLinearMap.snd ℝ ℝ Plane).comp frameW.toContinuousLinearMap

def projectionZ : ThreeSpace →L[ℝ] Plane :=
  (ContinuousLinearMap.snd ℝ ℝ Plane).comp frameZ.toContinuousLinearMap

@[simp] theorem projectionV_apply (x : ThreeSpace) :
    projectionV x = (x 0, x 1 - x 2) := by simp [projectionV]

@[simp] theorem projectionW_apply (x : ThreeSpace) :
    projectionW x = (x 0 - x 1, x 2) := by simp [projectionW]

@[simp] theorem projectionZ_apply (x : ThreeSpace) :
    projectionZ x = (x 0 - x 2, x 1 - (2 / 3 : ℝ) * x 2) := by simp [projectionZ]

def embedXY : Plane →L[ℝ] ThreeSpace where
  toFun p := ![p.1, p.2, 0]
  map_add' p q := by ext i; fin_cases i <;> simp
  map_smul' c p := by ext i; fin_cases i <;> simp
  cont := by apply continuous_pi; intro i; fin_cases i <;> fun_prop

def embedXZ : Plane →L[ℝ] ThreeSpace where
  toFun p := ![p.1, 0, p.2]
  map_add' p q := by ext i; fin_cases i <;> simp
  map_smul' c p := by ext i; fin_cases i <;> simp
  cont := by apply continuous_pi; intro i; fin_cases i <;> fun_prop

def embedYZ : Plane →L[ℝ] ThreeSpace where
  toFun p := ![0, p.1, p.2]
  map_add' p q := by ext i; fin_cases i <;> simp
  map_smul' c p := by ext i; fin_cases i <;> simp
  cont := by apply continuous_pi; intro i; fin_cases i <;> fun_prop

@[simp] theorem projectionV_embedXY (p : Plane) : projectionV (embedXY p) = p := by
  first
  | simp [embedXY]

@[simp] theorem projectionV_embedXZ (p : Plane) :
    projectionV (embedXZ p) = transport01 p := by simp [embedXZ]

@[simp] theorem projectionW_embedXZ (p : Plane) : projectionW (embedXZ p) = p := by
  first
  | simp [embedXZ]

@[simp] theorem projectionW_embedYZ (p : Plane) :
    projectionW (embedYZ p) = transport12 p := by simp [embedYZ]

@[simp] theorem projectionZ_embedXY (p : Plane) : projectionZ (embedXY p) = p := by
  first
  | simp [embedXY]

@[simp] theorem projectionZ_embedYZ (p : Plane) :
    projectionZ (embedYZ p) = transport20 p := by simp [embedYZ]

theorem embedXY_injective : Function.Injective embedXY := by
  first
  | intro p q h
    simpa only [projectionV_embedXY] using congrArg projectionV h

theorem embedXZ_injective : Function.Injective embedXZ := by
  first
  | intro p q h
    simpa only [projectionW_embedXZ] using congrArg projectionW h

theorem embedYZ_injective : Function.Injective embedYZ := by
  first
  | intro p q h
    apply transport12.injective
    simpa only [projectionW_embedYZ] using congrArg projectionW h

theorem range_embedXY : Set.range embedXY = {x : ThreeSpace | x 2 = 0} := by
  first
  | ext x
    constructor
    · rintro ⟨p, rfl⟩
      simp [embedXY]
    · intro hx
      refine ⟨(x 0, x 1), ?_⟩
      ext i
      fin_cases i <;> simp_all [embedXY]

theorem range_embedXZ : Set.range embedXZ = {x : ThreeSpace | x 1 = 0} := by
  first
  | ext x
    constructor
    · rintro ⟨p, rfl⟩
      simp [embedXZ]
    · intro hx
      refine ⟨(x 0, x 2), ?_⟩
      ext i
      fin_cases i <;> simp_all [embedXZ]

theorem range_embedYZ : Set.range embedYZ = {x : ThreeSpace | x 0 = 0} := by
  first
  | ext x
    constructor
    · rintro ⟨p, rfl⟩
      simp [embedYZ]
    · intro hx
      refine ⟨(x 1, x 2), ?_⟩
      ext i
      fin_cases i <;> simp_all [embedYZ]


end VolumePolynomials.Holonomy
