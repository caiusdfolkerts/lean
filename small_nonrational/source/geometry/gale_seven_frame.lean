module

public import GaleSevenCoordinates
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# Normalization of the seven-hyperplane Gale obstruction

Labels are `A,B,D,R,S,F,O,X,Y,Z`, in that order. The four points `B,D,R,S`
span the distinguished hyperplane. An actual independent frame with `O`
provides a linear change of coordinates, and nonzero individual scalings
normalize `X,Y,Z`. Independence of every labelled family is preserved in
both directions; no general-position assumption is introduced.
-/

noncomputable section
namespace Papers.RationalityTen.GaleSevenFrame

open Matrix Set Module
open scoped BigOperators Classical
open GaleSevenCoordinates

def fourSets : Fin 4 → Fin 4 → Fin 10 :=
  ![![0, 1, 2, 3], ![1, 2, 3, 4], ![0, 1, 2, 5], ![0, 3, 4, 5]]

def tripleSets : Fin 3 → Fin 3 → Fin 10 :=
  ![![6, 7, 1], ![8, 9, 2], ![7, 9, 4]]

def hyperplanes : Fin 7 → Fin 5 → Fin 10 :=
  ![![1, 2, 3, 6, 7], ![0, 1, 5, 6, 7], ![1, 2, 3, 8, 9],
    ![0, 2, 5, 8, 9], ![1, 4, 6, 7, 9], ![2, 4, 7, 8, 9],
    ![0, 3, 4, 7, 9]]

theorem fourSets_injective : ∀ i, Function.Injective (fourSets i) := by decide

theorem tripleSets_injective : ∀ i, Function.Injective (tripleSets i) := by decide

theorem hyperplanes_injective : ∀ i, Function.Injective (hyperplanes i) := by decide

def plane (p : Fin 10 → GaleSevenCoordinates.Vector) : Submodule ℝ GaleSevenCoordinates.Vector :=
  Submodule.span ℝ (Set.range (p ∘ fourSets 1))

structure Conditions (p : Fin 10 → GaleSevenCoordinates.Vector) : Prop where
  A_mem : p 0 ∈ plane p
  F_mem : p 5 ∈ plane p
  outside : ∀ i : Fin 4, p (⟨6 + i.val, by omega⟩ : Fin 10) ∉ plane p
  four_independent : ∀ i, LinearIndependent ℝ (p ∘ fourSets i)
  three_independent : ∀ i, LinearIndependent ℝ (p ∘ tripleSets i)
  hyperplane_dependent : ∀ i, ¬ LinearIndependent ℝ (p ∘ hyperplanes i)

def frame (p : Fin 10 → GaleSevenCoordinates.Vector) : Fin 5 → GaleSevenCoordinates.Vector :=
  Fin.snoc (p ∘ fourSets 1) (p 6)

theorem frame_independent (p : Fin 10 → GaleSevenCoordinates.Vector) (h : Conditions p) :
    LinearIndependent ℝ (frame p) := by
  exact (h.four_independent 1).finSnoc (h.outside 0)

def frameBasis (p : Fin 10 → GaleSevenCoordinates.Vector) (h : Conditions p) : Basis (Fin 5) ℝ GaleSevenCoordinates.Vector :=
  basisOfLinearIndependentOfCardEqFinrank (frame_independent p h) (by simp [GaleSevenCoordinates.Vector])

theorem frameBasis_apply (p : Fin 10 → GaleSevenCoordinates.Vector) (h : Conditions p) (i : Fin 5) :
    frameBasis p h i = frame p i := by
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank
    (frame_independent p h) (by simp [GaleSevenCoordinates.Vector])) i

def frameMap (p : Fin 10 → GaleSevenCoordinates.Vector) (h : Conditions p) : GaleSevenCoordinates.Vector ≃ₗ[ℝ] GaleSevenCoordinates.Vector :=
  (frameBasis p h).equivFun

theorem frameMap_frame (p : Fin 10 → GaleSevenCoordinates.Vector) (h : Conditions p) (i : Fin 5) :
    frameMap p h (frame p i) = unitPoint i := by
  rw [← frameBasis_apply p h i]
  ext j
  simpa only [frameMap, unitPoint, Pi.single_apply, eq_comm] using
    (frameBasis p h).equivFun_self i j

theorem plane_le_coordinate_kernel (p : Fin 10 → GaleSevenCoordinates.Vector) (h : Conditions p) :
    plane p ≤ ((LinearMap.proj (4 : Fin 5)).comp (frameMap p h).toLinearMap).ker := by
  apply Submodule.span_le.mpr
  rintro v ⟨i, rfl⟩
  change frameMap p h (p (fourSets 1 i)) 4 = 0
  have heq : p (fourSets 1 i) = frame p i.castSucc := by simp [frame]
  rw [heq, frameMap_frame]
  have hi : (i.castSucc : Fin 5) ≠ 4 := by
    intro heq
    have hv := congrArg Fin.val heq
    change i.val = 4 at hv
    omega
  simp [unitPoint, Pi.single_apply, hi, Ne.symm hi]

/-- Membership in the distinguished plane is exactly vanishing of the
last frame coordinate, including the reverse implication. -/
theorem mem_plane_iff_coordinate_zero (p : Fin 10 → GaleSevenCoordinates.Vector) (h : Conditions p)
    (v : GaleSevenCoordinates.Vector) : v ∈ plane p ↔ frameMap p h v 4 = 0 := by
  constructor
  · exact fun hv => plane_le_coordinate_kernel p h hv
  · intro hv
    have hsum : (∑ i, frameMap p h v i • frame p i) = v := by
      simpa only [frameMap, ← frameBasis_apply p h] using (frameBasis p h).sum_equivFun v
    rw [← hsum]
    apply Submodule.sum_mem
    intro i _
    by_cases hi : i = 4
    · simp [hi, hv]
    · apply Submodule.smul_mem
      have hi' : i.val < 4 := by omega
      let j : Fin 4 := ⟨i.val, hi'⟩
      have hij : i = j.castSucc := Fin.ext rfl
      rw [hij]
      have heq : frame p j.castSucc = p (fourSets 1 j) := by simp [frame]
      rw [heq]
      exact Submodule.subset_span ⟨j, rfl⟩

def scale (p : Fin 10 → GaleSevenCoordinates.Vector) (h : Conditions p) (i : Fin 10) : ℝ :=
  if 7 ≤ i.val then (frameMap p h (p i) 4)⁻¹ else 1

def normalized (p : Fin 10 → GaleSevenCoordinates.Vector) (h : Conditions p) (i : Fin 10) : GaleSevenCoordinates.Vector :=
  scale p h i • frameMap p h (p i)

theorem scale_ne_zero (p : Fin 10 → GaleSevenCoordinates.Vector) (h : Conditions p) (i : Fin 10) :
    scale p h i ≠ 0 := by
  unfold scale
  split_ifs with hi
  · apply inv_ne_zero
    intro hz
    have hmem := (mem_plane_iff_coordinate_zero p h (p i)).mpr hz
    let j : Fin 4 := ⟨i.val - 6, by omega⟩
    have hij : (⟨6 + j.val, by omega⟩ : Fin 10) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    exact h.outside j (hij.symm ▸ hmem)
  · exact one_ne_zero

/-- The normalization preserves independence of every finite indexed
family, including repeated labels and all dimensions. -/
theorem normalized_independent_iff (p : Fin 10 → GaleSevenCoordinates.Vector) (h : Conditions p)
    {m : ℕ} (b : Fin m → Fin 10) :
    LinearIndependent ℝ (normalized p h ∘ b) ↔ LinearIndependent ℝ (p ∘ b) := by
  let u : Fin m → ℝˣ := fun i => Units.mk0 (scale p h (b i)) (scale_ne_zero p h (b i))
  have hu := LinearIndependent.units_smul_iff (R := ℝ)
    (fun i => frameMap p h (p (b i))) u
  have hscale : LinearIndependent ℝ (normalized p h ∘ b) ↔
      LinearIndependent ℝ (fun i => frameMap p h (p (b i))) := by
    simpa only [u, normalized, Function.comp_def, Pi.smul_def',
      Units.smul_def, Units.val_mk0] using hu
  rw [hscale]
  constructor
  · intro hi
    exact LinearIndependent.of_comp (frameMap p h).toLinearMap hi
  · intro hi
    exact hi.map' (frameMap p h).toLinearMap
      (LinearMap.ker_eq_bot.mpr (frameMap p h).injective)

theorem normalized_frame (p : Fin 10 → GaleSevenCoordinates.Vector) (h : Conditions p) :
    normalized p h 1 = unitPoint 0 ∧ normalized p h 2 = unitPoint 1 ∧
    normalized p h 3 = unitPoint 2 ∧ normalized p h 4 = unitPoint 3 ∧
    normalized p h 6 = unitPoint 4 := by
  have h₀ := frameMap_frame p h ((0 : Fin 4).castSucc)
  have h₁ := frameMap_frame p h ((1 : Fin 4).castSucc)
  have h₂ := frameMap_frame p h ((2 : Fin 4).castSucc)
  have h₃ := frameMap_frame p h ((3 : Fin 4).castSucc)
  have h₄ := frameMap_frame p h (Fin.last 4)
  simp only [frame, Fin.snoc_castSucc, Fin.snoc_last, fourSets, Function.comp_def]
    at h₀ h₁ h₂ h₃ h₄
  simpa [normalized, scale] using And.intro h₀ (And.intro h₁ (And.intro h₂ (And.intro h₃ h₄)))

theorem normalized_internal (p : Fin 10 → GaleSevenCoordinates.Vector) (h : Conditions p) :
    normalized p h 0 4 = 0 ∧ normalized p h 5 4 = 0 := by
  have hA := (mem_plane_iff_coordinate_zero p h (p 0)).mp h.A_mem
  have hF := (mem_plane_iff_coordinate_zero p h (p 5)).mp h.F_mem
  simpa [normalized, scale] using And.intro hA hF

theorem normalized_outside (p : Fin 10 → GaleSevenCoordinates.Vector) (h : Conditions p)
    (i : Fin 10) (hi : 7 ≤ i.val) : normalized p h i 4 = 1 := by
  have hz : frameMap p h (p i) 4 ≠ 0 := by
    have hs := scale_ne_zero p h i
    simp only [scale, if_pos hi] at hs
    intro hz
    apply hs
    rw [hz, _root_.inv_zero]
  simp [normalized, scale, hi, hz]

end Papers.RationalityTen.GaleSevenFrame
