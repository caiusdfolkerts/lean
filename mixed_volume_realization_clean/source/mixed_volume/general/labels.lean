module

public import mixed_volume.general.reference_calibration

/-! The literal variable labels of the general cubic construction and finite
Minkowski-sum transport. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.GeneralLabels

open VolumePolynomials VolumePolynomials.Holonomy GeneralCalibration
open scoped Pointwise BigOperators

abbrev Reference (s : ℕ) := Fin 3 ⊕ (Fin s ⊕ Unit)
abbrev Label (s m : ℕ) := Reference s ⊕ (Fin m ⊕ ((Fin s × Fin m) ⊕ Unit))

def ref {s m : ℕ} (r : Reference s) : Label s m := .inl r
def axisRef {s : ℕ} (i : Fin 3) : Reference s := .inl i
def letterRef {s : ℕ} (a : Fin s) : Reference s := .inr (.inl a)
def identityRef {s : ℕ} : Reference s := .inr (.inr ())
def axisLabel {s m : ℕ} (i : Fin 3) : Label s m := ref (axisRef i)
def letterLabel {s m : ℕ} (a : Fin s) : Label s m := ref (letterRef a)
def identityLabel {s m : ℕ} : Label s m := ref identityRef
def stateLabel {s m : ℕ} (j : Fin m) : Label s m := .inr (.inl j)
def imageLabel {s m : ℕ} (a : Fin s) (j : Fin m) : Label s m := .inr (.inr (.inl (a,j)))
def deficitLabel {s m : ℕ} : Label s m := .inr (.inr (.inr ()))

def referenceDirection {s : ℕ} : Reference s → Space 3
  | .inl i => axis i
  | .inr (.inl a) => letterDirection a
  | .inr (.inr _) => identityDirection

theorem card_labels (s m : ℕ) : Fintype.card (Label s m) = (s + 1) * m + s + 5 := by
  simp only [Label, Reference, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_unit, Fintype.card_prod]
  ring

section Generic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def sumBody (K : ι → Body 3) (w : ι → ℝ) : Body 3 := ∑ i, w i • K i

def SameVolume (K L : ι → Body 3) : Prop :=
  ∀ w : ι → ℝ, (∀ i, 0 ≤ w i) → bodyVolume (sumBody K w) = bodyVolume (sumBody L w)

theorem SameVolume.refl (K : ι → Body 3) : SameVolume K K := fun _ _ => rfl

theorem SameVolume.symm {K L : ι → Body 3} (h : SameVolume K L) : SameVolume L K :=
  fun w hw => (h w hw).symm

theorem SameVolume.trans {K L M : ι → Body 3} (h : SameVolume K L) (h' : SameVolume L M) :
    SameVolume K M := fun w hw => (h w hw).trans (h' w hw)

def unitWeight (i : ι) : ι → ℝ := Pi.single i 1

theorem unitWeight_nonneg (i j : ι) : 0 ≤ unitWeight i j := by
  simp only [unitWeight, Pi.single_apply]
  split <;> norm_num

@[simp] theorem sumBody_unit (K : ι → Body 3) (i : ι) : sumBody K (unitWeight i) = K i := by
  simp [sumBody, unitWeight, Pi.single_apply]

theorem sumBody_add (K : ι → Body 3) (u v : ι → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) :
    sumBody K (u + v) = sumBody K u + sumBody K v := by
  simp only [sumBody, Pi.add_apply, body_add_smul _ (hu _) (hv _), Finset.sum_add_distrib]

theorem SameVolume.pair {K L : ι → Body 3} (h : SameVolume K L) (i j : ι) :
    bodyVolume (K i + K j) = bodyVolume (L i + L j) := by
  have hh := h (unitWeight i + unitWeight j)
    (fun k => add_nonneg (unitWeight_nonneg i k) (unitWeight_nonneg j k))
  simpa only [sumBody_add _ _ _ (unitWeight_nonneg i) (unitWeight_nonneg j), sumBody_unit] using hh

theorem SameVolume.triple {K L : ι → Body 3} (h : SameVolume K L) (i j k : ι) :
    bodyVolume (K i + K j + K k) = bodyVolume (L i + L j + L k) := by
  have hh := h (unitWeight i + unitWeight j + unitWeight k)
    (fun l => add_nonneg (add_nonneg (unitWeight_nonneg i l) (unitWeight_nonneg j l))
      (unitWeight_nonneg k l))
  have hs (M : ι → Body 3) :
      sumBody M (unitWeight i + unitWeight j + unitWeight k) = M i + M j + M k := by
    rw [sumBody_add M (unitWeight i + unitWeight j) (unitWeight k)
      (fun l => add_nonneg (unitWeight_nonneg i l) (unitWeight_nonneg j l)) (unitWeight_nonneg k),
      sumBody_add M (unitWeight i) (unitWeight j) (unitWeight_nonneg i) (unitWeight_nonneg j)]
    simp only [sumBody_unit]
  simpa only [hs] using hh

theorem sumBody_translate (K : ι → Body 3) (p : ι → Space 3) (w : ι → ℝ) :
    sumBody (fun i => translateBody (p i) (K i)) w =
      translateBody (∑ i, w i • p i) (sumBody K w) := by
  simp only [sumBody, translateBody, smul_add, ← pointBody_smul, Finset.sum_add_distrib]
  congr 1
  exact (map_sum (pointBodyHom (E := Space 3)) _ _).symm

theorem sameVolume_translate (K : ι → Body 3) (p : ι → Space 3) :
    SameVolume (fun i => translateBody (p i) (K i)) K := by
  intro w _
  rw [sumBody_translate, bodyVolume_translate]

theorem sumBody_map (K : ι → Body 3) (f : Space 3 →L[ℝ] Space 3) (w : ι → ℝ) :
    sumBody (fun i => mapBody f (K i)) w = mapBody f (sumBody K w) := by
  simp only [sumBody]
  rw [show mapBody f (∑ i, w i • K i) = ∑ i, mapBody f (w i • K i) from
    map_sum (mapBodyHom f) _ _]
  simp only [mapBody_smul]

theorem sameVolume_map (K : ι → Body 3) (f : Space 3 →L[ℝ] Space 3)
    (hf : |LinearMap.det f.toLinearMap| = 1) :
    SameVolume (fun i => mapBody f (K i)) K := by
  intro w _
  rw [sumBody_map, bodyVolume_map, hf, one_mul]

end Generic

end MixedVolume.GeneralLabels

end
