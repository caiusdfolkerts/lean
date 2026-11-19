module

public import mixed_volume.general.target_polynomial

/-! Signed evaluations supported in the common XZ plane vanish identically.
The proof is polynomial identity from actual nonnegative Minkowski sums. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.PlanarRestriction

open VolumePolynomials VolumePolynomials.Holonomy AutomatonWords GeneralLabels
open GeneralTarget CanonicalGeometry MvPolynomial Set MeasureTheory
open scoped Pointwise BigOperators Classical

abbrev Plane := AutomatonWords.Plane

section Generic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def maskVariable (keep : ι → Prop) (i : ι) : MvPolynomial ι ℝ := by
  classical
  exact if keep i then X i else 0

def maskWeight (keep : ι → Prop) (w : ι → ℝ) (i : ι) : ℝ := by
  classical
  exact if keep i then w i else 0

theorem eval_mask (keep : ι → Prop) (w : ι → ℝ) (P : MvPolynomial ι ℝ) :
    MvPolynomial.eval w (MvPolynomial.bind₁ (maskVariable keep) P) =
      MvPolynomial.eval (maskWeight keep w) P := by
  classical
  rw [MvPolynomial.eval,MvPolynomial.eval₂Hom_bind₁]
  have hf : (fun i => MvPolynomial.eval₂Hom (RingHom.id ℝ) w (maskVariable keep i)) =
      maskWeight keep w := by
    funext i
    by_cases hi : keep i <;> simp [maskVariable,maskWeight,hi]
  rw [hf]
  rfl

theorem masked_eval_zero (K : ι → Body 3) (keep : ι → Prop)
    (h : ∀ w : ι → ℝ, (∀ i, 0 ≤ w i) → bodyVolume (sumBody K (maskWeight keep w)) = 0)
    (w : ι → ℝ) : MvPolynomial.eval (maskWeight keep w) (indexedPolynomial K) = 0 := by
  classical
  have hp : MvPolynomial.bind₁ (maskVariable keep) (indexedPolynomial K) = 0 := by
    apply MvPolynomial.funext_set (fun _ => Ici (0 : ℝ)) (fun _ => Ici_infinite 0)
    intro v hv
    have hn : ∀ i, 0 ≤ v i := fun i => hv i (Set.mem_univ _)
    have hm : ∀ i, 0 ≤ maskWeight keep v i := by
      intro i
      by_cases hi : keep i <;> simp [maskWeight,hi,hn i]
    rw [eval_mask,indexedPolynomial_eval _ _ hm,map_zero]
    exact h v hn
  have he := congrArg (MvPolynomial.eval w) hp
  simpa only [eval_mask,map_zero] using he

end Generic

variable {s m : ℕ}

def keepXZ : Label s m → Prop
  | .inl (.inl i) => i = 0 ∨ i = 2
  | .inr (.inl _) => True
  | .inr (.inr (.inr _)) => True
  | _ => False

def xzBody (A : Data s m) (hs : 0 < s) : Label s m → ConvexBody Plane
  | .inl (.inl i) => if i = 0 then PlanarCorner.unitX else if i = 2 then PlanarCorner.unitY else 0
  | .inr (.inl j) => AutomatonZonoids.stateBody A hs j
  | _ => 0

theorem mapBody_zero_plane (f : Plane →L[ℝ] Space 3) : mapBody f (0 : ConvexBody Plane) = 0 :=
  (mapBodyHom f).map_zero

theorem masked_canonical (A : Data s m) (hs : 0 < s) (i : Label s m) :
    (if keepXZ i then canonical A hs i else 0) = mapBody embedXZ (xzBody A hs i) := by
  classical
  rcases i with (i | a | ⟨⟩) | j | ⟨a,j⟩ | ⟨⟩
  · fin_cases i <;> simp [keepXZ,xzBody,canonical,referenceDirection,
      embedXZ_unitX,embedXZ_unitY,mapBody_zero_plane]
  · simp [keepXZ,xzBody,mapBody_zero_plane]
  · simp [keepXZ,xzBody,mapBody_zero_plane]
  · simp [keepXZ,xzBody,canonical]
  · simp [keepXZ,xzBody,mapBody_zero_plane]
  · simp [keepXZ,xzBody,canonical,mapBody_zero_plane]

theorem sumBody_maskXZ (A : Data s m) (hs : 0 < s) (w : Label s m → ℝ) :
    sumBody (canonical A hs) (maskWeight keepXZ w) =
      mapBody embedXZ (∑ i, w i • xzBody A hs i) := by
  classical
  rw [show mapBody embedXZ (∑ i, w i • xzBody A hs i) =
      ∑ i, mapBody embedXZ (w i • xzBody A hs i) from map_sum (mapBodyHom embedXZ) _ _]
  simp only [sumBody,mapBody_smul,← masked_canonical A hs]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : keepXZ i <;> simp [maskWeight,hi]

theorem volume_embedXZ_zero (K : ConvexBody Plane) : bodyVolume (mapBody embedXZ K) = 0 := by
  have h := ScalarCombination.volume_planePair K 0
  simpa only [ScalarCombination.planePair,mapBody_zero_plane,add_zero,
    PlanarInteraction.height_zeroBody,PlanarInteraction.area_zeroBody,mul_zero,add_zero] using h

theorem eval_canonical_XZ (A : Data s m) (hs : 0 < s) (w : Label s m → ℝ)
    (hw : ∀ i, ¬ keepXZ i → w i = 0) :
    MvPolynomial.eval w (indexedPolynomial (canonical A hs)) = 0 := by
  classical
  have hmask : maskWeight keepXZ w = w := by
    funext i
    by_cases hi : keepXZ i <;> simp [maskWeight,hi,hw i]
  rw [← hmask]
  apply masked_eval_zero
  intro v _
  rw [sumBody_maskXZ,volume_embedXZ_zero]

/-- The deficit-plus-two-axis test is zero even when its shifted state
coefficients have arbitrary signs. -/
theorem target_deficit_plane (A : Data s m) (hs : 0 < s) (δ : Fin m → ℝ) :
    MvPolynomial.eval (unitWeight deficitLabel + unitWeight (axisLabel 0) + unitWeight (axisLabel 2))
      (targetPolynomial A hs δ) = 0 := by
  rw [targetPolynomial_eval]
  apply eval_canonical_XZ
  intro i hi
  rcases i with (i | a | ⟨⟩) | j | ⟨a,j⟩ | ⟨⟩
  · fin_cases i <;> simp_all [keepXZ,shiftWeight,unitWeight,axisLabel,ref,axisRef,deficitLabel,Pi.single_apply]
  · simp [shiftWeight,unitWeight,axisLabel,ref,axisRef,deficitLabel,Pi.single_apply]
  · simp [shiftWeight,unitWeight,axisLabel,ref,axisRef,deficitLabel,Pi.single_apply]
  · exact (hi trivial).elim
  · simp [shiftWeight,unitWeight,axisLabel,ref,axisRef,deficitLabel,Pi.single_apply]
  · exact (hi trivial).elim

end MixedVolume.PlanarRestriction

end
