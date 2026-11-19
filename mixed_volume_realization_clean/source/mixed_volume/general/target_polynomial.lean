module

public import mixed_volume.general.canonical_geometry

/-! The full homogeneous cubic and its signed substitution.  An identity on
an explicit open product of safe positive weights implies equality of every
coefficient; no truncated set of coefficients is used. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.GeneralTarget

open VolumePolynomials AutomatonWords GeneralLabels CanonicalGeometry MvPolynomial
open Set MeasureTheory
open scoped BigOperators Pointwise

section Indexed
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def indexedPolynomial (K : ι → Body 3) : MvPolynomial ι ℝ :=
  MvPolynomial.rename (Fintype.equivFin ι).symm
    (volumePolynomial volume (fun i => K ((Fintype.equivFin ι).symm i)))

theorem indexedPolynomial_eval (K : ι → Body 3) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    MvPolynomial.eval w (indexedPolynomial K) = bodyVolume (sumBody K w) := by
  rw [indexedPolynomial,MvPolynomial.eval_rename]
  rw [volumePolynomial_eval volume _ (w ∘ (Fintype.equivFin ι).symm) (fun i => hw _)]
  change volume.real (↑(∑ i, w ((Fintype.equivFin ι).symm i) •
    K ((Fintype.equivFin ι).symm i)) : Set (Space 3)) = volume.real (↑(∑ i, w i • K i) : Set (Space 3))
  rw [(Fintype.equivFin ι).symm.sum_comp (fun i => w i • K i)]

theorem indexedPolynomial_homogeneous (K : ι → Body 3) :
    (indexedPolynomial K).IsHomogeneous 3 := by
  have h := (volumePolynomial_homogeneous volume (fun i => K ((Fintype.equivFin ι).symm i))).rename_isHomogeneous
    (f := (Fintype.equivFin ι).symm)
  simpa only [indexedPolynomial,Space,Module.finrank_pi,Module.finrank_self,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one] using h

end Indexed

variable {s m : ℕ}

def shiftVariable (δ : Fin m → ℝ) : Label s m → MvPolynomial (Label s m) ℝ
  | .inr (.inl j) => X (stateLabel j) + C (δ j) * X deficitLabel
  | i => X i

def shiftWeight (δ : Fin m → ℝ) (w : Label s m → ℝ) : Label s m → ℝ
  | .inr (.inl j) => w (stateLabel j) + δ j * w deficitLabel
  | i => w i

def targetPolynomial (A : Data s m) (hs : 0 < s) (δ : Fin m → ℝ) :
    MvPolynomial (Label s m) ℝ :=
  MvPolynomial.bind₁ (shiftVariable δ) (indexedPolynomial (canonical A hs))

theorem targetPolynomial_eval (A : Data s m) (hs : 0 < s) (δ : Fin m → ℝ)
    (w : Label s m → ℝ) :
    MvPolynomial.eval w (targetPolynomial A hs δ) =
      MvPolynomial.eval (shiftWeight δ w) (indexedPolynomial (canonical A hs)) := by
  rw [targetPolynomial,MvPolynomial.eval,MvPolynomial.eval₂Hom_bind₁]
  have hfun : (fun i => MvPolynomial.eval₂Hom (RingHom.id ℝ) w (shiftVariable δ i)) =
      shiftWeight δ w := by
    funext i
    rcases i with r | j | aj | u <;> simp [shiftVariable,shiftWeight]
  rw [hfun]
  rfl

theorem shiftVariable_homogeneous (δ : Fin m → ℝ) (i : Label s m) :
    (shiftVariable δ i).IsHomogeneous 1 := by
  rcases i with r | j | aj | u
  · exact MvPolynomial.isHomogeneous_X ℝ _
  · exact (MvPolynomial.isHomogeneous_X ℝ _).add ((MvPolynomial.isHomogeneous_X ℝ _).C_mul _)
  · exact MvPolynomial.isHomogeneous_X ℝ _
  · exact MvPolynomial.isHomogeneous_X ℝ _

theorem targetPolynomial_homogeneous (A : Data s m) (hs : 0 < s) (δ : Fin m → ℝ) :
    (targetPolynomial A hs δ).IsHomogeneous 3 := by
  have h := (indexedPolynomial_homogeneous (canonical A hs)).aeval (shiftVariable δ)
    (shiftVariable_homogeneous δ)
  simpa only [targetPolynomial,MvPolynomial.aeval_eq_bind₁,one_mul] using h

def RealizesTarget (A : Data s m) (hs : 0 < s) (δ : Fin m → ℝ) (K : Label s m → Body 3) : Prop :=
  ∀ w : Label s m → ℝ, (∀ i, 0 ≤ w i) →
    MvPolynomial.eval w (targetPolynomial A hs δ) = bodyVolume (sumBody K w)

def SafeVolumeIdentity (A : Data s m) (hs : 0 < s) (δ : Fin m → ℝ)
    (K : Label s m → Body 3) : Prop :=
  ∀ w : Label s m → ℝ, (∀ i, 0 ≤ w i) → (∀ i, 0 ≤ shiftWeight δ w i) →
    bodyVolume (sumBody K w) = bodyVolume (sumBody (canonical A hs) (shiftWeight δ w))

def safeLower (δ : Fin m → ℝ) : ℝ := 1 + ∑ j, |δ j|
def safeBox (δ : Fin m → ℝ) (i : Label s m) : Set ℝ :=
  if i = deficitLabel then Ioo 0 1 else Ioi (safeLower δ)

theorem safeBox_infinite (δ : Fin m → ℝ) (i : Label s m) : (safeBox δ i).Infinite := by
  unfold safeBox
  split_ifs
  · exact Set.Ioo_infinite (by norm_num : (0 : ℝ) < 1)
  · exact Set.Ioi_infinite _

theorem safeBox_weights (δ : Fin m → ℝ) (w : Label s m → ℝ)
    (hw : w ∈ Set.pi Set.univ (safeBox δ)) :
    (∀ i, 0 ≤ w i) ∧ (∀ i, 0 ≤ shiftWeight δ w i) := by
  have hd : 0 < w deficitLabel ∧ w deficitLabel < 1 := by
    simpa [safeBox] using hw deficitLabel (Set.mem_univ _)
  have hlower : 0 ≤ safeLower δ := by
    dsimp [safeLower]
    exact add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hn (i : Label s m) : 0 ≤ w i := by
    by_cases hi : i = deficitLabel
    · subst i; exact hd.1.le
    · have hi' := hw i (Set.mem_univ _)
      simp only [safeBox,if_neg hi,Set.mem_Ioi] at hi'
      exact hlower.trans hi'.le
  refine ⟨hn,?_⟩
  intro i
  rcases i with r | j | aj | u
  · exact hn _
  · change 0 ≤ w (stateLabel j) + δ j * w deficitLabel
    have hj : safeLower δ < w (stateLabel j) := by
      simpa [safeBox,stateLabel,deficitLabel] using hw (stateLabel j) (Set.mem_univ _)
    have hsum : |δ j| ≤ ∑ k, |δ k| :=
      Finset.single_le_sum (fun k _ => abs_nonneg (δ k)) (Finset.mem_univ j)
    have hprod : -|δ j| ≤ δ j * w deficitLabel := by
      have hl := neg_abs_le (δ j)
      have hm := mul_le_mul_of_nonneg_right hl hd.1.le
      nlinarith [abs_nonneg (δ j)]
    dsimp [safeLower] at hj
    linarith
  · exact hn _
  · exact hn _

/-- Safe nonnegative Minkowski sums determine the entire signed-substitution
cubic, by polynomial identity on an explicitly proved infinite product. -/
theorem realizesTarget_iff_safe (A : Data s m) (hs : 0 < s) (δ : Fin m → ℝ)
    (K : Label s m → Body 3) :
    RealizesTarget A hs δ K ↔ SafeVolumeIdentity A hs δ K := by
  constructor
  · intro h w hw hshift
    rw [← h w hw,targetPolynomial_eval,indexedPolynomial_eval _ _ hshift]
  · intro h
    have heq : targetPolynomial A hs δ = indexedPolynomial K := by
      apply MvPolynomial.funext_set (safeBox δ) (safeBox_infinite δ)
      intro w hw
      obtain ⟨hn,hshift⟩ := safeBox_weights δ w hw
      rw [targetPolynomial_eval,indexedPolynomial_eval _ _ hshift,indexedPolynomial_eval _ _ hn]
      exact (h w hn hshift).symm
    intro w hw
    rw [heq,indexedPolynomial_eval _ _ hw]

theorem RealizesTarget.of_sameVolume {A : Data s m} {hs : 0 < s} {δ : Fin m → ℝ}
    {K L : Label s m → Body 3} (h : RealizesTarget A hs δ K) (heq : SameVolume L K) :
    RealizesTarget A hs δ L := fun w hw => (h w hw).trans (heq w hw).symm

theorem shiftWeight_zero_deficit (δ : Fin m → ℝ) (w : Label s m → ℝ)
    (hz : w deficitLabel = 0) : shiftWeight δ w = w := by
  funext i
  rcases i with r | j | aj | u <;> simp [shiftWeight,hz,stateLabel]

end MixedVolume.GeneralTarget

end
