module

public import VolumePolynomials.PolynomialMergeCoefficient
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Topology.Instances.RealVectorSpace

@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# Additivity of actual mixed volume

Selecting a subtuple sets the unused variables to zero. Adding two bodies
identifies their two variables. The squarefree-coefficient calculation then
proves additivity directly from the full volume-polynomial theorem.
-/

open Set MeasureTheory Module MvPolynomial
open scoped BigOperators Pointwise

namespace VolumePolynomials

def extendedWeights {m n : ℕ} (f : Fin m → Fin n) (hf : Function.Injective f)
    (t : Fin m → ℝ) (j : Fin n) : ℝ :=
  if h : j ∈ Set.range f then t ((Equiv.ofInjective f hf).symm ⟨j, h⟩) else 0

@[simp] theorem extendedWeights_apply {m n : ℕ} (f : Fin m → Fin n)
    (hf : Function.Injective f) (t : Fin m → ℝ) (i : Fin m) :
    extendedWeights f hf t (f i) = t i := by
  first
  | simp [extendedWeights, Equiv.ofInjective_symm_apply]

theorem extendedWeights_nonnegative {m n : ℕ} (f : Fin m → Fin n)
    (hf : Function.Injective f) (t : Fin m → ℝ) (ht : ∀ i, 0 ≤ t i) :
    ∀ j, 0 ≤ extendedWeights f hf t j := by
  first
  | intro j
    unfold extendedWeights
    split_ifs <;> first | exact ht _ | exact le_rfl

theorem eval_killCompl {m n : ℕ} (f : Fin m → Fin n) (hf : Function.Injective f)
    (t : Fin m → ℝ) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.eval t (MvPolynomial.killCompl hf p) =
      MvPolynomial.eval (extendedWeights f hf t) p := by
  first
  | classical
    have h : (MvPolynomial.aeval t : MvPolynomial (Fin m) ℝ →ₐ[ℝ] ℝ).comp
        (MvPolynomial.killCompl hf) =
        MvPolynomial.aeval (extendedWeights f hf t) := by
      first
      | apply MvPolynomial.algHom_ext
        intro j
        simp only [AlgHom.comp_apply, MvPolynomial.killCompl, MvPolynomial.aeval_X]
        unfold extendedWeights
        split_ifs <;> simp only [MvPolynomial.aeval_X, map_zero]
    simpa only [AlgHom.comp_apply, MvPolynomial.aeval_eq_eval] using
      congrArg (fun q : MvPolynomial (Fin n) ℝ →ₐ[ℝ] ℝ => q p) h

/-- Continuity extends additive nonnegative scalar behavior to every
nonnegative real scalar. The extension to the real line is proved additive
from the positive/negative-part identity. -/
theorem continuous_nonnegative_additive (f : ℝ → ℝ) (hf : Continuous f)
    (hf0 : f 0 = 0)
    (hadd : ∀ r s : ℝ, 0 ≤ r → 0 ≤ s → f (r + s) = f r + f s)
    {r : ℝ} (hr : 0 ≤ r) : f r = r * f 1 := by
  first
  | have hparts (x : ℝ) : max x 0 - max (-x) 0 = x := by
      first
      | rcases le_total 0 x with hx | hx
        · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), sub_zero]
        · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]
          ring
    let g : ℝ →+ ℝ :=
      { toFun := fun x => f (max x 0) - f (max (-x) 0)
        map_zero' := by simp only [neg_zero, max_self, hf0, sub_self]
        map_add' := fun x y => by
          have hb : max (x + y) 0 + max (-x) 0 + max (-y) 0 =
              max x 0 + max y 0 + max (-(x + y)) 0 := by
            first
            | linarith [hparts x, hparts y, hparts (x + y)]
          have h := congrArg f hb
          rw [hadd _ _ (add_nonneg (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _),
            hadd _ _ (le_max_right _ _) (le_max_right _ _),
            hadd _ _ (add_nonneg (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _),
            hadd _ _ (le_max_right _ _) (le_max_right _ _)] at h
          linarith }
    have hg : Continuous g :=
      (hf.comp (continuous_id.max continuous_const)).sub
        (hf.comp (continuous_neg.max continuous_const))
    have h := map_real_smul g hg r (1 : ℝ)
    simp only [smul_eq_mul, mul_one] at h
    change f (max r 0) - f (max (-r) 0) =
      r * (f (max 1 0) - f (max (-1) 0)) at h
    simpa only [max_eq_left hr, max_eq_right (neg_nonpos.mpr hr),
      max_eq_left zero_le_one, max_eq_right (by norm_num : (-1 : ℝ) ≤ 0),
      hf0, sub_zero] using h

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem sum_extendedWeights {m n : ℕ} (K : Fin n → ConvexBody E)
    (f : Fin m → Fin n) (hf : Function.Injective f) (t : Fin m → ℝ) :
    (∑ j, extendedWeights f hf t j • K j) = ∑ i, t i • K (f i) := by
  first
  | classical
    calc
      (∑ j, extendedWeights f hf t j • K j) =
          ∑ j ∈ Finset.univ.image f, extendedWeights f hf t j • K j := by
        first
        | symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro j _ hj
          have hj' : j ∉ Set.range f := by
            first
            | rintro ⟨i, hi⟩
              exact hj (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
          simp only [extendedWeights, dif_neg hj', body_zero_smul]
      _ = ∑ i, extendedWeights f hf t (f i) • K (f i) :=
        Finset.sum_image (fun i _ j _ h => hf h)
      _ = ∑ i, t i • K (f i) := by simp only [extendedWeights_apply]

theorem volumePolynomial_subtuple {m n : ℕ} (K : Fin n → ConvexBody E)
    (f : Fin m → Fin n) (hf : Function.Injective f) :
    volumePolynomial μ (fun i => K (f i)) =
      MvPolynomial.killCompl hf (volumePolynomial μ K) := by
  first
  | apply volumePolynomial_eq_of_eval
    intro t ht
    rw [eval_killCompl f hf, volumePolynomial_eval μ K _
      (extendedWeights_nonnegative f hf t ht), sum_extendedWeights K f hf t]

def mergedTuple {d : ℕ} (i : Fin d) (K : Fin (d + 1) → ConvexBody E) :
    Fin d → ConvexBody E := Function.update (fun j => K j.succ) i (K 0 + K i.succ)

theorem sum_mergedTuple {d : ℕ} (i : Fin d) (K : Fin (d + 1) → ConvexBody E)
    (t : Fin d → ℝ) :
    (∑ j, t j • mergedTuple i K j) = ∑ j, t (mergeIndex i j) • K j := by
  first
  | classical
    rw [Fin.sum_univ_succ]
    change (∑ j, t j • mergedTuple i K j) = t i • K 0 + ∑ j, t j • K j.succ
    calc
      (∑ j, t j • mergedTuple i K j) =
          ∑ j, ((if j = i then t i • K 0 else 0) + t j • K j.succ) := by
        first
        | apply Finset.sum_congr rfl
          intro j _
          by_cases hji : j = i
          · subst j
            simp [mergedTuple, smul_add]
          · simp [mergedTuple, hji]
      _ = t i • K 0 + ∑ j, t j • K j.succ := by simp [Finset.sum_add_distrib]

theorem volumePolynomial_merge {d : ℕ} (i : Fin d) (K : Fin (d + 1) → ConvexBody E) :
    volumePolynomial μ (mergedTuple i K) =
      MvPolynomial.rename (mergeIndex i) (volumePolynomial μ K) := by
  first
  | apply volumePolynomial_eq_of_eval
    intro t ht
    rw [MvPolynomial.eval_rename]
    change MvPolynomial.eval (fun j => t (mergeIndex i j)) (volumePolynomial μ K) =
      μ.real (↑(∑ j, t j • mergedTuple i K j) : Set E)
    rw [volumePolynomial_eval μ K _
      (fun j => ht (mergeIndex i j)), sum_mergedTuple i K t]

/-- Additivity in every argument, proved for arbitrary compact convex bodies.
Together with nonnegative scalar homogeneity this is Minkowski multilinearity. -/
theorem mixedVolume_add {d : ℕ} (K : Fin d → ConvexBody E) (i : Fin d)
    (A B : ConvexBody E) :
    mixedVolume μ (Function.update K i (A + B)) =
      mixedVolume μ (Function.update K i A) + mixedVolume μ (Function.update K i B) := by
  first
  | classical
    let L : Fin (d + 1) → ConvexBody E := Fin.cons A (Function.update K i B)
    have hmerged : mergedTuple i L = Function.update K i (A + B) := by
      first
      | funext j
        by_cases hj : j = i
        · subst j
          simp only [mergedTuple, Function.update_self, L, Fin.cons_zero, Fin.cons_succ]
        · simp only [mergedTuple, Function.update_of_ne hj, L, Fin.cons_succ]
    have hold : (fun j : Fin d => L j.succ) = Function.update K i B := by
      first
      | funext j
        simp only [L, Fin.cons_succ]
    have hnew : (fun j : Fin d => L (replaceIndex i j)) = Function.update K i A := by
      first
      | funext j
        by_cases hj : j = i
        · subst j
          simp only [replaceIndex_self, L, Fin.cons_zero, Function.update_self]
        · rw [replaceIndex_of_ne hj]
          simp only [L, Fin.cons_succ, Function.update_of_ne hj]
    have hpoly := volumePolynomial_merge μ i L
    rw [hmerged] at hpoly
    have holdpoly := volumePolynomial_subtuple μ L Fin.succ (Fin.succ_injective d)
    rw [hold] at holdpoly
    have hnewpoly := volumePolynomial_subtuple μ L (replaceIndex i) (replaceIndex_injective i)
    rw [hnew] at hnewpoly
    have holdcoeff : (volumePolynomial μ L).coeff (oldSquarefreeLift d) =
        (volumePolynomial μ (Function.update K i B)).coeff (squarefreeExponent d) := by
      first
      | rw [holdpoly, MvPolynomial.coeff_killCompl, oldSquarefreeLift_eq_mapDomain]
    have hnewcoeff : (volumePolynomial μ L).coeff (newSquarefreeLift i) =
        (volumePolynomial μ (Function.update K i A)).coeff (squarefreeExponent d) := by
      first
      | rw [hnewpoly, MvPolynomial.coeff_killCompl, newSquarefreeLift_eq_mapDomain]
    simp only [mixedVolume, hpoly, coeff_mergeIndex_squarefree, holdcoeff, hnewcoeff]
    ring

theorem mixedVolume_zero_arg {d : ℕ} (K : Fin d → ConvexBody E) (i : Fin d) :
    mixedVolume μ (Function.update K i 0) = 0 := by
  first
  | have h := mixedVolume_add μ K i (0 : ConvexBody E) 0
    rw [zero_add] at h
    linarith

/-- Positive homogeneity in every argument, including scalar zero. -/
theorem mixedVolume_smul {d : ℕ} (K : Fin d → ConvexBody E) (i : Fin d)
    (A : ConvexBody E) {r : ℝ} (hr : 0 ≤ r) :
    mixedVolume μ (Function.update K i (r • A)) =
      r * mixedVolume μ (Function.update K i A) := by
  first
  | let f : ℝ → ℝ := fun t => mixedVolume μ (Function.update K i (t • A))
    have hf : Continuous f := by
      first
      | apply (continuous_mixedVolume μ d).comp
        apply continuous_pi
        intro j
        by_cases hji : j = i
        · subst j
          simpa only [Function.update_self, Pi.smul_def', id_eq] using
            (continuous_id.smul continuous_const : Continuous (fun r : ℝ => r • A))
        · simpa only [Function.update_of_ne hji] using
            (continuous_const : Continuous (fun _ : ℝ => K j))
    have hf0 : f 0 = 0 := by
      first
      | dsimp only [f]
        rw [body_zero_smul, mixedVolume_zero_arg]
    have hadd : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → f (s + t) = f s + f t := by
      first
      | intro s t hs ht
        dsimp only [f]
        rw [body_add_smul A hs ht, mixedVolume_add]
    have h := continuous_nonnegative_additive f hf hf0 hadd hr
    simpa only [f, one_smul] using h

end Generic
end VolumePolynomials
