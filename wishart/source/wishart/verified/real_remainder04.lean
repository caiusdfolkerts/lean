module

public import wishart.verified.real_remainder03

/- Generated ordinary proof stage. See audit/staged_real_remainder/RealRemainder04/manifest.json. -/

@[expose] public section

section CanonicalSource30
/- Source: Wishart/LogSumExpGenerator.lean -/



/-!
# Log-sum-exp preserves nonnegative radial generators

The variance term is proved from positive semidefiniteness of the actual
matrix. It is not a formal convexity assumption about a differential operator.
-/

noncomputable section

open Matrix Filter Topology
open scoped BigOperators

namespace WishartVerification

variable {p : ℕ}

def radialGradient (f : SymmetricMatrix p → ℝ) (X : SymmetricMatrix p)
    (v : EuclideanSpace ℝ (Fin p)) : Fin p → ℝ :=
  fun i => fderiv ℝ f X (symmetricRankDirection v (coordinateVector i))

theorem symmetricCarreDuChamp_eq_quadratic (f : SymmetricMatrix p → ℝ)
    (X : SymmetricMatrix p) (v : EuclideanSpace ℝ (Fin p)) :
    symmetricCarreDuChamp f X v =
      matrixQuadratic (X : Matrix (Fin p) (Fin p) ℝ) (radialGradient f X v) := by
  simp only [symmetricCarreDuChamp, matrixQuadratic, radialGradient,
    dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem differentiableAt_directional_fderiv_exp
    {g : SymmetricMatrix p → ℝ} {X : SymmetricMatrix p}
    (hg : ∀ᶠ Y in 𝓝 X, DifferentiableAt ℝ g Y)
    (H : SymmetricMatrix p)
    (hD : DifferentiableAt ℝ (fun Y => fderiv ℝ g Y H) X) :
    DifferentiableAt ℝ (fun Y => fderiv ℝ (fun Z => Real.exp (g Z)) Y H) X := by
  have heq : (fun Y => fderiv ℝ (fun Z => Real.exp (g Z)) Y H) =ᶠ[𝓝 X]
      (fun Y => Real.exp (g Y) * fderiv ℝ g Y H) :=
    hg.mono fun Y hY => fderiv_exp_comp_apply hY H
  exact heq.differentiableAt_iff.mpr
    ((mem_of_mem_nhds hg).exp.mul hD)

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def exponentialSum (g : ι → SymmetricMatrix p → ℝ) (X : SymmetricMatrix p) : ℝ :=
  ∑ i, Real.exp (g i X)

theorem exponentialSum_pos (g : ι → SymmetricMatrix p → ℝ) (X : SymmetricMatrix p) :
    0 < exponentialSum g X :=
  Finset.sum_pos (fun i _ => Real.exp_pos (g i X)) Finset.univ_nonempty

theorem fderiv_exponentialSum_apply (g : ι → SymmetricMatrix p → ℝ)
    {X : SymmetricMatrix p} (hg : ∀ i, DifferentiableAt ℝ (g i) X)
    (H : SymmetricMatrix p) :
    fderiv ℝ (exponentialSum g) X H =
      ∑ i, Real.exp (g i X) * fderiv ℝ (g i) X H := by
  have h := fderiv_linear_combination_apply (fun _ : ι => (1 : ℝ))
    (fun i Y => Real.exp (g i Y)) (fun i => (hg i).exp) H
  have hcalc (i : ι) : fderiv ℝ (fun Y => Real.exp (g i Y)) X H =
      Real.exp (g i X) * fderiv ℝ (g i) X H := fderiv_exp_comp_apply (hg i) H
  have hsum : exponentialSum g = (fun Y => ∑ i, Real.exp (g i Y)) := rfl
  rw [hsum]
  simpa only [one_mul, hcalc] using h

theorem radialGradient_exponentialSum (g : ι → SymmetricMatrix p → ℝ)
    {X : SymmetricMatrix p} (hg : ∀ i, DifferentiableAt ℝ (g i) X)
    (v : EuclideanSpace ℝ (Fin p)) :
    radialGradient (exponentialSum g) X v =
      ∑ i, Real.exp (g i X) • radialGradient (g i) X v := by
  funext j
  simpa only [radialGradient, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
    fderiv_exponentialSum_apply g hg (symmetricRankDirection v (coordinateVector j))

theorem symmetricCarreDuChamp_exponentialSum_le
    (g : ι → SymmetricMatrix p → ℝ) {X : SymmetricMatrix p}
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (hg : ∀ i, DifferentiableAt ℝ (g i) X)
    (v : EuclideanSpace ℝ (Fin p)) :
    symmetricCarreDuChamp (exponentialSum g) X v ≤
      exponentialSum g X * ∑ i, Real.exp (g i X) * symmetricCarreDuChamp (g i) X v := by
  simp only [symmetricCarreDuChamp_eq_quadratic, radialGradient_exponentialSum g hg,
    exponentialSum]
  exact matrixQuadratic_weighted_sum_le hX (fun i => Real.exp (g i X))
    (fun i => (Real.exp_pos _).le) (fun i => radialGradient (g i) X v)

theorem exponentialSum_differentiable_near
    (g : ι → SymmetricMatrix p → ℝ) {X : SymmetricMatrix p}
    (hg : ∀ᶠ Y in 𝓝 X, ∀ i, DifferentiableAt ℝ (g i) Y) :
    ∀ᶠ Y in 𝓝 X, DifferentiableAt ℝ (exponentialSum g) Y := by
  filter_upwards [hg] with Y hY
  exact DifferentiableAt.fun_sum (fun i _ => (hY i).exp)

theorem exponentialSum_direction_differentiable
    (g : ι → SymmetricMatrix p → ℝ) {X : SymmetricMatrix p}
    (hg : ∀ᶠ Y in 𝓝 X, ∀ i, DifferentiableAt ℝ (g i) Y)
    (hD : ∀ i H, DifferentiableAt ℝ (fun Y => fderiv ℝ (g i) Y H) X)
    (H : SymmetricMatrix p) :
    DifferentiableAt ℝ (fun Y => fderiv ℝ (exponentialSum g) Y H) X := by
  have hgx := mem_of_mem_nhds hg
  have heq : (fun Y => fderiv ℝ (exponentialSum g) Y H) =ᶠ[𝓝 X]
      (fun Y => ∑ i, Real.exp (g i Y) * fderiv ℝ (g i) Y H) :=
    hg.mono fun Y hY => fderiv_exponentialSum_apply g hY H
  exact heq.differentiableAt_iff.mpr
    (DifferentiableAt.fun_sum (fun i _ => (hgx i).exp.mul (hD i H)))

theorem symmetricDirectionalGenerator_exponentialSum
    (g : ι → SymmetricMatrix p → ℝ) {X : SymmetricMatrix p}
    (hg : ∀ᶠ Y in 𝓝 X, ∀ i, DifferentiableAt ℝ (g i) Y)
    (hD : ∀ i H, DifferentiableAt ℝ (fun Y => fderiv ℝ (g i) Y H) X)
    (N : ℝ) (v : EuclideanSpace ℝ (Fin p)) :
    symmetricDirectionalGenerator N v (exponentialSum g) X =
      ∑ i, Real.exp (g i X) *
        (symmetricDirectionalGenerator N v (g i) X + symmetricCarreDuChamp (g i) X v) := by
  have hexp : ∀ᶠ Y in 𝓝 X, ∀ i, DifferentiableAt ℝ (fun Z => Real.exp (g i Z)) Y :=
    hg.mono fun Y hY i => (hY i).exp
  have hExpD (i : ι) (H : SymmetricMatrix p) :
      DifferentiableAt ℝ (fun Y => fderiv ℝ (fun Z => Real.exp (g i Z)) Y H) X :=
    differentiableAt_directional_fderiv_exp (hg.mono fun Y hY => hY i) H (hD i H)
  have hsum := symmetricDirectionalGenerator_linear_combination
    (fun _ : ι => (1 : ℝ)) (fun i Y => Real.exp (g i Y)) hexp hExpD N v
  simp only [one_mul] at hsum
  change symmetricDirectionalGenerator N v (exponentialSum g) X = _ at hsum
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i hi
  exact symmetricDirectionalGenerator_exp (hg.mono fun Y hY => hY i) (hD i) N v

/-- Log-sum-exp has a nonnegative radial generator whenever each input does.
The input matrix may be singular. -/
theorem symmetricDirectionalGenerator_logSumExp_nonneg
    (g : ι → SymmetricMatrix p → ℝ) {X : SymmetricMatrix p}
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (hg : ∀ᶠ Y in 𝓝 X, ∀ i, DifferentiableAt ℝ (g i) Y)
    (hD : ∀ i H, DifferentiableAt ℝ (fun Y => fderiv ℝ (g i) Y H) X)
    (N : ℝ) (v : EuclideanSpace ℝ (Fin p))
    (hgen : ∀ i, 0 ≤ symmetricDirectionalGenerator N v (g i) X) :
    0 ≤ symmetricDirectionalGenerator N v (fun Y => Real.log (exponentialSum g Y)) X := by
  let S := exponentialSum g X
  have hS : 0 < S := exponentialSum_pos g X
  have hnear := exponentialSum_differentiable_near g hg
  have hlog : ∀ᶠ Y in 𝓝 X, DifferentiableAt ℝ Real.log (exponentialSum g Y) :=
    Filter.Eventually.of_forall fun Y => Real.differentiableAt_log (exponentialSum_pos g Y).ne'
  have hlog' : DifferentiableAt ℝ (deriv Real.log) (exponentialSum g X) := by
    rw [Real.deriv_log']
    exact (hasDerivAt_inv hS.ne').differentiableAt
  rw [symmetricDirectionalGenerator_scalar_comp hnear hlog hlog'
    (exponentialSum_direction_differentiable g hg hD), Real.deriv_log,
    Real.deriv_log', deriv_inv]
  have hsum := symmetricDirectionalGenerator_exponentialSum g hg hD N v
  have hvariance := symmetricCarreDuChamp_exponentialSum_le g hX (mem_of_mem_nhds hg) v
  have hpositive : 0 ≤ ∑ i, Real.exp (g i X) * symmetricDirectionalGenerator N v (g i) X :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (Real.exp_pos _).le (hgen i))
  have hnumerator : 0 ≤ S * symmetricDirectionalGenerator N v (exponentialSum g) X -
      symmetricCarreDuChamp (exponentialSum g) X v := by
    rw [hsum]
    simp only [mul_add, Finset.sum_add_distrib]
    have h := mul_nonneg hS.le hpositive
    dsimp [S] at *
    nlinarith
  have hid : S⁻¹ * symmetricDirectionalGenerator N v (exponentialSum g) X +
      -(S ^ 2)⁻¹ * symmetricCarreDuChamp (exponentialSum g) X v =
      (S * symmetricDirectionalGenerator N v (exponentialSum g) X -
        symmetricCarreDuChamp (exponentialSum g) X v) / S ^ 2 := by
    field_simp [hS.ne']
    ring
  change 0 ≤ S⁻¹ * symmetricDirectionalGenerator N v (exponentialSum g) X +
      -(S ^ 2)⁻¹ * symmetricCarreDuChamp (exponentialSum g) X v
  rw [hid]
  exact div_nonneg hnumerator (sq_nonneg S)

end WishartVerification
end
end CanonicalSource30

section CanonicalSource31
/- Source: Wishart/PowerMeanDeterminants.lean -/



/-!
# Smooth power means of determinant monomials

These are the finite approximants used before passing to an arbitrary finite
convex logarithmic outer function. Their global derivative growth is proved,
and their local equality with the intended logarithmic expression is exact.
-/

noncomputable section

open Matrix Filter Topology
open scoped BigOperators

namespace WishartVerification

variable {p : ℕ} {k ι : Type*} [Fintype k] [DecidableEq k]
  [Fintype ι] [Nonempty ι]

def regularizedAffinePowerSum (ε L : ℝ) (B : Matrix k k ℝ)
    (M : Matrix (Fin p) k ℝ) (a b : ι → ℝ) (X : SymmetricMatrix p) : ℝ :=
  ∑ i, Real.exp (L * b i) * smoothRegularizedDetPower ε (L * a i) B M X

def regularizedAffinePowerMean (ε L : ℝ) (B : Matrix k k ℝ)
    (M : Matrix (Fin p) k ℝ) (a b : ι → ℝ) (X : SymmetricMatrix p) : ℝ :=
  (regularizedAffinePowerSum ε L B M a b X / Fintype.card ι) ^ (1 / L)

def affineDeterminantLog (ε L : ℝ) (B : Matrix k k ℝ)
    (M : Matrix (Fin p) k ℝ) (a b : ι → ℝ) (i : ι) (X : SymmetricMatrix p) : ℝ :=
  L * (b i + a i * compressionLog ε B M X)

theorem regularizedAffinePowerSum_pos {ε : ℝ} (hε : 0 < ε) (L : ℝ)
    (B : Matrix k k ℝ) (M : Matrix (Fin p) k ℝ) (a b : ι → ℝ)
    (X : SymmetricMatrix p) : 0 < regularizedAffinePowerSum ε L B M a b X :=
  Finset.sum_pos (fun i _ => mul_pos (Real.exp_pos _)
    (smoothRegularizedDetPower_pos hε _ B M X)) Finset.univ_nonempty

theorem hasTemperateGrowth_regularizedAffinePowerSum {ε : ℝ} (hε : 0 < ε) (L : ℝ)
    (B : Matrix k k ℝ) (M : Matrix (Fin p) k ℝ) (a b : ι → ℝ) :
    (regularizedAffinePowerSum ε L B M a b).HasTemperateGrowth :=
  Function.HasTemperateGrowth.sum (fun i _ =>
    (Function.HasTemperateGrowth.const _).mul
      (hasTemperateGrowth_smoothRegularizedDetPower hε _ B M))

theorem regularizedAffinePowerSum_lower {ε L : ℝ} (hε : 0 < ε) (hL : 0 < L)
    (B : Matrix k k ℝ) (M : Matrix (Fin p) k ℝ) (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ X, δ ≤ regularizedAffinePowerSum ε L B M a b X := by
  classical
  let i : ι := Classical.choice inferInstance
  let δ : ℝ := Real.exp (L * b i) * (ε ^ Fintype.card k / 2 / 2) ^ (L * a i)
  have hδ : 0 < δ := mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by positivity) _)
  refine ⟨δ, hδ, fun X => ?_⟩
  calc
    δ ≤ Real.exp (L * b i) * smoothRegularizedDetPower ε (L * a i) B M X :=
      mul_le_mul_of_nonneg_left
        (smoothRegularizedDetPower_lower hε (mul_nonneg hL.le (ha i)) B M X)
        (Real.exp_pos _).le
    _ ≤ regularizedAffinePowerSum ε L B M a b X := by
      unfold regularizedAffinePowerSum
      exact Finset.single_le_sum (fun j _ => mul_nonneg (Real.exp_pos (L * b j)).le
        (smoothRegularizedDetPower_pos hε (L * a j) B M X).le) (Finset.mem_univ i)

set_option backward.isDefEq.respectTransparency false in
theorem hasTemperateGrowth_regularizedAffinePowerMean {ε L : ℝ}
    (hε : 0 < ε) (hL : 0 < L) (B : Matrix k k ℝ)
    (M : Matrix (Fin p) k ℝ) (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (regularizedAffinePowerMean ε L B M a b).HasTemperateGrowth := by
  obtain ⟨δ, hδ, hbound⟩ := regularizedAffinePowerSum_lower hε hL B M a b ha
  have hc : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hf : (fun X => regularizedAffinePowerSum ε L B M a b X / Fintype.card ι).HasTemperateGrowth := by
    simpa only [div_eq_mul_inv, Pi.mul_def] using
      (hasTemperateGrowth_regularizedAffinePowerSum hε L B M a b).mul
        (Function.HasTemperateGrowth.const (Fintype.card ι : ℝ)⁻¹)
  exact hasTemperateGrowth_rpow_of_pos_lower hf (div_pos hδ hc)
    (fun X => div_le_div_of_nonneg_right (hbound X) hc.le) (1 / L)

theorem affineDeterminantLog_exp {ε L : ℝ} {B : Matrix k k ℝ}
    (M : Matrix (Fin p) k ℝ) (a b : ι → ℝ) (i : ι) (X : SymmetricMatrix p)
    (hQ : 0 < (regularizedCompression ε B M X).det) :
    Real.exp (affineDeterminantLog ε L B M a b i X) =
      Real.exp (L * b i) * (regularizedCompression ε B M X).det ^ (L * a i) := by
  rw [affineDeterminantLog, compressionLog, mul_add, Real.exp_add,
    Real.rpow_def_of_pos hQ]
  congr 2
  ring

theorem regularizedAffinePowerMean_eventually_exp {ε L : ℝ}
    (hε : 0 < ε) (hL : 0 < L) {B : Matrix k k ℝ} (hB : B.PosSemidef)
    (M : Matrix (Fin p) k ℝ) (a b : ι → ℝ)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    regularizedAffinePowerMean ε L B M a b =ᶠ[𝓝 X]
      (fun Y => Real.exp ((Real.log (exponentialSum (affineDeterminantLog ε L B M a b) Y) -
        Real.log (Fintype.card ι)) / L)) := by
  have hnear : ∀ᶠ Y in 𝓝 X, ∀ i,
      smoothRegularizedDetPower ε (L * a i) B M Y =
        (regularizedCompression ε B M Y).det ^ (L * a i) := by
    apply Filter.eventually_all.mpr
    intro i
    exact smoothRegularizedDetPower_eventuallyEq hε _ hB M hX
  have hc := (hasTemperateGrowth_regularizedCompression_det ε B M).1.continuous
  have hpositive := hc.continuousAt.eventually
    (Ioi_mem_nhds (regularizedCompression_posDef hε hB M hX).det_pos)
  filter_upwards [hnear, hpositive] with Y hY hQ
  have hsum : regularizedAffinePowerSum ε L B M a b Y =
      exponentialSum (affineDeterminantLog ε L B M a b) Y := by
    unfold regularizedAffinePowerSum exponentialSum
    apply Finset.sum_congr rfl
    intro i hi
    rw [hY i, affineDeterminantLog_exp M a b i Y hQ]
  have hcard : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  rw [regularizedAffinePowerMean, hsum,
    Real.rpow_def_of_pos (div_pos (exponentialSum_pos _ Y) hcard),
    Real.log_div (exponentialSum_pos _ Y).ne' hcard.ne']
  congr 1
  ring

end WishartVerification
end
end CanonicalSource31

section CanonicalSource32
/- Source: Wishart/AffineGeneratorCalculus.lean -/



/-!
# Affine changes and second directional derivatives

These elementary closure lemmas concern the actual Fréchet derivatives used
in the radial operator. They supply, rather than assume, the derivative data
for the finite power-mean approximations.
-/

noncomputable section

open Filter Topology
open scoped BigOperators

namespace WishartVerification

variable {p : ℕ} {g : SymmetricMatrix p → ℝ} {X : SymmetricMatrix p}

theorem fderiv_affine_comp_apply (hg : DifferentiableAt ℝ g X)
    (a b : ℝ) (H : SymmetricMatrix p) :
    fderiv ℝ (fun Y => a * g Y + b) X H = a * fderiv ℝ g X H := by
  rw [((hg.hasFDerivAt.const_mul a).add_const b).fderiv]
  simp

theorem differentiableAt_directional_fderiv_affine
    (hg : ∀ᶠ Y in 𝓝 X, DifferentiableAt ℝ g Y)
    (hD : ∀ H, DifferentiableAt ℝ (fun Y => fderiv ℝ g Y H) X)
    (a b : ℝ) (H : SymmetricMatrix p) :
    DifferentiableAt ℝ (fun Y => fderiv ℝ (fun Z => a * g Z + b) Y H) X := by
  have heq : (fun Y => fderiv ℝ (fun Z => a * g Z + b) Y H) =ᶠ[𝓝 X]
      (fun Y => a * fderiv ℝ g Y H) :=
    hg.mono fun Y hY => fderiv_affine_comp_apply hY a b H
  exact heq.differentiableAt_iff.mpr ((hD H).const_mul a)

theorem second_fderiv_affine_comp_apply
    (hg : ∀ᶠ Y in 𝓝 X, DifferentiableAt ℝ g Y)
    (hD : ∀ H, DifferentiableAt ℝ (fun Y => fderiv ℝ g Y H) X)
    (a b : ℝ) (H K : SymmetricMatrix p) :
    fderiv ℝ (fun Y => fderiv ℝ (fun Z => a * g Z + b) Y H) X K =
      a * fderiv ℝ (fun Y => fderiv ℝ g Y H) X K := by
  have heq : (fun Y => fderiv ℝ (fun Z => a * g Z + b) Y H) =ᶠ[𝓝 X]
      (fun Y => a * fderiv ℝ g Y H) :=
    hg.mono fun Y hY => fderiv_affine_comp_apply hY a b H
  rw [heq.fderiv_eq, ((hD H).hasFDerivAt.const_mul a).fderiv]
  simp

theorem symmetricDirectionalGenerator_affine
    (hg : ∀ᶠ Y in 𝓝 X, DifferentiableAt ℝ g Y)
    (hD : ∀ H, DifferentiableAt ℝ (fun Y => fderiv ℝ g Y H) X)
    (a b N : ℝ) (v : EuclideanSpace ℝ (Fin p)) :
    symmetricDirectionalGenerator N v (fun Y => a * g Y + b) X =
      a * symmetricDirectionalGenerator N v g X := by
  have h := mem_of_mem_nhds hg
  simp only [symmetricDirectionalGenerator, fderiv_affine_comp_apply h,
    second_fderiv_affine_comp_apply hg hD]
  have hterm (i j : Fin p) :
      (X : Matrix (Fin p) (Fin p) ℝ) i j *
          (a * fderiv ℝ (fun Y => fderiv ℝ g Y
            (symmetricRankDirection v (coordinateVector i))) X
              (symmetricRankDirection v (coordinateVector j))) =
        a * ((X : Matrix (Fin p) (Fin p) ℝ) i j *
          fderiv ℝ (fun Y => fderiv ℝ g Y
            (symmetricRankDirection v (coordinateVector i))) X
              (symmetricRankDirection v (coordinateVector j))) := by ring
  simp only [hterm, ← Finset.mul_sum]
  ring

theorem differentiableAt_directional_fderiv_log
    (hg : ∀ᶠ Y in 𝓝 X, DifferentiableAt ℝ g Y)
    (hpos : ∀ᶠ Y in 𝓝 X, g Y ≠ 0)
    (hD : ∀ H, DifferentiableAt ℝ (fun Y => fderiv ℝ g Y H) X)
    (H : SymmetricMatrix p) :
    DifferentiableAt ℝ (fun Y => fderiv ℝ (fun Z => Real.log (g Z)) Y H) X := by
  have hgX := mem_of_mem_nhds hg
  have hposX := mem_of_mem_nhds hpos
  have heq : (fun Y => fderiv ℝ (fun Z => Real.log (g Z)) Y H) =ᶠ[𝓝 X]
      (fun Y => (g Y)⁻¹ * fderiv ℝ g Y H) := by
    filter_upwards [hg, hpos] with Y hY hYpos
    simpa only [Real.deriv_log] using
      fderiv_scalar_comp_apply hY (Real.differentiableAt_log hYpos) H
  exact heq.differentiableAt_iff.mpr ((hgX.inv hposX).mul (hD H))

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem logSumExp_differentiable_near
    (g : ι → SymmetricMatrix p → ℝ) {X : SymmetricMatrix p}
    (hg : ∀ᶠ Y in 𝓝 X, ∀ i, DifferentiableAt ℝ (g i) Y) :
    ∀ᶠ Y in 𝓝 X, DifferentiableAt ℝ (fun Z => Real.log (exponentialSum g Z)) Y := by
  filter_upwards [exponentialSum_differentiable_near g hg] with Y hY
  exact (Real.differentiableAt_log (exponentialSum_pos g Y).ne').comp Y hY

theorem logSumExp_direction_differentiable
    (g : ι → SymmetricMatrix p → ℝ) {X : SymmetricMatrix p}
    (hg : ∀ᶠ Y in 𝓝 X, ∀ i, DifferentiableAt ℝ (g i) Y)
    (hD : ∀ i H, DifferentiableAt ℝ (fun Y => fderiv ℝ (g i) Y H) X)
    (H : SymmetricMatrix p) :
    DifferentiableAt ℝ
      (fun Y => fderiv ℝ (fun Z => Real.log (exponentialSum g Z)) Y H) X :=
  differentiableAt_directional_fderiv_log
    (exponentialSum_differentiable_near g hg)
    (Filter.Eventually.of_forall fun Y => (exponentialSum_pos g Y).ne')
    (exponentialSum_direction_differentiable g hg hD) H

end WishartVerification
end
end CanonicalSource32

section CanonicalSource33
/- Source: Wishart/PowerMeanGenerator.lean -/



/-!
# Radial positivity for finite power-mean approximations

The slopes are the nonnegative slopes of supporting affine functions of
`log f (exp s)`. Every operator calculation below is on actual derivatives;
the final test is the globally smooth extension with proved temperate growth.
-/

noncomputable section

open Filter Topology Matrix
open scoped BigOperators

namespace WishartVerification

variable {p : ℕ} {k ι : Type*} [Fintype k] [DecidableEq k]
  [Fintype ι] [Nonempty ι]

theorem compressionLog_differentiable_near (ε : ℝ) (B : Matrix k k ℝ)
    (M : Matrix (Fin p) k ℝ) {X : SymmetricMatrix p}
    (hX : IsUnit (regularizedCompression ε B M X).det) :
    ∀ᶠ Y in 𝓝 X, DifferentiableAt ℝ (compressionLog ε B M) Y := by
  have hc := (hasTemperateGrowth_regularizedCompression_det ε B M).1.continuous
  filter_upwards [hc.continuousAt.eventually_ne hX.ne_zero] with Y hY
  exact (hasFDerivAt_compressionLog ε B M (isUnit_iff_ne_zero.mpr hY)).differentiableAt

theorem affineDeterminantLog_eq_affine (ε L : ℝ) (B : Matrix k k ℝ)
    (M : Matrix (Fin p) k ℝ) (a b : ι → ℝ) (i : ι) :
    affineDeterminantLog ε L B M a b i =
      (fun X => (L * a i) * compressionLog ε B M X + L * b i) := by
  funext X
  unfold affineDeterminantLog
  ring

theorem affineDeterminantLog_differentiable_near (ε L : ℝ) (B : Matrix k k ℝ)
    (M : Matrix (Fin p) k ℝ) (a b : ι → ℝ) {X : SymmetricMatrix p}
    (hX : IsUnit (regularizedCompression ε B M X).det) :
    ∀ᶠ Y in 𝓝 X, ∀ i, DifferentiableAt ℝ (affineDeterminantLog ε L B M a b i) Y := by
  filter_upwards [compressionLog_differentiable_near ε B M hX] with Y hY i
  rw [affineDeterminantLog_eq_affine]
  exact (hY.const_mul (L * a i)).add_const _

theorem affineDeterminantLog_direction_differentiable (ε L : ℝ) (B : Matrix k k ℝ)
    (M : Matrix (Fin p) k ℝ) (a b : ι → ℝ) {X : SymmetricMatrix p}
    (hX : IsUnit (regularizedCompression ε B M X).det) (i : ι) (H : SymmetricMatrix p) :
    DifferentiableAt ℝ
      (fun Y => fderiv ℝ (affineDeterminantLog ε L B M a b i) Y H) X := by
  rw [affineDeterminantLog_eq_affine]
  exact differentiableAt_directional_fderiv_affine
    (compressionLog_differentiable_near ε B M hX)
    (fun K => (hasFDerivAt_compressionLog_direction ε B M hX K).differentiableAt)
    (L * a i) (L * b i) H

theorem affineDeterminantLog_generator_nonneg {ε L : ℝ}
    (hε : 0 < ε) (hL : 0 < L) {B : Matrix k k ℝ} (hB : B.PosSemidef)
    (M : Matrix (Fin p) k ℝ) (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    {N : ℝ} (hN : min (Fintype.card k : ℝ) (p : ℝ) + 1 ≤ N)
    (v : EuclideanSpace ℝ (Fin p)) (i : ι) :
    0 ≤ symmetricDirectionalGenerator N v (affineDeterminantLog ε L B M a b i) X := by
  have hunit : IsUnit (regularizedCompression ε B M X).det :=
    isUnit_iff_ne_zero.mpr (regularizedCompression_posDef hε hB M hX).det_pos.ne'
  rw [affineDeterminantLog_eq_affine,
    symmetricDirectionalGenerator_affine
      (compressionLog_differentiable_near ε B M hunit)
      (fun H => (hasFDerivAt_compressionLog_direction ε B M hunit H).differentiableAt)]
  exact mul_nonneg (mul_nonneg hL.le (ha i))
    (symmetricDirectionalGenerator_compressionLog_nonneg_min hε hB M hX hN v)

def affinePowerMeanLog (ε L : ℝ) (B : Matrix k k ℝ)
    (M : Matrix (Fin p) k ℝ) (a b : ι → ℝ) (X : SymmetricMatrix p) : ℝ :=
  (1 / L) * Real.log (exponentialSum (affineDeterminantLog ε L B M a b) X) -
    Real.log (Fintype.card ι) / L

theorem regularizedAffinePowerMean_eventually_exp_log {ε L : ℝ}
    (hε : 0 < ε) (hL : 0 < L) {B : Matrix k k ℝ} (hB : B.PosSemidef)
    (M : Matrix (Fin p) k ℝ) (a b : ι → ℝ)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    regularizedAffinePowerMean ε L B M a b =ᶠ[𝓝 X]
      (fun Y => Real.exp (affinePowerMeanLog ε L B M a b Y)) := by
  filter_upwards [regularizedAffinePowerMean_eventually_exp hε hL hB M a b hX] with Y hY
  rw [hY]
  congr 1
  unfold affinePowerMeanLog
  ring

theorem affinePowerMeanLog_differentiable_near (ε L : ℝ) (B : Matrix k k ℝ)
    (M : Matrix (Fin p) k ℝ) (a b : ι → ℝ) {X : SymmetricMatrix p}
    (hX : IsUnit (regularizedCompression ε B M X).det) :
    ∀ᶠ Y in 𝓝 X, DifferentiableAt ℝ (affinePowerMeanLog ε L B M a b) Y := by
  have h := logSumExp_differentiable_near (affineDeterminantLog ε L B M a b)
    (affineDeterminantLog_differentiable_near ε L B M a b hX)
  filter_upwards [h] with Y hY
  exact (hY.const_mul (1 / L)).sub_const _

theorem affinePowerMeanLog_direction_differentiable (ε L : ℝ) (B : Matrix k k ℝ)
    (M : Matrix (Fin p) k ℝ) (a b : ι → ℝ) {X : SymmetricMatrix p}
    (hX : IsUnit (regularizedCompression ε B M X).det) (H : SymmetricMatrix p) :
    DifferentiableAt ℝ
      (fun Y => fderiv ℝ (affinePowerMeanLog ε L B M a b) Y H) X := by
  let g := affineDeterminantLog ε L B M a b
  have hg := affineDeterminantLog_differentiable_near ε L B M a b hX
  have hD := affineDeterminantLog_direction_differentiable ε L B M a b hX
  change DifferentiableAt ℝ (fun Y => fderiv ℝ
    (fun Z => (1 / L) * Real.log (exponentialSum g Z) - Real.log (Fintype.card ι) / L) Y H) X
  simpa only [sub_eq_add_neg] using differentiableAt_directional_fderiv_affine
    (logSumExp_differentiable_near g hg)
    (logSumExp_direction_differentiable g hg hD)
    (1 / L) (-(Real.log (Fintype.card ι) / L)) H

theorem affinePowerMeanLog_generator_nonneg {ε L : ℝ}
    (hε : 0 < ε) (hL : 0 < L) {B : Matrix k k ℝ} (hB : B.PosSemidef)
    (M : Matrix (Fin p) k ℝ) (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    {N : ℝ} (hN : min (Fintype.card k : ℝ) (p : ℝ) + 1 ≤ N)
    (v : EuclideanSpace ℝ (Fin p)) :
    0 ≤ symmetricDirectionalGenerator N v (affinePowerMeanLog ε L B M a b) X := by
  have hunit : IsUnit (regularizedCompression ε B M X).det :=
    isUnit_iff_ne_zero.mpr (regularizedCompression_posDef hε hB M hX).det_pos.ne'
  let g := affineDeterminantLog ε L B M a b
  have hg := affineDeterminantLog_differentiable_near ε L B M a b hunit
  have hD := affineDeterminantLog_direction_differentiable ε L B M a b hunit
  have hnonneg := symmetricDirectionalGenerator_logSumExp_nonneg g hX hg hD N v
    (affineDeterminantLog_generator_nonneg hε hL hB M a b ha hX hN v)
  unfold affinePowerMeanLog
  simp only [sub_eq_add_neg]
  rw [symmetricDirectionalGenerator_affine
    (logSumExp_differentiable_near g hg) (logSumExp_direction_differentiable g hg hD)]
  exact mul_nonneg (one_div_nonneg.mpr hL.le) hnonneg

section Products

variable {κ : Type*} [Fintype κ]

def regularizedPowerMeanProduct (ε L : ℝ) (k : κ → ℕ)
    (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (a b : κ → ι → ℝ) (X : SymmetricMatrix p) : ℝ :=
  ∏ i, regularizedAffinePowerMean ε L (B i) (M i) (a i) (b i) X

theorem hasTemperateGrowth_regularizedPowerMeanProduct {ε L : ℝ}
    (hε : 0 < ε) (hL : 0 < L) (k : κ → ℕ)
    (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (a b : κ → ι → ℝ) (ha : ∀ i j, 0 ≤ a i j) :
    (regularizedPowerMeanProduct ε L k B M a b).HasTemperateGrowth :=
  hasTemperateGrowth_finset_prod Finset.univ _ (fun i _ =>
    hasTemperateGrowth_regularizedAffinePowerMean hε hL (B i) (M i) (a i) (b i) (ha i))

theorem regularizedPowerMeanProduct_generator_nonneg {ε L : ℝ}
    (hε : 0 < ε) (hL : 0 < L) (k : κ → ℕ)
    (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (a b : κ → ι → ℝ) (hB : ∀ i, (B i).PosSemidef)
    (ha : ∀ i j, 0 ≤ a i j)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    {N : ℝ} (hN : ∀ i, min (k i : ℝ) (p : ℝ) + 1 ≤ N)
    (v : EuclideanSpace ℝ (Fin p)) :
    0 ≤ symmetricRadialGenerator N v (regularizedPowerMeanProduct ε L k B M a b) X := by
  let g : κ → SymmetricMatrix p → ℝ := fun i =>
    affinePowerMeanLog ε L (B i) (M i) (a i) (b i)
  have hunit (i : κ) : IsUnit (regularizedCompression ε (B i) (M i) X).det :=
    isUnit_iff_ne_zero.mpr (regularizedCompression_posDef hε (hB i) (M i) hX).det_pos.ne'
  have hg : ∀ᶠ Y in 𝓝 X, ∀ i, DifferentiableAt ℝ (g i) Y :=
    Filter.eventually_all.mpr fun i =>
      affinePowerMeanLog_differentiable_near ε L (B i) (M i) (a i) (b i) (hunit i)
  have hD (i : κ) (H : SymmetricMatrix p) :
      DifferentiableAt ℝ (fun Y => fderiv ℝ (g i) Y H) X :=
    affinePowerMeanLog_direction_differentiable ε L (B i) (M i) (a i) (b i) (hunit i) H
  have hsumnear : ∀ᶠ Y in 𝓝 X, DifferentiableAt ℝ (fun Z => ∑ i, g i Z) Y := by
    filter_upwards [hg] with Y hY
    exact DifferentiableAt.fun_sum (fun i _ => hY i)
  have hsumD (H : SymmetricMatrix p) :
      DifferentiableAt ℝ (fun Y => fderiv ℝ (fun Z => ∑ i, g i Z) Y H) X := by
    have heq : (fun Y => fderiv ℝ (fun Z => ∑ i, g i Z) Y H) =ᶠ[𝓝 X]
        (fun Y => ∑ i, fderiv ℝ (g i) Y H) := by
      filter_upwards [hg] with Y hY
      simpa only [one_mul] using
        fderiv_linear_combination_apply (fun _ : κ => (1 : ℝ)) g hY H
    exact heq.differentiableAt_iff.mpr (DifferentiableAt.fun_sum (fun i _ => hD i H))
  have heq : regularizedPowerMeanProduct ε L k B M a b =ᶠ[𝓝 X]
      (fun Y => Real.exp (∑ i, g i Y)) := by
    have heach : ∀ᶠ Y in 𝓝 X, ∀ i,
        regularizedAffinePowerMean ε L (B i) (M i) (a i) (b i) Y = Real.exp (g i Y) :=
      Filter.eventually_all.mpr fun i =>
        regularizedAffinePowerMean_eventually_exp_log hε hL (hB i) (M i) (a i) (b i) hX
    filter_upwards [heach] with Y hY
    simp only [regularizedPowerMeanProduct, hY, Real.exp_sum]
  rw [symmetricRadialGenerator_eq_directional
    (hasTemperateGrowth_regularizedPowerMeanProduct hε hL k B M a b ha),
    symmetricDirectionalGenerator_congr heq,
    symmetricDirectionalGenerator_exp hsumnear hsumD]
  apply mul_nonneg (Real.exp_pos _).le
  apply add_nonneg _ (symmetricCarreDuChamp_nonneg _ hX v)
  have hsum := symmetricDirectionalGenerator_linear_combination
    (fun _ : κ => (1 : ℝ)) g hg hD N v
  simp only [one_mul] at hsum
  rw [hsum]
  apply Finset.sum_nonneg
  intro i hi
  exact affinePowerMeanLog_generator_nonneg hε hL (hB i) (M i) (a i) (b i) (ha i) hX
    (by simpa only [Fintype.card_fin] using hN i) v

end Products

end WishartVerification
end
end CanonicalSource33

section CanonicalSource34
/- Source: Wishart/FinitePowerMeans.lean -/



/-!
# The finite power-mean limit

The estimates retain the cardinality normalization. They apply to arbitrary
finite nonempty families of nonnegative real values, including families that
vanish. The limiting maximum is the actual finite maximum.
-/

noncomputable section

open Filter Topology
open scoped BigOperators

namespace WishartVerification

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def finiteMaximum (x : ι → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty x

def finitePowerMean (L : ℝ) (x : ι → ℝ) : ℝ :=
  ((∑ i, x i ^ L) / Fintype.card ι) ^ (1 / L)

theorem le_finiteMaximum (x : ι → ℝ) (i : ι) : x i ≤ finiteMaximum x :=
  Finset.le_sup' x (Finset.mem_univ i)

theorem finiteMaximum_le {x : ι → ℝ} {b : ℝ} (h : ∀ i, x i ≤ b) :
    finiteMaximum x ≤ b :=
  Finset.sup'_le Finset.univ_nonempty x (fun i _ => h i)

theorem finiteMaximum_nonneg {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) :
    0 ≤ finiteMaximum x := by
  let i : ι := Classical.choice inferInstance
  exact (hx i).trans (le_finiteMaximum x i)

theorem finiteMaximum_pos {x : ι → ℝ} (hx : ∀ i, 0 < x i) :
    0 < finiteMaximum x := by
  let i : ι := Classical.choice inferInstance
  exact (hx i).trans_le (le_finiteMaximum x i)

theorem finiteMaximum_le_sum {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) :
    finiteMaximum x ≤ ∑ i, x i :=
  finiteMaximum_le fun i => Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)

theorem finiteMaximum_mono {x y : ι → ℝ} (h : ∀ i, x i ≤ y i) :
    finiteMaximum x ≤ finiteMaximum y :=
  Finset.sup'_mono_fun (fun i _ => h i)

theorem continuous_finiteMaximum {E : Type*} [TopologicalSpace E]
    {x : ι → E → ℝ} (hx : ∀ i, Continuous (x i)) :
    Continuous (fun z => finiteMaximum (fun i => x i z)) :=
  Continuous.finset_sup'_apply Finset.univ_nonempty (fun i _ => hx i)

theorem finitePowerMean_nonneg {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (L : ℝ) :
    0 ≤ finitePowerMean L x :=
  Real.rpow_nonneg (div_nonneg (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hx i) L))
    (by positivity)) _

theorem finitePowerMean_pos {x : ι → ℝ} (hx : ∀ i, 0 < x i) (L : ℝ) :
    0 < finitePowerMean L x :=
  Real.rpow_pos_of_pos (div_pos
    (Finset.sum_pos (fun i _ => Real.rpow_pos_of_pos (hx i) L) Finset.univ_nonempty)
    (Nat.cast_pos.mpr Fintype.card_pos)) _

theorem finitePowerMean_le_max {L : ℝ} (hL : 0 < L)
    {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) :
    finitePowerMean L x ≤ finiteMaximum x := by
  have hc : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hM : 0 ≤ finiteMaximum x := finiteMaximum_nonneg hx
  have hsum : (∑ i, x i ^ L) ≤ (Fintype.card ι : ℝ) * finiteMaximum x ^ L := by
    calc
      _ ≤ ∑ _i : ι, finiteMaximum x ^ L :=
        Finset.sum_le_sum (fun i _ => Real.rpow_le_rpow (hx i) (le_finiteMaximum x i) hL.le)
      _ = _ := by simp
  have havg : (∑ i, x i ^ L) / Fintype.card ι ≤ finiteMaximum x ^ L :=
    (div_le_iff₀ hc).mpr (by simpa only [mul_comm] using hsum)
  calc
    finitePowerMean L x ≤ (finiteMaximum x ^ L) ^ (1 / L) :=
      Real.rpow_le_rpow
        (div_nonneg (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hx i) L)) hc.le)
        havg (one_div_nonneg.mpr hL.le)
    _ = finiteMaximum x := by
      rw [one_div, Real.rpow_rpow_inv hM hL.ne']

theorem max_div_card_rpow_le_finitePowerMean {L : ℝ} (hL : 0 < L)
    {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) :
    finiteMaximum x / (Fintype.card ι : ℝ) ^ (1 / L) ≤ finitePowerMean L x := by
  have hc : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hM : 0 ≤ finiteMaximum x := finiteMaximum_nonneg hx
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty x
  have hterm : finiteMaximum x ^ L ≤ ∑ j, x j ^ L := by
    change (Finset.univ.sup' Finset.univ_nonempty x) ^ L ≤ _
    rw [hmax]
    exact Finset.single_le_sum (fun j _ => Real.rpow_nonneg (hx j) L) hi
  have havg := div_le_div_of_nonneg_right hterm hc.le
  have hp := Real.rpow_le_rpow
    (div_nonneg (Real.rpow_nonneg hM L) hc.le) havg (one_div_nonneg.mpr hL.le)
  calc
    finiteMaximum x / (Fintype.card ι : ℝ) ^ (1 / L) =
        (finiteMaximum x ^ L / Fintype.card ι) ^ (1 / L) := by
      rw [Real.div_rpow (Real.rpow_nonneg hM L) hc.le, one_div,
        Real.rpow_rpow_inv hM hL.ne']
    _ ≤ finitePowerMean L x := hp

theorem finitePowerMean_tendsto_max {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) :
    Tendsto (fun n : ℕ => finitePowerMean ((n : ℝ) + 1) x)
      atTop (𝓝 (finiteMaximum x)) := by
  have hc : (Fintype.card ι : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (Fintype.card_pos (α := ι))).ne'
  have hdenom : Tendsto (fun n : ℕ => (Fintype.card ι : ℝ) ^ (1 / ((n : ℝ) + 1)))
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [Real.rpow_zero] using
      (tendsto_const_nhds (x := (Fintype.card ι : ℝ))).rpow
        tendsto_one_div_add_atTop_nhds_zero_nat (Or.inl hc)
  have hlower : Tendsto
      (fun n : ℕ => finiteMaximum x / (Fintype.card ι : ℝ) ^ (1 / ((n : ℝ) + 1)))
      atTop (𝓝 (finiteMaximum x)) := by
    have h := (tendsto_const_nhds (x := finiteMaximum x) :
      Tendsto (fun _ : ℕ => finiteMaximum x) atTop (𝓝 (finiteMaximum x))).div
        hdenom one_ne_zero
    change Tendsto
      (fun n : ℕ => finiteMaximum x / (Fintype.card ι : ℝ) ^ (1 / ((n : ℝ) + 1)))
      atTop (𝓝 (finiteMaximum x / 1)) at h
    simpa only [div_one] using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
    (fun n => max_div_card_rpow_le_finitePowerMean (by positivity) hx)
    (fun n => finitePowerMean_le_max (by positivity) hx)

theorem monomial_power_eq (x : ℝ) (hx : 0 ≤ x) (a b L : ℝ) :
    (Real.exp b * x ^ a) ^ L = Real.exp (L * b) * x ^ (L * a) := by
  rw [Real.mul_rpow (Real.exp_pos _).le (Real.rpow_nonneg hx _), ← Real.exp_mul,
    ← Real.rpow_mul hx]
  congr 1 <;> ring

end WishartVerification
end
end CanonicalSource34

section CanonicalSource35
/- Source: Wishart/PowerMeanIntegration.lean -/



/-!
# Integrating finite power-mean limits

The domination is a product of finite sums of the original monomials. It is
independent of the power-mean exponent. All needed moments are explicitly
derived from the moments of these monomials.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators

namespace WishartVerification

variable {Ω κ ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  [Fintype κ] [Fintype ι] [Nonempty ι]

theorem hasAllFiniteMoments_finiteMaximum (x : ι → Ω → ℝ)
    (hx : ∀ i, HasAllFiniteMoments (x i) μ) :
    HasAllFiniteMoments (fun z => finiteMaximum (fun i => x i z)) μ := by
  classical
  have hb : HasAllFiniteMoments (fun z => ∑ i, ‖x i z‖) μ :=
    HasAllFiniteMoments.finset_sum Finset.univ _ (fun i _ p hp => (hx i p hp).norm)
  have hxm : AEMeasurable (fun z i => x i z) μ :=
    aemeasurable_pi_iff.mpr fun i => (hx i).integrable.aemeasurable
  have hmaxc : Continuous (fun y : ι → ℝ => finiteMaximum y) :=
    continuous_finiteMaximum (fun i => continuous_apply i)
  intro p hp
  apply (hb p hp).mono'
  · exact (hmaxc.measurable.comp_aemeasurable hxm).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z => by
      obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup'
        (Finset.univ_nonempty (α := ι)) (fun i => x i z)
      change ‖(Finset.univ.sup' Finset.univ_nonempty (fun i => x i z))‖ ≤ _
      rw [heq]
      exact Finset.single_le_sum (f := fun j : ι => ‖x j z‖)
        (fun j _ => norm_nonneg (x j z)) hi

theorem hasAllFiniteMoments_finitePowerMean {L : ℝ} (hL : 0 < L)
    (x : ι → Ω → ℝ) (hx : ∀ i, HasAllFiniteMoments (x i) μ) :
    HasAllFiniteMoments (fun z => finitePowerMean L (fun i => x i z)) μ := by
  have hsum := HasAllFiniteMoments.finset_sum Finset.univ
    (fun i z => x i z ^ L) (fun i _ => (hx i).rpow hL.le)
  have havg := hsum.const_mul (Fintype.card ι : ℝ)⁻¹
  have h := havg.rpow (one_div_nonneg.mpr hL.le)
  simpa only [finitePowerMean, div_eq_mul_inv, mul_comm] using h

theorem powerMeanProduct_integral_tendsto (x : κ → ι → Ω → ℝ)
    (hx : ∀ i j, HasAllFiniteMoments (x i j) μ)
    (hpos : ∀ᵐ z ∂μ, ∀ i j, 0 ≤ x i j z) :
    Tendsto (fun n : ℕ => ∫ z, ∏ i,
      finitePowerMean ((n : ℝ) + 1) (fun j => x i j z) ∂μ) atTop
      (𝓝 (∫ z, ∏ i, finiteMaximum (fun j => x i j z) ∂μ)) := by
  classical
  let bound : Ω → ℝ := fun z => ∏ i, ∑ j, x i j z
  have hb : HasAllFiniteMoments bound μ :=
    HasAllFiniteMoments.finset_prod Finset.univ _ (fun i _ =>
      HasAllFiniteMoments.finset_sum Finset.univ _ (fun j _ => hx i j))
  have hm (n : ℕ) : HasAllFiniteMoments
      (fun z => ∏ i, finitePowerMean ((n : ℝ) + 1) (fun j => x i j z)) μ :=
    HasAllFiniteMoments.finset_prod Finset.univ _ (fun i _ =>
      hasAllFiniteMoments_finitePowerMean (by positivity) (x i) (hx i))
  apply tendsto_integral_of_dominated_convergence bound
    (fun n => (hm n).integrable.aestronglyMeasurable) hb.integrable
  · intro n
    filter_upwards [hpos] with z hz
    rw [norm_prod]
    apply Finset.prod_le_prod₀
    · intro i hi
      exact norm_nonneg _
    · intro i hi
      rw [Real.norm_of_nonneg (finitePowerMean_nonneg (hz i) _)]
      exact (finitePowerMean_le_max (by positivity) (hz i)).trans (finiteMaximum_le_sum (hz i))
  · filter_upwards [hpos] with z hz
    exact tendsto_finsetProd _ (fun i _ => finitePowerMean_tendsto_max (hz i))

end WishartVerification
end
end CanonicalSource35

section CanonicalSource36
/- Source: Wishart/FiniteOuterProducts.lean -/



/-!
# Finite supporting-plane products on the positive matrix cone

The logarithmic maximum is represented by an actual finite maximum of
determinant monomials. Power-mean limits are taken under the actual noise
measure, with a common integrable bound supplied by the preceding module.
-/

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped BigOperators Matrix.Norms.Operator

namespace WishartVerification

variable {p : ℕ} {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]

def affineMaximumProduct (ε : ℝ) (k : κ → ℕ)
    (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (a b : κ → ι → ℝ) (X : SymmetricMatrix p) : ℝ :=
  ∏ i, finiteMaximum (fun j => Real.exp (b i j) *
    (regularizedCompression ε (B i) (M i) X).det ^ (a i j))

theorem regularizedAffinePowerMean_eq_finitePowerMean
    {k : Type*} [Fintype k] [DecidableEq k] {ε : ℝ} (hε : 0 < ε)
    (L : ℝ) {B : Matrix k k ℝ} (hB : B.PosSemidef)
    (M : Matrix (Fin p) k ℝ) (a b : ι → ℝ)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    regularizedAffinePowerMean ε L B M a b X =
      finitePowerMean L (fun j => Real.exp (b j) *
        (regularizedCompression ε B M X).det ^ (a j)) := by
  have hdet : 0 ≤ (regularizedCompression ε B M X).det :=
    (regularizedCompression_posDef hε hB M hX).det_pos.le
  unfold regularizedAffinePowerMean regularizedAffinePowerSum finitePowerMean
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  rw [smoothRegularizedDetPower_eq hε _ hB M hX, monomial_power_eq _ hdet]

theorem continuous_affineMaximumProduct (ε : ℝ) (k : κ → ℕ)
    (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (a b : κ → ι → ℝ) (ha : ∀ i j, 0 ≤ a i j) :
    Continuous (affineMaximumProduct ε k B M a b) := by
  apply continuous_finsetProd
  intro i hi
  apply continuous_finiteMaximum
  intro j
  exact continuous_const.mul ((Real.continuous_rpow_const (ha i j)).comp
    (hasTemperateGrowth_regularizedCompression_det ε (B i) (M i)).1.continuous)

theorem regularizedPowerMeanProduct_integral_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ε : ℝ} (hε : 0 < ε) (k : κ → ℕ)
    (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (a b : κ → ι → ℝ) (hB : ∀ i, (B i).PosSemidef)
    (Z : Ω → SymmetricMatrix p)
    (hZ : ∀ᵐ z ∂μ, (Z z : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (hmom : ∀ i j, HasAllFiniteMoments (fun z => Real.exp (b i j) *
      (regularizedCompression ε (B i) (M i) (Z z)).det ^ (a i j)) μ) :
    Tendsto (fun n : ℕ => ∫ z,
      regularizedPowerMeanProduct ε ((n : ℝ) + 1) k B M a b (Z z) ∂μ) atTop
      (𝓝 (∫ z, affineMaximumProduct ε k B M a b (Z z) ∂μ)) := by
  let x : κ → ι → Ω → ℝ := fun i j z => Real.exp (b i j) *
    (regularizedCompression ε (B i) (M i) (Z z)).det ^ (a i j)
  have hpos : ∀ᵐ z ∂μ, ∀ i j, 0 ≤ x i j z := by
    filter_upwards [hZ] with z hz i j
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg
      (regularizedCompression_posDef hε (hB i) (M i) hz).det_pos.le _)
  have hlim := powerMeanProduct_integral_tendsto x hmom hpos
  have heq (n : ℕ) : (∫ z, ∏ i, finitePowerMean ((n : ℝ) + 1) (fun j => x i j z) ∂μ) =
      ∫ z, regularizedPowerMeanProduct ε ((n : ℝ) + 1) k B M a b (Z z) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hZ] with z hz
    unfold regularizedPowerMeanProduct
    apply Finset.prod_congr rfl
    intro i hi
    exact (regularizedAffinePowerMean_eq_finitePowerMean hε _ (hB i) (M i) (a i) (b i) hz).symm
  simpa only [heq, affineMaximumProduct, x] using hlim

theorem monomialMoments_of_temperate_matrix
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasure μ]
    (hμ : HasAllFiniteMoments (fun z : E => ‖z‖) μ)
    {Z : E → SymmetricMatrix p} (hZ : Z.HasTemperateGrowth)
    (ε : ℝ) (k : κ → ℕ)
    (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (a b : κ → ι → ℝ) (ha : ∀ i j, 0 ≤ a i j) :
    ∀ i j, HasAllFiniteMoments (fun z => Real.exp (b i j) *
      (regularizedCompression ε (B i) (M i) (Z z)).det ^ (a i j)) μ := by
  intro i j
  have hdet : HasAllFiniteMoments
      (fun z => (regularizedCompression ε (B i) (M i) (Z z)).det) μ :=
    fun q hq => memLp_temperate_of_allNormMoments hμ
      ((hasTemperateGrowth_regularizedCompression_det ε (B i) (M i)).comp hZ) hq
  exact (hdet.rpow (ha i j)).const_mul (Real.exp (b i j))

end WishartVerification

namespace Wishart

open WishartVerification

/-- At fixed regularization, the whole product of finite supporting-plane
maxima is monotone under the genuine real-shape transverse regression law. -/
theorem monotoneOn_scalarRadial_affineMaximumProduct
    {r : ℕ} {N ε : ℝ} (hN : (r : ℝ) < N) (hε : 0 < ε)
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin (1 + r)) (Fin (k i)) ℝ)
    (a b : κ → ι → ℝ) (hB : ∀ i, (B i).PosSemidef)
    (ha : ∀ i j, 0 ≤ a i j)
    (hsize : ∀ i, min (k i : ℝ) ((1 + r : ℕ) : ℝ) + 1 ≤ N) :
    MonotoneOn (fun t : ℝ => ∫ z : ScalarRegressionNoise r,
      affineMaximumProduct ε k B M a b (scalarRadialMatrix (Real.sqrt t) z)
        ∂scalarRegressionNoiseMeasure N r) (Set.Ici 0) := by
  letI := isProbabilityMeasure_scalarRegressionNoiseMeasure hN
  have hm (n : ℕ) := monotoneOn_scalarRadialProfile_of_generator_nonneg hN
    (hasTemperateGrowth_regularizedPowerMeanProduct hε (by positivity : 0 < (n : ℝ) + 1)
      k B M a b ha)
    (fun X hX => regularizedPowerMeanProduct_generator_nonneg hε (by positivity)
      k B M a b hB ha hX hsize (scalarTransverseAxis r))
  have hlimit (s : ℝ) := regularizedPowerMeanProduct_integral_tendsto hε k B M a b hB
    (scalarRadialMatrix s) (ae_scalarRadialMatrix_posSemidef N s)
    (monomialMoments_of_temperate_matrix (allFiniteNormMoments_scalarRegressionNoise hN)
      ((hasTemperateGrowth_scalarRadialMatrix r).comp
        (hasTemperateGrowth_prodMk (Function.HasTemperateGrowth.const s)
          Function.HasTemperateGrowth.id)) ε k B M a b ha)
  intro s hs t ht hst
  exact le_of_tendsto_of_tendsto (hlimit (Real.sqrt s)) (hlimit (Real.sqrt t))
    (Filter.Eventually.of_forall fun n => hm n hs ht hst)

end Wishart
end
end CanonicalSource36

section CanonicalSource37
/- Source: Wishart/OuterMatrixMoments.lean -/



/-! # Finite outer tests under matrix laws with all entry moments -/

noncomputable section

open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.Operator

namespace WishartVerification

variable {p : ℕ} {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]

theorem allFiniteMoments_affineMaximumProduct_of_entries
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (ε : ℝ) (k : κ → ℕ)
    (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (a b : κ → ι → ℝ) (ha : ∀ i j, 0 ≤ a i j)
    (X : Ω → SymmetricMatrix p)
    (hX : ∀ i j, HasAllFiniteMoments
      (fun z => (X z : Matrix (Fin p) (Fin p) ℝ) i j) μ) :
    HasAllFiniteMoments (fun z => affineMaximumProduct ε k B M a b (X z)) μ := by
  apply HasAllFiniteMoments.finset_prod Finset.univ
  intro i hi
  apply hasAllFiniteMoments_finiteMaximum
  intro j
  apply HasAllFiniteMoments.const_mul
  apply HasAllFiniteMoments.rpow _ (ha i j)
  apply HasAllFiniteMoments.det
  intro u v
  change HasAllFiniteMoments
    (fun z => ((B i) u v + ((M i)ᵀ * (X z : Matrix (Fin p) (Fin p) ℝ) * M i) u v) +
      (ε • (1 : Matrix (Fin (k i)) (Fin (k i)) ℝ)) u v) μ
  apply HasAllFiniteMoments.add _ (HasAllFiniteMoments.const _)
  apply (HasAllFiniteMoments.const _).add
  exact HasAllFiniteMoments.matrix_right_mul_entry _ (M i)
    (fun u v => HasAllFiniteMoments.matrix_left_mul_entry _ (M i)ᵀ hX u v) u v

theorem affineMaximumProduct_zero_nonneg
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (a b : κ → ι → ℝ)
    (hB : ∀ i, (B i).PosSemidef)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    0 ≤ affineMaximumProduct 0 k B M a b X := by
  apply Finset.prod_nonneg
  intro i hi
  apply finiteMaximum_nonneg
  intro j
  apply mul_nonneg (Real.exp_pos _).le
  apply Real.rpow_nonneg
  have hc : ((M i)ᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * M i).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hX.conjTranspose_mul_mul_same (M i)
  simpa only [regularizedCompression, compressionCLM_apply, zero_smul, add_zero] using
    ((hB i).add hc).det_nonneg

theorem affineMaximumProduct_add_offset
    (ε : ℝ) (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (a b : κ → ι → ℝ)
    (A X : SymmetricMatrix p) :
    affineMaximumProduct ε k B M a b (A + X) =
      affineMaximumProduct ε k
        (fun i => B i + (M i)ᵀ * (A : Matrix (Fin p) (Fin p) ℝ) * M i)
        M a b X := by
  unfold affineMaximumProduct
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  funext j
  congr 2
  simp only [regularizedCompression, compressionCLM_apply, Submodule.coe_add,
    Matrix.mul_add, Matrix.add_mul, add_assoc]

end WishartVerification
end
end CanonicalSource37

section CanonicalSource38
/- Source: Wishart/FiniteOuterRegularization.lean -/



/-!
# Removing regularization from finite convex outer approximations

The maximum and product bounds are uniform in epsilon. The resulting comparison
uses ordinary determinant monomials and is valid also at singular matrices.
Passage to the final positive-argument outer functions is a separate limit.
-/

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped BigOperators Matrix.Norms.Operator

namespace WishartVerification

variable {p : ℕ} {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]

theorem continuous_affineMaximumProduct_parameter (k : κ → ℕ)
    (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (a b : κ → ι → ℝ) (ha : ∀ i j, 0 ≤ a i j) (X : SymmetricMatrix p) :
    Continuous (fun ε : ℝ => affineMaximumProduct ε k B M a b X) := by
  apply continuous_finsetProd
  intro i hi
  apply continuous_finiteMaximum
  intro j
  exact continuous_const.mul ((Real.continuous_rpow_const (ha i j)).comp
    (show Continuous (fun ε : ℝ => (regularizedCompression ε (B i) (M i) X).det) from by
      unfold regularizedCompression
      fun_prop))

theorem hasTemperateGrowth_parameter_regularized_det
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Z : E → SymmetricMatrix p} (hZ : Z.HasTemperateGrowth)
    {k : Type*} [Fintype k] [DecidableEq k]
    (B : Matrix k k ℝ) (M : Matrix (Fin p) k ℝ) :
    (fun z : ℝ × E => (regularizedCompression z.1 B M (Z z.2)).det).HasTemperateGrowth := by
  have hinput := hZ.comp (ContinuousLinearMap.snd ℝ ℝ E).hasTemperateGrowth
  have hε := (ContinuousLinearMap.fst ℝ ℝ E).hasTemperateGrowth
  apply hasTemperateGrowth_matrix_det
  intro i j
  let L : SymmetricMatrix p →L[ℝ] ℝ :=
    (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℝ i j)).comp (compressionCLM M)
  exact ((Function.HasTemperateGrowth.const (B i j)).add (L.hasTemperateGrowth.comp hinput)).add
    (hε.mul (Function.HasTemperateGrowth.const ((1 : Matrix k k ℝ) i j)))

theorem affineMaximumProduct_regularization_integral_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsFiniteMeasure μ]
    (hμ : HasAllFiniteMoments (fun z : E => ‖z‖) μ)
    {Z : E → SymmetricMatrix p} (hZ : Z.HasTemperateGrowth)
    (hZpos : ∀ᵐ z ∂μ, (Z z : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (a b : κ → ι → ℝ) (hB : ∀ i, (B i).PosSemidef)
    (ha : ∀ i j, 0 ≤ a i j) :
    Tendsto (fun n : ℕ => ∫ z,
      affineMaximumProduct (determinantRegularization n) k B M a b (Z z) ∂μ) atTop
      (𝓝 (∫ z, affineMaximumProduct 0 k B M a b (Z z) ∂μ)) := by
  classical
  have hpoly (i : κ) := norm_temperate_uniform_parameter
    (hasTemperateGrowth_parameter_regularized_det hZ (B i) (M i)) 0
  choose d A hA hbound using hpoly
  let monomialBound : κ → ι → E → ℝ := fun i j z =>
    Real.exp (b i j) * (A i * (1 + ‖z‖) ^ d i) ^ (a i j)
  let bound : E → ℝ := fun z => ∏ i, ∑ j, monomialBound i j z
  have hmoment (i : κ) (j : ι) : HasAllFiniteMoments (monomialBound i j) μ := by
    have hpow := ((HasAllFiniteMoments.const (μ := μ) 1).add hμ).rpow
      (show 0 ≤ (d i : ℝ) by positivity)
    have hpolyMom : HasAllFiniteMoments (fun z : E => A i * (1 + ‖z‖) ^ d i) μ := by
      simpa only [Real.rpow_natCast] using hpow.const_mul (A i)
    exact (hpolyMom.rpow (ha i j)).const_mul (Real.exp (b i j))
  have hboundMom : HasAllFiniteMoments bound μ :=
    HasAllFiniteMoments.finset_prod Finset.univ _ (fun i _ =>
      HasAllFiniteMoments.finset_sum Finset.univ _ (fun j _ => hmoment i j))
  refine tendsto_integral_of_dominated_convergence bound ?_ hboundMom.integrable ?_ ?_
  · intro n
    exact ((continuous_affineMaximumProduct (determinantRegularization n) k B M a b ha).comp
      hZ.1.continuous).aestronglyMeasurable
  · intro n
    filter_upwards [hZpos] with z hz
    rw [affineMaximumProduct, norm_prod]
    apply Finset.prod_le_prod₀
    · intro i hi
      exact norm_nonneg _
    · intro i hi
      have hd : 0 ≤ (regularizedCompression (determinantRegularization n) (B i) (M i) (Z z)).det :=
        (regularizedCompression_posDef (determinantRegularization_pos n) (hB i) (M i) hz).det_pos.le
      have hval (j : ι) : 0 ≤ Real.exp (b i j) *
          (regularizedCompression (determinantRegularization n) (B i) (M i) (Z z)).det ^ (a i j) :=
        mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hd _)
      rw [Real.norm_of_nonneg (finiteMaximum_nonneg hval)]
      have heps : determinantRegularization n ∈ Set.Icc ((0 : ℝ) - 1) (0 + 1) :=
        ⟨by linarith [determinantRegularization_pos n],
          by simpa only [zero_add] using determinantRegularization_le_one n⟩
      have hdBound : (regularizedCompression (determinantRegularization n) (B i) (M i) (Z z)).det ≤
          A i * (1 + ‖z‖) ^ d i := by
        simpa only [Real.norm_of_nonneg hd] using hbound i _ heps z
      calc
        _ ≤ finiteMaximum (fun j => monomialBound i j z) :=
          finiteMaximum_mono fun j => mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow hd hdBound (ha i j)) (Real.exp_pos _).le
        _ ≤ ∑ j, monomialBound i j z := finiteMaximum_le_sum fun j =>
          mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (mul_nonneg (hA i) (by positivity)) _)
  · exact Filter.Eventually.of_forall fun z =>
      (continuous_affineMaximumProduct_parameter k B M a b ha (Z z)).continuousAt.tendsto.comp
        tendsto_determinantRegularization

theorem affineMaximumProduct_congruence {r : ℕ} (ε : ℝ) (k : κ → ℕ)
    (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (a b : κ → ι → ℝ)
    (L : Matrix (Fin p) (Fin r) ℝ) (X : SymmetricMatrix r) :
    affineMaximumProduct ε k B M a b (Matrix.symmetricCongruenceLinearMap L X) =
      affineMaximumProduct ε k B (fun i => Lᵀ * M i) a b X := by
  unfold affineMaximumProduct
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  funext j
  congr 2
  simp only [regularizedCompression, compressionCLM_apply,
    Matrix.coe_symmetricCongruenceLinearMap_apply, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.mul_assoc]

end WishartVerification

namespace Wishart

open WishartVerification

theorem monotoneOn_scalarRadial_finiteOuterProduct
    {r : ℕ} {N : ℝ} (hN : (r : ℝ) < N)
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin (1 + r)) (Fin (k i)) ℝ)
    (a b : κ → ι → ℝ) (hB : ∀ i, (B i).PosSemidef)
    (ha : ∀ i j, 0 ≤ a i j)
    (hsize : ∀ i, min (k i : ℝ) ((1 + r : ℕ) : ℝ) + 1 ≤ N) :
    MonotoneOn (fun t : ℝ => ∫ z : ScalarRegressionNoise r,
      affineMaximumProduct 0 k B M a b (scalarRadialMatrix (Real.sqrt t) z)
        ∂scalarRegressionNoiseMeasure N r) (Set.Ici 0) := by
  letI := isProbabilityMeasure_scalarRegressionNoiseMeasure hN
  have hlimit (s : ℝ) := affineMaximumProduct_regularization_integral_tendsto
    (allFiniteNormMoments_scalarRegressionNoise hN)
    ((hasTemperateGrowth_scalarRadialMatrix r).comp
      (hasTemperateGrowth_prodMk (Function.HasTemperateGrowth.const s)
        Function.HasTemperateGrowth.id))
    (ae_scalarRadialMatrix_posSemidef N s) k B M a b hB ha
  intro s hs t ht hst
  exact le_of_tendsto_of_tendsto (hlimit (Real.sqrt s)) (hlimit (Real.sqrt t))
    (Filter.Eventually.of_forall fun n =>
      monotoneOn_scalarRadial_affineMaximumProduct hN (determinantRegularization_pos n)
        k B M a b hB ha hsize hs ht hst)

/-- The finite convex outer approximation after an arbitrary rectangular
linear image. The exact smaller-dimension bound survives this transport. -/
theorem monotoneOn_linearRadial_finiteOuterProduct
    {p r : ℕ} {N : ℝ} (hN : (r : ℝ) < N)
    (L : Matrix (Fin p) (Fin r) ℝ) (v : EuclideanSpace ℝ (Fin p))
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (a b : κ → ι → ℝ) (hB : ∀ i, (B i).PosSemidef)
    (ha : ∀ i j, 0 ≤ a i j)
    (hsize : ∀ i, min (k i : ℝ) ((1 + r : ℕ) : ℝ) + 1 ≤ N) :
    MonotoneOn (fun t : ℝ => ∫ z : ScalarRegressionNoise r,
      affineMaximumProduct 0 k B M a b (linearRadialInput L v (Real.sqrt t) z)
        ∂scalarRegressionNoiseMeasure N r) (Set.Ici 0) := by
  have heq (t : ℝ) (z : ScalarRegressionNoise r) :
      affineMaximumProduct 0 k B M a b (linearRadialInput L v (Real.sqrt t) z) =
        affineMaximumProduct 0 k B
          (fun i => (radialLiftMatrix v L)ᵀ * M i) a b (scalarRadialMatrix (Real.sqrt t) z) := by
    rw [← radialLiftMatrix_scalarRadialMatrix, affineMaximumProduct_congruence]
  simpa only [heq] using monotoneOn_scalarRadial_finiteOuterProduct hN k B
    (fun i => (radialLiftMatrix v L)ᵀ * M i) a b hB ha hsize

end Wishart
end
end CanonicalSource38

section CanonicalSource39
/- Source: Wishart/OuterRegressionMonotonicity.lean -/



/-!
# Finite outer tests under the full conditional matrix law

Every entry of the full matrix is retained. Separating one Gaussian row reduces
the comparison to the actual transverse radial law. The remaining rows become
a positive semidefinite offset. No disjointness of the compressed matrices is
used.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart

theorem monotoneOn_linearShiftedRows_finiteOuter_coordinate
    {q m p : ℕ} {ν : ℝ} (hν : (m : ℝ) - 1 < ν)
    (L : Matrix (Fin p) (Fin m) ℝ)
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (a b : κ → ι → ℝ)
    (hB : ∀ i, (B i).PosSemidef) (ha : ∀ i j, 0 ≤ a i j)
    (hsize : ∀ i, min (k i : ℝ) (((1 + m : ℕ) : ℝ)) + 1 ≤ ν + 1)
    (v : Fin q → EuclideanSpace ℝ (Fin p)) (lam : Fin q → ℝ) (c : Fin q) :
    MonotoneOn (fun t : ℝ => ∫ x,
      affineMaximumProduct 0 k B M a b (linearShiftedRowsSym L v (Function.update lam c t) x)
        ∂gaussianResidualMeasure q 1 (nonsingularWishartMeasure ν 1)) (Set.Ici 0) := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure
    (S := (1 : Matrix (Fin m) (Fin m) ℝ)) Matrix.PosDef.one hν
  cases q with
  | zero => exact Fin.elim0 c
  | succ q =>
    let γ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) 1
    let μ := Measure.pi (fun _ : Fin q => γ)
    let ρ := scalarRegressionNoiseMeasure (ν + 1) m
    let A (z : Fin q → EuclideanSpace ℝ (Fin m)) :=
      rowBackground (v ∘ c.succAbove) (lam ∘ c.succAbove) (gaussianRowsLinearMap L z)
    let F (t : ℝ) (y : (Fin q → EuclideanSpace ℝ (Fin m)) × ScalarRegressionNoise m) :=
      affineMaximumProduct 0 k B M a b (A y.1 + linearRadialInput L (v c) (Real.sqrt t) y.2)
    have hsplit := measurePreserving_separateScalarRegressionRow (m := m) ν c
    have hFmeas (t : ℝ) : Measurable (F t) := by
      apply (continuous_affineMaximumProduct 0 k B M a b ha).measurable.comp
      apply Measurable.add
      · exact ((measurable_rowBackground _ _).comp
          (measurable_gaussianRowsLinearMap L)).comp measurable_fst
      · exact (measurable_linearRadialInput L (v c) (Real.sqrt t)).comp measurable_snd
    have hFcomp (t : ℝ) : F t ∘ separateScalarRegressionRow c =
        (fun x => affineMaximumProduct 0 k B M a b
          (linearShiftedRowsSym L v (Function.update lam c t) x)) := by
      funext x
      dsimp only [F, A, Function.comp_apply]
      rw [linearShiftedRowsSym_separate]
    have hFi (t : ℝ) : Integrable (F t) (μ.prod ρ) := by
      rw [← hsplit.map_eq]
      apply (integrable_map_measure (hFmeas t).aestronglyMeasurable
        hsplit.measurable.aemeasurable).mpr
      rw [hFcomp]
      apply HasAllFiniteMoments.integrable
      apply allFiniteMoments_affineMaximumProduct_of_entries 0 k B M a b ha
      exact allFiniteMoments_linearShiftedRowsSym_entry 1
        (fun i j => allFiniteMoments_wishart_entry (α := ν)
          (Sigma := (1 : Matrix (Fin m) (Fin m) ℝ)) i j)
        L v (Function.update lam c t)
    have heq (t : ℝ) :
        (∫ x, affineMaximumProduct 0 k B M a b
          (linearShiftedRowsSym L v (Function.update lam c t) x)
          ∂gaussianResidualMeasure (q + 1) 1 (nonsingularWishartMeasure ν 1)) =
        ∫ z, ∫ Y, F t (z, Y) ∂ρ ∂μ := by
      rw [← integral_prod _ (hFi t), ← hsplit.map_eq,
        integral_map hsplit.measurable.aemeasurable (hFmeas t).aestronglyMeasurable]
      exact congrArg (fun f => ∫ x, f x
        ∂gaussianResidualMeasure (q + 1) 1 (nonsingularWishartMeasure ν 1)) (hFcomp t).symm
    intro s hs t ht hst
    dsimp only
    rw [heq s, heq t]
    apply integral_mono_ae (hFi s).integral_prod_left (hFi t).integral_prod_left
    apply Filter.Eventually.of_forall
    intro z
    have hBz : ∀ i,
        (B i + (M i)ᵀ * (A z : Matrix (Fin p) (Fin p) ℝ) * M i).PosSemidef := by
      intro i
      apply (hB i).add
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        (rowBackground_posSemidef _ _ (gaussianRowsLinearMap L z)).conjTranspose_mul_mul_same (M i)
    have hN : (m : ℝ) < ν + 1 := by linarith
    simpa only [F, affineMaximumProduct_add_offset] using
      monotoneOn_linearRadial_finiteOuterProduct hN L (v c) k
        (fun i => B i + (M i)ᵀ * (A z : Matrix (Fin p) (Fin p) ℝ) * M i)
        M a b hBz ha hsize hs ht hst

theorem monotoneOn_linearShiftedRows_finiteOuter
    {q m p : ℕ} {ν : ℝ} (hν : (m : ℝ) - 1 < ν)
    (L : Matrix (Fin p) (Fin m) ℝ)
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (a b : κ → ι → ℝ)
    (hB : ∀ i, (B i).PosSemidef) (ha : ∀ i j, 0 ≤ a i j)
    (hsize : ∀ i, min (k i : ℝ) (((1 + m : ℕ) : ℝ)) + 1 ≤ ν + 1)
    (v : Fin q → EuclideanSpace ℝ (Fin p)) :
    MonotoneOn (fun lam : Fin q → ℝ => ∫ x,
      affineMaximumProduct 0 k B M a b (linearShiftedRowsSym L v lam x)
        ∂gaussianResidualMeasure q 1 (nonsingularWishartMeasure ν 1))
      (Set.Ici (0 : Fin q → ℝ)) :=
  monotoneOn_nonnegative_pi_of_update _ fun lam c =>
    monotoneOn_linearShiftedRows_finiteOuter_coordinate hν L k B M a b hB ha hsize v lam c

theorem monotoneOn_fullSpectralConditionalMoment_finiteOuter
    {q m : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Matrix (Fin q) (Fin q) ℝ)
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin (q + m)) (Fin (k i)) ℝ) (a b : κ → ι → ℝ)
    (hB : ∀ i, (B i).PosSemidef) (ha : ∀ i j, 0 ≤ a i j)
    (hsize : ∀ i, min (k i : ℝ) (((1 + m : ℕ) : ℝ)) + 1 ≤ n - q + 1) :
    MonotoneOn
      (fun lam => fullSpectralConditionalMoment n C K (affineMaximumProduct 0 k B M a b) lam O)
      (Set.Ici (0 : Fin q → ℝ)) := by
  have hν : (m : ℝ) - 1 < n - q := by
    push_cast at hn
    linarith
  simp_rw [fullSpectralConditionalMoment_standardNoise n hC K O _
    (continuous_affineMaximumProduct 0 k B M a b ha).measurable]
  exact monotoneOn_linearShiftedRows_finiteOuter hν
    (regressionNoiseInjection q m * CFC.sqrt C) k B M a b hB ha hsize
      (fullSpectralRegressionDirections K O)

end Wishart
end
end CanonicalSource39
