module

public import wishart.verified.field_frontier02
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import tau_ceti.probability.distributions.gaussian.chi_squared
public import Mathlib.Probability.Moments.IntegrableExpMul

/- Recovered canonical proof stage; see verification/recovery-patches.json. -/

@[expose] public section


section CanonicalSource24
/- Source: Wishart/NonnegativeRowIteration.lean -/



/-!
# From one random row to a finite product of rows

Tonelli is applied to the actual product measure, with no integrability
condition. A cone preserved by sums of row contributions keeps every
conditional background in the domain of the single-row comparison.
-/

noncomputable section
open MeasureTheory Set
open scoped Classical ENNReal
namespace WishartVerification

variable {Z E : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def shiftedRowSum {n : ℕ} (G : Z → E) (v : Fin n → Z)
    (lam : Fin n → ℝ) (z : Fin n → Z) : E :=
  ∑ a, G (z a + Real.sqrt (lam a) • v a)

theorem measurable_shiftedRowSum {n : ℕ} {G : Z → E} (hG : Measurable G)
    (v : Fin n → Z) (lam : Fin n → ℝ) : Measurable (shiftedRowSum G v lam) := by
  unfold shiftedRowSum
  apply Finset.measurable_sum
  intro a ha
  exact hG.comp ((measurable_pi_apply a).add measurable_const)

theorem shiftedRowSum_split {n : ℕ} (G : Z → E) (v : Fin (n + 1) → Z)
    (lam : Fin (n + 1) → ℝ) (a : Fin (n + 1)) (t : ℝ) (z : Fin (n + 1) → Z) :
    shiftedRowSum G v (Function.update lam a t) z =
      shiftedRowSum G (v ∘ a.succAbove) (lam ∘ a.succAbove) (z ∘ a.succAbove) +
        G (z a + Real.sqrt t • v a) := by
  unfold shiftedRowSum
  rw [Fin.sum_univ_succAbove _ a]
  simp only [Function.update_self, Function.update_of_ne (Fin.succAbove_ne _ _),
    Function.comp_apply]
  exact add_comm _ _

theorem shiftedRowSum_mem {n : ℕ} {P : E → Prop} (hzero : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y)) {G : Z → E}
    (hrow : ∀ z, P (G z)) (v : Fin n → Z) (lam : Fin n → ℝ) (z : Fin n → Z) :
    P (shiftedRowSum G v lam z) := by
  unfold shiftedRowSum
  exact Finset.sum_induction _ _ (fun x y hx hy => hadd x y hx hy)
    hzero (fun a ha => hrow _)

/-- The whole nonnegative orthant, including repeated and zero coordinates,
is covered. Neither finite expectations nor a finite background distribution
is assumed; only the one-row comparison is supplied to this general lemma. -/
theorem monotone_lintegral_shiftedRowSum {n : ℕ}
    (μ : Measure Z) [SigmaFinite μ] {P : E → Prop}
    (hzero : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (G : Z → E) (hG : Measurable G) (hrow : ∀ z, P (G z))
    (H : E → ℝ≥0∞) (hH : Measurable H)
    (hsingle : ∀ Q, P Q → ∀ v : Z,
      MonotoneOn (fun t : ℝ => ∫⁻ z, H (Q + G (z + Real.sqrt t • v)) ∂μ) (Ici 0))
    (Q : E) (hQ : P Q) (v : Fin n → Z) :
    MonotoneOn (fun lam : Fin n → ℝ =>
      ∫⁻ z, H (Q + shiftedRowSum G v lam z) ∂Measure.pi (fun _ : Fin n => μ)) (Ici 0) := by
  apply monotoneOn_of_monotone_updates (fun _ : Fin n => Ici (0 : ℝ))
  intro lam hlam a t ht hlamt
  cases n with
  | zero => exact Fin.elim0 a
  | succ n =>
    let ν := Measure.pi (fun _ : Fin n => μ)
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Z) a).trans
      (MeasurableEquiv.prodComm (α := Z) (β := Fin n → Z))
    have he : MeasurePreserving e (Measure.pi (fun _ : Fin (n + 1) => μ)) (ν.prod μ) :=
      Measure.measurePreserving_swap.comp (measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => μ) a)
    let A (z : Fin n → Z) := Q + shiftedRowSum G (v ∘ a.succAbove) (lam ∘ a.succAbove) z
    let F (s : ℝ) (w : (Fin n → Z) × Z) := H (A w.1 + G (w.2 + Real.sqrt s • v a))
    have hFm (s : ℝ) : Measurable (F s) := by
      apply hH.comp
      apply Measurable.add
      · exact (measurable_const.add (measurable_shiftedRowSum hG _ _)).comp measurable_fst
      · exact hG.comp (measurable_snd.add measurable_const)
    have hcomp (s : ℝ) : F s ∘ e =
        (fun z => H (Q + shiftedRowSum G v (Function.update lam a s) z)) := by
      funext z
      rw [shiftedRowSum_split]
      change H ((Q + shiftedRowSum G (v ∘ a.succAbove)
        (lam ∘ a.succAbove) (z ∘ a.succAbove)) + G (z a + Real.sqrt s • v a)) = _
      rw [add_assoc]
    have heq (s : ℝ) :
        (∫⁻ z, H (Q + shiftedRowSum G v (Function.update lam a s) z)
          ∂Measure.pi (fun _ : Fin (n + 1) => μ)) =
        ∫⁻ z, ∫⁻ u, F s (z,u) ∂μ ∂ν := by
      rw [← lintegral_prod _ (hFm s).aemeasurable, ← he.map_eq,
        lintegral_map (hFm s) he.measurable]
      exact congrArg (fun f => ∫⁻ z, f z ∂Measure.pi (fun _ : Fin (n + 1) => μ)) (hcomp s).symm
    have hleft : lam = Function.update lam a (lam a) := (Function.update_eq_self a lam).symm
    conv_lhs => rw [hleft]
    rw [heq (lam a), heq t]
    apply lintegral_mono
    intro z
    exact hsingle (A z)
      (hadd Q _ hQ (shiftedRowSum_mem hzero hadd hrow _ _ _)) (v a)
      (hlam a) ht hlamt

end WishartVerification
end
end CanonicalSource24

section CanonicalSource25
/- Source: Wishart/FieldGaussianTransform.lean -/



/-!
# Exact rectangular transforms of independent field Gaussian rows

Every map is the actual real continuous linear map of row vectors. The law
with factor `R*B` is the pushforward of the law with factor `R` under right
multiplication by `B`, including singular rectangular maps.
-/

noncomputable section
open Matrix MeasureTheory
open scoped Classical Quaternion ENNReal
namespace Wishart.FieldGaussian

variable (F : Type*) [NormedRing F] [StarRing F] [CStarRing F]
  [InnerProductSpace ℝ F] [StarModule ℝ F] [FiniteDimensional ℝ F]
  [SMulCommClass ℝ F F] [IsScalarTower ℝ F F]
  [MeasurableSpace F] [BorelSpace F]

theorem rowFactor_comp {r m k : ℕ} (R : Matrix (Fin r) (Fin m) F)
    (B : Matrix (Fin m) (Fin k) F) (z : Row F r) :
    rowFactorCLM F B (rowFactorCLM F R z) = rowFactorCLM F (R * B) z := by
  ext j
  simp only [rowFactorCLM_apply, Matrix.mul_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem gaussianRowWithFactor_map_factor {r m k : ℕ}
    (R : Matrix (Fin r) (Fin m) F) (B : Matrix (Fin m) (Fin k) F) :
    (gaussianRowWithFactor F R).map (rowFactorCLM F B) = gaussianRowWithFactor F (R * B) := by
  unfold gaussianRowWithFactor
  rw [Measure.map_map (rowFactorCLM F B).continuous.measurable
    (normalizedRowFactorCLM F R).continuous.measurable]
  apply congrArg ((ProbabilityTheory.stdGaussian (Row F r)).map)
  funext z
  simp only [Function.comp_apply, normalizedRowFactorCLM, ContinuousLinearMap.smul_apply,
    map_smul, rowFactor_comp]

theorem measurePreserving_gaussianRowFactor {r m k : ℕ}
    (R : Matrix (Fin r) (Fin m) F) (B : Matrix (Fin m) (Fin k) F) :
    MeasurePreserving (rowFactorCLM F B) (gaussianRowWithFactor F R)
      (gaussianRowWithFactor F (R * B)) :=
  ⟨(rowFactorCLM F B).continuous.measurable, gaussianRowWithFactor_map_factor F R B⟩

theorem measurePreserving_gaussianRowsFactor {r m k n : ℕ}
    (R : Matrix (Fin r) (Fin m) F) (B : Matrix (Fin m) (Fin k) F) :
    MeasurePreserving (fun z : Fin n → Row F m => fun i => rowFactorCLM F B (z i))
      (Measure.pi (fun _ : Fin n => gaussianRowWithFactor F R))
      (Measure.pi (fun _ : Fin n => gaussianRowWithFactor F (R * B))) :=
  measurePreserving_pi _ _ (fun _ => measurePreserving_gaussianRowFactor F R B)

theorem gaussianRowWithFactor_one_map_factor {m k : ℕ}
    (B : Matrix (Fin m) (Fin k) F) :
    (gaussianRowWithFactor F (1 : Matrix (Fin m) (Fin m) F)).map (rowFactorCLM F B) =
      gaussianRowWithFactor F B := by
  simpa only [Matrix.one_mul] using gaussianRowWithFactor_map_factor F (1 : Matrix (Fin m) (Fin m) F) B

theorem gaussianRowsWithFactor_one_map_factor {m k n : ℕ}
    (B : Matrix (Fin m) (Fin k) F) :
    (Measure.pi (fun _ : Fin n => gaussianRowWithFactor F (1 : Matrix (Fin m) (Fin m) F))).map
      (fun z : Fin n → Row F m => fun i => rowFactorCLM F B (z i)) =
        Measure.pi (fun _ : Fin n => gaussianRowWithFactor F B) := by
  simpa only [Matrix.one_mul] using (measurePreserving_gaussianRowsFactor (n := n) F (1 : Matrix (Fin m) (Fin m) F) B).map_eq

theorem rowsMatrix_factor {r p n : ℕ} (R : Matrix (Fin r) (Fin p) F)
    (z : Fin n → Row F r) :
    rowsMatrix F (fun i => rowFactorCLM F R (z i)) = rowsMatrix F z * R := by
  ext i j
  simp only [rowsMatrix, Matrix.of_apply, rowFactorCLM_apply, Matrix.mul_apply]

theorem rowsGram_factor {r p n : ℕ} (R : Matrix (Fin r) (Fin p) F)
    (z : Fin n → Row F r) :
    (rowsGram F (fun i => rowFactorCLM F R (z i)) : Matrix (Fin p) (Fin p) F) =
      Rᴴ * (rowsGram F z : Matrix (Fin r) (Fin r) F) * R := by
  change (rowsMatrix F (fun i => rowFactorCLM F R (z i)))ᴴ *
    rowsMatrix F (fun i => rowFactorCLM F R (z i)) =
      Rᴴ * ((rowsMatrix F z)ᴴ * rowsMatrix F z) * R
  rw [rowsMatrix_factor, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

end Wishart.FieldGaussian
end
end CanonicalSource25

section CanonicalSource26
/- Source: Wishart/ConditionalAssociation.lean -/



/-!
# Association after an actual conditional representation

The selected factor is a function of the conditioning variable. The other
factor may depend on all the auxiliary randomness. Every expectation here is
an extended nonnegative integral, so the statement includes infinite moments.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace WishartVerification

theorem selected_split_of_conditional_association
    {E L N : Type*} [MeasurableSpace E] [MeasurableSpace L] [MeasurableSpace N]
    [Preorder L] (μ : Measure E) (κ : Measure L) (η : Measure N)
    [SFinite κ] [IsProbabilityMeasure η]
    (C : Set L) (hC : ∀ᵐ x ∂κ, x ∈ C)
    (T : L × N → E) (hT : Measurable T) (hlaw : (κ.prod η).map T = μ)
    (f g : E → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (φ : L → ℝ≥0∞) (hφ : Measurable φ)
    (hselected : ∀ l ∈ C, ∀ z, f (T (l,z)) = φ l)
    (hassoc : ∀ a b : L → ℝ≥0∞, Measurable a → Measurable b →
      MonotoneOn a C → MonotoneOn b C →
      (∫⁻ l, a l ∂κ) * (∫⁻ l, b l ∂κ) ≤ ∫⁻ l, a l * b l ∂κ)
    (hφmono : MonotoneOn φ C)
    (hgmono : MonotoneOn (fun l => ∫⁻ z, g (T (l,z)) ∂η) C) :
    (∫⁻ x, f x ∂μ) * (∫⁻ x, g x ∂μ) ≤ ∫⁻ x, f x * g x ∂μ := by
  let ψ : L → ℝ≥0∞ := fun l => ∫⁻ z, g (T (l,z)) ∂η
  have hψ : Measurable ψ := (hg.comp hT).lintegral_prod_right'
  have hconditional (u : E → ℝ≥0∞) (hu : Measurable u) :
      (∫⁻ x, u x ∂μ) = ∫⁻ l, ∫⁻ z, u (T (l,z)) ∂η ∂κ := by
    calc
      (∫⁻ x, u x ∂μ) = ∫⁻ x, u x ∂(κ.prod η).map T := by rw [hlaw]
      _ = ∫⁻ y, u (T y) ∂κ.prod η := lintegral_map hu hT
      _ = _ := lintegral_prod (fun y => u (T y)) (hu.comp hT).aemeasurable
  have hfint : (∫⁻ x, f x ∂μ) = ∫⁻ l, φ l ∂κ := by
    rw [hconditional f hf]
    apply lintegral_congr_ae
    filter_upwards [hC] with l hl
    simp only [hselected l hl, lintegral_const, measure_univ, mul_one]
  have hgint : (∫⁻ x, g x ∂μ) = ∫⁻ l, ψ l ∂κ := hconditional g hg
  have hfgint : (∫⁻ x, f x * g x ∂μ) = ∫⁻ l, φ l * ψ l ∂κ := by
    rw [hconditional (fun x => f x * g x) (hf.mul hg)]
    apply lintegral_congr_ae
    filter_upwards [hC] with l hl
    simp only [hselected l hl]
    exact lintegral_const_mul _ ((hg.comp hT).comp (measurable_const.prodMk measurable_id))
  rw [hfint, hgint, hfgint]
  exact hassoc φ ψ hφ hψ hφmono hgmono

theorem map_nested_prod {L U N S E : Type*}
    [MeasurableSpace L] [MeasurableSpace U] [MeasurableSpace N]
    [MeasurableSpace S] [MeasurableSpace E]
    (κ : Measure L) (η : Measure U) (ν : Measure N) [SFinite η] [SFinite ν]
    (A : L × U → S) (hA : Measurable A)
    (B : S × N → E) (hB : Measurable B) :
    (((κ.prod η).map A).prod ν).map B =
      (κ.prod (η.prod ν)).map (fun z => B (A (z.1,z.2.1),z.2.2)) := by
  have hp := Measure.map_prod_map (κ.prod η) ν hA (measurable_id : Measurable (@id N))
  simp only [Measure.map_id] at hp
  let C : L × (U × N) → E := fun z => B (A (z.1,z.2.1),z.2.2)
  have hC : Measurable C := hB.comp ((hA.comp (measurable_fst.prodMk
      (measurable_fst.comp measurable_snd))).prodMk
        (measurable_snd.comp measurable_snd))
  calc
    (((κ.prod η).map A).prod ν).map B =
        (((κ.prod η).prod ν).map (Prod.map A id)).map B :=
      congrArg (Measure.map B) hp
    _ = ((κ.prod η).prod ν).map (B ∘ Prod.map A id) :=
      Measure.map_map hB (hA.prodMap measurable_id)
    _ = ((κ.prod η).prod ν).map (C ∘ MeasurableEquiv.prodAssoc) := rfl
    _ = (((κ.prod η).prod ν).map MeasurableEquiv.prodAssoc).map C :=
      (Measure.map_map hC MeasurableEquiv.prodAssoc.measurable).symm
    _ = (κ.prod (η.prod ν)).map C :=
      congrArg (Measure.map C) (measurePreserving_prodAssoc κ η ν).map_eq

end WishartVerification
end
end CanonicalSource26

section CanonicalSource27
/- Source: Wishart/NonnegativeProductLimits.lean -/



/-!
# Monotone limits of selected-factor inequalities, including zero factors

The product of two expectations is written as one integral over independent
copies before taking the limit. This avoids an unjustified continuity claim
for extended multiplication at `(0, ∞)`. All pointwise limits remain the
actual finite real factors; only their expectations may be infinite.
-/

noncomputable section
open MeasureTheory Filter Set Topology
open scoped Classical BigOperators ENNReal
namespace WishartVerification

theorem nonnegative_product_lintegral_tendsto {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω)
    (f : ℕ → ι → Ω → ℝ) (g : ι → Ω → ℝ)
    (hfm : ∀ n i, AEMeasurable (f n i) μ)
    (hf0 : ∀ᵐ x ∂μ, ∀ n i, 0 ≤ f n i x)
    (hfmono : ∀ᵐ x ∂μ, ∀ i, Monotone (fun n => f n i x))
    (hlim : ∀ᵐ x ∂μ, ∀ i, Tendsto (fun n => f n i x) atTop (𝓝 (g i x))) :
    Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (∏ i, f n i x) ∂μ) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (∏ i, g i x) ∂μ)) := by
  apply lintegral_tendsto_of_tendsto_of_monotone
  · intro n
    exact (Finset.aemeasurable_fun_prod _ fun i _ => hfm n i).ennreal_ofReal
  · filter_upwards [hf0, hfmono] with x hx hm
    intro n m hnm
    apply ENNReal.ofReal_le_ofReal
    exact Finset.prod_le_prod₀ (fun i _ => hx n i) (fun i _ => hm i hnm)
  · filter_upwards [hlim] with x hx
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_finsetProd _ fun i _ => hx i)

theorem nonnegative_product_comparison_of_approximations {Ω Ξ ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] [Fintype ι]
    (μ : Measure Ω) (ν : Measure Ξ)
    (f : ℕ → ι → Ω → ℝ) (f' : ℕ → ι → Ξ → ℝ)
    (g : ι → Ω → ℝ) (g' : ι → Ξ → ℝ)
    (hfm : ∀ n i, AEMeasurable (f n i) μ)
    (hf'm : ∀ n i, AEMeasurable (f' n i) ν)
    (hf0 : ∀ᵐ x ∂μ, ∀ n i, 0 ≤ f n i x)
    (hf'0 : ∀ᵐ x ∂ν, ∀ n i, 0 ≤ f' n i x)
    (hfmono : ∀ᵐ x ∂μ, ∀ i, Monotone (fun n => f n i x))
    (hf'mono : ∀ᵐ x ∂ν, ∀ i, Monotone (fun n => f' n i x))
    (hlim : ∀ᵐ x ∂μ, ∀ i, Tendsto (fun n => f n i x) atTop (𝓝 (g i x)))
    (hlim' : ∀ᵐ x ∂ν, ∀ i, Tendsto (fun n => f' n i x) atTop (𝓝 (g' i x)))
    (hfinite : ∀ n, (∫⁻ x, ENNReal.ofReal (∏ i, f n i x) ∂μ) ≤
      ∫⁻ x, ENNReal.ofReal (∏ i, f' n i x) ∂ν) :
    (∫⁻ x, ENNReal.ofReal (∏ i, g i x) ∂μ) ≤
      ∫⁻ x, ENNReal.ofReal (∏ i, g' i x) ∂ν :=
  le_of_tendsto_of_tendsto
    (nonnegative_product_lintegral_tendsto μ f g hfm hf0 hfmono hlim)
    (nonnegative_product_lintegral_tendsto ν f' g' hf'm hf'0 hf'mono hlim')
    (Filter.Eventually.of_forall hfinite)

/-- An internal limit theorem whose finite-comparison premise is to be
supplied by the actual regression and spectral association argument. -/
theorem selected_split_of_nonnegative_approximations {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω) [SFinite μ]
    (f₀ : ℕ → Ω → ℝ) (f : ℕ → ι → Ω → ℝ)
    (g₀ : Ω → ℝ) (g : ι → Ω → ℝ)
    (hfm₀ : ∀ n, Measurable (f₀ n)) (hfm : ∀ n i, Measurable (f n i))
    (hf0₀ : ∀ᵐ x ∂μ, ∀ n, 0 ≤ f₀ n x)
    (hf0 : ∀ᵐ x ∂μ, ∀ n i, 0 ≤ f n i x)
    (hfmono₀ : ∀ᵐ x ∂μ, Monotone (fun n => f₀ n x))
    (hfmono : ∀ᵐ x ∂μ, ∀ i, Monotone (fun n => f n i x))
    (hlim₀ : ∀ᵐ x ∂μ, Tendsto (fun n => f₀ n x) atTop (𝓝 (g₀ x)))
    (hlim : ∀ᵐ x ∂μ, ∀ i, Tendsto (fun n => f n i x) atTop (𝓝 (g i x)))
    (hfinite : ∀ n, (∫⁻ x, ENNReal.ofReal (f₀ n x) ∂μ) *
      (∫⁻ x, ENNReal.ofReal (∏ i, f n i x) ∂μ) ≤
      ∫⁻ x, ENNReal.ofReal (f₀ n x * ∏ i, f n i x) ∂μ) :
    (∫⁻ x, ENNReal.ofReal (g₀ x) ∂μ) *
      (∫⁻ x, ENNReal.ofReal (∏ i, g i x) ∂μ) ≤
      ∫⁻ x, ENNReal.ofReal (g₀ x * ∏ i, g i x) ∂μ := by
  let left (n : ℕ) (i : Option ι) (x : Ω × Ω) : ℝ :=
    Option.elim i (f₀ n x.1) (fun j => f n j x.2)
  let right (n : ℕ) (i : Option ι) (x : Ω) : ℝ :=
    Option.elim i (f₀ n x) (fun j => f n j x)
  let limitLeft (i : Option ι) (x : Ω × Ω) : ℝ :=
    Option.elim i (g₀ x.1) (fun j => g j x.2)
  let limitRight (i : Option ι) (x : Ω) : ℝ :=
    Option.elim i (g₀ x) (fun j => g j x)
  have hlm (n : ℕ) (i : Option ι) : AEMeasurable (left n i) (μ.prod μ) := by
    cases i with
    | none => exact ((hfm₀ n).comp measurable_fst).aemeasurable
    | some i => exact ((hfm n i).comp measurable_snd).aemeasurable
  have hrm (n : ℕ) (i : Option ι) : AEMeasurable (right n i) μ := by
    cases i with
    | none => exact (hfm₀ n).aemeasurable
    | some i => exact (hfm n i).aemeasurable
  have hl0 : ∀ᵐ x ∂μ.prod μ, ∀ n i, 0 ≤ left n i x := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hf0₀,
      Measure.quasiMeasurePreserving_snd.ae hf0] with x hx₀ hx n i
    cases i with
    | none => exact hx₀ n
    | some i => exact hx n i
  have hr0 : ∀ᵐ x ∂μ, ∀ n i, 0 ≤ right n i x := by
    filter_upwards [hf0₀, hf0] with x hx₀ hx n i
    cases i with
    | none => exact hx₀ n
    | some i => exact hx n i
  have hlmono : ∀ᵐ x ∂μ.prod μ, ∀ i, Monotone (fun n => left n i x) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hfmono₀,
      Measure.quasiMeasurePreserving_snd.ae hfmono] with x hx₀ hx i
    cases i with
    | none => exact hx₀
    | some i => exact hx i
  have hrmono : ∀ᵐ x ∂μ, ∀ i, Monotone (fun n => right n i x) := by
    filter_upwards [hfmono₀, hfmono] with x hx₀ hx i
    cases i with
    | none => exact hx₀
    | some i => exact hx i
  have hllim : ∀ᵐ x ∂μ.prod μ, ∀ i,
      Tendsto (fun n => left n i x) atTop (𝓝 (limitLeft i x)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hlim₀,
      Measure.quasiMeasurePreserving_snd.ae hlim] with x hx₀ hx i
    cases i with
    | none => exact hx₀
    | some i => exact hx i
  have hrlim : ∀ᵐ x ∂μ, ∀ i,
      Tendsto (fun n => right n i x) atTop (𝓝 (limitRight i x)) := by
    filter_upwards [hlim₀, hlim] with x hx₀ hx i
    cases i with
    | none => exact hx₀
    | some i => exact hx i
  have hcompare := nonnegative_product_comparison_of_approximations
    (μ.prod μ) μ left right limitLeft limitRight hlm hrm hl0 hr0 hlmono hrmono hllim hrlim
    (fun n => by
      simp only [left, right, Fintype.prod_option, Option.elim_none, Option.elim_some]
      rw [lintegral_independent_real_product (hfm₀ n).aemeasurable
        (Finset.aemeasurable_fun_prod _ fun i _ => (hfm n i).aemeasurable)
        (hf0₀.mono fun x hx => hx n)]
      exact hfinite n)
  have hgm₀ : AEMeasurable g₀ μ :=
    aemeasurable_of_tendsto_metrizable_ae atTop (fun n => (hfm₀ n).aemeasurable) hlim₀
  have hgm (i : ι) : AEMeasurable (g i) μ :=
    aemeasurable_of_tendsto_metrizable_ae atTop (fun n => (hfm n i).aemeasurable)
      (hlim.mono fun x hx => hx i)
  have hg0₀ : ∀ᵐ x ∂μ, 0 ≤ g₀ x := by
    filter_upwards [hf0₀, hlim₀] with x hx hl
    exact ge_of_tendsto hl (Filter.Eventually.of_forall hx)
  simp only [limitLeft, limitRight, Fintype.prod_option, Option.elim_none,
    Option.elim_some] at hcompare
  rw [lintegral_independent_real_product hgm₀
    (Finset.aemeasurable_fun_prod _ fun i _ => hgm i) hg0₀] at hcompare
  exact hcompare

end WishartVerification
end
end CanonicalSource27

section CanonicalSource28
/- Source: Wishart/FieldGaussianNorm.lean -/



/-!
# The exact scalar norm law of an actual field Gaussian column

The proof is through an ordinary real orthonormal basis and the proved
chi-squared law of a finite sum of real Gaussian squares.  It gives the
Gamma(beta*n/2,beta/2) seed for the integer field Gram recursion.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory TauCeti.Probability
open scoped Classical Quaternion ENNReal

namespace Wishart.FieldGaussian

theorem stdGaussian_map_norm_sq (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] :
    (stdGaussian E).map (fun x => ‖x‖ ^ 2) =
      chiSquaredMeasure (Module.finrank ℝ E) := by
  let b := stdOrthonormalBasis ℝ E
  rw [stdGaussian_eq_map_pi_orthonormalBasis b,
    Measure.map_map (by fun_prop) (by fun_prop)]
  have heq : (fun x : Fin (Module.finrank ℝ E) → ℝ => ‖∑ i, x i • b i‖ ^ 2) =
      (fun x => ∑ i, x i ^ 2) := by
    funext x
    rw [show (∑ i, x i • b i) = b.repr.symm (WithLp.toLp 2 x) from b.sum_repr_symm _]
    rw [b.repr.symm.norm_map]
    exact EuclideanSpace.real_norm_sq_eq _
  change (Measure.pi fun _ : Fin (Module.finrank ℝ E) => gaussianReal 0 1).map
    (fun x => ‖∑ i, x i • b i‖ ^ 2) = _
  rw [heq]
  simpa only [NNReal.coe_one,one_mul,Fintype.card_fin,Measure.map_id'] using
    map_sum_sq_pi_gaussianReal (ι := Fin (Module.finrank ℝ E)) 1

variable (F : Type*) [NormedRing F] [StarRing F] [CStarRing F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [SMulCommClass ℝ F F] [IsScalarTower ℝ F F]
  [MeasurableSpace F] [BorelSpace F]

theorem finrank_row (n : ℕ) : Module.finrank ℝ (Row F n) = n * Module.finrank ℝ F := by
  rw [(WithLp.linearEquiv 2 ℝ (Fin n → F)).finrank_eq,Module.finrank_pi_fintype]
  simp

theorem normalizedRowFactorCLM_one {n : ℕ} (z : Row F n) :
    normalizedRowFactorCLM F (1 : Matrix (Fin n) (Fin n) F) z = standardDeviation F • z := by
  ext i
  simp only [normalizedRowFactorCLM,ContinuousLinearMap.smul_apply,rowFactorCLM_apply,
    Matrix.one_apply,PiLp.smul_apply]
  simp

theorem standardDeviation_sq (hF : 0 < Module.finrank ℝ F) :
    standardDeviation F ^ 2 = (Module.finrank ℝ F : ℝ)⁻¹ := by
  rw [standardDeviation,inv_pow,Real.sq_sqrt (Nat.cast_nonneg _)]

theorem normalizedRowFactorCLM_one_norm_sq {n : ℕ}
    (hF : 0 < Module.finrank ℝ F) (z : Row F n) :
    ‖normalizedRowFactorCLM F (1 : Matrix (Fin n) (Fin n) F) z‖ ^ 2 =
      (Module.finrank ℝ F : ℝ)⁻¹ * ‖z‖ ^ 2 := by
  rw [normalizedRowFactorCLM_one,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,
    standardDeviation_sq F hF]

theorem gaussianRowWithFactor_one_norm_sq_chiSquared (n : ℕ)
    (hF : 0 < Module.finrank ℝ F) :
    (gaussianRowWithFactor F (1 : Matrix (Fin n) (Fin n) F)).map (fun z => ‖z‖ ^ 2) =
      (chiSquaredMeasure (n * Module.finrank ℝ F)).map
        (fun x => (Module.finrank ℝ F : ℝ)⁻¹ * x) := by
  unfold gaussianRowWithFactor
  rw [Measure.map_map (by fun_prop) (normalizedRowFactorCLM F 1).continuous.measurable]
  have heq : (fun z : Row F n => ‖normalizedRowFactorCLM F 1 z‖ ^ 2) =
      (fun x : ℝ => (Module.finrank ℝ F : ℝ)⁻¹ * x) ∘ (fun z => ‖z‖ ^ 2) :=
    funext (normalizedRowFactorCLM_one_norm_sq F hF)
  change (stdGaussian (Row F n)).map (fun z => ‖normalizedRowFactorCLM F 1 z‖ ^ 2) = _
  rw [heq,← Measure.map_map (by fun_prop) (by fun_prop),stdGaussian_map_norm_sq,finrank_row,Nat.cast_mul]

theorem gaussianRowWithFactor_one_norm_sq_gamma {n : ℕ} (hn : 0 < n)
    (hF : 0 < Module.finrank ℝ F) :
    (gaussianRowWithFactor F (1 : Matrix (Fin n) (Fin n) F)).map (fun z => ‖z‖ ^ 2) =
      gammaMeasure ((Module.finrank ℝ F : ℝ) * n / 2) ((Module.finrank ℝ F : ℝ) / 2) := by
  have hb : 0 < (Module.finrank ℝ F : ℝ) := by exact_mod_cast hF
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [gaussianRowWithFactor_one_norm_sq_chiSquared F n hF,
    chiSquaredMeasure_eq_gammaMeasure (by exact_mod_cast Nat.mul_pos hn hF),
    gammaMeasure_map_const_mul (by positivity) (by norm_num) (inv_pos.mpr hb)]
  congr 1 <;> push_cast <;> field_simp [hb.ne'] <;> ring

end Wishart.FieldGaussian
end
end CanonicalSource28

section CanonicalSource29
/- Source: Wishart/ExponentialMoments.lean -/



/-!
# Positive exponential integrability implies every finite moment

The lower exponential is bounded by one on a nonnegative random variable.
Mathlib's two-sided exponential-moment theorem then gives every real power,
which is converted to the full finite-Lp formulation used by the project.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace WishartVerification

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

theorem allFiniteMoments_of_positive_exponential {f : Ω → ℝ}
    (hf : Measurable f) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) {a : ℝ} (ha : 0 < a)
    (hexp : (∫⁻ x, ENNReal.ofReal (Real.exp (a * f x)) ∂μ) < ⊤) :
    HasAllFiniteMoments f μ := by
  have hpos : Integrable (fun x => Real.exp (a * f x)) μ :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      ((hf.const_mul a).exp.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)).mp hexp.ne
  have hneg : Integrable (fun x => Real.exp (-a * f x)) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      ((hf.const_mul (-a)).exp.aestronglyMeasurable)
    filter_upwards [hf0] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le) hx)
  intro p hp
  by_cases hp0 : p = 0
  · subst p
    exact memLp_zero_iff_aestronglyMeasurable.mpr hf.aestronglyMeasurable
  apply (integrable_norm_rpow_iff hf.aestronglyMeasurable hp0 hp).mp
  simpa only [Real.norm_eq_abs] using
    integrable_rpow_abs_of_integrable_exp_mul ha.ne' hpos hneg ENNReal.toReal_nonneg

theorem allFiniteMoments_of_nonnegative_bound {f g : Ω → ℝ}
    (hf : Measurable f) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hfg : ∀ᵐ x ∂μ, f x ≤ g x) (hg : HasAllFiniteMoments g μ) :
    HasAllFiniteMoments f μ := by
  intro p hp
  apply (hg p hp).mono' hf.aestronglyMeasurable
  filter_upwards [hf0, hfg] with x h0 hle
  simpa only [Real.norm_eq_abs, abs_of_nonneg h0] using hle

end WishartVerification
end
end CanonicalSource29
