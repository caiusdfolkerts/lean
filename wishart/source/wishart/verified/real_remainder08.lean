module

public import wishart.verified.real_remainder07
public import Mathlib.Algebra.Order.Rearrangement

/- Generated ordinary proof stage. See audit/staged_real_remainder/RealRemainder08/manifest.json. -/

@[expose] public section

section CanonicalSource70
/- Source: Wishart/GaugeFiniteApproximation.lean -/



/-!
# Finite positive-support approximations of compressed spectral gauges

The approximation is pointwise on the whole positive semidefinite cone,
including zero. Only finite nonnegative powers are passed through this limit.
General geometrically log-convex outer functions are treated separately at
the final nonsingular law, where their arguments are strictly positive.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability Filter Topology
open WishartVerification
open scoped Matrix MatrixOrder Matrix.Norms.Operator RealInnerProductSpace

namespace WishartVerification

theorem finiteMaximum_prod_index {ι τ : Type*} [Fintype ι] [Nonempty ι]
    [Fintype τ] [Nonempty τ] (x : ι → τ → ℝ) :
    finiteMaximum (fun j => finiteMaximum (x j)) =
      finiteMaximum (fun z : ι × τ => x z.1 z.2) := by
  apply le_antisymm
  · apply finiteMaximum_le
    intro j
    apply finiteMaximum_le
    intro l
    exact le_finiteMaximum (fun z : ι × τ => x z.1 z.2) (j, l)
  · apply finiteMaximum_le
    intro z
    exact (le_finiteMaximum (x z.1) z.2).trans
      (le_finiteMaximum (fun j => finiteMaximum (x j)) z.1)

theorem finiteMaximum_monomial {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    Real.exp b * finiteMaximum x ^ a =
      finiteMaximum (fun i => Real.exp b * x i ^ a) := by
  apply le_antisymm
  · obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty x
    change Real.exp b * (Finset.univ.sup' Finset.univ_nonempty x) ^ a ≤ _
    rw [heq]
    exact le_finiteMaximum (fun j => Real.exp b * x j ^ a) i
  · apply finiteMaximum_le
    intro i
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (hx i) (le_finiteMaximum x i) ha) (Real.exp_pos b).le

theorem finiteOuterTest_nonneg_of_nonneg {κ ι : Type*} [Fintype κ]
    [Fintype ι] [Nonempty ι] (a b : κ → ι → ℝ) {x : κ → ℝ}
    (hx : ∀ i, 0 ≤ x i) : 0 ≤ finiteOuterTest a b x := by
  apply Finset.prod_nonneg
  intro i _
  exact finiteMaximum_nonneg fun j =>
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (hx i) _)

theorem finiteOuterTest_mono_nonneg {κ ι : Type*} [Fintype κ]
    [Fintype ι] [Nonempty ι] (a b : κ → ι → ℝ) (ha : ∀ i j, 0 ≤ a i j)
    {x y : κ → ℝ} (hx : ∀ i, 0 ≤ x i) (hxy : x ≤ y) :
    finiteOuterTest a b x ≤ finiteOuterTest a b y := by
  apply Finset.prod_le_prod₀
  · intro i _
    exact finiteMaximum_nonneg fun j =>
      mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (hx i) _)
  · intro i _
    exact finiteMaximum_mono fun j => mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (hx i) (hxy i) (ha i j)) (Real.exp_pos _).le

end WishartVerification

namespace Wishart.SpectralGauge

variable {k : ℕ} (Φ : SpectralGauge k)

def supportSequence : ℕ → SymmetricMatrix k :=
  Classical.choose Φ.exists_countable_positive_support

theorem supportSequence_mem (n : ℕ) : Φ.supportSequence n ∈ Φ.supportSet :=
  (Classical.choose_spec Φ.exists_countable_positive_support).1 n

theorem supportSequence_sup {X : SymmetricMatrix k}
    (hX : X ∈ positiveSemidefiniteCone k) :
    (⨆ n, ⟪Φ.supportSequence n, X⟫) = Φ X :=
  (Classical.choose_spec Φ.exists_countable_positive_support).2 X hX

def supportMaximum (n : ℕ) (X : SymmetricMatrix k) : ℝ :=
  finiteMaximum (fun l : Fin (n + 1) => ⟪Φ.supportSequence l, X⟫)

theorem supportMaximum_nonneg (n : ℕ) {X : SymmetricMatrix k}
    (hX : X ∈ positiveSemidefiniteCone k) : 0 ≤ Φ.supportMaximum n X :=
  finiteMaximum_nonneg fun l =>
    inner_nonneg_of_posSemidef (Φ.supportSequence_mem l).1 hX

theorem supportMaximum_le (n : ℕ) {X : SymmetricMatrix k}
    (hX : X ∈ positiveSemidefiniteCone k) : Φ.supportMaximum n X ≤ Φ X :=
  finiteMaximum_le fun l => (Φ.supportSequence_mem l).2 X hX

theorem supportMaximum_mono (X : SymmetricMatrix k) : Monotone (fun n => Φ.supportMaximum n X) := by
  intro n m hnm
  apply finiteMaximum_le
  intro l
  exact le_finiteMaximum
    (fun j : Fin (m + 1) => ⟪Φ.supportSequence j, X⟫)
    (Fin.castLE (Nat.add_le_add_right hnm 1) l)

theorem supportMaximum_tendsto {X : SymmetricMatrix k}
    (hX : X ∈ positiveSemidefiniteCone k) :
    Tendsto (fun n => Φ.supportMaximum n X) atTop (𝓝 (Φ X)) := by
  have hb : BddAbove (Set.range (fun n => Φ.supportMaximum n X)) :=
    ⟨Φ X, by rintro _ ⟨n, rfl⟩; exact Φ.supportMaximum_le n hX⟩
  have heq : (⨆ n, Φ.supportMaximum n X) = Φ X := by
    apply le_antisymm (ciSup_le fun n => Φ.supportMaximum_le n hX)
    rw [← Φ.supportSequence_sup hX]
    apply ciSup_le
    intro n
    exact (le_finiteMaximum
      (fun j : Fin (n + 1) => ⟪Φ.supportSequence j, X⟫)
      ⟨n, Nat.lt_succ_self n⟩).trans (le_ciSup hb n)
  simpa only [heq] using tendsto_atTop_ciSup (Φ.supportMaximum_mono X) hb

end Wishart.SpectralGauge

namespace Wishart

/-- A PSD offset and arbitrary rectangular compression, evaluated by a genuine
spectral gauge. Full column rank is needed only by the final positivity theorem. -/
structure GaugeCompression (p : ℕ) where
  size : ℕ
  gauge : SpectralGauge size
  offset : SymmetricMatrix size
  offset_posSemidef : (offset : Matrix (Fin size) (Fin size) ℝ).PosSemidef
  linear : Matrix (Fin p) (Fin size) ℝ

namespace GaugeCompression

variable {p : ℕ} (G : GaugeCompression p)

def matrix (X : SymmetricMatrix p) : SymmetricMatrix G.size :=
  G.offset + Matrix.symmetricCongruenceLinearMap G.linearᵀ X

@[fun_prop] theorem measurable_matrix : Measurable G.matrix :=
  measurable_const.add (LinearMap.continuous_of_finiteDimensional
    (Matrix.symmetricCongruenceLinearMap G.linearᵀ)).measurable

theorem matrix_posSemidef {X : SymmetricMatrix p}
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    (G.matrix X : Matrix (Fin G.size) (Fin G.size) ℝ).PosSemidef := by
  apply G.offset_posSemidef.add
  simpa only [Matrix.coe_symmetricCongruenceLinearMap_apply,
    Matrix.conjTranspose_eq_transpose_of_trivial] using hX.mul_mul_conjTranspose_same G.linearᵀ

def value (X : SymmetricMatrix p) : ℝ := G.gauge.value (G.matrix X)

@[fun_prop] theorem measurable_value : Measurable G.value :=
  G.gauge.measurable_value.comp G.measurable_matrix

theorem value_nonneg (X : SymmetricMatrix p) : 0 ≤ G.value X := G.gauge.value_nonneg _

theorem value_eq {X : SymmetricMatrix p}
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    G.value X = G.gauge (G.matrix X) := G.gauge.value_eq (G.matrix_posSemidef hX)

theorem matrixTestAllMoments_value : MatrixTestAllMoments G.value := by
  intro Ω _ μ _ X hXm hX hentries
  apply G.gauge.allFiniteMoments_value (G.measurable_matrix.comp hXm)
    (hX.mono fun z hz => G.matrix_posSemidef hz)
  intro i j
  have hc := HasAllFiniteMoments.matrix_right_mul_entry
    (fun z => G.linearᵀ * (X z : Matrix (Fin p) (Fin p) ℝ)) G.linear
    (fun i j => HasAllFiniteMoments.matrix_left_mul_entry _ G.linearᵀ hentries i j) i j
  simpa only [Function.comp_apply, matrix, Submodule.coe_add, Matrix.coe_symmetricCongruenceLinearMap_apply,
    Matrix.transpose_transpose, Matrix.add_apply] using
    (HasAllFiniteMoments.const ((G.offset : Matrix (Fin G.size) (Fin G.size) ℝ) i j)).add hc

def supportConstant (l : ℕ) : ℝ := ⟪G.gauge.supportSequence l, G.offset⟫

def supportMatrix (l : ℕ) : SymmetricMatrix p :=
  Matrix.symmetricCongruenceLinearMap G.linear (G.gauge.supportSequence l)

theorem supportConstant_nonneg (l : ℕ) : 0 ≤ G.supportConstant l :=
  inner_nonneg_of_posSemidef (G.gauge.supportSequence_mem l).1 G.offset_posSemidef

theorem supportMatrix_posSemidef (l : ℕ) :
    (G.supportMatrix l : Matrix (Fin p) (Fin p) ℝ).PosSemidef := by
  simpa only [supportMatrix, Matrix.coe_symmetricCongruenceLinearMap_apply,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    (G.gauge.supportSequence_mem l).1.mul_mul_conjTranspose_same G.linear

theorem support_trace_eq (l : ℕ) (X : SymmetricMatrix p) :
    G.supportConstant l + ⟪G.supportMatrix l, X⟫ =
      ⟪G.gauge.supportSequence l, G.matrix X⟫ := by
  change ⟪G.gauge.supportSequence l, G.offset⟫ +
    ⟪Matrix.symmetricCongruenceLinearMap G.linear (G.gauge.supportSequence l), X⟫ =
      ⟪G.gauge.supportSequence l,
        G.offset + Matrix.symmetricCongruenceLinearMap G.linearᵀ X⟫
  rw [Matrix.inner_symmetricCongruenceLinearMap G.linear (G.gauge.supportSequence l) X]
  simp only [selfAdjoint.inner_eq_trace_mul, Submodule.coe_add, Matrix.add_mul,
    Matrix.trace_add]

end GaugeCompression

variable {p : ℕ} {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]

def gaugeMaximumProduct (G : κ → GaugeCompression p) (a b : κ → ι → ℝ)
    (X : SymmetricMatrix p) : ℝ := finiteOuterTest a b (fun i => (G i).value X)

theorem measurable_gaugeMaximumProduct (G : κ → GaugeCompression p)
    (a b : κ → ι → ℝ) (ha : ∀ i j, 0 ≤ a i j) :
    Measurable (gaugeMaximumProduct G a b) :=
  (continuous_finiteOuterTest a b ha).measurable.comp
    (measurable_pi_iff.mpr fun i => (G i).measurable_value)

theorem gaugeMaximumProduct_nonneg (G : κ → GaugeCompression p)
    (a b : κ → ι → ℝ) (X : SymmetricMatrix p) : 0 ≤ gaugeMaximumProduct G a b X :=
  finiteOuterTest_nonneg_of_nonneg a b fun i => (G i).value_nonneg X

theorem matrixTestAllMoments_gaugeMaximumProduct (G : κ → GaugeCompression p)
    (a b : κ → ι → ℝ) (ha : ∀ i j, 0 ≤ a i j) :
    MatrixTestAllMoments (gaugeMaximumProduct G a b) := by
  intro Ω _ μ _ X hXm hX hentries
  apply HasAllFiniteMoments.finset_prod Finset.univ
  intro i _
  apply hasAllFiniteMoments_finiteMaximum
  intro j
  exact (((G i).matrixTestAllMoments_value hXm hX hentries).rpow (ha i j)).const_mul
    (Real.exp (b i j))

def gaugeSupportProduct (G : κ → GaugeCompression p) (a b : κ → ι → ℝ)
    (n : ℕ) (X : SymmetricMatrix p) : ℝ :=
  traceMaximumProduct 0
    (fun i (z : ι × Fin (n + 1)) => (G i).supportConstant z.2)
    (fun i (z : ι × Fin (n + 1)) => a i z.1)
    (fun i (z : ι × Fin (n + 1)) => b i z.1)
    (fun i (z : ι × Fin (n + 1)) => (G i).supportMatrix z.2) X

theorem gaugeSupportProduct_eq (G : κ → GaugeCompression p)
    (a b : κ → ι → ℝ) (ha : ∀ i j, 0 ≤ a i j) (n : ℕ)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    gaugeSupportProduct G a b n X =
      finiteOuterTest a b (fun i => (G i).gauge.supportMaximum n ((G i).matrix X)) := by
  unfold gaugeSupportProduct traceMaximumProduct finiteOuterTest
  apply Finset.prod_congr rfl
  intro i _
  simp only [zero_add, GaugeCompression.support_trace_eq]
  rw [← finiteMaximum_prod_index (fun (j : ι) (l : Fin (n + 1)) =>
    Real.exp (b i j) * ⟪(G i).gauge.supportSequence l, (G i).matrix X⟫ ^ a i j)]
  congr 1
  funext j
  exact (finiteMaximum_monomial
    (fun l : Fin (n + 1) => ⟪(G i).gauge.supportSequence l, (G i).matrix X⟫)
    (fun l : Fin (n + 1) => inner_nonneg_of_posSemidef ((G i).gauge.supportSequence_mem l).1
      ((G i).matrix_posSemidef hX)) (ha i j) (b i j)).symm

theorem gaugeSupportProduct_le (G : κ → GaugeCompression p)
    (a b : κ → ι → ℝ) (ha : ∀ i j, 0 ≤ a i j) (n : ℕ)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    gaugeSupportProduct G a b n X ≤ gaugeMaximumProduct G a b X := by
  rw [gaugeSupportProduct_eq G a b ha n hX]
  apply finiteOuterTest_mono_nonneg a b ha
  · intro i
    exact (G i).gauge.supportMaximum_nonneg n ((G i).matrix_posSemidef hX)
  · intro i
    change (G i).gauge.supportMaximum n ((G i).matrix X) ≤ (G i).value X
    rw [(G i).value_eq hX]
    exact (G i).gauge.supportMaximum_le n ((G i).matrix_posSemidef hX)

theorem gaugeSupportProduct_tendsto (G : κ → GaugeCompression p)
    (a b : κ → ι → ℝ) (ha : ∀ i j, 0 ≤ a i j)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    Tendsto (fun n => gaugeSupportProduct G a b n X) atTop (𝓝 (gaugeMaximumProduct G a b X)) := by
  simp only [gaugeSupportProduct_eq G a b ha _ hX]
  apply (continuous_finiteOuterTest a b ha).continuousAt.tendsto.comp
  apply tendsto_pi_nhds.mpr
  intro i
  rw [(G i).value_eq hX]
  exact (G i).gauge.supportMaximum_tendsto ((G i).matrix_posSemidef hX)

set_option maxHeartbeats 800000 in
theorem gaugeSupportProduct_integral_tendsto
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → SymmetricMatrix p} (hXm : Measurable X)
    (hX : ∀ᵐ z ∂μ, (X z : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (hentries : ∀ i j : Fin p, HasAllFiniteMoments
      (fun z => (X z : Matrix (Fin p) (Fin p) ℝ) i j) μ)
    (G : κ → GaugeCompression p) (a b : κ → ι → ℝ) (ha : ∀ i j, 0 ≤ a i j) :
    Tendsto (fun n => ∫ z, gaugeSupportProduct G a b n (X z) ∂μ) atTop
      (𝓝 (∫ z, gaugeMaximumProduct G a b (X z) ∂μ)) := by
  have hi : Integrable (fun z => gaugeMaximumProduct G a b (X z)) μ :=
    (matrixTestAllMoments_gaugeMaximumProduct G a b ha hXm hX hentries).integrable
  refine tendsto_integral_of_dominated_convergence
    (fun z => gaugeMaximumProduct G a b (X z)) ?_ hi ?_ ?_
  · intro n
    exact ((continuous_traceMaximumProduct 0
      (fun i (z : ι × Fin (n + 1)) => (G i).supportConstant z.2)
      (fun i (z : ι × Fin (n + 1)) => a i z.1)
      (fun i (z : ι × Fin (n + 1)) => b i z.1)
      (fun i (z : ι × Fin (n + 1)) => (G i).supportMatrix z.2)
      (fun i (z : ι × Fin (n + 1)) => ha i z.1)).measurable.comp hXm).aestronglyMeasurable
  · intro n
    filter_upwards [hX] with z hz
    have hp : 0 ≤ gaugeSupportProduct G a b n (X z) :=
      traceMaximumProduct_nonneg 0 le_rfl
        (fun i (j : ι × Fin (n + 1)) => (G i).supportConstant j.2)
        (fun i (j : ι × Fin (n + 1)) => a i j.1)
        (fun i (j : ι × Fin (n + 1)) => b i j.1)
        (fun i (j : ι × Fin (n + 1)) => (G i).supportMatrix j.2)
        (fun i (j : ι × Fin (n + 1)) => (G i).supportConstant_nonneg j.2)
        (fun i (j : ι × Fin (n + 1)) => (G i).supportMatrix_posSemidef j.2) hz
    rw [Real.norm_of_nonneg hp]
    exact gaugeSupportProduct_le G a b ha n hz
  · exact hX.mono fun z hz => gaugeSupportProduct_tendsto G a b ha hz

end Wishart
end
end CanonicalSource70

section CanonicalSource71
/- Source: Wishart/OuterRadialComparison.lean -/



/-!
# The radial comparison for general geometric outer functions

Finite maxima have all finite moments under the actual regression-noise law.
The last limit is an extended nonnegative integral, so the final outer
functions need not have polynomial growth or finite expectations. Positivity
of their determinant arguments is recorded explicitly here and is discharged
from the nonsingular conditional matrix in the overlap application.
-/

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped BigOperators ENNReal Matrix.Norms.Operator

namespace WishartVerification

variable {p : ℕ} {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]

theorem allFiniteMoments_affineMaximumProduct
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasure μ]
    (hμ : HasAllFiniteMoments (fun z : E => ‖z‖) μ)
    {Z : E → SymmetricMatrix p} (hZ : Z.HasTemperateGrowth)
    (ε : ℝ) (k : κ → ℕ)
    (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (a b : κ → ι → ℝ) (ha : ∀ i j, 0 ≤ a i j)
    (hdet : ∀ᵐ z ∂μ, ∀ i, 0 ≤ (regularizedCompression ε (B i) (M i) (Z z)).det) :
    HasAllFiniteMoments (fun z => affineMaximumProduct ε k B M a b (Z z)) μ := by
  classical
  let x : κ → ι → E → ℝ := fun i j z => Real.exp (b i j) *
    (regularizedCompression ε (B i) (M i) (Z z)).det ^ (a i j)
  have hx : ∀ i j, HasAllFiniteMoments (x i j) μ :=
    monomialMoments_of_temperate_matrix hμ hZ ε k B M a b ha
  have hbound : HasAllFiniteMoments (fun z => ∏ i, ∑ j, x i j z) μ :=
    HasAllFiniteMoments.finset_prod Finset.univ _ (fun i _ =>
      HasAllFiniteMoments.finset_sum Finset.univ _ (fun j _ => hx i j))
  intro q hq
  apply (hbound q hq).mono'
  · exact ((continuous_affineMaximumProduct ε k B M a b ha).comp
      hZ.1.continuous).aestronglyMeasurable
  · filter_upwards [hdet] with z hz
    have hpos (i : κ) (j : ι) : 0 ≤ x i j z :=
      mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (hz i) _)
    rw [affineMaximumProduct, norm_prod]
    apply Finset.prod_le_prod₀
    · intro i hi
      exact norm_nonneg _
    · intro i hi
      rw [Real.norm_of_nonneg (finiteMaximum_nonneg (hpos i))]
      exact finiteMaximum_le_sum (hpos i)

theorem affineMaximumProduct_eq_finiteOuterTest (ε : ℝ) (k : κ → ℕ)
    (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (a b : κ → ι → ℝ) (X : SymmetricMatrix p) :
    affineMaximumProduct ε k B M a b X =
      finiteOuterTest a b (fun i => (regularizedCompression ε (B i) (M i) X).det) := rfl

end WishartVerification

namespace Wishart

open WishartVerification

theorem hasTemperateGrowth_linearRadialInput {p r : ℕ}
    (L : Matrix (Fin p) (Fin r) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    (linearRadialInput L v s).HasTemperateGrowth := by
  have hscalar := (hasTemperateGrowth_scalarRadialMatrix r).comp
    (hasTemperateGrowth_prodMk (Function.HasTemperateGrowth.const s)
      Function.HasTemperateGrowth.id)
  have hcong := (LinearMap.toContinuousLinearMap
    (Matrix.symmetricCongruenceLinearMap (radialLiftMatrix v L))).hasTemperateGrowth
  simpa only [Function.comp_def, id_eq, LinearMap.coe_toContinuousLinearMap',
    radialLiftMatrix_scalarRadialMatrix] using hcong.comp hscalar

/-- The full geometric outer class under the genuine scalar-regression noise
law. This is an extended-integral comparison: no unproved moment assumption on
the outer functions is included. The positivity premise concerns only the
determinant arguments and is verified in the nonsingular overlap assembly. -/
theorem monotoneOn_linearRadial_geometricProduct
    {p r : ℕ} {N : ℝ} (hN : (r : ℝ) < N)
    (L : Matrix (Fin p) (Fin r) ℝ) (v : EuclideanSpace ℝ (Fin p))
    {κ : Type*} [Fintype κ]
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hB : ∀ i, (B i).PosSemidef)
    (hsize : ∀ i, min (k i : ℝ) ((1 + r : ℕ) : ℝ) + 1 ≤ N)
    (hpos : ∀ t ∈ Set.Ioi (0 : ℝ),
      ∀ᵐ z ∂scalarRegressionNoiseMeasure N r, ∀ i,
        0 < (regularizedCompression 0 (B i) (M i)
          (linearRadialInput L v (Real.sqrt t) z)).det)
    (f : κ → ℝ → ℝ) (hf : ∀ i, GeometricallyLogConvex (f i)) :
    MonotoneOn (fun t : ℝ => ∫⁻ z : ScalarRegressionNoise r,
      ENNReal.ofReal (∏ i, f i ((regularizedCompression 0 (B i) (M i)
        (linearRadialInput L v (Real.sqrt t) z)).det))
        ∂scalarRegressionNoiseMeasure N r) (Set.Ioi 0) := by
  letI := isProbabilityMeasure_scalarRegressionNoiseMeasure hN
  let d : ℝ → ScalarRegressionNoise r → κ → ℝ := fun t z i =>
    (regularizedCompression 0 (B i) (M i) (linearRadialInput L v (Real.sqrt t) z)).det
  have hdm (t : ℝ) : Measurable (d t) := by
    apply measurable_pi_iff.mpr
    intro i
    exact ((hasTemperateGrowth_regularizedCompression_det 0 (B i) (M i)).1.continuous.comp
      (hasTemperateGrowth_linearRadialInput L v (Real.sqrt t)).1.continuous).measurable
  intro s hs t ht hst
  apply geometric_outer_comparison_of_finite_comparisons
    (scalarRegressionNoiseMeasure N r) (scalarRegressionNoiseMeasure N r)
    (d s) (d t) (hdm s) (hdm t) (hpos s hs) (hpos t ht) _ f hf
  intro n a b ha
  have hmom (u : ℝ) (hu : u ∈ Set.Ioi (0 : ℝ)) :=
    allFiniteMoments_affineMaximumProduct (allFiniteNormMoments_scalarRegressionNoise hN)
      (hasTemperateGrowth_linearRadialInput L v (Real.sqrt u))
      0 k B M a b ha ((hpos u hu).mono fun z hz i => (hz i).le)
  have hnonneg (u : ℝ) (hu : u ∈ Set.Ioi (0 : ℝ)) :
      ∀ᵐ z ∂scalarRegressionNoiseMeasure N r,
        0 ≤ affineMaximumProduct 0 k B M a b (linearRadialInput L v (Real.sqrt u) z) := by
    filter_upwards [hpos u hu] with z hz
    apply Finset.prod_nonneg
    intro i hi
    exact finiteMaximum_nonneg fun j =>
      mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (hz i).le _)
  have hint (u : ℝ) (hu : u ∈ Set.Ioi (0 : ℝ)) :=
    ofReal_integral_eq_lintegral_ofReal (hmom u hu).integrable (hnonneg u hu)
  change (∫⁻ z, ENNReal.ofReal
      (affineMaximumProduct 0 k B M a b (linearRadialInput L v (Real.sqrt s) z))
      ∂scalarRegressionNoiseMeasure N r) ≤
    ∫⁻ z, ENNReal.ofReal
      (affineMaximumProduct 0 k B M a b (linearRadialInput L v (Real.sqrt t) z))
      ∂scalarRegressionNoiseMeasure N r
  rw [← hint s hs, ← hint t ht]
  exact ENNReal.ofReal_le_ofReal
    (monotoneOn_linearRadial_finiteOuterProduct hN L v k B M a b hB ha hsize hs.le ht.le hst)

end Wishart
end
end CanonicalSource71

section CanonicalSource72
/- Source: Wishart/GaugeRegressionMonotonicity.lean -/



/-!
# Actual conditional monotonicity for spectral gauges

Finite support maxima converge under an explicit gauge-moment envelope.
The many-factor comparison uses N≥2. For one remaining gauge the Gaussian
Anderson comparison applies directly, without a degree restriction.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability Filter Topology
open WishartVerification
open scoped Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart

def symmetricMatrixEntryCLM {p : ℕ} (i j : Fin p) : SymmetricMatrix p →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((Matrix.entryLinearMap ℝ ℝ i j).comp
      (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)).subtype)

@[simp] theorem symmetricMatrixEntryCLM_apply {p : ℕ} (i j : Fin p)
    (X : SymmetricMatrix p) : symmetricMatrixEntryCLM i j X =
      (X : Matrix (Fin p) (Fin p) ℝ) i j := rfl

theorem allFiniteMoments_scalarAffineInput_entry {p r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) (B : SymmetricMatrix p)
    (L : Matrix (Fin p) (Fin r) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ)
    (i j : Fin p) :
    HasAllFiniteMoments (fun z : ScalarRegressionNoise r =>
      (B + linearRadialInput L v s z : SymmetricMatrix p).val i j)
      (scalarRegressionNoiseMeasure N r) := by
  letI := isProbabilityMeasure_scalarRegressionNoiseMeasure hN
  intro u hu
  apply memLp_temperate_of_allNormMoments (allFiniteNormMoments_scalarRegressionNoise hN) _ hu
  exact (symmetricMatrixEntryCLM i j).hasTemperateGrowth.comp
    ((Function.HasTemperateGrowth.const B).add (hasTemperateGrowth_linearRadialInput L v s))

theorem ae_scalarAffineInput_posSemidef {p r : ℕ} (N : ℝ)
    {B : SymmetricMatrix p} (hB : (B : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (L : Matrix (Fin p) (Fin r) ℝ) (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    ∀ᵐ z ∂scalarRegressionNoiseMeasure N r,
      ((B + linearRadialInput L v s z : SymmetricMatrix p) :
        Matrix (Fin p) (Fin p) ℝ).PosSemidef := by
  filter_upwards [ae_scalarRadialMatrix_posSemidef N s] with z hz
  apply hB.add
  rw [← radialLiftMatrix_scalarRadialMatrix]
  simpa only [Matrix.coe_symmetricCongruenceLinearMap_apply,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    hz.mul_mul_conjTranspose_same (radialLiftMatrix v L)

theorem scalarRadialTestMonotone_gaugeMaximumProduct
    {p r : ℕ} {N : ℝ} (hN : (r : ℝ) < N) (hNtwo : 2 ≤ N)
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (G : κ → GaugeCompression p) (a b : κ → ι → ℝ) (ha : ∀ i j, 0 ≤ a i j) :
    ScalarRadialTestMonotone N r (gaugeMaximumProduct G a b) := by
  intro B hB L v
  let Z (s : ℝ) (z : ScalarRegressionNoise r) := B + linearRadialInput L v s z
  have hZm (s : ℝ) : Measurable (Z s) :=
    measurable_const.add (measurable_linearRadialInput L v s)
  have hlim (s : ℝ) : Tendsto
      (fun n => ∫ z, gaugeSupportProduct G a b n (Z s z) ∂scalarRegressionNoiseMeasure N r)
      atTop (𝓝 (∫ z, gaugeMaximumProduct G a b (Z s z) ∂scalarRegressionNoiseMeasure N r)) :=
    gaugeSupportProduct_integral_tendsto (hZm s) (ae_scalarAffineInput_posSemidef N hB L v s)
      (allFiniteMoments_scalarAffineInput_entry hN B L v s) G a b ha
  intro s hs t ht hst
  exact le_of_tendsto_of_tendsto (hlim (Real.sqrt s)) (hlim (Real.sqrt t))
    (Filter.Eventually.of_forall fun n =>
      scalarRadialTestMonotone_traceMaximumProduct hN hNtwo
        (fun i (z : ι × Fin (n + 1)) => (G i).supportConstant z.2)
        (fun i (z : ι × Fin (n + 1)) => a i z.1)
        (fun i (z : ι × Fin (n + 1)) => b i z.1)
        (fun i (z : ι × Fin (n + 1)) => (G i).supportMatrix z.2)
        (fun i z => (G i).supportConstant_nonneg z.2)
        (fun i z => ha i z.1) (fun i z => (G i).supportMatrix_posSemidef z.2)
        B hB L v hs ht hst)

theorem monotoneOn_fullRegressionSpectralAverage_gaugeMaximumProduct
    {q m : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (hdegree : (q : ℝ) + 1 ≤ n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (G : κ → GaugeCompression (q + m)) (a b : κ → ι → ℝ) (ha : ∀ i j, 0 ≤ a i j) :
    MonotoneOn (fullRegressionSpectralAverage n C K (gaugeMaximumProduct G a b))
      (Spectral.positiveChamber q) := by
  have hN : (m : ℝ) < n - q + 1 := by
    push_cast at hn
    linarith
  exact monotoneOn_fullRegressionSpectralAverage_test hn hC K
    (measurable_gaugeMaximumProduct G a b ha)
    (matrixTestAllMoments_gaugeMaximumProduct G a b ha)
    (scalarRadialTestMonotone_gaugeMaximumProduct hN (by linarith) G a b ha)

theorem GaugeCompression.matrix_add_rankOne {p : ℕ} (G : GaugeCompression p)
    (B : SymmetricMatrix p) (u : EuclideanSpace ℝ (Fin p)) :
    G.matrix (B + rankOneSymmetric u) =
      G.matrix B + rankOneSymmetric (G.linearᵀ.toEuclideanLin u) := by
  simp only [GaugeCompression.matrix, map_add, symmetricCongruence_rankOne, add_assoc]

theorem GaugeCompression.value_add_gaussianRankOne {p m : ℕ} (G : GaugeCompression p)
    {B : SymmetricMatrix p} (hB : (B : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (L : Matrix (Fin p) (Fin m) ℝ) (v : EuclideanSpace ℝ (Fin p))
    (t : ℝ) (z : EuclideanSpace ℝ (Fin m)) :
    G.value (B + rankOneSymmetric (L.toEuclideanLin z + Real.sqrt t • v)) =
      G.gauge (G.matrix B + rankOneSymmetric
        ((G.linearᵀ * L).toEuclideanLin z + Real.sqrt t • G.linearᵀ.toEuclideanLin v)) := by
  rw [G.value_eq (hB.add (rankOneSymmetric_posSemidef _)), G.matrix_add_rankOne,
    map_add, map_smul, ← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same]

/-- The single remaining gauge comparison permits every increasing measurable
outer test for which the two actual row integrals are finite. -/
theorem monotoneOn_linearShiftedRows_gauge_coordinate_of_integrable
    {q m p : ℕ} {ν : ℝ} (hν : (m : ℝ) - 1 < ν)
    (L : Matrix (Fin p) (Fin m) ℝ) (G : GaugeCompression p)
    {f : ℝ → ℝ} (hfm : Measurable f) (hf : MonotoneOn f (Set.Ici 0))
    (v : Fin q → EuclideanSpace ℝ (Fin p)) (lam : Fin q → ℝ) (a : Fin q)
    (hint : ∀ t : ℝ, Integrable
      (fun x => f (G.value (linearShiftedRowsSym L v (Function.update lam a t) x)))
      (gaussianResidualMeasure q 1 (nonsingularWishartMeasure ν 1))) :
    MonotoneOn (fun t : ℝ => ∫ x,
      f (G.value (linearShiftedRowsSym L v (Function.update lam a t) x))
        ∂gaussianResidualMeasure q 1 (nonsingularWishartMeasure ν 1)) (Set.Ici 0) := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure
    (S := (1 : Matrix (Fin m) (Fin m) ℝ)) Matrix.PosDef.one hν
  cases q with
  | zero => exact Fin.elim0 a
  | succ q =>
    let γ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) 1
    let μ : Measure (RegressionNoise q m) :=
      gaussianResidualMeasure q 1 (nonsingularWishartMeasure ν 1)
    let B : RegressionNoise q m → SymmetricMatrix p :=
      linearShiftedRowsSym L (v ∘ a.succAbove) (lam ∘ a.succAbove)
    let H (t : ℝ) (y : RegressionNoise q m × EuclideanSpace ℝ (Fin m)) : ℝ :=
      f (G.value (B y.1 + rankOneSymmetric (L.toEuclideanLin y.2 + Real.sqrt t • v a)))
    have hsplit := measurePreserving_splitRegressionRow (1 : Matrix (Fin m) (Fin m) ℝ)
      (nonsingularWishartMeasure ν 1) a
    have hHm (t : ℝ) : Measurable (H t) := by
      apply hfm.comp
      apply G.measurable_value.comp
      apply Measurable.add
      · exact (measurable_linearShiftedRowsSym L _ _).comp measurable_fst
      · exact hasTemperateGrowth_rankOneSymmetric.1.continuous.measurable.comp
          (((L.toEuclideanLin.toContinuousLinearMap).continuous.measurable.comp measurable_snd).add
            measurable_const)
    have hHcomp (t : ℝ) : H t ∘ splitRegressionRow a =
        (fun x => f (G.value (linearShiftedRowsSym L v (Function.update lam a t) x))) := by
      funext x
      dsimp only [H, B, Function.comp_apply]
      rw [linearShiftedRowsSym_split]
      rfl
    have hHi (t : ℝ) : Integrable (H t) (μ.prod γ) := by
      rw [← hsplit.map_eq]
      apply (integrable_map_measure (hHm t).aestronglyMeasurable hsplit.measurable.aemeasurable).mpr
      rw [hHcomp]
      exact hint t
    have heq (t : ℝ) :
        (∫ x, f (G.value (linearShiftedRowsSym L v (Function.update lam a t) x))
          ∂gaussianResidualMeasure (q + 1) 1 (nonsingularWishartMeasure ν 1)) =
        ∫ y, ∫ z, H t (y, z) ∂γ ∂μ := by
      rw [← integral_prod _ (hHi t), ← hsplit.map_eq,
        integral_map hsplit.measurable.aemeasurable (hHm t).aestronglyMeasurable]
      exact congrArg (fun g => ∫ x, g x
        ∂gaussianResidualMeasure (q + 1) 1 (nonsingularWishartMeasure ν 1)) (hHcomp t).symm
    have hB : ∀ᵐ y ∂μ, (B y : Matrix (Fin p) (Fin p) ℝ).PosSemidef := by
      filter_upwards [Measure.quasiMeasurePreserving_snd.ae
        (ae_posDef_nonsingularWishartMeasure ν (1 : Matrix (Fin m) (Fin m) ℝ))] with y hy
      exact linearShiftedRowsSym_posSemidef L _ _ y hy.posSemidef
    intro s hs t ht hst
    dsimp only
    rw [heq s, heq t]
    apply integral_mono_ae (hHi s).integral_prod_left (hHi t).integral_prod_left
    filter_upwards [hB, (hHi s).prod_right_ae, (hHi t).prod_right_ae] with y hy hys hyt
    have hfun (r : ℝ) : (fun z => H r (y, z)) =
        fun z => f (G.gauge (G.matrix (B y) + rankOneSymmetric
          ((G.linearᵀ * L).toEuclideanLin z + Real.sqrt r • G.linearᵀ.toEuclideanLin (v a)))) := by
      funext z
      exact congrArg f (G.value_add_gaussianRankOne hy L (v a) r z)
    rw [hfun s, hfun t]
    rw [hfun s] at hys
    rw [hfun t] at hyt
    exact G.gauge.integral_rectangularGaussian_rankOne_le (G.matrix_posSemidef hy)
      (G.linearᵀ * L) (G.linearᵀ.toEuclideanLin (v a)) hfm hf hs hst hys hyt

def gaugeFiniteTest {p : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (G : GaugeCompression p) (a b : ι → ℝ) (X : SymmetricMatrix p) : ℝ :=
  finiteMaximum (fun j => Real.exp (b j) * (G.value X) ^ (a j))

theorem measurable_gaugeFiniteTest {p : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (G : GaugeCompression p) (a b : ι → ℝ) : Measurable (gaugeFiniteTest G a b) :=
  measurable_finiteMaximum _ fun j => measurable_const.mul (G.measurable_value.pow_const _)

theorem matrixTestAllMoments_gaugeFiniteTest {p : ℕ} {ι : Type*}
    [Fintype ι] [Nonempty ι] (G : GaugeCompression p) (a b : ι → ℝ) (ha : ∀ j, 0 ≤ a j) :
    MatrixTestAllMoments (gaugeFiniteTest G a b) := by
  intro Ω _ μ _ X hXm hX hentries
  exact hasAllFiniteMoments_finiteMaximum _ fun j =>
    ((G.matrixTestAllMoments_value hXm hX hentries).rpow (ha j)).const_mul (Real.exp (b j))

theorem monotoneOn_fullSpectralConditionalMoment_gaugeFiniteTest
    {q m : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Matrix (Fin q) (Fin q) ℝ)
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (G : GaugeCompression (q + m)) (a b : ι → ℝ) (ha : ∀ j, 0 ≤ a j) :
    MonotoneOn (fun lam => fullSpectralConditionalMoment n C K (gaugeFiniteTest G a b) lam O)
      (Set.Ici (0 : Fin q → ℝ)) := by
  have hν : (m : ℝ) - 1 < n - q := by
    push_cast at hn
    linarith
  letI := isProbabilityMeasure_nonsingularWishartMeasure
    (S := (1 : Matrix (Fin m) (Fin m) ℝ)) Matrix.PosDef.one hν
  let L := regressionNoiseInjection q m * CFC.sqrt C
  let v := fullSpectralRegressionDirections K O
  have hmono : MonotoneOn (fun lam : Fin q → ℝ => ∫ x,
      gaugeFiniteTest G a b (linearShiftedRowsSym L v lam x)
        ∂gaussianResidualMeasure q 1 (nonsingularWishartMeasure (n - q) 1))
      (Set.Ici (0 : Fin q → ℝ)) := by
    apply monotoneOn_nonnegative_pi_of_update
    intro lam u
    apply monotoneOn_linearShiftedRows_gauge_coordinate_of_integrable hν L G
      (measurable_finiteMaximum _ fun j => measurable_const.mul (measurable_id.pow_const _))
      (fun x hx y hy hxy => finiteMaximum_mono fun j => mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hx hxy (ha j)) (Real.exp_pos _).le) v lam u
    intro t
    apply HasAllFiniteMoments.integrable
    apply matrixTestAllMoments_gaugeFiniteTest G a b ha
      (measurable_linearShiftedRowsSym L v (Function.update lam u t))
    · filter_upwards [Measure.quasiMeasurePreserving_snd.ae
        (ae_posDef_nonsingularWishartMeasure (n - q) (1 : Matrix (Fin m) (Fin m) ℝ))] with x hx
      exact linearShiftedRowsSym_posSemidef L v _ x hx.posSemidef
    · exact allFiniteMoments_linearShiftedRowsSym_entry 1
        (fun i j => allFiniteMoments_wishart_entry (α := n - q)
          (Sigma := (1 : Matrix (Fin m) (Fin m) ℝ)) i j) L v _
  intro lam hlam lam' hlam' hle
  dsimp only
  rw [fullSpectralConditionalMoment_standardNoise n hC K O lam (measurable_gaugeFiniteTest G a b),
    fullSpectralConditionalMoment_standardNoise n hC K O lam' (measurable_gaugeFiniteTest G a b)]
  exact hmono hlam hlam' hle

theorem monotoneOn_fullRegressionSpectralAverage_gaugeFiniteTest
    {q m : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ) {ι : Type*} [Fintype ι] [Nonempty ι]
    (G : GaugeCompression (q + m)) (a b : ι → ℝ) (ha : ∀ j, 0 ≤ a j) :
    MonotoneOn (fullRegressionSpectralAverage n C K (gaugeFiniteTest G a b))
      (Spectral.positiveChamber q) := by
  apply parameterAverageOn_monotoneOn
  · intro lam hlam
    exact integrable_haar_fullSpectralConditionalMoment_test hn hC K
      (matrixTestAllMoments_gaugeFiniteTest G a b ha) lam
  · intro lam hlam lam' hlam' hle
    exact Filter.Eventually.of_forall fun O =>
      monotoneOn_fullSpectralConditionalMoment_gaugeFiniteTest hn hC K ↑O G a b ha
        (fun i => (hlam.2 i).le) (fun i => (hlam'.2 i).le) hle

end Wishart
end
end CanonicalSource72

section CanonicalSource73
/- Source: Wishart/GaugeSelectedTests.lean -/



/-! # Exact selected spectral tests for normalized convex gauges -/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart

theorem GaugeCompression.value_loewner {p : ℕ} (G : GaugeCompression p)
    (X Y : SymmetricMatrix p)
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (hY : (Y : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (hXY : ((Y - X : SymmetricMatrix p) : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    G.value X ≤ G.value Y := by
  rw [G.value_eq hX, G.value_eq hY]
  apply G.gauge.loewner _ (G.matrix_posSemidef hX) _ (G.matrix_posSemidef hY)
  have heq : G.matrix Y - G.matrix X = Matrix.symmetricCongruenceLinearMap G.linearᵀ (Y - X) := by
    simp only [GaugeCompression.matrix, map_sub]
    abel
  rw [heq]
  simpa only [Matrix.coe_symmetricCongruenceLinearMap_apply,
    Matrix.conjTranspose_eq_transpose_of_trivial] using hXY.mul_mul_conjTranspose_same G.linearᵀ

theorem gaugeMaximumProduct_loewner {p : ℕ} {κ ι : Type*}
    [Fintype κ] [Fintype ι] [Nonempty ι]
    (G : κ → GaugeCompression p) (a b : κ → ι → ℝ) (ha : ∀ i j, 0 ≤ a i j)
    (X Y : SymmetricMatrix p)
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (hY : (Y : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (hXY : ((Y - X : SymmetricMatrix p) : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    gaugeMaximumProduct G a b X ≤ gaugeMaximumProduct G a b Y :=
  finiteOuterTest_mono_nonneg a b ha (fun i => (G i).value_nonneg X)
    (fun i => (G i).value_loewner X Y hX hY hXY)

def identityGaugeCompression {q : ℕ} (Φ : SpectralGauge q) (c : ℝ) (hc : 0 ≤ c) :
    GaugeCompression q where
  size := q
  gauge := Φ
  offset := c • SpectralGauge.identitySymmetric q
  offset_posSemidef := Matrix.PosSemidef.one.smul hc
  linear := 1

theorem identityGaugeCompression_matrix {q : ℕ}
    (Φ : SpectralGauge q) {c : ℝ} (hc : 0 ≤ c) (S : SymmetricMatrix q) :
    (identityGaugeCompression Φ c hc).matrix S = S + c • SpectralGauge.identitySymmetric q := by
  change c • SpectralGauge.identitySymmetric q +
    Matrix.symmetricCongruenceLinearMap (1 : Matrix (Fin q) (Fin q) ℝ)ᵀ S = _
  rw [Matrix.transpose_one, Matrix.symmetricCongruenceLinearMap_one, LinearMap.id_apply,
    add_comm]

def shiftedGaugeValue {q : ℕ} (Φ : SpectralGauge q) (c : ℝ) (S : SymmetricMatrix q) : ℝ :=
  Φ.value (S + c • SpectralGauge.identitySymmetric q)

theorem measurable_shiftedGaugeValue {q : ℕ} (Φ : SpectralGauge q) (c : ℝ) :
    Measurable (shiftedGaugeValue Φ c) := Φ.measurable_value.comp (measurable_id.add measurable_const)

theorem shiftedGaugeValue_identity {q : ℕ} (Φ : SpectralGauge q) {c : ℝ}
    (hc : 0 ≤ c) (S : SymmetricMatrix q) :
    (identityGaugeCompression Φ c hc).value S = shiftedGaugeValue Φ c S := by
  unfold GaugeCompression.value shiftedGaugeValue
  rw [identityGaugeCompression_matrix]
  rfl

theorem matrixTestAllMoments_shiftedGaugeValue {q : ℕ} (Φ : SpectralGauge q) {c : ℝ}
    (hc : 0 ≤ c) : MatrixTestAllMoments (shiftedGaugeValue Φ c) := by
  intro Ω _ μ _ X hm hp he
  simpa only [shiftedGaugeValue_identity] using
    (identityGaugeCompression Φ c hc).matrixTestAllMoments_value hm hp he

def selectedGaugeFiniteTest {q : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (Φ : SpectralGauge q) (c : ℝ) (a b : ι → ℝ) (S : SymmetricMatrix q) : ℝ :=
  finiteMaximum (fun j => Real.exp (b j) * shiftedGaugeValue Φ c S ^ (a j))

def selectedGaugeSpectralTest {q : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (Φ : SpectralGauge q) (c : ℝ) (a b : ι → ℝ) (lam : Fin q → ℝ) : ℝ :=
  selectedGaugeFiniteTest Φ c a b (Spectral.diagonalSym lam)

theorem measurable_selectedGaugeFiniteTest {q : ℕ} {ι : Type*}
    [Fintype ι] [Nonempty ι] (Φ : SpectralGauge q) (c : ℝ) (a b : ι → ℝ) :
    Measurable (selectedGaugeFiniteTest Φ c a b) :=
  measurable_finiteMaximum _ fun j =>
    measurable_const.mul ((measurable_shiftedGaugeValue Φ c).pow_const _)

theorem measurable_selectedGaugeSpectralTest {q : ℕ} {ι : Type*}
    [Fintype ι] [Nonempty ι] (Φ : SpectralGauge q) (c : ℝ) (a b : ι → ℝ) :
    Measurable (selectedGaugeSpectralTest Φ c a b) :=
  (measurable_selectedGaugeFiniteTest Φ c a b).comp (by
    apply Measurable.subtype_mk
    fun_prop)

theorem selectedGaugeFiniteTest_nonneg {q : ℕ} {ι : Type*}
    [Fintype ι] [Nonempty ι] (Φ : SpectralGauge q) (c : ℝ) (a b : ι → ℝ)
    (S : SymmetricMatrix q) : 0 ≤ selectedGaugeFiniteTest Φ c a b S :=
  finiteMaximum_nonneg fun j => mul_nonneg (Real.exp_pos _).le
    (Real.rpow_nonneg (Φ.value_nonneg _) _)

theorem matrixTestAllMoments_selectedGaugeFiniteTest {q : ℕ} {ι : Type*}
    [Fintype ι] [Nonempty ι] (Φ : SpectralGauge q) {c : ℝ} (hc : 0 ≤ c)
    (a b : ι → ℝ) (ha : ∀ j, 0 ≤ a j) :
    MatrixTestAllMoments (selectedGaugeFiniteTest Φ c a b) := by
  intro Ω _ μ _ X hXm hX hentries
  exact hasAllFiniteMoments_finiteMaximum _ fun j =>
    (((matrixTestAllMoments_shiftedGaugeValue Φ hc) hXm hX hentries).rpow (ha j)).const_mul
      (Real.exp (b j))

theorem shiftedGaugeValue_spectral {q : ℕ} (Φ : SpectralGauge q) {c : ℝ}
    (hc : 0 ≤ c) (lam : Fin q → ℝ) (hlam : ∀ i, 0 ≤ lam i) (O : Spectral.Orth q) :
    shiftedGaugeValue Φ c (regressionSpectralMatrix (lam, O)) =
      shiftedGaugeValue Φ c (Spectral.diagonalSym lam) := by
  let D := Spectral.diagonalSym lam + c • SpectralGauge.identitySymmetric q
  have hD : (D : Matrix (Fin q) (Fin q) ℝ).PosSemidef :=
    (Matrix.posSemidef_diagonal_iff.mpr hlam).add (Matrix.PosSemidef.one.smul hc)
  have heq : regressionSpectralMatrix (lam, O) + c • SpectralGauge.identitySymmetric q =
      Matrix.symmetricCongruenceLinearMap (↑O : Matrix (Fin q) (Fin q) ℝ) D := by
    apply Subtype.ext
    simp only [D, regressionSpectralMatrix, Spectral.conjugate,
      Matrix.coe_symmetricCongruenceLinearMap_apply, Submodule.coe_add, Submodule.coe_smul,
      SpectralGauge.identitySymmetric, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, Spectral.orth_mul_transpose]
  unfold shiftedGaugeValue
  rw [heq, Φ.value_eq, Φ.value_eq hD]
  · exact Φ.orthogonalInvariant O D hD
  · change ((Matrix.symmetricCongruenceLinearMap (↑O : Matrix (Fin q) (Fin q) ℝ) D :
      SymmetricMatrix q) : Matrix (Fin q) (Fin q) ℝ).PosSemidef
    simpa only [Matrix.coe_symmetricCongruenceLinearMap_apply,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      hD.mul_mul_conjTranspose_same (↑O : Matrix (Fin q) (Fin q) ℝ)

theorem selectedGaugeFiniteTest_spectral {q : ℕ} {ι : Type*}
    [Fintype ι] [Nonempty ι] (Φ : SpectralGauge q) {c : ℝ} (hc : 0 ≤ c)
    (a b : ι → ℝ) (lam : Fin q → ℝ) (hlam : lam ∈ Spectral.positiveChamber q)
    (O : Spectral.Orth q) :
    selectedGaugeFiniteTest Φ c a b (regressionSpectralMatrix (lam, O)) =
      selectedGaugeSpectralTest Φ c a b lam := by
  simp only [selectedGaugeSpectralTest, selectedGaugeFiniteTest]
  simp only [shiftedGaugeValue_spectral Φ hc lam (fun i => (hlam.2 i).le) O]

theorem selectedGaugeSpectralTest_monotone {q : ℕ} {ι : Type*}
    [Fintype ι] [Nonempty ι] (Φ : SpectralGauge q) {c : ℝ} (hc : 0 ≤ c)
    (a b : ι → ℝ) (ha : ∀ j, 0 ≤ a j) :
    MonotoneOn (selectedGaugeSpectralTest Φ c a b) (Spectral.positiveChamber q) := by
  intro lam hlam lam' hlam' hle
  have hp : (Spectral.diagonalSym lam : Matrix (Fin q) (Fin q) ℝ).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr fun i => (hlam.2 i).le
  have hp' : (Spectral.diagonalSym lam' : Matrix (Fin q) (Fin q) ℝ).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr fun i => (hlam'.2 i).le
  have hd : ((Spectral.diagonalSym lam' - Spectral.diagonalSym lam : SymmetricMatrix q) :
      Matrix (Fin q) (Fin q) ℝ).PosSemidef := by
    change (Matrix.diagonal lam' - Matrix.diagonal lam).PosSemidef
    rw [Matrix.diagonal_sub]
    exact Matrix.posSemidef_diagonal_iff.mpr fun i => sub_nonneg.mpr (hle i)
  have hg := (identityGaugeCompression Φ c hc).value_loewner _ _ hp hp' hd
  simp only [shiftedGaugeValue_identity] at hg
  exact finiteMaximum_mono fun j => mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Φ.value_nonneg _) hg (ha j)) (Real.exp_pos _).le

theorem identity_leading_gaugeFinite_split
    {q m : ℕ} {n c : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (hdegree : (q : ℝ) + 1 ≤ n) (Φ : SpectralGauge q) (hc : 0 ≤ c)
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (a₀ b₀ : ι → ℝ) (ha₀ : ∀ j, 0 ≤ a₀ j)
    (G : κ → GaugeCompression (q + m)) (a b : κ → ι → ℝ) (ha : ∀ i j, 0 ≤ a i j) :
    (∫ X, selectedGaugeFiniteTest Φ c a₀ b₀ (principalSymmetricBlock (Fin.castAdd m) X)
      ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) *
      (∫ X, gaugeMaximumProduct G a b X
        ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) ≤
      ∫ X, selectedGaugeFiniteTest Φ c a₀ b₀ (principalSymmetricBlock (Fin.castAdd m) X) *
        gaugeMaximumProduct G a b X
        ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) := by
  have h := regression_test_split_of_spectral_monotone hn
    (0 : Matrix (Fin q) (Fin m) ℝ) Matrix.PosDef.one
    (measurable_selectedGaugeFiniteTest Φ c a₀ b₀)
    (MatrixTestAllMoments.wishart (matrixTestAllMoments_selectedGaugeFiniteTest Φ hc a₀ b₀ ha₀) n 1)
    (measurable_selectedGaugeSpectralTest Φ c a₀ b₀)
    (fun lam => selectedGaugeFiniteTest_nonneg Φ c a₀ b₀ (Spectral.diagonalSym lam))
    (selectedGaugeSpectralTest_monotone Φ hc a₀ b₀ ha₀)
    (selectedGaugeFiniteTest_spectral Φ hc a₀ b₀)
    (measurable_gaugeMaximumProduct G a b ha)
    (matrixTestAllMoments_gaugeMaximumProduct G a b ha)
    (fun X _ => gaugeMaximumProduct_nonneg G a b X)
    (monotoneOn_fullRegressionSpectralAverage_gaugeMaximumProduct hn hdegree
      Matrix.PosDef.one 0 G a b ha)
  simpa only [regressionScale_zero_one] using h

theorem identity_leading_gaugeFinite_pair
    {q m : ℕ} {n c : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (Φ : SpectralGauge q) (hc : 0 ≤ c)
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (a₀ b₀ : ι → ℝ) (ha₀ : ∀ j, 0 ≤ a₀ j)
    (G : GaugeCompression (q + m)) (a b : ι → ℝ) (ha : ∀ j, 0 ≤ a j) :
    (∫ X, selectedGaugeFiniteTest Φ c a₀ b₀ (principalSymmetricBlock (Fin.castAdd m) X)
      ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) *
      (∫ X, gaugeFiniteTest G a b X
        ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) ≤
      ∫ X, selectedGaugeFiniteTest Φ c a₀ b₀ (principalSymmetricBlock (Fin.castAdd m) X) *
        gaugeFiniteTest G a b X
        ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) := by
  have h := regression_test_split_of_spectral_monotone hn
    (0 : Matrix (Fin q) (Fin m) ℝ) Matrix.PosDef.one
    (measurable_selectedGaugeFiniteTest Φ c a₀ b₀)
    (MatrixTestAllMoments.wishart (matrixTestAllMoments_selectedGaugeFiniteTest Φ hc a₀ b₀ ha₀) n 1)
    (measurable_selectedGaugeSpectralTest Φ c a₀ b₀)
    (fun lam => selectedGaugeFiniteTest_nonneg Φ c a₀ b₀ (Spectral.diagonalSym lam))
    (selectedGaugeSpectralTest_monotone Φ hc a₀ b₀ ha₀)
    (selectedGaugeFiniteTest_spectral Φ hc a₀ b₀)
    (measurable_gaugeFiniteTest G a b) (matrixTestAllMoments_gaugeFiniteTest G a b ha)
    (fun X _ => finiteMaximum_nonneg fun j =>
      mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (G.value_nonneg X) _))
    (monotoneOn_fullRegressionSpectralAverage_gaugeFiniteTest hn Matrix.PosDef.one 0 G a b ha)
  simpa only [regressionScale_zero_one] using h

end Wishart
end
end CanonicalSource73

section CanonicalSource74
/- Source: Wishart/WholeMatrixTestAssembly.lean -/



/-! # Unrestricted full-rank splitting for general Loewner-increasing tests -/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart

theorem integrable_haar_wholeMatrix_test {p : ℕ}
    {F : SymmetricMatrix p → ℝ} (hFM : MatrixTestAllMoments F)
    (lam : Fin p → ℝ) (hlam : ∀ i, 0 ≤ lam i) :
    Integrable (fun O : Spectral.Orth p => F (regressionSpectralMatrix (lam, O)))
      (haarProb (Spectral.Orth p)) := by
  apply HasAllFiniteMoments.integrable
  apply hFM
  · exact (measurable_regressionSpectralMatrix p).comp (measurable_const.prodMk measurable_id)
  · exact Filter.Eventually.of_forall fun O => spectralMatrix_posSemidef O lam hlam
  · intro i j
    apply allFiniteMoments_continuous_compact
    change Continuous (fun O : Spectral.Orth p =>
      (Spectral.conjugate O (Spectral.diagonalSym lam) : Matrix (Fin p) (Fin p) ℝ) i j)
    have hconj : Continuous (fun O : Spectral.Orth p =>
        Spectral.conjugate O (Spectral.diagonalSym lam)) :=
      (Spectral.continuous_conjugate p).comp (continuous_id.prodMk continuous_const)
    exact (continuous_apply j).comp ((continuous_apply i).comp hconj.subtype_val)

theorem wholeMatrixSpectralAverage_test_nonneg {p : ℕ} {F : SymmetricMatrix p → ℝ}
    (hF0 : ∀ X : SymmetricMatrix p, (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef → 0 ≤ F X)
    (lam : Fin p → ℝ) : 0 ≤ wholeMatrixSpectralAverage F lam := by
  unfold wholeMatrixSpectralAverage
  apply parameterAverageOn_nonneg
  intro lam' hlam O
  exact hF0 _ (spectralMatrix_posSemidef O lam' (fun i => (hlam.2 i).le))

theorem monotoneOn_wholeMatrixSpectralAverage_test {p : ℕ} {F : SymmetricMatrix p → ℝ}
    (hFM : MatrixTestAllMoments F)
    (hFl : ∀ X Y : SymmetricMatrix p,
      (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef →
      (Y : Matrix (Fin p) (Fin p) ℝ).PosSemidef →
      ((Y - X : SymmetricMatrix p) : Matrix (Fin p) (Fin p) ℝ).PosSemidef → F X ≤ F Y) :
    MonotoneOn (wholeMatrixSpectralAverage F) (Spectral.positiveChamber p) := by
  apply parameterAverageOn_monotoneOn
  · intro lam hlam
    exact integrable_haar_wholeMatrix_test hFM lam (fun i => (hlam.2 i).le)
  · intro lam hlam lam' hlam' hle
    exact Filter.Eventually.of_forall fun O => hFl _ _
      (spectralMatrix_posSemidef O lam (fun i => (hlam.2 i).le))
      (spectralMatrix_posSemidef O lam' (fun i => (hlam'.2 i).le))
      (spectralMatrix_difference_posSemidef O lam lam' hle)

/-- The full-rank identity-scale split follows from the actual Haar–Laguerre
representation and association, with no additional degree threshold. -/
theorem wholeMatrix_test_split {p : ℕ} {n : ℝ} (hn : (p : ℝ) - 1 < n)
    {h : SymmetricMatrix p → ℝ} (hh : Measurable h)
    (hHM : HasAllFiniteMoments h (nonsingularWishartMeasure n 1))
    {f : (Fin p → ℝ) → ℝ} (hfm : Measurable f) (hf0 : ∀ lam, 0 ≤ f lam)
    (hfmono : MonotoneOn f (Spectral.positiveChamber p))
    (hspectral : ∀ lam ∈ Spectral.positiveChamber p, ∀ O : Spectral.Orth p,
      h (regressionSpectralMatrix (lam, O)) = f lam)
    {F : SymmetricMatrix p → ℝ} (hFm : Measurable F) (hFM : MatrixTestAllMoments F)
    (hF0 : ∀ X : SymmetricMatrix p, (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef → 0 ≤ F X)
    (hFl : ∀ X Y : SymmetricMatrix p,
      (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef →
      (Y : Matrix (Fin p) (Fin p) ℝ).PosSemidef →
      ((Y - X : SymmetricMatrix p) : Matrix (Fin p) (Fin p) ℝ).PosSemidef → F X ≤ F Y) :
    (∫ X, h X ∂nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ)) *
      (∫ X, F X ∂nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ)) ≤
      ∫ X, h X * F X ∂nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ) := by
  letI := Spectral.laguerreLaw_isProbability hn
  let μ := nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ)
  let ν := (regressionEigenLaw p n).prod (haarProb (Spectral.Orth p))
  have hremaining := hFM.wishart n 1
  have hjoint := (hHM.mul hremaining).integrable
  have hs : (fun x => h (regressionSpectralMatrix x)) =ᵐ[ν] (fun x => f x.1) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae
      (Spectral.ae_laguerreLaw_mem_chamber hn)] with x hx
    exact hspectral x.1 hx x.2
  have hfiSource : Integrable (fun x : (Fin p → ℝ) × Spectral.Orth p => f x.1) ν :=
    ((measurePreserving_regressionSpectralMatrix hn).integrable_comp_of_integrable hHM.integrable).congr hs
  have hfi : Integrable f (regressionEigenLaw p n) := by
    simpa only [integral_const, probReal_univ, one_smul] using hfiSource.integral_prod_left
  have hjiSource : Integrable
      (fun x => f x.1 * F (regressionSpectralMatrix x)) ν := by
    apply ((measurePreserving_regressionSpectralMatrix hn).integrable_comp_of_integrable hjoint).congr
    exact hs.mono fun x hx => congrArg (fun r => r * F (regressionSpectralMatrix x)) hx
  have hselected : (∫ X, h X ∂μ) = ∫ lam, f lam ∂regressionEigenLaw p n := by
    rw [integral_regressionSpectralMatrix hn hh.aestronglyMeasurable,
      integral_congr_ae hs, integral_fun_fst]
    simp only [probReal_univ, one_smul]
  have hjointEq : (∫ X, h X * F X ∂μ) =
      ∫ lam, f lam * wholeMatrixSpectralAverage F lam ∂regressionEigenLaw p n := by
    rw [integral_regressionSpectralMatrix hn hjoint.aestronglyMeasurable,
      integral_congr_ae (hs.mono fun x hx => congrArg (fun r => r * F (regressionSpectralMatrix x)) hx)]
    exact (integral_mul_parameterAverageOn _ _ _
      (Spectral.ae_laguerreLaw_mem_chamber hn) _ _ hjiSource).symm
  rw [hselected, integral_wholeMatrixSpectralAverage hn hremaining.integrable, hjointEq]
  exact integral_laguerre_mul_ge hn hfm (measurable_wholeMatrixSpectralAverage hFm)
    hf0 (wholeMatrixSpectralAverage_test_nonneg hF0) hfmono
    (monotoneOn_wholeMatrixSpectralAverage_test hFM hFl) hfi
    (integrable_wholeMatrixSpectralAverage hn hremaining.integrable)
    (mul_parameterAverageOn_integrable _ _ _
      (Spectral.ae_laguerreLaw_mem_chamber hn) _ _ hjiSource)

end Wishart
end
end CanonicalSource74

section CanonicalSource75
/- Source: Wishart/GaugeNormalization.lean -/



/-!
# Arbitrary covariance normalization for the gauge splits

The selected normalized matrix becomes the exact leading block. All remaining
compressed matrices are retained by rectangular pullback. No determinant
scaling formula is imposed on a general gauge.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart

def GaugeCompression.pullback {p r : ℕ} (G : GaugeCompression p)
    (A : Matrix (Fin p) (Fin r) ℝ) : GaugeCompression r where
  size := G.size
  gauge := G.gauge
  offset := G.offset
  offset_posSemidef := G.offset_posSemidef
  linear := Aᵀ * G.linear

theorem GaugeCompression.matrix_pullback {p r : ℕ} (G : GaugeCompression p)
    (A : Matrix (Fin p) (Fin r) ℝ) (X : SymmetricMatrix r) :
    (G.pullback A).matrix X = G.matrix (Matrix.symmetricCongruenceLinearMap A X) := by
  unfold GaugeCompression.matrix GaugeCompression.pullback
  rw [Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.symmetricCongruenceLinearMap_mul, LinearMap.comp_apply]

theorem GaugeCompression.value_pullback {p r : ℕ} (G : GaugeCompression p)
    (A : Matrix (Fin p) (Fin r) ℝ) (X : SymmetricMatrix r) :
    (G.pullback A).value X = G.value (Matrix.symmetricCongruenceLinearMap A X) := by
  unfold GaugeCompression.value
  rw [G.matrix_pullback]
  rfl

theorem gaugeMaximumProduct_pullback {p r : ℕ} {κ ι : Type*}
    [Fintype κ] [Fintype ι] [Nonempty ι]
    (G : κ → GaugeCompression p) (A : Matrix (Fin p) (Fin r) ℝ)
    (a b : κ → ι → ℝ) (X : SymmetricMatrix r) :
    gaugeMaximumProduct (fun i => (G i).pullback A) a b X =
      gaugeMaximumProduct G a b (Matrix.symmetricCongruenceLinearMap A X) := by
  simp only [gaugeMaximumProduct, GaugeCompression.value_pullback]

theorem gaugeFiniteTest_pullback {p r : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (G : GaugeCompression p) (A : Matrix (Fin p) (Fin r) ℝ)
    (a b : ι → ℝ) (X : SymmetricMatrix r) :
    gaugeFiniteTest (G.pullback A) a b X =
      gaugeFiniteTest G a b (Matrix.symmetricCongruenceLinearMap A X) := by
  simp only [gaugeFiniteTest, GaugeCompression.value_pullback]

def normalizedGaugeValue {p q : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (B : Matrix (Fin p) (Fin q) ℝ) (Φ : SpectralGauge q) (c : ℝ)
    (X : SymmetricMatrix p) : ℝ := shiftedGaugeValue Φ c (normalizedCompression Sigma B X)

theorem measurable_normalizedGaugeValue {p q : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (B : Matrix (Fin p) (Fin q) ℝ) (Φ : SpectralGauge q) (c : ℝ) :
    Measurable (normalizedGaugeValue Sigma B Φ c) :=
  (measurable_shiftedGaugeValue Φ c).comp (measurable_normalizedCompression Sigma B)

def normalizedGaugeCompression {p q : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (B : Matrix (Fin p) (Fin q) ℝ) (Φ : SpectralGauge q) (c : ℝ) (hc : 0 ≤ c) :
    GaugeCompression p where
  size := q
  gauge := Φ
  offset := c • SpectralGauge.identitySymmetric q
  offset_posSemidef := Matrix.PosSemidef.one.smul hc
  linear := (normalizedCompressionRows Sigma B)ᵀ

theorem normalizedGaugeCompression_value {p q : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (B : Matrix (Fin p) (Fin q) ℝ) (Φ : SpectralGauge q) {c : ℝ} (hc : 0 ≤ c)
    (X : SymmetricMatrix p) :
    (normalizedGaugeCompression Sigma B Φ c hc).value X = normalizedGaugeValue Sigma B Φ c X := by
  simp only [GaugeCompression.value, GaugeCompression.matrix, normalizedGaugeCompression,
    normalizedGaugeValue, shiftedGaugeValue, normalizedCompression, Matrix.transpose_transpose,
    add_comm]
  rfl

theorem normalizedGaugeValue_nonneg {p q : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (B : Matrix (Fin p) (Fin q) ℝ) (Φ : SpectralGauge q) (c : ℝ) (X : SymmetricMatrix p) :
    0 ≤ normalizedGaugeValue Sigma B Φ c X := Φ.value_nonneg _

/-- The totalized measurable expression agrees with the manuscript's literal
gauge at every PSD input, and therefore almost everywhere under its Wishart law. -/
theorem normalizedGaugeValue_eq_raw {p q : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (B : Matrix (Fin p) (Fin q) ℝ) (Φ : SpectralGauge q) {c : ℝ} (hc : 0 ≤ c)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    normalizedGaugeValue Sigma B Φ c X =
      Φ (normalizedCompression Sigma B X + c • SpectralGauge.identitySymmetric q) := by
  apply Φ.value_eq
  apply Matrix.PosSemidef.add _ (Matrix.PosSemidef.one.smul hc)
  simpa only [normalizedCompression, Matrix.coe_symmetricCongruenceLinearMap_apply,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    hX.mul_mul_conjTranspose_same (normalizedCompressionRows Sigma B)

theorem matrixTestAllMoments_normalizedGaugeValue {p q : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin q) ℝ)
    (Φ : SpectralGauge q) {c : ℝ} (hc : 0 ≤ c) :
    MatrixTestAllMoments (normalizedGaugeValue Sigma B Φ c) := by
  intro Ω _ μ _ X hm hp he
  simpa only [normalizedGaugeCompression_value] using
    (normalizedGaugeCompression Sigma B Φ c hc).matrixTestAllMoments_value hm hp he

def normalizedGaugeFiniteTest {p q : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin q) ℝ)
    (Φ : SpectralGauge q) (c : ℝ) (a b : ι → ℝ) (X : SymmetricMatrix p) : ℝ :=
  selectedGaugeFiniteTest Φ c a b (normalizedCompression Sigma B X)

theorem measurable_normalizedGaugeFiniteTest {p q : ℕ} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin q) ℝ)
    (Φ : SpectralGauge q) (c : ℝ) (a b : ι → ℝ) :
    Measurable (normalizedGaugeFiniteTest Sigma B Φ c a b) :=
  (measurable_selectedGaugeFiniteTest Φ c a b).comp (measurable_normalizedCompression Sigma B)

theorem normalizedGaugeFiniteTest_congruence_sum {q m : ℕ} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    {Sigma : Matrix (Fin (q + m)) (Fin (q + m)) ℝ} (hSigma : Sigma.PosDef)
    (B : Matrix (Fin (q + m)) (Fin q) ℝ) (hB : B.rank = q)
    (N : CompressionNormalization Sigma B) (Φ : SpectralGauge q) (c : ℝ) (a b : ι → ℝ)
    (X : SymmetricMatrix (q + m)) :
    normalizedGaugeFiniteTest Sigma B Φ c a b (Matrix.symmetricCongruenceLinearMap N.ambient X) =
      selectedGaugeFiniteTest Φ c a b (principalSymmetricBlock (Fin.castAdd m) X) := by
  unfold normalizedGaugeFiniteTest
  rw [normalizedCompression_congruence_sum hSigma B hB N X]

theorem normalizedGaugeFinite_split_of_identity {q m : ℕ} {n c : ℝ} {ι : Type*}
    [Fintype ι] [Nonempty ι]
    {Sigma : Matrix (Fin (q + m)) (Fin (q + m)) ℝ} (hSigma : Sigma.PosDef)
    (B : Matrix (Fin (q + m)) (Fin q) ℝ) (hB : B.rank = q)
    (Φ : SpectralGauge q) (a b : ι → ℝ)
    {F : SymmetricMatrix (q + m) → ℝ} (hFm : Measurable F)
    (hidentity :
      (∫ X, selectedGaugeFiniteTest Φ c a b (principalSymmetricBlock (Fin.castAdd m) X)
        ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) *
        (∫ X, F (Matrix.symmetricCongruenceLinearMap (compressionNormalization hSigma B hB).ambient X)
          ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) ≤
        ∫ X, selectedGaugeFiniteTest Φ c a b (principalSymmetricBlock (Fin.castAdd m) X) *
          F (Matrix.symmetricCongruenceLinearMap (compressionNormalization hSigma B hB).ambient X)
          ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) :
    (∫ X, normalizedGaugeFiniteTest Sigma B Φ c a b X ∂nonsingularWishartMeasure n Sigma) *
      (∫ X, F X ∂nonsingularWishartMeasure n Sigma) ≤
      ∫ X, normalizedGaugeFiniteTest Sigma B Φ c a b X * F X ∂nonsingularWishartMeasure n Sigma := by
  let N := compressionNormalization hSigma B hB
  have hpush := map_compressionNormalization n N
  have htransform (f : SymmetricMatrix (q + m) → ℝ) (hf : Measurable f) :
      (∫ X, f X ∂nonsingularWishartMeasure n Sigma) =
        ∫ Y, f (Matrix.symmetricCongruenceLinearMap N.ambient Y)
          ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) := by
    rw [← hpush, integral_map (LinearMap.continuous_of_finiteDimensional _).measurable.aemeasurable
      hf.aestronglyMeasurable]
  rw [htransform _ (measurable_normalizedGaugeFiniteTest Sigma B Φ c a b), htransform _ hFm,
    htransform (fun X => normalizedGaugeFiniteTest Sigma B Φ c a b X * F X)
      ((measurable_normalizedGaugeFiniteTest Sigma B Φ c a b).mul hFm)]
  simpa only [normalizedGaugeFiniteTest_congruence_sum hSigma B hB N] using hidentity

theorem normalizedGaugeFinite_selected_split {p q : ℕ} {n c : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (hdegree : (q : ℝ) + 1 ≤ n) (B : Matrix (Fin p) (Fin q) ℝ) (hB : B.rank = q)
    (Φ : SpectralGauge q) (hc : 0 ≤ c)
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (a₀ b₀ : ι → ℝ) (ha₀ : ∀ j, 0 ≤ a₀ j)
    (G : κ → GaugeCompression p) (a b : κ → ι → ℝ) (ha : ∀ i j, 0 ≤ a i j) :
    (∫ X, normalizedGaugeFiniteTest Sigma B Φ c a₀ b₀ X ∂nonsingularWishartMeasure n Sigma) *
      (∫ X, gaugeMaximumProduct G a b X ∂nonsingularWishartMeasure n Sigma) ≤
      ∫ X, normalizedGaugeFiniteTest Sigma B Φ c a₀ b₀ X * gaugeMaximumProduct G a b X
        ∂nonsingularWishartMeasure n Sigma := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (compressionNormalization hSigma B hB).q_le
  apply normalizedGaugeFinite_split_of_identity hSigma B hB Φ a₀ b₀
    (measurable_gaugeMaximumProduct G a b ha)
  simpa only [gaugeMaximumProduct_pullback] using
    identity_leading_gaugeFinite_split hn hdegree Φ hc a₀ b₀ ha₀
      (fun i => (G i).pullback (compressionNormalization hSigma B hB).ambient) a b ha

theorem normalizedGaugeFinite_pair {p q : ℕ} {n c : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (B : Matrix (Fin p) (Fin q) ℝ) (hB : B.rank = q) (Φ : SpectralGauge q) (hc : 0 ≤ c)
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (a₀ b₀ : ι → ℝ) (ha₀ : ∀ j, 0 ≤ a₀ j)
    (G : GaugeCompression p) (a b : ι → ℝ) (ha : ∀ j, 0 ≤ a j) :
    (∫ X, normalizedGaugeFiniteTest Sigma B Φ c a₀ b₀ X ∂nonsingularWishartMeasure n Sigma) *
      (∫ X, gaugeFiniteTest G a b X ∂nonsingularWishartMeasure n Sigma) ≤
      ∫ X, normalizedGaugeFiniteTest Sigma B Φ c a₀ b₀ X * gaugeFiniteTest G a b X
        ∂nonsingularWishartMeasure n Sigma := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (compressionNormalization hSigma B hB).q_le
  apply normalizedGaugeFinite_split_of_identity hSigma B hB Φ a₀ b₀ (measurable_gaugeFiniteTest G a b)
  simpa only [gaugeFiniteTest_pullback] using
    identity_leading_gaugeFinite_pair hn Φ hc a₀ b₀ ha₀
      (G.pullback (compressionNormalization hSigma B hB).ambient) a b ha

theorem identity_fullRank_gaugeFinite_split {p : ℕ} {n c : ℝ} (hn : (p : ℝ) - 1 < n)
    (Φ : SpectralGauge p) (hc : 0 ≤ c)
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (a₀ b₀ : ι → ℝ) (ha₀ : ∀ j, 0 ≤ a₀ j)
    (G : κ → GaugeCompression p) (a b : κ → ι → ℝ) (ha : ∀ i j, 0 ≤ a i j) :
    (∫ X, selectedGaugeFiniteTest Φ c a₀ b₀ X ∂nonsingularWishartMeasure n 1) *
      (∫ X, gaugeMaximumProduct G a b X ∂nonsingularWishartMeasure n 1) ≤
      ∫ X, selectedGaugeFiniteTest Φ c a₀ b₀ X * gaugeMaximumProduct G a b X
        ∂nonsingularWishartMeasure n 1 := by
  exact wholeMatrix_test_split hn (measurable_selectedGaugeFiniteTest Φ c a₀ b₀)
    (MatrixTestAllMoments.wishart (matrixTestAllMoments_selectedGaugeFiniteTest Φ hc a₀ b₀ ha₀) n 1)
    (measurable_selectedGaugeSpectralTest Φ c a₀ b₀)
    (fun lam => selectedGaugeFiniteTest_nonneg Φ c a₀ b₀ (Spectral.diagonalSym lam))
    (selectedGaugeSpectralTest_monotone Φ hc a₀ b₀ ha₀)
    (selectedGaugeFiniteTest_spectral Φ hc a₀ b₀)
    (measurable_gaugeMaximumProduct G a b ha) (matrixTestAllMoments_gaugeMaximumProduct G a b ha)
    (fun X _ => gaugeMaximumProduct_nonneg G a b X) (gaugeMaximumProduct_loewner G a b ha)

theorem normalizedGaugeFinite_fullRank_split {p : ℕ} {n c : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (B : Matrix (Fin p) (Fin p) ℝ) (hB : B.rank = p) (Φ : SpectralGauge p) (hc : 0 ≤ c)
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (a₀ b₀ : ι → ℝ) (ha₀ : ∀ j, 0 ≤ a₀ j)
    (G : κ → GaugeCompression p) (a b : κ → ι → ℝ) (ha : ∀ i j, 0 ≤ a i j) :
    (∫ X, normalizedGaugeFiniteTest Sigma B Φ c a₀ b₀ X ∂nonsingularWishartMeasure n Sigma) *
      (∫ X, gaugeMaximumProduct G a b X ∂nonsingularWishartMeasure n Sigma) ≤
      ∫ X, normalizedGaugeFiniteTest Sigma B Φ c a₀ b₀ X * gaugeMaximumProduct G a b X
        ∂nonsingularWishartMeasure n Sigma := by
  let N := compressionNormalization hSigma B hB
  have hpush := map_compressionNormalization n N
  have htransform (f : SymmetricMatrix p → ℝ) (hf : Measurable f) :
      (∫ X, f X ∂nonsingularWishartMeasure n Sigma) =
        ∫ Y, f (Matrix.symmetricCongruenceLinearMap N.ambient Y)
          ∂nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ) := by
    rw [← hpush, integral_map (LinearMap.continuous_of_finiteDimensional _).measurable.aemeasurable
      hf.aestronglyMeasurable]
  rw [htransform _ (measurable_normalizedGaugeFiniteTest Sigma B Φ c a₀ b₀),
    htransform _ (measurable_gaugeMaximumProduct G a b ha),
    htransform (fun X => normalizedGaugeFiniteTest Sigma B Φ c a₀ b₀ X * gaugeMaximumProduct G a b X)
      ((measurable_normalizedGaugeFiniteTest Sigma B Φ c a₀ b₀).mul
      (measurable_gaugeMaximumProduct G a b ha))]
  simpa only [normalizedGaugeFiniteTest, normalizedCompression_congruence_full hSigma B hB N,
    gaugeMaximumProduct_pullback] using
    identity_fullRank_gaugeFinite_split hn Φ hc a₀ b₀ ha₀
      (fun i => (G i).pullback N.ambient) a b ha

end Wishart
end
end CanonicalSource75

section CanonicalSource76
/- Source: Wishart/GaugeGeometricSplits.lean -/



/-!
# The full geometric outer-function gauge splits

All supporting-power comparisons are established under the actual Wishart law.
The final limit uses nonnegative extended integrals and strictly positive gauge
arguments on the nonsingular support. No polynomial-growth or integrability
restriction is imposed on the final outer functions.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped Matrix MatrixOrder Matrix.Norms.Operator ENNReal

namespace Wishart

theorem normalizedGaugeValue_pos {p q : ℕ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (B : Matrix (Fin p) (Fin q) ℝ) (hB : B.rank = q) (Φ : SpectralGauge q)
    {c : ℝ} (hc : 0 ≤ c) {X : SymmetricMatrix p}
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    0 < normalizedGaugeValue Sigma B Φ c X := by
  rw [normalizedGaugeValue_eq_raw Sigma B Φ hc hX.posSemidef]
  exact Φ.positive_of_posDef ((normalizedCompression_posDef hSigma B hB hX).add_posSemidef
    (Matrix.PosSemidef.one.smul hc))

theorem normalizedGauge_geometric_split_of_finite {p q : ℕ} {n c : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (B : Matrix (Fin p) (Fin q) ℝ) (hB : B.rank = q) (Φ : SpectralGauge q) (hc : 0 ≤ c)
    {κ : Type*} [Fintype κ]
    (k : κ → ℕ) (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hM : ∀ i, (M i).rank = k i) (Ψ : ∀ i, SpectralGauge (k i))
    (d : κ → ℝ) (hd : ∀ i, 0 ≤ d i)
    (f₀ : ℝ → ℝ) (f : κ → ℝ → ℝ)
    (hf₀ : GeometricallyLogConvex f₀) (hf : ∀ i, GeometricallyLogConvex (f i))
    (hfinite : ∀ l : ℕ, ∀ a₀ b₀ : Fin (l + 1) → ℝ,
      ∀ a b : κ → Fin (l + 1) → ℝ,
      (∀ j, 0 ≤ a₀ j) → (∀ i j, 0 ≤ a i j) →
      (∫ X, normalizedGaugeFiniteTest Sigma B Φ c a₀ b₀ X ∂nonsingularWishartMeasure n Sigma) *
        (∫ X, gaugeMaximumProduct
          (fun i => normalizedGaugeCompression Sigma (M i) (Ψ i) (d i) (hd i)) a b X
          ∂nonsingularWishartMeasure n Sigma) ≤
        ∫ X, normalizedGaugeFiniteTest Sigma B Φ c a₀ b₀ X *
          gaugeMaximumProduct
            (fun i => normalizedGaugeCompression Sigma (M i) (Ψ i) (d i) (hd i)) a b X
          ∂nonsingularWishartMeasure n Sigma) :
    (∫⁻ X, ENNReal.ofReal (f₀ (normalizedGaugeValue Sigma B Φ c X))
      ∂nonsingularWishartMeasure n Sigma) *
      (∫⁻ X, ENNReal.ofReal (∏ i, f i (normalizedGaugeValue Sigma (M i) (Ψ i) (d i) X))
        ∂nonsingularWishartMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (f₀ (normalizedGaugeValue Sigma B Φ c X) *
        ∏ i, f i (normalizedGaugeValue Sigma (M i) (Ψ i) (d i) X))
        ∂nonsingularWishartMeasure n Sigma := by
  let μ := nonsingularWishartMeasure n Sigma
  let G := fun i => normalizedGaugeCompression Sigma (M i) (Ψ i) (d i) (hd i)
  have h₀pos : ∀ᵐ X ∂μ, 0 < normalizedGaugeValue Sigma B Φ c X :=
    (ae_posDef_nonsingularWishartMeasure n Sigma).mono fun X hX =>
      normalizedGaugeValue_pos hSigma B hB Φ hc hX
  have hpos : ∀ᵐ X ∂μ, ∀ i, 0 < normalizedGaugeValue Sigma (M i) (Ψ i) (d i) X :=
    (ae_posDef_nonsingularWishartMeasure n Sigma).mono fun X hX i =>
      normalizedGaugeValue_pos hSigma (M i) (hM i) (Ψ i) (hd i) hX
  apply geometric_outer_selected_split_of_finite_splits μ
    (normalizedGaugeValue Sigma B Φ c)
    (fun X i => normalizedGaugeValue Sigma (M i) (Ψ i) (d i) X)
    (measurable_normalizedGaugeValue Sigma B Φ c)
    (measurable_pi_iff.mpr fun i => measurable_normalizedGaugeValue Sigma (M i) (Ψ i) (d i))
    h₀pos hpos _ f₀ f hf₀ hf
  intro l a₀ b₀ a b ha₀ ha
  let selected := normalizedGaugeFiniteTest Sigma B Φ c a₀ b₀
  let remaining := gaugeMaximumProduct G a b
  have hsM : HasAllFiniteMoments selected μ :=
    hasAllFiniteMoments_finiteMaximum _ fun j =>
      ((MatrixTestAllMoments.wishart (matrixTestAllMoments_normalizedGaugeValue Sigma B Φ hc) n Sigma).rpow
        (ha₀ j)).const_mul (Real.exp (b₀ j))
  have hrM : HasAllFiniteMoments remaining μ :=
    MatrixTestAllMoments.wishart (matrixTestAllMoments_gaugeMaximumProduct G a b ha) n Sigma
  have hs0 : ∀ᵐ X ∂μ, 0 ≤ selected X := Filter.Eventually.of_forall fun X =>
    selectedGaugeFiniteTest_nonneg Φ c a₀ b₀ (normalizedCompression Sigma B X)
  have hr0 : ∀ᵐ X ∂μ, 0 ≤ remaining X := Filter.Eventually.of_forall fun X =>
    gaugeMaximumProduct_nonneg G a b X
  have h := ENNReal.ofReal_le_ofReal (hfinite l a₀ b₀ a b ha₀ ha)
  rw [ENNReal.ofReal_mul (integral_nonneg_of_ae hs0),
    ofReal_integral_eq_lintegral_ofReal hsM.integrable hs0,
    ofReal_integral_eq_lintegral_ofReal hrM.integrable hr0,
    ofReal_integral_eq_lintegral_ofReal (hsM.mul hrM).integrable
      (by filter_upwards [hs0, hr0] with X hs hr; exact mul_nonneg hs hr)] at h
  simpa only [selected, remaining, G, gaugeMaximumProduct, normalizedGaugeCompression_value,
    normalizedGaugeFiniteTest, selectedGaugeFiniteTest, normalizedGaugeValue] using h

/-- The proper selected-factor assertion of Theorem 5.2, with exactly n≥q+1
and with arbitrary full-rank overlapping compressions and all geometric outers. -/
theorem normalizedGauge_geometric_selected_split {p q : ℕ} {n c : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (hdegree : (q : ℝ) + 1 ≤ n)
    (B : Matrix (Fin p) (Fin q) ℝ) (hB : B.rank = q) (Φ : SpectralGauge q) (hc : 0 ≤ c)
    {κ : Type*} [Fintype κ]
    (k : κ → ℕ) (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hM : ∀ i, (M i).rank = k i) (Ψ : ∀ i, SpectralGauge (k i))
    (d : κ → ℝ) (hd : ∀ i, 0 ≤ d i)
    (f₀ : ℝ → ℝ) (f : κ → ℝ → ℝ)
    (hf₀ : GeometricallyLogConvex f₀) (hf : ∀ i, GeometricallyLogConvex (f i)) :
    (∫⁻ X, ENNReal.ofReal (f₀ (normalizedGaugeValue Sigma B Φ c X))
      ∂nonsingularWishartMeasure n Sigma) *
      (∫⁻ X, ENNReal.ofReal (∏ i, f i (normalizedGaugeValue Sigma (M i) (Ψ i) (d i) X))
        ∂nonsingularWishartMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (f₀ (normalizedGaugeValue Sigma B Φ c X) *
        ∏ i, f i (normalizedGaugeValue Sigma (M i) (Ψ i) (d i) X))
        ∂nonsingularWishartMeasure n Sigma := by
  apply normalizedGauge_geometric_split_of_finite hSigma hn B hB Φ hc k M hM Ψ d hd f₀ f hf₀ hf
  intro l a₀ b₀ a b ha₀ ha
  exact normalizedGaugeFinite_selected_split hSigma hn hdegree B hB Φ hc a₀ b₀ ha₀
    (fun i => normalizedGaugeCompression Sigma (M i) (Ψ i) (d i) (hd i)) a b ha

theorem normalizedGauge_geometric_pair {p q k : ℕ} {n c d : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (B : Matrix (Fin p) (Fin q) ℝ) (hB : B.rank = q) (Φ : SpectralGauge q) (hc : 0 ≤ c)
    (M : Matrix (Fin p) (Fin k) ℝ) (hM : M.rank = k) (Ψ : SpectralGauge k) (hd : 0 ≤ d)
    (f g : ℝ → ℝ) (hf : GeometricallyLogConvex f) (hg : GeometricallyLogConvex g) :
    (∫⁻ X, ENNReal.ofReal (f (normalizedGaugeValue Sigma B Φ c X))
      ∂nonsingularWishartMeasure n Sigma) *
      (∫⁻ X, ENNReal.ofReal (g (normalizedGaugeValue Sigma M Ψ d X))
        ∂nonsingularWishartMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (f (normalizedGaugeValue Sigma B Φ c X) *
        g (normalizedGaugeValue Sigma M Ψ d X)) ∂nonsingularWishartMeasure n Sigma := by
  have h := normalizedGauge_geometric_split_of_finite hSigma hn B hB Φ hc
    (fun _ : Unit => k) (fun _ => M) (fun _ => hM) (fun _ => Ψ)
    (fun _ => d) (fun _ => hd) f (fun _ => g) hf (fun _ => hg) (by
      intro l a₀ b₀ a b ha₀ ha
      simpa only [gaugeMaximumProduct, finiteOuterTest, Fintype.prod_unique, gaugeFiniteTest] using
        normalizedGaugeFinite_pair hSigma hn B hB Φ hc a₀ b₀ ha₀
          (normalizedGaugeCompression Sigma M Ψ d hd) (a ()) (b ()) (ha ()))
  simpa only [Fintype.prod_unique] using h

/-- Every full-rank selected gauge splits throughout the nonsingular real-shape
range. This uses whole-spectrum association and no radial degree bound. -/
theorem normalizedGauge_geometric_fullRank_split {p : ℕ} {n c : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (B : Matrix (Fin p) (Fin p) ℝ) (hB : B.rank = p) (Φ : SpectralGauge p) (hc : 0 ≤ c)
    {κ : Type*} [Fintype κ]
    (k : κ → ℕ) (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hM : ∀ i, (M i).rank = k i) (Ψ : ∀ i, SpectralGauge (k i))
    (d : κ → ℝ) (hd : ∀ i, 0 ≤ d i)
    (f₀ : ℝ → ℝ) (f : κ → ℝ → ℝ)
    (hf₀ : GeometricallyLogConvex f₀) (hf : ∀ i, GeometricallyLogConvex (f i)) :
    (∫⁻ X, ENNReal.ofReal (f₀ (normalizedGaugeValue Sigma B Φ c X))
      ∂nonsingularWishartMeasure n Sigma) *
      (∫⁻ X, ENNReal.ofReal (∏ i, f i (normalizedGaugeValue Sigma (M i) (Ψ i) (d i) X))
        ∂nonsingularWishartMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (f₀ (normalizedGaugeValue Sigma B Φ c X) *
        ∏ i, f i (normalizedGaugeValue Sigma (M i) (Ψ i) (d i) X))
        ∂nonsingularWishartMeasure n Sigma := by
  apply normalizedGauge_geometric_split_of_finite hSigma hn B hB Φ hc k M hM Ψ d hd f₀ f hf₀ hf
  intro l a₀ b₀ a b ha₀ ha
  exact normalizedGaugeFinite_fullRank_split hSigma hn B hB Φ hc a₀ b₀ ha₀
    (fun i => normalizedGaugeCompression Sigma (M i) (Ψ i) (d i) (hd i)) a b ha

end Wishart
end
end CanonicalSource76

section CanonicalSource77
/- Source: Wishart/GaugeRankIteration.lean -/



/-! # The exact third-largest-rank threshold for convex gauges -/

noncomputable section

open scoped Classical ENNReal BigOperators

namespace WishartVerification.MomentAssembly

variable {ι : Type*} [DecidableEq ι]

def gaugeRankTripleThreshold (rank : ι → ℕ) (A : Finset ι) (n : ℝ) : Prop :=
  ∀ i ∈ A, ∀ j ∈ A, ∀ k ∈ A,
    i ≠ j → i ≠ k → j ≠ k → rank i ≤ rank j → rank i ≤ rank k → (rank i : ℝ) + 1 ≤ n

def orderedGaugeRankThreshold (rank : ι → ℕ) (A : Finset ι) (n : ℝ) : Prop :=
  ∀ h : 3 ≤ Fintype.card A, (descendingRanks rank A ⟨2, by omega⟩ : ℝ) + 1 ≤ n

theorem gaugeRankTripleThreshold_of_card_le_two (rank : ι → ℕ) (A : Finset ι)
    (n : ℝ) (hA : A.card ≤ 2) : gaugeRankTripleThreshold rank A n := by
  intro i hi j hj k hk hij hik hjk _ _
  have hsub : ({i, j, k} : Finset ι) ⊆ A := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> assumption
  have hcard : ({i, j, k} : Finset ι).card = 3 := by simp [hij, hik, hjk]
  have hle := Finset.card_le_card hsub
  omega

theorem gaugeRankTripleThreshold_equiv {κ : Type*} [Fintype κ] [DecidableEq κ]
    (rank : ι → ℕ) (A : Finset ι) (e : κ ≃ A) (n : ℝ) :
    gaugeRankTripleThreshold rank A n ↔
      gaugeRankTripleThreshold (fun i => rank (e i)) Finset.univ n := by
  constructor
  · intro h i _ j _ k _ hij hik hjk hrij hrik
    apply h (e i) (e i).property (e j) (e j).property (e k) (e k).property
    · intro heq
      exact hij (e.injective (Subtype.ext heq))
    · intro heq
      exact hik (e.injective (Subtype.ext heq))
    · intro heq
      exact hjk (e.injective (Subtype.ext heq))
    · exact hrij
    · exact hrik
  · intro h i hi j hj k hk hij hik hjk hrij hrik
    have hne (a b : A) (hab : (a : ι) ≠ b) : e.symm a ≠ e.symm b := by
      intro heq
      exact hab (congrArg Subtype.val (e.symm.injective heq))
    have h' := h (e.symm ⟨i, hi⟩) (Finset.mem_univ _)
      (e.symm ⟨j, hj⟩) (Finset.mem_univ _) (e.symm ⟨k, hk⟩) (Finset.mem_univ _)
      (hne _ _ hij) (hne _ _ hik) (hne _ _ hjk)
      (by simpa only [Equiv.apply_symm_apply] using hrij)
      (by simpa only [Equiv.apply_symm_apply] using hrik)
    simpa only [Equiv.apply_symm_apply] using h'

theorem gaugeRankTripleThreshold_iff_third {d : ℕ} (hd : 3 ≤ d)
    (rank : Fin d → ℕ) (hsorted : Antitone rank) (n : ℝ) :
    gaugeRankTripleThreshold rank Finset.univ n ↔ (rank ⟨2, by omega⟩ : ℝ) + 1 ≤ n := by
  constructor
  · intro h
    exact h ⟨2, by omega⟩ (Finset.mem_univ _) ⟨0, by omega⟩ (Finset.mem_univ _)
      ⟨1, by omega⟩ (Finset.mem_univ _)
      (by intro heq; have hv := congrArg Fin.val heq; change (2 : ℕ) = 0 at hv; omega)
      (by intro heq; have hv := congrArg Fin.val heq; change (2 : ℕ) = 1 at hv; omega)
      (by intro heq; have hv := congrArg Fin.val heq; change (0 : ℕ) = 1 at hv; omega)
      (hsorted (show (⟨0, by omega⟩ : Fin d) ≤ ⟨2, by omega⟩ from by
        change (0 : ℕ) ≤ 2; decide))
      (hsorted (show (⟨1, by omega⟩ : Fin d) ≤ ⟨2, by omega⟩ from by
        change (1 : ℕ) ≤ 2; decide))
  · intro h i _ j _ k _ hij hik hjk hrij hrik
    have hijv : i.val ≠ j.val := fun heq => hij (Fin.ext heq)
    have hikv : i.val ≠ k.val := fun heq => hik (Fin.ext heq)
    have hjkv : j.val ≠ k.val := fun heq => hjk (Fin.ext heq)
    have hindices : 2 ≤ i.val ∨ 2 ≤ j.val ∨ 2 ≤ k.val := by omega
    have hi3 : rank i ≤ rank ⟨2, by omega⟩ := by
      rcases hindices with hi | hj | hk
      · exact hsorted hi
      · exact hrij.trans (hsorted hj)
      · exact hrik.trans (hsorted hk)
    have hi3' : (rank i : ℝ) ≤ rank ⟨2, by omega⟩ := Nat.cast_le.mpr hi3
    linarith

theorem orderedGaugeRankThreshold_iff (rank : ι → ℕ) (A : Finset ι) (n : ℝ) :
    orderedGaugeRankThreshold rank A n ↔ gaugeRankTripleThreshold rank A n := by
  rw [gaugeRankTripleThreshold_equiv rank A (descendingRankEquiv rank A) n]
  change orderedGaugeRankThreshold rank A n ↔
    gaugeRankTripleThreshold (descendingRanks rank A) Finset.univ n
  by_cases hd : 3 ≤ Fintype.card A
  · rw [gaugeRankTripleThreshold_iff_third hd _ (antitone_descendingRanks rank A)]
    exact ⟨fun h => h hd, fun h _ => h⟩
  · constructor
    · intro _
      apply gaugeRankTripleThreshold_of_card_le_two
      simpa only [Finset.card_univ, Fintype.card_fin] using (show Fintype.card A ≤ 2 by omega)
    · intro _ h
      exact (hd h).elim

theorem extended_product_singletons_le_by_gauge_rank (m : Finset ι → ℝ≥0∞)
    (rank : ι → ℕ) (A : Finset ι) (n : ℝ)
    (hempty : m ∅ = 1)
    (houtside : ∀ J i, i ∈ J → i ∉ A → m {i} * m (J.erase i) ≤ m J)
    (hpair : ∀ J i, i ∈ J → J.card ≤ 2 → m {i} * m (J.erase i) ≤ m J)
    (hrank : ∀ J i, i ∈ J → (rank i : ℝ) + 1 ≤ n → m {i} * m (J.erase i) ≤ m J)
    (hthreshold : orderedGaugeRankThreshold rank A n) (J : Finset ι) :
    (∏ i ∈ J, m {i}) ≤ m J := by
  apply extended_product_singletons_le_of_exists_split m hempty (fun _ => bot_le) _ J
  intro S hS
  by_cases hout : ∃ i ∈ S, i ∉ A
  · obtain ⟨i, hi, hiA⟩ := hout
    exact ⟨i, hi, houtside S i hi hiA⟩
  have hSA : S ⊆ A := by
    intro i hi
    by_contra hiA
    exact hout ⟨i, hi, hiA⟩
  by_cases hsmall : S.card ≤ 2
  · obtain ⟨i, hi⟩ := hS
    exact ⟨i, hi, hpair S i hi hsmall⟩
  obtain ⟨i, hi, hmin⟩ := S.exists_min_image rank hS
  obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr
    (show S.erase i ≠ ∅ by
      intro he
      have hcard := Finset.card_erase_of_mem hi
      rw [he, Finset.card_empty] at hcard
      omega)
  have hjS := Finset.mem_of_mem_erase hj
  have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
  have hex : ∃ k ∈ S, k ≠ i ∧ k ≠ j := by
    by_contra hnone
    have hsub : S ⊆ ({i, j} : Finset ι) := by
      intro k hk
      by_cases hki : k = i
      · simp [hki]
      · have hkj : k = j := by
          by_contra hkj
          exact hnone ⟨k, hk, hki, hkj⟩
        simp [hkj]
    exact hsmall ((Finset.card_le_card hsub).trans Finset.card_le_two)
  obtain ⟨k, hk, hki, hkj⟩ := hex
  exact ⟨i, hi, hrank S i hi
    ((orderedGaugeRankThreshold_iff rank A n).mp hthreshold i (hSA hi) j (hSA hjS) k (hSA hk)
      hij hki.symm hkj.symm (hmin j hjS) (hmin k hk))⟩

end WishartVerification.MomentAssembly
end
end CanonicalSource77

section CanonicalSource78
/- Source: Wishart/GaugeProducts.lean -/



/-!
# The full spectral-gauge product inequality

Every factor is evaluated on its covariance-normalized compression. The exact
third-largest-rank condition is applied after removing literal constant factors
and full-rank factors. All expectations are nonnegative extended integrals.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification WishartVerification.MomentAssembly
open scoped Classical BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart

structure GeometricGaugeFamily (p : ℕ) (ι : Type*) where
  size : ι → ℕ
  matrix : ∀ i, Matrix (Fin p) (Fin (size i)) ℝ
  full_rank : ∀ i, (matrix i).rank = size i
  gauge : ∀ i, SpectralGauge (size i)
  shift : ι → ℝ
  shift_nonneg : ∀ i, 0 ≤ shift i
  outer : ι → ℝ → ℝ
  geometric : ∀ i, GeometricallyLogConvex (outer i)

namespace GeometricGaugeFamily

variable {p : ℕ} {ι : Type*} [DecidableEq ι]
variable (F : GeometricGaugeFamily p ι) (Sigma : Matrix (Fin p) (Fin p) ℝ)

def factor (i : ι) (X : SymmetricMatrix p) : ℝ :=
  F.outer i (normalizedGaugeValue Sigma (F.matrix i) (F.gauge i) (F.shift i) X)

def subproduct (J : Finset ι) (X : SymmetricMatrix p) : ℝ := ∏ i ∈ J, F.factor Sigma i X

def moment (n : ℝ) (J : Finset ι) : ℝ≥0∞ :=
  ∫⁻ X, ENNReal.ofReal (F.subproduct Sigma J X) ∂nonsingularWishartMeasure n Sigma

def ConstantFactor (i : ι) : Prop :=
  ∃ c : ℝ, ∀ X : SymmetricMatrix p,
    (X : Matrix (Fin p) (Fin p) ℝ).PosDef → F.factor Sigma i X = c

def activeProper [Fintype ι] : Finset ι :=
  Finset.univ.filter (fun i => F.size i < p ∧ ¬ F.ConstantFactor Sigma i)

theorem size_le (i : ι) : F.size i ≤ p := by
  rw [← F.full_rank i]
  exact (F.matrix i).rank_le_height

theorem factor_eq_raw (i : ι) {X : SymmetricMatrix p}
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    F.factor Sigma i X = F.outer i (F.gauge i
      (normalizedCompression Sigma (F.matrix i) X + F.shift i • SpectralGauge.identitySymmetric (F.size i))) := by
  unfold factor
  rw [normalizedGaugeValue_eq_raw Sigma (F.matrix i) (F.gauge i) (F.shift_nonneg i) hX]

theorem factor_pos (hSigma : Sigma.PosDef) (i : ι) {X : SymmetricMatrix p}
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosDef) : 0 < F.factor Sigma i X :=
  (F.geometric i).positive _
    (normalizedGaugeValue_pos hSigma (F.matrix i) (F.full_rank i) (F.gauge i) (F.shift_nonneg i) hX)

theorem aemeasurable_factor {n : ℝ} (hSigma : Sigma.PosDef) (i : ι) :
    AEMeasurable (F.factor Sigma i) (nonsingularWishartMeasure n Sigma) := by
  apply aemeasurable_geometric_outer_comp (F.geometric i)
    (measurable_normalizedGaugeValue Sigma (F.matrix i) (F.gauge i) (F.shift i))
  exact (ae_posDef_nonsingularWishartMeasure n Sigma).mono fun X hX =>
    normalizedGaugeValue_pos hSigma (F.matrix i) (F.full_rank i) (F.gauge i) (F.shift_nonneg i) hX

theorem aemeasurable_subproduct {n : ℝ} (hSigma : Sigma.PosDef) (J : Finset ι) :
    AEMeasurable (F.subproduct Sigma J) (nonsingularWishartMeasure n Sigma) :=
  Finset.aemeasurable_fun_prod J (fun i _ => F.aemeasurable_factor Sigma hSigma i)

@[simp] theorem moment_singleton (n : ℝ) (i : ι) :
    F.moment Sigma n {i} =
      ∫⁻ X, ENNReal.ofReal (F.factor Sigma i X) ∂nonsingularWishartMeasure n Sigma := by
  simp only [moment, subproduct, Finset.prod_singleton]

theorem moment_empty {n : ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n) :
    F.moment Sigma n ∅ = 1 := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure hSigma hn
  simp only [moment, subproduct, Finset.prod_empty, ENNReal.ofReal_one,
    lintegral_const, measure_univ, mul_one]

theorem moment_split (n : ℝ) (J : Finset ι) (i : ι) (hi : i ∈ J) :
    F.moment Sigma n J =
      ∫⁻ X, ENNReal.ofReal (F.factor Sigma i X * F.subproduct Sigma (J.erase i) X)
        ∂nonsingularWishartMeasure n Sigma := by
  apply lintegral_congr_ae
  filter_upwards with X
  congr 1
  exact (Finset.mul_prod_erase J (fun i => F.factor Sigma i X) hi).symm

theorem moment_constant_split {n : ℝ}
    (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (J : Finset ι) (i : ι) (hi : i ∈ J) (hconst : F.ConstantFactor Sigma i) :
    F.moment Sigma n {i} * F.moment Sigma n (J.erase i) = F.moment Sigma n J := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure hSigma hn
  obtain ⟨c, hc⟩ := hconst
  have hcpos : 0 < c := by
    rw [← hc ⟨Sigma, hSigma.isHermitian.isSelfAdjoint⟩ hSigma]
    exact F.factor_pos Sigma hSigma i hSigma
  have hcae : ∀ᵐ X ∂nonsingularWishartMeasure n Sigma, F.factor Sigma i X = c :=
    (ae_posDef_nonsingularWishartMeasure n Sigma).mono fun X hX => hc X hX
  have hsingle : F.moment Sigma n {i} = ENNReal.ofReal c := by
    rw [F.moment_singleton]
    calc
      (∫⁻ X, ENNReal.ofReal (F.factor Sigma i X) ∂nonsingularWishartMeasure n Sigma) =
          ∫⁻ _X, ENNReal.ofReal c ∂nonsingularWishartMeasure n Sigma :=
        lintegral_congr_ae (hcae.mono fun X hX => congrArg ENNReal.ofReal hX)
      _ = _ := by simp only [lintegral_const, measure_univ, mul_one]
  rw [hsingle, F.moment_split Sigma n J i hi]
  calc
    ENNReal.ofReal c * F.moment Sigma n (J.erase i) =
        ∫⁻ X, ENNReal.ofReal c * ENNReal.ofReal (F.subproduct Sigma (J.erase i) X)
          ∂nonsingularWishartMeasure n Sigma :=
      (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hcae] with X hX
      rw [hX, ENNReal.ofReal_mul hcpos.le]

theorem moment_selected_split {n : ℝ}
    (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (J : Finset ι) (i : ι) (hi : i ∈ J) (hdegree : (F.size i : ℝ) + 1 ≤ n) :
    F.moment Sigma n {i} * F.moment Sigma n (J.erase i) ≤ F.moment Sigma n J := by
  have h := normalizedGauge_geometric_selected_split hSigma hn hdegree
    (F.matrix i) (F.full_rank i) (F.gauge i) (F.shift_nonneg i)
    (fun j : J.erase i => F.size j) (fun j => F.matrix j) (fun j => F.full_rank j)
    (fun j => F.gauge j) (fun j => F.shift j) (fun j => F.shift_nonneg j)
    (F.outer i) (fun j => F.outer j) (F.geometric i) (fun j => F.geometric j)
  change (∫⁻ X, ENNReal.ofReal (F.factor Sigma i X) ∂nonsingularWishartMeasure n Sigma) *
      (∫⁻ X, ENNReal.ofReal (∏ j : J.erase i, F.factor Sigma (j : ι) X)
        ∂nonsingularWishartMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (F.factor Sigma i X *
        ∏ j : J.erase i, F.factor Sigma (j : ι) X) ∂nonsingularWishartMeasure n Sigma at h
  rw [F.moment_singleton, F.moment_split Sigma n J i hi]
  have hprod (X : SymmetricMatrix p) :
      (∏ j : J.erase i, F.factor Sigma (j : ι) X) =
        F.subproduct Sigma (J.erase i) X :=
    Finset.prod_coe_sort (J.erase i) (fun j => F.factor Sigma j X)
  simp_rw [hprod] at h
  simpa only [moment] using h

theorem moment_full_rank_split {n : ℝ}
    (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (J : Finset ι) (i : ι) (hi : i ∈ J) (hfull : F.size i = p) :
    F.moment Sigma n {i} * F.moment Sigma n (J.erase i) ≤ F.moment Sigma n J := by
  have hsplit (q : ℕ) (Q : Matrix (Fin p) (Fin q) ℝ) (hQ : Q.rank = q)
      (Φ : SpectralGauge q) (hqp : q = p) :
      (∫⁻ X, ENNReal.ofReal (F.outer i (normalizedGaugeValue Sigma Q Φ (F.shift i) X))
        ∂nonsingularWishartMeasure n Sigma) * F.moment Sigma n (J.erase i) ≤
        ∫⁻ X, ENNReal.ofReal (F.outer i (normalizedGaugeValue Sigma Q Φ (F.shift i) X) *
          F.subproduct Sigma (J.erase i) X) ∂nonsingularWishartMeasure n Sigma := by
    subst q
    have h := normalizedGauge_geometric_fullRank_split hSigma hn Q hQ Φ (F.shift_nonneg i)
      (fun j : J.erase i => F.size j) (fun j => F.matrix j) (fun j => F.full_rank j)
      (fun j => F.gauge j) (fun j => F.shift j) (fun j => F.shift_nonneg j)
      (F.outer i) (fun j => F.outer j) (F.geometric i) (fun j => F.geometric j)
    change (∫⁻ X, ENNReal.ofReal
        (F.outer i (normalizedGaugeValue Sigma Q Φ (F.shift i) X))
        ∂nonsingularWishartMeasure n Sigma) *
        (∫⁻ X, ENNReal.ofReal (∏ j : J.erase i, F.factor Sigma (j : ι) X)
          ∂nonsingularWishartMeasure n Sigma) ≤
        ∫⁻ X, ENNReal.ofReal
          (F.outer i (normalizedGaugeValue Sigma Q Φ (F.shift i) X) *
            ∏ j : J.erase i, F.factor Sigma (j : ι) X)
          ∂nonsingularWishartMeasure n Sigma at h
    have hprod (X : SymmetricMatrix p) :
        (∏ j : J.erase i, F.factor Sigma (j : ι) X) =
          F.subproduct Sigma (J.erase i) X :=
      Finset.prod_coe_sort (J.erase i) (fun j => F.factor Sigma j X)
    simp_rw [hprod] at h
    simpa only [moment] using h
  rw [F.moment_singleton, F.moment_split Sigma n J i hi]
  exact hsplit (F.size i) (F.matrix i) (F.full_rank i) (F.gauge i) hfull

theorem moment_pair_split {n : ℝ}
    (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (J : Finset ι) (i : ι) (hi : i ∈ J) (hsmall : J.card ≤ 2) :
    F.moment Sigma n {i} * F.moment Sigma n (J.erase i) ≤ F.moment Sigma n J := by
  have hcard : (J.erase i).card ≤ 1 := by rw [Finset.card_erase_of_mem hi]; omega
  by_cases hrest : J.erase i = ∅
  · have hJ : J = {i} := by
      have h := Finset.insert_erase hi
      rw [hrest, Finset.insert_empty] at h
      exact h.symm
    rw [hrest, hJ, F.moment_empty Sigma hSigma hn, mul_one]
  · have hcard' : (J.erase i).card = 1 := by
      have hp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hrest)
      omega
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard'
    have h := normalizedGauge_geometric_pair hSigma hn
      (F.matrix i) (F.full_rank i) (F.gauge i) (F.shift_nonneg i)
      (F.matrix j) (F.full_rank j) (F.gauge j) (F.shift_nonneg j)
      (F.outer i) (F.outer j) (F.geometric i) (F.geometric j)
    rw [F.moment_singleton, F.moment_split Sigma n J i hi, hj, F.moment_singleton]
    simpa only [factor, subproduct, Finset.prod_singleton] using h

theorem moment_split_outside_activeProper [Fintype ι] {n : ℝ}
    (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (J : Finset ι) (i : ι) (hi : i ∈ J) (hinactive : i ∉ F.activeProper Sigma) :
    F.moment Sigma n {i} * F.moment Sigma n (J.erase i) ≤ F.moment Sigma n J := by
  by_cases hc : F.ConstantFactor Sigma i
  · exact (F.moment_constant_split Sigma hSigma hn J i hi hc).le
  have hfull : F.size i = p := by
    have hle := F.size_le i
    by_contra hne
    have hklt : F.size i < p := lt_of_le_of_ne hle hne
    exact hinactive (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hklt, hc⟩)
  exact F.moment_full_rank_split Sigma hSigma hn J i hi hfull

/-- The full Theorem 5.2 geometric gauge product inequality. The condition is
vacuous for at most two retained factors, and otherwise is exactly n≥k_(3)+1. -/
theorem product_moments_le [Fintype ι] {n : ℝ}
    (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (hsize : orderedGaugeRankThreshold F.size (F.activeProper Sigma) n) (J : Finset ι) :
    (∏ i ∈ J, F.moment Sigma n {i}) ≤ F.moment Sigma n J :=
  extended_product_singletons_le_by_gauge_rank (F.moment Sigma n) F.size (F.activeProper Sigma) n
    (F.moment_empty Sigma hSigma hn) (F.moment_split_outside_activeProper Sigma hSigma hn)
    (F.moment_pair_split Sigma hSigma hn) (F.moment_selected_split Sigma hSigma hn) hsize J

theorem product_integrals_le_integral_product [Fintype ι] {n : ℝ}
    (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (hsize : orderedGaugeRankThreshold F.size (F.activeProper Sigma) n) :
    (∏ i, ∫⁻ X, ENNReal.ofReal (F.factor Sigma i X) ∂nonsingularWishartMeasure n Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (∏ i, F.factor Sigma i X) ∂nonsingularWishartMeasure n Sigma := by
  simpa only [moment_singleton, moment, subproduct, Finset.prod_singleton] using
    F.product_moments_le Sigma hSigma hn hsize Finset.univ

end GeometricGaugeFamily

end Wishart
end
end CanonicalSource78

section CanonicalSource79
/- Source: Wishart/SpectralConvexApproximation.lean -/



/-!
# Supporting planes for symmetric increasing convex spectral profiles

The countable affine approximation is supplied by the proved separation theorem
in Mathlib. Monotonicity on the whole coordinate space forces every coefficient
to be nonnegative. Symmetry permits sorting each coefficient vector in decreasing
order while preserving its global minorant property. Rearrangement proves that
these sorted planes still have the original function as their supremum on the
decreasing chamber.
-/

noncomputable section

open Set Filter Topology
open scoped Classical

namespace Wishart.Spectral

def SymmetricProfile {k : ℕ} (h : (Fin k → ℝ) → ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin k)) (x : Fin k → ℝ), h (x ∘ σ) = h x

def coordinatePlane {k : ℕ} (a : Fin k → ℝ) (b : ℝ) (x : Fin k → ℝ) : ℝ :=
  (∑ i, a i * x i) + b

theorem linearForm_eq_coordinate_sum {k : ℕ}
    (l : (Fin k → ℝ) →L[ℝ] ℝ) (x : Fin k → ℝ) :
    l x = ∑ i, l (Pi.single i 1) * x i := by
  have hx : x = ∑ i : Fin k, x i • Pi.single i (1 : ℝ) := by
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    simp
  conv_lhs => rw [hx, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [map_smul, smul_eq_mul, mul_comm]

theorem linearForm_single {k : ℕ} (l : (Fin k → ℝ) →L[ℝ] ℝ)
    (i : Fin k) (t : ℝ) : l (Pi.single i t) = l (Pi.single i 1) * t := by
  have hs : Pi.single i t = t • Pi.single i (1 : ℝ) := by
    ext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [Pi.single_apply, hji, Ne.symm hji]
  rw [hs, map_smul, smul_eq_mul, mul_comm]

theorem coordinate_coeff_nonneg {k : ℕ} {h : (Fin k → ℝ) → ℝ}
    (hm : Monotone h) (l : (Fin k → ℝ) →L[ℝ] ℝ) (b : ℝ)
    (hle : ∀ x, l x + b ≤ h x) (i : Fin k) : 0 ≤ l (Pi.single i 1) := by
  have hmline : Monotone (fun t : ℝ => h (Pi.single i t)) := by
    intro s t hst
    apply hm
    intro j
    by_cases hji : j = i
    · subst j
      simpa using hst
    · simp [Pi.single_apply, hji, Ne.symm hji]
  apply WishartVerification.nonnegative_slope_of_affine_minorant hmline
  intro t
  have ht := hle (Pi.single i t)
  rw [linearForm_single] at ht
  exact ht

theorem exists_nonnegative_coordinate_minorants {k : ℕ}
    {h : (Fin k → ℝ) → ℝ} (hc : ConvexOn ℝ Set.univ h) (hm : Monotone h) :
    ∃ (a : ℕ → Fin k → ℝ) (b : ℕ → ℝ),
      (∀ n i, 0 ≤ a n i) ∧
      (∀ n x, coordinatePlane (a n) (b n) x ≤ h x) ∧
      (∀ x, (⨆ n, coordinatePlane (a n) (b n) x) = h x) := by
  have hcont : Continuous h := by
    simpa only [interior_univ, continuousOn_univ] using hc.continuousOn_interior
  obtain ⟨l, b, hle, hsup⟩ := hc.real_univ_sSup_of_nat_affine_eq hcont.lowerSemicontinuous
  have hl (n : ℕ) (x : Fin k → ℝ) : l n x + b n ≤ h x := by
    simpa only [Pi.add_apply, Function.const_apply] using hle n x
  refine ⟨fun n i => l n (Pi.single i 1), b,
    fun n i => coordinate_coeff_nonneg hm (l n) (b n) (hl n) i, ?_, ?_⟩
  · intro n x
    have hh := hl n x
    rw [linearForm_eq_coordinate_sum] at hh
    exact hh
  · intro x
    have hh := congrFun hsup x
    simp only [iSup_apply, Pi.add_apply, Function.const_apply] at hh
    have heq (n : ℕ) : l n x + b n =
        coordinatePlane (fun i => l n (Pi.single i 1)) (b n) x := by
      rw [linearForm_eq_coordinate_sum]
      rfl
    simp only [heq] at hh
    exact hh

def sortedCoefficients {k : ℕ} (a : Fin k → ℝ) : Fin k → ℝ :=
  a ∘ Tuple.sortDesc a

theorem antitone_sortedCoefficients {k : ℕ} (a : Fin k → ℝ) :
    Antitone (sortedCoefficients a) := Tuple.antitone_sortDesc a

theorem sortedCoefficients_nonneg {k : ℕ} {a : Fin k → ℝ}
    (ha : ∀ i, 0 ≤ a i) (i : Fin k) : 0 ≤ sortedCoefficients a i := ha _

/-- Every permuted supporting plane remains a minorant of a symmetric profile. -/
theorem coordinatePlane_permutation_minorant {k : ℕ}
    {h : (Fin k → ℝ) → ℝ} (hsym : SymmetricProfile h)
    {a : Fin k → ℝ} {b : ℝ} (hle : ∀ x, coordinatePlane a b x ≤ h x)
    (σ : Equiv.Perm (Fin k)) (x : Fin k → ℝ) :
    coordinatePlane (a ∘ σ) b x ≤ h x := by
  have heq : (∑ i, a (σ i) * x i) = ∑ i, a i * x (σ.symm i) := by
    simpa only [σ.symm_apply_apply] using
      (Equiv.sum_comp σ (fun i => a i * x (σ.symm i)))
  have hh := hle (x ∘ σ.symm)
  rw [hsym σ.symm x] at hh
  simpa only [coordinatePlane, Function.comp_apply, heq] using hh

theorem coordinatePlane_le_sorted_on_chamber {k : ℕ}
    (a : Fin k → ℝ) (b : ℝ) {x : Fin k → ℝ} (hx : Antitone x) :
    coordinatePlane a b x ≤ coordinatePlane (sortedCoefficients a) b x := by
  have hmv := (antitone_sortedCoefficients a).monovary hx
  have hr := hmv.sum_comp_perm_mul_le_sum_mul (σ := (Tuple.sortDesc a).symm)
  change (∑ i, a i * x i) + b ≤ (∑ i, sortedCoefficients a i * x i) + b
  have hr' : (∑ i, a i * x i) ≤ ∑ i, sortedCoefficients a i * x i := by
    simpa only [sortedCoefficients, Function.comp_apply, Equiv.apply_symm_apply] using hr
  linarith

/-- Countably many nonnegative decreasing coefficient vectors recover the
complete symmetric convex increasing profile on its ordered chamber. -/
theorem exists_sorted_coordinate_minorants {k : ℕ}
    {h : (Fin k → ℝ) → ℝ} (hc : ConvexOn ℝ Set.univ h)
    (hm : Monotone h) (hsym : SymmetricProfile h) :
    ∃ (a : ℕ → Fin k → ℝ) (b : ℕ → ℝ),
      (∀ n i, 0 ≤ a n i) ∧ (∀ n, Antitone (a n)) ∧
      (∀ n x, coordinatePlane (a n) (b n) x ≤ h x) ∧
      (∀ x, Antitone x → (⨆ n, coordinatePlane (a n) (b n) x) = h x) := by
  obtain ⟨a, b, ha, hle, hsup⟩ := exists_nonnegative_coordinate_minorants hc hm
  have hsorted (n : ℕ) (x : Fin k → ℝ) :
      coordinatePlane (sortedCoefficients (a n)) (b n) x ≤ h x :=
    coordinatePlane_permutation_minorant hsym (hle n) (Tuple.sortDesc (a n)) x
  refine ⟨fun n => sortedCoefficients (a n), b,
    fun n i => sortedCoefficients_nonneg (ha n) i,
    fun n => antitone_sortedCoefficients (a n), hsorted, ?_⟩
  intro x hx
  have hb : BddAbove (Set.range (fun n => coordinatePlane (sortedCoefficients (a n)) (b n) x)) :=
    ⟨h x, by rintro _ ⟨n, rfl⟩; exact hsorted n x⟩
  apply le_antisymm
  · exact ciSup_le (fun n => hsorted n x)
  · rw [← hsup x]
    apply ciSup_le
    intro n
    exact (coordinatePlane_le_sorted_on_chamber (a n) (b n) hx).trans (le_ciSup hb n)

def coordinatePartialMaximum {k : ℕ} (a : ℕ → Fin k → ℝ) (b : ℕ → ℝ)
    (n : ℕ) (x : Fin k → ℝ) : ℝ :=
  (Finset.range (n + 1)).sup'
    (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero n))
    (fun m => coordinatePlane (a m) (b m) x)

theorem coordinatePartialMaximum_monotone_index {k : ℕ}
    (a : ℕ → Fin k → ℝ) (b : ℕ → ℝ) (x : Fin k → ℝ) :
    Monotone (fun n => coordinatePartialMaximum a b n x) := by
  intro m n hmn
  exact Finset.sup'_mono (fun i => coordinatePlane (a i) (b i) x)
    (Finset.range_mono (Nat.add_le_add_right hmn 1)) _

theorem coordinatePartialMaximum_le {k : ℕ}
    {a : ℕ → Fin k → ℝ} {b : ℕ → ℝ} {h : (Fin k → ℝ) → ℝ}
    (hle : ∀ n x, coordinatePlane (a n) (b n) x ≤ h x) (n : ℕ) (x : Fin k → ℝ) :
    coordinatePartialMaximum a b n x ≤ h x :=
  Finset.sup'_le _ _ (fun m _ => hle m x)

theorem coordinatePlane_le_partialMaximum {k : ℕ}
    (a : ℕ → Fin k → ℝ) (b : ℕ → ℝ) (n : ℕ) (x : Fin k → ℝ) :
    coordinatePlane (a n) (b n) x ≤ coordinatePartialMaximum a b n x :=
  Finset.le_sup' (fun i => coordinatePlane (a i) (b i) x)
    (Finset.mem_range.mpr (Nat.lt_succ_self n))

theorem coordinatePartialMaximum_tendsto {k : ℕ}
    {a : ℕ → Fin k → ℝ} {b : ℕ → ℝ} {h : (Fin k → ℝ) → ℝ}
    (hle : ∀ n x, coordinatePlane (a n) (b n) x ≤ h x)
    {x : Fin k → ℝ} (hsup : (⨆ n, coordinatePlane (a n) (b n) x) = h x) :
    Tendsto (fun n => coordinatePartialMaximum a b n x) atTop (𝓝 (h x)) := by
  have hb : BddAbove (Set.range (fun n => coordinatePartialMaximum a b n x)) :=
    ⟨h x, by rintro _ ⟨n, rfl⟩; exact coordinatePartialMaximum_le hle n x⟩
  have heq : (⨆ n, coordinatePartialMaximum a b n x) = h x := by
    apply le_antisymm
    · exact ciSup_le (fun n => coordinatePartialMaximum_le hle n x)
    · rw [← hsup]
      exact ciSup_le (fun n =>
        (coordinatePlane_le_partialMaximum a b n x).trans (le_ciSup hb n))
  simpa only [heq] using tendsto_atTop_ciSup
    (coordinatePartialMaximum_monotone_index a b x) hb

end Wishart.Spectral
end
end CanonicalSource79
