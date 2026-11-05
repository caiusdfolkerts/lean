module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Elab.Tactic.Omega
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Int.Even
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Round
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Order.IntermediateValue
public import paper_verification.lattice001
public import paper_verification.lattice002

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.GaussianProduct
section Source_GaussianProduct

-- original header: module
-- original header: public import PaperVerification.Gaussian
-- original header: public import PaperVerification.LatticeDefs
-- original header: public import Mathlib.Algebra.BigOperators.Fin
-- original header: public import Mathlib.Data.Fin.Tuple.Basic
-- original header: @[expose] public section
noncomputable section

open scoped BigOperators

namespace PaperVerification.ColdSpots

/-- Absolute convergence justifies products of finitely many one-dimensional sums. -/
theorem hasSum_fin_product (n : ℕ) {κ : Type*} (f : Fin n → κ → ℝ)
    (hf : ∀ i, Summable (f i)) :
    HasSum (fun z : Fin n → κ ↦ ∏ i, f i (z i)) (∏ i, ∑' k, f i k) := by
  induction n with
  | zero =>
      simpa using hasSum_fintype (fun z : Fin 0 → κ ↦ ∏ i, f i (z i))
  | succ n ih =>
      let g : (Fin n → κ) → ℝ := fun z ↦ ∏ i : Fin n, f i.succ (z i)
      have htail : HasSum g
          (∏ i : Fin n, ∑' k, f i.succ k) :=
        ih (fun i ↦ f i.succ) (fun i ↦ hf i.succ)
      have hfabs : Summable (fun k : κ ↦ |f 0 k|) := (hf 0).abs
      have hgabs : Summable (fun z : Fin n → κ ↦ |g z|) :=
        htail.summable.abs
      have habsprod : Summable (fun p : κ × (Fin n → κ) ↦
          |f 0 p.1| * |g p.2|) :=
        Summable.mul_of_nonneg (f := fun k : κ ↦ |f 0 k|)
          (g := fun z : Fin n → κ ↦ |g z|)
          hfabs hgabs (fun _ ↦ abs_nonneg _) (fun _ ↦ abs_nonneg _)
      have habs : Summable (fun p : κ × (Fin n → κ) ↦
          f 0 p.1 * g p.2) := by
        apply Summable.of_abs
        simpa only [abs_mul] using habsprod
      have hprod : HasSum (fun p : κ × (Fin n → κ) ↦
          f 0 p.1 * g p.2)
          ((∑' k, f 0 k) * ∏ i : Fin n, ∑' k, f i.succ k) :=
        (hf 0).hasSum.mul htail habs
      apply ((Fin.consEquiv (fun _ : Fin (n + 1) ↦ κ)).hasSum_iff
        (f := fun z : Fin (n + 1) → κ ↦ ∏ i, f i (z i))).mp
      simpa [g, Function.comp_def, Fin.consEquiv, Fin.prod_univ_succ] using hprod

theorem summable_fin_product (n : ℕ) {κ : Type*} (f : Fin n → κ → ℝ)
    (hf : ∀ i, Summable (f i)) :
    Summable (fun z : Fin n → κ ↦ ∏ i, f i (z i)) :=
  (hasSum_fin_product n f hf).summable

theorem tsum_fin_product (n : ℕ) {κ : Type*} (f : Fin n → κ → ℝ)
    (hf : ∀ i, Summable (f i)) :
    (∑' z : Fin n → κ, ∏ i, f i (z i)) = ∏ i, ∑' k, f i k :=
  (hasSum_fin_product n f hf).tsum_eq

/-- The Gaussian lattice sum on the ordinary integer lattice in dimension `n`. -/
def integerGaussian {n : ℕ} (α : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑' z : Fin n → ℤ, Real.exp (-α * sqDist (intVec z) x)

lemma exp_neg_sqDist {n : ℕ} (α : ℝ) (z : Fin n → ℤ) (x : Fin n → ℝ) :
    Real.exp (-α * sqDist (intVec z) x) =
      ∏ i, Real.exp (-α * ((z i : ℝ) - x i) ^ 2) := by
  change Real.exp (-α * ∑ i : Fin n, ((z i : ℝ) - x i) ^ 2) = _
  rw [Finset.mul_sum, Real.exp_sum]

lemma summable_integerGaussian {n : ℕ} {α : ℝ} (hα : 0 < α) (x : Fin n → ℝ) :
    Summable (fun z : Fin n → ℤ ↦ Real.exp (-α * sqDist (intVec z) x)) := by
  simp only [exp_neg_sqDist]
  exact summable_fin_product n (fun i (z : ℤ) ↦ Real.exp (-α * ((z : ℝ) - x i) ^ 2))
    (fun i ↦ summable_gaussian hα (x i))

theorem integerGaussian_eq_product {n : ℕ} {α : ℝ} (hα : 0 < α) (x : Fin n → ℝ) :
    integerGaussian α x = ∏ i, gaussian α (x i) := by
  unfold integerGaussian gaussian
  simp only [exp_neg_sqDist]
  exact tsum_fin_product n (fun i (z : ℤ) ↦ Real.exp (-α * ((z : ℝ) - x i) ^ 2))
    (fun i ↦ summable_gaussian hα (x i))

end PaperVerification.ColdSpots
end
end Source_GaussianProduct
-- END ORIGINAL PaperVerification.GaussianProduct


-- BEGIN ORIGINAL PaperVerification.DnGaussian
section Source_DnGaussian

-- original header: module
-- original header: public import PaperVerification.GaussianProduct
-- original header: public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
-- original header: @[expose] public section
/-!
# Exact Gaussian factorization for D_n and D_n^+

The theta functions below start as series over actual even-sum integer tuples.
The factorization into one-dimensional series is proved, not used as a definition.
The final equivalence identifies the tagged two-coset sum with the set of distinct
points in `dPlusSet`, so no lattice point is counted twice.
-/

noncomputable section

open scoped BigOperators

namespace PaperVerification.ColdSpots

abbrev EvenTuple (n : ℕ) := {z : Fin n → ℤ // Even (∑ i, z i)}

def dGaussian {n : ℕ} (α : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑' z : EvenTuple n, Real.exp (-α * sqDist (intVec z.val) x)

def dPlusGaussian {n : ℕ} (α : ℝ) (x : Fin n → ℝ) : ℝ :=
  dGaussian α x + dGaussian α (fun i ↦ x i - 1 / 2)

def setGaussian {n : ℕ} (L : Set (Fin n → ℝ)) (α : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑' z : L, Real.exp (-α * sqDist z.val x)

def IsColdSpot {n : ℕ} (L : Set (Fin n → ℝ)) (α : ℝ) (x : Fin n → ℝ) : Prop :=
  ∀ y, setGaussian L α x ≤ setGaussian L α y

lemma paritySign_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    paritySign (∑ i ∈ s, f i) = ∏ i ∈ s, paritySign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [paritySign_zero]
  | @insert i s hi ih => simp [hi, paritySign_add, ih]

lemma signed_gaussian_term_product {n : ℕ} (α : ℝ) (x : Fin n → ℝ) (z : Fin n → ℤ) :
    paritySign (∑ i, z i) * Real.exp (-α * sqDist (intVec z) x) =
      ∏ i, (paritySign (z i) * Real.exp (-α * ((z i : ℝ) - x i) ^ 2)) := by
  rw [paritySign_sum]
  rw [exp_neg_sqDist, Finset.prod_mul_distrib]

lemma summable_signed_integerGaussian {n : ℕ} {α : ℝ} (hα : 0 < α)
    (x : Fin n → ℝ) :
    Summable (fun z : Fin n → ℤ ↦
      paritySign (∑ i, z i) * Real.exp (-α * sqDist (intVec z) x)) := by
  simp only [signed_gaussian_term_product]
  exact summable_fin_product n
    (fun i z ↦ paritySign z * Real.exp (-α * ((z : ℝ) - x i) ^ 2))
    (fun i ↦ summable_alternatingGaussian hα (x i))

lemma signed_integerGaussian_eq_product {n : ℕ} {α : ℝ} (hα : 0 < α)
    (x : Fin n → ℝ) :
    (∑' z : Fin n → ℤ,
      paritySign (∑ i, z i) * Real.exp (-α * sqDist (intVec z) x)) =
      ∏ i, alternatingGaussian α (x i) := by
  simp only [signed_gaussian_term_product, alternatingGaussian]
  exact tsum_fin_product n
    (fun i z ↦ paritySign z * Real.exp (-α * ((z : ℝ) - x i) ^ 2))
    (fun i ↦ summable_alternatingGaussian hα (x i))

lemma summable_dGaussian {n : ℕ} {α : ℝ} (hα : 0 < α) (x : Fin n → ℝ) :
    Summable (fun z : EvenTuple n ↦ Real.exp (-α * sqDist (intVec z.val) x)) :=
  (summable_integerGaussian hα x).subtype _

/-- The parity projector gives the D_n theta function exactly. -/
theorem dGaussian_eq_product {n : ℕ} {α : ℝ} (hα : 0 < α) (x : Fin n → ℝ) :
    dGaussian α x = (1 / 2) *
      ((∏ i, gaussian α (x i)) + (∏ i, alternatingGaussian α (x i))) := by
  unfold dGaussian
  change (∑' z : {z : Fin n → ℤ | Even (∑ i, z i)},
    Real.exp (-α * sqDist (intVec z.val) x)) = _
  rw [tsum_subtype {z : Fin n → ℤ | Even (∑ i, z i)}
    (fun z ↦ Real.exp (-α * sqDist (intVec z) x))]
  have hpoint (z : Fin n → ℤ) :
      Set.indicator {z : Fin n → ℤ | Even (∑ i, z i)}
        (fun z ↦ Real.exp (-α * sqDist (intVec z) x)) z =
      (1 / 2) * (Real.exp (-α * sqDist (intVec z) x) +
        paritySign (∑ i, z i) * Real.exp (-α * sqDist (intVec z) x)) := by
    by_cases hz : Even (∑ i, z i) <;> simp [Set.indicator, paritySign, hz] <;> ring
  simp_rw [hpoint]
  rw [tsum_mul_left, (summable_integerGaussian hα x).tsum_add
    (summable_signed_integerGaussian hα x)]
  rw [signed_integerGaussian_eq_product hα x]
  change (1 / 2) * (integerGaussian α x + _) = _
  rw [integerGaussian_eq_product hα x]

/-- Equation (8) of the manuscript, for every positive parameter and every dimension. -/
theorem dPlusGaussian_eq_product {n : ℕ} {α : ℝ} (hα : 0 < α) (x : Fin n → ℝ) :
    dPlusGaussian α x = (1 / 2) *
      ((∏ i, gaussian α (x i)) + (∏ i, alternatingGaussian α (x i)) +
       (∏ i, gaussian α (x i - 1 / 2)) +
       (∏ i, alternatingGaussian α (x i - 1 / 2))) := by
  rw [dPlusGaussian, dGaussian_eq_product hα, dGaussian_eq_product hα]
  ring

lemma intVec_injective (n : ℕ) : Function.Injective (@intVec n) := by
  intro z w h
  funext i
  exact Int.cast_injective (congrFun h i)

lemma integer_ne_half_shift (a b : ℤ) : (a : ℝ) ≠ (b : ℝ) + 1 / 2 := by
  intro h
  have h' : (2 : ℤ) * a = 2 * b + 1 := by
    exact_mod_cast (show (2 : ℝ) * a = 2 * b + 1 by linarith)
  omega

def dPlusTagMap {n : ℕ} : EvenTuple n ⊕ EvenTuple n → dPlusSet n
  | .inl z => ⟨intVec z.val, z.val, z.property, Or.inl rfl⟩
  | .inr z => ⟨(fun i ↦ (z.val i : ℝ) + 1 / 2), z.val, z.property, Or.inr rfl⟩

lemma dPlusTagMap_bijective {n : ℕ} (hn : 0 < n) :
    Function.Bijective (@dPlusTagMap n) := by
  constructor
  · intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        congr 1
        apply Subtype.ext
        exact intVec_injective n (congrArg Subtype.val h)
      | inr b =>
        have hi := congrFun (congrArg Subtype.val h) ⟨0, hn⟩
        exact (integer_ne_half_shift (a.val ⟨0, hn⟩) (b.val ⟨0, hn⟩) hi).elim
    | inr a =>
      cases b with
      | inl b =>
        have hi := congrFun (congrArg Subtype.val h) ⟨0, hn⟩
        exact (integer_ne_half_shift (b.val ⟨0, hn⟩) (a.val ⟨0, hn⟩) hi.symm).elim
      | inr b =>
        congr 1
        apply Subtype.ext
        funext i
        have hi := congrFun (congrArg Subtype.val h) i
        apply Int.cast_injective (α := ℝ)
        dsimp [dPlusTagMap] at hi
        linarith
  · rintro ⟨x, z, hz, h | h⟩
    · exact ⟨Sum.inl ⟨z, hz⟩, Subtype.ext h.symm⟩
    · exact ⟨Sum.inr ⟨z, hz⟩, Subtype.ext h.symm⟩

def dPlusTagEquiv {n : ℕ} (hn : 0 < n) :
    EvenTuple n ⊕ EvenTuple n ≃ dPlusSet n :=
  Equiv.ofBijective dPlusTagMap (dPlusTagMap_bijective hn)

lemma sqDist_half_shift {n : ℕ} (z : Fin n → ℤ) (x : Fin n → ℝ) :
    sqDist (fun i ↦ (z i : ℝ) + 1 / 2) x =
      sqDist (intVec z) (fun i ↦ x i - 1 / 2) := by
  apply Finset.sum_congr rfl
  intro i _
  dsimp [intVec]
  ring

/-- The two-coset formula counts exactly the points of the stated real lattice. -/
theorem setGaussian_dPlus_eq {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α)
    (x : Fin n → ℝ) : setGaussian (dPlusSet n) α x = dPlusGaussian α x := by
  let f : dPlusSet n → ℝ := fun z ↦ Real.exp (-α * sqDist z.val x)
  have hl : HasSum (fun z : EvenTuple n ↦ f (dPlusTagEquiv hn (Sum.inl z)))
      (dGaussian α x) := by
    change HasSum (fun z : EvenTuple n ↦ Real.exp (-α * sqDist (intVec z.val) x))
      (dGaussian α x)
    unfold dGaussian
    exact (summable_dGaussian hα x).hasSum
  have hr : HasSum (fun z : EvenTuple n ↦ f (dPlusTagEquiv hn (Sum.inr z)))
      (dGaussian α (fun i ↦ x i - 1 / 2)) := by
    change HasSum (fun z : EvenTuple n ↦
      Real.exp (-α * sqDist (fun i ↦ (z.val i : ℝ) + 1 / 2) x)) _
    simp only [sqDist_half_shift]
    unfold dGaussian
    exact (summable_dGaussian hα (fun i ↦ x i - 1 / 2)).hasSum
  have hsum : HasSum (fun z : EvenTuple n ⊕ EvenTuple n ↦ f (dPlusTagEquiv hn z))
      (dPlusGaussian α x) := hl.sum hr
  exact ((dPlusTagEquiv hn).hasSum_iff (f := f)).mp hsum |>.tsum_eq

end PaperVerification.ColdSpots
end
end Source_DnGaussian
-- END ORIGINAL PaperVerification.DnGaussian


-- BEGIN ORIGINAL PaperVerification.GeometricMeanLaws
section Source_GeometricMeanLaws

-- original header: module
-- original header: public import PaperVerification.GeometricMeanLog
-- original header: public import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.Hyperbolic

open MeasureTheory Set Filter Topology

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [CompactSpace X] [OpensMeasurableSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [CompactSpace Y] [OpensMeasurableSpace Y]

theorem geometricMoment_congr_ae (k : ℝ) {f g : C(X, ℝ)} (μ : ProbabilityMeasure X)
    (h : ∀ᵐ x ∂(μ : Measure X), f x = g x) :
    geometricMoment k f μ = geometricMoment k g μ := by
  unfold geometricMoment
  congr 1
  funext n
  unfold truncatedGeometricMoment
  congr 2
  apply integral_congr_ae
  filter_upwards [h] with x hx
  simp only [truncatedLog, ContinuousMap.coe_mk, hx]

theorem geometricMoment_map [BorelSpace Y] (k : ℝ) (f : C(Y, ℝ)) (T : C(X, Y))
    (μ : ProbabilityMeasure X) :
    geometricMoment k f (μ.map T) = geometricMoment k (f.comp T) μ := by
  unfold geometricMoment
  congr 1
  funext n
  unfold truncatedGeometricMoment
  congr 2
  change (∫ y, truncatedLog f n y ∂Measure.map T (μ : Measure X)) = _
  rw [integral_map_of_stronglyMeasurable T.continuous.measurable
    (truncatedLog f n).continuous.stronglyMeasurable]
  rfl

theorem geometricMoment_const (k : ℝ) (hk : 0 ≤ k) {c : ℝ} (hc : 0 < c)
    (μ : ProbabilityMeasure X) :
    geometricMoment k (ContinuousMap.const X c) μ = c ^ k := by
  rw [geometricMoment_eq_exp_integral_of_lower_bound k hk _ μ hc (fun _ ↦ le_rfl)]
  simp only [ContinuousMap.const_apply, integral_const, measureReal_def, measure_univ,
    ENNReal.toReal_one, one_smul]
  rw [Real.rpow_def_of_pos hc]
  congr 1
  ring

theorem geometricMean_const {c : ℝ} (hc : 0 < c) (μ : ProbabilityMeasure X) :
    geometricMean (ContinuousMap.const X c) μ = c := by
  rw [geometricMean, geometricMoment_const 1 zero_le_one hc, Real.rpow_one]

/-- Multiplication by a positive continuous factor, including zero and divergent means. -/
theorem geometricMoment_mul_pos_right (k : ℝ) (hk : 0 < k) (f g : C(X, ℝ))
    (μ : ProbabilityMeasure X) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 < g x) :
    geometricMoment k (f * g) μ = geometricMoment k f μ * geometricMoment k g μ := by
  let logg : C(X, ℝ) := ⟨fun x ↦ Real.log (g x), g.continuous.log (fun x ↦ (hg x).ne')⟩
  have hglog : Integrable (fun x ↦ Real.log (g x)) (μ : Measure X) :=
    integrable_continuousMap logg μ
  have hgae : ∀ᵐ x ∂(μ : Measure X), 0 < g x := Eventually.of_forall hg
  have hfg : ∀ x, 0 ≤ (f * g) x := fun x ↦ mul_nonneg (hf x) (hg x).le
  by_cases hfzero : geometricMoment k f μ = 0
  · have hzero : geometricMoment k (f * g) μ = 0 := by
      by_contra hne
      have hp : 0 < geometricMoment k (f * g) μ :=
        lt_of_le_of_ne (geometricMoment_nonneg k (f * g) μ) (Ne.symm hne)
      obtain ⟨hpae, hplog⟩ :=
        ae_pos_and_integrable_log_of_geometricMoment_pos k hk (f * g) μ hfg hp
      have hfae : ∀ᵐ x ∂(μ : Measure X), 0 < f x := by
        filter_upwards [hpae] with x hx
        change 0 < f x * g x at hx
        exact pos_of_mul_pos_right (by simpa only [mul_comm] using hx) (hg x).le
      have hlogf : Integrable (fun x ↦ Real.log (f x)) (μ : Measure X) := by
        apply (hplog.sub hglog).congr
        filter_upwards [hfae] with x hx
        change Real.log (f x * g x) - Real.log (g x) = Real.log (f x)
        rw [Real.log_mul hx.ne' (hg x).ne']
        ring
      have hp' := (geometricMoment_pos_iff k hk f μ hf).mpr ⟨hfae, hlogf⟩
      rw [hfzero] at hp'
      exact (lt_irrefl _) hp'
    rw [hzero, hfzero, zero_mul]
  · have hp : 0 < geometricMoment k f μ :=
      lt_of_le_of_ne (geometricMoment_nonneg k f μ) (Ne.symm hfzero)
    obtain ⟨hfae, hflog⟩ := ae_pos_and_integrable_log_of_geometricMoment_pos k hk f μ hf hp
    have hpae : ∀ᵐ x ∂(μ : Measure X), 0 < (f * g) x := by
      filter_upwards [hfae] with x hx
      exact mul_pos hx (hg x)
    have hlogeq : (fun x ↦ Real.log ((f * g) x)) =ᵐ[(μ : Measure X)]
        (fun x ↦ Real.log (f x) + Real.log (g x)) := by
      filter_upwards [hfae] with x hx
      exact Real.log_mul hx.ne' (hg x).ne'
    have hplog : Integrable (fun x ↦ Real.log ((f * g) x)) (μ : Measure X) :=
      (hflog.add hglog).congr hlogeq.symm
    rw [geometricMoment_eq_exp_integral_of_integrable_log k hk.le (f * g) μ hpae hplog,
      geometricMoment_eq_exp_integral_of_integrable_log k hk.le f μ hfae hflog,
      geometricMoment_eq_exp_integral_of_integrable_log k hk.le g μ hgae hglog,
      integral_congr_ae hlogeq, integral_add hflog hglog, mul_add, Real.exp_add]

theorem geometricMean_mul_pos_right (f g : C(X, ℝ)) (μ : ProbabilityMeasure X)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 < g x) :
    geometricMean (f * g) μ = geometricMean f μ * geometricMean g μ :=
  geometricMoment_mul_pos_right 1 zero_lt_one f g μ hf hg

theorem geometricMean_ge_const (f : C(X, ℝ)) (μ : ProbabilityMeasure X)
    {c : ℝ} (hc : 0 < c) (hf : ∀ x, c ≤ f x) : c ≤ geometricMean f μ := by
  rw [← geometricMean_const hc μ]
  exact geometricMoment_mono 1 zero_le_one hf μ

/-- Equality in a positive uniform lower bound is exactly almost-everywhere equality. -/
theorem geometricMean_eq_const_iff (f : C(X, ℝ)) (μ : ProbabilityMeasure X)
    {c : ℝ} (hc : 0 < c) (hf : ∀ x, c ≤ f x) :
    geometricMean f μ = c ↔ ∀ᵐ x ∂(μ : Measure X), f x = c := by
  let logf : C(X, ℝ) := ⟨fun x ↦ Real.log (f x),
    f.continuous.log (fun x ↦ (hc.trans_le (hf x)).ne')⟩
  have hi : Integrable (fun x ↦ Real.log (f x)) (μ : Measure X) :=
    integrable_continuousMap logf μ
  have hcint : (∫ _ : X, Real.log c ∂μ) = Real.log c := by simp
  have heq : geometricMean f μ = Real.exp (∫ x, Real.log (f x) ∂μ) := by
    simpa only [geometricMean, one_mul] using geometricMoment_eq_exp_integral_of_lower_bound
      1 zero_le_one f μ hc hf
  constructor
  · intro h
    rw [heq, ← Real.exp_log hc] at h
    have hint : (∫ _ : X, Real.log c ∂μ) = ∫ x, Real.log (f x) ∂μ := by
      rw [hcint]
      exact (Real.exp_injective h).symm
    have hae := (integral_eq_iff_of_ae_le (integrable_const (Real.log c)) hi
      (Eventually.of_forall (fun x ↦ Real.log_le_log hc (hf x)))).mp hint
    filter_upwards [hae] with x hx
    exact (Real.log_injOn_pos (hc.trans_le (hf x)) hc hx.symm)
  · intro h
    change geometricMoment 1 f μ = c
    rw [geometricMoment_congr_ae 1 (g := ContinuousMap.const X c) μ h]
    exact geometricMean_const hc μ

theorem geometricMoment_pos_of_pos (k : ℝ) (hk : 0 < k) (f : C(X, ℝ))
    (μ : ProbabilityMeasure X) (hf : ∀ x, 0 < f x) : 0 < geometricMoment k f μ := by
  let logf : C(X, ℝ) := ⟨fun x ↦ Real.log (f x), f.continuous.log (fun x ↦ (hf x).ne')⟩
  exact (geometricMoment_pos_iff k hk f μ (fun x ↦ (hf x).le)).mpr
    ⟨Eventually.of_forall hf, integrable_continuousMap logf μ⟩

/-- All positive real moments have the expected power law, including zero means. -/
theorem geometricMoment_eq_rpow (k : ℝ) (hk : 0 < k) (f : C(X, ℝ))
    (μ : ProbabilityMeasure X) (hf : ∀ x, 0 ≤ f x) :
    geometricMoment k f μ = geometricMean f μ ^ k := by
  by_cases hz : geometricMean f μ = 0
  · have hm : geometricMoment k f μ = 0 := by
      apply (geometricMoment_eq_zero_iff k hk f μ hf).mpr
      exact (geometricMoment_eq_zero_iff 1 zero_lt_one f μ hf).mp hz
    rw [hm, hz, Real.zero_rpow hk.ne']
  · have hp : 0 < geometricMean f μ :=
      lt_of_le_of_ne (geometricMean_nonneg f μ) (Ne.symm hz)
    obtain ⟨hfae, hflog⟩ :=
      ae_pos_and_integrable_log_of_geometricMoment_pos 1 zero_lt_one f μ hf hp
    have heq : geometricMean f μ = Real.exp (∫ x, Real.log (f x) ∂μ) := by
      simpa only [geometricMean, one_mul] using
        geometricMoment_eq_exp_integral_of_integrable_log 1 zero_le_one f μ hfae hflog
    rw [geometricMoment_eq_exp_integral_of_integrable_log k hk.le f μ hfae hflog,
      heq, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring

theorem geometricMean_pow (n : ℕ) (f : C(X, ℝ)) (μ : ProbabilityMeasure X)
    (hf : ∀ x, 0 ≤ f x) : geometricMean (f ^ n) μ = geometricMean f μ ^ n := by
  rcases eq_or_lt_of_le (Nat.zero_le n) with rfl | hn
  · simp only [pow_zero]
    exact geometricMean_const zero_lt_one μ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpower : ∀ x, 0 ≤ (f ^ n) x := fun x ↦ pow_nonneg (hf x) n
  by_cases hz : geometricMean f μ = 0
  · have hpzero : geometricMean (f ^ n) μ = 0 := by
      apply (geometricMoment_eq_zero_iff 1 zero_lt_one (f ^ n) μ hpower).mpr
      rintro ⟨hpae, hplog⟩
      have hfae : ∀ᵐ x ∂(μ : Measure X), 0 < f x := by
        filter_upwards [hpae] with x hx
        apply lt_of_le_of_ne (hf x)
        intro heq
        have hfx : f x = 0 := heq.symm
        simp only [ContinuousMap.coe_pow, Pi.pow_apply, hfx, zero_pow hn.ne'] at hx
        exact (lt_irrefl (0 : ℝ)) hx
      have hflog : Integrable (fun x ↦ Real.log (f x)) (μ : Measure X) := by
        apply (hplog.const_mul (n : ℝ)⁻¹).congr
        exact Eventually.of_forall (fun x ↦ by
          simp only [ContinuousMap.coe_pow, Pi.pow_apply, Real.log_pow]
          field_simp [hnR.ne'])
      have hp := (geometricMoment_pos_iff 1 zero_lt_one f μ hf).mpr ⟨hfae, hflog⟩
      rw [show geometricMoment 1 f μ = geometricMean f μ from rfl, hz] at hp
      exact (lt_irrefl _) hp
    rw [hpzero, hz, zero_pow hn.ne']
  · have hp : 0 < geometricMean f μ :=
      lt_of_le_of_ne (geometricMean_nonneg f μ) (Ne.symm hz)
    obtain ⟨hfae, hflog⟩ :=
      ae_pos_and_integrable_log_of_geometricMoment_pos 1 zero_lt_one f μ hf hp
    have hpae : ∀ᵐ x ∂(μ : Measure X), 0 < (f ^ n) x := by
      filter_upwards [hfae] with x hx
      exact pow_pos hx n
    have hplog : Integrable (fun x ↦ Real.log ((f ^ n) x)) (μ : Measure X) := by
      simpa only [ContinuousMap.coe_pow, Pi.pow_apply, Real.log_pow] using hflog.const_mul (n : ℝ)
    rw [geometricMean,
      geometricMoment_eq_exp_integral_of_integrable_log 1 zero_le_one (f ^ n) μ hpae hplog,
      ← geometricMoment_nat n f μ,
      geometricMoment_eq_exp_integral_of_integrable_log (n : ℝ) hnR.le f μ hfae hflog]
    simp only [one_mul, ContinuousMap.coe_pow, Pi.pow_apply, Real.log_pow, integral_const_mul]

theorem geometricMoment_nat_pow (k n : ℕ) (f : C(X, ℝ)) (μ : ProbabilityMeasure X)
    (hf : ∀ x, 0 ≤ f x) :
    geometricMoment (k : ℝ) (f ^ n) μ = geometricMoment ((n * k : ℕ) : ℝ) f μ := by
  rw [geometricMoment_nat, geometricMean_pow n f μ hf, ← pow_mul, ← geometricMoment_nat]


end PaperVerification.Hyperbolic
end
end Source_GeometricMeanLaws
-- END ORIGINAL PaperVerification.GeometricMeanLaws


-- BEGIN ORIGINAL PaperVerification.FiniteGeometricMean
section Source_FiniteGeometricMean

-- original header: module
-- original header: public import PaperVerification.GeometricMeanLaws
-- original header: public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
-- original header: public import Mathlib.MeasureTheory.Measure.Count
-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.Hyperbolic

open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal

variable (X : Type*) [Fintype X] [Nonempty X] [MeasurableSpace X]
  [MeasurableSingletonClass X]

/-- The genuine uniform probability measure on an arbitrary nonempty finite type. -/
def uniformProbability : ProbabilityMeasure X := by
  refine ⟨(Fintype.card X : ℝ≥0∞)⁻¹ • (Measure.count : Measure X), ⟨?_⟩⟩
  have hc : (Measure.count : Measure X) univ = (Fintype.card X : ℝ≥0∞) := by
    simpa only [Finset.coe_univ, Finset.card_univ] using
      (Measure.count_apply_finset (Finset.univ : Finset X))
  rw [Measure.smul_apply, smul_eq_mul, hc]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero)
    (ENNReal.natCast_ne_top _)

theorem ae_uniformProbability_iff (p : X → Prop) :
    (∀ᵐ x ∂(uniformProbability X : Measure X), p x) ↔ ∀ x, p x := by
  change (∀ᵐ x ∂(Fintype.card X : ℝ≥0∞)⁻¹ • (Measure.count : Measure X), p x) ↔ _
  rw [Measure.ae_ennreal_smul_measure_iff (by simp : (Fintype.card X : ℝ≥0∞)⁻¹ ≠ 0),
    Measure.ae_count_iff]

theorem integral_uniformProbability (f : X → ℝ) :
    (∫ x, f x ∂(uniformProbability X : Measure X)) =
      (∑ x, f x) / (Fintype.card X : ℝ) := by
  change (∫ x, f x ∂(Fintype.card X : ℝ≥0∞)⁻¹ • (Measure.count : Measure X)) = _
  rw [integral_smul_measure, integral_count]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul, div_eq_mul_inv, mul_comm]

variable [TopologicalSpace X] [CompactSpace X] [OpensMeasurableSpace X]

/-- Finite-product formula, proved with every zero-factor case included. -/
theorem geometricMoment_uniformProbability (k : ℝ) (hk : 0 < k) (f : C(X, ℝ))
    (hf : ∀ x, 0 ≤ f x) :
    geometricMoment k f (uniformProbability X) =
      (∏ x, f x) ^ (k / (Fintype.card X : ℝ)) := by
  have hn : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  by_cases hpos : ∀ x, 0 < f x
  · let logf : C(X, ℝ) := ⟨fun x ↦ Real.log (f x),
      f.continuous.log (fun x ↦ (hpos x).ne')⟩
    rw [geometricMoment_eq_exp_integral_of_integrable_log k hk.le f
      (uniformProbability X) (Eventually.of_forall hpos)
      (integrable_continuousMap logf (uniformProbability X)), integral_uniformProbability,
      Real.rpow_def_of_pos (Finset.prod_pos (fun x _ ↦ hpos x)),
      Real.log_prod (fun x _ ↦ (hpos x).ne')]
    congr 1
    ring
  · obtain ⟨x, hx⟩ := not_forall.mp hpos
    have hxzero : f x = 0 := le_antisymm (le_of_not_gt hx) (hf x)
    have hz : geometricMoment k f (uniformProbability X) = 0 := by
      apply (geometricMoment_eq_zero_iff k hk f (uniformProbability X) hf).mpr
      rintro ⟨hae, _⟩
      have hall := (ae_uniformProbability_iff X (fun x ↦ 0 < f x)).mp hae
      exact hx (hall x)
    have hprod : (∏ x, f x) = 0 := Finset.prod_eq_zero (Finset.mem_univ x) hxzero
    rw [hz, hprod, Real.zero_rpow (div_pos hk hn).ne']

theorem geometricMean_uniformProbability (f : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    geometricMean f (uniformProbability X) =
      (∏ x, f x) ^ (1 / (Fintype.card X : ℝ)) :=
  geometricMoment_uniformProbability X 1 zero_lt_one f hf

end PaperVerification.Hyperbolic
end
end Source_FiniteGeometricMean
-- END ORIGINAL PaperVerification.FiniteGeometricMean


-- BEGIN ORIGINAL PaperVerification.LatticeCoordinates
section Source_LatticeCoordinates

-- original header: module
-- original header: public import Mathlib.Algebra.Order.Round
-- original header: public import Mathlib.Algebra.Group.Int.Even
-- original header: public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
-- original header: public import Mathlib.Algebra.BigOperators.Ring.Finset
-- original header: public import Mathlib.Algebra.Order.BigOperators.Group.Finset
-- original header: public import Mathlib.Data.Real.Basic
-- original header: public import Mathlib.Tactic.Linarith
-- original header: public import Mathlib.Tactic.Ring
-- original header: public import Mathlib.Tactic.NormNum
-- original header: @[expose] public section
/-! # Integer coordinate rounding and exact parity repair

These are geometric statements about actual integer coordinate tuples. All sums
are squared Euclidean distances, written in coordinates. They do not assume any
of the covering or Gaussian-minimum conclusions.
-/

namespace PaperVerification.ColdSpots

open scoped BigOperators

variable {n : ℕ}

/-- Change one integer coordinate by an integer step. -/
def alterCoordinate (q : Fin n → ℤ) (j : Fin n) (e : ℤ) : Fin n → ℤ :=
  fun i => q i + if i = j then e else 0

theorem sum_alterCoordinate (q : Fin n → ℤ) (j : Fin n) (e : ℤ) :
    (∑ i, alterCoordinate q j e i) = (∑ i, q i) + e := by
  simp [alterCoordinate, Finset.sum_add_distrib]

/-- Exact change in squared Euclidean distance under one coordinate step. -/
theorem sq_sum_alterCoordinate (x : Fin n → ℝ) (q : Fin n → ℤ) (j : Fin n) (e : ℤ) :
    (∑ i, (x i - (alterCoordinate q j e i : ℝ)) ^ 2) =
      (∑ i, (x i - (q i : ℝ)) ^ 2) +
        ((e : ℝ) ^ 2 - 2 * (e : ℝ) * (x j - (q j : ℝ))) := by
  calc
    _ = ∑ i, ((x i - (q i : ℝ)) ^ 2 +
        if i = j then (e : ℝ) ^ 2 - 2 * (e : ℝ) * (x j - (q j : ℝ)) else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : i = j
      · subst i
        simp only [alterCoordinate, ↓reduceIte, Int.cast_add]
        ring
      · simp [alterCoordinate, h]
    _ = _ := by simp [Finset.sum_add_distrib]

/-- Parity can be repaired at any coordinate at additional squared cost
`1 - 2 * |x j - q j|`, provided that coordinate was rounded within one half. -/
theorem exists_even_parity_repair (x : Fin n → ℝ) (q : Fin n → ℤ) (j : Fin n)
    (hj : |x j - (q j : ℝ)| ≤ 1 / 2) :
    ∃ z : Fin n → ℤ, Even (∑ i, z i) ∧
      (∑ i, (x i - (z i : ℝ)) ^ 2) ≤
        (∑ i, (x i - (q i : ℝ)) ^ 2) + 1 - 2 * |x j - (q j : ℝ)| := by
  by_cases he : Even (∑ i, q i)
  · exact ⟨q, he, by linarith⟩
  · by_cases hd : 0 ≤ x j - (q j : ℝ)
    · refine ⟨alterCoordinate q j 1, ?_, ?_⟩
      · rw [sum_alterCoordinate]
        exact Int.even_add_one.mpr he
      · rw [sq_sum_alterCoordinate, abs_of_nonneg hd]
        norm_num <;> linarith
    · refine ⟨alterCoordinate q j (-1), ?_, ?_⟩
      · rw [sum_alterCoordinate]
        simpa only [sub_eq_add_neg] using Int.even_sub_one.mpr he
      · rw [sq_sum_alterCoordinate, abs_of_neg (lt_of_not_ge hd)]
        norm_num <;> linarith


/-- Distinct integers are separated by at least one in the real metric. -/
theorem one_le_abs_int_sub (q z : ℤ) (hne : q ≠ z) :
    1 ≤ |(q : ℝ) - (z : ℝ)| := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hz : (q : ℝ) + 1 ≤ (z : ℝ) := by
      exact_mod_cast (Int.add_one_le_iff.mpr h)
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hz : (z : ℝ) + 1 ≤ (q : ℝ) := by
      exact_mod_cast (Int.add_one_le_iff.mpr h)
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- Moving away from a nearest integer has at least the parity-repair cost. -/
theorem sq_sub_int_lower (x : ℝ) (q z : ℤ)
    (hq : |x - (q : ℝ)| ≤ 1 / 2) (hne : q ≠ z) :
    (x - (q : ℝ)) ^ 2 + 1 - 2 * |x - (q : ℝ)| ≤ (x - (z : ℝ)) ^ 2 := by
  have hz := one_le_abs_int_sub q z hne
  have htri : |(q : ℝ) - (z : ℝ)| ≤ |x - (q : ℝ)| + |x - (z : ℝ)| := by
    calc
      _ = |(x - (z : ℝ)) - (x - (q : ℝ))| := by congr 1 <;> ring
      _ ≤ |x - (z : ℝ)| + |x - (q : ℝ)| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (x - (z : ℝ)) 0 (x - (q : ℝ)))
      _ = _ := add_comm _ _
  have ha : 0 ≤ |x - (z : ℝ)| - (1 - |x - (q : ℝ)|) := by linarith
  have hb : 0 ≤ |x - (z : ℝ)| + (1 - |x - (q : ℝ)|) := by
    linarith [abs_nonneg (x - (z : ℝ))]
  have hp := mul_nonneg ha hb
  nlinarith only [hp, sq_abs (x - (q : ℝ)), sq_abs (x - (z : ℝ))]

/-- A coordinate within one half of an integer is indeed nearest to that integer. -/
theorem sq_sub_int_nearest (x : ℝ) (q z : ℤ) (hq : |x - (q : ℝ)| ≤ 1 / 2) :
    (x - (q : ℝ)) ^ 2 ≤ (x - (z : ℝ)) ^ 2 := by
  by_cases heq : q = z
  · simp [heq]
  · linarith [sq_sub_int_lower x q z hq heq]

/-- Lower bound for the even integer coset. It contains the exact parity cost,
so it can be paired with the explicit rounding witness above. -/
theorem even_integer_sq_lower (x : Fin n → ℝ) (q z : Fin n → ℤ) (M : ℝ)
    (hq : ∀ i, |x i - (q i : ℝ)| ≤ 1 / 2)
    (hM : ∀ i, |x i - (q i : ℝ)| ≤ M) (hz : Even (∑ i, z i)) :
    (∑ i, (x i - (q i : ℝ)) ^ 2) + (if Even (∑ i, q i) then 0 else 1 - 2 * M) ≤
      ∑ i, (x i - (z i : ℝ)) ^ 2 := by
  classical
  by_cases he : Even (∑ i, q i)
  · simp only [if_pos he, add_zero]
    exact Finset.sum_le_sum fun i _ => sq_sub_int_nearest (x i) (q i) (z i) (hq i)
  · simp only [if_neg he]
    have hneq : q ≠ z := by
      intro heq
      exact he (by simpa only [heq] using hz)
    obtain ⟨j, hj⟩ : ∃ j, q j ≠ z j := not_forall.mp (fun h => hneq (funext h))
    have hs : (∑ i, ((x i - (q i : ℝ)) ^ 2 + if i = j then 1 - 2 * M else 0)) ≤
        ∑ i, (x i - (z i : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hij : i = j
      · subst i
        simp only [↓reduceIte]
        linarith [sq_sub_int_lower (x j) (q j) (z j) (hq j) hj, hM j]
      · simp only [if_neg hij, add_zero]
        exact sq_sub_int_nearest (x i) (q i) (z i) (hq i)
    simpa [Finset.sum_add_distrib] using hs

/-- Coordinatewise nearest integer, breaking ties as in Mathlib's `round`. -/
noncomputable def roundedInt (x : Fin n → ℝ) : Fin n → ℤ := fun i => round (x i)

/-- Distance of each coordinate to its nearest integer. -/
noncomputable def foldedRadius (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => |x i - (roundedInt x i : ℝ)|

theorem foldedRadius_nonneg (x : Fin n → ℝ) (i : Fin n) : 0 ≤ foldedRadius x i :=
  abs_nonneg _

theorem foldedRadius_le_half (x : Fin n → ℝ) (i : Fin n) : foldedRadius x i ≤ 1 / 2 :=
  abs_sub_round (x i)

theorem sq_sub_roundedInt (x : Fin n → ℝ) (i : Fin n) :
    (x i - (roundedInt x i : ℝ)) ^ 2 = (foldedRadius x i) ^ 2 := by
  simp [foldedRadius, sq_abs]

/-- The integer part of a nearest half-integer coordinate. -/
noncomputable def halfRoundedInt (x : Fin n → ℝ) : Fin n → ℤ :=
  fun i => roundedInt x i + if 0 ≤ x i - (roundedInt x i : ℝ) then 0 else -1

/-- The distance to a nearest half integer is exactly one half minus the distance
to a nearest integer, including all tied-rounding endpoints. -/
theorem abs_sub_halfRoundedInt (x : Fin n → ℝ) (i : Fin n) :
    |x i - ((halfRoundedInt x i : ℝ) + 1 / 2)| = 1 / 2 - foldedRadius x i := by
  have hr := foldedRadius_le_half x i
  unfold foldedRadius at hr ⊢
  by_cases hd : 0 ≤ x i - (roundedInt x i : ℝ)
  · rw [abs_of_nonneg hd] at hr ⊢
    have hh : x i - ((roundedInt x i : ℝ) + 1 / 2) ≤ 0 := by linarith
    simp only [halfRoundedInt, if_pos hd, add_zero]
    rw [abs_of_nonpos hh]
    ring
  · have hneg := lt_of_not_ge hd
    rw [abs_of_neg hneg] at hr ⊢
    have hh : 0 ≤ x i - ((roundedInt x i : ℝ) - 1 + 1 / 2) := by linarith
    simp only [halfRoundedInt, if_neg hd, Int.cast_add, Int.cast_neg, Int.cast_one]
    rw [show (roundedInt x i : ℝ) + -1 + 1 / 2 =
      (roundedInt x i : ℝ) - 1 + 1 / 2 by ring, abs_of_nonneg hh]
    ring

theorem exists_even_integer_bound (x : Fin n → ℝ) (j : Fin n) :
    ∃ z : Fin n → ℤ, Even (∑ i, z i) ∧
      (∑ i, (x i - (z i : ℝ)) ^ 2) ≤
        (∑ i, (foldedRadius x i) ^ 2) + 1 - 2 * foldedRadius x j := by
  obtain ⟨z, he, hz⟩ := exists_even_parity_repair x (roundedInt x) j
    (foldedRadius_le_half x j)
  refine ⟨z, he, ?_⟩
  simpa only [foldedRadius, sq_abs] using hz

/-- The analogous parity repair in the all-half-integer coset has cost `2r_j`. -/
theorem exists_even_half_integer_bound (x : Fin n → ℝ) (j : Fin n) :
    ∃ z : Fin n → ℤ, Even (∑ i, z i) ∧
      (∑ i, (x i - ((z i : ℝ) + 1 / 2)) ^ 2) ≤
        (∑ i, (1 / 2 - foldedRadius x i) ^ 2) + 2 * foldedRadius x j := by
  have hrepr (i : Fin n) :
      |(x i - 1 / 2) - (halfRoundedInt x i : ℝ)| = 1 / 2 - foldedRadius x i := by
    convert abs_sub_halfRoundedInt x i using 1 <;> congr 1 <;> ring
  have hj : |(x j - 1 / 2) - (halfRoundedInt x j : ℝ)| ≤ 1 / 2 := by
    rw [hrepr]
    linarith [foldedRadius_nonneg x j]
  obtain ⟨z, he, hz⟩ := exists_even_parity_repair (fun i => x i - 1 / 2)
    (halfRoundedInt x) j hj
  refine ⟨z, he, ?_⟩
  have hsq (i : Fin n) : ((x i - 1 / 2) - (halfRoundedInt x i : ℝ)) ^ 2 =
      (1 / 2 - foldedRadius x i) ^ 2 := by
    rw [← hrepr, sq_abs]
  have htrans (i : Fin n) : (x i - ((z i : ℝ) + 1 / 2)) ^ 2 =
      ((x i - 1 / 2) - (z i : ℝ)) ^ 2 := by ring
  simp only [hsq, hrepr] at hz
  simp only [htrans]
  linarith


/-- Zero folded radius means exactly an integer coordinate. -/
theorem foldedRadius_eq_zero_iff (x : Fin n → ℝ) (i : Fin n) :
    foldedRadius x i = 0 ↔ ∃ z : ℤ, x i = (z : ℝ) := by
  constructor
  · intro h
    exact ⟨roundedInt x i, sub_eq_zero.mp (abs_eq_zero.mp h)⟩
  · rintro ⟨z, hz⟩
    simp [foldedRadius, roundedInt, hz]

/-- Radius one half means exactly a nonintegral half-integer coordinate. -/
theorem foldedRadius_eq_half_iff (x : Fin n → ℝ) (i : Fin n) :
    foldedRadius x i = 1 / 2 ↔ ∃ z : ℤ, x i = (z : ℝ) + 1 / 2 := by
  constructor
  · intro h
    have ht := sub_half_lt_round (x i)
    change x i - 1 / 2 < (roundedInt x i : ℝ) at ht
    unfold foldedRadius at h
    by_cases hd : 0 ≤ x i - (roundedInt x i : ℝ)
    · rw [abs_of_nonneg hd] at h
      linarith
    · rw [abs_of_neg (lt_of_not_ge hd)] at h
      refine ⟨roundedInt x i - 1, ?_⟩
      push_cast
      linarith
  · rintro ⟨z, hz⟩
    have hh : round (1 / 2 : ℝ) = 1 := by norm_num [round_eq]
    unfold foldedRadius roundedInt
    rw [hz, round_intCast_add, hh]
    push_cast
    have h : (z : ℝ) + 1 / 2 - ((z : ℝ) + 1) = -(1 / 2 : ℝ) := by ring
    rw [h]
    norm_num

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.exists_even_integer_bound
#print axioms PaperVerification.ColdSpots.exists_even_half_integer_bound
end Source_LatticeCoordinates
-- END ORIGINAL PaperVerification.LatticeCoordinates


-- BEGIN ORIGINAL PaperVerification.LatticeRounding
section Source_LatticeRounding

-- original header: module
-- original header: public import Mathlib.Data.Real.Basic
-- original header: public import Mathlib.Algebra.Order.BigOperators.Group.Finset
-- original header: public import Mathlib.Algebra.BigOperators.Ring.Finset
-- original header: public import Mathlib.Tactic.Linarith
-- original header: public import Mathlib.Tactic.Ring
-- original header: @[expose] public section
/-!
# The all-dimensional rounding estimate

The inequalities here are the continuous optimization in equations (11)--(12)
of the lattice paper. They are valid for every real `n ≥ 8`, and consequently
for every dimension in the paper. No theta or lattice conclusion is declared
without the missing geometric and analytic dependencies.
-/

noncomputable section

namespace PaperVerification.Lattice

open scoped BigOperators

/-- The two affine parity-repair upper bounds after taking the secant estimate. -/
def roundingEnvelope (n m M T : ℝ) : ℝ :=
  min ((m + M) * T - n * m * M + 1 - 2 * M)
    ((m + M - 1) * T + n / 4 - n * m * M + 2 * m)

/-- Their common value, written in the factored form useful for equality. -/
def roundingPeak (n m M : ℝ) : ℝ :=
  n / 8 - (n / 4 - 2) * (m + M - 1 / 2) ^ 2 -
    (1 / 2 - (M - m)) * (n / 4 * (M - m) + n / 8 - 1)

/-- The envelope of the increasing and decreasing affine bounds is bounded
by their common value, without any restriction on the coordinate sum `T`. -/
theorem roundingEnvelope_le_peak (n m M T : ℝ)
    (hm : 0 ≤ m) (hmM : m ≤ M) (hM : M ≤ 1 / 2) :
    roundingEnvelope n m M T ≤ roundingPeak n m M := by
  have hs : 0 ≤ m + M := by linarith
  have hs1 : m + M ≤ 1 := by linarith
  rcases le_total T (n / 4 - 1 + 2 * (m + M)) with hT | hT
  · refine (min_le_left _ _).trans ?_
    unfold roundingPeak
    have hprod := mul_nonneg hs (sub_nonneg.mpr hT)
    linarith
  · refine (min_le_right _ _).trans ?_
    unfold roundingPeak
    have hprod := mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hT)
    linarith

/-- The sharp polynomial estimate, valid throughout the full dimension range. -/
theorem roundingPeak_le (n m M : ℝ) (hn : 8 ≤ n)
    (hm : 0 ≤ m) (hmM : m ≤ M) (hM : M ≤ 1 / 2) :
    roundingPeak n m M ≤ n / 8 := by
  have ha : 0 ≤ (n / 4 - 2) * (m + M - 1 / 2) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have hb : 0 ≤ (1 / 2 - (M - m)) * (n / 4 * (M - m) + n / 8 - 1) := by
    apply mul_nonneg
    · linarith
    · have := mul_nonneg (by linarith : 0 ≤ n / 4) (sub_nonneg.mpr hmM)
      linarith
  unfold roundingPeak
  linarith

/-- Equation (12) implies the uniform `n/8` upper bound. -/
theorem roundingEnvelope_le (n m M T : ℝ) (hn : 8 ≤ n)
    (hm : 0 ≤ m) (hmM : m ≤ M) (hM : M ≤ 1 / 2) :
    roundingEnvelope n m M T ≤ n / 8 :=
  (roundingEnvelope_le_peak n m M T hm hmM hM).trans (roundingPeak_le n m M hn hm hmM hM)

/-- Above dimension eight, equality forces the two extreme folded coordinates
and the balanced total. This is the sharp equality statement for the envelope. -/
theorem roundingEnvelope_eq_iff (n m M T : ℝ) (hn : 8 < n)
    (hm : 0 ≤ m) (hmM : m ≤ M) (hM : M ≤ 1 / 2) :
    roundingEnvelope n m M T = n / 8 ↔ m = 0 ∧ M = 1 / 2 ∧ T = n / 4 := by
  constructor
  · intro heq
    have hpeak : roundingPeak n m M = n / 8 := le_antisymm
      (roundingPeak_le n m M hn.le hm hmM hM)
      (heq ▸ roundingEnvelope_le_peak n m M T hm hmM hM)
    have ha : 0 ≤ (n / 4 - 2) * (m + M - 1 / 2) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    have hp : 0 < n / 4 * (M - m) + n / 8 - 1 := by
      have := mul_nonneg (by linarith : 0 ≤ n / 4) (sub_nonneg.mpr hmM)
      linarith
    have hb : 0 ≤ (1 / 2 - (M - m)) * (n / 4 * (M - m) + n / 8 - 1) :=
      mul_nonneg (by linarith) hp.le
    have hz : (1 / 2 - (M - m)) * (n / 4 * (M - m) + n / 8 - 1) = 0 := by
      unfold roundingPeak at hpeak
      linarith
    have hδ : 1 / 2 - (M - m) = 0 :=
      (mul_eq_zero.mp hz).resolve_right (ne_of_gt hp)
    have hm0 : m = 0 := by linarith
    have hMhalf : M = 1 / 2 := by linarith
    refine ⟨hm0, hMhalf, ?_⟩
    unfold roundingEnvelope at heq
    have hleft := (le_min_iff.mp heq.ge).1
    have hright := (le_min_iff.mp heq.ge).2
    rw [hm0, hMhalf] at hleft hright
    linarith
  · rintro ⟨rfl, rfl, rfl⟩
    unfold roundingEnvelope
    ring_nf
    simp


/-- Dimension eight has exactly two extremal spread values. -/
theorem roundingPeak_eight_eq_iff (m M : ℝ)
    (hm : 0 ≤ m) (hmM : m ≤ M) (hM : M ≤ 1 / 2) :
    roundingPeak 8 m M = 1 ↔ M = m ∨ (m = 0 ∧ M = 1 / 2) := by
  have hid : roundingPeak 8 m M = 1 - 2 * ((M - m) * (1 / 2 - (M - m))) := by
    unfold roundingPeak
    ring
  rw [hid]
  constructor
  · intro h
    have hz : (M - m) * (1 / 2 - (M - m)) = 0 := by linarith
    rcases mul_eq_zero.mp hz with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr ⟨by linarith, by linarith⟩
  · rintro (h | ⟨h, h'⟩)
    · rw [h]
      ring
    · rw [h, h']
      norm_num

/-- The secant bound for a family of folded coordinates. -/
theorem folded_square_sum_le {ι : Type*} (s : Finset ι) (r : ι → ℝ) (m M : ℝ)
    (hm : ∀ i ∈ s, m ≤ r i) (hM : ∀ i ∈ s, r i ≤ M) :
    (∑ i ∈ s, r i ^ 2) ≤ (m + M) * (∑ i ∈ s, r i) - (s.card : ℝ) * m * M := by
  have hs : (∑ i ∈ s, r i ^ 2) ≤ ∑ i ∈ s, ((m + M) * r i - m * M) := by
    apply Finset.sum_le_sum
    intro i hi
    have := mul_nonneg (sub_nonneg.mpr (hm i hi)) (sub_nonneg.mpr (hM i hi))
    linarith
  simpa [Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc] using hs

end PaperVerification.Lattice

#print axioms PaperVerification.Lattice.roundingEnvelope_eq_iff
#print axioms PaperVerification.Lattice.folded_square_sum_le
end
end Source_LatticeRounding
-- END ORIGINAL PaperVerification.LatticeRounding


-- BEGIN ORIGINAL PaperVerification.LatticeGeometry
section Source_LatticeGeometry

-- original header: module
-- original header: public import PaperVerification.LatticeDefs
-- original header: public import PaperVerification.LatticeRounding
-- original header: public import PaperVerification.LatticeCoordinates
-- original header: public import Mathlib.Data.Finset.Max
-- original header: public import Mathlib.Tactic.NormNum
-- original header: public import Mathlib.Algebra.Group.Nat.Even
-- original header: public import Mathlib.Algebra.Ring.Int.Parity
-- original header: @[expose] public section
/-! # Exact squared-distance formula and covering estimate for `D_n^+` -/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

variable {n : ℕ}

/-- Squared nearest-integer distance before a parity correction. -/
def integerBaseCost (x : Fin n → ℝ) : ℝ := ∑ i, (foldedRadius x i) ^ 2

/-- Squared nearest-half-integer distance before a parity correction. -/
def halfBaseCost (x : Fin n → ℝ) : ℝ := ∑ i, (1 / 2 - foldedRadius x i) ^ 2

/-- The actual correction in the even integer coset. -/
def integerRepairCost (x : Fin n → ℝ) (M : ℝ) : ℝ :=
  integerBaseCost x + if Even (∑ i, roundedInt x i) then 0 else 1 - 2 * M

/-- The actual correction in the even half-integer coset. -/
def halfRepairCost (x : Fin n → ℝ) (m : ℝ) : ℝ :=
  halfBaseCost x + if Even (∑ i, halfRoundedInt x i) then 0 else 2 * m

theorem halfBaseCost_eq (x : Fin n → ℝ) :
    halfBaseCost x = integerBaseCost x - (∑ i, foldedRadius x i) + (n : ℝ) / 4 := by
  unfold halfBaseCost integerBaseCost
  calc
    _ = ∑ i, ((foldedRadius x i) ^ 2 - foldedRadius x i + 1 / 4) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]; ring

theorem sqDist_roundedInt (x : Fin n → ℝ) :
    sqDist x (intVec (roundedInt x)) = integerBaseCost x := by
  simp [sqDist, intVec, integerBaseCost, foldedRadius, sq_abs]

theorem sqDist_halfRoundedInt (x : Fin n → ℝ) :
    sqDist x (fun i => (halfRoundedInt x i : ℝ) + 1 / 2) = halfBaseCost x := by
  apply Finset.sum_congr rfl
  intro i hi
  have h := congrArg (fun t : ℝ => t ^ 2) (abs_sub_halfRoundedInt x i)
  simpa only [sq_abs] using h

theorem integerRepairCost_le_sqDist (x : Fin n → ℝ) (z : Fin n → ℤ) (M : ℝ)
    (hM : ∀ i, foldedRadius x i ≤ M) (hz : Even (∑ i, z i)) :
    integerRepairCost x M ≤ sqDist x (intVec z) := by
  have h := even_integer_sq_lower x (roundedInt x) z M
    (foldedRadius_le_half x) hM hz
  simpa only [integerRepairCost, integerBaseCost, sqDist, intVec, foldedRadius, sq_abs] using h

theorem halfRepairCost_le_sqDist (x : Fin n → ℝ) (z : Fin n → ℤ) (m : ℝ)
    (hm : ∀ i, m ≤ foldedRadius x i) (hz : Even (∑ i, z i)) :
    halfRepairCost x m ≤ sqDist x (fun i => (z i : ℝ) + 1 / 2) := by
  have hrepr (i : Fin n) :
      |(x i - 1 / 2) - (halfRoundedInt x i : ℝ)| = 1 / 2 - foldedRadius x i := by
    convert abs_sub_halfRoundedInt x i using 1 <;> congr 1 <;> ring
  have hq (i : Fin n) : |(x i - 1 / 2) - (halfRoundedInt x i : ℝ)| ≤ 1 / 2 := by
    rw [hrepr]
    linarith [foldedRadius_nonneg x i]
  have hM (i : Fin n) : |(x i - 1 / 2) - (halfRoundedInt x i : ℝ)| ≤ 1 / 2 - m := by
    rw [hrepr]
    linarith [hm i]
  have h := even_integer_sq_lower (fun i => x i - 1 / 2) (halfRoundedInt x) z
    (1 / 2 - m) hq hM hz
  have hs (i : Fin n) : ((x i - 1 / 2) - (halfRoundedInt x i : ℝ)) ^ 2 =
      (1 / 2 - foldedRadius x i) ^ 2 := by
    rw [← hrepr, sq_abs]
  have ht (i : Fin n) : ((x i - 1 / 2) - (z i : ℝ)) ^ 2 =
      (x i - ((z i : ℝ) + 1 / 2)) ^ 2 := by ring
  simp only [hs, ht] at h
  unfold halfRepairCost halfBaseCost sqDist
  by_cases he : Even (∑ i, halfRoundedInt x i) <;> simp only [he, if_true, if_false] at h ⊢ <;>
    linarith

theorem squaredDepth_le_integerRepairCost (x : Fin n → ℝ) (j : Fin n) :
    squaredDepth (dPlusSet n) x ≤ integerRepairCost x (foldedRadius x j) := by
  by_cases he : Even (∑ i, roundedInt x i)
  · calc
      _ ≤ sqDist x (intVec (roundedInt x)) :=
        squaredDepth_le (L := dPlusSet n) x ⟨roundedInt x, he, Or.inl rfl⟩
      _ = _ := by rw [sqDist_roundedInt]; simp [integerRepairCost, he]
  · obtain ⟨z, hz, hdist⟩ := exists_even_integer_bound x j
    calc
      _ ≤ sqDist x (intVec z) := squaredDepth_le (L := dPlusSet n) x ⟨z, hz, Or.inl rfl⟩
      _ ≤ _ := by simpa [sqDist, intVec, integerRepairCost, integerBaseCost, he, sub_eq_add_neg, add_assoc] using hdist

theorem squaredDepth_le_halfRepairCost (x : Fin n → ℝ) (j : Fin n) :
    squaredDepth (dPlusSet n) x ≤ halfRepairCost x (foldedRadius x j) := by
  by_cases he : Even (∑ i, halfRoundedInt x i)
  · calc
      _ ≤ sqDist x (fun i => (halfRoundedInt x i : ℝ) + 1 / 2) :=
        squaredDepth_le (L := dPlusSet n) x ⟨halfRoundedInt x, he, Or.inr rfl⟩
      _ = _ := by rw [sqDist_halfRoundedInt]; simp [halfRepairCost, he]
  · obtain ⟨z, hz, hdist⟩ := exists_even_half_integer_bound x j
    calc
      _ ≤ sqDist x (fun i => (z i : ℝ) + 1 / 2) := squaredDepth_le (L := dPlusSet n) x ⟨z, hz, Or.inr rfl⟩
      _ ≤ _ := by simpa [sqDist, halfRepairCost, halfBaseCost, he] using hdist

/-- Exact squared distance to the actual union of the two even coordinate cosets. -/
theorem squaredDepth_dPlus_eq (x : Fin n → ℝ) (lo hi : Fin n)
    (hlo : ∀ i, foldedRadius x lo ≤ foldedRadius x i)
    (hhi : ∀ i, foldedRadius x i ≤ foldedRadius x hi) :
    squaredDepth (dPlusSet n) x =
      min (integerRepairCost x (foldedRadius x hi)) (halfRepairCost x (foldedRadius x lo)) := by
  apply le_antisymm
  · exact le_min (squaredDepth_le_integerRepairCost x hi) (squaredDepth_le_halfRepairCost x lo)
  · apply le_csInf ((dPlusSet_nonempty n).image (fun z => sqDist x z))
    rintro r ⟨v, hv, rfl⟩
    rcases hv with ⟨z, hz, h | h⟩
    · rw [h]
      exact (min_le_left _ _).trans (integerRepairCost_le_sqDist x z _ hhi hz)
    · rw [h]
      exact (min_le_right _ _).trans (halfRepairCost_le_sqDist x z _ hlo hz)

/-- Both parity repairs are bounded by the sharp algebraic envelope. -/
theorem squaredDepth_le_roundingEnvelope (x : Fin n → ℝ) (lo hi : Fin n)
    (hlo : ∀ i, foldedRadius x lo ≤ foldedRadius x i)
    (hhi : ∀ i, foldedRadius x i ≤ foldedRadius x hi) :
    squaredDepth (dPlusSet n) x ≤ PaperVerification.Lattice.roundingEnvelope (n : ℝ)
      (foldedRadius x lo) (foldedRadius x hi) (∑ i, foldedRadius x i) := by
  have hs : integerBaseCost x ≤ (foldedRadius x lo + foldedRadius x hi) *
      (∑ i, foldedRadius x i) - (n : ℝ) * foldedRadius x lo * foldedRadius x hi := by
    simpa [integerBaseCost] using PaperVerification.Lattice.folded_square_sum_le
      Finset.univ (foldedRadius x) (foldedRadius x lo) (foldedRadius x hi)
      (fun i _ => hlo i) (fun i _ => hhi i)
  obtain ⟨zi, hzi, hdi⟩ := exists_even_integer_bound x hi
  obtain ⟨zh, hzh, hdh⟩ := exists_even_half_integer_bound x lo
  have hiDepth := (squaredDepth_le x (show intVec zi ∈ dPlusSet n from
    ⟨zi, hzi, Or.inl rfl⟩)).trans hdi
  have hhDepth := (squaredDepth_le x (show (fun i => (zh i : ℝ) + 1 / 2) ∈ dPlusSet n from
    ⟨zh, hzh, Or.inr rfl⟩)).trans hdh
  change squaredDepth (dPlusSet n) x ≤ integerBaseCost x + 1 - 2 * foldedRadius x hi at hiDepth
  change squaredDepth (dPlusSet n) x ≤ halfBaseCost x + 2 * foldedRadius x lo at hhDepth
  rw [halfBaseCost_eq] at hhDepth
  unfold PaperVerification.Lattice.roundingEnvelope
  exact le_min (by linarith) (by linarith)

/-- The covering-radius upper bound in Proposition 3.4, for all dimensions n>=8. -/
theorem squaredDepth_dPlus_le (hn : 8 ≤ n) (x : Fin n → ℝ) :
    squaredDepth (dPlusSet n) x ≤ (n : ℝ) / 8 := by
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 8) hn
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn0⟩, Finset.mem_univ _⟩
  obtain ⟨lo, _, hlo⟩ := Finset.exists_min_image Finset.univ (foldedRadius x) hne
  obtain ⟨hi, _, hhi⟩ := Finset.exists_max_image Finset.univ (foldedRadius x) hne
  have hlo' : ∀ i, foldedRadius x lo ≤ foldedRadius x i := fun i => hlo i (Finset.mem_univ _)
  have hhi' : ∀ i, foldedRadius x i ≤ foldedRadius x hi := fun i => hhi i (Finset.mem_univ _)
  exact (squaredDepth_le_roundingEnvelope x lo hi hlo' hhi').trans
    (PaperVerification.Lattice.roundingEnvelope_le (n : ℝ) _ _ _ (by exact_mod_cast hn)
      (foldedRadius_nonneg x lo) (hlo' hi) (foldedRadius_le_half x hi))

/-- Every lattice point is at least as far away as independent coordinate rounding. -/
theorem min_baseCost_le_squaredDepth (x : Fin n → ℝ) :
    min (integerBaseCost x) (halfBaseCost x) ≤ squaredDepth (dPlusSet n) x := by
  apply le_csInf ((dPlusSet_nonempty n).image (fun z => sqDist x z))
  rintro r ⟨v, hv, rfl⟩
  rcases hv with ⟨z, hz, h | h⟩
  · rw [h]
    have hi := integerRepairCost_le_sqDist x z (1 / 2) (foldedRadius_le_half x) hz
    simp only [integerRepairCost] at hi
    norm_num at hi
    exact (min_le_left _ _).trans hi
  · rw [h]
    have hi := halfRepairCost_le_sqDist x z 0 (foldedRadius_nonneg x) hz
    simp only [halfRepairCost, mul_zero, ite_self, add_zero] at hi
    exact (min_le_right _ _).trans hi

/-- The folded-coordinate formulation of exactly half integer and half half-integer
coordinates. A separate equivalence identifies these radii with the stated grid. -/
def BalancedHalfGrid (x : Fin n → ℝ) : Prop :=
  (∀ i, foldedRadius x i = 0 ∨ foldedRadius x i = 1 / 2) ∧
    (∑ i, foldedRadius x i) = (n : ℝ) / 4

theorem integerBaseCost_of_balanced {x : Fin n → ℝ} (hx : BalancedHalfGrid x) :
    integerBaseCost x = (n : ℝ) / 8 := by
  have hi (i : Fin n) : (foldedRadius x i) ^ 2 = foldedRadius x i / 2 := by
    rcases hx.1 i with h | h <;> rw [h] <;> norm_num
  unfold integerBaseCost
  simp only [hi]
  rw [← Finset.sum_div, hx.2]
  ring

theorem halfBaseCost_of_balanced {x : Fin n → ℝ} (hx : BalancedHalfGrid x) :
    halfBaseCost x = (n : ℝ) / 8 := by
  rw [halfBaseCost_eq, integerBaseCost_of_balanced hx, hx.2]
  ring

/-- Every point in the full balanced half-grid attains the sharp radius. -/
theorem squaredDepth_dPlus_of_balanced (hn : 8 ≤ n) {x : Fin n → ℝ} (hx : BalancedHalfGrid x) :
    squaredDepth (dPlusSet n) x = (n : ℝ) / 8 := by
  apply le_antisymm (squaredDepth_dPlus_le hn x)
  have h := min_baseCost_le_squaredDepth x
  simpa only [integerBaseCost_of_balanced hx, halfBaseCost_of_balanced hx, min_self] using h


/-- The all-dimensional bound has no additional equality points when n>8. -/
theorem balanced_of_squaredDepth_eq (hn : 8 < n) {x : Fin n → ℝ}
    (hdepth : squaredDepth (dPlusSet n) x = (n : ℝ) / 8) : BalancedHalfGrid x := by
  have hn0 : 0 < n := lt_trans (by decide : 0 < 8) hn
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn0⟩, Finset.mem_univ _⟩
  obtain ⟨lo, _, hlo⟩ := Finset.exists_min_image Finset.univ (foldedRadius x) hne
  obtain ⟨hi, _, hhi⟩ := Finset.exists_max_image Finset.univ (foldedRadius x) hne
  have hlo' : ∀ i, foldedRadius x lo ≤ foldedRadius x i := fun i => hlo i (Finset.mem_univ _)
  have hhi' : ∀ i, foldedRadius x i ≤ foldedRadius x hi := fun i => hhi i (Finset.mem_univ _)
  have henv : PaperVerification.Lattice.roundingEnvelope (n : ℝ)
      (foldedRadius x lo) (foldedRadius x hi) (∑ i, foldedRadius x i) = (n : ℝ) / 8 := by
    apply le_antisymm
    · exact PaperVerification.Lattice.roundingEnvelope_le (n : ℝ) _ _ _
        (by exact_mod_cast hn.le) (foldedRadius_nonneg x lo) (hlo' hi) (foldedRadius_le_half x hi)
    · rw [← hdepth]
      exact squaredDepth_le_roundingEnvelope x lo hi hlo' hhi'
  obtain ⟨hm0, hMhalf, hT⟩ := (PaperVerification.Lattice.roundingEnvelope_eq_iff
    (n : ℝ) _ _ _ (by exact_mod_cast hn) (foldedRadius_nonneg x lo) (hlo' hi)
    (foldedRadius_le_half x hi)).mp henv
  have hhalf : halfBaseCost x = integerBaseCost x := by
    rw [halfBaseCost_eq, hT]
    ring
  have hQ : integerBaseCost x = (n : ℝ) / 8 := by
    have h := squaredDepth_dPlus_eq x lo hi hlo' hhi'
    simp [integerRepairCost, halfRepairCost, hm0, hMhalf, hhalf] at h
    linarith
  have hsum : (∑ i, foldedRadius x i * (1 / 2 - foldedRadius x i)) = 0 := by
    calc
      _ = (∑ i, foldedRadius x i) / 2 - integerBaseCost x := by
        unfold integerBaseCost
        rw [Finset.sum_div, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [hT, hQ]; ring
  refine ⟨?_, hT⟩
  intro i
  have hi : foldedRadius x i * (1 / 2 - foldedRadius x i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (foldedRadius_nonneg x j)
      (sub_nonneg.mpr (foldedRadius_le_half x j)))).mp hsum i (Finset.mem_univ _)
  rcases mul_eq_zero.mp hi with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-- An explicit finite-set construction supplies a balanced half-grid point
in every even dimension. No bounded enumeration is used. -/
theorem exists_balancedHalfGrid (heven : Even n) : ∃ x : Fin n → ℝ, BalancedHalfGrid x := by
  classical
  have hcard : n / 2 ≤ (Finset.univ : Finset (Fin n)).card := by
    simpa using Nat.div_le_self n 2
  obtain ⟨s, _, hs⟩ := Finset.exists_subset_card_eq hcard
  let x : Fin n → ℝ := fun i => if i ∈ s then 1 / 2 else 0
  have hround : round (1 / 2 : ℝ) = 1 := by norm_num [round_eq]
  have hr (i : Fin n) : foldedRadius x i = if i ∈ s then 1 / 2 else 0 := by
    by_cases hi : i ∈ s
    · norm_num [foldedRadius, roundedInt, x, hi, hround]
    · simp [foldedRadius, roundedInt, x, hi]
  refine ⟨x, ?_, ?_⟩
  · intro i
    rw [hr]
    by_cases hi : i ∈ s <;> simp [hi]
  · have hsum : (∑ i, foldedRadius x i) = (s.card : ℝ) / 2 := by
      simp only [hr]
      rw [Fintype.sum_ite_mem]
      simp <;> ring
    rw [hsum, hs]
    have he : 2 * (↑(n / 2) : ℝ) = (n : ℝ) := by
      exact_mod_cast Nat.two_mul_div_two_of_even heven
    linarith

/-- The maximum squared distance in every even dimension n>=8 is exactly n/8. -/
theorem dPlus_squared_covering_radius (hn : 8 ≤ n) (heven : Even n) :
    (∀ x : Fin n → ℝ, squaredDepth (dPlusSet n) x ≤ (n : ℝ) / 8) ∧
      ∃ x : Fin n → ℝ, squaredDepth (dPlusSet n) x = (n : ℝ) / 8 := by
  refine ⟨squaredDepth_dPlus_le hn, ?_⟩
  obtain ⟨x, hx⟩ := exists_balancedHalfGrid heven
  exact ⟨x, squaredDepth_dPlus_of_balanced hn hx⟩

theorem isDeepHole_dPlus_iff_depth (hn : 8 ≤ n) (heven : Even n) (x : Fin n → ℝ) :
    IsDeepHole (dPlusSet n) x ↔ squaredDepth (dPlusSet n) x = (n : ℝ) / 8 := by
  obtain ⟨hupper, y, hy⟩ := dPlus_squared_covering_radius hn heven
  constructor
  · intro hx
    exact le_antisymm (hupper x) (hy ▸ hx y)
  · intro hx y
    rw [hx]
    exact hupper y

/-- Complete deep-hole classification in all even dimensions strictly above eight. -/
theorem isDeepHole_dPlus_iff_balanced (hn : 8 < n) (heven : Even n) (x : Fin n → ℝ) :
    IsDeepHole (dPlusSet n) x ↔ BalancedHalfGrid x := by
  rw [isDeepHole_dPlus_iff_depth hn.le heven]
  exact ⟨balanced_of_squaredDepth_eq hn, squaredDepth_dPlus_of_balanced hn.le⟩


/-- Exact distance when every folded coordinate has the same value. -/
theorem squaredDepth_dPlus_of_constant (x : Fin n → ℝ) (j : Fin n) (t : ℝ)
    (ht : ∀ i, foldedRadius x i = t) :
    squaredDepth (dPlusSet n) x =
      min ((n : ℝ) * t ^ 2 + if Even (∑ i, roundedInt x i) then 0 else 1 - 2 * t)
        ((n : ℝ) * (1 / 2 - t) ^ 2 + if Even (∑ i, halfRoundedInt x i) then 0 else 2 * t) := by
  have h := squaredDepth_dPlus_eq x j j (by simp [ht]) (by simp [ht])
  simpa [integerRepairCost, halfRepairCost, integerBaseCost, halfBaseCost, ht] using h

/-- At the full spread endpoints, attaining n/8 forces the balanced half-grid. -/
theorem balanced_of_endpoint_extrema (x : Fin n → ℝ) (lo hi : Fin n)
    (hlo : ∀ i, foldedRadius x lo ≤ foldedRadius x i)
    (hhi : ∀ i, foldedRadius x i ≤ foldedRadius x hi)
    (hm : foldedRadius x lo = 0) (hM : foldedRadius x hi = 1 / 2)
    (hd : squaredDepth (dPlusSet n) x = (n : ℝ) / 8) : BalancedHalfGrid x := by
  have he := squaredDepth_le_roundingEnvelope x lo hi hlo hhi
  rw [hd, hm, hM] at he
  unfold PaperVerification.Lattice.roundingEnvelope at he
  obtain ⟨ha, hb⟩ := le_min_iff.mp he
  have hT : (∑ i, foldedRadius x i) = (n : ℝ) / 4 := by linarith
  have hhalf : halfBaseCost x = integerBaseCost x := by
    rw [halfBaseCost_eq, hT]
    ring
  have hQ : integerBaseCost x = (n : ℝ) / 8 := by
    have h := squaredDepth_dPlus_eq x lo hi hlo hhi
    simp [integerRepairCost, halfRepairCost, hm, hM, hhalf] at h
    linarith
  have hsum : (∑ i, foldedRadius x i * (1 / 2 - foldedRadius x i)) = 0 := by
    calc
      _ = (∑ i, foldedRadius x i) / 2 - integerBaseCost x := by
        unfold integerBaseCost
        rw [Finset.sum_div, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [hT, hQ]; ring
  refine ⟨?_, hT⟩
  intro i
  have hi : foldedRadius x i * (1 / 2 - foldedRadius x i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (foldedRadius_nonneg x j)
      (sub_nonneg.mpr (foldedRadius_le_half x j)))).mp hsum i (Finset.mem_univ _)
  exact (mul_eq_zero.mp hi).imp id (fun h => by linarith)

/-- The exceptional dimension-eight equality families, in canonical rounding
coordinates. The two endpoint families together give the integer/all-half hole
coset; the final family records both necessary quarter-grid parity conditions. -/
def E8FoldedHole (x : Fin 8 → ℝ) : Prop :=
  ((∀ i, foldedRadius x i = 0) ∧ ¬Even (∑ i, roundedInt x i)) ∨
  ((∀ i, foldedRadius x i = 1 / 2) ∧ ¬Even (∑ i, halfRoundedInt x i)) ∨
  BalancedHalfGrid x ∨
  ((∀ i, foldedRadius x i = 1 / 4) ∧ ¬Even (∑ i, roundedInt x i) ∧
    ¬Even (∑ i, halfRoundedInt x i))

/-- Complete equality analysis in dimension eight, including all extra families. -/
theorem squaredDepth_E8_eq_one_iff (x : Fin 8 → ℝ) :
    squaredDepth (dPlusSet 8) x = 1 ↔ E8FoldedHole x := by
  constructor
  · intro hd
    obtain ⟨lo, _, hlo⟩ := Finset.exists_min_image Finset.univ (foldedRadius x)
      (show (Finset.univ : Finset (Fin 8)).Nonempty from ⟨0, Finset.mem_univ _⟩)
    obtain ⟨hi, _, hhi⟩ := Finset.exists_max_image Finset.univ (foldedRadius x)
      (show (Finset.univ : Finset (Fin 8)).Nonempty from ⟨0, Finset.mem_univ _⟩)
    have hlo' : ∀ i, foldedRadius x lo ≤ foldedRadius x i := fun i => hlo i (Finset.mem_univ _)
    have hhi' : ∀ i, foldedRadius x i ≤ foldedRadius x hi := fun i => hhi i (Finset.mem_univ _)
    have hp : PaperVerification.Lattice.roundingPeak 8 (foldedRadius x lo) (foldedRadius x hi) = 1 := by
      apply le_antisymm
      · simpa using PaperVerification.Lattice.roundingPeak_le 8 _ _ (by norm_num)
          (foldedRadius_nonneg x lo) (hlo' hi) (foldedRadius_le_half x hi)
      · rw [← hd]
        exact (squaredDepth_le_roundingEnvelope x lo hi hlo' hhi').trans
          (PaperVerification.Lattice.roundingEnvelope_le_peak 8 _ _ _
            (foldedRadius_nonneg x lo) (hlo' hi) (foldedRadius_le_half x hi))
    rcases (PaperVerification.Lattice.roundingPeak_eight_eq_iff _ _
      (foldedRadius_nonneg x lo) (hlo' hi) (foldedRadius_le_half x hi)).mp hp with hflat | hends
    · let t := foldedRadius x lo
      have ht : ∀ i, foldedRadius x i = t := by
        intro i
        exact le_antisymm ((hhi' i).trans_eq hflat) (hlo' i)
      have hnonneg : 0 ≤ t := foldedRadius_nonneg x lo
      have hhalf : t ≤ 1 / 2 := foldedRadius_le_half x lo
      have hformula := squaredDepth_dPlus_of_constant x lo t ht
      rw [hd] at hformula
      by_cases hz : t = 0
      · apply Or.inl
        refine ⟨by simpa [hz] using ht, ?_⟩
        intro he
        norm_num [hz, he] at hformula
      · by_cases hh : t = 1 / 2
        · refine Or.inr (Or.inl ?_)
          refine ⟨by simpa [hh] using ht, ?_⟩
          intro he
          norm_num [hh, he] at hformula
        · have htpos : 0 < t := lt_of_le_of_ne hnonneg (Ne.symm hz)
          have htlt : t < 1 / 2 := lt_of_le_of_ne hhalf hh
          obtain ⟨zi, hzi, hdi⟩ := exists_even_integer_bound x lo
          obtain ⟨zh, hzh, hdh⟩ := exists_even_half_integer_bound x lo
          have hiDepth := (squaredDepth_le x (show intVec zi ∈ dPlusSet 8 from
            ⟨zi, hzi, Or.inl rfl⟩)).trans hdi
          have hhDepth := (squaredDepth_le x (show (fun i => (zh i : ℝ) + 1 / 2) ∈ dPlusSet 8 from
            ⟨zh, hzh, Or.inr rfl⟩)).trans hdh
          simp only [hd, ht, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_ofNat] at hiDepth hhDepth
          have hquarter : t = 1 / 4 := by
            apply le_antisymm
            · by_contra h
              have hp := mul_pos (by linarith : 0 < 4 * t - 1) (by linarith : 0 < 1 - 2 * t)
              nlinarith only [hhDepth, hp]
            · by_contra h
              have hp := mul_pos htpos (by linarith : 0 < 1 - 4 * t)
              nlinarith only [hiDepth, hp]
          refine Or.inr (Or.inr (Or.inr ?_))
          refine ⟨by simpa [hquarter] using ht, ?_, ?_⟩
          · intro he
            by_cases he' : Even (∑ i, halfRoundedInt x i) <;>
              norm_num [hquarter, he, he'] at hformula
          · intro he
            by_cases he' : Even (∑ i, roundedInt x i) <;>
              norm_num [hquarter, he, he'] at hformula
    · refine Or.inr (Or.inr (Or.inl ?_))
      exact balanced_of_endpoint_extrema x lo hi hlo' hhi' hends.1 hends.2 (by simpa using hd)
  · rintro (⟨ht, he⟩ | ⟨ht, he⟩ | hb | ⟨ht, he, he'⟩)
    · have h := squaredDepth_dPlus_of_constant x 0 0 ht
      norm_num [he] at h
      exact h
    · have h := squaredDepth_dPlus_of_constant x 0 (1 / 2) ht
      norm_num [he] at h
      exact h
    · simpa using squaredDepth_dPlus_of_balanced (by decide : 8 ≤ 8) hb
    · have h := squaredDepth_dPlus_of_constant x 0 (1 / 4) ht
      norm_num [he, he'] at h
      exact h

/-- The complete deep-hole classification for E8 in folded coordinates. -/
theorem isDeepHole_E8_iff (x : Fin 8 → ℝ) : IsDeepHole (dPlusSet 8) x ↔ E8FoldedHole x := by
  rw [isDeepHole_dPlus_iff_depth (by decide : 8 ≤ 8) (⟨4, by norm_num⟩ : Even 8)]
  norm_num
  exact squaredDepth_E8_eq_one_iff x


/-- Membership in the coordinate half-integer grid, with its usual meaning. -/
def HalfIntegerGrid (x : Fin n → ℝ) : Prop := ∀ i, ∃ k : ℤ, x i = (k : ℝ) / 2

/-- Count coordinates that are not integers. -/
def nonintegerCount (x : Fin n → ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => ¬∃ k : ℤ, x i = (k : ℝ)).card

/-- The exact set displayed in equation (10) of the manuscript. -/
def PaperHalfGrid (x : Fin n → ℝ) : Prop := HalfIntegerGrid x ∧ nonintegerCount x = n / 2

theorem halfIntegerCoordinate_iff (x : Fin n → ℝ) (i : Fin n) :
    (∃ k : ℤ, x i = (k : ℝ) / 2) ↔
      foldedRadius x i = 0 ∨ foldedRadius x i = 1 / 2 := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨z, he | ho⟩ := Int.even_or_odd' k
    · apply Or.inl
      apply (foldedRadius_eq_zero_iff x i).mpr
      refine ⟨z, ?_⟩
      rw [hk, he]
      push_cast
      ring
    · apply Or.inr
      apply (foldedRadius_eq_half_iff x i).mpr
      refine ⟨z, ?_⟩
      rw [hk, ho]
      push_cast
      ring
  · rintro (h | h)
    · obtain ⟨z, hz⟩ := (foldedRadius_eq_zero_iff x i).mp h
      refine ⟨2 * z, ?_⟩
      rw [hz]
      push_cast
      ring
    · obtain ⟨z, hz⟩ := (foldedRadius_eq_half_iff x i).mp h
      refine ⟨2 * z + 1, ?_⟩
      rw [hz]
      push_cast
      ring

theorem folded_sum_eq_nonintegerCount (x : Fin n → ℝ)
    (hx : ∀ i, foldedRadius x i = 0 ∨ foldedRadius x i = 1 / 2) :
    (∑ i, foldedRadius x i) = (nonintegerCount x : ℝ) / 2 := by
  classical
  have hi (i : Fin n) : foldedRadius x i =
      if ¬∃ k : ℤ, x i = (k : ℝ) then 1 / 2 else 0 := by
    by_cases hz : ∃ k : ℤ, x i = (k : ℝ)
    · simp [hz, (foldedRadius_eq_zero_iff x i).mpr hz]
    · simp only [hz, not_false_eq_true, if_true]
      rcases hx i with h | h
      · exact False.elim (hz ((foldedRadius_eq_zero_iff x i).mp h))
      · exact h
  simp only [hi]
  rw [Finset.sum_ite]
  simp [nonintegerCount] <;> ring

/-- The folded characterization is faithfully equivalent to the paper's actual
half-grid and exact cardinality condition, throughout its stated even dimensions. -/
theorem balancedHalfGrid_iff_paperHalfGrid (heven : Even n) (x : Fin n → ℝ) :
    BalancedHalfGrid x ↔ PaperHalfGrid x := by
  constructor
  · intro hx
    refine ⟨fun i => (halfIntegerCoordinate_iff x i).mpr (hx.1 i), ?_⟩
    have hsum := folded_sum_eq_nonintegerCount x hx.1
    have he : 2 * nonintegerCount x = n := by
      have heR : 2 * (nonintegerCount x : ℝ) = (n : ℝ) := by linarith [hx.2]
      exact_mod_cast heR
    calc
      nonintegerCount x = (2 * nonintegerCount x) / 2 := by simp
      _ = n / 2 := by rw [he]
  · rintro ⟨hgrid, hcount⟩
    have hx : ∀ i, foldedRadius x i = 0 ∨ foldedRadius x i = 1 / 2 :=
      fun i => (halfIntegerCoordinate_iff x i).mp (hgrid i)
    refine ⟨hx, ?_⟩
    rw [folded_sum_eq_nonintegerCount x hx, hcount]
    have he : 2 * (↑(n / 2) : ℝ) = (n : ℝ) := by
      exact_mod_cast Nat.two_mul_div_two_of_even heven
    linarith

/-- Proposition 3.4's complete n>8 equality locus with its original coordinate meaning. -/
theorem isDeepHole_dPlus_iff_paperHalfGrid (hn : 8 < n) (heven : Even n) (x : Fin n → ℝ) :
    IsDeepHole (dPlusSet n) x ↔ PaperHalfGrid x :=
  (isDeepHole_dPlus_iff_balanced hn heven x).trans (balancedHalfGrid_iff_paperHalfGrid heven x)

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.squaredDepth_dPlus_le
#print axioms PaperVerification.ColdSpots.squaredDepth_dPlus_of_balanced

#print axioms PaperVerification.ColdSpots.dPlus_squared_covering_radius
#print axioms PaperVerification.ColdSpots.isDeepHole_dPlus_iff_balanced

#print axioms PaperVerification.ColdSpots.isDeepHole_E8_iff

#print axioms PaperVerification.ColdSpots.isDeepHole_dPlus_iff_paperHalfGrid
end
end Source_LatticeGeometry
-- END ORIGINAL PaperVerification.LatticeGeometry


-- BEGIN ORIGINAL PaperVerification.GaussianFourier
section Source_GaussianFourier

-- original header: module
-- original header: public import PaperVerification.Gaussian
-- original header: public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
-- original header: public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
-- original header: public import Mathlib.Tactic.FieldSimp
-- original header: @[expose] public section
noncomputable section

open scoped BigOperators

namespace PaperVerification.ColdSpots

def fourierGaussian (β t : ℝ) : ℝ :=
  ∑' n : ℤ, Real.exp (-β * (n : ℝ) ^ 2) * Real.cos (2 * Real.pi * t * n)

def complexFourierTerm (β t : ℝ) (n : ℤ) : ℂ :=
  Complex.exp (((-β * (n : ℝ) ^ 2 : ℝ) : ℂ) +
    ((2 * Real.pi * t * n : ℝ) : ℂ) * Complex.I)

lemma complexFourierTerm_norm (β t : ℝ) (n : ℤ) :
    ‖complexFourierTerm β t n‖ = Real.exp (-β * (n : ℝ) ^ 2) := by
  rw [complexFourierTerm, Complex.norm_exp]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

lemma complexFourierTerm_re (β t : ℝ) (n : ℤ) :
    (complexFourierTerm β t n).re =
      Real.exp (-β * (n : ℝ) ^ 2) * Real.cos (2 * Real.pi * t * n) := by
  rw [complexFourierTerm, Complex.exp_re]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    mul_one, sub_zero, add_zero, zero_add]

lemma summable_complexFourierTerm {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    Summable (complexFourierTerm β t) := by
  apply (summable_gaussian_zero hβ).of_norm_bounded
  intro n
  rw [complexFourierTerm_norm]

lemma summable_fourierGaussian {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    Summable (fun n : ℤ ↦ Real.exp (-β * (n : ℝ) ^ 2) *
      Real.cos (2 * Real.pi * t * n)) := by
  apply (summable_gaussian_zero hβ).of_norm_bounded
  intro n
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)

/-- Poisson summation with its normalization explicitly matched to the manuscript. -/
theorem gaussian_poisson {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α t = Real.sqrt (Real.pi / α) * fourierGaussian (Real.pi ^ 2 / α) t := by
  have ha : 0 < Real.pi / α := div_pos Real.pi_pos hα
  have hβ : 0 < Real.pi ^ 2 / α := div_pos (sq_pos_of_pos Real.pi_pos) hα
  have hπC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hαC : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  have hl (n : ℤ) :
      Complex.exp (-(Real.pi : ℂ) * (Real.pi / α : ℝ) * (n : ℂ) ^ 2 +
        2 * Real.pi * (Complex.I * (t : ℂ)) * n) =
      complexFourierTerm (Real.pi ^ 2 / α) t n := by
    unfold complexFourierTerm
    congr 1
    push_cast
    ring
  have hI : Complex.I * (Complex.I * (t : ℂ)) = -(t : ℂ) := by
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  have hr (n : ℤ) :
      Complex.exp (-(Real.pi : ℂ) / (Real.pi / α : ℝ) *
        ((n : ℂ) + Complex.I * (Complex.I * (t : ℂ))) ^ 2) =
      (Real.exp (-α * ((n : ℝ) - t) ^ 2) : ℂ) := by
    rw [hI, Complex.ofReal_exp]
    congr 1
    push_cast
    field_simp [hπC, hαC]
    ring
  have hc : (1 : ℂ) / ((Real.pi / α : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
      ((1 / Real.sqrt (Real.pi / α) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow]
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    rw [Complex.ofReal_cpow ha.le]
    norm_num
  have ht := Complex.tsum_exp_neg_quadratic
    (show 0 < ((Real.pi / α : ℝ) : ℂ).re by simpa using ha) (Complex.I * (t : ℂ))
  simp only [hl, hr, hc, ← Complex.ofReal_tsum] at ht
  have hre := congrArg Complex.re ht
  rw [Complex.re_tsum (summable_complexFourierTerm hβ t)] at hre
  simp only [complexFourierTerm_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] at hre
  change fourierGaussian (Real.pi ^ 2 / α) t =
    (1 / Real.sqrt (Real.pi / α)) * gaussian α t at hre
  have hs : Real.sqrt (Real.pi / α) ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  rw [hre]
  field_simp

lemma fourierGaussian_le_zero {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    fourierGaussian β t ≤ fourierGaussian β 0 := by
  unfold fourierGaussian
  apply (summable_fourierGaussian hβ t).tsum_le_tsum _ (summable_fourierGaussian hβ 0)
  intro n
  simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.cos_le_one _)

lemma fourierGaussian_lt_zero {β : ℝ} (hβ : 0 < β) (t : ℝ)
    (ht : ¬∃ z : ℤ, t = (z : ℝ)) : fourierGaussian β t < fourierGaussian β 0 := by
  have hcos : Real.cos (2 * Real.pi * t) < 1 := by
    apply lt_of_le_of_ne (Real.cos_le_one _)
    intro heq
    obtain ⟨z, hz⟩ := (Real.cos_eq_one_iff _).mp heq
    apply ht
    refine ⟨z, ?_⟩
    apply (mul_left_cancel₀ (show 2 * Real.pi ≠ 0 by positivity))
    nlinarith [hz]
  unfold fourierGaussian
  apply Summable.tsum_lt_tsum (i := (1 : ℤ)) ?_ ?_
    (summable_fourierGaussian hβ t) (summable_fourierGaussian hβ 0)
  · intro n
    simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.cos_le_one _)
  · simp only [Int.cast_one, mul_one, one_pow, mul_zero, zero_mul, Real.cos_zero]
    simpa only [mul_one] using mul_lt_mul_of_pos_left hcos (Real.exp_pos (-β))

theorem gaussian_le_zero {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α t ≤ gaussian α 0 := by
  rw [gaussian_poisson hα t, gaussian_poisson hα 0]
  exact mul_le_mul_of_nonneg_left
    (fourierGaussian_le_zero (div_pos (sq_pos_of_pos Real.pi_pos) hα) t)
    (Real.sqrt_nonneg _)

theorem gaussian_maximum_iff {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α t = gaussian α 0 ↔ ∃ z : ℤ, t = (z : ℝ) := by
  constructor
  · intro heq
    by_contra ht
    have hlt := fourierGaussian_lt_zero (div_pos (sq_pos_of_pos Real.pi_pos) hα) t ht
    have h := mul_lt_mul_of_pos_left hlt
      (Real.sqrt_pos.mpr (div_pos Real.pi_pos hα))
    rw [← gaussian_poisson hα t, ← gaussian_poisson hα 0] at h
    exact (ne_of_lt h) heq
  · rintro ⟨z, rfl⟩
    simpa only [zero_add] using gaussian_int_period α 0 z

end PaperVerification.ColdSpots
end
end Source_GaussianFourier
-- END ORIGINAL PaperVerification.GaussianFourier


-- BEGIN ORIGINAL PaperVerification.GaussianDuplication
section Source_GaussianDuplication

-- original header: module
-- original header: public import PaperVerification.GaussianProduct
-- original header: public import Lean.Elab.Tactic.Omega
-- original header: @[expose] public section
noncomputable section

open scoped BigOperators

namespace PaperVerification.ColdSpots

/-- Half-sum/half-difference coordinates, with an explicit parity tag. -/
def pairParityEquiv : (ℤ × ℤ) ⊕ (ℤ × ℤ) ≃ ℤ × ℤ where
  toFun
    | .inl (u, v) => (u + v, u - v)
    | .inr (u, v) => (u + v + 1, u - v)
  invFun p := if Even (p.1 + p.2) then
    .inl ((p.1 + p.2) / 2, (p.1 - p.2) / 2) else
    .inr ((p.1 + p.2) / 2, (p.1 - p.2) / 2)
  left_inv := by
    intro s
    cases s with
    | inl p =>
      rcases p with ⟨u, v⟩
      have he : Even (u + v + (u - v)) := by
        exact ⟨u, by omega⟩
      simp only [he, ↓reduceIte, Sum.inl.injEq, Prod.mk.injEq]
      omega
    | inr p =>
      rcases p with ⟨u, v⟩
      have he : ¬Even (u + v + 1 + (u - v)) := by
        rw [Int.even_iff]
        omega
      simp only [he, ↓reduceIte, Sum.inr.injEq, Prod.mk.injEq]
      omega
  right_inv := by
    rintro ⟨a, b⟩
    dsimp only
    split_ifs with he
    · rw [Int.even_iff] at he
      apply Prod.ext <;> dsimp <;> omega
    · rw [Int.even_iff] at he
      apply Prod.ext <;> dsimp <;> omega

lemma hasSum_gaussian_pair {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (t s : ℝ) :
    HasSum (fun p : ℤ × ℤ ↦ Real.exp (-α * ((p.1 : ℝ) - t) ^ 2) *
      Real.exp (-β * ((p.2 : ℝ) - s) ^ 2)) (gaussian α t * gaussian β s) :=
  (hasSum_gaussian hα t).mul (hasSum_gaussian hβ s)
    (summable_mul_of_summable_norm (summable_gaussian hα t).norm
      (summable_gaussian hβ s).norm)

lemma hasSum_alternatingGaussian_pair {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (t s : ℝ) :
    HasSum (fun p : ℤ × ℤ ↦
      (paritySign p.1 * Real.exp (-α * ((p.1 : ℝ) - t) ^ 2)) *
      (paritySign p.2 * Real.exp (-β * ((p.2 : ℝ) - s) ^ 2)))
      (alternatingGaussian α t * alternatingGaussian β s) :=
  (hasSum_alternatingGaussian hα t).mul
    (hasSum_alternatingGaussian hβ s)
    (summable_mul_of_summable_norm (summable_alternatingGaussian hα t).norm
      (summable_alternatingGaussian hβ s).norm)

lemma gaussian_pair_even (α t : ℝ) (p : ℤ × ℤ) :
    Real.exp (-α * (((pairParityEquiv (.inl p)).1 : ℝ) - t) ^ 2) *
      Real.exp (-α * (((pairParityEquiv (.inl p)).2 : ℝ) - t) ^ 2) =
    Real.exp (-(2 * α) * ((p.1 : ℝ) - t) ^ 2) *
      Real.exp (-(2 * α) * (p.2 : ℝ) ^ 2) := by
  simp only [pairParityEquiv, Equiv.coe_fn_mk, Int.cast_add, Int.cast_sub]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

lemma gaussian_pair_odd (α t : ℝ) (p : ℤ × ℤ) :
    Real.exp (-α * (((pairParityEquiv (.inr p)).1 : ℝ) - t) ^ 2) *
      Real.exp (-α * (((pairParityEquiv (.inr p)).2 : ℝ) - t) ^ 2) =
    Real.exp (-(2 * α) * ((p.1 : ℝ) - (t - 1 / 2)) ^ 2) *
      Real.exp (-(2 * α) * ((p.2 : ℝ) - (-(1 / 2))) ^ 2) := by
  simp only [pairParityEquiv, Equiv.coe_fn_mk, Int.cast_add, Int.cast_sub, Int.cast_one]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The first duplication formula in Equation (1), as an identity of convergent series. -/
theorem gaussian_duplication {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α t ^ 2 = gaussian (2 * α) 0 * gaussian (2 * α) t +
      gaussian (2 * α) (1 / 2) * gaussian (2 * α) (t - 1 / 2) := by
  let f : ℤ × ℤ → ℝ := fun p ↦
    Real.exp (-α * ((p.1 : ℝ) - t) ^ 2) * Real.exp (-α * ((p.2 : ℝ) - t) ^ 2)
  have he : HasSum (fun p : ℤ × ℤ ↦ f (pairParityEquiv (.inl p)))
      (gaussian (2 * α) t * gaussian (2 * α) 0) := by
    simpa only [f, gaussian_pair_even, sub_zero] using
      hasSum_gaussian_pair (mul_pos (by norm_num) hα) (mul_pos (by norm_num) hα) t 0
  have ho : HasSum (fun p : ℤ × ℤ ↦ f (pairParityEquiv (.inr p)))
      (gaussian (2 * α) (t - 1 / 2) * gaussian (2 * α) (-(1 / 2))) := by
    simpa only [f, gaussian_pair_odd] using
      hasSum_gaussian_pair (mul_pos (by norm_num) hα) (mul_pos (by norm_num) hα)
        (t - 1 / 2) (-(1 / 2))
  have hs : HasSum f (gaussian (2 * α) t * gaussian (2 * α) 0 +
      gaussian (2 * α) (t - 1 / 2) * gaussian (2 * α) (-(1 / 2))) :=
    (pairParityEquiv.hasSum_iff (f := f)).mp (he.sum ho)
  have hu := (hasSum_gaussian_pair hα hα t t).unique hs
  rw [gaussian_even] at hu
  simpa only [pow_two, mul_comm] using hu

lemma paritySign_pair_even (p : ℤ × ℤ) :
    paritySign (pairParityEquiv (.inl p)).1 *
      paritySign (pairParityEquiv (.inl p)).2 = 1 := by
  rw [← paritySign_add]
  have he : Even ((pairParityEquiv (.inl p)).1 + (pairParityEquiv (.inl p)).2) := by
    refine ⟨p.1, ?_⟩
    dsimp [pairParityEquiv]
    omega
  simp [paritySign, he]

lemma paritySign_pair_odd (p : ℤ × ℤ) :
    paritySign (pairParityEquiv (.inr p)).1 *
      paritySign (pairParityEquiv (.inr p)).2 = -1 := by
  rw [← paritySign_add]
  have he : ¬Even ((pairParityEquiv (.inr p)).1 + (pairParityEquiv (.inr p)).2) := by
    rw [Int.even_iff]
    dsimp [pairParityEquiv]
    omega
  simp [paritySign, he]

lemma alternating_pair_even (α t : ℝ) (p : ℤ × ℤ) :
    (paritySign (pairParityEquiv (.inl p)).1 *
      Real.exp (-α * (((pairParityEquiv (.inl p)).1 : ℝ) - t) ^ 2)) *
    (paritySign (pairParityEquiv (.inl p)).2 *
      Real.exp (-α * (((pairParityEquiv (.inl p)).2 : ℝ) - t) ^ 2)) =
    Real.exp (-(2 * α) * ((p.1 : ℝ) - t) ^ 2) *
      Real.exp (-(2 * α) * (p.2 : ℝ) ^ 2) := by
  rw [mul_mul_mul_comm, paritySign_pair_even, one_mul, gaussian_pair_even]

lemma alternating_pair_odd (α t : ℝ) (p : ℤ × ℤ) :
    (paritySign (pairParityEquiv (.inr p)).1 *
      Real.exp (-α * (((pairParityEquiv (.inr p)).1 : ℝ) - t) ^ 2)) *
    (paritySign (pairParityEquiv (.inr p)).2 *
      Real.exp (-α * (((pairParityEquiv (.inr p)).2 : ℝ) - t) ^ 2)) =
    -(Real.exp (-(2 * α) * ((p.1 : ℝ) - (t - 1 / 2)) ^ 2) *
      Real.exp (-(2 * α) * ((p.2 : ℝ) - (-(1 / 2))) ^ 2)) := by
  rw [mul_mul_mul_comm, paritySign_pair_odd, neg_one_mul, gaussian_pair_odd]

/-- The alternating duplication formula in Equation (1). -/
theorem alternatingGaussian_duplication {α : ℝ} (hα : 0 < α) (t : ℝ) :
    alternatingGaussian α t ^ 2 = gaussian (2 * α) 0 * gaussian (2 * α) t -
      gaussian (2 * α) (1 / 2) * gaussian (2 * α) (t - 1 / 2) := by
  let f : ℤ × ℤ → ℝ := fun p ↦
    (paritySign p.1 * Real.exp (-α * ((p.1 : ℝ) - t) ^ 2)) *
    (paritySign p.2 * Real.exp (-α * ((p.2 : ℝ) - t) ^ 2))
  have he : HasSum (fun p : ℤ × ℤ ↦ f (pairParityEquiv (.inl p)))
      (gaussian (2 * α) t * gaussian (2 * α) 0) := by
    simpa only [f, alternating_pair_even, sub_zero] using
      hasSum_gaussian_pair (mul_pos (by norm_num) hα) (mul_pos (by norm_num) hα) t 0
  have ho : HasSum (fun p : ℤ × ℤ ↦ f (pairParityEquiv (.inr p)))
      (-(gaussian (2 * α) (t - 1 / 2) * gaussian (2 * α) (-(1 / 2)))) := by
    simpa only [f, alternating_pair_odd] using
      (hasSum_gaussian_pair (mul_pos (by norm_num) hα) (mul_pos (by norm_num) hα)
        (t - 1 / 2) (-(1 / 2))).neg
  have hs : HasSum f (gaussian (2 * α) t * gaussian (2 * α) 0 +
      -(gaussian (2 * α) (t - 1 / 2) * gaussian (2 * α) (-(1 / 2)))) :=
    (pairParityEquiv.hasSum_iff (f := f)).mp (he.sum ho)
  have hu := (hasSum_alternatingGaussian_pair hα hα t t).unique hs
  rw [gaussian_even] at hu
  simpa only [pow_two, sub_eq_add_neg, mul_comm] using hu

end PaperVerification.ColdSpots
end
end Source_GaussianDuplication
-- END ORIGINAL PaperVerification.GaussianDuplication


-- BEGIN ORIGINAL PaperVerification.GaussianIdentities
section Source_GaussianIdentities

-- original header: module
-- original header: public import PaperVerification.GaussianDuplication
-- original header: public import Mathlib.Tactic.FieldSimp
-- original header: @[expose] public section
noncomputable section

open scoped BigOperators

namespace PaperVerification.ColdSpots

/-- The two congruence classes of the integers, without counting any point twice. -/
def integerParityEquiv : ℤ ⊕ ℤ ≃ ℤ where
  toFun
    | .inl u => 2 * u
    | .inr u => 2 * u + 1
  invFun z := if Even z then .inl (z / 2) else .inr (z / 2)
  left_inv := by
    intro z
    cases z with
    | inl u =>
      have he : Even (2 * u) := ⟨u, by omega⟩
      simp only [he, ↓reduceIte, Sum.inl.injEq]
      omega
    | inr u =>
      have he : ¬Even (2 * u + 1) := by rw [Int.even_iff]; omega
      simp only [he, ↓reduceIte, Sum.inr.injEq]
      omega
  right_inv := by
    intro z
    dsimp only
    split_ifs with he
    · rw [Int.even_iff] at he
      dsimp
      omega
    · rw [Int.even_iff] at he
      dsimp
      omega

lemma gaussian_integer_even_term (α t : ℝ) (u : ℤ) :
    Real.exp (-α * ((integerParityEquiv (.inl u) : ℝ) - t) ^ 2) =
      Real.exp (-(4 * α) * ((u : ℝ) - t / 2) ^ 2) := by
  simp only [integerParityEquiv, Equiv.coe_fn_mk, Int.cast_mul, Int.cast_ofNat]
  congr 1
  ring

lemma gaussian_integer_odd_term (α t : ℝ) (u : ℤ) :
    Real.exp (-α * ((integerParityEquiv (.inr u) : ℝ) - t) ^ 2) =
      Real.exp (-(4 * α) * ((u : ℝ) - (t - 1) / 2) ^ 2) := by
  simp only [integerParityEquiv, Equiv.coe_fn_mk, Int.cast_mul, Int.cast_ofNat,
    Int.cast_add, Int.cast_one]
  congr 1
  ring

theorem gaussian_split {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α t = gaussian (4 * α) (t / 2) + gaussian (4 * α) ((t - 1) / 2) := by
  have h4 : 0 < 4 * α := mul_pos (by norm_num) hα
  have he : HasSum (fun u : ℤ ↦
      Real.exp (-α * ((integerParityEquiv (.inl u) : ℝ) - t) ^ 2))
      (gaussian (4 * α) (t / 2)) := by
    simpa only [gaussian_integer_even_term] using
      hasSum_gaussian h4 (t / 2)
  have ho : HasSum (fun u : ℤ ↦
      Real.exp (-α * ((integerParityEquiv (.inr u) : ℝ) - t) ^ 2))
      (gaussian (4 * α) ((t - 1) / 2)) := by
    simpa only [gaussian_integer_odd_term] using
      hasSum_gaussian h4 ((t - 1) / 2)
  exact ((integerParityEquiv.hasSum_iff
    (f := fun z : ℤ ↦ Real.exp (-α * ((z : ℝ) - t) ^ 2))).mp (he.sum ho)).tsum_eq

theorem alternatingGaussian_split {α : ℝ} (hα : 0 < α) (t : ℝ) :
    alternatingGaussian α t =
      gaussian (4 * α) (t / 2) - gaussian (4 * α) ((t - 1) / 2) := by
  have h4 : 0 < 4 * α := mul_pos (by norm_num) hα
  have hsignEven (u : ℤ) : paritySign (integerParityEquiv (.inl u)) = 1 := by
    have h : Even (2 * u) := ⟨u, by ring⟩
    change (if Even (2 * u) then (1 : ℝ) else -1) = 1
    simp only [h, ite_true]
  have hsignOdd (u : ℤ) : paritySign (integerParityEquiv (.inr u)) = -1 := by
    have h : ¬Even (2 * u + 1) := by rw [Int.even_iff]; omega
    change (if Even (2 * u + 1) then (1 : ℝ) else -1) = -1
    simp only [h, ite_false]
  let f : ℤ → ℝ := fun z ↦ paritySign z * Real.exp (-α * ((z : ℝ) - t) ^ 2)
  have he : HasSum (fun u : ℤ ↦ f (integerParityEquiv (.inl u)))
      (gaussian (4 * α) (t / 2)) := by
    simpa only [f, hsignEven, one_mul, gaussian_integer_even_term] using
      hasSum_gaussian h4 (t / 2)
  have ho : HasSum (fun u : ℤ ↦ f (integerParityEquiv (.inr u)))
      (-gaussian (4 * α) ((t - 1) / 2)) := by
    simpa only [f, hsignOdd, neg_one_mul, gaussian_integer_odd_term] using
      (hasSum_gaussian h4 ((t - 1) / 2)).neg
  have hs := (integerParityEquiv.hasSum_iff (f := f)).mp (he.sum ho)
  simpa only [sub_eq_add_neg] using (hasSum_alternatingGaussian hα t).unique hs

theorem gaussian_half_eq_twice_quarter {α : ℝ} (hα : 0 < α) :
    gaussian α (1 / 2) = 2 * gaussian (4 * α) (1 / 4) := by
  rw [gaussian_split hα]
  norm_num
  rw [gaussian_even]
  ring

lemma gaussian_pair_general_even (α t s : ℝ) (p : ℤ × ℤ) :
    Real.exp (-α * (((pairParityEquiv (.inl p)).1 : ℝ) - t) ^ 2) *
      Real.exp (-α * (((pairParityEquiv (.inl p)).2 : ℝ) - s) ^ 2) =
    Real.exp (-(2 * α) * ((p.1 : ℝ) - (t + s) / 2) ^ 2) *
      Real.exp (-(2 * α) * ((p.2 : ℝ) - (t - s) / 2) ^ 2) := by
  simp only [pairParityEquiv, Equiv.coe_fn_mk, Int.cast_add, Int.cast_sub]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

lemma gaussian_pair_general_odd (α t s : ℝ) (p : ℤ × ℤ) :
    Real.exp (-α * (((pairParityEquiv (.inr p)).1 : ℝ) - t) ^ 2) *
      Real.exp (-α * (((pairParityEquiv (.inr p)).2 : ℝ) - s) ^ 2) =
    Real.exp (-(2 * α) * ((p.1 : ℝ) - (t + s - 1) / 2) ^ 2) *
      Real.exp (-(2 * α) * ((p.2 : ℝ) - (t - s - 1) / 2) ^ 2) := by
  simp only [pairParityEquiv, Equiv.coe_fn_mk, Int.cast_add, Int.cast_sub, Int.cast_one]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- Addition formula obtained from a bijection of the two-dimensional integer lattice. -/
theorem gaussian_addition {α : ℝ} (hα : 0 < α) (t s : ℝ) :
    gaussian α t * gaussian α s =
      gaussian (2 * α) ((t + s) / 2) * gaussian (2 * α) ((t - s) / 2) +
      gaussian (2 * α) ((t + s - 1) / 2) * gaussian (2 * α) ((t - s - 1) / 2) := by
  let f : ℤ × ℤ → ℝ := fun p ↦
    Real.exp (-α * ((p.1 : ℝ) - t) ^ 2) * Real.exp (-α * ((p.2 : ℝ) - s) ^ 2)
  have h2 : 0 < 2 * α := mul_pos (by norm_num) hα
  have he : HasSum (fun p : ℤ × ℤ ↦ f (pairParityEquiv (.inl p)))
      (gaussian (2 * α) ((t + s) / 2) * gaussian (2 * α) ((t - s) / 2)) := by
    simpa only [f, gaussian_pair_general_even] using
      hasSum_gaussian_pair h2 h2 ((t + s) / 2) ((t - s) / 2)
  have ho : HasSum (fun p : ℤ × ℤ ↦ f (pairParityEquiv (.inr p)))
      (gaussian (2 * α) ((t + s - 1) / 2) *
        gaussian (2 * α) ((t - s - 1) / 2)) := by
    simpa only [f, gaussian_pair_general_odd] using
      hasSum_gaussian_pair h2 h2 ((t + s - 1) / 2) ((t - s - 1) / 2)
  exact (hasSum_gaussian_pair hα hα t s).unique
    ((pairParityEquiv.hasSum_iff (f := f)).mp (he.sum ho))

/-- Equation (3) of the cold-spots manuscript. -/
theorem gaussian_shift_product {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α t * gaussian α (t - 1 / 2) =
      gaussian (2 * α) (1 / 4) * gaussian (α / 2) (2 * t - 1 / 2) := by
  rw [gaussian_addition hα]
  have hs := gaussian_split (half_pos hα) (2 * t - 1 / 2)
  have h₁ : (t + (t - 1 / 2)) / 2 = t - 1 / 4 := by ring
  have h₂ : (t - (t - 1 / 2)) / 2 = (1 / 4 : ℝ) := by ring
  have h₃ : (t + (t - 1 / 2) - 1) / 2 = t - 3 / 4 := by ring
  have h₄ : (t - (t - 1 / 2) - 1) / 2 = -(1 / 4 : ℝ) := by ring
  rw [h₁, h₂, h₃, h₄, gaussian_even]
  rw [show 4 * (α / 2) = 2 * α by ring,
    show (2 * t - 1 / 2) / 2 = t - 1 / 4 by ring,
    show (2 * t - 1 / 2 - 1) / 2 = t - 3 / 4 by ring] at hs
  rw [hs]
  ring

theorem gaussian_diagonal_sum {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α t ^ 2 + gaussian α (t - 1 / 2) ^ 2 =
      gaussian (α / 2) 0 * gaussian (α / 2) (2 * t) := by
  rw [gaussian_duplication hα, gaussian_duplication hα]
  have hp : gaussian (2 * α) (t - 1 / 2 - 1 / 2) = gaussian (2 * α) t := by
    have h := gaussian_one_period (2 * α) (t - 1)
    rw [show t - 1 + 1 = t by ring] at h
    rw [show t - 1 / 2 - 1 / 2 = t - 1 by ring]
    exact h.symm
  rw [hp]
  have hs0 := gaussian_split (half_pos hα) 0
  have hst := gaussian_split (half_pos hα) (2 * t)
  norm_num at hs0
  rw [show 4 * (α / 2) = 2 * α by ring, gaussian_even] at hs0
  rw [show 4 * (α / 2) = 2 * α by ring,
    show 2 * t / 2 = t by ring,
    show (2 * t - 1) / 2 = t - 1 / 2 by ring] at hst
  rw [hs0, hst]
  ring

theorem gaussian_constant_quadratics {α : ℝ} (hα : 0 < α) :
    gaussian α 0 ^ 2 = gaussian (2 * α) 0 ^ 2 + gaussian (2 * α) (1 / 2) ^ 2 ∧
    alternatingGaussian α 0 ^ 2 =
      gaussian (2 * α) 0 ^ 2 - gaussian (2 * α) (1 / 2) ^ 2 ∧
    gaussian α (1 / 2) ^ 2 = 2 * gaussian (2 * α) 0 * gaussian (2 * α) (1 / 2) := by
  have ha := gaussian_duplication hα 0
  have hb := alternatingGaussian_duplication hα 0
  have hc := gaussian_duplication hα (1 / 2)
  norm_num at ha hb hc
  rw [gaussian_even] at ha hb
  constructor
  · nlinarith [ha]
  constructor
  · nlinarith [hb]
  · nlinarith [hc]

/-- Jacobi's quartic identity in the Gaussian normalization of the paper. -/
theorem gaussian_constant_quartic {α : ℝ} (hα : 0 < α) :
    gaussian α 0 ^ 4 = alternatingGaussian α 0 ^ 4 + gaussian α (1 / 2) ^ 4 := by
  obtain ⟨ha, hb, hc⟩ := gaussian_constant_quadratics hα
  calc
    gaussian α 0 ^ 4 = (gaussian α 0 ^ 2) ^ 2 := by ring
    _ = (gaussian (2 * α) 0 ^ 2 + gaussian (2 * α) (1 / 2) ^ 2) ^ 2 := by rw [ha]
    _ = (gaussian (2 * α) 0 ^ 2 - gaussian (2 * α) (1 / 2) ^ 2) ^ 2 +
        (2 * gaussian (2 * α) 0 * gaussian (2 * α) (1 / 2)) ^ 2 := by ring
    _ = alternatingGaussian α 0 ^ 4 + gaussian α (1 / 2) ^ 4 := by rw [← hb, ← hc]; ring

end PaperVerification.ColdSpots
end
end Source_GaussianIdentities
-- END ORIGINAL PaperVerification.GaussianIdentities


-- BEGIN ORIGINAL PaperVerification.GaussianContinuity
section Source_GaussianContinuity

-- original header: module
-- original header: public import PaperVerification.GaussianFourier
-- original header: public import PaperVerification.GaussianIdentities
-- original header: public import Mathlib.Analysis.Normed.Group.FunctionSeries
-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

theorem continuous_fourierGaussian {β : ℝ} (hβ : 0 < β) :
    Continuous (fourierGaussian β) := by
  unfold fourierGaussian
  apply continuous_tsum
    (u := fun n : ℤ ↦ Real.exp (-β * (n : ℝ) ^ 2))
  · intro n
    exact continuous_const.mul (Real.continuous_cos.comp
      ((continuous_const.mul continuous_id).mul continuous_const))
  · exact summable_gaussian_zero hβ
  · intro n t
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)

theorem continuous_gaussian {α : ℝ} (hα : 0 < α) : Continuous (gaussian α) := by
  have hfun : gaussian α = fun t ↦
      Real.sqrt (Real.pi / α) * fourierGaussian (Real.pi ^ 2 / α) t :=
    funext (gaussian_poisson hα)
  rw [hfun]
  exact continuous_const.mul
    (continuous_fourierGaussian (div_pos (sq_pos_of_pos Real.pi_pos) hα))

theorem continuous_alternatingGaussian {α : ℝ} (hα : 0 < α) :
    Continuous (alternatingGaussian α) := by
  have hfun : alternatingGaussian α = fun t ↦
      gaussian (4 * α) (t / 2) - gaussian (4 * α) ((t - 1) / 2) :=
    funext (alternatingGaussian_split hα)
  rw [hfun]
  have h4 := continuous_gaussian (show 0 < 4 * α by positivity)
  exact (h4.comp (continuous_id.div_const 2)).sub
    (h4.comp ((continuous_id.sub continuous_const).div_const 2))

end PaperVerification.ColdSpots
end
end Source_GaussianContinuity
-- END ORIGINAL PaperVerification.GaussianContinuity


-- BEGIN ORIGINAL PaperVerification.GaussianLargeParameter
section Source_GaussianLargeParameter

-- original header: module
-- original header: public import PaperVerification.Gaussian
-- original header: public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
-- original header: public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
-- original header: public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
-- original header: public import Mathlib.Analysis.Complex.ExponentialBounds
-- original header: @[expose] public section
noncomputable section

open scoped BigOperators

namespace PaperVerification.ColdSpots

lemma cosh_quadratic_lower (x : ℝ) : 1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have h := (Real.hasSum_cosh x).summable.sum_le_tsum (Finset.range 2)
    (fun n _ ↦ show 0 ≤ x ^ (2 * n) / (Nat.factorial (2 * n) : ℝ) by
      apply div_nonneg
      · rw [Nat.mul_comm 2 n, pow_mul]
        exact sq_nonneg _
      · positivity)
  rw [(Real.hasSum_cosh x).tsum_eq] at h
  norm_num [Finset.sum_range_succ] at h
  exact h

lemma exp_lt_one_add_two_mul {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    Real.exp s < 1 + 2 * s := by
  have hconv := convexOn_exp.2
  have h := hconv (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (a := 1 - s) (b := s) (sub_nonneg.mpr hs1) hs.le (by ring)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.exp_zero] at h
  nlinarith [Real.exp_one_lt_three]

/-- An elementary estimate covering the large Gaussian parameter regime. -/
lemma cosh_alpha_mul_gt_exp_sq {α u : ℝ} (hα : 4 ≤ α) (hu : 0 < u)
    (hu2 : u ≤ 1 / 2) : Real.exp (α * u ^ 2) < Real.cosh (α * u) := by
  have hα0 : 0 < α := by linarith
  have hx : 0 < α * u := mul_pos hα0 hu
  by_cases hx2 : α * u ≤ 2
  · have hs0 : 0 < (α * u) ^ 2 / 4 := div_pos (sq_pos_of_pos hx) (by norm_num)
    have hs1 : (α * u) ^ 2 / 4 ≤ 1 := by nlinarith
    have he := exp_lt_one_add_two_mul hs0 hs1
    have hq := cosh_quadratic_lower (α * u)
    have harg : α * u ^ 2 ≤ (α * u) ^ 2 / 4 := by
      nlinarith [mul_nonneg (show 0 ≤ α * u ^ 2 by positivity) (sub_nonneg.mpr hα)]
    have he' := Real.exp_le_exp.mpr harg
    nlinarith
  · have hx2' : 2 ≤ α * u := le_of_lt (lt_of_not_ge hx2)
    have he1 : 2 < Real.exp (α * u / 2) :=
      lt_of_lt_of_le Real.exp_one_gt_two (Real.exp_le_exp.mpr (by linarith))
    have harg : α * u ^ 2 ≤ α * u / 2 := by nlinarith
    have hearg := Real.exp_le_exp.mpr harg
    have hex : Real.exp (α * u) = Real.exp (α * u / 2) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [Real.cosh_eq, hex]
    nlinarith [Real.exp_pos (-(α * u))]

lemma cosh_alpha_mul_ge_exp_sq {α u : ℝ} (hα : 4 ≤ α) (hu : 0 ≤ u)
    (hu2 : u ≤ 1 / 2) : Real.exp (α * u ^ 2) ≤ Real.cosh (α * u) := by
  rcases eq_or_lt_of_le hu with rfl | hu
  · simp
  · exact (cosh_alpha_mul_gt_exp_sq hα hu hu2).le

lemma gaussian_pair_centered (α d u : ℝ) :
    Real.exp (-α * (d - u) ^ 2) + Real.exp (-α * (d + u) ^ 2) =
      2 * Real.exp (-α * d ^ 2) * Real.exp (-α * u ^ 2) * Real.cosh (2 * α * d * u) := by
  have h₁ : Real.exp (-α * (d - u) ^ 2) =
      Real.exp (-α * d ^ 2) * Real.exp (-α * u ^ 2) * Real.exp (2 * α * d * u) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h₂ : Real.exp (-α * (d + u) ^ 2) =
      Real.exp (-α * d ^ 2) * Real.exp (-α * u ^ 2) * Real.exp (-(2 * α * d * u)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [h₁, h₂, Real.cosh_eq]
  ring

lemma gaussian_pair_min {α d u : ℝ} (hα : 4 ≤ α) (hd : 1 / 2 ≤ d)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) :
    2 * Real.exp (-α * d ^ 2) ≤
      Real.exp (-α * (d - u) ^ 2) + Real.exp (-α * (d + u) ^ 2) := by
  have hα0 : 0 ≤ α := le_trans (by norm_num) hα
  have harg : α * u ≤ 2 * α * d * u := by
    nlinarith [mul_nonneg (mul_nonneg hα0 hu) (show 0 ≤ 2 * d - 1 by linarith)]
  have hc : Real.cosh (α * u) ≤ Real.cosh (2 * α * d * u) := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg (mul_nonneg hα0 hu), abs_of_nonneg (by positivity)]
    exact harg
  have he := le_trans (cosh_alpha_mul_ge_exp_sq hα hu hu2) hc
  have hex : Real.exp (-α * u ^ 2) * Real.exp (α * u ^ 2) = 1 := by
    rw [← Real.exp_add]
    simp
  have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos (-α * u ^ 2)).le
  rw [hex] at hm
  rw [gaussian_pair_centered]
  nlinarith [mul_nonneg (show 0 ≤ 2 * Real.exp (-α * d ^ 2) by positivity) (sub_nonneg.mpr hm)]

lemma gaussian_pair_min_strict {α d u : ℝ} (hα : 4 ≤ α) (hd : 1 / 2 ≤ d)
    (hu : 0 < u) (hu2 : u ≤ 1 / 2) :
    2 * Real.exp (-α * d ^ 2) <
      Real.exp (-α * (d - u) ^ 2) + Real.exp (-α * (d + u) ^ 2) := by
  have hα0 : 0 ≤ α := le_trans (by norm_num) hα
  have harg : α * u ≤ 2 * α * d * u := by
    nlinarith [mul_nonneg (mul_nonneg hα0 hu.le) (show 0 ≤ 2 * d - 1 by linarith)]
  have hc : Real.cosh (α * u) ≤ Real.cosh (2 * α * d * u) := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg (mul_nonneg hα0 hu.le), abs_of_nonneg (by positivity)]
    exact harg
  have he := lt_of_lt_of_le (cosh_alpha_mul_gt_exp_sq hα hu hu2) hc
  have hex : Real.exp (-α * u ^ 2) * Real.exp (α * u ^ 2) = 1 := by
    rw [← Real.exp_add]
    simp
  have hm := mul_lt_mul_of_pos_left he (Real.exp_pos (-α * u ^ 2))
  rw [hex] at hm
  rw [gaussian_pair_centered]
  nlinarith [mul_pos (show 0 < 2 * Real.exp (-α * d ^ 2) by positivity) (sub_pos.mpr hm)]

lemma gaussian_neg_half_pair_sum {α : ℝ} (hα : 0 < α) (t : ℝ) :
    HasSum (fun n : ℕ ↦ Real.exp (-α * ((n : ℝ) + t) ^ 2) +
      Real.exp (-α * ((n : ℝ) + 1 - t) ^ 2)) (gaussian α t) := by
  have h := (hasSum_gaussian hα (-t)).nat_add_neg_add_one
  rw [gaussian_even] at h
  convert h using 1
  funext n
  simp only [Int.cast_natCast, Int.cast_neg, Int.cast_add, Int.cast_one, sub_neg_eq_add]
  congr 1
  congr 1
  ring

theorem gaussian_min_large_parameter {α t : ℝ} (hα : 4 ≤ α) (ht : 0 ≤ t)
    (ht2 : t ≤ 1 / 2) : gaussian α (1 / 2) ≤ gaussian α t := by
  have hα0 : 0 < α := lt_of_lt_of_le (by norm_num) hα
  have h₀ := gaussian_neg_half_pair_sum hα0 (1 / 2)
  have ht' := gaussian_neg_half_pair_sum hα0 t
  apply hasSum_le _ h₀ ht'
  intro n
  have h := gaussian_pair_min hα
    (show (1 / 2 : ℝ) ≤ (n : ℝ) + 1 / 2 by linarith [Nat.cast_nonneg (α := ℝ) n])
    (show 0 ≤ (1 / 2 : ℝ) - t by linarith) (show (1 / 2 : ℝ) - t ≤ 1 / 2 by linarith)
  rw [show (n : ℝ) + 1 / 2 - (1 / 2 - t) = n + t by ring,
    show (n : ℝ) + 1 / 2 + (1 / 2 - t) = n + 1 - t by ring, two_mul] at h
  simpa only [show (n : ℝ) + 1 - 1 / 2 = n + 1 / 2 by ring] using h

theorem gaussian_min_large_parameter_strict {α t : ℝ} (hα : 4 ≤ α) (ht : 0 ≤ t)
    (ht2 : t < 1 / 2) : gaussian α (1 / 2) < gaussian α t := by
  have hα0 : 0 < α := lt_of_lt_of_le (by norm_num) hα
  have h₀ := gaussian_neg_half_pair_sum hα0 (1 / 2)
  have ht' := gaussian_neg_half_pair_sum hα0 t
  apply hasSum_lt (i := (0 : ℕ)) ?_ ?_ h₀ ht'
  · intro n
    have h := gaussian_pair_min hα
      (show (1 / 2 : ℝ) ≤ (n : ℝ) + 1 / 2 by linarith [Nat.cast_nonneg (α := ℝ) n])
      (show 0 ≤ (1 / 2 : ℝ) - t by linarith) (show (1 / 2 : ℝ) - t ≤ 1 / 2 by linarith)
    rw [show (n : ℝ) + 1 / 2 - (1 / 2 - t) = n + t by ring,
      show (n : ℝ) + 1 / 2 + (1 / 2 - t) = n + 1 - t by ring, two_mul] at h
    simpa only [show (n : ℝ) + 1 - 1 / 2 = n + 1 / 2 by ring] using h
  · have h := gaussian_pair_min_strict hα (show (1 / 2 : ℝ) ≤ 1 / 2 by rfl)
      (show 0 < (1 / 2 : ℝ) - t by linarith) (show (1 / 2 : ℝ) - t ≤ 1 / 2 by linarith)
    rw [show (1 / 2 : ℝ) - (1 / 2 - t) = t by ring,
      show (1 / 2 : ℝ) + (1 / 2 - t) = 1 - t by ring, two_mul] at h
    simpa only [Nat.cast_zero, zero_add, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] using h

end PaperVerification.ColdSpots
end
end Source_GaussianLargeParameter
-- END ORIGINAL PaperVerification.GaussianLargeParameter


-- BEGIN ORIGINAL PaperVerification.FourierDominance
section Source_FourierDominance

-- original header: module
-- original header: public import PaperVerification.GaussianFourier
-- original header: public import Mathlib.Analysis.Complex.ExponentialBounds
-- original header: public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
-- original header: public import Mathlib.Data.Nat.Basic
-- original header: @[expose] public section
noncomputable section

open scoped BigOperators

namespace PaperVerification.ColdSpots

lemma abs_sin_nat_mul_bound (n : ℕ) (x : ℝ) :
    |Real.sin ((n : ℝ) * x)| ≤ n * |Real.sin x| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add_one, add_mul, one_mul, Real.sin_add]
    calc
      |Real.sin (n * x) * Real.cos x + Real.cos (n * x) * Real.sin x|
          ≤ |Real.sin (n * x) * Real.cos x| + |Real.cos (n * x) * Real.sin x| := abs_add_le _ _
      _ = |Real.sin (n * x)| * |Real.cos x| + |Real.cos (n * x)| * |Real.sin x| := by
          rw [abs_mul, abs_mul]
      _ ≤ |Real.sin (n * x)| + |Real.sin x| := add_le_add
          (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
          (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _))
      _ ≤ n * |Real.sin x| + |Real.sin x| := add_le_add ih le_rfl
      _ = (n + 1) * |Real.sin x| := by ring

lemma one_sub_cos_nat_mul_bound (n : ℕ) (x : ℝ) :
    1 - Real.cos ((n : ℝ) * x) ≤ (n : ℝ) ^ 2 * (1 - Real.cos x) := by
  have hs := abs_sin_nat_mul_bound n (x / 2)
  have hs2 : Real.sin ((n : ℝ) * (x / 2)) ^ 2 ≤
      (n : ℝ) ^ 2 * Real.sin (x / 2) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))).mpr hs
    simpa only [sq_abs, mul_pow] using h
  rw [Real.sin_sq_eq_half_sub, Real.sin_sq_eq_half_sub] at hs2
  rw [show 2 * ((n : ℝ) * (x / 2)) = n * x by ring,
    show 2 * (x / 2) = x by ring] at hs2
  nlinarith

lemma cosine_coefficient_lower (n : ℕ) (x : ℝ) :
    -(n : ℝ) ^ 2 * (1 + Real.cos x) ≤
      Real.cos ((n : ℝ) * x) - Real.cos ((n : ℝ) * Real.pi) := by
  have h := one_sub_cos_nat_mul_bound n (x - Real.pi)
  rw [Real.cos_sub_pi] at h
  have hshift : Real.cos ((n : ℝ) * x) =
      (-1 : ℝ) ^ n * Real.cos ((n : ℝ) * (x - Real.pi)) := by
    convert Real.cos_add_nat_mul_pi ((n : ℝ) * (x - Real.pi)) n using 1 <;> congr 1 <;> ring
  rw [hshift, Real.cos_nat_mul_pi]
  have hc : (-1 : ℝ) ^ n ≤ 1 := by
    calc (-1 : ℝ) ^ n ≤ |(-1 : ℝ) ^ n| := le_abs_self _
      _ = 1 := by simp
  have hp := mul_nonneg (sub_nonneg.mpr hc)
    (sub_nonneg.mpr (Real.cos_le_one ((n : ℝ) * (x - Real.pi))))
  nlinarith

lemma nat_sq_le_four_pow (n : ℕ) : (n : ℝ) ^ 2 ≤ (4 : ℝ) ^ n := by
  have h := Nat.two_mul_sq_add_one_le_two_pow_two_mul n
  have h' : 2 * n ^ 2 + 1 ≤ 4 ^ n := by
    simpa only [pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num] using h
  exact_mod_cast (show n ^ 2 ≤ 4 ^ n by omega)

lemma gaussian_tail_ratio {β : ℝ} (hβ : 2 ≤ β) :
    0 ≤ 4 * Real.exp (-(3 * β / 2)) ∧ 4 * Real.exp (-(3 * β / 2)) ≤ 1 / 2 := by
  constructor
  · positivity
  have he3 : 8 < Real.exp 3 := by
    have he := Real.exp_one_gt_two
    have hpower : Real.exp 3 = Real.exp 1 ^ 3 := by
      simpa using Real.exp_nat_mul (1 : ℝ) 3
    rw [hpower]
    nlinarith [sq_nonneg (Real.exp 1 - 2)]
  have he : 8 < Real.exp (3 * β / 2) :=
    he3.trans_le (Real.exp_le_exp.mpr (by linarith))
  have hc : Real.exp (3 * β / 2) * Real.exp (-(3 * β / 2)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hp := mul_pos (sub_pos.mpr he) (Real.exp_pos (-(3 * β / 2)))
  nlinarith

lemma gaussian_frequency_tail_term {β : ℝ} (hβ : 2 ≤ β) {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) ^ 2 * Real.exp (-β * (n : ℝ) ^ 2) ≤
      Real.exp (-β) * (1 / 2 : ℝ) ^ n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hβ0 : 0 ≤ β := by linarith
  have hsq : 1 + 3 * (n : ℝ) / 2 ≤ (n : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) - 2 by linarith)
      (show 0 ≤ (n : ℝ) + 1 / 2 by positivity)]
  have hex : -β * (n : ℝ) ^ 2 ≤ -β - (3 * β / 2) * n := by
    nlinarith [mul_nonneg hβ0 (sub_nonneg.mpr hsq)]
  have hfactor : Real.exp (-β - (3 * β / 2) * n) =
      Real.exp (-β) * Real.exp (-(3 * β / 2)) ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  calc
    (n : ℝ) ^ 2 * Real.exp (-β * (n : ℝ) ^ 2)
        ≤ (4 : ℝ) ^ n * Real.exp (-β - (3 * β / 2) * n) :=
      mul_le_mul (nat_sq_le_four_pow n) (Real.exp_le_exp.mpr hex)
        (Real.exp_pos _).le (by positivity)
    _ = Real.exp (-β) * (4 * Real.exp (-(3 * β / 2))) ^ n := by
      rw [hfactor, mul_pow]
      ring
    _ ≤ Real.exp (-β) * (1 / 2 : ℝ) ^ n :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (gaussian_tail_ratio hβ).1 (gaussian_tail_ratio hβ).2 n)
        (Real.exp_pos _).le

theorem gaussian_frequency_tail {β : ℝ} (hβ : 2 ≤ β) :
    Summable (fun n : ℕ ↦ ((n : ℝ) + 2) ^ 2 * Real.exp (-β * ((n : ℝ) + 2) ^ 2)) ∧
    (∑' n : ℕ, ((n : ℝ) + 2) ^ 2 * Real.exp (-β * ((n : ℝ) + 2) ^ 2)) ≤
      Real.exp (-β) / 2 := by
  let g : ℕ → ℝ := fun n ↦ (Real.exp (-β) / 4) * (1 / 2 : ℝ) ^ n
  have hg : HasSum g (Real.exp (-β) / 2) := by
    change HasSum (fun n : ℕ ↦ (Real.exp (-β) / 4) * (1 / 2 : ℝ) ^ n)
      (Real.exp (-β) / 2)
    convert hasSum_geometric_two.mul_left (Real.exp (-β) / 4) using 1 <;> ring
  have hle (n : ℕ) : ((n : ℝ) + 2) ^ 2 * Real.exp (-β * ((n : ℝ) + 2) ^ 2) ≤ g n := by
    have h := gaussian_frequency_tail_term hβ (n := n + 2) (by omega)
    convert h using 1
    · norm_num
    · dsimp [g]
      rw [pow_add]
      norm_num
      ring
  have hf : Summable (fun n : ℕ ↦ ((n : ℝ) + 2) ^ 2 *
      Real.exp (-β * ((n : ℝ) + 2) ^ 2)) :=
    hg.summable.of_nonneg_of_le (fun n ↦ by positivity) hle
  exact ⟨hf, (hf.tsum_le_tsum hle hg.summable).trans_eq hg.tsum_eq⟩

end PaperVerification.ColdSpots
end
end Source_FourierDominance
-- END ORIGINAL PaperVerification.FourierDominance


-- BEGIN ORIGINAL PaperVerification.GaussianSmallParameter
section Source_GaussianSmallParameter

-- original header: module
-- original header: public import PaperVerification.FourierDominance
-- original header: public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
-- original header: public import Mathlib.Analysis.Real.Pi.Bounds
-- original header: @[expose] public section
noncomputable section

open scoped BigOperators

namespace PaperVerification.ColdSpots

lemma summable_nat_fourierGaussian {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    Summable (fun n : ℕ ↦ Real.exp (-β * ((n : ℝ) + 1) ^ 2) *
      Real.cos (2 * Real.pi * t * ((n : ℝ) + 1))) := by
  have h := (summable_fourierGaussian hβ t).comp_injective
    (i := fun n : ℕ ↦ (n : ℤ) + 1) (by
      intro a b h
      change (a : ℤ) + 1 = (b : ℤ) + 1 at h
      exact_mod_cast (add_right_cancel h))
  simpa only [Function.comp_def, Int.cast_add, Int.cast_natCast, Int.cast_one] using h

lemma fourierGaussian_nat {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    fourierGaussian β t = 1 + 2 * ∑' n : ℕ,
      Real.exp (-β * ((n : ℝ) + 1) ^ 2) *
        Real.cos (2 * Real.pi * t * ((n : ℝ) + 1)) := by
  let f : ℤ → ℝ := fun n ↦ Real.exp (-β * (n : ℝ) ^ 2) *
    Real.cos (2 * Real.pi * t * n)
  have heven (n : ℤ) : f (-n) = f n := by
    simp only [f, Int.cast_neg, neg_sq, mul_neg, Real.cos_neg]
  have hp : Summable (fun n : ℕ ↦ f ((n : ℤ) + 1)) := by
    simpa only [f, Int.cast_add, Int.cast_natCast, Int.cast_one] using
      summable_nat_fourierGaussian hβ t
  have hn : Summable (fun n : ℕ ↦ f (-((n : ℤ) + 1))) :=
    hp.congr (fun n ↦ (heven ((n : ℤ) + 1)).symm)
  have h := tsum_of_add_one_of_neg_add_one hp hn
  simp only [heven] at h
  change fourierGaussian β t = _ at h
  have hzero : f 0 = 1 := by simp [f]
  rw [hzero] at h
  simp only [f, Int.cast_add, Int.cast_natCast, Int.cast_one] at h
  rw [h]
  ring

/-- The first Fourier harmonic dominates the entire remaining series, uniformly in `t`. -/
theorem fourierGaussian_min_gap {β : ℝ} (hβ : 2 ≤ β) (t : ℝ) :
    Real.exp (-β) * (1 + Real.cos (2 * Real.pi * t)) ≤
      fourierGaussian β t - fourierGaussian β (1 / 2) := by
  have hβ0 : 0 < β := by linarith
  let D : ℝ := 1 + Real.cos (2 * Real.pi * t)
  let g : ℝ → ℕ → ℝ := fun u n ↦ Real.exp (-β * ((n : ℝ) + 1) ^ 2) *
    Real.cos (2 * Real.pi * u * ((n : ℝ) + 1))
  let c : ℕ → ℝ := fun n ↦ ((n : ℝ) + 2) ^ 2 *
    Real.exp (-β * ((n : ℝ) + 2) ^ 2)
  have hD : 0 ≤ D := by dsimp [D]; linarith [Real.neg_one_le_cos (2 * Real.pi * t)]
  have hgt : Summable (g t) := summable_nat_fourierGaussian hβ0 t
  have hgh : Summable (g (1 / 2)) := summable_nat_fourierGaussian hβ0 (1 / 2)
  have hdiff : Summable (fun n ↦ g t n - g (1 / 2) n) := hgt.sub hgh
  have htail : Summable (fun n : ℕ ↦ g t (n + 1) - g (1 / 2) (n + 1)) :=
    hdiff.comp_injective (i := fun n : ℕ ↦ n + 1) (by
      intro a b h
      change a + 1 = b + 1 at h
      exact Nat.add_right_cancel h)
  have hc : Summable c := (gaussian_frequency_tail hβ).1
  have hcb : (∑' n, c n) ≤ Real.exp (-β) / 2 := (gaussian_frequency_tail hβ).2
  have hterm (n : ℕ) : -D * c n ≤ g t (n + 1) - g (1 / 2) (n + 1) := by
    have h := mul_le_mul_of_nonneg_left
      (cosine_coefficient_lower (n + 2) (2 * Real.pi * t))
      (Real.exp_pos (-β * ((n : ℝ) + 2) ^ 2)).le
    have ha : ((n : ℝ) + 2) * (2 * Real.pi * t) =
        2 * Real.pi * t * ((n : ℝ) + 2) := by ring
    have hb : ((n : ℝ) + 2) * Real.pi =
        2 * Real.pi * (1 / 2) * ((n : ℝ) + 2) := by ring
    simp only [Nat.cast_add, Nat.cast_ofNat] at h
    rw [ha, hb] at h
    convert h using 1 <;> (try dsimp only [D, c, g]) <;>
      (try simp only [Nat.cast_add_one]) <;> ring
  have hsum := (hc.mul_left (-D)).tsum_le_tsum hterm htail
  rw [tsum_mul_left] at hsum
  have hbound : -D * (Real.exp (-β) / 2) ≤ -D * ∑' n, c n :=
    mul_le_mul_of_nonpos_left hcb (neg_nonpos.mpr hD)
  have hzero : g t 0 - g (1 / 2) 0 = Real.exp (-β) * D := by
    norm_num [g, D]
    rw [show 2 * Real.pi * (1 / 2) = Real.pi by ring, Real.cos_pi]
    ring
  have hsplit := hdiff.tsum_eq_zero_add
  rw [hzero, hgt.tsum_sub hgh] at hsplit
  rw [fourierGaussian_nat hβ0 t, fourierGaussian_nat hβ0 (1 / 2)]
  change Real.exp (-β) * D ≤ (1 + 2 * ∑' n, g t n) -
    (1 + 2 * ∑' n, g (1 / 2) n)
  linarith

theorem fourierGaussian_min {β : ℝ} (hβ : 2 ≤ β) (t : ℝ) :
    fourierGaussian β (1 / 2) ≤ fourierGaussian β t := by
  have hD : 0 ≤ 1 + Real.cos (2 * Real.pi * t) := by
    linarith [Real.neg_one_le_cos (2 * Real.pi * t)]
  have h := fourierGaussian_min_gap hβ t
  nlinarith [Real.exp_pos (-β)]

theorem fourierGaussian_min_strict {β t : ℝ} (hβ : 2 ≤ β) (ht : 0 ≤ t)
    (ht2 : t < 1 / 2) : fourierGaussian β (1 / 2) < fourierGaussian β t := by
  have hx : 2 * Real.pi * t ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨by positivity, by nlinarith [Real.pi_pos]⟩
  have hxlt : 2 * Real.pi * t < Real.pi := by nlinarith [Real.pi_pos]
  have hc := Real.strictAntiOn_cos hx ⟨Real.pi_pos.le, le_rfl⟩ hxlt
  rw [Real.cos_pi] at hc
  have hpos : 0 < Real.exp (-β) * (1 + Real.cos (2 * Real.pi * t)) :=
    mul_pos (Real.exp_pos _) (by linarith)
  have h := fourierGaussian_min_gap hβ t
  linarith

lemma gaussian_reciprocal_parameter_ge_two {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 4) :
    2 ≤ Real.pi ^ 2 / α := by
  apply (le_div_iff₀ hα).mpr
  nlinarith [Real.pi_gt_three]

theorem gaussian_min_small_parameter {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 4)
    (t : ℝ) : gaussian α (1 / 2) ≤ gaussian α t := by
  rw [gaussian_poisson hα (1 / 2), gaussian_poisson hα t]
  exact mul_le_mul_of_nonneg_left
    (fourierGaussian_min (gaussian_reciprocal_parameter_ge_two hα hα4) t)
    (Real.sqrt_nonneg _)

theorem gaussian_min_small_parameter_strict {α t : ℝ} (hα : 0 < α) (hα4 : α ≤ 4)
    (ht : 0 ≤ t) (ht2 : t < 1 / 2) : gaussian α (1 / 2) < gaussian α t := by
  rw [gaussian_poisson hα (1 / 2), gaussian_poisson hα t]
  exact mul_lt_mul_of_pos_left
    (fourierGaussian_min_strict (gaussian_reciprocal_parameter_ge_two hα hα4) ht ht2)
    (Real.sqrt_pos.mpr (div_pos Real.pi_pos hα))

end PaperVerification.ColdSpots
end
end Source_GaussianSmallParameter
-- END ORIGINAL PaperVerification.GaussianSmallParameter


-- BEGIN ORIGINAL PaperVerification.GaussianExtrema
section Source_GaussianExtrema

-- original header: module
-- original header: public import PaperVerification.GaussianSmallParameter
-- original header: public import PaperVerification.GaussianLargeParameter
-- original header: public import Mathlib.Algebra.Order.Round
-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

theorem gaussian_min_on_half_interval {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t)
    (ht2 : t ≤ 1 / 2) : gaussian α (1 / 2) ≤ gaussian α t := by
  rcases le_total α 4 with hsmall | hlarge
  · exact gaussian_min_small_parameter hα hsmall t
  · exact gaussian_min_large_parameter hlarge ht ht2

theorem gaussian_min_on_half_interval_strict {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t)
    (ht2 : t < 1 / 2) : gaussian α (1 / 2) < gaussian α t := by
  rcases le_total α 4 with hsmall | hlarge
  · exact gaussian_min_small_parameter_strict hα hsmall ht ht2
  · exact gaussian_min_large_parameter_strict hlarge ht ht2

lemma gaussian_abs (α t : ℝ) : gaussian α |t| = gaussian α t := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht), gaussian_even]

lemma gaussian_fold (α t : ℝ) :
    gaussian α t = gaussian α |t - (round t : ℝ)| := by
  rw [gaussian_abs]
  have h := gaussian_int_period α (t - (round t : ℝ)) (round t)
  simpa only [sub_add_cancel] using h

/-- Global minimum of the actual integer Gaussian series, for every positive parameter. -/
theorem gaussian_minimum {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α (1 / 2) ≤ gaussian α t := by
  rw [gaussian_fold α t]
  exact gaussian_min_on_half_interval hα (abs_nonneg _) (abs_sub_round t)

/-- Equality in the Gaussian minimum occurs exactly at nonintegral half integers. -/
theorem gaussian_minimum_iff {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α t = gaussian α (1 / 2) ↔ ∃ z : ℤ, t = (z : ℝ) + 1 / 2 := by
  constructor
  · intro heq
    have hfold : |t - (round t : ℝ)| = 1 / 2 := by
      apply le_antisymm (abs_sub_round t)
      by_contra h
      have hlt := gaussian_min_on_half_interval_strict hα (abs_nonneg (t - (round t : ℝ)))
        (lt_of_not_ge h)
      rw [← gaussian_fold, heq] at hlt
      exact (lt_irrefl _) hlt
    have hround := sub_half_lt_round t
    by_cases hd : 0 ≤ t - (round t : ℝ)
    · rw [abs_of_nonneg hd] at hfold
      linarith
    · rw [abs_of_neg (lt_of_not_ge hd)] at hfold
      refine ⟨round t - 1, ?_⟩
      push_cast
      linarith
  · rintro ⟨z, rfl⟩
    rw [add_comm, gaussian_int_period]

theorem gaussian_half_lt_zero {α : ℝ} (hα : 0 < α) :
    gaussian α (1 / 2) < gaussian α 0 :=
  gaussian_min_on_half_interval_strict hα le_rfl (by norm_num)

end PaperVerification.ColdSpots
end
end Source_GaussianExtrema
-- END ORIGINAL PaperVerification.GaussianExtrema


-- BEGIN ORIGINAL PaperVerification.GaussianAlternating
section Source_GaussianAlternating

-- original header: module
-- original header: public import PaperVerification.GaussianContinuity
-- original header: public import PaperVerification.GaussianExtrema
-- original header: public import Mathlib.Topology.Order.IntermediateValue
-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

theorem alternatingGaussian_zero_pos {α : ℝ} (hα : 0 < α) :
    0 < alternatingGaussian α 0 := by
  have hs := alternatingGaussian_split hα 0
  norm_num at hs
  rw [gaussian_even] at hs
  rw [hs]
  exact sub_pos.mpr (gaussian_half_lt_zero (show 0 < 4 * α by positivity))

lemma alternatingGaussian_sq_pos {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t)
    (ht2 : t < 1 / 2) : 0 < alternatingGaussian α t ^ 2 := by
  have h2 : 0 < 2 * α := by positivity
  have hu := gaussian_min_on_half_interval_strict h2 ht ht2
  have hw := gaussian_le_zero h2 (t - 1 / 2)
  have hP := gaussian_pos h2 0
  have hQ := gaussian_pos h2 (1 / 2)
  have hmul := mul_pos hP (sub_pos.mpr hu)
  have hmul' := mul_nonneg hQ.le (sub_nonneg.mpr hw)
  rw [alternatingGaussian_duplication hα]
  nlinarith

theorem alternatingGaussian_pos {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t)
    (ht2 : t < 1 / 2) : 0 < alternatingGaussian α t := by
  by_contra h
  have htB : alternatingGaussian α t ≤ 0 := le_of_not_gt h
  have hzero := alternatingGaussian_zero_pos hα
  obtain ⟨s, hs, hsz⟩ := intermediate_value_Icc' ht
    (continuous_alternatingGaussian hα).continuousOn ⟨htB, hzero.le⟩
  have hsq := alternatingGaussian_sq_pos hα hs.1 (lt_of_le_of_lt hs.2 ht2)
  rw [hsz] at hsq
  norm_num at hsq

theorem alternatingGaussian_nonneg {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t)
    (ht2 : t ≤ 1 / 2) : 0 ≤ alternatingGaussian α t := by
  rcases eq_or_lt_of_le ht2 with rfl | hlt
  · rw [alternatingGaussian_half]
  · exact (alternatingGaussian_pos hα ht hlt).le

theorem alternatingGaussian_zero_iff_on_half_interval {α t : ℝ} (hα : 0 < α)
    (ht : 0 ≤ t) (ht2 : t ≤ 1 / 2) : alternatingGaussian α t = 0 ↔ t = 1 / 2 := by
  constructor
  · intro hz
    by_contra hne
    have hpos := alternatingGaussian_pos hα ht (lt_of_le_of_ne ht2 hne)
    rw [hz] at hpos
    exact (lt_irrefl _) hpos
  · rintro rfl
    exact alternatingGaussian_half α

lemma alternatingGaussian_int_period (α t : ℝ) (k : ℤ) :
    alternatingGaussian α (t + k) = paritySign k * alternatingGaussian α t := by
  unfold alternatingGaussian
  rw [← (Equiv.addRight k).tsum_eq, ← tsum_mul_left]
  apply tsum_congr
  intro z
  simp only [Equiv.coe_addRight, paritySign_add, Int.cast_add]
  rw [show (z : ℝ) + k - (t + k) = (z : ℝ) - t by ring]
  ring

lemma abs_paritySign (k : ℤ) : |paritySign k| = 1 := by
  simpa only [Real.norm_eq_abs] using norm_paritySign k

lemma alternatingGaussian_abs_period (α t : ℝ) (k : ℤ) :
    |alternatingGaussian α (t + k)| = |alternatingGaussian α t| := by
  rw [alternatingGaussian_int_period, abs_mul, abs_paritySign, one_mul]

lemma alternatingGaussian_abs_argument (α t : ℝ) :
    alternatingGaussian α |t| = alternatingGaussian α t := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht), alternatingGaussian_even]

lemma alternatingGaussian_fold {α : ℝ} (hα : 0 < α) (t : ℝ) :
    |alternatingGaussian α t| = alternatingGaussian α |t - (round t : ℝ)| := by
  have h := alternatingGaussian_abs_period α (t - (round t : ℝ)) (round t)
  rw [sub_add_cancel] at h
  rw [h, ← alternatingGaussian_abs_argument]
  exact abs_of_nonneg (alternatingGaussian_nonneg hα (abs_nonneg _) (abs_sub_round t))

lemma gaussian_halfshift_abs (α t : ℝ) :
    gaussian α (|t| - 1 / 2) = gaussian α (t - 1 / 2) := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht), show -t - 1 / 2 = -(t + 1 / 2) by ring,
      gaussian_even]
    have h := gaussian_one_period α (t - 1 / 2)
    simpa only [show t - 1 / 2 + 1 = t + 1 / 2 by ring] using h

lemma gaussian_halfshift_fold (α t : ℝ) :
    gaussian α (t - 1 / 2) = gaussian α (|t - (round t : ℝ)| - 1 / 2) := by
  rw [gaussian_halfshift_abs]
  have h := gaussian_int_period α (t - (round t : ℝ) - 1 / 2) (round t)
  simpa only [show t - (round t : ℝ) - 1 / 2 + (round t : ℝ) = t - 1 / 2 by ring] using h

lemma alternatingGaussian_abs_halfshift_abs (α t : ℝ) :
    |alternatingGaussian α (|t| - 1 / 2)| = |alternatingGaussian α (t - 1 / 2)| := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht), show -t - 1 / 2 = -(t + 1 / 2) by ring,
      alternatingGaussian_even]
    have h := alternatingGaussian_antiperiod α (t - 1 / 2)
    rw [show t - 1 / 2 + 1 = t + 1 / 2 by ring] at h
    rw [h, abs_neg]

lemma alternatingGaussian_halfshift_fold {α : ℝ} (hα : 0 < α) (t : ℝ) :
    |alternatingGaussian α (t - 1 / 2)| =
      alternatingGaussian α (|t - (round t : ℝ)| - 1 / 2) := by
  have h := alternatingGaussian_abs_period α (t - (round t : ℝ) - 1 / 2) (round t)
  rw [show t - (round t : ℝ) - 1 / 2 + (round t : ℝ) = t - 1 / 2 by ring] at h
  rw [h, ← alternatingGaussian_abs_halfshift_abs]
  apply abs_of_nonneg
  rw [show |t - (round t : ℝ)| - 1 / 2 = -(1 / 2 - |t - (round t : ℝ)|) by ring,
    alternatingGaussian_even]
  apply alternatingGaussian_nonneg hα
  · linarith [abs_sub_round t]
  · linarith [abs_nonneg (t - (round t : ℝ))]

end PaperVerification.ColdSpots
end
end Source_GaussianAlternating
-- END ORIGINAL PaperVerification.GaussianAlternating


-- BEGIN ORIGINAL PaperVerification.ThetaRelations
section Source_ThetaRelations

-- original header: module
-- original header: public import PaperVerification.GaussianIdentities
-- original header: public import PaperVerification.GaussianExtrema
-- original header: public import Mathlib.Tactic.IntervalCases
-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

lemma gaussian_sub_one (α t : ℝ) : gaussian α (t - 1) = gaussian α t := by
  have h := gaussian_int_period α (t - 1) 1
  simpa only [Int.cast_one, sub_add_cancel] using h.symm

lemma gaussian_four_duplications {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α t ^ 2 =
      gaussian (2 * α) 0 * gaussian (2 * α) t +
        gaussian (2 * α) (1 / 2) * gaussian (2 * α) (t - 1 / 2) ∧
    alternatingGaussian α t ^ 2 =
      gaussian (2 * α) 0 * gaussian (2 * α) t -
        gaussian (2 * α) (1 / 2) * gaussian (2 * α) (t - 1 / 2) ∧
    gaussian α (t - 1 / 2) ^ 2 =
      gaussian (2 * α) 0 * gaussian (2 * α) (t - 1 / 2) +
        gaussian (2 * α) (1 / 2) * gaussian (2 * α) t ∧
    alternatingGaussian α (t - 1 / 2) ^ 2 =
      gaussian (2 * α) 0 * gaussian (2 * α) (t - 1 / 2) -
        gaussian (2 * α) (1 / 2) * gaussian (2 * α) t := by
  refine ⟨gaussian_duplication hα t, alternatingGaussian_duplication hα t, ?_, ?_⟩
  · simpa only [show t - 1 / 2 - 1 / 2 = t - 1 by ring, gaussian_sub_one] using
      gaussian_duplication hα (t - 1 / 2)
  · simpa only [show t - 1 / 2 - 1 / 2 = t - 1 by ring, gaussian_sub_one] using
      alternatingGaussian_duplication hα (t - 1 / 2)

/-- Both quadratic relations in Equation (2), with the actual series as their arguments. -/
theorem gaussian_quadratic_relations {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α 0 ^ 2 * gaussian α t ^ 2 =
      alternatingGaussian α 0 ^ 2 * alternatingGaussian α t ^ 2 +
        gaussian α (1 / 2) ^ 2 * gaussian α (t - 1 / 2) ^ 2 ∧
    gaussian α 0 ^ 2 * gaussian α (t - 1 / 2) ^ 2 =
      gaussian α (1 / 2) ^ 2 * gaussian α t ^ 2 +
        alternatingGaussian α 0 ^ 2 * alternatingGaussian α (t - 1 / 2) ^ 2 := by
  obtain ⟨ha, hb, hc⟩ := gaussian_constant_quadratics hα
  obtain ⟨hA, hB, hC, hD⟩ := gaussian_four_duplications hα t
  constructor <;> simp only [ha, hb, hc, hA, hB, hC, hD] <;> ring

theorem gaussian_quadratic_relation_reverse {α : ℝ} (hα : 0 < α) (t : ℝ) :
    alternatingGaussian α 0 ^ 2 * gaussian α t ^ 2 =
      gaussian α 0 ^ 2 * alternatingGaussian α t ^ 2 +
        gaussian α (1 / 2) ^ 2 * alternatingGaussian α (t - 1 / 2) ^ 2 := by
  obtain ⟨ha, hb, hc⟩ := gaussian_constant_quadratics hα
  obtain ⟨hA, hB, hC, hD⟩ := gaussian_four_duplications hα t
  simp only [ha, hb, hc, hA, hB, hC, hD]
  ring

def thetaScale (α t : ℝ) : ℝ := gaussian α t ^ 4 - alternatingGaussian α t ^ 4

lemma fourth_difference_algebra (A B P Q U W : ℝ)
    (hA : A ^ 2 = P * U + Q * W) (hB : B ^ 2 = P * U - Q * W) :
    A ^ 4 - B ^ 4 = 4 * P * Q * U * W := by
  calc A ^ 4 - B ^ 4 = (A ^ 2) ^ 2 - (B ^ 2) ^ 2 := by ring
    _ = 4 * P * Q * U * W := by rw [hA, hB]; ring

lemma thetaScale_product {α : ℝ} (hα : 0 < α) (t : ℝ) :
    thetaScale α t = 4 * gaussian (2 * α) 0 * gaussian (2 * α) (1 / 2) *
      gaussian (2 * α) t * gaussian (2 * α) (t - 1 / 2) :=
  fourth_difference_algebra _ _ _ _ _ _ (gaussian_duplication hα t)
    (alternatingGaussian_duplication hα t)

lemma thetaScale_shift {α : ℝ} (hα : 0 < α) (t : ℝ) :
    thetaScale α (t - 1 / 2) = thetaScale α t := by
  rw [thetaScale_product hα, thetaScale_product hα]
  rw [show t - 1 / 2 - 1 / 2 = t - 1 by ring, gaussian_sub_one]
  ring

theorem thetaScale_pos {α : ℝ} (hα : 0 < α) (t : ℝ) : 0 < thetaScale α t := by
  rw [thetaScale_product hα]
  have h2 : 0 < 2 * α := by positivity
  exact mul_pos (mul_pos (mul_pos (mul_pos (by norm_num)
    (gaussian_pos h2 0)) (gaussian_pos h2 (1 / 2)))
    (gaussian_pos h2 t)) (gaussian_pos h2 (t - 1 / 2))

/-- First quartic identity in Equation (4). -/
theorem thetaScale_identity {α : ℝ} (hα : 0 < α) (t : ℝ) :
    thetaScale α t = gaussian α (1 / 2) ^ 3 * gaussian α (2 * t - 1 / 2) := by
  have h2 : 0 < 2 * α := by positivity
  have hc := (gaussian_constant_quadratics hα).2.2
  have hc1 := gaussian_half_eq_twice_quarter hα
  calc
    thetaScale α t = (2 * gaussian α (1 / 2) ^ 2) *
        (gaussian (2 * α) t * gaussian (2 * α) (t - 1 / 2)) := by
      rw [thetaScale_product hα, hc]
      ring
    _ = (2 * gaussian α (1 / 2) ^ 2) *
        (gaussian (4 * α) (1 / 4) * gaussian α (2 * t - 1 / 2)) := by
      rw [gaussian_shift_product h2]
      rw [show 2 * (2 * α) = 4 * α by ring, show (2 * α) / 2 = α by ring]
    _ = gaussian α (1 / 2) ^ 3 * gaussian α (2 * t - 1 / 2) := by
      rw [hc1]
      ring

/-- Second quartic identity in Equation (4). -/
theorem gaussian_quartic_diagonal {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α t ^ 4 + alternatingGaussian α (t - 1 / 2) ^ 4 =
      gaussian α 0 ^ 3 * gaussian α (2 * t) := by
  obtain ⟨hA, hB, hC, hD⟩ := gaussian_four_duplications hα t
  have ha := (gaussian_constant_quadratics hα).1
  have hd : gaussian (2 * α) t ^ 2 + gaussian (2 * α) (t - 1 / 2) ^ 2 =
      gaussian α 0 * gaussian α (2 * t) := by
    simpa only [show (2 * α) / 2 = α by ring] using
      gaussian_diagonal_sum (show 0 < 2 * α by positivity) t
  calc
    gaussian α t ^ 4 + alternatingGaussian α (t - 1 / 2) ^ 4 =
        (gaussian α t ^ 2) ^ 2 + (alternatingGaussian α (t - 1 / 2) ^ 2) ^ 2 := by ring
    _ = (gaussian (2 * α) 0 ^ 2 + gaussian (2 * α) (1 / 2) ^ 2) *
        (gaussian (2 * α) t ^ 2 + gaussian (2 * α) (t - 1 / 2) ^ 2) := by
      rw [hA, hD]
      ring
    _ = gaussian α 0 ^ 3 * gaussian α (2 * t) := by rw [← ha, hd]; ring

theorem gaussian_shift_product_min {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α 0 * gaussian α (1 / 2) ≤ gaussian α t * gaussian α (t - 1 / 2) := by
  have hzero := gaussian_shift_product hα 0
  simp only [zero_sub, zero_mul, mul_zero, gaussian_even] at hzero
  rw [gaussian_shift_product hα, hzero]
  exact mul_le_mul_of_nonneg_left (gaussian_minimum (half_pos hα) (2 * t - 1 / 2))
    (gaussian_pos (show 0 < 2 * α by positivity) (1 / 4)).le

theorem gaussian_shift_product_min_iff {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α t * gaussian α (t - 1 / 2) = gaussian α 0 * gaussian α (1 / 2) ↔
      ∃ z : ℤ, 2 * t = (z : ℝ) := by
  have hzero := gaussian_shift_product hα 0
  simp only [zero_sub, zero_mul, mul_zero, gaussian_even] at hzero
  rw [gaussian_shift_product hα, hzero,
    mul_right_inj' (gaussian_pos (show 0 < 2 * α by positivity) (1 / 4)).ne',
    gaussian_minimum_iff (half_pos hα)]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z + 1, ?_⟩
    push_cast
    linarith
  · rintro ⟨z, hz⟩
    refine ⟨z - 1, ?_⟩
    push_cast
    linarith

def thetaDiagonal (α t : ℝ) : ℝ :=
  (1 / 2) * (gaussian α t ^ 8 + gaussian α (t - 1 / 2) ^ 8 -
    alternatingGaussian α t ^ 8 - alternatingGaussian α (t - 1 / 2) ^ 8)

theorem thetaDiagonal_scale {α : ℝ} (hα : 0 < α) (t : ℝ) :
    thetaDiagonal α t = thetaScale α t *
      (gaussian α t ^ 4 + alternatingGaussian α (t - 1 / 2) ^ 4) := by
  have hB : alternatingGaussian α t ^ 4 = gaussian α t ^ 4 - thetaScale α t := by
    unfold thetaScale
    ring
  have hC : gaussian α (t - 1 / 2) ^ 4 =
      alternatingGaussian α (t - 1 / 2) ^ 4 + thetaScale α t := by
    rw [← thetaScale_shift hα t]
    unfold thetaScale
    ring
  calc
    thetaDiagonal α t = (1 / 2) * ((gaussian α t ^ 4) ^ 2 +
        (gaussian α (t - 1 / 2) ^ 4) ^ 2 - (alternatingGaussian α t ^ 4) ^ 2 -
        (alternatingGaussian α (t - 1 / 2) ^ 4) ^ 2) := by unfold thetaDiagonal; ring
    _ = _ := by rw [hB, hC]; ring

theorem thetaDiagonal_identity {α : ℝ} (hα : 0 < α) (t : ℝ) :
    thetaDiagonal α t = (gaussian α 0 * gaussian α (1 / 2)) ^ 3 *
      (gaussian α (2 * t) * gaussian α (2 * t - 1 / 2)) := by
  have hB : alternatingGaussian α t ^ 4 = gaussian α t ^ 4 - thetaScale α t := by
    unfold thetaScale
    ring
  have hC : gaussian α (t - 1 / 2) ^ 4 =
      alternatingGaussian α (t - 1 / 2) ^ 4 + thetaScale α t := by
    rw [← thetaScale_shift hα t]
    unfold thetaScale
    ring
  calc
    thetaDiagonal α t = (1 / 2) * ((gaussian α t ^ 4) ^ 2 +
        (gaussian α (t - 1 / 2) ^ 4) ^ 2 - (alternatingGaussian α t ^ 4) ^ 2 -
        (alternatingGaussian α (t - 1 / 2) ^ 4) ^ 2) := by unfold thetaDiagonal; ring
    _ = thetaScale α t *
        (gaussian α t ^ 4 + alternatingGaussian α (t - 1 / 2) ^ 4) := by rw [hB, hC]; ring
    _ = (gaussian α 0 * gaussian α (1 / 2)) ^ 3 *
        (gaussian α (2 * t) * gaussian α (2 * t - 1 / 2)) := by
      rw [thetaScale_identity hα, gaussian_quartic_diagonal hα]
      ring

theorem thetaDiagonal_min {α : ℝ} (hα : 0 < α) (t : ℝ) :
    (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ≤ thetaDiagonal α t := by
  rw [thetaDiagonal_identity hα]
  have hp := gaussian_shift_product_min hα (2 * t)
  have hmul := mul_le_mul_of_nonneg_left hp
    (pow_nonneg (mul_nonneg (gaussian_pos hα 0).le (gaussian_pos hα (1 / 2)).le) 3)
  nlinarith only [hmul]

theorem thetaDiagonal_min_iff {α : ℝ} (hα : 0 < α) (t : ℝ) :
    thetaDiagonal α t = (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ↔
      ∃ z : ℤ, 4 * t = (z : ℝ) := by
  have hp : 0 < gaussian α 0 * gaussian α (1 / 2) :=
    mul_pos (gaussian_pos hα 0) (gaussian_pos hα (1 / 2))
  rw [thetaDiagonal_identity hα, show (gaussian α 0 * gaussian α (1 / 2)) ^ 4 =
    (gaussian α 0 * gaussian α (1 / 2)) ^ 3 *
      (gaussian α 0 * gaussian α (1 / 2)) by ring,
    mul_right_inj' (pow_pos hp 3).ne', gaussian_shift_product_min_iff hα]
  simp only [show 2 * (2 * t) = 4 * t by ring]

theorem thetaDiagonal_equality_points {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t)
    (ht2 : t ≤ 1 / 2) :
    thetaDiagonal α t = (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ↔
      t = 0 ∨ t = 1 / 4 ∨ t = 1 / 2 := by
  rw [thetaDiagonal_min_iff hα]
  constructor
  · rintro ⟨z, hz⟩
    have hz0 : (0 : ℤ) ≤ z := by exact_mod_cast (show (0 : ℝ) ≤ z by linarith)
    have hz2 : z ≤ (2 : ℤ) := by exact_mod_cast (show (z : ℝ) ≤ 2 by linarith)
    interval_cases z
    · left; norm_num at hz; linarith
    · right; left; norm_num at hz; linarith
    · right; right; norm_num at hz; linarith
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by norm_num⟩
    · exact ⟨1, by norm_num⟩
    · exact ⟨2, by norm_num⟩

end PaperVerification.ColdSpots
end
end Source_ThetaRelations
-- END ORIGINAL PaperVerification.ThetaRelations


-- BEGIN ORIGINAL PaperVerification.ThetaHyperbolicArc
section Source_ThetaHyperbolicArc

-- original header: module
-- original header: public import PaperVerification.ThetaRelations
-- original header: public import PaperVerification.GaussianAlternating
-- original header: public import Mathlib.Analysis.SpecialFunctions.Arsinh
-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

def thetaR (α : ℝ) : ℝ :=
  Real.arsinh (alternatingGaussian α 0 ^ 2 / gaussian α (1 / 2) ^ 2)

def thetaP (α t : ℝ) : ℝ :=
  Real.arsinh (alternatingGaussian α t ^ 2 / Real.sqrt (thetaScale α t))

lemma cosh_arsinh_of_hyperbola {x y : ℝ} (hx : 0 ≤ x) (hxy : x ^ 2 - y ^ 2 = 1) :
    Real.cosh (Real.arsinh y) = x := by
  rw [Real.cosh_arsinh]
  exact (Real.sqrt_eq_iff_eq_sq (by positivity) hx).mpr (by linarith)

theorem thetaR_pos {α : ℝ} (hα : 0 < α) : 0 < thetaR α := by
  apply Real.arsinh_pos_iff.mpr
  exact div_pos (sq_pos_of_pos (alternatingGaussian_zero_pos hα))
    (sq_pos_of_pos (gaussian_pos hα (1 / 2)))

theorem thetaR_sinh (α : ℝ) :
    Real.sinh (thetaR α) = alternatingGaussian α 0 ^ 2 / gaussian α (1 / 2) ^ 2 := by
  exact Real.sinh_arsinh _

theorem thetaR_cosh {α : ℝ} (hα : 0 < α) :
    Real.cosh (thetaR α) = gaussian α 0 ^ 2 / gaussian α (1 / 2) ^ 2 := by
  apply cosh_arsinh_of_hyperbola (by positivity)
  have hq := gaussian_constant_quartic hα
  have hc : gaussian α (1 / 2) ≠ 0 := (gaussian_pos hα (1 / 2)).ne'
  field_simp [hc]
  nlinarith [hq]

theorem thetaP_sinh (α t : ℝ) :
    Real.sinh (thetaP α t) = alternatingGaussian α t ^ 2 / Real.sqrt (thetaScale α t) := by
  exact Real.sinh_arsinh _

theorem thetaP_cosh {α : ℝ} (hα : 0 < α) (t : ℝ) :
    Real.cosh (thetaP α t) = gaussian α t ^ 2 / Real.sqrt (thetaScale α t) := by
  apply cosh_arsinh_of_hyperbola (by positivity)
  have hs := thetaScale_pos hα t
  have hroot := Real.sq_sqrt hs.le
  have hr : Real.sqrt (thetaScale α t) ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  field_simp [hr]
  change Real.sqrt (thetaScale α t) ^ 2 = gaussian α t ^ 4 - alternatingGaussian α t ^ 4 at hroot
  nlinarith [hroot]

theorem thetaP_cosh_sub {α : ℝ} (hα : 0 < α) (t : ℝ) :
    Real.cosh (thetaR α - thetaP α t) =
      gaussian α (t - 1 / 2) ^ 2 / Real.sqrt (thetaScale α t) := by
  rw [Real.cosh_sub, thetaR_cosh hα, thetaP_cosh hα, thetaR_sinh, thetaP_sinh]
  have hc : gaussian α (1 / 2) ≠ 0 := (gaussian_pos hα (1 / 2)).ne'
  have hr : Real.sqrt (thetaScale α t) ≠ 0 := (Real.sqrt_pos.mpr (thetaScale_pos hα t)).ne'
  field_simp [hc, hr]
  rw [show (2 * t - 1) / 2 = t - 1 / 2 by ring]
  nlinarith [(gaussian_quadratic_relations hα t).1]

theorem thetaP_sinh_sub {α : ℝ} (hα : 0 < α) (t : ℝ) :
    Real.sinh (thetaR α - thetaP α t) =
      alternatingGaussian α (t - 1 / 2) ^ 2 / Real.sqrt (thetaScale α t) := by
  rw [Real.sinh_sub, thetaR_cosh hα, thetaP_cosh hα, thetaR_sinh, thetaP_sinh]
  have hc : gaussian α (1 / 2) ≠ 0 := (gaussian_pos hα (1 / 2)).ne'
  have hr : Real.sqrt (thetaScale α t) ≠ 0 := (Real.sqrt_pos.mpr (thetaScale_pos hα t)).ne'
  field_simp [hc, hr]
  rw [show (2 * t - 1) / 2 = t - 1 / 2 by ring]
  nlinarith [gaussian_quadratic_relation_reverse hα t]

/-- The hyperbolic parameter lies in the full claimed range; no monotonicity assumption is used. -/
theorem thetaP_mem_Icc {α : ℝ} (hα : 0 < α) (t : ℝ) :
    thetaP α t ∈ Set.Icc 0 (thetaR α) := by
  constructor
  · exact Real.arsinh_nonneg_iff.mpr (div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))
  · have h := Real.sinh_nonneg_iff.mp (show 0 ≤ Real.sinh (thetaR α - thetaP α t) by
      rw [thetaP_sinh_sub hα]
      positivity)
    linarith

theorem continuous_thetaScale {α : ℝ} (hα : 0 < α) : Continuous (thetaScale α) :=
  ((continuous_gaussian hα).pow 4).sub ((continuous_alternatingGaussian hα).pow 4)

theorem continuous_thetaP {α : ℝ} (hα : 0 < α) : Continuous (thetaP α) := by
  apply Real.continuous_arsinh.comp
  exact ((continuous_alternatingGaussian hα).pow 2).div
    (Real.continuous_sqrt.comp (continuous_thetaScale hα))
    (fun t ↦ (Real.sqrt_pos.mpr (thetaScale_pos hα t)).ne')

theorem thetaP_zero {α : ℝ} (hα : 0 < α) : thetaP α 0 = thetaR α := by
  apply Real.sinh_injective
  rw [thetaP_sinh, thetaR_sinh]
  have hs : thetaScale α 0 = gaussian α (1 / 2) ^ 4 := by
    unfold thetaScale
    nlinarith [gaussian_constant_quartic hα]
  rw [hs, show gaussian α (1 / 2) ^ 4 = (gaussian α (1 / 2) ^ 2) ^ 2 by ring,
    Real.sqrt_sq (sq_nonneg _)]

theorem thetaP_half (α : ℝ) : thetaP α (1 / 2) = 0 := by
  apply Real.sinh_injective
  rw [thetaP_sinh, alternatingGaussian_half]
  simp

theorem thetaP_quarter {α : ℝ} (hα : 0 < α) : thetaP α (1 / 4) = thetaR α / 2 := by
  have hD : alternatingGaussian α ((1 / 4 : ℝ) - 1 / 2) = alternatingGaussian α (1 / 4) := by
    rw [show (1 / 4 : ℝ) - 1 / 2 = -(1 / 4 : ℝ) by ring, alternatingGaussian_even]
  have hs := thetaP_sinh_sub hα (1 / 4)
  rw [hD, ← thetaP_sinh] at hs
  have he := Real.sinh_injective hs
  linarith

/-- The measurable parameter map used for the pushforward in Proposition 3.2. -/
def thetaArcPoint {α : ℝ} (hα : 0 < α) (t : Set.Icc (0 : ℝ) (1 / 2)) :
    Set.Icc (0 : ℝ) (thetaR α) :=
  ⟨thetaP α t, thetaP_mem_Icc hα t⟩

theorem continuous_thetaArcPoint {α : ℝ} (hα : 0 < α) : Continuous (thetaArcPoint hα) :=
  ((continuous_thetaP hα).comp continuous_subtype_val).subtype_mk _

end PaperVerification.ColdSpots
end
end Source_ThetaHyperbolicArc
-- END ORIGINAL PaperVerification.ThetaHyperbolicArc


-- BEGIN ORIGINAL PaperVerification.ThetaGeometricTransfer
section Source_ThetaGeometricTransfer

-- original header: module
-- original header: public import PaperVerification.ThetaHyperbolicArc
-- original header: public import PaperVerification.GeometricMeanLaws
-- original header: public import PaperVerification.HyperbolicMeasure
-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open MeasureTheory Set Filter Topology
open PaperVerification.Hyperbolic

abbrev HalfInterval := Set.Icc (0 : ℝ) (1 / 2)

def thetaAMap {α : ℝ} (hα : 0 < α) : C(HalfInterval, ℝ) :=
  ⟨fun t ↦ gaussian α t, (continuous_gaussian hα).comp continuous_subtype_val⟩

def thetaBMap {α : ℝ} (hα : 0 < α) : C(HalfInterval, ℝ) :=
  ⟨fun t ↦ alternatingGaussian α t, (continuous_alternatingGaussian hα).comp continuous_subtype_val⟩

def thetaCMap {α : ℝ} (hα : 0 < α) : C(HalfInterval, ℝ) :=
  ⟨fun t ↦ gaussian α ((t : ℝ) - 1 / 2),
    (continuous_gaussian hα).comp (continuous_subtype_val.sub continuous_const)⟩

def thetaDMap {α : ℝ} (hα : 0 < α) : C(HalfInterval, ℝ) :=
  ⟨fun t ↦ alternatingGaussian α ((t : ℝ) - 1 / 2),
    (continuous_alternatingGaussian hα).comp (continuous_subtype_val.sub continuous_const)⟩

def thetaRootMap {α : ℝ} (hα : 0 < α) : C(HalfInterval, ℝ) :=
  ⟨fun t ↦ Real.sqrt (thetaScale α t),
    Real.continuous_sqrt.comp ((continuous_thetaScale hα).comp continuous_subtype_val)⟩

def thetaArcMap {α : ℝ} (hα : 0 < α) : C(HalfInterval, Interval (thetaR α)) :=
  ⟨thetaArcPoint hα, continuous_thetaArcPoint hα⟩

def thetaDiagonalMap {α : ℝ} (hα : 0 < α) : C(HalfInterval, ℝ) :=
  ⟨thetaDiagonal α ∘ Subtype.val, by
    exact continuous_const.mul
      (((((thetaAMap hα).continuous.pow 8).add ((thetaCMap hα).continuous.pow 8)).sub
        ((thetaBMap hα).continuous.pow 8)).sub ((thetaDMap hα).continuous.pow 8))⟩

def centeredCoshMap (R : ℝ) : C(Interval R, ℝ) :=
  ⟨fun p ↦ Real.cosh (2 * (p : ℝ) - R),
    Real.continuous_cosh.comp
      ((continuous_const.mul continuous_subtype_val).sub continuous_const)⟩

def thetaPush {α : ℝ} (hα : 0 < α) (μ : ProbabilityMeasure HalfInterval) :
    ProbabilityMeasure (Interval (thetaR α)) := μ.map (thetaArcMap hα)

lemma thetaAMap_pos {α : ℝ} (hα : 0 < α) (t : HalfInterval) : 0 < thetaAMap hα t :=
  gaussian_pos hα t

lemma thetaBMap_nonneg {α : ℝ} (hα : 0 < α) (t : HalfInterval) : 0 ≤ thetaBMap hα t :=
  alternatingGaussian_nonneg hα t.property.1 t.property.2

lemma thetaCMap_pos {α : ℝ} (hα : 0 < α) (t : HalfInterval) : 0 < thetaCMap hα t :=
  gaussian_pos hα _

lemma thetaDMap_nonneg {α : ℝ} (hα : 0 < α) (t : HalfInterval) : 0 ≤ thetaDMap hα t := by
  change 0 ≤ alternatingGaussian α ((t : ℝ) - 1 / 2)
  rw [show (t : ℝ) - 1 / 2 = -(1 / 2 - (t : ℝ)) by ring, alternatingGaussian_even]
  exact alternatingGaussian_nonneg hα (by linarith [t.property.2])
    (by linarith [t.property.1])

lemma thetaRootMap_pos {α : ℝ} (hα : 0 < α) (t : HalfInterval) :
    0 < thetaRootMap hα t := Real.sqrt_pos.mpr (thetaScale_pos hα t)

lemma thetaAMap_square {α : ℝ} (hα : 0 < α) :
    thetaAMap hα ^ 2 = (intervalCosh (thetaR α)).comp (thetaArcMap hα) * thetaRootMap hα := by
  ext t
  change gaussian α t ^ 2 = Real.cosh (thetaP α t) * Real.sqrt (thetaScale α t)
  exact ((eq_div_iff (Real.sqrt_pos.mpr (thetaScale_pos hα t)).ne').mp (thetaP_cosh hα t)).symm

lemma thetaBMap_square {α : ℝ} (hα : 0 < α) :
    thetaBMap hα ^ 2 = (intervalSinh (thetaR α)).comp (thetaArcMap hα) * thetaRootMap hα := by
  ext t
  change alternatingGaussian α t ^ 2 = Real.sinh (thetaP α t) * Real.sqrt (thetaScale α t)
  exact ((eq_div_iff (Real.sqrt_pos.mpr (thetaScale_pos hα t)).ne').mp (thetaP_sinh α t)).symm

lemma thetaCMap_square {α : ℝ} (hα : 0 < α) :
    thetaCMap hα ^ 2 =
      (intervalReflectedCosh (thetaR α)).comp (thetaArcMap hα) * thetaRootMap hα := by
  ext t
  change gaussian α ((t : ℝ) - 1 / 2) ^ 2 =
    Real.cosh (thetaR α - thetaP α t) * Real.sqrt (thetaScale α t)
  exact ((eq_div_iff (Real.sqrt_pos.mpr (thetaScale_pos hα t)).ne').mp
    (thetaP_cosh_sub hα t)).symm

lemma thetaDMap_square {α : ℝ} (hα : 0 < α) :
    thetaDMap hα ^ 2 =
      (intervalReflectedSinh (thetaR α)).comp (thetaArcMap hα) * thetaRootMap hα := by
  ext t
  change alternatingGaussian α ((t : ℝ) - 1 / 2) ^ 2 =
    Real.sinh (thetaR α - thetaP α t) * Real.sqrt (thetaScale α t)
  exact ((eq_div_iff (Real.sqrt_pos.mpr (thetaScale_pos hα t)).ne').mp
    (thetaP_sinh_sub hα t)).symm

lemma hyperbolic_half_diagonal (R p : ℝ) :
    Real.cosh p ^ 2 + Real.sinh (R - p) ^ 2 =
      Real.cosh R * Real.cosh (2 * p - R) := by
  have h₁ := Real.cosh_add R (2 * p - R)
  have h₂ := Real.cosh_sub R (2 * p - R)
  rw [show R + (2 * p - R) = 2 * p by ring] at h₁
  rw [show R - (2 * p - R) = 2 * (R - p) by ring] at h₂
  rw [Real.cosh_two_mul] at h₁ h₂
  nlinarith [Real.cosh_sq_sub_sinh_sq p, Real.cosh_sq_sub_sinh_sq (R - p)]

theorem thetaDiagonal_hyperbolic {α : ℝ} (hα : 0 < α) (t : ℝ) :
    thetaDiagonal α t = thetaScale α t ^ 2 * Real.cosh (thetaR α) *
      Real.cosh (2 * thetaP α t - thetaR α) := by
  have hr : Real.sqrt (thetaScale α t) ≠ 0 := (Real.sqrt_pos.mpr (thetaScale_pos hα t)).ne'
  have hA := ((eq_div_iff hr).mp (thetaP_cosh hα t)).symm
  have hD := ((eq_div_iff hr).mp (thetaP_sinh_sub hα t)).symm
  calc
    thetaDiagonal α t = thetaScale α t *
        (gaussian α t ^ 4 + alternatingGaussian α (t - 1 / 2) ^ 4) := thetaDiagonal_scale hα t
    _ = thetaScale α t * (Real.sqrt (thetaScale α t) ^ 2 *
        (Real.cosh (thetaP α t) ^ 2 + Real.sinh (thetaR α - thetaP α t) ^ 2)) := by
      rw [show gaussian α t ^ 4 = (gaussian α t ^ 2) ^ 2 by ring,
        show alternatingGaussian α (t - 1 / 2) ^ 4 =
          (alternatingGaussian α (t - 1 / 2) ^ 2) ^ 2 by ring, hA, hD]
      ring
    _ = _ := by
      rw [Real.sq_sqrt (thetaScale_pos hα t).le, hyperbolic_half_diagonal]
      ring

def thetaNormalization {α : ℝ} (hα : 0 < α) (μ : ProbabilityMeasure HalfInterval) : ℝ :=
  geometricMoment 4 (thetaRootMap hα) μ

def thetaMomentNumerator {α : ℝ} (hα : 0 < α) (μ : ProbabilityMeasure HalfInterval) : ℝ :=
  geometricMoment 8 (thetaAMap hα) μ + geometricMoment 8 (thetaCMap hα) μ -
    geometricMoment 8 (thetaBMap hα) μ - geometricMoment 8 (thetaDMap hα) μ

theorem thetaNormalization_pos {α : ℝ} (hα : 0 < α) (μ : ProbabilityMeasure HalfInterval) :
    0 < thetaNormalization hα μ :=
  geometricMoment_pos_of_pos 4 (by norm_num) (thetaRootMap hα) μ (thetaRootMap_pos hα)

lemma theta_moment_factorization {α : ℝ} (hα : 0 < α) (μ : ProbabilityMeasure HalfInterval)
    (f : C(HalfInterval, ℝ)) (F : C(Interval (thetaR α), ℝ))
    (hf : ∀ t, 0 ≤ f t) (hF : ∀ t, 0 ≤ F t)
    (heq : f ^ 2 = F.comp (thetaArcMap hα) * thetaRootMap hα) :
    geometricMoment 8 f μ = thetaNormalization hα μ * geometricMoment 4 F (thetaPush hα μ) := by
  have hp := geometricMoment_nat_pow 4 2 f μ hf
  norm_num only [Nat.reduceMul, Nat.cast_ofNat] at hp
  rw [← hp, heq,
    geometricMoment_mul_pos_right 4 (by norm_num) _ _ μ
      (fun t ↦ hF (thetaArcMap hα t)) (thetaRootMap_pos hα),
    ← geometricMoment_map]
  unfold thetaNormalization thetaPush
  ring

theorem thetaMomentNumerator_factorization {α : ℝ} (hα : 0 < α)
    (μ : ProbabilityMeasure HalfInterval) :
    thetaMomentNumerator hα μ =
      thetaNormalization hα μ * hyperbolicNumerator (thetaR α) (thetaPush hα μ) := by
  have hA := theta_moment_factorization hα μ (thetaAMap hα) (intervalCosh (thetaR α))
    (fun t ↦ (thetaAMap_pos hα t).le) (fun p ↦ (Real.cosh_pos (p : ℝ)).le) (thetaAMap_square hα)
  have hB := theta_moment_factorization hα μ (thetaBMap hα) (intervalSinh (thetaR α))
    (thetaBMap_nonneg hα) (fun p ↦ Real.sinh_nonneg_iff.mpr p.property.1) (thetaBMap_square hα)
  have hC := theta_moment_factorization hα μ (thetaCMap hα) (intervalReflectedCosh (thetaR α))
    (fun t ↦ (thetaCMap_pos hα t).le) (fun p ↦ (Real.cosh_pos _).le) (thetaCMap_square hα)
  have hD := theta_moment_factorization hα μ (thetaDMap hα) (intervalReflectedSinh (thetaR α))
    (thetaDMap_nonneg hα) (fun p ↦ Real.sinh_nonneg_iff.mpr (sub_nonneg.mpr p.property.2))
    (thetaDMap_square hα)
  unfold thetaMomentNumerator hyperbolicNumerator
  rw [hA, hB, hC, hD]
  ring

lemma thetaDiagonalMap_factorization {α : ℝ} (hα : 0 < α) :
    thetaDiagonalMap hα = thetaRootMap hα ^ 4 *
      (ContinuousMap.const HalfInterval (Real.cosh (thetaR α)) *
        (centeredCoshMap (thetaR α)).comp (thetaArcMap hα)) := by
  ext t
  change thetaDiagonal α t = Real.sqrt (thetaScale α t) ^ 4 *
    (Real.cosh (thetaR α) * Real.cosh (2 * thetaP α t - thetaR α))
  rw [thetaDiagonal_hyperbolic hα,
    show Real.sqrt (thetaScale α t) ^ 4 = (Real.sqrt (thetaScale α t) ^ 2) ^ 2 by ring,
    Real.sq_sqrt (thetaScale_pos hα t).le]
  ring

theorem thetaDiagonal_geometric_factorization {α : ℝ} (hα : 0 < α)
    (μ : ProbabilityMeasure HalfInterval) :
    geometricMean (thetaDiagonalMap hα) μ = thetaNormalization hα μ * Real.cosh (thetaR α) *
      geometricMean (centeredCoshMap (thetaR α)) (thetaPush hα μ) := by
  have hroot : geometricMean (thetaRootMap hα) μ ^ 4 = thetaNormalization hα μ :=
    (geometricMoment_nat 4 (thetaRootMap hα) μ).symm
  have hmap : geometricMean (centeredCoshMap (thetaR α)) (thetaPush hα μ) =
      geometricMean ((centeredCoshMap (thetaR α)).comp (thetaArcMap hα)) μ :=
    geometricMoment_map 1 (centeredCoshMap (thetaR α)) (thetaArcMap hα) μ
  rw [thetaDiagonalMap_factorization hα,
    geometricMean_mul_pos_right _ _ μ (fun t ↦ pow_nonneg (thetaRootMap_pos hα t).le 4)
      (fun t ↦ mul_pos (Real.cosh_pos _) (Real.cosh_pos _)),
    geometricMean_pow 4 _ μ (fun t ↦ (thetaRootMap_pos hα t).le),
    geometricMean_mul_pos_right _ _ μ (fun _ ↦ (Real.cosh_pos _).le)
      (fun _ ↦ Real.cosh_pos _),
    geometricMean_const (Real.cosh_pos _) μ, hroot, ← hmap]
  ring

theorem thetaDiagonal_geometric_lower {α : ℝ} (hα : 0 < α)
    (μ : ProbabilityMeasure HalfInterval) :
    (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ≤ geometricMean (thetaDiagonalMap hα) μ :=
  geometricMean_ge_const (thetaDiagonalMap hα) μ
    (pow_pos (mul_pos (gaussian_pos hα 0) (gaussian_pos hα (1 / 2))) 4)
    (fun t ↦ thetaDiagonal_min hα t)

/-- The diagonal equality condition is exact for every probability measure. -/
theorem thetaDiagonal_geometric_eq_iff {α : ℝ} (hα : 0 < α)
    (μ : ProbabilityMeasure HalfInterval) :
    geometricMean (thetaDiagonalMap hα) μ = (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ↔
      ∀ᵐ (t : HalfInterval) ∂(μ : Measure HalfInterval),
        (t : ℝ) = 0 ∨ (t : ℝ) = 1 / 4 ∨ (t : ℝ) = 1 / 2 := by
  rw [geometricMean_eq_const_iff (thetaDiagonalMap hα) μ
    (pow_pos (mul_pos (gaussian_pos hα 0) (gaussian_pos hα (1 / 2))) 4)
    (fun t ↦ thetaDiagonal_min hα t)]
  constructor
  · intro h
    filter_upwards [h] with t ht
    exact (thetaDiagonal_equality_points hα t.property.1 t.property.2).mp ht
  · intro h
    filter_upwards [h] with t ht
    exact (thetaDiagonal_equality_points hα t.property.1 t.property.2).mpr ht

/-- Exact transfer step; the hypothesis here is the separately proved hyperbolic inequality. -/
theorem thetaMoment_bound_from_hyperbolic {α : ℝ} (hα : 0 < α)
    (μ : ProbabilityMeasure HalfInterval)
    (hH : 2 * Real.cosh (thetaR α) *
      geometricMean (centeredCoshMap (thetaR α)) (thetaPush hα μ) ≤
        hyperbolicNumerator (thetaR α) (thetaPush hα μ)) :
    2 * (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ≤ thetaMomentNumerator hα μ := by
  have hK := thetaNormalization_pos hα μ
  have hnum := thetaMomentNumerator_factorization hα μ
  have hdiag := thetaDiagonal_geometric_factorization hα μ
  have hlower := thetaDiagonal_geometric_lower hα μ
  have hmul := mul_le_mul_of_nonneg_left hH hK.le
  nlinarith [hmul]

/-- Equality is retained at both stages of the transfer, including singular measures. -/
theorem thetaMoment_equality_from_hyperbolic {α : ℝ} (hα : 0 < α)
    (μ : ProbabilityMeasure HalfInterval)
    (hH : 2 * Real.cosh (thetaR α) *
      geometricMean (centeredCoshMap (thetaR α)) (thetaPush hα μ) ≤
        hyperbolicNumerator (thetaR α) (thetaPush hα μ)) :
    thetaMomentNumerator hα μ = 2 * (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ↔
      geometricMean (thetaDiagonalMap hα) μ = (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ∧
      hyperbolicNumerator (thetaR α) (thetaPush hα μ) = 2 * Real.cosh (thetaR α) *
        geometricMean (centeredCoshMap (thetaR α)) (thetaPush hα μ) := by
  have hK := thetaNormalization_pos hα μ
  have hnum := thetaMomentNumerator_factorization hα μ
  have hdiag := thetaDiagonal_geometric_factorization hα μ
  have hlower := thetaDiagonal_geometric_lower hα μ
  have hmul := mul_le_mul_of_nonneg_left hH hK.le
  constructor
  · intro heq
    have hd : geometricMean (thetaDiagonalMap hα) μ =
        (gaussian α 0 * gaussian α (1 / 2)) ^ 4 := by nlinarith [hmul]
    refine ⟨hd, ?_⟩
    apply mul_left_cancel₀ hK.ne'
    calc
      thetaNormalization hα μ * hyperbolicNumerator (thetaR α) (thetaPush hα μ) =
          thetaMomentNumerator hα μ := hnum.symm
      _ = 2 * (gaussian α 0 * gaussian α (1 / 2)) ^ 4 := heq
      _ = 2 * geometricMean (thetaDiagonalMap hα) μ := by rw [hd]
      _ = _ := by rw [hdiag]; ring
  · rintro ⟨hd, heq⟩
    rw [heq] at hnum
    nlinarith only [hnum, hdiag, hd]

end PaperVerification.ColdSpots
end
end Source_ThetaGeometricTransfer
-- END ORIGINAL PaperVerification.ThetaGeometricTransfer


-- Kernel-environment audit: every mathematical source body precedes this command.
set_option maxHeartbeats 0 in
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let kenv := env.checked.get
  let entries := kenv.constants.foldStage2
    (fun rows name ci => rows.push (name, ci)) (#[] : Array (Name × ConstantInfo))
  let kind : ConstantInfo → String := fun ci => match ci with
    | .axiomInfo _ => "axiom"
    | .defnInfo _ => "definition"
    | .thmInfo _ => "theorem"
    | .opaqueInfo _ => "opaque"
    | .quotInfo _ => "quotient"
    | .ctorInfo _ => "constructor"
    | .recInfo _ => "recursor"
    | .inductInfo _ => "inductive"
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut rows : Array Json := #[]
  let mut failures : Array Json := #[]
  for (name, ci) in entries do
    if ci.isUnsafe then
      failures := failures.push (Json.mkObj [
        ("declaration", toJson name.toString),
        ("unsafe_declaration", toJson true)])
    let deps := ci.getUsedConstantsAsSet.toArray.qsort Name.lt
    let mut dependencyRows : Array Json := #[]
    for dep in deps do
      match kenv.find? dep with
      | none =>
        failures := failures.push (Json.mkObj [
          ("declaration", toJson name.toString),
          ("missing_dependency", toJson dep.toString)])
      | some info =>
        let origin := match env.getModuleIdxFor? dep with
          | some idx => env.header.moduleNames[idx]!.toString
          | none => env.mainModule.toString
        dependencyRows := dependencyRows.push (Json.mkObj [
          ("name", toJson dep.toString), ("kind", toJson (kind info)),
          ("module", toJson origin)])
    let axioms ← Lean.collectAxioms name
    let bad := axioms.filter (fun ax => !allowed.contains ax)
    if !bad.isEmpty then
      failures := failures.push (Json.mkObj [
        ("declaration", toJson name.toString),
        ("unapproved_axioms", toJson (bad.map Name.toString))])
    rows := rows.push (Json.mkObj [
      ("name", toJson name.toString), ("kind", toJson (kind ci)),
      ("unsafe", toJson ci.isUnsafe),
      ("type", toJson (toString ci.type)),
      ("level_parameters", toJson (ci.levelParams.map Name.toString)),
      ("has_body", toJson (ci.value? (allowOpaque := true)).isSome),
      ("dependencies", Json.arr dependencyRows),
      ("axioms", toJson (axioms.map Name.toString))])
  let sourceHash ← IO.getEnv "PAPER_VERIFICATION_SOURCE_SHA256"
  let fingerprint ← IO.getEnv "PAPER_VERIFICATION_FINGERPRINT"
  let document := Json.mkObj [
    ("schema", toJson (1 : Nat)),
    ("module", toJson env.mainModule.toString),
    ("source_sha256", toJson sourceHash),
    ("fingerprint", toJson fingerprint),
    ("kernel_environment", toJson true),
    ("declarations", Json.arr rows),
    ("failures", Json.arr failures),
    ("passed", toJson failures.isEmpty)]
  let target := (← IO.getEnv "PAPER_VERIFICATION_AUDIT_PATH").getD ".lake/build/paper-audit/PaperVerification_Lattice003.json"
  let path : System.FilePath := target
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile path (document.compress ++ "\n")
  if !failures.isEmpty then
    throwError "Kernel declaration audit rejected {failures.size} dependency/axiom findings; see {target}"
  logInfo m!"Kernel declaration audit passed for {rows.size} declarations; see {target}"
