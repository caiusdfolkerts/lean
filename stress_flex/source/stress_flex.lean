module

public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import TauCeti.AlgebraicTopology.Cellular.Comparison
public import TauCeti.AlgebraicTopology.Cellular.Incidence
public import TauCeti.AlgebraicTopology.Singular.Sphere
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import TauCeti.AlgebraicTopology.Cellular.EdgeIncidence
public import TauCeti.Topology.CWComplex.Classical.Zero
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Neighborhood

@[expose] public section

noncomputable section

/-! ## Source fragment: StressFlex/Continuation.lean -/

open Matrix Filter
open scoped BigOperators Topology

namespace StressFlex

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

abbrev Coordinates (κ : Type*) := κ → ℝ

def IsConeFixedMotion (E : ι → ι → Prop) (p u : ι → Coordinates κ) : Prop :=
  (∀ i, p i ⬝ᵥ u i = 0) ∧
    ∀ i j, E i j → (p i - p j) ⬝ᵥ (u i - u j) = 0

def IsOuterStress (E : ι → ι → Prop) (p : ι → Coordinates κ)
    (M : Matrix ι ι ℝ) (x : Coordinates κ) : Prop :=
  (∀ i j, M i j = M j i) ∧
  (∀ i j, i ≠ j → ¬ E i j → M i j = 0) ∧
  ∀ i, ∑ j, M i j • (p j - x) = 0

def weightedVelocity (M : Matrix ι ι ℝ) (u : ι → Coordinates κ) : Coordinates κ :=
  ∑ i, (∑ j, M i j) • u i

theorem dot_sum_right {α : Type*} [Fintype α]
    (a : Coordinates κ) (b : α → Coordinates κ) :
    a ⬝ᵥ (∑ i, b i) = ∑ i, a ⬝ᵥ b i := by
  classical
  simp only [dotProduct, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem dot_sum_left {α : Type*} [Fintype α]
    (a : α → Coordinates κ) (b : Coordinates κ) :
    (∑ i, a i) ⬝ᵥ b = ∑ i, a i ⬝ᵥ b := by
  classical
  simp only [dotProduct, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem dot_smul_left (c : ℝ) (a b : Coordinates κ) :
    (c • a) ⬝ᵥ b = c * (a ⬝ᵥ b) := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem dot_smul_right (c : ℝ) (a b : Coordinates κ) :
    a ⬝ᵥ (c • b) = c * (a ⬝ᵥ b) := by
  rw [dotProduct_comm, dot_smul_left, dotProduct_comm]

/-- The two mixed terms in the usual stress–motion trace are equal. -/
theorem symmetric_mixed_sum (M : Matrix ι ι ℝ) (p u : ι → Coordinates κ)
    (hM : ∀ i j, M i j = M j i) :
    (∑ i, ∑ j, M i j * (p i ⬝ᵥ u j)) =
      ∑ i, ∑ j, M i j * (p j ⬝ᵥ u i) := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hM j i]

/-- The edge equations and the original cone equations cancel the stress trace. -/
theorem stress_motion_trace_zero (E : ι → ι → Prop)
    (p u : ι → Coordinates κ) (M : Matrix ι ι ℝ)
    (hsym : ∀ i j, M i j = M j i)
    (hsupp : ∀ i j, i ≠ j → ¬ E i j → M i j = 0)
    (hu : IsConeFixedMotion E p u) :
    (∑ i, ∑ j, M i j * (p j ⬝ᵥ u i)) = 0 := by
  classical
  have heq (i j : ι) :
      M i j * ((p i - p j) ⬝ᵥ (u i - u j)) = 0 := by
    by_cases hij : i = j
    · subst j
      simp
    by_cases hE : E i j
    · rw [hu.2 i j hE, mul_zero]
    · rw [hsupp i j hij hE, zero_mul]
  have hexpand (i j : ι) :
      M i j * ((p i - p j) ⬝ᵥ (u i - u j)) =
        -(M i j * (p i ⬝ᵥ u j)) - M i j * (p j ⬝ᵥ u i) := by
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hu.1 i, hu.1 j]
    ring
  have hz : (∑ i, ∑ j,
      (-(M i j * (p i ⬝ᵥ u j)) - M i j * (p j ⬝ᵥ u i))) = 0 := by
    simp_rw [← hexpand]
    simp only [heq, Finset.sum_const_zero]
  have hmix := symmetric_mixed_sum M p u hsym
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hz
  linarith

/-- Pairing a moved-apex stress with an original fixed-apex motion. -/
theorem moved_stress_pairing_zero (E : ι → ι → Prop)
    (p u : ι → Coordinates κ) (M : Matrix ι ι ℝ) (x : Coordinates κ)
    (hM : IsOuterStress E p M x) (hu : IsConeFixedMotion E p u) :
    x ⬝ᵥ weightedVelocity M u = 0 := by
  classical
  have heq (i : ι) :
      (∑ j, M i j * (p j ⬝ᵥ u i)) -
        (∑ j, M i j) * (x ⬝ᵥ u i) = 0 := by
    have h := congrArg (fun z => z ⬝ᵥ u i) (hM.2.2 i)
    simp only [dot_sum_left, dot_smul_left, sub_dotProduct, zero_dotProduct,
      mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul] at h
    exact h
  have hsum : (∑ i, ((∑ j, M i j * (p j ⬝ᵥ u i)) -
      (∑ j, M i j) * (x ⬝ᵥ u i))) = 0 := by
    simp only [heq, Finset.sum_const_zero]
  have htrace := stress_motion_trace_zero E p u M hM.1 hM.2.1 hu
  simp only [Finset.sum_sub_distrib, htrace, zero_sub, neg_eq_zero] at hsum
  simpa only [weightedVelocity, dot_sum_right, dot_smul_right] using hsum

/-- Continuity and the identity x·f(x)=0 near zero force f(0)=0. -/
theorem continuous_pairing_vanishes (f : Coordinates κ → Coordinates κ)
    (hf : ContinuousAt f 0)
    (hpair : ∀ᶠ x in 𝓝 (0 : Coordinates κ), x ⬝ᵥ f x = 0) :
    f 0 = 0 := by
  classical
  have hz (z : Coordinates κ) : z ⬝ᵥ f 0 = 0 := by
    have hline : ContinuousAt (fun t : ℝ => t • z) 0 := by fun_prop
    have htf : ContinuousAt (fun t : ℝ => f (t • z)) 0 := by
      exact hf.comp_of_eq hline (by simp)
    have hdot : ContinuousAt (fun t : ℝ => z ⬝ᵥ f (t • z)) 0 := by
      unfold dotProduct
      apply tendsto_finsetSum
      intro k hk
      exact continuousAt_const.mul ((continuous_apply k).continuousAt.comp htf)
    have htend : Tendsto (fun t : ℝ => t • z) (𝓝[≠] (0 : ℝ))
        (𝓝 (0 : Coordinates κ)) := by
      simpa only [zero_smul] using hline.tendsto.mono_left nhdsWithin_le_nhds
    have hevent : ∀ᶠ t in 𝓝[≠] (0 : ℝ), z ⬝ᵥ f (t • z) = 0 := by
      filter_upwards [htend.eventually hpair, self_mem_nhdsWithin] with t ht hne
      have hmul : t * (z ⬝ᵥ f (t • z)) = 0 := by
        simpa only [dot_smul_left] using ht
      exact (mul_eq_zero.mp hmul).resolve_left hne
    have hzero : Tendsto (fun t : ℝ => z ⬝ᵥ f (t • z))
        (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hevent)
    have hvalue := tendsto_nhds_unique (hdot.tendsto.mono_left nhdsWithin_le_nhds) hzero
    simpa only [zero_smul] using hvalue
  exact dotProduct_self_eq_zero.mp (hz (f 0))

/-- Lemma 2 of the paper, with arbitrary finite vertex and coordinate types. -/
theorem continuation_orthogonality (E : ι → ι → Prop)
    (p u : ι → Coordinates κ) (M : Coordinates κ → Matrix ι ι ℝ)
    (hu : IsConeFixedMotion E p u) (hcont : ContinuousAt M 0)
    (hstress : ∀ᶠ x in 𝓝 (0 : Coordinates κ), IsOuterStress E p (M x) x) :
    weightedVelocity (M 0) u = 0 := by
  classical
  apply continuous_pairing_vanishes (fun x => weightedVelocity (M x) u)
  · unfold weightedVelocity
    apply tendsto_finsetSum
    intro i hi
    apply Filter.Tendsto.smul
    · apply tendsto_finsetSum
      intro j hj
      exact ((continuous_apply j).comp (continuous_apply i)).continuousAt.comp hcont
    · exact tendsto_const_nhds
  · filter_upwards [hstress] with x hx
    exact moved_stress_pairing_zero E p u (M x) x hx hu

end StressFlex

/-! ## Source fragment: StressFlex/AnalyticFormulas.lean -/

open Matrix
open scoped BigOperators

namespace StressFlex.Rational

abbrev Vec := Fin 3 → ℝ

theorem analyticAt_coord {f : Vec → Vec} {x : Vec}
    (hf : AnalyticAt ℝ f x) (k : Fin 3) :
    AnalyticAt ℝ (fun y => f y k) x := by
  exact ((ContinuousLinearMap.proj k : Vec →L[ℝ] ℝ).analyticAt (f x)).comp hf

theorem analyticAt_dot {f g : Vec → Vec} {x : Vec}
    (hf : AnalyticAt ℝ f x) (hg : AnalyticAt ℝ g x) :
    AnalyticAt ℝ (fun y => f y ⬝ᵥ g y) x := by
  simpa only [dotProduct, Finset.sum_apply, Pi.mul_apply] using!
    (Finset.univ.analyticAt_fun_sum fun k _ =>
      (analyticAt_coord hf k).fun_mul (analyticAt_coord hg k))

theorem analyticAt_cross {f g : Vec → Vec} {x : Vec}
    (hf : AnalyticAt ℝ f x) (hg : AnalyticAt ℝ g x) :
    AnalyticAt ℝ (fun y => f y ⨯₃ g y) x := by
  apply AnalyticAt.pi
  intro k
  fin_cases k
  · simpa [cross_apply] using!
      ((analyticAt_coord hf 1).mul (analyticAt_coord hg 2)).sub
        ((analyticAt_coord hf 2).mul (analyticAt_coord hg 1))
  · simpa [cross_apply] using!
      ((analyticAt_coord hf 2).mul (analyticAt_coord hg 0)).sub
        ((analyticAt_coord hf 0).mul (analyticAt_coord hg 2))
  · simpa [cross_apply] using!
      ((analyticAt_coord hf 0).mul (analyticAt_coord hg 1)).sub
        ((analyticAt_coord hf 1).mul (analyticAt_coord hg 0))

/-- The face functional that keeps all affine vertex heights fixed. -/
def faceForm (a n x : Vec) : Vec :=
  a + ((a ⬝ᵥ x) / (1 - n ⬝ᵥ x)) • n

theorem analyticAt_faceForm (a n x : Vec) (hn : 1 - n ⬝ᵥ x ≠ 0) :
    AnalyticAt ℝ (faceForm a n) x := by
  exact analyticAt_const.add
    (((analyticAt_dot analyticAt_const analyticAt_id).div
      (analyticAt_const.sub (analyticAt_dot analyticAt_const analyticAt_id)) hn).smul
        analyticAt_const)

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]

def edgeCross (p : V → Vec) (s t : E → V) (x : Vec) (e : E) : Vec :=
  (p (s e) - x) ⨯₃ (p (t e) - x)

def boundaryForm (B : E → F → ℝ) (n a : F → Vec) (x : Vec) (e : E) : Vec :=
  ∑ f, B e f • faceForm (a f) (n f) x

def edgeWeight (p : V → Vec) (s t : E → V)
    (B : E → F → ℝ) (n a : F → Vec) (x : Vec) (e : E) : ℝ :=
  (boundaryForm B n a x e ⬝ᵥ edgeCross p s t x e) /
    (edgeCross p s t x e ⬝ᵥ edgeCross p s t x e)

theorem analyticAt_edgeCross (p : V → Vec) (s t : E → V) (x : Vec) (e : E) :
    AnalyticAt ℝ (fun y => edgeCross p s t y e) x := by
  exact analyticAt_cross (analyticAt_const.sub analyticAt_id)
    (analyticAt_const.sub analyticAt_id)

theorem analyticAt_boundaryForm (B : E → F → ℝ) (n a : F → Vec) (x : Vec)
    (hn : ∀ f, 1 - n f ⬝ᵥ x ≠ 0) (e : E) :
    AnalyticAt ℝ (fun y => boundaryForm B n a y e) x := by
  simpa only [boundaryForm, Finset.sum_apply, Pi.smul_apply] using!
    (Finset.univ.analyticAt_fun_sum fun f _ =>
      ((analyticAt_faceForm (a f) (n f) x (hn f)).fun_const_smul (c := B e f)))

theorem analyticAt_edgeWeight (p : V → Vec) (s t : E → V)
    (B : E → F → ℝ) (n a : F → Vec) (x : Vec)
    (hn : ∀ f, 1 - n f ⬝ᵥ x ≠ 0) (e : E)
    (hq : edgeCross p s t x e ⬝ᵥ edgeCross p s t x e ≠ 0) :
    AnalyticAt ℝ (fun y => edgeWeight p s t B n a y e) x := by
  exact (analyticAt_dot (analyticAt_boundaryForm B n a x hn e)
    (analyticAt_edgeCross p s t x e)).div
      (analyticAt_dot (analyticAt_edgeCross p s t x e)
        (analyticAt_edgeCross p s t x e)) hq

/-- Endpoint signs use a fixed arbitrary orientation of each outer edge. -/
def incidence [DecidableEq V] (s t : E → V) (v : V) (e : E) : ℝ :=
  (if v = t e then 1 else 0) - (if v = s e then 1 else 0)

def force [DecidableEq V] (p : V → Vec) (s t : E → V)
    (B : E → F → ℝ) (n a : F → Vec) (x : Vec) (v : V) : Vec :=
  ∑ e, (incidence s t v e * edgeWeight p s t B n a x e) •
    (p (t e) - p (s e))

def coneWeight [DecidableEq V] (p : V → Vec) (s t : E → V)
    (B : E → F → ℝ) (n a : F → Vec) (x : Vec) (v : V) : ℝ :=
  -(force p s t B n a x v ⬝ᵥ (p v - x)) / ((p v - x) ⬝ᵥ (p v - x))

def GoodPoint (p : V → Vec) (s t : E → V) (n : F → Vec) (x : Vec) : Prop :=
  (∀ f, 1 - n f ⬝ᵥ x ≠ 0) ∧
  (∀ e, edgeCross p s t x e ⬝ᵥ edgeCross p s t x e ≠ 0) ∧
  (∀ v, (p v - x) ⬝ᵥ (p v - x) ≠ 0)

theorem analyticAt_force [DecidableEq V] (p : V → Vec) (s t : E → V)
    (B : E → F → ℝ) (n a : F → Vec) (x : Vec)
    (hx : GoodPoint p s t n x) (v : V) :
    AnalyticAt ℝ (fun y => force p s t B n a y v) x := by
  simpa only [force, Finset.sum_apply, Pi.smul_apply, Pi.mul_apply] using!
    (Finset.univ.analyticAt_fun_sum fun e _ =>
      ((analyticAt_const : AnalyticAt ℝ (fun _ : Vec => incidence s t v e) x).fun_mul
        (analyticAt_edgeWeight p s t B n a x hx.1 e (hx.2.1 e))).fun_smul
          (analyticAt_const : AnalyticAt ℝ (fun _ : Vec => p (t e) - p (s e)) x))

theorem analyticAt_coneWeight [DecidableEq V] (p : V → Vec) (s t : E → V)
    (B : E → F → ℝ) (n a : F → Vec) (x : Vec)
    (hx : GoodPoint p s t n x) (v : V) :
    AnalyticAt ℝ (fun y => coneWeight p s t B n a y v) x := by
  exact (analyticAt_dot (analyticAt_force p s t B n a x hx v)
    (analyticAt_const.sub analyticAt_id)).neg.div
      (analyticAt_dot (analyticAt_const.sub analyticAt_id)
        (analyticAt_const.sub analyticAt_id)) (hx.2.2 v)

/-- The full edge-and-cone coefficient family is real analytic at every good apex. -/
theorem analyticAt_family [DecidableEq V] (p : V → Vec) (s t : E → V)
    (B : E → F → ℝ) (n a : F → Vec) (x : Vec)
    (hx : GoodPoint p s t n x) :
    AnalyticAt ℝ
      (fun y => ((fun e => edgeWeight p s t B n a y e),
                 (fun v => coneWeight p s t B n a y v))) x := by
  exact (AnalyticAt.pi fun e =>
    analyticAt_edgeWeight p s t B n a x hx.1 e (hx.2.1 e)).prod
      (AnalyticAt.pi fun v => analyticAt_coneWeight p s t B n a x hx v)

/-- Real analyticity on the entire set where the geometric denominators do not vanish. -/
theorem analyticOnNhd_family [DecidableEq V] (p : V → Vec) (s t : E → V)
    (B : E → F → ℝ) (n a : F → Vec) :
    AnalyticOnNhd ℝ
      (fun y => ((fun e => edgeWeight p s t B n a y e),
                 (fun v => coneWeight p s t B n a y v)))
      {x | GoodPoint p s t n x} := by
  intro x hx
  exact analyticAt_family p s t B n a x hx

end StressFlex.Rational

/-! ## Source fragment: StressFlex/Geometry.lean -/

open Matrix Filter
open scoped BigOperators Topology

namespace StressFlex.Geometric

abbrev Vec := Fin 3 → ℝ

theorem dot_self_ne_zero {v : Vec} (hv : v ≠ 0) : v ⬝ᵥ v ≠ 0 :=
  fun h => hv (dotProduct_self_eq_zero.mp h)

theorem parallel_of_cross_zero {v w : Vec} (hv : v ≠ 0) (h : v ⨯₃ w = 0) :
    w = ((w ⬝ᵥ v) / (v ⬝ᵥ v)) • v := by
  have hd := dot_self_ne_zero hv
  have heq : (v ⬝ᵥ v) • w = (w ⬝ᵥ v) • v := by
    apply sub_eq_zero.mp
    simpa [h] using (cross_cross_eq_smul_sub_smul v w v).symm
  calc
    w = (v ⬝ᵥ v)⁻¹ • ((v ⬝ᵥ v) • w) := by
      rw [smul_smul, inv_mul_cancel₀ hd, one_smul]
    _ = ((w ⬝ᵥ v) / (v ⬝ᵥ v)) • v := by
      rw [heq, smul_smul]
      congr 1
      ring

theorem perpendicular_decomposition {a b c : Vec} (hq : a ⨯₃ b ≠ 0)
    (ha : a ⬝ᵥ c = 0) (hb : b ⬝ᵥ c = 0) :
    c = ((c ⬝ᵥ (a ⨯₃ b)) / ((a ⨯₃ b) ⬝ᵥ (a ⨯₃ b))) • (a ⨯₃ b) := by
  apply parallel_of_cross_zero hq
  rw [cross_cross_eq_smul_sub_smul, ha, hb]
  simp

theorem cross_ne_zero_of_plane {n a b : Vec}
    (ha : n ⬝ᵥ a = 1) (hb : n ⬝ᵥ b = 1) (hab : a ≠ b) :
    a ⨯₃ b ≠ 0 := by
  have hane : a ≠ 0 := by
    intro h
    simp [h] at ha
  intro h
  have heq := parallel_of_cross_zero hane h
  have hc : (b ⬝ᵥ a) / (a ⬝ᵥ a) = 1 := by
    have ht := congrArg (fun y => n ⬝ᵥ y) heq
    simpa only [dot_smul_right, ha, hb, mul_one] using ht.symm
  rw [hc, one_smul] at heq
  exact hab heq.symm

theorem faceForm_zero (a n : Vec) : Rational.faceForm a n 0 = a := by
  simp [Rational.faceForm]

theorem faceForm_evaluation (a n p x : Vec)
    (hp : n ⬝ᵥ p = 1) (hx : 1 - n ⬝ᵥ x ≠ 0) :
    Rational.faceForm a n x ⬝ᵥ (p - x) = a ⬝ᵥ p := by
  unfold Rational.faceForm
  rw [add_dotProduct, dot_smul_left, dotProduct_sub, dotProduct_sub, hp]
  field_simp [hx]
  ring

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F] [DecidableEq V]

def force (p : V → Vec) (s t : E → V) (w : E → ℝ) (v : V) : Vec :=
  ∑ e, (Rational.incidence s t v e * w e) • (p (t e) - p (s e))

def IsStress (p : V → Vec) (s t : E → V) (x : Vec)
    (w : E → ℝ) (c : V → ℝ) : Prop :=
  ∀ v, c v • (p v - x) + force p s t w v = 0

def IsMotion (p : V → Vec) (s t : E → V) (u : V → Vec) : Prop :=
  (∀ v, p v ⬝ᵥ u v = 0) ∧
  ∀ e, (p (t e) - p (s e)) ⬝ᵥ (u (t e) - u (s e)) = 0

def boundary (B : E → F → ℝ) (a : F → Vec) (e : E) : Vec :=
  ∑ f, B e f • a f

def BoundarySquaredZero (s t : E → V) (B : E → F → ℝ) : Prop :=
  ∀ v f, ∑ e, Rational.incidence s t v e * B e f = 0

def Planes (p : V → Vec) (s t : E → V) (B : E → F → ℝ)
    (n : F → Vec) : Prop :=
  ∀ e f, B e f ≠ 0 → n f ⬝ᵥ p (s e) = 1 ∧ n f ⬝ᵥ p (t e) = 1

theorem sum_incidence (s t : E → V) (e : E) :
    ∑ v, Rational.incidence s t v e = 0 := by
  classical
  simp [Rational.incidence, Finset.sum_sub_distrib]

/-- Equilibrium at the apex follows from the outer vertex equations. -/
theorem apex_equilibrium (p : V → Vec) (s t : E → V) (x : Vec)
    (w : E → ℝ) (c : V → ℝ) (h : IsStress p s t x w c) :
    ∑ v, c v • (p v - x) = 0 := by
  classical
  have hf : ∑ v, force p s t w v = 0 := by
    unfold force
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro e he
    rw [← Finset.sum_smul, ← Finset.sum_mul, sum_incidence, zero_mul, zero_smul]
  have hh : (∑ v, (c v • (p v - x) + force p s t w v)) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    exact h v
  rw [Finset.sum_add_distrib, hf, add_zero] at hh
  exact hh

theorem incidence_cross (p : V → Vec) (s t : E → V) (v : V) (e : E) :
    Rational.incidence s t v e • (p v ⨯₃ (p (t e) - p (s e))) =
      Rational.incidence s t v e • (p (s e) ⨯₃ p (t e)) := by
  by_cases ht : v = t e
  · subst v
    by_cases hs : t e = s e
    · simp [Rational.incidence, hs]
    · ext k
      fin_cases k <;> simp [Rational.incidence, hs, cross_apply] <;> ring
  · by_cases hs : v = s e
    · subst v
      ext k
      fin_cases k <;> simp [Rational.incidence, ht, cross_apply] <;> ring
    · simp [Rational.incidence, ht, hs]

theorem cross_force (p : V → Vec) (s t : E → V) (w : E → ℝ) (v : V) :
    p v ⨯₃ force p s t w v =
      ∑ e, Rational.incidence s t v e • (w e • (p (s e) ⨯₃ p (t e))) := by
  classical
  simp only [force, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro e he
  have h := congrArg (fun z => w e • z) (incidence_cross p s t v e)
  simpa only [smul_smul, mul_comm] using h

theorem force_shift (p : V → Vec) (s t : E → V) (w : E → ℝ) (x : Vec) (v : V) :
    force (fun v => p v - x) s t w v = force p s t w v := by
  unfold force
  apply Finset.sum_congr rfl
  intro e he
  congr 1
  exact sub_sub_sub_cancel_right _ _ _

theorem stress_cycle (p : V → Vec) (s t : E → V) (w : E → ℝ) (c : V → ℝ)
    (h : IsStress p s t 0 w c) (v : V) :
    ∑ e, Rational.incidence s t v e • (w e • (p (s e) ⨯₃ p (t e))) = 0 := by
  have hv := congrArg (fun z => p v ⨯₃ z) (h v)
  simpa only [sub_zero, map_add, map_smul, cross_self, smul_zero,
    zero_add, map_zero, cross_force] using hv

theorem boundary_closed (s t : E → V) (B : E → F → ℝ)
    (hB : BoundarySquaredZero s t B) (a : F → Vec) (v : V) :
    ∑ e, Rational.incidence s t v e • boundary B a e = 0 := by
  classical
  calc
    (∑ e, Rational.incidence s t v e • boundary B a e) =
        ∑ f, (∑ e, Rational.incidence s t v e * B e f) • a f := by
      simp only [boundary, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro f hf
      rw [hB v f, zero_smul]

theorem boundaryForm_evaluation (B : E → F → ℝ) (n a : F → Vec) (x p : Vec) (e : E)
    (hplane : ∀ f, B e f ≠ 0 → n f ⬝ᵥ p = 1)
    (hx : ∀ f, 1 - n f ⬝ᵥ x ≠ 0) :
    Rational.boundaryForm B n a x e ⬝ᵥ (p - x) = boundary B a e ⬝ᵥ p := by
  classical
  simp only [Rational.boundaryForm, boundary, dot_sum_left, dot_smul_left]
  apply Finset.sum_congr rfl
  intro f hf
  by_cases hB : B e f = 0
  · simp [hB]
  · rw [faceForm_evaluation (a f) (n f) p x (hplane f hB) (hx f)]

theorem edgeWeight_reconstruct (p : V → Vec) (s t : E → V)
    (B : E → F → ℝ) (n a : F → Vec) (w : E → ℝ) (x : Vec)
    (hplanes : Planes p s t B n)
    (ha : ∀ e, boundary B a e = w e • (p (s e) ⨯₃ p (t e)))
    (hx : Rational.GoodPoint p s t n x) (e : E) :
    Rational.edgeWeight p s t B n a x e • Rational.edgeCross p s t x e =
      Rational.boundaryForm B n a x e := by
  have hq : Rational.edgeCross p s t x e ≠ 0 := by
    intro hq
    exact hx.2.1 e (by simp [hq])
  have htail : (p (s e) - x) ⬝ᵥ Rational.boundaryForm B n a x e = 0 := by
    rw [dotProduct_comm, boundaryForm_evaluation B n a x (p (s e)) e
      (fun f hf => (hplanes e f hf).1) hx.1, ha e, dot_smul_left]
    simp only [dotProduct_comm (p (s e) ⨯₃ p (t e)), dot_self_cross, mul_zero]
  have hhead : (p (t e) - x) ⬝ᵥ Rational.boundaryForm B n a x e = 0 := by
    rw [dotProduct_comm, boundaryForm_evaluation B n a x (p (t e)) e
      (fun f hf => (hplanes e f hf).2) hx.1, ha e, dot_smul_left]
    simp only [dotProduct_comm (p (s e) ⨯₃ p (t e)), dot_cross_self, mul_zero]
  exact (perpendicular_decomposition hq htail hhead).symm

theorem moved_isStress (p : V → Vec) (s t : E → V)
    (B : E → F → ℝ) (n a : F → Vec) (w : E → ℝ) (x : Vec)
    (hplanes : Planes p s t B n) (hB : BoundarySquaredZero s t B)
    (ha : ∀ e, boundary B a e = w e • (p (s e) ⨯₃ p (t e)))
    (hx : Rational.GoodPoint p s t n x) :
    IsStress p s t x (Rational.edgeWeight p s t B n a x)
      (Rational.coneWeight p s t B n a x) := by
  intro v
  have hcross : (p v - x) ⨯₃ Rational.force p s t B n a x v = 0 := by
    change (p v - x) ⨯₃ force p s t (Rational.edgeWeight p s t B n a x) v = 0
    rw [← force_shift p s t (Rational.edgeWeight p s t B n a x) x v]
    change (fun v => p v - x) v ⨯₃ force (fun v => p v - x) s t
      (Rational.edgeWeight p s t B n a x) v = 0
    rw [cross_force (fun v => p v - x) s t (Rational.edgeWeight p s t B n a x) v]
    have he := edgeWeight_reconstruct p s t B n a w x hplanes ha hx
    change (∑ e, Rational.incidence s t v e •
      (Rational.edgeWeight p s t B n a x e • Rational.edgeCross p s t x e)) = 0
    simp_rw [he]
    exact boundary_closed s t B hB (fun f => Rational.faceForm (a f) (n f) x) v
  have hp : p v - x ≠ 0 := by
    intro h
    exact hx.2.2 v (by simp [h])
  have hpar := parallel_of_cross_zero hp hcross
  change Rational.coneWeight p s t B n a x v • (p v - x) +
    Rational.force p s t B n a x v = 0
  unfold Rational.coneWeight
  rw [neg_div, neg_smul, ← hpar, neg_add_cancel]

theorem edgeWeight_zero (p : V → Vec) (s t : E → V)
    (B : E → F → ℝ) (n a : F → Vec) (w : E → ℝ)
    (ha : ∀ e, boundary B a e = w e • (p (s e) ⨯₃ p (t e)))
    (hq : ∀ e, p (s e) ⨯₃ p (t e) ≠ 0) (e : E) :
    Rational.edgeWeight p s t B n a 0 e = w e := by
  have hd := dot_self_ne_zero (hq e)
  unfold Rational.edgeWeight Rational.edgeCross Rational.boundaryForm
  simp only [sub_zero, faceForm_zero]
  change (boundary B a e ⬝ᵥ (p (s e) ⨯₃ p (t e))) /
    ((p (s e) ⨯₃ p (t e)) ⬝ᵥ (p (s e) ⨯₃ p (t e))) = w e
  rw [ha e, dot_smul_left]
  exact mul_div_cancel_right₀ (w e) hd

theorem cone_unique (p : V → Vec) (s t : E → V) (x : Vec)
    (w : E → ℝ) (c d : V → ℝ)
    (hc : IsStress p s t x w c) (hd : IsStress p s t x w d)
    (hp : ∀ v, p v - x ≠ 0) : c = d := by
  funext v
  have heq : c v • (p v - x) = d v • (p v - x) :=
    (eq_neg_of_add_eq_zero_left (hc v)).trans (eq_neg_of_add_eq_zero_left (hd v)).symm
  have hz : (c v - d v) • (p v - x) = 0 := by
    rw [sub_smul, heq, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right (hp v))

theorem goodPoint_zero (p : V → Vec) (s t : E → V) (n : F → Vec)
    (hp : ∀ v, p v ≠ 0) (hq : ∀ e, p (s e) ⨯₃ p (t e) ≠ 0) :
    Rational.GoodPoint p s t n 0 := by
  refine ⟨fun f => by simp, fun e => ?_, fun v => ?_⟩
  · simpa only [Rational.edgeCross, sub_zero] using dot_self_ne_zero (hq e)
  · simpa only [sub_zero] using dot_self_ne_zero (hp v)

theorem eventually_goodPoint (p : V → Vec) (s t : E → V) (n : F → Vec)
    (hp : ∀ v, p v ≠ 0) (hq : ∀ e, p (s e) ⨯₃ p (t e) ≠ 0) :
    ∀ᶠ x in 𝓝 (0 : Vec), Rational.GoodPoint p s t n x := by
  have h0 := goodPoint_zero p s t n hp hq
  have hfaces (f : F) : ∀ᶠ x in 𝓝 (0 : Vec), 1 - n f ⬝ᵥ x ≠ 0 :=
    (analyticAt_const.sub (Rational.analyticAt_dot analyticAt_const analyticAt_id)).continuousAt.eventually_ne
      (h0.1 f)
  have hedges (e : E) : ∀ᶠ x in 𝓝 (0 : Vec),
      Rational.edgeCross p s t x e ⬝ᵥ Rational.edgeCross p s t x e ≠ 0 :=
    (Rational.analyticAt_dot (Rational.analyticAt_edgeCross p s t 0 e)
      (Rational.analyticAt_edgeCross p s t 0 e)).continuousAt.eventually_ne (h0.2.1 e)
  have hvertices (v : V) : ∀ᶠ x in 𝓝 (0 : Vec), (p v - x) ⬝ᵥ (p v - x) ≠ 0 :=
    (Rational.analyticAt_dot (analyticAt_const.sub analyticAt_id)
      (analyticAt_const.sub analyticAt_id)).continuousAt.eventually_ne (h0.2.2 v)
  filter_upwards [Filter.eventually_all.mpr hfaces,
    Filter.eventually_all.mpr hedges, Filter.eventually_all.mpr hvertices] with x hf he hv
  exact ⟨hf, he, hv⟩

theorem coneWeight_zero (p : V → Vec) (s t : E → V)
    (B : E → F → ℝ) (n a : F → Vec) (w : E → ℝ) (c : V → ℝ)
    (hplanes : Planes p s t B n) (hB : BoundarySquaredZero s t B)
    (ha : ∀ e, boundary B a e = w e • (p (s e) ⨯₃ p (t e)))
    (hp : ∀ v, p v ≠ 0) (hq : ∀ e, p (s e) ⨯₃ p (t e) ≠ 0)
    (hc : IsStress p s t 0 w c) :
    Rational.coneWeight p s t B n a 0 = c := by
  have heq : Rational.edgeWeight p s t B n a 0 = w :=
    funext (edgeWeight_zero p s t B n a w ha hq)
  have hnew := moved_isStress p s t B n a w 0 hplanes hB ha (goodPoint_zero p s t n hp hq)
  rw [heq] at hnew
  exact cone_unique p s t 0 w _ _ hnew hc (by simpa only [sub_zero] using hp)


theorem sum_incidence_smul (s t : E → V) (u : V → Vec) (e : E) :
    ∑ v, Rational.incidence s t v e • u v = u (t e) - u (s e) := by
  classical
  simp [Rational.incidence, sub_smul, Finset.sum_sub_distrib]

/-- The ordinary virtual-work identity for an arbitrarily oriented finite graph. -/
theorem virtual_work (p u : V → Vec) (s t : E → V) (w : E → ℝ)
    (hu : ∀ e, (p (t e) - p (s e)) ⬝ᵥ (u (t e) - u (s e)) = 0) :
    ∑ v, force p s t w v ⬝ᵥ u v = 0 := by
  classical
  calc
    (∑ v, force p s t w v ⬝ᵥ u v) =
        ∑ e, w e * ((p (t e) - p (s e)) ⬝ᵥ
          (∑ v, Rational.incidence s t v e • u v)) := by
      simp only [force, dot_sum_left, dot_smul_left, dot_sum_right,
        dot_smul_right, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _ = 0 := by simp only [sum_incidence_smul, hu, mul_zero, Finset.sum_const_zero]

/-- Every stress at a moved apex annihilates the motion after pairing with the displacement. -/
theorem moved_pairing (p u : V → Vec) (s t : E → V) (w : E → ℝ)
    (c : V → ℝ) (x : Vec) (hu : IsMotion p s t u) (hc : IsStress p s t x w c) :
    x ⬝ᵥ (∑ v, c v • u v) = 0 := by
  classical
  have hsum : (∑ v, (c v • (p v - x) + force p s t w v) ⬝ᵥ u v) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    rw [hc v, zero_dotProduct]
  simp only [add_dotProduct, Finset.sum_add_distrib, virtual_work p u s t w hu.2,
    add_zero, dot_smul_left, sub_dotProduct, hu.1, zero_sub,
    mul_neg, Finset.sum_neg_distrib, neg_eq_zero] at hsum
  simpa only [dot_sum_right, dot_smul_right] using hsum

/-- The geometric conclusion once an actual cellular boundary has supplied the face chain. -/
theorem orthogonality_of_potentials (p u : V → Vec) (s t : E → V)
    (B : E → F → ℝ) (n a : F → Vec) (w : E → ℝ) (c : V → ℝ)
    (hplanes : Planes p s t B n) (hB : BoundarySquaredZero s t B)
    (ha : ∀ e, boundary B a e = w e • (p (s e) ⨯₃ p (t e)))
    (hp : ∀ v, p v ≠ 0) (hq : ∀ e, p (s e) ⨯₃ p (t e) ≠ 0)
    (hc : IsStress p s t 0 w c) (hu : IsMotion p s t u) :
    ∑ v, c v • u v = 0 := by
  have hz := goodPoint_zero p s t n hp hq
  have heq := coneWeight_zero p s t B n a w c hplanes hB ha hp hq hc
  have hcont : ContinuousAt (fun x => ∑ v, Rational.coneWeight p s t B n a x v • u v) 0 := by
    apply tendsto_finsetSum
    intro v hv
    exact (Rational.analyticAt_coneWeight p s t B n a 0 hz v).continuousAt.smul continuousAt_const
  have hpair : ∀ᶠ x in 𝓝 (0 : Vec),
      x ⬝ᵥ (∑ v, Rational.coneWeight p s t B n a x v • u v) = 0 := by
    filter_upwards [eventually_goodPoint p s t n hp hq] with x hx
    exact moved_pairing p u s t (Rational.edgeWeight p s t B n a x)
      (Rational.coneWeight p s t B n a x) x hu
      (moved_isStress p s t B n a w x hplanes hB ha hx)
  simpa only [heq] using continuous_pairing_vanishes _ hcont hpair

end StressFlex.Geometric

/-! ## Source fragment: StressFlex/SphericalHomology.lean -/

open CategoryTheory Limits Topology Topology.RelCWComplex
open scoped BigOperators

namespace StressFlex.Cellular

variable {X : Type} [TopologicalSpace X] [T2Space X]
  (C : Set X) [CWComplex C]

abbrev Coeff : ModuleCat.{0} ℝ := ModuleCat.of ℝ ℝ

/-- Coordinates in the actual cellular chain group, through TauCeti's proved cellular basis. -/
def coordinates (n : ℕ) [Fintype (cell C n)] :
    (TauCeti.cellularChainComplex C Coeff).X n ≃ₗ[ℝ] (cell C n → ℝ) :=
  (eqToIso (TauCeti.cellularChainComplex_X C Coeff n)).toLinearEquiv ≪≫ₗ
    (TauCeti.cellularChainBasis C ℝ n).repr ≪≫ₗ
      Finsupp.linearEquivFunOnFinite ℝ ℝ (cell C n)

theorem coordinates_d (n : ℕ) [Fintype (cell C n)] [Fintype (cell C (n + 1))]
    (x : (TauCeti.cellularChainComplex C Coeff).X (n + 1)) (i : cell C n) :
    coordinates C n ((TauCeti.cellularChainComplex C Coeff).d (n + 1) n x) i =
      ∑ j, coordinates C (n + 1) x j * TauCeti.cellularIncidence C ℝ n i j := by
  classical
  change (TauCeti.cellularChainBasis C ℝ n).repr
      (eqToHom (TauCeti.cellularChainComplex_X C Coeff n)
        ((TauCeti.cellularChainComplex C Coeff).d (n + 1) n x)) i =
    ∑ j, (TauCeti.cellularChainBasis C ℝ (n + 1)).repr
      (eqToHom (TauCeti.cellularChainComplex_X C Coeff (n + 1)) x) j *
        TauCeti.cellularIncidence C ℝ n i j
  rw [TauCeti.cellularChainComplex_d]
  simp only [← ConcreteCategory.comp_apply, Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id]
  rw [ConcreteCategory.comp_apply, TauCeti.cellularChainBasis_repr_differential_apply]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j hj hnot
  rw [Finsupp.notMem_support_iff.mp hnot, zero_mul]

/-- The coefficient identity A B = 0 is inherited from the kernel-checked cellular differential. -/
theorem sum_incidence_mul (n : ℕ) [Fintype (cell C (n + 1))]
    (i : cell C n) (f : cell C (n + 2)) :
    ∑ e, TauCeti.cellularIncidence C ℝ n i e *
      TauCeti.cellularIncidence C ℝ (n + 1) e f = 0 := by
  classical
  have h := TauCeti.sum_cellularIncidence_mul C ℝ n i f
  have hs : (∑ e ∈ (TauCeti.cellularBoundaryColumn C ℝ (n + 1) f).support,
      TauCeti.cellularIncidence C ℝ (n + 1) e f *
      TauCeti.cellularIncidence C ℝ n i e) =
      ∑ e, TauCeti.cellularIncidence C ℝ (n + 1) e f *
        TauCeti.cellularIncidence C ℝ n i e := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e he hnot
    have hz := Finsupp.notMem_support_iff.mp hnot
    have hz' : TauCeti.cellularIncidence C ℝ (n + 1) e f = 0 := by
      simpa only [TauCeti.cellularBoundaryColumn_apply] using hz
    rw [hz', zero_mul]
  rw [hs] at h
  simpa only [mul_comm] using h

variable [CWComplex (Set.univ : Set X)]

/-- H₁ of an actual space homeomorphic to S² vanishes, using singular homology of spheres. -/
theorem isZero_cellular_homology_one (hS : X ≃ₜ TopCat.sphere.{0} 2) :
    IsZero ((TauCeti.cellularChainComplex (Set.univ : Set X) Coeff).homology 1) := by
  let H := (AlgebraicTopology.singularHomologyFunctor.{0} (ModuleCat.{0} ℝ) 1).obj Coeff
  have hzero : IsZero (H.obj (TopCat.sphere.{0} 2)) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    apply (Module.finrank_zero_iff (R := ℝ)).mp
    simpa [H] using (ModuleCat.finrank_singularHomology_sphere Coeff 2 1)
  exact hzero.of_iso
    (TauCeti.cellularSingularHomologyIsoUniv Coeff 1 ≪≫
      H.mapIso (TopCat.isoOfHomeo hS))

/-- Every coordinate 1-cycle on a genuine CW sphere is the boundary of a 2-chain. -/
theorem exists_face_chain
    [Fintype (cell (Set.univ : Set X) 0)]
    [Fintype (cell (Set.univ : Set X) 1)]
    [Fintype (cell (Set.univ : Set X) 2)]
    (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (b : cell (Set.univ : Set X) 1 → ℝ)
    (hb : ∀ v, ∑ e, TauCeti.cellularIncidence (Set.univ : Set X) ℝ 0 v e * b e = 0) :
    ∃ a : cell (Set.univ : Set X) 2 → ℝ,
      ∀ e, ∑ f, TauCeti.cellularIncidence (Set.univ : Set X) ℝ 1 e f * a f = b e := by
  classical
  let K := TauCeti.cellularChainComplex (Set.univ : Set X) Coeff
  let y : K.X 1 := (coordinates (Set.univ : Set X) 1).symm b
  have hy : K.d 1 0 y = 0 := by
    apply (coordinates (Set.univ : Set X) 0).injective
    ext v
    rw [map_zero]
    change coordinates (Set.univ : Set X) 0 (K.d 1 0 y) v = 0
    rw [coordinates_d]
    simpa only [y, LinearEquiv.apply_symm_apply, mul_comm] using hb v
  have hex : K.ExactAt 1 :=
    (K.exactAt_iff_isZero_homology 1).mpr (isZero_cellular_homology_one hS)
  have hex' : (K.sc' 2 1 0).Exact :=
    (K.exactAt_iff' 2 1 0 (by simp) (by simp)).mp hex
  obtain ⟨a, ha⟩ := (ShortComplex.moduleCat_exact_iff _).mp hex' y hy
  refine ⟨coordinates (Set.univ : Set X) 2 a, fun e => ?_⟩
  have hc := congrArg (fun z => coordinates (Set.univ : Set X) 1 z e) ha
  change coordinates (Set.univ : Set X) 1 (K.d 2 1 a) e =
    coordinates (Set.univ : Set X) 1 y e at hc
  rw [coordinates_d] at hc
  simpa only [y, LinearEquiv.apply_symm_apply, mul_comm] using hc

end StressFlex.Cellular

/-! ## Source fragment: StressFlex/Sphere.lean -/

open CategoryTheory Limits Topology Topology.RelCWComplex Matrix
open scoped BigOperators

namespace StressFlex.Spherical

variable {X : Type} [TopologicalSpace X] [T2Space X]
  [CWComplex (Set.univ : Set X)]

abbrev Vertex (X : Type) [TopologicalSpace X] [CWComplex (Set.univ : Set X)] :=
  cell (Set.univ : Set X) 0
abbrev Edge (X : Type) [TopologicalSpace X] [CWComplex (Set.univ : Set X)] :=
  cell (Set.univ : Set X) 1
abbrev Face (X : Type) [TopologicalSpace X] [CWComplex (Set.univ : Set X)] :=
  cell (Set.univ : Set X) 2

def vertexPoint (v : Vertex X) : X := map 0 v ![]

/-- The actual zero-cell points, with the evaluation formula exposed for endpoint transport.
The proof is the zero-skeleton bijection, using the CW union and disjointness properties. -/
def vertexEquiv : Vertex X ≃ ↑(skeletonLT (Set.univ : Set X) ((1 : ℕ) : ℕ∞)) :=
  Equiv.ofBijective (fun v => ⟨vertexPoint v,
    closedCell_subset_skeletonLT 0 v (by
      simpa only [vertexPoint, Matrix.zero_empty] using map_zero_mem_closedCell 0 v)⟩) (by
    constructor
    · intro i j h
      exact injective_map_zero (Set.univ : Set X) (congrArg Subtype.val h)
    · rintro ⟨x, hx⟩
      have hs : (skeletonLT (Set.univ : Set X) ((1 : ℕ) : ℕ∞) : Set X) =
          ⋃ i : Vertex X, closedCell 0 i := by
        simpa [CWComplex.skeletonLT_zero_eq_empty] using
          (skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ
            (C := (Set.univ : Set X)) 0).symm
      change x ∈ (skeletonLT (Set.univ : Set X) ((1 : ℕ) : ℕ∞) : Set X) at hx
      rw [hs] at hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨i, hi⟩ := hx
      rw [closedCell_zero_eq_singleton] at hi
      exact ⟨i, Subtype.ext hi.symm⟩)

@[simp] theorem vertexEquiv_apply (v : Vertex X) :
    (vertexEquiv v : X) = vertexPoint v := rfl

def tail (e : Edge X) : Vertex X :=
  vertexEquiv.symm (TauCeti.cellAttachingMap e TauCeti.spherePlus)

def head (e : Edge X) : Vertex X :=
  vertexEquiv.symm (TauCeti.cellAttachingMap e TauCeti.sphereMinus)

theorem vertexPoint_tail (e : Edge X) :
    vertexPoint (tail e) = (TauCeti.cellAttachingMap e TauCeti.spherePlus : X) := by
  simpa only [vertexEquiv_apply, tail] using!
    congrArg Subtype.val (vertexEquiv.apply_symm_apply
      (TauCeti.cellAttachingMap e TauCeti.spherePlus))

theorem vertexPoint_head (e : Edge X) :
    vertexPoint (head e) = (TauCeti.cellAttachingMap e TauCeti.sphereMinus : X) := by
  simpa only [vertexEquiv_apply, head] using!
    congrArg Subtype.val (vertexEquiv.apply_symm_apply
      (TauCeti.cellAttachingMap e TauCeti.sphereMinus))

theorem vertexPoint_injective : Function.Injective (vertexPoint : Vertex X → X) :=
  injective_map_zero (Set.univ : Set X)

theorem incidence_zero [DecidableEq (Vertex X)] (v : Vertex X) (e : Edge X) :
    TauCeti.cellularIncidence (Set.univ : Set X) ℝ 0 v e =
      Rational.incidence tail head v e := by
  have hm : (TauCeti.cellAttachingMap e TauCeti.sphereMinus : X) ∈ openCell 0 v ↔
      v = head e := by
    rw [← vertexPoint_head, openCell_zero_eq_singleton, Set.mem_singleton_iff]
    change map 0 (head e) ![] = map 0 v ![] ↔ v = head e
    rw [map_zero_eq_self_iff]
    exact eq_comm
  have hp : (TauCeti.cellAttachingMap e TauCeti.spherePlus : X) ∈ openCell 0 v ↔
      v = tail e := by
    rw [← vertexPoint_tail, openCell_zero_eq_singleton, Set.mem_singleton_iff]
    change map 0 (tail e) ![] = map 0 v ![] ↔ v = tail e
    rw [map_zero_eq_self_iff]
    exact eq_comm
  simpa only [hm, hp, Rational.incidence] using
    TauCeti.cellularIncidence_zero (Set.univ : Set X) ℝ v e

theorem endpoint_mem_closedEdge (e : Edge X) :
    vertexPoint (tail e) ∈ closedCell 1 e ∧ vertexPoint (head e) ∈ closedCell 1 e := by
  constructor
  · rw [vertexPoint_tail]
    apply cellFrontier_subset_closedCell 1 e
    rw [← TauCeti.range_cellAttachingMap]
    exact ⟨TauCeti.spherePlus, rfl⟩
  · rw [vertexPoint_head]
    apply cellFrontier_subset_closedCell 1 e
    rw [← TauCeti.range_cellAttachingMap]
    exact ⟨TauCeti.sphereMinus, rfl⟩

/-- A nonzero genuine boundary coefficient forces the entire edge into the face closure. -/
theorem closedEdge_subset_closedFace (e : Edge X) (f : Face X)
    (h : TauCeti.cellularIncidence (Set.univ : Set X) ℝ 1 e f ≠ 0) :
    closedCell 1 e ⊆ closedCell 2 f := by
  have ho : openCell 1 e ⊆ closedCell 2 f := by
    intro x hx
    apply cellFrontier_subset_closedCell 2 f
    by_contra hmiss
    exact h (TauCeti.cellularIncidence_eq_zero_of_not_mem_cellFrontier
      (Set.univ : Set X) ℝ
      ⟨x, openCell_subset_skeletonLT 1 e hx⟩ hx f hmiss)
  rw [← closure_openCell_eq_closedCell]
  exact isClosed_closedCell.closure_subset_iff.mpr ho

theorem tail_ne_head_of_injective (e : Edge X)
    (h : Function.Injective (TauCeti.cellAttachingMap e)) : tail e ≠ head e := by
  intro heq
  have hpoint := congrArg vertexPoint heq
  rw [vertexPoint_tail, vertexPoint_head] at hpoint
  exact TauCeti.sphereMinus_ne_spherePlus (h (Subtype.ext hpoint)).symm

/-- For a one-cell, the attaching sphere has precisely two points, so injectivity is
exactly the simple graph's prohibition of loops. -/
theorem edge_attaching_injective_iff (e : Edge X) :
    Function.Injective (TauCeti.cellAttachingMap e) ↔ tail e ≠ head e := by
  refine ⟨tail_ne_head_of_injective e, ?_⟩
  intro h p q hpq
  rcases TauCeti.eq_sphereMinus_or_eq_spherePlus p with rfl | rfl <;>
    rcases TauCeti.eq_sphereMinus_or_eq_spherePlus q with rfl | rfl
  · rfl
  · exfalso
    apply h
    apply vertexPoint_injective
    rw [vertexPoint_tail, vertexPoint_head]
    exact (congrArg Subtype.val hpq).symm
  · exfalso
    apply h
    apply vertexPoint_injective
    rw [vertexPoint_tail, vertexPoint_head]
    exact congrArg Subtype.val hpq
  · rfl

/-- Geometric vertex positions are independent of the topological realization of the surface.
No embedding into Euclidean space is part of this data. -/
structure NormalizedRealization where
  position : Vertex X → Geometric.Vec
  injective_position : Function.Injective position
  normal : Face X → Geometric.Vec
  planar : ∀ (f : Face X) (v : Vertex X), vertexPoint v ∈ closedCell 2 f → normal f ⬝ᵥ position v = 1
  vertex_in_face : ∀ v : Vertex X, ∃ f : Face X, vertexPoint v ∈ closedCell 2 f
  edge_in_face : ∀ e : Edge X, ∃ f : Face X, closedCell 1 e ⊆ closedCell 2 f
  edge_injective : ∀ e : Edge X, Function.Injective (TauCeti.cellAttachingMap e)

variable [Fintype (Vertex X)] [Fintype (Edge X)] [Fintype (Face X)]
  [DecidableEq (Vertex X)]

def faceBoundary (e : Edge X) (f : Face X) : ℝ :=
  TauCeti.cellularIncidence (Set.univ : Set X) ℝ 1 e f

theorem boundarySquaredZero :
    Geometric.BoundarySquaredZero (tail : Edge X → Vertex X) head faceBoundary := by
  intro v f
  simpa only [Geometric.BoundarySquaredZero, faceBoundary, ← incidence_zero] using
    Cellular.sum_incidence_mul (Set.univ : Set X) 0 v f

theorem positions_ne_zero (P : NormalizedRealization (X := X)) (v : Vertex X) :
    P.position v ≠ 0 := by
  obtain ⟨f, hf⟩ := P.vertex_in_face v
  have hp := P.planar f v hf
  intro hz
  simp [hz] at hp

theorem edge_cross_ne_zero (P : NormalizedRealization (X := X)) (e : Edge X) :
    P.position (tail e) ⨯₃ P.position (head e) ≠ 0 := by
  obtain ⟨f, hf⟩ := P.edge_in_face e
  apply Geometric.cross_ne_zero_of_plane
    (P.planar f _ (hf (endpoint_mem_closedEdge e).1))
    (P.planar f _ (hf (endpoint_mem_closedEdge e).2))
  exact fun h => tail_ne_head_of_injective e (P.edge_injective e) (P.injective_position h)

theorem boundary_planes (P : NormalizedRealization (X := X)) :
    Geometric.Planes P.position tail head faceBoundary P.normal := by
  intro e f h
  have hf := closedEdge_subset_closedFace e f h
  exact ⟨P.planar f _ (hf (endpoint_mem_closedEdge e).1),
    P.planar f _ (hf (endpoint_mem_closedEdge e).2)⟩

/-- The vector face potential is derived from H₁(S²;ℝ)=0, not assumed. -/
theorem exists_vector_face_chain (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (P : NormalizedRealization (X := X)) (w : Edge X → ℝ) (c : Vertex X → ℝ)
    (hc : Geometric.IsStress P.position tail head 0 w c) :
    ∃ a : Face X → Geometric.Vec, ∀ e,
      Geometric.boundary faceBoundary a e =
        w e • (P.position (tail e) ⨯₃ P.position (head e)) := by
  classical
  have hcycle := Geometric.stress_cycle P.position tail head w c hc
  have hex (k : Fin 3) :
      ∃ a : Face X → ℝ, ∀ e, ∑ f, faceBoundary e f * a f =
        (w e • (P.position (tail e) ⨯₃ P.position (head e))) k := by
    apply Cellular.exists_face_chain hS
    intro v
    have h := congrArg (fun z : Geometric.Vec => z k) (hcycle v)
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, incidence_zero] using h
  choose a ha using hex
  refine ⟨fun f k => a k f, fun e => ?_⟩
  ext k
  simpa only [Geometric.boundary, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using ha k e

/-- The sphere conclusion with an actual topological sphere and its actual cellular incidence. -/
theorem stress_flex_orthogonality (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (P : NormalizedRealization (X := X)) (w : Edge X → ℝ) (c : Vertex X → ℝ)
    (u : Vertex X → Geometric.Vec)
    (hc : Geometric.IsStress P.position tail head 0 w c)
    (hu : Geometric.IsMotion P.position tail head u) :
    ∑ v, c v • u v = 0 := by
  obtain ⟨a, ha⟩ := exists_vector_face_chain hS P w c hc
  exact Geometric.orthogonality_of_potentials P.position u tail head faceBoundary P.normal a w c
    (boundary_planes P) boundarySquaredZero ha (positions_ne_zero P) (edge_cross_ne_zero P) hc hu

/-- The same face-chain construction yields an analytic extension of every given stress. -/
theorem analytic_stress_extension (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (P : NormalizedRealization (X := X)) (w : Edge X → ℝ) (c : Vertex X → ℝ)
    (hc : Geometric.IsStress P.position tail head 0 w c) :
    ∃ (W : Geometric.Vec → Edge X → ℝ) (C : Geometric.Vec → Vertex X → ℝ),
      W 0 = w ∧ C 0 = c ∧ AnalyticAt ℝ W 0 ∧ AnalyticAt ℝ C 0 ∧
        ∀ᶠ x in nhds 0, Geometric.IsStress P.position tail head x (W x) (C x) := by
  obtain ⟨a, ha⟩ := exists_vector_face_chain hS P w c hc
  let W := Rational.edgeWeight P.position tail head faceBoundary P.normal a
  let C := Rational.coneWeight P.position tail head faceBoundary P.normal a
  have h0 := Geometric.goodPoint_zero P.position tail head P.normal
    (positions_ne_zero P) (edge_cross_ne_zero P)
  refine ⟨W, C, funext (Geometric.edgeWeight_zero _ _ _ _ _ _ _ ha (edge_cross_ne_zero P)),
    Geometric.coneWeight_zero _ _ _ _ _ _ _ _ (boundary_planes P) boundarySquaredZero
      ha (positions_ne_zero P) (edge_cross_ne_zero P) hc, ?_, ?_, ?_⟩
  · apply AnalyticAt.pi
    intro e
    exact Rational.analyticAt_edgeWeight _ _ _ _ _ _ _ h0.1 e (h0.2.1 e)
  · apply AnalyticAt.pi
    intro v
    exact Rational.analyticAt_coneWeight _ _ _ _ _ _ _ h0 v
  · filter_upwards [Geometric.eventually_goodPoint P.position tail head P.normal
      (positions_ne_zero P) (edge_cross_ne_zero P)] with x hx
    exact Geometric.moved_isStress _ _ _ _ _ _ w x (boundary_planes P)
      boundarySquaredZero ha hx



/-- Every stress extends analytically on an actual open neighbourhood, with all equilibrium
equations holding at each apex in that neighbourhood. -/
theorem analytic_stress_extension_on_open (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (P : NormalizedRealization (X := X)) (w : Edge X → ℝ) (c : Vertex X → ℝ)
    (hc : Geometric.IsStress P.position tail head 0 w c) :
    ∃ (U : Set Geometric.Vec) (W : Geometric.Vec → Edge X → ℝ)
      (C : Geometric.Vec → Vertex X → ℝ),
      IsOpen U ∧ (0 : Geometric.Vec) ∈ U ∧ W 0 = w ∧ C 0 = c ∧
      AnalyticOnNhd ℝ W U ∧ AnalyticOnNhd ℝ C U ∧
      ∀ x ∈ U, Geometric.IsStress P.position tail head x (W x) (C x) := by
  obtain ⟨a, ha⟩ := exists_vector_face_chain hS P w c hc
  let W := Rational.edgeWeight P.position tail head faceBoundary P.normal a
  let C := Rational.coneWeight P.position tail head faceBoundary P.normal a
  have hgood := Geometric.eventually_goodPoint P.position tail head P.normal
    (positions_ne_zero P) (edge_cross_ne_zero P)
  obtain ⟨U, hUG, hUo, h0U⟩ := mem_nhds_iff.mp hgood
  refine ⟨U, W, C, hUo, h0U,
    funext (Geometric.edgeWeight_zero _ _ _ _ _ _ _ ha (edge_cross_ne_zero P)),
    Geometric.coneWeight_zero _ _ _ _ _ _ _ _ (boundary_planes P) boundarySquaredZero
      ha (positions_ne_zero P) (edge_cross_ne_zero P) hc, ?_, ?_, ?_⟩
  · intro x hx
    exact AnalyticAt.pi fun e =>
      Rational.analyticAt_edgeWeight _ _ _ _ _ _ _ (hUG hx).1 e ((hUG hx).2.1 e)
  · intro x hx
    exact AnalyticAt.pi fun v => Rational.analyticAt_coneWeight _ _ _ _ _ _ _ (hUG hx) v
  · intro x hx
    exact Geometric.moved_isStress _ _ _ _ _ _ w x (boundary_planes P)
      boundarySquaredZero ha (hUG hx)


/-- The unnormalised geometry: affine face planes and a separate vertex map into ℝ³. -/
structure AffineRealization where
  position : Vertex X → Geometric.Vec
  injective_position : Function.Injective position
  normal : Face X → Geometric.Vec
  level : Face X → ℝ
  planar : ∀ (f : Face X) (v : Vertex X), vertexPoint v ∈ closedCell 2 f → normal f ⬝ᵥ position v = level f
  vertex_in_face : ∀ v : Vertex X, ∃ f : Face X, vertexPoint v ∈ closedCell 2 f
  edge_in_face : ∀ e : Edge X, ∃ f : Face X, closedCell 1 e ⊆ closedCell 2 f
  edge_injective : ∀ e : Edge X, Function.Injective (TauCeti.cellAttachingMap e)

/-- Translation to the apex and normalization of each genuine affine face plane. -/
def AffineRealization.normalized (P : AffineRealization (X := X)) (x : Geometric.Vec)
    (hx : ∀ f, P.normal f ⬝ᵥ x ≠ P.level f) : NormalizedRealization (X := X) where
  position := fun v => P.position v - x
  injective_position := fun _ _ h => P.injective_position (sub_left_inj.mp h)
  normal := fun f => (P.level f - P.normal f ⬝ᵥ x)⁻¹ • P.normal f
  planar := by
    intro f v hv
    rw [dot_smul_left, dotProduct_sub, P.planar f v hv]
    exact inv_mul_cancel₀ (sub_ne_zero.mpr (hx f).symm)
  vertex_in_face := P.vertex_in_face
  edge_in_face := P.edge_in_face
  edge_injective := P.edge_injective

/-- The sphere conclusion at an arbitrary admissible apex, without an embedding hypothesis. -/
theorem stress_flex_orthogonality_at_apex (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (P : AffineRealization (X := X)) (x : Geometric.Vec)
    (hx : ∀ f, P.normal f ⬝ᵥ x ≠ P.level f)
    (w : Edge X → ℝ) (c : Vertex X → ℝ) (u : Vertex X → Geometric.Vec)
    (hc : Geometric.IsStress P.position tail head x w c)
    (hu : Geometric.IsMotion (fun v => P.position v - x) tail head u) :
    ∑ v, c v • u v = 0 := by
  apply stress_flex_orthogonality hS (P.normalized x hx) w c u
  · intro v
    dsimp only [AffineRealization.normalized]
    change c v • (P.position v - x - 0) +
      Geometric.force (fun v => P.position v - x) tail head w v = 0
    rw [sub_zero, Geometric.force_shift]
    exact hc v
  · simpa only [AffineRealization.normalized] using hu


/-- Normalisation commutes exactly with moving the apex by a displacement. -/
theorem AffineRealization.isStress_normalized_iff
    (P : AffineRealization (X := X)) (x t : Geometric.Vec)
    (hx : ∀ f, P.normal f ⬝ᵥ x ≠ P.level f)
    (w : Edge X → ℝ) (c : Vertex X → ℝ) :
    Geometric.IsStress (P.normalized x hx).position tail head t w c ↔
      Geometric.IsStress P.position tail head (x + t) w c := by
  simp only [Geometric.IsStress, AffineRealization.normalized,
    Geometric.force_shift, sub_add_eq_sub_sub]

/-- The real-analytic continuation assertion of Proposition 3 at any admissible apex. -/
theorem analytic_stress_extension_at_apex (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (P : AffineRealization (X := X)) (x : Geometric.Vec)
    (hx : ∀ f, P.normal f ⬝ᵥ x ≠ P.level f)
    (w : Edge X → ℝ) (c : Vertex X → ℝ)
    (hc : Geometric.IsStress P.position tail head x w c) :
    ∃ (U : Set Geometric.Vec) (W : Geometric.Vec → Edge X → ℝ)
      (C : Geometric.Vec → Vertex X → ℝ),
      IsOpen U ∧ x ∈ U ∧ W x = w ∧ C x = c ∧
      AnalyticOnNhd ℝ W U ∧ AnalyticOnNhd ℝ C U ∧
      ∀ y ∈ U, Geometric.IsStress P.position tail head y (W y) (C y) := by
  have hc' : Geometric.IsStress (P.normalized x hx).position tail head 0 w c := by
    rw [P.isStress_normalized_iff x 0 hx w c, add_zero]
    exact hc
  obtain ⟨U, W, C, hU, h0, hW, hC, hWA, hCA, hSstress⟩ :=
    analytic_stress_extension_on_open hS (P.normalized x hx) w c hc'
  refine ⟨(fun y => y - x) ⁻¹' U, (fun y => W (y - x)), (fun y => C (y - x)),
    hU.preimage (by fun_prop), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Set.mem_preimage, sub_self] using h0
  · simpa only [sub_self] using hW
  · simpa only [sub_self] using hC
  · intro y hy
    simpa only [sub_add_cancel] using (hWA (y - x) hy).comp_sub x
  · intro y hy
    simpa only [sub_add_cancel] using (hCA (y - x) hy).comp_sub x
  · intro y hy
    have hs := (P.isStress_normalized_iff x (y - x) hx (W (y - x)) (C (y - x))).mp
      (hSstress (y - x) hy)
    have hxy : x + (y - x) = y := by
      ext k
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    simpa only [hxy] using hs

end StressFlex.Spherical

/-! ## Source fragment: StressFlex/LocalCoefficient.lean -/

open CategoryTheory Set Topology

namespace StressFlex.LocalCoefficient

variable {X : Type} [TopologicalSpace X] [T2Space X]
    (N : ModuleCat.{0} ℝ) (k : ℕ)

abbrev restrictPoint {S : Set X} {x : X} (hx : x ∈ S) :
    TauCeti.localHomology N S k ⟶ TauCeti.localHomology N ({x} : Set X) k :=
  TauCeti.localHomologyRestriction N (singleton_subset_iff.mpr hx) k

/-- A relative homology class whose local coefficient is constant on a set
has that same coefficient at every point of its closure where the reference
class is a nonzero local generator. The equality at the limiting point is
the only input about its local homology group. -/
theorem coefficient_eq_of_mem_closure {S T : Set X} {x : X}
    (hS : S ∈ 𝓝 x) (hTS : T ⊆ S) (hx : x ∈ closure T)
    (h g : (TauCeti.localHomology N S k : ModuleCat.{0} ℝ))
    (a c : ℝ)
    (hxEq : restrictPoint N k (mem_of_mem_nhds hS) h =
      c • restrictPoint N k (mem_of_mem_nhds hS) g)
    (hTEq : ∀ y, ∀ hy : y ∈ T,
      restrictPoint N k (hTS hy) h = a • restrictPoint N k (hTS hy) g)
    (hTne : ∀ y, ∀ hy : y ∈ T, restrictPoint N k (hTS hy) g ≠ 0) :
    a = c := by
  have hS' : S ∈ 𝓝ˢ ({x} : Set X) := by simpa using hS
  have hz : TauCeti.localHomologyRestriction N
      (subset_of_mem_nhdsSet hS') k (h - c • g) = 0 := by
    simpa only [map_sub, map_smul, sub_eq_zero] using hxEq
  obtain ⟨W, hW, hWS, hzW⟩ :=
    TauCeti.exists_mem_nhdsSet_localHomologyRestriction_eq_zero N k hS'
      (h - c • g) hz
  have hW' : W ∈ 𝓝 x := by simpa using hW
  obtain ⟨U, hUW, hUo, hxU⟩ := mem_nhds_iff.mp hW'
  obtain ⟨y, hyU, hyT⟩ := mem_closure_iff.mp hx U hUo hxU
  have hyW : y ∈ W := hUW hyU
  have hyS : y ∈ S := hWS hyW
  have hzY : restrictPoint N k hyS (h - c • g) = 0 := by
    have hcomp := ConcreteCategory.congr_hom
      (TauCeti.localHomologyRestriction_comp N
        (singleton_subset_iff.mpr hyW) hWS k) (h - c • g)
    calc
      restrictPoint N k hyS (h - c • g) =
          restrictPoint N k hyW
            (TauCeti.localHomologyRestriction N hWS k (h - c • g)) := by
        simpa only [ModuleCat.comp_apply] using hcomp.symm
      _ = 0 := by rw [hzW, map_zero]
  have hEq : a • restrictPoint N k hyS g = c • restrictPoint N k hyS g := by
    calc
      a • restrictPoint N k hyS g = restrictPoint N k hyS h := (hTEq y hyT).symm
      _ = c • restrictPoint N k hyS g := by
        simpa only [map_sub, map_smul, sub_eq_zero] using hzY
  by_contra hac
  have hsmul : (a - c) • restrictPoint N k hyS g = 0 := by
    rw [sub_smul, hEq, sub_self]
  exact hTne y hyT ((smul_eq_zero.mp hsmul).resolve_left (sub_ne_zero.mpr hac))

end StressFlex.LocalCoefficient

/-! ## Source fragment: StressFlex/Gauge.lean -/

open Topology
open scoped ComplexConjugate

namespace StressFlex

/-- A continuous positive homogeneous gauge. Its level set is parametrised by the genuine circle. -/
structure PositiveGauge where
  toFun : ℂ → ℝ
  continuous_toFun : Continuous toFun
  map_zero : toFun 0 = 0
  positive : ∀ z, z ≠ 0 → 0 < toFun z
  homogeneous : ∀ (a : ℝ), 0 ≤ a → ∀ z, toFun (a • z) = a * toFun z

namespace PositiveGauge

instance : CoeFun PositiveGauge (fun _ => ℂ → ℝ) := ⟨toFun⟩

abbrev Boundary (g : PositiveGauge) := {z : ℂ // g z = 1}

theorem boundary_ne_zero (g : PositiveGauge) (z : g.Boundary) : (z : ℂ) ≠ 0 := by
  intro hz
  have h := z.2
  rw [hz, g.map_zero] at h
  exact zero_ne_one h

def fromCircle (g : PositiveGauge) (z : Circle) : g.Boundary :=
  ⟨(g z)⁻¹ • (z : ℂ), by
    rw [g.homogeneous _ (inv_nonneg.mpr (g.positive z z.coe_ne_zero).le)]
    exact inv_mul_cancel₀ (g.positive z z.coe_ne_zero).ne'⟩

def toCircle (g : PositiveGauge) (z : g.Boundary) : Circle :=
  ⟨‖(z : ℂ)‖⁻¹ • (z : ℂ), by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (g.boundary_ne_zero z))⟩

theorem fromCircle_toCircle (g : PositiveGauge) (z : g.Boundary) :
    g.fromCircle (g.toCircle z) = z := by
  apply Subtype.ext
  change (g (‖(z : ℂ)‖⁻¹ • (z : ℂ)))⁻¹ •
    (‖(z : ℂ)‖⁻¹ • (z : ℂ)) = (z : ℂ)
  rw [g.homogeneous _ (inv_nonneg.mpr (norm_nonneg _)), z.2, mul_one,
    inv_inv, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (g.boundary_ne_zero z)), one_smul]

theorem toCircle_fromCircle (g : PositiveGauge) (z : Circle) :
    g.toCircle (g.fromCircle z) = z := by
  apply Subtype.ext
  change ‖(g z)⁻¹ • (z : ℂ)‖⁻¹ • ((g z)⁻¹ • (z : ℂ)) = (z : ℂ)
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (g.positive z z.coe_ne_zero).le),
    Circle.norm_coe, mul_one, inv_inv, smul_smul,
    mul_inv_cancel₀ (g.positive z z.coe_ne_zero).ne', one_smul]

theorem continuous_fromCircle (g : PositiveGauge) : Continuous g.fromCircle := by
  unfold fromCircle
  apply Continuous.subtype_mk
  exact ((g.continuous_toFun.comp
    (continuous_subtype_val : Continuous (fun z : Circle => (z : ℂ)))).inv₀
    (fun z : Circle => (g.positive z (Circle.coe_ne_zero z)).ne')).smul
      (continuous_subtype_val : Continuous (fun z : Circle => (z : ℂ)))

theorem continuous_toCircle (g : PositiveGauge) : Continuous g.toCircle := by
  unfold toCircle
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.norm.inv₀
    (fun z => norm_ne_zero_iff.mpr (g.boundary_ne_zero z))).smul continuous_subtype_val

def circleHomeomorph (g : PositiveGauge) : Circle ≃ₜ g.Boundary where
  toFun := g.fromCircle
  invFun := g.toCircle
  left_inv := g.toCircle_fromCircle
  right_inv := g.fromCircle_toCircle
  continuous_toFun := g.continuous_fromCircle
  continuous_invFun := g.continuous_toCircle

instance (g : PositiveGauge) : CompactSpace g.Boundary :=
  Function.Surjective.compactSpace g.circleHomeomorph.continuous g.circleHomeomorph.surjective

end PositiveGauge

def baseGaugeFun (z : ℂ) : ℝ :=
  max (z.re + z.im) (max (z.re - 2 * z.im) (-2 * z.re + z.im))

def baseGauge : PositiveGauge where
  toFun := baseGaugeFun
  continuous_toFun := by unfold baseGaugeFun; fun_prop
  map_zero := by simp [baseGaugeFun]
  positive := by
    intro z hz
    by_contra h
    have h0 : baseGaugeFun z ≤ 0 := le_of_not_gt h
    have h1 := (le_max_left (z.re + z.im) _).trans h0
    have h2 := (le_max_left (z.re - 2 * z.im) _).trans
      ((le_max_right (z.re + z.im) _).trans h0)
    have h3 := (le_max_right (z.re - 2 * z.im) _).trans
      ((le_max_right (z.re + z.im) _).trans h0)
    apply hz
    apply Complex.ext <;> simp only [Complex.zero_re, Complex.zero_im] <;> linarith
  homogeneous := by
    intro a ha z
    simp only [baseGaugeFun, Complex.smul_re, Complex.smul_im, smul_eq_mul,
      mul_max_of_nonneg _ _ ha]
    congr 1
    · ring
    · congr 1 <;> ring

def sectionGaugeFun (z : ℂ) : ℝ :=
  max (-(3 / 2 : ℝ) * z.re)
    (max ((3 / 4 : ℝ) * z.re + (3 / 2 : ℝ) * z.im)
      ((3 / 4 : ℝ) * z.re - (3 / 2 : ℝ) * z.im))

def sectionGauge : PositiveGauge where
  toFun := sectionGaugeFun
  continuous_toFun := by unfold sectionGaugeFun; fun_prop
  map_zero := by simp [sectionGaugeFun]
  positive := by
    intro z hz
    by_contra h
    have h0 : sectionGaugeFun z ≤ 0 := le_of_not_gt h
    have h1 := (le_max_left (-(3 / 2 : ℝ) * z.re) _).trans h0
    have h2 := (le_max_left ((3 / 4 : ℝ) * z.re + (3 / 2 : ℝ) * z.im) _).trans
      ((le_max_right (-(3 / 2 : ℝ) * z.re) _).trans h0)
    have h3 := (le_max_right ((3 / 4 : ℝ) * z.re + (3 / 2 : ℝ) * z.im) _).trans
      ((le_max_right (-(3 / 2 : ℝ) * z.re) _).trans h0)
    apply hz
    apply Complex.ext <;> simp only [Complex.zero_re, Complex.zero_im] <;> linarith
  homogeneous := by
    intro a ha z
    simp only [sectionGaugeFun, Complex.smul_re, Complex.smul_im, smul_eq_mul,
      mul_max_of_nonneg _ _ ha]
    congr 1
    · ring
    · congr 1 <;> ring

end StressFlex

/-! ## Source fragment: StressFlex/TorusGeometry.lean -/

open Topology
open scoped BigOperators

namespace StressFlex.Torus

abbrev Vec := Fin 3 → ℝ
abbrev Parameter := baseGauge.Boundary × sectionGauge.Boundary

def radius (z : sectionGauge.Boundary) : ℝ := (z : ℂ).re + 8 / 3

theorem radius_ge_two (z : sectionGauge.Boundary) : 2 ≤ radius z := by
  have h := (le_max_left (-(3 / 2 : ℝ) * (z : ℂ).re)
    (max ((3 / 4 : ℝ) * (z : ℂ).re + (3 / 2 : ℝ) * (z : ℂ).im)
      ((3 / 4 : ℝ) * (z : ℂ).re - (3 / 2 : ℝ) * (z : ℂ).im)))
  change -(3 / 2 : ℝ) * (z : ℂ).re ≤ sectionGauge z at h
  rw [z.2] at h
  unfold radius
  linarith

theorem radius_pos (z : sectionGauge.Boundary) : 0 < radius z :=
  lt_of_lt_of_le (by norm_num) (radius_ge_two z)

def param (q : Parameter) : Vec :=
  ![radius q.2 * (q.1 : ℂ).re, radius q.2 * (q.1 : ℂ).im, (q.2 : ℂ).im]

theorem continuous_param : Continuous param := by
  apply continuous_pi
  intro k
  fin_cases k <;> simp only [param, radius, Matrix.cons_val_zero,
    Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> fun_prop

theorem param_injective : Function.Injective param := by
  rintro ⟨ξ, z⟩ ⟨η, t⟩ h
  have h0 := congrArg (fun p : Vec => p 0) h
  have h1 := congrArg (fun p : Vec => p 1) h
  have h2 := congrArg (fun p : Vec => p 2) h
  simp only [param, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  have hxy : radius z • (ξ : ℂ) = radius t • (η : ℂ) := by
    apply Complex.ext
    · simpa only [Complex.smul_re, smul_eq_mul] using h0
    · simpa only [Complex.smul_im, smul_eq_mul] using h1
  have hr := congrArg (fun v : ℂ => baseGauge v) hxy
  rw [baseGauge.homogeneous _ (radius_pos z).le, baseGauge.homogeneous _ (radius_pos t).le,
    ξ.2, η.2, mul_one, mul_one] at hr
  have hξ : ξ = η := by
    apply Subtype.ext
    rw [← hr] at hxy
    exact (smul_right_injective ℂ (radius_pos z).ne') hxy
  have hz : z = t := by
    apply Subtype.ext
    apply Complex.ext
    · dsimp [radius] at hr
      linarith
    · exact h2
  exact Prod.ext hξ hz

theorem closedEmbedding_param : IsClosedEmbedding param :=
  continuous_param.isClosedEmbedding param_injective

def Surface : Set Vec := Set.range param

def parameterHomeomorph : Parameter ≃ₜ Surface :=
  closedEmbedding_param.toIsEmbedding.toHomeomorph

/-- A genuine topological embedding of S¹ × S¹ onto the constructed geometric surface. -/
def torusHomeomorph : (Circle × Circle) ≃ₜ Surface :=
  (baseGauge.circleHomeomorph.prodCongr sectionGauge.circleHomeomorph).trans parameterHomeomorph

theorem compact_surface : IsCompact Surface := isCompact_range continuous_param

end StressFlex.Torus

/-! ## Source fragment: StressFlex/TorusFramework.lean -/

open Matrix
open scoped BigOperators

namespace StressFlex.Torus

abbrev FrameworkVertex := Fin 10
abbrev FrameworkVector := Fin 3 → ℝ

def position : FrameworkVertex → FrameworkVector :=
  ![![0, 0, 0], ![2, 0, -1], ![0, 2, -1], ![-2, -2, -1],
    ![4, 0, 0], ![0, 4, 0], ![-4, -4, 0],
    ![2, 0, 1], ![0, 2, 1], ![-2, -2, 1]]

def velocity : FrameworkVertex → FrameworkVector :=
  ![![0, 0, 0], ![0, 1, 0], ![-1, 0, 0], ![1, -1, 0],
    ![0, 0, 0], ![0, 0, 0], ![0, 0, 0],
    ![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]

def affineDependence : FrameworkVertex → ℝ :=
  ![-1, 1, 0, 0, -1, 0, 0, 1, 0, 0]

def adjacency (i j : FrameworkVertex) : Prop :=
  i ≠ j ∧ (i = 0 ∨ j = 0 ∨
    (i.val - 1) / 3 = (j.val - 1) / 3 ∨
    (i.val - 1) % 3 = (j.val - 1) % 3)

instance : DecidableRel adjacency := fun i j => by
  unfold adjacency
  infer_instance

/-- The framework graph is the following symmetric, loopless finite relation.
Its defining formula is unchanged from the Cartesian-product graph presentation. -/
theorem adjacency_iff (i j : FrameworkVertex) :
    adjacency i j ↔ i ≠ j ∧ (i = 0 ∨ j = 0 ∨
      (i.val - 1) / 3 = (j.val - 1) / 3 ∨
      (i.val - 1) % 3 = (j.val - 1) % 3) := Iff.rfl

theorem adjacency_symmetric : Symmetric adjacency := by
  intro i j h
  exact ⟨h.1.symm, h.2.elim (fun hi => Or.inr (Or.inl hi))
    (fun hrest => hrest.elim (fun hj => Or.inl hj)
      (fun hlast => hlast.elim
        (fun hrow => Or.inr (Or.inr (Or.inl hrow.symm)))
        (fun hcol => Or.inr (Or.inr (Or.inr hcol.symm)))))⟩

theorem adjacency_irreflexive (i : FrameworkVertex) : ¬ adjacency i i := fun h => h.1 rfl

def stress (i j : FrameworkVertex) : ℝ :=
  if i = j then 0 else -affineDependence i * affineDependence j

def faceVertex : Fin 9 → Fin 4 → FrameworkVertex :=
  ![![1, 4, 5, 2], ![2, 5, 6, 3], ![3, 6, 4, 1],
    ![4, 7, 8, 5], ![5, 8, 9, 6], ![6, 9, 7, 4],
    ![7, 1, 2, 8], ![8, 2, 3, 9], ![9, 3, 1, 7]]

def faceNormal : Fin 9 → FrameworkVector :=
  ![![1, 1, -2], ![-2, 1, -2], ![1, -2, -2],
    ![1, 1, 2], ![-2, 1, 2], ![1, -2, 2],
    ![1, 1, 0], ![-2, 1, 0], ![1, -2, 0]]

def faceLevel : Fin 9 → ℝ := ![4, 4, 4, 4, 4, 4, 2, 2, 2]

/-- An integer-valued linear observation distinguishes the ten displayed points. -/
def positionCode : FrameworkVertex → ℤ := ![0, 19, 5, -27, 40, 12, -52, 21, 7, -25]

theorem positionCode_injective : Function.Injective positionCode := by decide

theorem position_code (i : FrameworkVertex) :
    10 * position i 0 + 3 * position i 1 + position i 2 = (positionCode i : ℝ) := by
  fin_cases i <;> norm_num [position, positionCode]

theorem position_injective : Function.Injective position := by
  intro i j hij
  have h := congrArg (fun p : FrameworkVector => 10 * p 0 + 3 * p 1 + p 2) hij
  rw [position_code, position_code] at h
  exact positionCode_injective (Int.cast_injective h)

theorem face_planar (f : Fin 9) (k : Fin 4) :
    faceNormal f ⬝ᵥ position (faceVertex f k) = faceLevel f := by
  fin_cases f <;> fin_cases k <;>
    norm_num [faceNormal, position, faceVertex, faceLevel, dotProduct, Fin.sum_univ_succ]

theorem apex_outside_face_planes (f : Fin 9) :
    faceNormal f ⬝ᵥ position 0 ≠ faceLevel f := by
  fin_cases f <;>
    norm_num [faceNormal, position, faceLevel, dotProduct, Fin.sum_univ_succ]

theorem face_noncollinear (f : Fin 9) :
    (position (faceVertex f 1) - position (faceVertex f 0)) ⨯₃
      (position (faceVertex f 2) - position (faceVertex f 0)) ≠ 0 := by
  fin_cases f <;>
    norm_num [position, faceVertex, cross_apply, funext_iff, Fin.forall_fin_succ]

/-- The faces use precisely the Cartesian-product graph edges stated in the paper. -/
theorem outer_edges_exactly_face_edges (i j : FrameworkVertex) (hi : i ≠ 0) (hj : j ≠ 0) :
    adjacency i j ↔ ∃ f : Fin 9, ∃ k : Fin 4,
      (i = faceVertex f k ∧ j = faceVertex f (k + 1)) ∨
      (j = faceVertex f k ∧ i = faceVertex f (k + 1)) := by
  revert i j hi hj
  decide

theorem every_outer_vertex_is_face_vertex (i : FrameworkVertex) (hi : i ≠ 0) :
    ∃ f : Fin 9, ∃ k : Fin 4, i = faceVertex f k := by
  revert i hi
  decide

theorem stress_symmetric (i j : FrameworkVertex) : stress i j = stress j i := by
  unfold stress
  by_cases h : i = j
  · subst j
    simp
  · have hji : j ≠ i := fun hji => h hji.symm
    simp only [h, hji, if_false]
    ring

theorem stress_supported (i j : FrameworkVertex) (h : ¬ adjacency i j) :
    stress i j = 0 := by
  fin_cases i <;> fin_cases j <;>
    (norm_num [adjacency] at h <;> norm_num [stress, affineDependence])

/-- All ten equilibrium equations, including the apex equation. -/
theorem equilibrium (i : FrameworkVertex) :
    ∑ j, stress i j • (position j - position i) = 0 := by
  fin_cases i <;> ext k <;> fin_cases k <;>
    norm_num [stress, affineDependence, position, Fin.sum_univ_succ]

theorem apex_position : position 0 = 0 := by
  ext k
  fin_cases k <;> norm_num [position]

theorem fixed_apex : velocity 0 = 0 := by
  ext k
  fin_cases k <;> norm_num [velocity]

theorem edge_motion (i j : FrameworkVertex) (h : adjacency i j) :
    (position i - position j) ⬝ᵥ (velocity i - velocity j) = 0 := by
  fin_cases i <;> fin_cases j <;>
    (norm_num [adjacency] at h <;>
      norm_num [position, velocity, dotProduct, Fin.sum_univ_succ])

theorem weighted_velocity :
    ∑ i, stress 0 i • velocity i = ![0, 1, 0] := by
  ext k
  fin_cases k <;>
    norm_num [stress, affineDependence, velocity, Fin.sum_univ_succ]

/-- The sum over exactly the nine surface vertices, with the apex omitted as in the paper. -/
theorem weighted_velocity_outer :
    ∑ i : Fin 9, stress 0 i.succ • velocity i.succ = ![0, 1, 0] := by
  have h := weighted_velocity
  rw [Fin.sum_univ_succ] at h
  simpa [stress] using h

theorem orthogonality_fails_outer :
    (∑ i : Fin 9, stress 0 i.succ • velocity i.succ) ≠ 0 := by
  rw [weighted_velocity_outer]
  intro h
  have hh := congrArg (fun u : FrameworkVector => u 1) h
  norm_num at hh

theorem orthogonality_fails : (∑ i, stress 0 i • velocity i) ≠ 0 := by
  rw [weighted_velocity]
  intro h
  have := congrArg (fun u : FrameworkVector => u 1) h
  norm_num at this

end StressFlex.Torus

/-! ## Source fragment: StressFlex/TorusFaces.lean -/

open Topology
open scoped BigOperators

namespace StressFlex.Torus

abbrev I := Set.Icc (0 : ℝ) 1

def i0 : I := ⟨0, by constructor <;> norm_num⟩
def i1 : I := ⟨1, by constructor <;> norm_num⟩

theorem max_three_eq_one (a b c : ℝ) :
    max a (max b c) = 1 ↔ a ≤ 1 ∧ b ≤ 1 ∧ c ≤ 1 ∧ (a = 1 ∨ b = 1 ∨ c = 1) := by
  constructor
  · intro h
    have ha := (le_max_left a (max b c)).trans_eq h
    have hb := ((le_max_left b c).trans (le_max_right a (max b c))).trans_eq h
    have hc := ((le_max_right b c).trans (le_max_right a (max b c))).trans_eq h
    refine ⟨ha, hb, hc, ?_⟩
    by_contra hn
    push_neg at hn
    have hlt : max a (max b c) < 1 :=
      max_lt (lt_of_le_of_ne ha hn.1) (max_lt (lt_of_le_of_ne hb hn.2.1)
        (lt_of_le_of_ne hc hn.2.2))
    rw [h] at hlt
    exact lt_irrefl _ hlt
  · rintro ⟨ha, hb, hc, h⟩
    apply le_antisymm (max_le ha (max_le hb hc))
    rcases h with rfl | rfl | rfl
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)

def baseEdgeCoord (a : Fin 3) (s : ℝ) : ℂ :=
  ![⟨1 - s, s⟩, ⟨-s, 1 - 2 * s⟩, ⟨-1 + 2 * s, -1 + s⟩] a

def sectionEdgeCoord (b : Fin 3) (t : ℝ) : ℂ :=
  ![⟨-2 / 3 + 2 * t, -1 + t⟩, ⟨4 / 3 - 2 * t, t⟩, ⟨-2 / 3, 1 - 2 * t⟩] b

theorem baseEdge_mem (a : Fin 3) (s : I) : baseGauge (baseEdgeCoord a s) = 1 := by
  have hs0 := s.2.1
  have hs1 := s.2.2
  change baseGaugeFun (baseEdgeCoord a s) = 1
  fin_cases a
  all_goals
    simp only [baseEdgeCoord, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, baseGaugeFun]
    apply (max_three_eq_one _ _ _).mpr
    refine ⟨by linarith, by linarith, by linarith, ?_⟩
  · exact Or.inl (by ring)
  · exact Or.inr (Or.inr (by ring))
  · exact Or.inr (Or.inl (by ring))

theorem sectionEdge_mem (b : Fin 3) (t : I) : sectionGauge (sectionEdgeCoord b t) = 1 := by
  have ht0 := t.2.1
  have ht1 := t.2.2
  change sectionGaugeFun (sectionEdgeCoord b t) = 1
  fin_cases b
  all_goals
    simp only [sectionEdgeCoord, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, sectionGaugeFun]
    apply (max_three_eq_one _ _ _).mpr
    refine ⟨by linarith, by linarith, by linarith, ?_⟩
  · exact Or.inr (Or.inr (by ring))
  · exact Or.inr (Or.inl (by ring))
  · exact Or.inl (by ring)

def baseEdge (a : Fin 3) (s : I) : baseGauge.Boundary :=
  ⟨baseEdgeCoord a s, baseEdge_mem a s⟩

def sectionEdge (b : Fin 3) (t : I) : sectionGauge.Boundary :=
  ⟨sectionEdgeCoord b t, sectionEdge_mem b t⟩

theorem base_edges_cover (ξ : baseGauge.Boundary) :
    ∃ a : Fin 3, ∃ s : I, baseEdge a s = ξ := by
  obtain ⟨h1, h2, h3, heq⟩ := (max_three_eq_one _ _ _).mp ξ.2
  rcases heq with h | h | h
  · refine ⟨0, ⟨(ξ : ℂ).im, by constructor <;> linarith⟩, ?_⟩
    apply Subtype.ext
    apply Complex.ext <;> simp only [baseEdge, baseEdgeCoord, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Complex.re, Complex.im] <;> linarith
  · refine ⟨2, ⟨((ξ : ℂ).re + 1) / 2, by constructor <;> linarith⟩, ?_⟩
    apply Subtype.ext
    apply Complex.ext <;> simp only [baseEdge, baseEdgeCoord, Matrix.cons_val_fin_one, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Matrix.cons_val_one] <;> linarith
  · refine ⟨1, ⟨-(ξ : ℂ).re, by constructor <;> linarith⟩, ?_⟩
    apply Subtype.ext
    apply Complex.ext <;> simp only [baseEdge, baseEdgeCoord, Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Complex.re, Complex.im] <;> linarith

theorem section_edges_cover (z : sectionGauge.Boundary) :
    ∃ b : Fin 3, ∃ t : I, sectionEdge b t = z := by
  obtain ⟨h1, h2, h3, heq⟩ := (max_three_eq_one _ _ _).mp z.2
  rcases heq with h | h | h
  · refine ⟨2, ⟨(1 - (z : ℂ).im) / 2, by constructor <;> linarith⟩, ?_⟩
    apply Subtype.ext
    apply Complex.ext <;> simp only [sectionEdge, sectionEdgeCoord, Matrix.cons_val_fin_one, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Matrix.cons_val_one] <;> linarith
  · refine ⟨1, ⟨(z : ℂ).im, by constructor <;> linarith⟩, ?_⟩
    apply Subtype.ext
    apply Complex.ext <;> simp only [sectionEdge, sectionEdgeCoord, Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Complex.re, Complex.im] <;> linarith
  · refine ⟨0, ⟨(z : ℂ).im + 1, by constructor <;> linarith⟩, ?_⟩
    apply Subtype.ext
    apply Complex.ext <;> simp only [sectionEdge, sectionEdgeCoord, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Complex.re, Complex.im] <;> linarith

theorem baseEdge_injective (a : Fin 3) : Function.Injective (baseEdge a) := by
  intro s t h
  have hr := congrArg (fun x : baseGauge.Boundary => (x : ℂ).re) h
  have hi := congrArg (fun x : baseGauge.Boundary => (x : ℂ).im) h
  apply Subtype.ext
  fin_cases a <;>
    simp only [baseEdge, baseEdgeCoord, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hr hi <;> linarith

theorem sectionEdge_injective (b : Fin 3) : Function.Injective (sectionEdge b) := by
  intro s t h
  have hr := congrArg (fun x : sectionGauge.Boundary => (x : ℂ).re) h
  have hi := congrArg (fun x : sectionGauge.Boundary => (x : ℂ).im) h
  apply Subtype.ext
  fin_cases b <;>
    simp only [sectionEdge, sectionEdgeCoord, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hr hi <;> linarith

def cellParam (a b : Fin 3) (st : I × I) : Vec :=
  param (baseEdge a st.1, sectionEdge b st.2)

def faceSet (a b : Fin 3) : Set Vec := Set.range (cellParam a b)

theorem cellParam_injective (a b : Fin 3) : Function.Injective (cellParam a b) := by
  intro q r h
  have h' := param_injective h
  exact Prod.ext (baseEdge_injective a (congrArg Prod.fst h'))
    (sectionEdge_injective b (congrArg Prod.snd h'))

@[fun_prop] theorem continuous_complex_mk {Y : Type*} [TopologicalSpace Y]
    {f g : Y → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => (⟨f x, g x⟩ : ℂ)) := by
  simp_rw [Complex.mk_eq_add_mul_I]
  fun_prop

theorem continuous_cellParam (a b : Fin 3) : Continuous (cellParam a b) := by
  apply continuous_param.comp
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    fin_cases a <;> simp only [baseEdge, baseEdgeCoord, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> fun_prop
  · apply Continuous.subtype_mk
    fin_cases b <;> simp only [sectionEdge, sectionEdgeCoord, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> fun_prop

theorem faceSet_subset_surface (a b : Fin 3) : faceSet a b ⊆ Surface := by
  rintro x ⟨q, rfl⟩
  exact ⟨(baseEdge a q.1, sectionEdge b q.2), rfl⟩

theorem faces_cover_surface : (⋃ a : Fin 3, ⋃ b : Fin 3, faceSet a b) = Surface := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun a => Set.iUnion_subset fun b => faceSet_subset_surface a b
  · rintro x ⟨⟨ξ, z⟩, rfl⟩
    obtain ⟨a, s, rfl⟩ := base_edges_cover ξ
    obtain ⟨b, t, rfl⟩ := section_edges_cover z
    exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨b, ⟨(s, t), rfl⟩⟩⟩

def faceIndex (a b : Fin 3) : Fin 9 := ⟨3 * b.val + a.val, by omega⟩

/-- The product patches enumerate all nine printed faces exactly once. -/
theorem faceIndex_bijective :
    Function.Bijective (fun ab : Fin 3 × Fin 3 => faceIndex ab.1 ab.2) := by
  decide

def squareCorner : Fin 4 → I × I := ![(i0, i0), (i0, i1), (i1, i1), (i1, i0)]

/-- The parametrized patches have exactly the nine corner cycles printed in the paper. -/
theorem cellParam_corner (a b : Fin 3) (k : Fin 4) :
    cellParam a b (squareCorner k) = position (faceVertex (faceIndex a b) k) := by
  fin_cases a <;> fin_cases b <;> fin_cases k <;> ext j <;> fin_cases j <;>
    norm_num [cellParam, param, baseEdge, sectionEdge, baseEdgeCoord, sectionEdgeCoord,
      radius, squareCorner, i0, i1, faceIndex, position, faceVertex]

end StressFlex.Torus

/-! ## Source fragment: StressFlex/RadialQuad.lean -/

open scoped BigOperators

namespace StressFlex.RadialQuad

abbrev Vec := Fin 3 → ℝ

variable (u v : Fin 2 → ℝ) (r₀ r₁ z₀ z₁ : ℝ)

def radius (t : ℝ) : ℝ := (1 - t) * r₀ + t * r₁

def point (s t : ℝ) : Vec :=
  ![radius r₀ r₁ t * ((1 - s) * u 0 + s * v 0),
    radius r₀ r₁ t * ((1 - s) * u 1 + s * v 1),
    (1 - t) * z₀ + t * z₁]

def patch : Set Vec := Set.range (fun st : Torus.I × Torus.I =>
  point u v r₀ r₁ z₀ z₁ st.1 st.2)

def corners : Fin 4 → Vec :=
  ![point u v r₀ r₁ z₀ z₁ 0 0, point u v r₀ r₁ z₀ z₁ 0 1,
    point u v r₀ r₁ z₀ z₁ 1 1, point u v r₀ r₁ z₀ z₁ 1 0]

theorem radius_pos (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (t : Torus.I) :
    0 < radius r₀ r₁ t := by
  have ht₀ := t.2.1
  have ht₁ := t.2.2
  by_cases ht : (t : ℝ) = 1
  · simp [radius, ht, hr₁]
  · have hpos := mul_pos (sub_pos.mpr (lt_of_le_of_ne ht₁ ht)) hr₀
    exact add_pos_of_pos_of_nonneg hpos (mul_nonneg ht₀ hr₁.le)

theorem radius_affine (a b s t : ℝ) (hab : a + b = 1) :
    radius r₀ r₁ (a * s + b * t) =
      a * radius r₀ r₁ s + b * radius r₀ r₁ t := by
  unfold radius
  linear_combination -r₀ * hab

theorem patch_convex (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) :
    Convex ℝ (patch u v r₀ r₁ z₀ z₁) := by
  rintro _ ⟨⟨s, t⟩, rfl⟩ _ ⟨⟨s', t'⟩, rfl⟩ a b ha hb hab
  let t'' : Torus.I := ⟨a * t + b * t', by
    constructor
    · exact add_nonneg (mul_nonneg ha t.2.1) (mul_nonneg hb t'.2.1)
    · nlinarith [mul_nonneg ha (sub_nonneg.mpr t.2.2),
        mul_nonneg hb (sub_nonneg.mpr t'.2.2)]⟩
  have hr := radius_pos r₀ r₁ hr₀ hr₁ t''
  have hrt := radius_pos r₀ r₁ hr₀ hr₁ t
  have hrt' := radius_pos r₀ r₁ hr₀ hr₁ t'
  have hrad : radius r₀ r₁ t'' = a * radius r₀ r₁ t + b * radius r₀ r₁ t' :=
    radius_affine r₀ r₁ a b t t' hab
  let N := a * radius r₀ r₁ t * s + b * radius r₀ r₁ t' * s'
  have hN : 0 ≤ N := add_nonneg
    (mul_nonneg (mul_nonneg ha hrt.le) s.2.1)
    (mul_nonneg (mul_nonneg hb hrt'.le) s'.2.1)
  have hNle : N ≤ radius r₀ r₁ t'' := by
    rw [hrad]
    dsimp [N]
    nlinarith [mul_nonneg (mul_nonneg ha hrt.le) (sub_nonneg.mpr s.2.2),
      mul_nonneg (mul_nonneg hb hrt'.le) (sub_nonneg.mpr s'.2.2)]
  let s'' : Torus.I := ⟨N / radius r₀ r₁ t'',
    ⟨div_nonneg hN hr.le, (div_le_one hr).mpr hNle⟩⟩
  refine ⟨(s'', t''), ?_⟩
  ext k
  fin_cases k
  · change radius r₀ r₁ t'' *
        ((1 - N / radius r₀ r₁ t'') * u 0 + N / radius r₀ r₁ t'' * v 0) =
      a * (radius r₀ r₁ t * ((1 - (s : ℝ)) * u 0 + s * v 0)) +
      b * (radius r₀ r₁ t' * ((1 - (s' : ℝ)) * u 0 + s' * v 0))
    rw [hrad]
    have hd : a * radius r₀ r₁ t + b * radius r₀ r₁ t' ≠ 0 := by
      rw [← hrad]
      exact hr.ne'
    dsimp [N]
    field_simp [hd]
    ring
  · change radius r₀ r₁ t'' *
        ((1 - N / radius r₀ r₁ t'') * u 1 + N / radius r₀ r₁ t'' * v 1) =
      a * (radius r₀ r₁ t * ((1 - (s : ℝ)) * u 1 + s * v 1)) +
      b * (radius r₀ r₁ t' * ((1 - (s' : ℝ)) * u 1 + s' * v 1))
    rw [hrad]
    have hd : a * radius r₀ r₁ t + b * radius r₀ r₁ t' ≠ 0 := by
      rw [← hrad]
      exact hr.ne'
    dsimp [N]
    field_simp [hd]
    ring
  · change (1 - (a * (t : ℝ) + b * (t' : ℝ))) * z₀ +
        (a * (t : ℝ) + b * (t' : ℝ)) * z₁ =
      a * ((1 - (t : ℝ)) * z₀ + t * z₁) +
      b * ((1 - (t' : ℝ)) * z₀ + t' * z₁)
    linear_combination -z₀ * hab

theorem bilinear_formula (s t : ℝ) :
    point u v r₀ r₁ z₀ z₁ s t =
      (1 - t) • ((1 - s) • point u v r₀ r₁ z₀ z₁ 0 0 +
        s • point u v r₀ r₁ z₀ z₁ 1 0) +
      t • ((1 - s) • point u v r₀ r₁ z₀ z₁ 0 1 +
        s • point u v r₀ r₁ z₀ z₁ 1 1) := by
  ext k
  fin_cases k <;> simp [point, radius] <;> ring

/-- Each radial patch with positive endpoint radii is exactly its four-corner convex hull. -/
theorem patch_eq_convexHull (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) :
    patch u v r₀ r₁ z₀ z₁ = convexHull ℝ (Set.range (corners u v r₀ r₁ z₀ z₁)) := by
  let Q := Set.range (corners u v r₀ r₁ z₀ z₁)
  have hc := convex_convexHull ℝ Q
  have hcorner (k : Fin 4) : corners u v r₀ r₁ z₀ z₁ k ∈ convexHull ℝ Q :=
    subset_convexHull ℝ Q ⟨k, rfl⟩
  apply Set.Subset.antisymm
  · rintro x ⟨⟨s, t⟩, rfl⟩
    change point u v r₀ r₁ z₀ z₁ (s : ℝ) (t : ℝ) ∈ convexHull ℝ Q
    rw [bilinear_formula]
    apply hc
    · exact hc (hcorner 0) (hcorner 3) (sub_nonneg.mpr s.2.2) s.2.1 (by ring)
    · exact hc (hcorner 1) (hcorner 2) (sub_nonneg.mpr s.2.2) s.2.1 (by ring)
    · exact sub_nonneg.mpr t.2.2
    · exact t.2.1
    · ring
  · apply convexHull_min
    · rintro x ⟨k, rfl⟩
      fin_cases k
      · exact ⟨(Torus.i0, Torus.i0), rfl⟩
      · exact ⟨(Torus.i0, Torus.i1), rfl⟩
      · exact ⟨(Torus.i1, Torus.i1), rfl⟩
      · exact ⟨(Torus.i1, Torus.i0), rfl⟩
    · exact patch_convex u v r₀ r₁ z₀ z₁ hr₀ hr₁

end StressFlex.RadialQuad

/-! ## Source fragment: StressFlex/TorusPolyhedral.lean -/

open Matrix Topology
open scoped BigOperators

namespace StressFlex.Torus

def baseStart (a : Fin 3) : Fin 2 → ℝ :=
  ![(baseEdgeCoord a 0).re, (baseEdgeCoord a 0).im]
def baseEnd (a : Fin 3) : Fin 2 → ℝ :=
  ![(baseEdgeCoord a 1).re, (baseEdgeCoord a 1).im]
def radiusStart : Fin 3 → ℝ := ![2, 4, 2]
def radiusEnd : Fin 3 → ℝ := ![4, 2, 2]
def heightStart : Fin 3 → ℝ := ![-1, 0, 1]
def heightEnd : Fin 3 → ℝ := ![0, 1, -1]

theorem radiusStart_pos (b : Fin 3) : 0 < radiusStart b := by
  fin_cases b <;> norm_num [radiusStart]
theorem radiusEnd_pos (b : Fin 3) : 0 < radiusEnd b := by
  fin_cases b <;> norm_num [radiusEnd]

theorem cellParam_radial (a b : Fin 3) (st : I × I) :
    cellParam a b st =
      RadialQuad.point (baseStart a) (baseEnd a) (radiusStart b) (radiusEnd b)
        (heightStart b) (heightEnd b) st.1 st.2 := by
  fin_cases a <;> fin_cases b <;> ext k <;> fin_cases k <;>
    simp [cellParam, param, baseEdge, sectionEdge, baseEdgeCoord, sectionEdgeCoord,
      radius, baseStart, baseEnd, radiusStart, radiusEnd, heightStart, heightEnd,
      RadialQuad.point, RadialQuad.radius] <;> ring <;> simp

theorem faceSet_eq_patch (a b : Fin 3) :
    faceSet a b =
      RadialQuad.patch (baseStart a) (baseEnd a) (radiusStart b) (radiusEnd b)
        (heightStart b) (heightEnd b) := by
  apply congrArg Set.range
  funext st
  exact cellParam_radial a b st

theorem radial_corners (a b : Fin 3) :
    RadialQuad.corners (baseStart a) (baseEnd a) (radiusStart b) (radiusEnd b)
        (heightStart b) (heightEnd b) =
      fun k => position (faceVertex (faceIndex a b) k) := by
  funext k
  have h := cellParam_corner a b k
  rw [cellParam_radial] at h
  fin_cases k <;> simpa only [RadialQuad.corners, squareCorner, i0, i1,
    Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using h

/-- The nine actual surface patches are precisely the convex quadrilaterals of the paper. -/
theorem faceSet_eq_convexHull (a b : Fin 3) :
    faceSet a b = convexHull ℝ
      (Set.range (fun k : Fin 4 => position (faceVertex (faceIndex a b) k))) := by
  rw [faceSet_eq_patch, RadialQuad.patch_eq_convexHull _ _ _ _ _ _
    (radiusStart_pos b) (radiusEnd_pos b), radial_corners]

theorem faceSet_convex (a b : Fin 3) : Convex ℝ (faceSet a b) := by
  rw [faceSet_eq_convexHull]
  exact convex_convexHull _ _

theorem faceSet_planar (a b : Fin 3) :
    ∀ p ∈ faceSet a b, faceNormal (faceIndex a b) ⬝ᵥ p = faceLevel (faceIndex a b) := by
  have hplane : Convex ℝ {p : Vec |
      faceNormal (faceIndex a b) ⬝ᵥ p = faceLevel (faceIndex a b)} := by
    intro x hx y hy c d hc hd hcd
    change faceNormal (faceIndex a b) ⬝ᵥ x = faceLevel (faceIndex a b) at hx
    change faceNormal (faceIndex a b) ⬝ᵥ y = faceLevel (faceIndex a b) at hy
    change faceNormal (faceIndex a b) ⬝ᵥ (c • x + d • y) = faceLevel (faceIndex a b)
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hx, hy]
    linear_combination faceLevel (faceIndex a b) * hcd
  have hs : (Set.range (fun k : Fin 4 => position (faceVertex (faceIndex a b) k))) ⊆
      {p : Vec | faceNormal (faceIndex a b) ⬝ᵥ p = faceLevel (faceIndex a b)} := by
    rintro p ⟨k, rfl⟩
    exact face_planar _ k
  rw [faceSet_eq_convexHull]
  intro p hp
  exact (convexHull_min hs hplane) hp

theorem compact_faceSet (a b : Fin 3) : IsCompact (faceSet a b) :=
  isCompact_range (continuous_cellParam a b)

def faceHomeomorph (a b : Fin 3) : (I × I) ≃ₜ faceSet a b :=
  ((continuous_cellParam a b).isClosedEmbedding (cellParam_injective a b)).toIsEmbedding.toHomeomorph

def reverseInterval (t : I) : I :=
  ⟨1 - t, by constructor <;> linarith [t.2.1, t.2.2]⟩

def squareEdge (k : Fin 4) (t : I) : I × I :=
  ![(i0, t), (t, i1), (i1, reverseInterval t), (reverseInterval t, i0)] k

/-- Each side of the square is the straight graph edge between the listed consecutive corners. -/
theorem cellParam_squareEdge (a b : Fin 3) (k : Fin 4) (t : I) :
    cellParam a b (squareEdge k t) =
      (1 - (t : ℝ)) • position (faceVertex (faceIndex a b) k) +
        (t : ℝ) • position (faceVertex (faceIndex a b) (k + 1)) := by
  fin_cases a <;> fin_cases b <;> fin_cases k <;> ext j <;> fin_cases j <;>
    norm_num [cellParam, param, baseEdge, sectionEdge, baseEdgeCoord, sectionEdgeCoord,
      radius, squareEdge, reverseInterval, i0, i1, faceIndex, position, faceVertex] <;> ring

theorem baseEdge_intersection (a c : Fin 3) (s t : I)
    (h : baseEdge a s = baseEdge c t) :
    (a = c ∧ s = t) ∨
      (((s : ℝ) = 0 ∨ (s : ℝ) = 1) ∧ ((t : ℝ) = 0 ∨ (t : ℝ) = 1)) := by
  by_cases hac : a = c
  · subst c
    exact Or.inl ⟨rfl, baseEdge_injective a h⟩
  right
  have hr := congrArg (fun x : baseGauge.Boundary => (x : ℂ).re) h
  have hi := congrArg (fun x : baseGauge.Boundary => (x : ℂ).im) h
  fin_cases a <;> fin_cases c
  all_goals
    simp only [baseEdge, baseEdgeCoord, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hr hi
    first | exact False.elim (hac rfl) |
      (constructor <;> first | exact Or.inl (by linarith) | exact Or.inr (by linarith))

theorem sectionEdge_intersection (b d : Fin 3) (s t : I)
    (h : sectionEdge b s = sectionEdge d t) :
    (b = d ∧ s = t) ∨
      (((s : ℝ) = 0 ∨ (s : ℝ) = 1) ∧ ((t : ℝ) = 0 ∨ (t : ℝ) = 1)) := by
  by_cases hbd : b = d
  · subst d
    exact Or.inl ⟨rfl, sectionEdge_injective b h⟩
  right
  have hr := congrArg (fun x : sectionGauge.Boundary => (x : ℂ).re) h
  have hi := congrArg (fun x : sectionGauge.Boundary => (x : ℂ).im) h
  fin_cases b <;> fin_cases d
  all_goals
    simp only [sectionEdge, sectionEdgeCoord, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hr hi
    first | exact False.elim (hbd rfl) |
      (constructor <;> first | exact Or.inl (by linarith) | exact Or.inr (by linarith))

/-- Distinct patches meet only along their common product edges or product vertices. -/
theorem cellParam_intersection (a b c d : Fin 3) (s t : I × I)
    (h : cellParam a b s = cellParam c d t) :
    ((a = c ∧ s.1 = t.1) ∨
      (((s.1 : ℝ) = 0 ∨ (s.1 : ℝ) = 1) ∧
        ((t.1 : ℝ) = 0 ∨ (t.1 : ℝ) = 1))) ∧
    ((b = d ∧ s.2 = t.2) ∨
      (((s.2 : ℝ) = 0 ∨ (s.2 : ℝ) = 1) ∧
        ((t.2 : ℝ) = 0 ∨ (t.2 : ℝ) = 1))) := by
  have hparam := param_injective h
  exact ⟨baseEdge_intersection a c s.1 t.1 (congrArg Prod.fst hparam),
    sectionEdge_intersection b d s.2 t.2 (congrArg Prod.snd hparam)⟩

end StressFlex.Torus

/-! ## Source fragment: StressFlex/Torus.lean -/

open Matrix Topology
open scoped BigOperators

namespace StressFlex.Torus

def outerPosition (i : Fin 9) : Vec := position i.succ

theorem outerPosition_injective : Function.Injective outerPosition := by
  intro i j h
  exact Fin.succ_injective _ (position_injective h)

/-- Explicit affine coordinates using A₁, A₂, A₃ and C₁; all other weights are zero. -/
def affineWeights (p : Vec) : Fin 9 → ℝ :=
  ![1 - (2 - p 0 + 2 * p 1) / 6 - (2 - p 0 - p 1) / 6 - (p 2 + 1) / 2,
    (2 - p 0 + 2 * p 1) / 6, (2 - p 0 - p 1) / 6, 0, 0, 0,
    (p 2 + 1) / 2, 0, 0]

theorem affineWeights_sum (p : Vec) : ∑ i, affineWeights p i = 1 := by
  norm_num [affineWeights, Fin.sum_univ_succ] <;> ring

theorem affineWeights_position (p : Vec) :
    ∑ i, affineWeights p i • outerPosition i = p := by
  ext k
  fin_cases k <;>
    norm_num [affineWeights, outerPosition, position, Fin.sum_univ_succ] <;> ring

/-- The example satisfies the full-affine-span requirement of the cited strong conjecture. -/
theorem outer_affineSpan_eq_top : affineSpan ℝ (Set.range outerPosition) = ⊤ := by
  apply top_le_iff.mp
  intro p hp
  have h := affineCombination_mem_affineSpan
    (s := Finset.univ) (w := affineWeights p) (affineWeights_sum p) outerPosition
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (affineWeights_sum p),
    affineWeights_position] at h
  exact h

theorem nine_distinct_vertices : (Set.range outerPosition).ncard = 9 := by
  rw [Set.ncard_range_of_injective outerPosition_injective]
  simp

theorem face_vertices_are_outer (f : Fin 9) (k : Fin 4) : faceVertex f k ≠ 0 := by
  revert f k
  decide

theorem outer_vertices_mem_surface (i : FrameworkVertex) (hi : i ≠ 0) :
    position i ∈ Surface := by
  obtain ⟨f, k, rfl⟩ := every_outer_vertex_is_face_vertex i hi
  obtain ⟨⟨a, b⟩, hab⟩ := faceIndex_bijective.2 f
  change faceIndex a b = f at hab
  rw [← hab]
  apply faceSet_subset_surface a b
  exact ⟨squareCorner k, cellParam_corner a b k⟩

theorem all_consecutive_face_triples_noncollinear (f : Fin 9) (k : Fin 4) :
    (position (faceVertex f (k + 1)) - position (faceVertex f k)) ⨯₃
      (position (faceVertex f (k + 2)) - position (faceVertex f k)) ≠ 0 := by
  fin_cases f <;> fin_cases k <;>
    norm_num [position, faceVertex, cross_apply, funext_iff, Fin.forall_fin_succ]

theorem faceVertex_injective (f : Fin 9) : Function.Injective (faceVertex f) := by
  revert f
  decide

/-- The complete counterexample: the geometric object is an embedded torus covered by the
nine specified convex quadrilaterals, and the displayed stress and fixed-apex motion violate
the proposed orthogonality identity. Every equilibrium equation includes the apex. -/
theorem stress_flex_counterexample :
    Symmetric adjacency ∧ (∀ i, ¬ adjacency i i) ∧
    Nonempty ((Circle × Circle) ≃ₜ Surface) ∧
    (Set.range outerPosition).ncard = 9 ∧
    affineSpan ℝ (Set.range outerPosition) = ⊤ ∧
    Function.Injective position ∧
    (∀ i, i ≠ 0 → position i ∈ Surface) ∧
    (⋃ a : Fin 3, ⋃ b : Fin 3, faceSet a b) = Surface ∧
    Function.Bijective (fun ab : Fin 3 × Fin 3 => faceIndex ab.1 ab.2) ∧
    (∀ a b, faceSet a b = convexHull ℝ
      (Set.range (fun k : Fin 4 => position (faceVertex (faceIndex a b) k)))) ∧
    (∀ a b, Function.Injective (cellParam a b)) ∧
    (∀ a b, Nonempty ((I × I) ≃ₜ faceSet a b)) ∧
    (∀ a b k t, cellParam a b (squareEdge k t) =
      (1 - (t : ℝ)) • position (faceVertex (faceIndex a b) k) +
        (t : ℝ) • position (faceVertex (faceIndex a b) (k + 1))) ∧
    (∀ f k, faceNormal f ⬝ᵥ position (faceVertex f k) = faceLevel f) ∧
    (∀ f, faceNormal f ⬝ᵥ position 0 ≠ faceLevel f) ∧
    (∀ f k, (position (faceVertex f (k + 1)) - position (faceVertex f k)) ⨯₃
      (position (faceVertex f (k + 2)) - position (faceVertex f k)) ≠ 0) ∧
    (∀ f, Function.Injective (faceVertex f)) ∧
    (∀ f k, faceVertex f k ≠ 0) ∧
    (∀ i, i ≠ 0 → ∃ f : Fin 9, ∃ k : Fin 4, i = faceVertex f k) ∧
    (∀ i j, i ≠ 0 → j ≠ 0 →
      (adjacency i j ↔ ∃ f : Fin 9, ∃ k : Fin 4,
        (i = faceVertex f k ∧ j = faceVertex f (k + 1)) ∨
        (j = faceVertex f k ∧ i = faceVertex f (k + 1)))) ∧
    (∀ a b c d (s t : I × I), cellParam a b s = cellParam c d t →
      (((a = c ∧ s.1 = t.1) ∨
        (((s.1 : ℝ) = 0 ∨ (s.1 : ℝ) = 1) ∧ ((t.1 : ℝ) = 0 ∨ (t.1 : ℝ) = 1))) ∧
       ((b = d ∧ s.2 = t.2) ∨
        (((s.2 : ℝ) = 0 ∨ (s.2 : ℝ) = 1) ∧ ((t.2 : ℝ) = 0 ∨ (t.2 : ℝ) = 1))))) ∧
    (∀ i j, stress i j = stress j i) ∧
    (∀ i j, ¬ adjacency i j → stress i j = 0) ∧
    (∀ i, ∑ j, stress i j • (position j - position i) = 0) ∧
    position 0 = 0 ∧ velocity 0 = 0 ∧
    (∀ i j, adjacency i j →
      (position i - position j) ⬝ᵥ (velocity i - velocity j) = 0) ∧
    (∑ i, stress 0 i • velocity i) ≠ 0 ∧
    (∑ i : Fin 9, stress 0 i.succ • velocity i.succ) = ![0, 1, 0] ∧
    (∑ i : Fin 9, stress 0 i.succ • velocity i.succ) ≠ 0 :=
  ⟨adjacency_symmetric, adjacency_irreflexive, ⟨torusHomeomorph⟩, nine_distinct_vertices, outer_affineSpan_eq_top, position_injective, outer_vertices_mem_surface,
    faces_cover_surface, faceIndex_bijective,
    faceSet_eq_convexHull, cellParam_injective, (fun a b => ⟨faceHomeomorph a b⟩),
    cellParam_squareEdge, face_planar,
    apex_outside_face_planes, all_consecutive_face_triples_noncollinear,
    faceVertex_injective, face_vertices_are_outer, every_outer_vertex_is_face_vertex,
    outer_edges_exactly_face_edges, cellParam_intersection,
    stress_symmetric, stress_supported, equilibrium, apex_position, fixed_apex, edge_motion,
    orthogonality_fails, weighted_velocity_outer, orthogonality_fails_outer⟩

end StressFlex.Torus

/-! ## Kernel axiom audit of the principal continuation and sphere conclusions. -/
#print axioms StressFlex.continuation_orthogonality
#print axioms StressFlex.Geometric.apex_equilibrium
#print axioms StressFlex.Spherical.stress_flex_orthogonality_at_apex
#print axioms StressFlex.Spherical.analytic_stress_extension_at_apex
#print axioms StressFlex.LocalCoefficient.coefficient_eq_of_mem_closure
#print axioms StressFlex.Torus.adjacency_symmetric
#print axioms StressFlex.Torus.adjacency_irreflexive
#print axioms StressFlex.Torus.stress_flex_counterexample

/-! ## Pinned upstream support for Proposition 3 -/

end
end

public section
noncomputable section

/- Exact pinned source: TauCeti.Topology.CWComplex.Classical.Subcomplex; SHA256 6b6ee0c6fa8dc95677784a20cd63be3b7172cc5d115566847d8fcd52a5234ed0. -/
section StressFlexPinnedSupport0

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# A CW complex relative to a subcomplex

Let `E` be a subcomplex of a relative CW complex `(C, D)`. Mathlib makes `E` itself a CW complex
relative to `D` (`Topology.RelCWComplex.Subcomplex.instRelCWComplex`), with the cells of `C` that
lie in `E`. This file supplies the complementary structure: `C` is a CW complex relative to `E`,
whose `n`-cells are the `n`-cells of `C` that do not lie in `E`, with the same characteristic maps
(`Topology.RelCWComplex.Subcomplex.relCWComplex`). Together the two structures split the cells of
`C` along `E`; this is how cellular invariants of the pair `(C, E)`, such as relative cellular
homology and the relative Euler characteristic, are computed from those of `C` and `E`.

The structure is not an instance: the base of a relative CW complex is an `outParam`, so `C`
cannot carry one instance for each of its subcomplexes.

A subcomplex `F` contained in another subcomplex `E` uses a subset of the cells of `E`
(`Topology.RelCWComplex.Subcomplex.le_iff_I_subset`), so it is a subcomplex of the CW complex `E`
(`Topology.RelCWComplex.Subcomplex.ofLE`). Combined with the relative structure, this makes `E`
a CW complex relative to `F`, and so lets cellular arguments run along a filtration of `C` by
subcomplexes.

## Main definitions and results

* `Topology.RelCWComplex.Subcomplex.relCWComplex`: the CW structure on `C` relative to a
  subcomplex `E`.
* `Topology.RelCWComplex.Subcomplex.relCWComplexCellEquiv`: its `n`-cells are the `n`-cells of `C`
  not in `E`.
* `Topology.RelCWComplex.Subcomplex.finite_relCWComplex`: it is finite when `C` is.
* `Topology.RelCWComplex.Subcomplex.le_iff_I_subset`: one subcomplex lies in another exactly when
  its cells do.
* `Topology.RelCWComplex.Subcomplex.ofLE`: a subcomplex `F ≤ E`, as a subcomplex of `E`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0 and Section 2.2, for CW pairs `(X, A)` with `A` a subcomplex.
-/



open Metric Set

namespace Topology.RelCWComplex.Subcomplex

variable {X : Type*} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]

/-- A relative CW complex `(C, D)` is a CW complex relative to any subcomplex `E`: its `n`-cells
are the `n`-cells of `C` that do not lie in `E`, with the characteristic maps of `C`. -/
@[instance_reducible]
def relCWComplex (E : Subcomplex C) : RelCWComplex C E where
  cell n := ↥(E.I n)ᶜ
  map n i := map n (i : cell C n)
  source_eq n i := source_eq n (i : cell C n)
  continuousOn n i := continuousOn n (i : cell C n)
  continuousOn_symm n i := continuousOn_symm n (i : cell C n)
  pairwiseDisjoint' := by
    intro ⟨n, i⟩ _ ⟨m, j⟩ _ hne
    refine pairwiseDisjoint (C := C) (mem_univ ⟨n, i⟩) (mem_univ ⟨m, j⟩) ?_
    exact Function.injective_id.sigma_map (fun _ ↦ Subtype.val_injective) |>.ne hne
  disjointBase' n i := E.disjoint_openCell_subcomplex_of_notMem i.2
  mapsTo n i := by
    classical
    obtain ⟨J, hJ⟩ := cellFrontier_subset_base_union_finite_closedCell (C := C) n (i : cell C n)
    refine ⟨fun m ↦ (J m).subtype (· ∈ (E.I m)ᶜ), ?_⟩
    rw [mapsTo_iff_image_subset]
    intro x hx
    rcases hJ hx with hxD | hx
    · exact Or.inl (E.base_subset hxD)
    simp only [mem_iUnion, exists_prop] at hx
    obtain ⟨m, hmn, j, hj, hxj⟩ := hx
    by_cases hjE : j ∈ E.I m
    · exact Or.inl (E.closedCell_subset_of_mem hjE hxj)
    · simp only [mem_union, mem_iUnion, exists_prop]
      exact Or.inr ⟨m, hmn, ⟨j, hjE⟩, by simpa using hj, hxj⟩
  closed' A hAC h := by
    refine (RelCWComplex.closed C A hAC).2 ⟨fun n j ↦ ?_, ?_⟩
    · by_cases hj : j ∈ E.I n
      · rw [← inter_eq_right.2 (E.closedCell_subset_of_mem hj), ← inter_assoc]
        exact h.2.inter isClosed_closedCell
      · exact h.1 n ⟨j, hj⟩
    · rw [← inter_eq_right.2 E.base_subset, ← inter_assoc]
      exact h.2.inter (isClosedBase C)
  isClosedBase := E.closed
  union' := by
    refine subset_antisymm (union_subset E.subset_complex
      (iUnion₂_subset fun n j ↦ closedCell_subset_complex n (j : cell C n))) ?_
    refine (RelCWComplex.union (C := C)).superset.trans <|
      union_subset (E.base_subset.trans subset_union_left) (iUnion₂_subset fun n j ↦ ?_)
    by_cases hj : j ∈ E.I n
    · exact (E.closedCell_subset_of_mem hj).trans subset_union_left
    · exact subset_union_of_subset_right
        (subset_iUnion₂ (s := fun n (j : ↥(E.I n)ᶜ) ↦ closedCell n (j : cell C n)) n ⟨j, hj⟩) _

/-- The `n`-cells of `C` relative to a subcomplex `E` are the `n`-cells of `C` not in `E`. -/
def relCWComplexCellEquiv (E : Subcomplex C) (n : ℕ) :
    @cell X _ C E E.relCWComplex n ≃ ↥(E.I n)ᶜ :=
  Equiv.refl _

/-- The characteristic maps of `C` relative to `E` are characteristic maps of `C`. -/
@[simp]
lemma map_relCWComplex (E : Subcomplex C) (n : ℕ) (i : @cell X _ C E E.relCWComplex n) :
    @map X _ C E E.relCWComplex n i = map n (E.relCWComplexCellEquiv n i : cell C n) :=
  (rfl)

/-- The open cells of `C` relative to `E` are open cells of `C`. -/
@[simp]
lemma openCell_relCWComplex (E : Subcomplex C) (n : ℕ) (i : @cell X _ C E E.relCWComplex n) :
    @openCell X _ C E E.relCWComplex n i = openCell n (E.relCWComplexCellEquiv n i : cell C n) :=
  (rfl)

/-- The closed cells of `C` relative to `E` are closed cells of `C`. -/
@[simp]
lemma closedCell_relCWComplex (E : Subcomplex C) (n : ℕ) (i : @cell X _ C E E.relCWComplex n) :
    @closedCell X _ C E E.relCWComplex n i =
      closedCell n (E.relCWComplexCellEquiv n i : cell C n) :=
  (rfl)

/-- The boundaries of the cells of `C` relative to `E` are boundaries of cells of `C`. -/
@[simp]
lemma cellFrontier_relCWComplex (E : Subcomplex C) (n : ℕ)
    (i : @cell X _ C E E.relCWComplex n) :
    @cellFrontier X _ C E E.relCWComplex n i =
      cellFrontier n (E.relCWComplexCellEquiv n i : cell C n) :=
  (rfl)

/-- The CW structure on `C` relative to a subcomplex is finite dimensional when `C` is. -/
lemma finiteDimensional_relCWComplex [FiniteDimensional C] (E : Subcomplex C) :
    @FiniteDimensional X _ C E E.relCWComplex :=
  @FiniteDimensional.mk X _ C E E.relCWComplex <| by
    filter_upwards [FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D)] with n hn
    rw [(E.relCWComplexCellEquiv n).isEmpty_congr]
    simp [isEmpty_subtype]

/-- The CW structure on `C` relative to a subcomplex is of finite type when `C` is. -/
lemma finiteType_relCWComplex [FiniteType C] (E : Subcomplex C) :
    @FiniteType X _ C E E.relCWComplex :=
  @FiniteType.mk X _ C E E.relCWComplex fun n ↦
    have := FiniteType.finite_cell (C := C) (D := D) n
    (E.relCWComplexCellEquiv n).finite_iff.2 Subtype.finite

/-- The CW structure on `C` relative to a subcomplex is finite when `C` is. -/
lemma finite_relCWComplex [Finite C] (E : Subcomplex C) :
    @Finite X _ C E E.relCWComplex :=
  @finite_of_finiteDimensional_finiteType X _ C E E.relCWComplex
    (finiteDimensional_relCWComplex E) (finiteType_relCWComplex E)

omit [T2Space X] in
/-- One subcomplex lies in another exactly when its cells are among the cells of the other. -/
lemma le_iff_I_subset {F E : Subcomplex C} : F ≤ E ↔ ∀ n, F.I n ⊆ E.I n := by
  refine ⟨fun h n i hi ↦ ?_, fun h ↦ ?_⟩
  · by_contra hiE
    obtain ⟨x, hx⟩ := openCell_nonempty (C := C) n i
    refine (E.disjoint_openCell_subcomplex_of_notMem hiE).notMem_of_mem_left hx (h ?_)
    rw [← SetLike.mem_coe, ← F.union]
    exact Or.inr (mem_iUnion₂.2 ⟨n, ⟨i, hi⟩, hx⟩)
  · rw [← SetLike.coe_subset_coe, ← F.union, ← E.union]
    exact union_subset_union_right D
      (iUnion_mono fun n ↦ iUnion_mono' fun j ↦ ⟨⟨j, h n j.2⟩, subset_rfl⟩)

/-- A subcomplex `F` of `C` contained in a subcomplex `E`, as a subcomplex of the CW complex `E`.
Its cells are the cells of `E` that are cells of `F`. -/
def ofLE {F E : Subcomplex C} (h : F ≤ E) : Subcomplex (E : Set X) where
  carrier := F
  I n := (Subtype.val : E.I n → cell C n) ⁻¹' F.I n
  closed' := F.closed
  union' := by
    rw [← F.union]
    congr 1
    refine iUnion_congr fun n ↦ iUnion_congr_of_surjective
      (fun j ↦ ⟨(j.1 : E.I n).1, j.2⟩)
      (fun j ↦ ⟨⟨⟨j.1, le_iff_I_subset.1 h n j.2⟩, j.2⟩, rfl⟩) fun j ↦ rfl

/-- As a set, `ofLE h` is the subcomplex `F`. -/
@[simp]
lemma coe_ofLE {F E : Subcomplex C} (h : F ≤ E) : (ofLE h : Set X) = F :=
  (rfl)

/-- The `n`-cells of `ofLE h` are the `n`-cells of `E` that are `n`-cells of `F`. -/
@[simp]
lemma ofLE_I {F E : Subcomplex C} (h : F ≤ E) (n : ℕ) :
    (ofLE h).I n = (Subtype.val : E.I n → cell C n) ⁻¹' F.I n :=
  (rfl)

end Topology.RelCWComplex.Subcomplex

end StressFlexPinnedSupport0

/- Exact pinned source: TauCeti.Topology.CWComplex.Classical.Map; SHA256 d55b9f60e74abbd231ba3222a04986987541a1ef5bf9a9f7addcbf9aa763a038. -/
section StressFlexPinnedSupport1

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Cellular maps of relative CW complexes

A cellular map preserves the skeletal filtration of a relative CW complex. This condition
ensures that the map restricts to each skeleton and to each consecutive skeletal pair, the
restrictions used to act on cellular chains. A map carrying the base into the base and the
characteristic map of every cell onto the characteristic map of a cell of the same dimension is
cellular (`TauCeti.isCellular_of_map_eq`).

The mathematical source is Hatcher, *Algebraic Topology*, Section 2.2.
-/


open CategoryTheory Metric Topology Topology.RelCWComplex

universe w

namespace TauCeti

variable {X Y Z : Type w} [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Z] [T2Space Z]
  {D : Set X} {E : Set Y} {F : Set Z}
  (C : Set X) [RelCWComplex C D] (C' : Set Y) [RelCWComplex C' E]

/-- A map of relative CW complexes is cellular if it preserves every stage of the skeletal
filtration. In particular, it sends the base (stage zero) into the target base. -/
abbrev IsCellular (f : TopCat.of C ⟶ TopCat.of C') : Prop :=
  ∀ n : ℕ, Set.MapsTo f
    {x : C | x.1 ∈ skeletonLT C (n : ℕ∞)}
    {y : C' | y.1 ∈ skeletonLT C' (n : ℕ∞)}

/-- The identity map preserves every skeleton. -/
lemma isCellular_id : IsCellular C C (𝟙 (TopCat.of C)) := fun _ _ h ↦ h

/-- The composite of cellular maps is cellular. -/
lemma IsCellular.comp {C'' : Set Z} [RelCWComplex C'' F]
    {f : TopCat.of C ⟶ TopCat.of C'} {g : TopCat.of C' ⟶ TopCat.of C''}
    (hf : IsCellular C C' f) (hg : IsCellular C' C'' g) :
    IsCellular C C'' (f ≫ g) := fun n _ hx ↦ hg n (hf n hx)

/-- A map of relative CW complexes carrying the base into the base and the characteristic map of
every cell onto the characteristic map of a cell of the same dimension, on the closed unit ball,
is cellular. -/
lemma isCellular_of_map_eq {f : TopCat.of C ⟶ TopCat.of C'}
    (hD : ∀ x : C, x.1 ∈ D → (f x).1 ∈ E)
    (hf : ∀ (n : ℕ) (i : cell C n), ∃ i' : cell C' n, ∀ x ∈ closedBall (0 : Fin n → ℝ) 1,
      ∀ hx : map n i x ∈ C, (f ⟨map n i x, hx⟩).1 = map n i' x) :
    IsCellular C C' f := by
  rintro n ⟨x, hxC⟩ (hx : x ∈ skeletonLT C n)
  change (f ⟨x, hxC⟩).1 ∈ skeletonLT C' n  -- the membership of a subtype point in a set
  rw [RelCWComplex.mem_skeletonLT_iff] at hx ⊢
  obtain hxD | ⟨m, hm, i, y, hy, rfl⟩ := hx
  · exact Or.inl (hD _ hxD)
  · obtain ⟨i', hi'⟩ := hf m i
    exact Or.inr ⟨m, hm, i', y, hy, (hi' y (ball_subset_closedBall hy) hxC).symm⟩

variable {f : TopCat.of C ⟶ TopCat.of C'} (hf : IsCellular C C' f)

/-- The restriction of a cellular map to the `n`-th stage of the skeletal filtration. -/
def skeletonMap (n : ℕ) : skeletonObj C n ⟶ skeletonObj C' n :=
  TopCat.ofHom ⟨fun x ↦ ⟨(f ⟨x.1, (skeletonLT C (n : ℕ∞)).subset_complex x.2⟩).1,
    hf n x.2⟩, by fun_prop⟩

/-- On points, the restriction to a skeleton agrees with the original cellular map. -/
@[simp]
lemma skeletonMap_apply (n : ℕ) (x : skeletonObj C n) :
    (skeletonMap C C' hf n).hom.toFun x =
      ⟨(f ⟨x.1, (skeletonLT C (n : ℕ∞)).subset_complex x.2⟩).1, hf n x.2⟩ := by
  simp [skeletonMap]

/-- Restriction of a cellular map commutes with inclusions of skeleta. -/
@[reassoc]
lemma skeletonMap_comp_inclusion {n m : ℕ} (h : n ≤ m) :
    skeletonMap C C' hf n ≫
      TopCat.ofHom (ContinuousMap.inclusion (skeletonLT_mono (C := C') (mod_cast h))) =
    TopCat.ofHom (ContinuousMap.inclusion (skeletonLT_mono (C := C) (mod_cast h))) ≫
      skeletonMap C C' hf m := by
  ext x
  rfl

/-- Restriction of a cellular map commutes with inclusion of a skeleton into the complex. -/
@[reassoc]
lemma skeletonMap_comp_inclusion_complex (n : ℕ) :
    skeletonMap C C' hf n ≫
      TopCat.ofHom (ContinuousMap.inclusion (skeletonLT C' n).subset_complex) =
    TopCat.ofHom (ContinuousMap.inclusion (skeletonLT C n).subset_complex) ≫ f := by
  ext x
  rfl

/-- Restriction of the identity map to a skeleton is the identity. -/
@[simp]
lemma skeletonMap_id (n : ℕ) :
    skeletonMap C C (isCellular_id C) n = 𝟙 (skeletonObj C n) := by
  ext x
  rfl

variable (C'' : Set Z) [RelCWComplex C'' F]
  {g : TopCat.of C' ⟶ TopCat.of C''} (hg : IsCellular C' C'' g)

/-- Restriction to a skeleton respects composition of cellular maps. -/
@[reassoc]
lemma skeletonMap_comp (n : ℕ) :
    skeletonMap C C'' (IsCellular.comp C C' hf hg) n =
      skeletonMap C C' hf n ≫ skeletonMap C' C'' hg n := by
  ext x
  rfl

end TauCeti

end StressFlexPinnedSupport1

/- Exact pinned source: TauCeti.AlgebraicTopology.Cellular.Map; SHA256 f16f0e7726b387a0030527232e9e0eb46094aeb4f1b758d7db94c6dfaf8a15b0. -/
section StressFlexPinnedSupport2

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Cellular maps act on cellular chains

A continuous map between the carriers of relative CW complexes is cellular when it carries each
stage of the skeletal filtration into the stage of the same degree. It then induces maps of
consecutive skeletal pairs. Naturality of the connecting morphism of a pair shows that these maps
commute with the cellular differential, giving a chain map. Restrictions to skeleta relative
to the base and the map of the whole base pairs commute with the skeletal inclusions. These
are the maps used in the natural cellular–singular comparison. This construction keeps the
maps of pairs visible, so the resulting chain map is induced by the original continuous map.

The mathematical source is Hatcher, *Algebraic Topology*, Section 2.2.
-/



open CategoryTheory Limits Topology Topology.RelCWComplex

universe w v u

namespace TauCeti

variable {X Y : Type w} [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Y] [T2Space Y]
  {D : Set X} {E : Set Y}
  (C : Set X) [RelCWComplex C D] (C' : Set Y) [RelCWComplex C' E]

variable {f : TopCat.of C ⟶ TopCat.of C'} (hf : IsCellular C C' f)

/-- The restrictions to three consecutive skeleta form a map of skeletal triples. -/
private def skeletonTripleMap (n : ℕ) : skeletonTriple C n ⟶ skeletonTriple C' n :=
  ⟨ComposableArrows.homMk₂ (skeletonMap C C' hf n)
    (skeletonMap C C' hf (n + 1)) (skeletonMap C C' hf (n + 2))
    (skeletonMap_comp_inclusion C C' hf n.le_succ).symm
    (skeletonMap_comp_inclusion C C' hf (n + 1).le_succ).symm⟩

/-- The restrictions to two consecutive skeleta form a map of skeletal pairs. -/
def skeletonPairMap (n : ℕ) : skeletonPair C n ⟶ skeletonPair C' n :=
  TopTriple.innerPair.map (skeletonTripleMap C C' hf n)

@[simp]
lemma skeletonPairMap_fst (n : ℕ) :
    TopPair.Hom.fst (skeletonPairMap C C' hf n) = skeletonMap C C' hf (n + 1) := by
  exact TopTriple.innerPair_map_fst (skeletonTripleMap C C' hf n)

@[simp]
lemma skeletonPairMap_snd (n : ℕ) :
    TopPair.Hom.snd (skeletonPairMap C C' hf n) = skeletonMap C C' hf n := by
  exact TopTriple.innerPair_map_snd (skeletonTripleMap C C' hf n)

/-- A cellular map restricts to each skeleton relative to the base. -/
def skeletonBasePairMap (n : ℕ) : skeletonBasePair C n ⟶ skeletonBasePair C' n :=
  TopPair.ofHom (skeletonMap C C' hf (n + 1)) (skeletonMap C C' hf 0)
    (skeletonMap_comp_inclusion C C' hf (Nat.zero_le (n + 1)))

@[simp]
lemma skeletonBasePairMap_fst (n : ℕ) :
    TopPair.Hom.fst (skeletonBasePairMap C C' hf n) = skeletonMap C C' hf (n + 1) := (rfl)

@[simp]
lemma skeletonBasePairMap_snd (n : ℕ) :
    TopPair.Hom.snd (skeletonBasePairMap C C' hf n) = skeletonMap C C' hf 0 := (rfl)

/-- A cellular map induces a map of the whole complexes relative to their bases. -/
def complexBasePairMap : complexBasePair C ⟶ complexBasePair C' :=
  TopPair.ofHom f (skeletonMap C C' hf 0) (skeletonMap_comp_inclusion_complex C C' hf 0)

@[simp]
lemma complexBasePairMap_fst : TopPair.Hom.fst (complexBasePairMap C C' hf) = f := (rfl)

@[simp]
lemma complexBasePairMap_snd :
    TopPair.Hom.snd (complexBasePairMap C C' hf) = skeletonMap C C' hf 0 := (rfl)

/-- Restriction relative to the base commutes with inclusions between skeleta. -/
@[reassoc]
lemma skeletonBasePairMap_comp_inclusion {n m : ℕ} (h : n ≤ m) :
    skeletonBasePairMap C C' hf n ≫ skeletonBasePairInclusion C' h =
      skeletonBasePairInclusion C h ≫ skeletonBasePairMap C C' hf m := by
  refine MorphismProperty.Arrow.Hom.ext ?_ ?_
  · simp only [MorphismProperty.Comma.comp_left, skeletonBasePairMap_snd]
    ext x
    -- The pair subspace objects and their skeletal presentations agree at default transparency.
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      skeletonBasePairInclusion_snd_apply, skeletonBasePairInclusion_snd_apply]
    rfl
  · simp only [MorphismProperty.Comma.comp_right, skeletonBasePairMap_fst]
    have hC : (skeletonBasePairInclusion C h).right =
        TopCat.ofHom (ContinuousMap.inclusion
          (skeletonLT_mono (C := C) (mod_cast Nat.add_le_add_right h 1))) := by
      ext x
      exact Subtype.ext (coe_skeletonBasePairInclusion_fst_apply C h x)
    have hC' : (skeletonBasePairInclusion C' h).right =
        TopCat.ofHom (ContinuousMap.inclusion
          (skeletonLT_mono (C := C') (mod_cast Nat.add_le_add_right h 1))) := by
      ext x
      exact Subtype.ext (coe_skeletonBasePairInclusion_fst_apply C' h x)
    -- Use the ambient skeletal presentations when rewriting the pair components.
    erw [hC, hC']
    exact skeletonMap_comp_inclusion C C' hf (Nat.add_le_add_right h 1)

/-- Restriction relative to the base commutes with the map to a consecutive skeletal pair. -/
@[reassoc]
lemma skeletonBasePairMap_comp_toSkeletonPair (n : ℕ) :
    skeletonBasePairMap C C' hf n ≫ skeletonBasePairToSkeletonPair C' n =
      skeletonBasePairToSkeletonPair C n ≫ skeletonPairMap C C' hf n := by
  refine MorphismProperty.Arrow.Hom.ext ?_ ?_
  · simp only [MorphismProperty.Comma.comp_left, skeletonBasePairMap_snd, skeletonPairMap_snd,
      skeletonBasePairToSkeletonPair_snd]
    exact skeletonMap_comp_inclusion C C' hf (Nat.zero_le n)
  · simp only [MorphismProperty.Comma.comp_right, skeletonBasePairMap_fst, skeletonPairMap_fst,
      skeletonBasePairToSkeletonPair_fst]
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- Restriction relative to the base commutes with inclusion into the whole complex. -/
@[reassoc]
lemma skeletonBasePairMap_comp_toComplex (n : ℕ) :
    skeletonBasePairMap C C' hf n ≫ skeletonBasePairToComplex C' n =
      skeletonBasePairToComplex C n ≫ complexBasePairMap C C' hf := by
  refine MorphismProperty.Arrow.Hom.ext ?_ ?_
  · simp only [MorphismProperty.Comma.comp_left, skeletonBasePairMap_snd, complexBasePairMap_snd,
      skeletonBasePairToComplex_snd]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · simp only [MorphismProperty.Comma.comp_right, skeletonBasePairMap_fst, complexBasePairMap_fst,
      skeletonBasePairToComplex_fst]
    exact skeletonMap_comp_inclusion_complex C C' hf (n + 1)

/-- Restriction of the identity map to a skeletal pair is the identity pair map. -/
@[simp]
lemma skeletonPairMap_id (n : ℕ) :
    skeletonPairMap C C (isCellular_id C) n = 𝟙 (skeletonPair C n) := by
  ext : 1 <;> simp [skeletonPairMap_fst, skeletonPairMap_snd]

/-- The identity cellular map restricts to the identity on each base pair. -/
@[simp]
lemma skeletonBasePairMap_id (n : ℕ) :
    skeletonBasePairMap C C (isCellular_id C) n = 𝟙 (skeletonBasePair C n) := by
  ext : 1 <;> simp <;> rfl

/-- The identity cellular map induces the identity on the whole base pair. -/
@[simp]
lemma complexBasePairMap_id :
    complexBasePairMap C C (isCellular_id C) = 𝟙 (complexBasePair C) := by
  ext : 1 <;> simp <;> rfl

variable {Z : Type w} [TopologicalSpace Z] [T2Space Z] {F : Set Z}
  (C'' : Set Z) [RelCWComplex C'' F]
  {g : TopCat.of C' ⟶ TopCat.of C''} (hg : IsCellular C' C'' g)

/-- Maps of skeletal pairs respect composition of cellular maps. -/
@[reassoc]
lemma skeletonPairMap_comp (n : ℕ) :
    skeletonPairMap C C'' (IsCellular.comp C C' hf hg) n =
      skeletonPairMap C C' hf n ≫ skeletonPairMap C' C'' hg n := by
  ext : 1
  · exact skeletonMap_comp C C' hf C'' hg n
  · exact skeletonMap_comp C C' hf C'' hg (n + 1)

/-- Restrictions to base pairs respect composition of cellular maps. -/
@[reassoc]
lemma skeletonBasePairMap_comp (n : ℕ) :
    skeletonBasePairMap C C'' (IsCellular.comp C C' hf hg) n =
      skeletonBasePairMap C C' hf n ≫ skeletonBasePairMap C' C'' hg n := by
  refine MorphismProperty.Arrow.Hom.ext ?_ ?_
  · exact skeletonMap_comp C C' hf C'' hg 0
  · exact skeletonMap_comp C C' hf C'' hg (n + 1)

/-- Maps of whole base pairs respect composition of cellular maps. -/
@[reassoc]
lemma complexBasePairMap_comp :
    complexBasePairMap C C'' (IsCellular.comp C C' hf hg) =
      complexBasePairMap C C' hf ≫ complexBasePairMap C' C'' hg := by
  refine MorphismProperty.Arrow.Hom.ext ?_ ?_
  · exact skeletonMap_comp C C' hf C'' hg 0
  · rfl

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- A cellular map induces a morphism on each cellular chain group. -/
def cellularChainGroupMap (n : ℕ) :
    cellularChainGroup C R n ⟶ cellularChainGroup C' R n :=
  TopPair.singularHomologyMap (skeletonPairMap C C' hf n) R n

/-- The map on a cellular chain group is relative singular homology of the skeletal pair map.
This formula allows importing modules to rewrite without exposing the definition's body. -/
lemma cellularChainGroupMap_def (n : ℕ) :
    cellularChainGroupMap C C' hf R n =
      TopPair.singularHomologyMap (skeletonPairMap C C' hf n) R n := (rfl)

/-- The identity cellular map acts as the identity on each cellular chain group. -/
@[simp]
lemma cellularChainGroupMap_id (n : ℕ) :
    cellularChainGroupMap C C (isCellular_id C) R n = 𝟙 (cellularChainGroup C R n) := by
  simp [cellularChainGroupMap, skeletonPairMap_id,
    TopPair.singularHomologyMap]

/-- The maps on cellular chain groups respect composition of cellular maps. -/
@[reassoc]
lemma cellularChainGroupMap_comp (n : ℕ) :
    cellularChainGroupMap C C'' (IsCellular.comp C C' hf hg) R n =
      cellularChainGroupMap C C' hf R n ≫ cellularChainGroupMap C' C'' hg R n := by
  rw [cellularChainGroupMap,
    skeletonPairMap_comp C C' hf C'' hg n]
  rw [TopPair.singularHomologyMap, Functor.map_comp, SSetPair.homologyMap_comp]
  rfl

/-- The cellular chain-group maps commute with the cellular differential. -/
@[reassoc]
lemma cellularChainGroupMap_comp_cellularDifferential (n : ℕ) :
    cellularChainGroupMap C C' hf R (n + 1) ≫ cellularDifferential C' R n =
      cellularDifferential C R n ≫ cellularChainGroupMap C C' hf R n := by
  rw [cellularDifferential_eq_singularHomologyδ,
    cellularDifferential_eq_singularHomologyδ]
  exact (TopTriple.singularHomologyδ_naturality
    (skeletonTripleMap C C' hf n) R (n + 1) n).symm

/-- A cellular map induces a chain map between the cellular chain complexes. -/
def cellularChainComplexMap : cellularChainComplex C R ⟶ cellularChainComplex C' R :=
  ChainComplex.ofHom (fun n ↦
    eqToHom (cellularChainComplex_X C R n) ≫ cellularChainGroupMap C C' hf R n ≫
      eqToHom (cellularChainComplex_X C' R n).symm)
    (by
      intro n
      simp only [cellularChainComplex_d, Category.assoc]
      simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
      simpa only [Category.assoc] using congrArg
        (fun a ↦ eqToHom (cellularChainComplex_X C R (n + 1)) ≫ a ≫
          eqToHom (cellularChainComplex_X C' R n).symm)
        (cellularChainGroupMap_comp_cellularDifferential C C' hf R n))

@[simp]
lemma cellularChainComplexMap_f (n : ℕ) :
    (cellularChainComplexMap C C' hf R).f n =
      eqToHom (cellularChainComplex_X C R n) ≫ cellularChainGroupMap C C' hf R n ≫
        eqToHom (cellularChainComplex_X C' R n).symm := (rfl)

/-- The identity cellular map induces the identity chain map. -/
@[simp]
lemma cellularChainComplexMap_id :
    cellularChainComplexMap C C (isCellular_id C) R = 𝟙 (cellularChainComplex C R) := by
  ext n
  simp only [cellularChainComplexMap_f, cellularChainGroupMap_id]
  simp

/-- Composition of cellular maps induces composition of cellular chain maps. -/
@[reassoc]
lemma cellularChainComplexMap_comp :
    cellularChainComplexMap C C'' (IsCellular.comp C C' hf hg) R =
      cellularChainComplexMap C C' hf R ≫ cellularChainComplexMap C' C'' hg R := by
  ext n
  simp only [cellularChainComplexMap_f, HomologicalComplex.comp_f]
  rw [cellularChainGroupMap_comp C C' hf C'' hg R n]
  simp [Category.assoc]

end TauCeti

end StressFlexPinnedSupport2

/- Exact pinned source: TauCeti.AlgebraicTopology.Cellular.Permutation; SHA256 7c155433fe2d180386d50ea252a149029f1ee4e2e8c1549e89e3a0dc226dbe9b. -/
section StressFlexPinnedSupport3

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Maps carrying characteristic maps to characteristic maps act on cells

Let `f` be a map between relative CW complexes that carries the base into the base and the
characteristic map of every cell onto the characteristic map of a cell of the same dimension:
`f ∘ φᵢ = φᵢ'` on the closed unit ball. Such a map is cellular
(`TauCeti.isCellular_of_map_eq`, in `TauCeti.Topology.CWComplex.Classical.Map`), and on cellular
chains it relabels the cells: the summand of the cell `i` in the cellular chain group
`Hₙ(Xⁿ, Xⁿ⁻¹)` is sent identically onto the summand of `i'`
(`TauCeti.ι_cellularChainGroupIso_inv_comp_cellularChainGroupMap`). With coefficients in a ring
this says that `f` sends each cellular basis vector to a cellular basis vector, with no sign
(`TauCeti.cellularChainGroupMap_cellularChainBasis`).

The deck transformations of the lift of a CW structure along a covering map are maps of this kind,
which is how the cellular chains of a free `G`-CW complex become modules over the group ring.
A map that only carries open cells onto open cells acts on the basis up to the local degrees
`±1` of the induced self-maps of the cells; the strict compatibility assumed here excludes signs.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, cellular maps and cellular homology.
-/



open CategoryTheory Limits Metric Topology Topology.RelCWComplex

universe w v u

namespace TauCeti

variable {X Y : Type w} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
  {D : Set X} {E : Set Y} (C : Set X) [RelCWComplex C D] (C' : Set Y) [RelCWComplex C' E]

variable {f : TopCat.of C ⟶ TopCat.of C'} (hf : IsCellular C C' f)
  {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- **A map carrying the characteristic map of `i` onto that of `i'` sends the summand of `i` in
the cellular chain group onto the summand of `i'`.** -/
@[reassoc]
lemma ι_cellularChainGroupIso_inv_comp_cellularChainGroupMap {n : ℕ}
    [HasExactColimitsOfShape (Discrete (cell C n)) A]
    [HasExactColimitsOfShape (Discrete (cell C' n)) A] {i : cell C n} {i' : cell C' n}
    (hi : ∀ x ∈ closedBall (0 : Fin n → ℝ) 1, ∀ hx : map n i x ∈ C,
      (f ⟨map n i x, hx⟩).1 = map n i' x) :
    Sigma.ι (fun _ : cell C n ↦ R) i ≫ (cellularChainGroupIso C R n).inv ≫
        cellularChainGroupMap C C' hf R n =
      Sigma.ι (fun _ : cell C' n ↦ R) i' ≫ (cellularChainGroupIso C' R n).inv := by
  rw [ι_cellularChainGroupIso_inv_eq_singularHomologyMap_characteristicCellPairMap_assoc,
    ι_cellularChainGroupIso_inv_eq_singularHomologyMap_characteristicCellPairMap,
    cellularChainGroupMap_def,
    ← TopPair.singularHomologyMap_comp]
  congr 2
  refine TopPair.hom_ext_of_fst _ (TopCat.hom_ext (ContinuousMap.ext fun p ↦ Subtype.ext ?_))
  -- Both sides send a point of the Euclidean disk to the characteristic map of the respective
  -- cell, evaluated at the radial rescaling of that point.
  simp only [MorphismProperty.Comma.comp_right, skeletonPairMap_fst]
  have hs (q : skeletonObj C (n + 1)) : ((skeletonMap C C' hf (n + 1)) q).1 =
      (f ⟨q.1, (skeletonLT C _).subset_complex q.2⟩).1 :=
    congrArg Subtype.val (skeletonMap_apply C C' hf (n + 1) q)
  have hy : (EuclideanSpace.equiv (Fin n) ℝ).unitBallHomeomorph
      ((p : ULift.{w} (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).down :
        EuclideanSpace ℝ (Fin n)) ∈ closedBall 0 1 := by
    rw [mem_closedBall_zero_iff, ContinuousLinearEquiv.norm_unitBallHomeomorph_le_one_iff,
      ← mem_closedBall_zero_iff]
    exact (p : ULift.{w} (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).down.2
  have hC : map n i _ ∈ C := closedCell_subset_complex n i ⟨_, hy, rfl⟩
  have key : ∀ (a b : X) (ha : a ∈ C) (hb : b ∈ C), a = b → (f ⟨a, ha⟩).1 = (f ⟨b, hb⟩).1 := by
    rintro a _ _ _ rfl
    rfl
  exact (hs _).trans ((key _ _ _ hC (coe_characteristicCellPairMap_fst_apply C i p)).trans
    ((hi _ hy hC).trans (coe_characteristicCellPairMap_fst_apply C' i' p).symm))

/-- **A map carrying the characteristic map of `i` onto that of `i'` sends the cellular basis
vector of `i` to the cellular basis vector of `i'`**, with coefficients in a ring. -/
lemma cellularChainGroupMap_cellularChainBasis (R : Type w) [Ring R] {n : ℕ} {i : cell C n}
    {i' : cell C' n} (hi : ∀ x ∈ closedBall (0 : Fin n → ℝ) 1, ∀ hx : map n i x ∈ C,
      (f ⟨map n i x, hx⟩).1 = map n i' x) :
    cellularChainGroupMap C C' hf (ModuleCat.of R R) n (cellularChainBasis C R n i) =
      cellularChainBasis C' R n i' := by
  rw [cellularChainBasis_apply, cellularChainBasis_apply, ← ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ι_cellularChainGroupIso_inv_comp_cellularChainGroupMap C C' hf _ hi]

end TauCeti

end StressFlexPinnedSupport3

end
end

@[expose] public section
noncomputable section

/-! ## Complete Proposition 3 source -/

/-! ### Source fragment: StressFlex/Liftings.lean -/

open Matrix
open scoped BigOperators

namespace StressFlex.Liftings

abbrev Vec := Fin 3 → ℝ

/-- Three noncollinear points of a plane avoiding zero determine a unique linear functional. -/
theorem functional_eq_zero_of_three_points
    (n p₀ p₁ p₂ a : Vec)
    (hn₀ : n ⬝ᵥ p₀ = 1) (hn₁ : n ⬝ᵥ p₁ = 1) (hn₂ : n ⬝ᵥ p₂ = 1)
    (hcross : (p₁ - p₀) ⨯₃ (p₂ - p₀) ≠ 0)
    (ha₀ : a ⬝ᵥ p₀ = 0) (ha₁ : a ⬝ᵥ p₁ = 0) (ha₂ : a ⬝ᵥ p₂ = 0) :
    a = 0 := by
  let q := (p₁ - p₀) ⨯₃ (p₂ - p₀)
  have hn := Geometric.perpendicular_decomposition hcross
    (by rw [dotProduct_comm, dotProduct_sub, hn₁, hn₀, sub_self])
    (by rw [dotProduct_comm, dotProduct_sub, hn₂, hn₀, sub_self])
  have ha := Geometric.perpendicular_decomposition hcross
    (by rw [dotProduct_comm, dotProduct_sub, ha₁, ha₀, sub_self])
    (by rw [dotProduct_comm, dotProduct_sub, ha₂, ha₀, sub_self])
  have hq : q ⬝ᵥ p₀ ≠ 0 := by
    intro hz
    have h := congrArg (fun z => z ⬝ᵥ p₀) hn
    rw [hn₀, dot_smul_left, hz, mul_zero] at h
    exact one_ne_zero h
  have hcoef : (a ⬝ᵥ q) / (q ⬝ᵥ q) = 0 := by
    have h := congrArg (fun z => z ⬝ᵥ p₀) ha
    rw [ha₀, dot_smul_left] at h
    exact (mul_eq_zero.mp h.symm).resolve_right hq
  rw [hcoef, zero_smul] at ha
  exact ha

/-- The coefficient presentation is an ordinary Mathlib affine map. -/
def affineFunctional (a : Vec) (d : ℝ) : Vec →ᵃ[ℝ] ℝ where
  toFun p := a ⬝ᵥ p + d
  linear := {
    toFun := fun p => a ⬝ᵥ p
    map_add' := fun p q => dotProduct_add a p q
    map_smul' := fun c p => dot_smul_right c a p }
  map_vadd' p v := by
    change a ⬝ᵥ (v + p) + d = a ⬝ᵥ v + (a ⬝ᵥ p + d)
    rw [dotProduct_add]
    ring

/-- Conversely every affine map on real coordinate three-space has precisely this form. -/
theorem affineMap_has_coefficients (A : Vec →ᵃ[ℝ] ℝ) :
    ∃ a : Vec, ∃ d : ℝ, ∀ p, A p = a ⬝ᵥ p + d := by
  let a : Vec := fun k => A.linear (Pi.single k 1)
  refine ⟨a, A 0, fun p => ?_⟩
  have hp : p = ∑ k : Fin 3, p k • (Pi.single k 1 : Vec) := by
    ext k
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite]
  have hL : A.linear p = a ⬝ᵥ p := by
    conv_lhs => rw [hp]
    simp only [map_sum, map_smul, smul_eq_mul, dotProduct, a]
    apply Finset.sum_congr rfl
    intro k hk
    exact mul_comm _ _
  calc
    A p = A.linear p + A 0 := congrFun (AffineMap.decomp A) p
    _ = a ⬝ᵥ p + A 0 := by rw [hL]

variable {V F : Type*} [Fintype V] [Fintype F]

/-- The paper's L(S): vertex heights affine on each actual face. -/
def affineLiftings (p : V → Vec) (face : F → V → Prop) : Submodule ℝ (V → ℝ) where
  carrier := {h | ∀ f, ∃ a : Vec, ∃ d : ℝ, ∀ v, face f v → h v = a ⬝ᵥ p v + d}
  zero_mem' := by
    intro f
    exact ⟨0, 0, fun v hv => by simp⟩
  add_mem' := by
    intro h g hh hg f
    obtain ⟨a, d, ha⟩ := hh f
    obtain ⟨b, e, hb⟩ := hg f
    refine ⟨a + b, d + e, fun v hv => ?_⟩
    change h v + g v = (a + b) ⬝ᵥ p v + (d + e)
    rw [ha v hv, hb v hv, add_dotProduct]
    ring
  smul_mem' := by
    intro c h hh f
    obtain ⟨a, d, ha⟩ := hh f
    refine ⟨c • a, c * d, fun v hv => ?_⟩
    change c * h v = (c • a) ⬝ᵥ p v + c * d
    rw [ha v hv, dot_smul_left]
    ring

/-- The definition of L(S) is equivalent to restricting genuine affine maps on each face. -/
theorem mem_affineLiftings_iff_affineMap (p : V → Vec) (face : F → V → Prop)
    (h : V → ℝ) :
    h ∈ affineLiftings p face ↔
      ∀ f, ∃ A : Vec →ᵃ[ℝ] ℝ, ∀ v, face f v → h v = A (p v) := by
  constructor
  · intro hh f
    obtain ⟨a, d, ha⟩ := hh f
    exact ⟨affineFunctional a d, ha⟩
  · intro hh f
    obtain ⟨A, hA⟩ := hh f
    obtain ⟨a, d, ha⟩ := affineMap_has_coefficients A
    exact ⟨a, d, fun v hv => (hA v hv).trans (ha (p v))⟩

def linearLiftings (p : V → Vec) (face : F → V → Prop) : Submodule ℝ (V → ℝ) where
  carrier := {h | ∀ f, ∃ a : Vec, ∀ v, face f v → h v = a ⬝ᵥ p v}
  zero_mem' := by intro f; exact ⟨0, fun v hv => by simp⟩
  add_mem' := by
    intro h g hh hg f
    obtain ⟨a, ha⟩ := hh f
    obtain ⟨b, hb⟩ := hg f
    exact ⟨a + b, fun v hv => by
      change h v + g v = (a + b) ⬝ᵥ p v
      rw [ha v hv, hb v hv, add_dotProduct]⟩
  smul_mem' := by
    intro c h hh f
    obtain ⟨a, ha⟩ := hh f
    exact ⟨c • a, fun v hv => by
      change c * h v = (c • a) ⬝ᵥ p v
      rw [ha v hv, dot_smul_left]⟩

instance coeFunLinearLiftings (p : V → Vec) (face : F → V → Prop) :
    CoeFun (linearLiftings p face) (fun _ => V → ℝ) := ⟨Subtype.val⟩

/-- The normalization n_f·p=1 converts affine face data into linear face data exactly. -/
theorem affineLiftings_eq_linearLiftings (p : V → Vec) (face : F → V → Prop)
    (n : F → Vec) (hn : ∀ f v, face f v → n f ⬝ᵥ p v = 1) :
    affineLiftings p face = linearLiftings p face := by
  ext h
  constructor
  · intro hh f
    obtain ⟨a, d, ha⟩ := hh f
    refine ⟨a + d • n f, fun v hv => ?_⟩
    rw [ha v hv, add_dotProduct, dot_smul_left, hn f v hv, mul_one]
  · intro hh f
    obtain ⟨a, ha⟩ := hh f
    exact ⟨a, 0, fun v hv => by rw [ha v hv, add_zero]⟩

def globalLinear (p : V → Vec) (face : F → V → Prop) :
    Vec →ₗ[ℝ] linearLiftings p face where
  toFun a := ⟨fun v => a ⬝ᵥ p v, fun f => ⟨a, fun v hv => rfl⟩⟩
  map_add' a b := by ext v; exact add_dotProduct a b (p v)
  map_smul' c a := by ext v; exact dot_smul_left c a (p v)

variable (p : V → Vec) (face : F → V → Prop)
  (hunique : ∀ f (a b : Vec),
    (∀ v, face f v → a ⬝ᵥ p v = b ⬝ᵥ p v) → a = b)

/-- The unique face functional of a height lifting. -/
def faceForm (h : linearLiftings p face) (f : F) : Vec := (h.2 f).choose

theorem faceForm_spec (h : linearLiftings p face) (f : F) (v : V) (hv : face f v) :
    faceForm p face h f ⬝ᵥ p v = h v := ((h.2 f).choose_spec v hv).symm

/-- The passage from vertex heights to face functionals is a genuine linear map. -/
def faceForms : linearLiftings p face →ₗ[ℝ] (F → Vec) where
  toFun := faceForm p face
  map_add' h g := by
    funext f
    apply hunique f
    intro v hv
    change faceForm p face (h + g) f ⬝ᵥ p v =
      (faceForm p face h f + faceForm p face g f) ⬝ᵥ p v
    rw [faceForm_spec p face (h + g) f v hv, add_dotProduct,
      faceForm_spec p face h f v hv, faceForm_spec p face g f v hv] <;> rfl
  map_smul' c h := by
    funext f
    apply hunique f
    intro v hv
    change faceForm p face (c • h) f ⬝ᵥ p v =
      (c • faceForm p face h f) ⬝ᵥ p v
    rw [faceForm_spec p face (c • h) f v hv, dot_smul_left,
      faceForm_spec p face h f v hv] <;> rfl

theorem faceForms_globalLinear (a : Vec) (f : F) :
    faceForms p face hunique (globalLinear p face a) f = a := by
  apply hunique f
  intro v hv
  exact faceForm_spec p face (globalLinear p face a) f v hv

end StressFlex.Liftings

/-! ### Source fragment: StressFlex/LiftingTopology.lean -/

open CategoryTheory Limits Topology Topology.RelCWComplex Matrix
open scoped BigOperators

namespace StressFlex.Spherical

variable {X : Type} [TopologicalSpace X] [T2Space X]
  [CWComplex (Set.univ : Set X)]
  [Fintype (Vertex X)] [Fintype (Edge X)] [Fintype (Face X)]
  [DecidableEq (Vertex X)]

theorem cellFrontier_edge (e : Edge X) :
    cellFrontier 1 e = {vertexPoint (tail e), vertexPoint (head e)} := by
  ext x
  rw [← TauCeti.range_cellAttachingMap]
  constructor
  · rintro ⟨q, rfl⟩
    rcases TauCeti.eq_sphereMinus_or_eq_spherePlus q with rfl | rfl
    · exact Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr (vertexPoint_head e).symm)
    · exact Set.mem_insert_iff.mpr (Or.inl (vertexPoint_tail e).symm)
  · intro hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · exact ⟨TauCeti.spherePlus, (vertexPoint_tail e).symm.trans hx.symm⟩
    · exact ⟨TauCeti.sphereMinus,
        (vertexPoint_head e).symm.trans (Set.mem_singleton_iff.mp hx).symm⟩

theorem closedCell_edge (e : Edge X) :
    closedCell 1 e =
      {vertexPoint (tail e), vertexPoint (head e)} ∪ openCell 1 e := by
  rw [← cellFrontier_union_openCell_eq_closedCell, cellFrontier_edge]

/-- In a nontrivial connected two-dimensional CW space, whole-edge face coverage already
forces vertex face coverage. An uncovered vertex would be an isolated clopen point. -/
theorem vertex_in_face_of_edge_coverage [PreconnectedSpace X] [Nontrivial X]
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n))
    (hedge : ∀ e : Edge X, ∃ f : Face X, closedCell 1 e ⊆ closedCell 2 f)
    (v : Vertex X) : ∃ f : Face X, vertexPoint v ∈ closedCell 2 f := by
  classical
  by_contra hv
  push_neg at hv
  have hmiss (n : ℕ) (hn : 0 < n) (i : cell (Set.univ : Set X) n) :
      vertexPoint v ∉ closedCell n i := by
    by_cases hn1 : n = 1
    · subst n
      obtain ⟨f, hf⟩ := hedge i
      exact fun hi => hv f (hf hi)
    by_cases hn2 : n = 2
    · subst n
      exact hv i
    haveI := hdim n (by omega)
    exact isEmptyElim i
  have hc : IsClosed ({vertexPoint v}ᶜ : Set X) := by
    apply CWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell
      (C := (Set.univ : Set X)) (Set.subset_univ _)
    intro n hn i
    right
    have hi : ({vertexPoint v}ᶜ : Set X) ∩ closedCell n i = closedCell n i := by
      apply Set.inter_eq_right.mpr
      intro y hy hyv
      exact hmiss n hn i ((Set.mem_singleton_iff.mp hyv) ▸ hy)
    rw [hi]
    exact isClosed_closedCell
  have ho : IsOpen ({vertexPoint v} : Set X) := by
    simpa only [compl_compl] using hc.isOpen_compl
  have hu : ({vertexPoint v} : Set X) = Set.univ :=
    (show IsClopen ({vertexPoint v} : Set X) from ⟨isClosed_singleton, ho⟩).eq_univ
      (Set.singleton_nonempty _)
  obtain ⟨w, hw⟩ := exists_ne (vertexPoint v)
  have hwv : w ∈ ({vertexPoint v} : Set X) := hu.symm ▸ Set.mem_univ w
  exact hw (Set.mem_singleton_iff.mp hwv)

/-- The closed graph obtained by removing a vertex and every open edge incident with it.
It is an actual CW subcomplex, so relative cellular homology is available. -/
def oppositeGraph (v : Vertex X) : CWComplex.Subcomplex (Set.univ : Set X) where
  carrier :=
    (⋃ w : {w : Vertex X // w ≠ v}, closedCell 0 w.1) ∪
    ⋃ e : {e : Edge X // tail e ≠ v ∧ head e ≠ v}, closedCell 1 e.1
  I
    | 0 => {w | w ≠ v}
    | 1 => {e | tail e ≠ v ∧ head e ≠ v}
    | _ + 2 => ∅
  closed' :=
    (isClosed_iUnion_of_finite fun _ => isClosed_closedCell).union
      (isClosed_iUnion_of_finite fun _ => isClosed_closedCell)
  union' := by
    ext x
    simp only [Set.empty_union, Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq,
      Set.mem_empty_iff_false]
    constructor
    · rintro ⟨n, j, hx⟩
      cases n with
      | zero =>
          exact Or.inl ⟨j, (openCell_subset_closedCell 0 j.1) hx⟩
      | succ n =>
          cases n with
          | zero => exact Or.inr ⟨j, (openCell_subset_closedCell 1 j.1) hx⟩
          | succ n => exact False.elim j.2
    · rintro (⟨w, hw⟩ | ⟨e, he⟩)
      · refine ⟨0, w, ?_⟩
        simpa only [closedCell_zero_eq_singleton, openCell_zero_eq_singleton] using hw
      · rw [closedCell_edge] at he
        rcases he with he | he
        · rcases Set.mem_insert_iff.mp he with he | he
          · refine ⟨0, ⟨tail e.1, e.2.1⟩, ?_⟩
            simpa only [openCell_zero_eq_singleton, Set.mem_singleton_iff, vertexPoint] using he
          · refine ⟨0, ⟨head e.1, e.2.2⟩, ?_⟩
            simpa only [openCell_zero_eq_singleton, Set.mem_singleton_iff, vertexPoint] using he
        · exact ⟨1, e, he⟩

theorem vertex_not_mem_oppositeGraph (v : Vertex X) :
    vertexPoint v ∉ (oppositeGraph v : Set X) := by
  have hm : v ∉ (oppositeGraph v).I 0 := by simp [oppositeGraph]
  have hd := (oppositeGraph v).disjoint_openCell_subcomplex_of_notMem hm
  apply hd.notMem_of_mem_left
  simp only [openCell_zero_eq_singleton, Set.mem_singleton_iff, vertexPoint]

theorem openFace_disjoint_oppositeGraph (v : Vertex X) (f : Face X) :
    Disjoint (openCell 2 f) (oppositeGraph v : Set X) :=
  (oppositeGraph v).disjoint_openCell_subcomplex_of_notMem (by simp [oppositeGraph])

end StressFlex.Spherical

/-! ### Source fragment: StressFlex/RelativeLocal.lean -/

open CategoryTheory Limits Topology Topology.RelCWComplex
open scoped BigOperators

namespace StressFlex.Cellular.Ambient

variable {X : Type} [TopologicalSpace X] [T2Space X]
  {D : Set X} (C : Set X) [RelCWComplex C D]

/-- The inclusion of the actual skeleton relative to its base into an ambient local pair. -/
def basePairToLocal (n : ℕ) (S : Set X) (hDS : D ⊆ Sᶜ) :
    TauCeti.skeletonBasePair C n ⟶ TopPair.ofSubset (X := TopCat.of X) (Sᶜ : Set X) :=
  TopPair.ofHom
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    (TopCat.ofHom ⟨fun z => ⟨z.1, hDS (by
      simpa only [Nat.cast_zero, skeletonLT_zero_eq_base] using z.2)⟩,
      continuous_subtype_val.subtype_mk _⟩) rfl

@[simp] theorem basePairToLocal_fst (n : ℕ) (S : Set X) (hDS : D ⊆ Sᶜ) :
    TopPair.Hom.fst (basePairToLocal C n S hDS) =
      TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ := rfl

/-- A point outside the preceding skeleton can read a cellular chain in ambient local homology. -/
def skeletonPairToLocal {n : ℕ} (x : X)
    (hx : x ∉ (skeletonLT C (n : ℕ∞) : Set X)) :
    TauCeti.skeletonPair C n ⟶ TopPair.ofSubset (X := TopCat.of X) ({x}ᶜ : Set X) :=
  TopPair.ofHom
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    (TopCat.ofHom ⟨fun y => ⟨y.1, fun hy => hx (hy ▸ y.2)⟩,
      continuous_subtype_val.subtype_mk _⟩) rfl

@[simp] theorem skeletonPairToLocal_fst {n : ℕ} (x : X)
    (hx : x ∉ (skeletonLT C (n : ℕ∞) : Set X)) :
    TopPair.Hom.fst (skeletonPairToLocal C x hx) =
      TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ := rfl

/-- The characteristic disk, read directly in the local homology of the ambient space. -/
def cellClass {n : ℕ} (i : cell C n) (x : X) (hx : x ∈ openCell n i) :
    Coeff ⟶ TauCeti.localHomology (A := ModuleCat.{0} ℝ) Coeff ({x} : Set X) n :=
  (TauCeti.singularHomologyDiskBoundaryPairIso Coeff n).inv ≫
    TopPair.singularHomologyMap
      (TauCeti.characteristicCellPairMap C i ≫
        skeletonPairToLocal C x (TauCeti.notMem_skeletonLT_of_mem_openCell n hx)) Coeff n

theorem basis_to_local_self {n : ℕ} (i : cell C n) (x : X) (hx : x ∈ openCell n i) :
    TopPair.singularHomologyMap
      (skeletonPairToLocal C x (TauCeti.notMem_skeletonLT_of_mem_openCell n hx)) Coeff n
        (TauCeti.cellularChainBasis C ℝ n i) = cellClass C i x hx 1 := by
  have h :
      Sigma.ι (fun _ : cell C n => Coeff) i ≫
        (TauCeti.cellularChainGroupIso C Coeff n).inv ≫
        TopPair.singularHomologyMap
          (skeletonPairToLocal C x (TauCeti.notMem_skeletonLT_of_mem_openCell n hx)) Coeff n =
      cellClass C i x hx := by
    rw [TauCeti.ι_cellularChainGroupIso_inv_eq_singularHomologyMap_characteristicCellPairMap_assoc,
      ← TopPair.singularHomologyMap_comp] <;> rfl
  simpa only [TauCeti.cellularChainBasis_apply, ConcreteCategory.comp_apply] using
    ConcreteCategory.congr_hom h (1 : ℝ)

theorem basis_to_local_of_ne {n : ℕ} (i j : cell C n) (hji : j ≠ i)
    (x : X) (hx : x ∈ openCell n i) :
    TopPair.singularHomologyMap
      (skeletonPairToLocal C x (TauCeti.notMem_skeletonLT_of_mem_openCell n hx)) Coeff n
        (TauCeti.cellularChainBasis C ℝ n j) = 0 := by
  let q := TauCeti.characteristicCellPairMap C j ≫
    skeletonPairToLocal C x (TauCeti.notMem_skeletonLT_of_mem_openCell n hx)
  have hmiss (z : TopCat.disk.{0} n) :
      (TauCeti.cellDiskHom j z : X) ≠ x := by
    intro hz
    have hmem : x ∈ closedCell n j := by
      rw [← hz]
      rw [TauCeti.coe_cellDiskHom_apply]
      exact ⟨_, (TauCeti.diskHomeomorphClosedBall n z).2, rfl⟩
    exact (TauCeti.disjoint_closedCell_openCell_of_ne n le_rfl
      (fun h => hji (eq_of_heq (Sigma.mk.inj_iff.1 h).2))).notMem_of_mem_left hmem hx
  let g : TopCat.disk.{0} n ⟶ (TopPair.ofSubset (X := TopCat.of X) ({x}ᶜ : Set X)).snd :=
    TopCat.ofHom ⟨fun z =>
      ⟨(TauCeti.cellDiskHom j z : X), hmiss z⟩,
      (continuous_subtype_val.comp
        (TauCeti.cellDiskHom j).hom.continuous).subtype_mk _⟩
  have hfac : g ≫ (TopPair.ofSubset (X := TopCat.of X) ({x}ᶜ : Set X)).map = TopPair.Hom.fst q := by
    simp only [q, TopPair.Hom.fst_comp, TauCeti.characteristicCellPairMap_fst,
      skeletonPairToLocal_fst]
    apply ConcreteCategory.ext_apply
    intro z
    rfl
  have hz := TopPair.singularHomologyMap_eq_zero_of_fac q Coeff g hfac n
  have h :
      Sigma.ι (fun _ : cell C n => Coeff) j ≫
        (TauCeti.cellularChainGroupIso C Coeff n).inv ≫
        TopPair.singularHomologyMap
          (skeletonPairToLocal C x (TauCeti.notMem_skeletonLT_of_mem_openCell n hx)) Coeff n = 0 := by
    rw [TauCeti.ι_cellularChainGroupIso_inv_eq_singularHomologyMap_characteristicCellPairMap_assoc,
      ← TopPair.singularHomologyMap_comp]
    rw [hz, Limits.comp_zero]
  simpa only [TauCeti.cellularChainBasis_apply, ConcreteCategory.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using
    ConcreteCategory.congr_hom h (1 : ℝ)

/-- The ambient local class reads exactly the coefficient of the cell containing the point. -/
theorem read_coefficient {n : ℕ} (i : cell C n) (x : X) (hx : x ∈ openCell n i)
    (a : TauCeti.cellularChainGroup (A := ModuleCat.{0} ℝ) C Coeff n) :
    TopPair.singularHomologyMap
      (skeletonPairToLocal C x (TauCeti.notMem_skeletonLT_of_mem_openCell n hx)) Coeff n a =
      (TauCeti.cellularChainBasis C ℝ n).repr a i • cellClass C i x hx 1 := by
  classical
  conv_lhs => rw [← (TauCeti.cellularChainBasis C ℝ n).linearCombination_repr a]
  simp only [Finsupp.linearCombination_apply, map_finsuppSum, map_smul]
  rw [Finsupp.sum, Finset.sum_eq_single i]
  · rw [basis_to_local_self C i x hx]
  · intro j hj hji
    rw [basis_to_local_of_ne C i j hji x hx, smul_zero]
  · intro hi
    rw [Finsupp.notMem_support_iff.mp hi, zero_smul]

/-- The base-pair representative and its cellular image have the same local restriction. -/
theorem basePairToLocal_comp_restriction {n : ℕ} (S : Set X) (hDS : D ⊆ Sᶜ)
    (x : X) (hxS : x ∈ S) (hx : x ∉ (skeletonLT C (n : ℕ∞) : Set X)) :
    TopPair.singularHomologyMap (basePairToLocal C n S hDS) Coeff n ≫
      TauCeti.localHomologyRestriction Coeff (Set.singleton_subset_iff.mpr hxS) n =
    TopPair.singularHomologyMap
      (TauCeti.skeletonBasePairToSkeletonPair C n) Coeff n ≫
      TopPair.singularHomologyMap (skeletonPairToLocal C x hx) Coeff n := by
  rw [TauCeti.localHomologyRestriction_def, ← TopPair.singularHomologyMap_comp,
    ← TopPair.singularHomologyMap_comp]
  congr 1
  apply TopPair.hom_ext_of_fst
  simp only [TopPair.Hom.fst_comp, basePairToLocal_fst, TopPair.ofSubsetMap_fst,
    TauCeti.skeletonBasePairToSkeletonPair_fst, skeletonPairToLocal_fst,
    Category.comp_id, Category.id_comp]
  all_goals
    apply ConcreteCategory.ext_apply
    intro z
    try simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply]
    all_goals
      erw [TopPair.ofSubsetMap_fst_apply] <;> rfl

/-- Every actual cellular cycle has a base-pair homology representative with precisely that
cellular image. This is the verified cellular-cycle comparison, used elementwise. -/
theorem exists_base_class (n : ℕ)
    (a : TauCeti.cellularChainGroup (A := ModuleCat.{0} ℝ) C Coeff (n + 1))
    (ha : TauCeti.cellularDifferential C Coeff n a = 0) :
    ∃ h : (TauCeti.skeletonBasePair C (n + 1)).singularHomology (C := ModuleCat.{0} ℝ) Coeff (n + 1),
      TopPair.singularHomologyMap
        (TauCeti.skeletonBasePairToSkeletonPair C (n + 1)) Coeff (n + 1) h = a := by
  let K := TauCeti.cellularChainComplex C Coeff
  let a' : K.X (n + 1) :=
    eqToHom (TauCeti.cellularChainComplex_X C Coeff (n + 1)).symm a
  have ha' : K.d (n + 1) n a' = 0 := by
    have ht : eqToHom (TauCeti.cellularChainComplex_X C Coeff (n + 1)).symm ≫
        K.d (n + 1) n =
        TauCeti.cellularDifferential C Coeff n ≫
          eqToHom (TauCeti.cellularChainComplex_X C Coeff n).symm := by
      dsimp only [K]
      rw [TauCeti.cellularChainComplex_d]
      simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
    simpa only [ConcreteCategory.comp_apply, a', ha, map_zero] using
      ConcreteCategory.congr_hom ht a
  let k : Coeff ⟶ K.X (n + 1) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℝ (K.X (n + 1)) a')
  have hk : k ≫ K.d (n + 1) n = 0 := by
    apply ConcreteCategory.ext_apply
    intro r
    change (K.d (n + 1) n).hom (r • a') = 0
    have hz' : (K.d (n + 1) n).hom a' = 0 := ha'
    rw [map_smul, hz', smul_zero]
  let z := K.liftCycles k n (by simp) hk 1
  have hz : K.iCycles (n + 1) z = a' := by
    have hi := ConcreteCategory.congr_hom (K.liftCycles_i k n (by simp) hk) (1 : ℝ)
    have hk1 : k 1 = a' := by
      change (1 : ℝ) • a' = a'
      exact one_smul ℝ a'
    rw [ConcreteCategory.comp_apply] at hi
    change K.iCycles (n + 1) z = k 1 at hi
    exact hi.trans hk1
  refine ⟨(TauCeti.cellularCyclesIso C Coeff (n + 1)).hom z, ?_⟩
  have hinc := ConcreteCategory.congr_hom
    (TauCeti.cellularCyclesIso_inv_comp_iCycles C Coeff (n + 1))
      ((TauCeti.cellularCyclesIso C Coeff (n + 1)).hom z)
  simp only [ConcreteCategory.comp_apply, Iso.hom_inv_id_apply] at hinc
  change K.iCycles (n + 1) z =
    eqToHom (TauCeti.cellularChainComplex_X C Coeff (n + 1)).symm
      (TopPair.singularHomologyMap
        (TauCeti.skeletonBasePairToSkeletonPair C (n + 1)) Coeff (n + 1)
          ((TauCeti.cellularCyclesIso C Coeff (n + 1)).hom z)) at hinc
  rw [hz] at hinc
  have hcast : Function.Injective
      (eqToHom (TauCeti.cellularChainComplex_X C Coeff (n + 1)).symm) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  exact hcast hinc.symm

end StressFlex.Cellular.Ambient

/-! ### Source fragment: StressFlex/RelativeCellular.lean -/

open CategoryTheory Limits Topology Topology.RelCWComplex Metric
open scoped BigOperators

namespace StressFlex.Cellular.Relative

variable {X : Type} [TopologicalSpace X] [T2Space X]
  (C : Set X) [CWComplex C] (K : CWComplex.Subcomplex C)

abbrev RelCell (n : ℕ) :=
  @cell X _ C (K : Set X) K.relCWComplex n

abbrev relSkeleton (n : ℕ∞) : Set X :=
  @skeletonLT X _ _ C (K : Set X) K.relCWComplex n

theorem skeleton_subset_relative (n : ℕ∞) :
    (skeletonLT C n : Set X) ⊆ relSkeleton C K n := by
  intro x hx
  obtain ⟨m, hm, i, hi⟩ := CWComplex.mem_skeletonLT_iff.mp hx
  by_cases hK : i ∈ K.I m
  · have hxK : x ∈ (K : Set X) := K.closedCell_subset_of_mem hK
      (openCell_subset_closedCell m i hi)
    letI : RelCWComplex C (K : Set X) := K.relCWComplex
    exact (skeletonLT C n).base_subset hxK
  · let j : RelCell C K m := (K.relCWComplexCellEquiv m).symm ⟨i, hK⟩
    have hji : @openCell X _ C (K : Set X) K.relCWComplex m j = openCell m i := by
      simp only [j, Subcomplex.openCell_relCWComplex, Equiv.apply_symm_apply]
    letI : RelCWComplex C (K : Set X) := K.relCWComplex
    apply RelCWComplex.mem_skeletonLT_iff.mpr
    exact Or.inr ⟨m, hm, j, hji.symm ▸ hi⟩

/-- Identity on the carrier, from the absolute CW structure to the genuine relative one. -/
theorem quotient_isCellular :
    @TauCeti.IsCellular X X _ _ _ _ ∅ (K : Set X)
      C (CWComplex.instRelCWComplex C) C K.relCWComplex (𝟙 (TopCat.of C)) := by
  intro n x hx
  exact skeleton_subset_relative C K n hx

abbrev chainGroup (n : ℕ) : ModuleCat.{0} ℝ := by
  letI : RelCWComplex C (K : Set X) := K.relCWComplex
  exact TauCeti.cellularChainGroup (A := ModuleCat.{0} ℝ) (D := (K : Set X)) C Coeff n

def quotientChains (n : ℕ) :
    TauCeti.cellularChainGroup (A := ModuleCat.{0} ℝ) C Coeff n ⟶ chainGroup C K n :=
  @TauCeti.cellularChainGroupMap X X _ _ _ _ ∅ (K : Set X)
    C (CWComplex.instRelCWComplex C) C K.relCWComplex (𝟙 (TopCat.of C))
      (quotient_isCellular C K) (ModuleCat.{0} ℝ) _ _ _ Coeff n

def basis (n : ℕ) : Module.Basis (RelCell C K n) ℝ (chainGroup C K n) := by
  letI : RelCWComplex C (K : Set X) := K.relCWComplex
  exact TauCeti.cellularChainBasis (D := (K : Set X)) C ℝ n

def keptCell {n : ℕ} (i : cell C n) (hi : i ∉ K.I n) : RelCell C K n :=
  (K.relCWComplexCellEquiv n).symm ⟨i, hi⟩

/-- A characteristic map retained by the relative CW structure retains its exact generator. -/
theorem quotientChains_basis_of_not_mem {n : ℕ} (i : cell C n) (hi : i ∉ K.I n) :
    quotientChains C K n (TauCeti.cellularChainBasis C ℝ n i) =
      basis C K n (keptCell C K i hi) := by
  apply @TauCeti.cellularChainGroupMap_cellularChainBasis X X _ _ _ _ ∅ (K : Set X)
    C (CWComplex.instRelCWComplex C) C K.relCWComplex (𝟙 (TopCat.of C))
      (quotient_isCellular C K) ℝ _ n i (keptCell C K i hi)
  intro x hx hxC
  simp only [keptCell, Subcomplex.map_relCWComplex, Equiv.apply_symm_apply] <;> rfl

def quotientPair (n : ℕ) :
    TauCeti.skeletonPair C n ⟶
      @TauCeti.skeletonPair X _ _ (K : Set X) C K.relCWComplex n :=
  @TauCeti.skeletonPairMap X X _ _ _ _ ∅ (K : Set X)
    C (CWComplex.instRelCWComplex C) C K.relCWComplex (𝟙 (TopCat.of C))
      (quotient_isCellular C K) n

/-- A discarded cell is sent into the base of the target pair, so its homology class vanishes. -/
theorem quotientChains_basis_of_mem {n : ℕ} (i : cell C n) (hi : i ∈ K.I n) :
    quotientChains C K n (TauCeti.cellularChainBasis C ℝ n i) = 0 := by
  let q := TauCeti.characteristicCellPairMap C i ≫ quotientPair C K n
  have hmem (z : TopCat.disk.{0} n) :
      (TauCeti.cellDiskHom i z : X) ∈ K := by
    apply K.closedCell_subset_of_mem hi
    rw [TauCeti.coe_cellDiskHom_apply]
    exact ⟨_, (TauCeti.diskHomeomorphClosedBall n z).2, rfl⟩
  have hskel (z : TopCat.disk.{0} n) :
      (TauCeti.cellDiskHom i z : X) ∈ relSkeleton C K n := by
    letI : RelCWComplex C (K : Set X) := K.relCWComplex
    exact (skeletonLT C n).base_subset (hmem z)
  let g : TopCat.disk.{0} n ⟶
      (@TauCeti.skeletonPair X _ _ (K : Set X) C K.relCWComplex n).snd :=
    TopCat.ofHom ⟨fun z => ⟨(TauCeti.cellDiskHom i z : X), hskel z⟩,
      (continuous_subtype_val.comp
        (TauCeti.cellDiskHom i).hom.continuous).subtype_mk hskel⟩
  have hfac : g ≫ (@TauCeti.skeletonPair X _ _ (K : Set X) C K.relCWComplex n).map =
      TopPair.Hom.fst q := by
    change g ≫ (@TauCeti.skeletonPair X _ _ (K : Set X) C K.relCWComplex n).map =
      TopPair.Hom.fst (TauCeti.characteristicCellPairMap C i ≫ quotientPair C K n)
    rw [TopPair.Hom.fst_comp, TauCeti.characteristicCellPairMap_fst]
    erw [quotientPair, TauCeti.skeletonPairMap_fst]
    ext z
    simp only [ConcreteCategory.comp_apply, TauCeti.skeletonMap_apply]
    rfl
  have hz := TopPair.singularHomologyMap_eq_zero_of_fac q Coeff g hfac n
  have hcomp :
      Sigma.ι (fun _ : cell C n => Coeff) i ≫
        (TauCeti.cellularChainGroupIso C Coeff n).inv ≫ quotientChains C K n = 0 := by
    rw [TauCeti.ι_cellularChainGroupIso_inv_eq_singularHomologyMap_characteristicCellPairMap_assoc]
    change (TauCeti.singularHomologyDiskBoundaryPairIso Coeff n).inv ≫
      TopPair.singularHomologyMap (TauCeti.characteristicCellPairMap C i) Coeff n ≫
        TopPair.singularHomologyMap (quotientPair C K n) Coeff n = 0
    rw [← TopPair.singularHomologyMap_comp, hz, Limits.comp_zero]
  simpa only [TauCeti.cellularChainBasis_apply, ConcreteCategory.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply]
    using ConcreteCategory.congr_hom hcomp (1 : ℝ)

/-- Relative cellular coordinates are obtained by deleting exactly the cells of the subcomplex. -/
theorem quotientChains_coordinate [Fintype (cell C n)] (a : TauCeti.cellularChainGroup (A := ModuleCat.{0} ℝ) C Coeff n)
    (i : cell C n) (hi : i ∉ K.I n) :
    (basis C K n).repr (quotientChains C K n a) (keptCell C K i hi) =
      (TauCeti.cellularChainBasis C ℝ n).repr a i := by
  classical
  conv_lhs => rw [← (TauCeti.cellularChainBasis C ℝ n).sum_repr a]
  simp only [map_sum, map_smul]
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single i]
  · rw [quotientChains_basis_of_not_mem C K i hi, Module.Basis.repr_self]
    simp
  · intro j hj hji
    by_cases hjK : j ∈ K.I n
    · rw [quotientChains_basis_of_mem C K j hjK, map_zero, smul_zero, Finsupp.zero_apply]
    · rw [quotientChains_basis_of_not_mem C K j hjK, Module.Basis.repr_self]
      have hne : keptCell C K j hjK ≠ keptCell C K i hi := by
        intro h
        have hv := congrArg (fun k => ((K.relCWComplexCellEquiv n k).val)) h
        exact hji (by simpa only [keptCell, Equiv.apply_symm_apply] using hv)
      simp [hne]
  · simp

abbrev baseGroup (n : ℕ) : ModuleCat.{0} ℝ := by
  letI : RelCWComplex C (K : Set X) := K.relCWComplex
  exact (TauCeti.skeletonBasePair (D := (K : Set X)) C n).singularHomology (C := ModuleCat.{0} ℝ) Coeff n

def baseToChains (n : ℕ) : baseGroup C K n ⟶ chainGroup C K n := by
  letI : RelCWComplex C (K : Set X) := K.relCWComplex
  exact TopPair.singularHomologyMap
    (TauCeti.skeletonBasePairToSkeletonPair (D := (K : Set X)) C n) Coeff n

def quotientBasePair (n : ℕ) :
    TauCeti.skeletonBasePair C n ⟶
      @TauCeti.skeletonBasePair X _ _ (K : Set X) C K.relCWComplex n :=
  @TauCeti.skeletonBasePairMap X X _ _ _ _ ∅ (K : Set X)
    C (CWComplex.instRelCWComplex C) C K.relCWComplex (𝟙 (TopCat.of C))
      (quotient_isCellular C K) n

def quotientBase (n : ℕ) :
    (TauCeti.skeletonBasePair C n).singularHomology (C := ModuleCat.{0} ℝ) Coeff n ⟶ baseGroup C K n :=
  TopPair.singularHomologyMap (quotientBasePair C K n) Coeff n

/-- The absolute-to-relative comparison commutes with passage from cycles to cellular chains. -/
theorem quotientBase_comp (n : ℕ) :
    quotientBase C K n ≫ baseToChains C K n =
      TopPair.singularHomologyMap
        (TauCeti.skeletonBasePairToSkeletonPair C n) Coeff n ≫ quotientChains C K n := by
  have h := @TauCeti.skeletonBasePairMap_comp_toSkeletonPair X X _ _ _ _
    ∅ (K : Set X) C (CWComplex.instRelCWComplex C) C K.relCWComplex
    (𝟙 (TopCat.of C)) (quotient_isCellular C K) n
  have hh := congrArg (fun f => TopPair.singularHomologyMap f Coeff n) h
  simpa only [TopPair.singularHomologyMap_comp, quotientBase, quotientBasePair,
    baseToChains, quotientChains, TauCeti.cellularChainGroupMap_def] using hh

/-- The cellular boundary commutes with deleting a genuine subcomplex. -/
theorem quotientChains_d (n : ℕ) :
    quotientChains C K (n + 1) ≫
      @TauCeti.cellularDifferential X _ _ (K : Set X) C K.relCWComplex
        (ModuleCat.{0} ℝ) _ _ _ Coeff n =
      TauCeti.cellularDifferential C Coeff n ≫ quotientChains C K n := by
  exact @TauCeti.cellularChainGroupMap_comp_cellularDifferential X X _ _ _ _
    ∅ (K : Set X) C (CWComplex.instRelCWComplex C) C K.relCWComplex
    (𝟙 (TopCat.of C)) (quotient_isCellular C K)
    (ModuleCat.{0} ℝ) _ _ _ Coeff n

end StressFlex.Cellular.Relative

/-! ### Source fragment: StressFlex/SphereTopHomology.lean -/

open CategoryTheory Limits Topology Topology.RelCWComplex Metric
open scoped BigOperators

namespace StressFlex.Cellular

abbrev TopHomology (Y : Type) [TopologicalSpace Y] :=
  ((AlgebraicTopology.singularHomologyFunctor.{0} (ModuleCat.{0} ℝ) 2).obj Coeff).obj (TopCat.of Y)

/-- The actual second singular homology of a topological sphere, with its chosen orientation. -/
def singularTopIso {Y : Type} [TopologicalSpace Y] (hS : Y ≃ₜ TopCat.sphere.{0} 2) :
    TopHomology Y ≅ Coeff := by
  haveI : IsIso ((TauCeti.reducedSingularHomologyι Coeff 2).app (TopCat.sphere.{0} 2)) := by
    rw [TauCeti.reducedSingularHomologyι_succ_app]
    infer_instance
  exact (((AlgebraicTopology.singularHomologyFunctor.{0} (ModuleCat.{0} ℝ) 2).obj Coeff).mapIso
    (TopCat.isoOfHomeo hS)) ≪≫
      (asIso ((TauCeti.reducedSingularHomologyι Coeff 2).app (TopCat.sphere.{0} 2))).symm ≪≫
        TauCeti.reducedSingularHomologyTopCatSphereIso Coeff 2

/-- The sphere's global generator remains a generator in local homology at every point. -/
theorem global_to_local_isIso {Y : Type} [TopologicalSpace Y]
    (hS : Y ≃ₜ TopCat.sphere.{0} 2) (x : Y) :
    IsIso ((TopPair.ofSubset (X := TopCat.of Y) ({x}ᶜ : Set Y)).singularHomologyπ (C := ModuleCat.{0} ℝ) Coeff 2) := by
  let e : Y ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    hS.trans Homeomorph.ulift
  haveI : ContractibleSpace (TopPair.ofSubset (X := TopCat.of Y) ({x}ᶜ : Set Y)).snd :=
    (e.subtype (q := (· ∈ ({e x}ᶜ : Set _))) fun y =>
      not_congr e.injective.eq_iff.symm).contractibleSpace_iff.mpr
        (TauCeti.contractibleSpace_sphere_compl_singleton _)
  exact TopPair.isIso_singularHomologyπ_of_contractibleSpace _ Coeff 1

variable {X : Type} [TopologicalSpace X] [T2Space X]
  [CWComplex (Set.univ : Set X)]

/-- The top skeleton is the actual whole space, with the underlying inclusion exposed. -/
def skeletonToSpaceHomeomorph
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n)) :
    TauCeti.skeletonObj (Set.univ : Set X) 3 ≃ₜ X :=
  (Homeomorph.setCongr
    (TauCeti.skeletonLT_eq_complex_of_isEmpty_cell (Set.univ : Set X) 3 hdim)).trans
      (Homeomorph.Set.univ X)

@[simp] theorem skeletonToSpaceHomeomorph_apply
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n))
    (x : TauCeti.skeletonObj (Set.univ : Set X) 3) :
    skeletonToSpaceHomeomorph hdim x = (x : X) := rfl

def skeletonTwoHomeomorph (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n)) :
    TauCeti.skeletonObj (Set.univ : Set X) 3 ≃ₜ TopCat.sphere.{0} 2 :=
  (skeletonToSpaceHomeomorph hdim).trans hS

/-- The top generator is transported through the actual inclusion into the ambient sphere. -/
def skeletalTopIso (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n)) :
    TopHomology (TauCeti.skeletonObj (Set.univ : Set X) 3) ≅ Coeff :=
  (((AlgebraicTopology.singularHomologyFunctor.{0} (ModuleCat.{0} ℝ) 2).obj Coeff).mapIso
    (TopCat.isoOfHomeo (skeletonToSpaceHomeomorph hdim))) ≪≫ singularTopIso hS

/-- The base of an absolute CW structure is empty, so its ordinary-to-relative
homology projection is an isomorphism in every degree. -/
theorem isIso_skeletonBase_projection (n : ℕ) :
    IsIso ((TauCeti.skeletonBasePair (Set.univ : Set X) n).singularHomologyπ
      (C := ModuleCat.{0} ℝ) Coeff n) := by
  letI : IsEmpty (TauCeti.skeletonBasePair (Set.univ : Set X) n).snd := by
    change IsEmpty (skeletonLT (Set.univ : Set X) (0 : ℕ∞) : Set X)
    rw [skeletonLT_zero_eq_base]
    infer_instance
  infer_instance

/-- No combinatorial assertion is used to identify the kernel of the face boundary:
it is the actual group of cellular cycles, then H₂(S²;ℝ). -/
def topCyclesIso (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n)) :
    (TauCeti.cellularChainComplex (A := ModuleCat.{0} ℝ) (Set.univ : Set X) Coeff).cycles 2 ≅ Coeff := by
  haveI := isIso_skeletonBase_projection (X := X) 2
  exact TauCeti.cellularCyclesIso (A := ModuleCat.{0} ℝ) (Set.univ : Set X) Coeff 2 ≪≫
    (asIso ((TauCeti.skeletonBasePair (Set.univ : Set X) 2).singularHomologyπ (C := ModuleCat.{0} ℝ) Coeff 2)).symm ≪≫
      skeletalTopIso hS hdim

/-- The actual cellular differential in full finite coordinates, including zero coefficients. -/
theorem boundary_coefficient_sum (n : ℕ)
    [Fintype (cell (Set.univ : Set X) (n + 1))]
    (a : TauCeti.cellularChainGroup (A := ModuleCat.{0} ℝ) (Set.univ : Set X) Coeff (n + 1))
    (e : cell (Set.univ : Set X) n) :
    (TauCeti.cellularChainBasis (Set.univ : Set X) ℝ n).repr
      (TauCeti.cellularDifferential (A := ModuleCat.{0} ℝ) (Set.univ : Set X) Coeff n a) e =
      ∑ f, TauCeti.cellularIncidence (Set.univ : Set X) ℝ n e f *
        (TauCeti.cellularChainBasis (Set.univ : Set X) ℝ (n + 1)).repr a f := by
  classical
  rw [TauCeti.cellularChainBasis_repr_differential_apply]
  have hs :
      (∑ f ∈ ((TauCeti.cellularChainBasis (Set.univ : Set X) ℝ (n + 1)).repr a).support,
        (TauCeti.cellularChainBasis (Set.univ : Set X) ℝ (n + 1)).repr a f *
          TauCeti.cellularIncidence (Set.univ : Set X) ℝ n e f) =
      ∑ f, (TauCeti.cellularChainBasis (Set.univ : Set X) ℝ (n + 1)).repr a f *
        TauCeti.cellularIncidence (Set.univ : Set X) ℝ n e f := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro f hf hnot
    rw [Finsupp.notMem_support_iff.mp hnot, zero_mul]
  simpa only [mul_comm] using hs

variable [Fintype (cell (Set.univ : Set X) 2)]

def fundamentalChain (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n)) :
    TauCeti.cellularChainGroup (A := ModuleCat.{0} ℝ) (Set.univ : Set X) Coeff 2 :=
  TauCeti.skeletonPairπ (A := ModuleCat.{0} ℝ) (Set.univ : Set X) Coeff 2
    ((skeletalTopIso hS hdim).inv 1)

def fundamentalCellularCycle (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n)) :
    cell (Set.univ : Set X) 2 → ℝ :=
  fun f => (TauCeti.cellularChainBasis (Set.univ : Set X) ℝ 2).repr
    (fundamentalChain hS hdim) f

/-- Reading any cellular chain at a point of an open face selects exactly that face's coefficient. -/
theorem local_value_of_cellular_chain
    (f : cell (Set.univ : Set X) 2)
    (x : TauCeti.skeletonObj (Set.univ : Set X) 3)
    (hx : (x : X) ∈ openCell 2 f)
    (a : TauCeti.cellularChainGroup (A := ModuleCat.{0} ℝ) (Set.univ : Set X) Coeff 2) :
    TopPair.singularHomologyMap (C := ModuleCat.{0} ℝ)
      (TauCeti.skeletonPairToComplSingleton (Set.univ : Set X) x
        (TauCeti.notMem_skeletonLT_of_mem_openCell 2 hx)) Coeff 2 a =
      (TauCeti.cellularChainBasis (Set.univ : Set X) ℝ 2).repr a f •
        TauCeti.cellLocalClass (Set.univ : Set X) Coeff x hx 1 := by
  classical
  conv_lhs =>
    rw [← (TauCeti.cellularChainBasis (Set.univ : Set X) ℝ 2).linearCombination_repr a]
  simp only [Finsupp.linearCombination_apply, map_finsuppSum, map_smul]
  rw [Finsupp.sum]
  rw [Finset.sum_eq_single f]
  · rw [TauCeti.singularHomologyMap_skeletonPairToComplSingleton_cellularChainBasis_self]
  · intro g hg hgf
    rw [TauCeti.singularHomologyMap_skeletonPairToComplSingleton_cellularChainBasis_of_ne
      (Set.univ : Set X) ℝ x hx hgf, smul_zero]
  · intro hf
    rw [Finsupp.notMem_support_iff.mp hf, zero_smul]

/-- Passing from the empty base to the preceding skeleton factors the ordinary projection. -/
theorem base_projection_comp (n : ℕ) :
    (TauCeti.skeletonBasePair (Set.univ : Set X) n).singularHomologyπ (C := ModuleCat.{0} ℝ) Coeff n ≫
      TopPair.singularHomologyMap (C := ModuleCat.{0} ℝ)
        (TauCeti.skeletonBasePairToSkeletonPair (Set.univ : Set X) n) Coeff n =
      TauCeti.skeletonPairπ (A := ModuleCat.{0} ℝ) (Set.univ : Set X) Coeff n := by
  have h := TopPair.singularHomologyπ_naturality (C := ModuleCat.{0} ℝ)
    (TauCeti.skeletonBasePairToSkeletonPair (Set.univ : Set X) n) (R := Coeff) n
  erw [TauCeti.skeletonBasePairToSkeletonPair_fst, CategoryTheory.Functor.map_id,
    SSet.homologyMap_id, Category.id_comp] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
theorem mono_skeleton_projection (n : ℕ) :
    Mono (TauCeti.skeletonPairπ (A := ModuleCat.{0} ℝ) (Set.univ : Set X) Coeff n) := by
  haveI := isIso_skeletonBase_projection (X := X) n
  haveI : Mono (TopPair.singularHomologyMap (C := ModuleCat.{0} ℝ)
      (TauCeti.skeletonBasePairToSkeletonPair (Set.univ : Set X) n) Coeff n) :=
    TauCeti.mono_singularHomologyMap_skeletonBasePairToSkeletonPair
      (A := ModuleCat.{0} ℝ) (Set.univ : Set X) Coeff n
  rw [← base_projection_comp]
  exact CategoryTheory.mono_comp'
    (show Mono ((TauCeti.skeletonBasePair (Set.univ : Set X) n).singularHomologyπ
      (C := ModuleCat.{0} ℝ) Coeff n) from inferInstance)
    (TauCeti.mono_singularHomologyMap_skeletonBasePairToSkeletonPair
      (A := ModuleCat.{0} ℝ) (Set.univ : Set X) Coeff n)

theorem fundamentalChain_closed (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n)) :
    TauCeti.cellularDifferential (A := ModuleCat.{0} ℝ) (Set.univ : Set X) Coeff 1
      (fundamentalChain hS hdim) = 0 := by
  have hz : TauCeti.skeletonPairπ (A := ModuleCat.{0} ℝ) (Set.univ : Set X) Coeff 2 ≫
      TauCeti.cellularDifferential (A := ModuleCat.{0} ℝ) (Set.univ : Set X) Coeff 1 = 0 := by
    rw [TauCeti.cellularDifferential_eq_skeletonPairδ_comp_skeletonPairπ,
      ← Category.assoc, TauCeti.skeletonPairπ_comp_skeletonPairδ, Limits.zero_comp]
  exact ConcreteCategory.congr_hom hz
    ((skeletalTopIso hS hdim).inv 1)

set_option backward.isDefEq.respectTransparency false in
theorem fundamentalChain_ne_zero (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n)) :
    fundamentalChain hS hdim ≠ 0 := by
  haveI := mono_skeleton_projection (X := X) 2
  intro hz
  have h := (ModuleCat.mono_iff_injective
    (TauCeti.skeletonPairπ (A := ModuleCat.{0} ℝ) (Set.univ : Set X) Coeff 2)).mp inferInstance
      (hz.trans (map_zero _).symm)
  change (skeletalTopIso hS hdim).symm.toLinearEquiv (1 : ℝ) = 0 at h
  have h10 : (1 : ℝ) = 0 :=
    (skeletalTopIso hS hdim).symm.toLinearEquiv.map_eq_zero_iff.mp h
  exact one_ne_zero h10

/-- Every genuine face has a nonzero coefficient in the fundamental cellular cycle. -/
theorem fundamentalCellularCycle_ne_zero (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n))
    (f : cell (Set.univ : Set X) 2) :
    fundamentalCellularCycle hS hdim f ≠ 0 := by
  obtain ⟨x₀, hx₀⟩ := openCell_nonempty (C := (Set.univ : Set X)) 2 f
  let x : TauCeti.skeletonObj (Set.univ : Set X) 3 :=
    ⟨x₀, openCell_subset_skeletonLT 2 f hx₀⟩
  let I := skeletalTopIso hS hdim
  let P := TopPair.ofSubset (X := TauCeti.skeletonObj (Set.univ : Set X) 3)
    ({x}ᶜ : Set (TauCeti.skeletonObj (Set.univ : Set X) 3))
  haveI : IsIso (P.singularHomologyπ (C := ModuleCat.{0} ℝ) Coeff 2) :=
    global_to_local_isIso (skeletonTwoHomeomorph hS hdim) x
  have hlocal : P.singularHomologyπ (C := ModuleCat.{0} ℝ) Coeff 2 (I.inv 1) ≠ 0 := by
    intro h
    have h'' : I.inv 1 = 0 :=
      (ModuleCat.mono_iff_injective (P.singularHomologyπ (C := ModuleCat.{0} ℝ) Coeff 2)).mp
        inferInstance (h.trans (map_zero _).symm)
    have h''' := congrArg I.hom h''
    have h10 : (1 : ℝ) = 0 := by
      simpa only [Iso.inv_hom_id_apply, map_zero] using h'''
    exact one_ne_zero h10
  have hr := local_value_of_cellular_chain f x hx₀ (fundamentalChain hS hdim)
  have hp := ConcreteCategory.congr_hom
    (TauCeti.skeletonPairπ_comp_singularHomologyMap_skeletonPairToComplSingleton
      (Set.univ : Set X) Coeff x (TauCeti.notMem_skeletonLT_of_mem_openCell 2 hx₀)) (I.inv 1)
  intro hz
  apply hlocal
  calc
    P.singularHomologyπ (C := ModuleCat.{0} ℝ) Coeff 2 (I.inv 1) =
        TopPair.singularHomologyMap (C := ModuleCat.{0} ℝ)
          (TauCeti.skeletonPairToComplSingleton (Set.univ : Set X) x
            (TauCeti.notMem_skeletonLT_of_mem_openCell 2 hx₀)) Coeff 2
          (fundamentalChain hS hdim) := hp.symm
    _ = 0 := by
      rw [hr]
      change fundamentalCellularCycle hS hdim f • _ = 0
      rw [hz, zero_smul]

/-- Elementwise lifting into the actual categorical kernel of the cellular differential. -/
theorem exists_cycles_element
    (a : (TauCeti.cellularChainComplex (A := ModuleCat.{0} ℝ) (Set.univ : Set X) Coeff).X 2)
    (ha : (TauCeti.cellularChainComplex (A := ModuleCat.{0} ℝ) (Set.univ : Set X) Coeff).d 2 1 a = 0) :
    ∃ z, (TauCeti.cellularChainComplex (A := ModuleCat.{0} ℝ) (Set.univ : Set X) Coeff).iCycles 2 z = a := by
  let K := TauCeti.cellularChainComplex (A := ModuleCat.{0} ℝ) (Set.univ : Set X) Coeff
  let k : Coeff ⟶ K.X 2 := ModuleCat.ofHom (LinearMap.toSpanSingleton ℝ (K.X 2) a)
  have hk : k ≫ K.d 2 1 = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change K.d 2 1 (r • a) = 0
    rw [map_smul, ha, smul_zero]
  have hkone : k (1 : ℝ) = a := by
    change (1 : ℝ) • a = a
    exact one_smul ℝ a
  refine ⟨K.liftCycles k 1 (by simp) hk 1, ?_⟩
  have h := ConcreteCategory.congr_hom (K.liftCycles_i k 1 (by simp) hk) (1 : ℝ)
  change K.iCycles 2 (K.liftCycles k 1 (by simp) hk 1) = k (1 : ℝ) at h
  exact h.trans hkone

variable [Fintype (cell (Set.univ : Set X) 1)]

/-- The entire kernel of the face boundary is exactly the span of the fundamental cycle. -/
theorem face_cycle_is_scalar_fundamental (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n))
    (a : cell (Set.univ : Set X) 2 → ℝ)
    (ha : ∀ e, ∑ f, TauCeti.cellularIncidence (Set.univ : Set X) ℝ 1 e f * a f = 0) :
    ∃ t : ℝ, ∀ f, a f = t * fundamentalCellularCycle hS hdim f := by
  let K := TauCeti.cellularChainComplex (A := ModuleCat.{0} ℝ) (Set.univ : Set X) Coeff
  let aC : K.X 2 := (coordinates (Set.univ : Set X) 2).symm a
  let zC : K.X 2 := eqToHom (TauCeti.cellularChainComplex_X (Set.univ : Set X) Coeff 2).symm
    (fundamentalChain hS hdim)
  have haC : K.d 2 1 aC = 0 := by
    apply (coordinates (Set.univ : Set X) 1).injective
    ext e
    rw [map_zero]
    change coordinates (Set.univ : Set X) 1 (K.d 2 1 aC) e = 0
    rw [coordinates_d]
    simpa only [aC, LinearEquiv.apply_symm_apply, mul_comm] using ha e
  have hzC : K.d 2 1 zC = 0 := by
    rw [TauCeti.cellularChainComplex_d]
    change (eqToIso (TauCeti.cellularChainComplex_X (Set.univ : Set X) Coeff 1)).inv
      (TauCeti.cellularDifferential (A := ModuleCat.{0} ℝ) (Set.univ : Set X) Coeff 1
        ((eqToIso (TauCeti.cellularChainComplex_X (Set.univ : Set X) Coeff 2)).hom
          ((eqToIso (TauCeti.cellularChainComplex_X (Set.univ : Set X) Coeff 2)).inv
            (fundamentalChain hS hdim)))) = 0
    rw [Iso.inv_hom_id_apply, fundamentalChain_closed, map_zero]
  obtain ⟨qa, hqa⟩ := exists_cycles_element aC haC
  obtain ⟨qz, hqz⟩ := exists_cycles_element zC hzC
  have hqz0 : qz ≠ 0 := by
    intro h
    rw [h, map_zero] at hqz
    have hz := congrArg (eqToHom (TauCeti.cellularChainComplex_X (Set.univ : Set X) Coeff 2)) hqz
    apply fundamentalChain_ne_zero hS hdim
    simpa only [zC, map_zero, ← ConcreteCategory.comp_apply, eqToHom_trans,
      eqToHom_refl, ModuleCat.id_apply] using hz.symm
  let I := (topCyclesIso hS hdim).toLinearEquiv
  have hi : I qz ≠ 0 := by
    intro h
    exact hqz0 (I.injective (h.trans I.map_zero.symm))
  let t := I qa / I qz
  have hqa' : qa = t • qz := by
    apply I.injective
    rw [map_smul]
    exact (div_mul_cancel₀ (I qa) hi).symm
  refine ⟨t, fun f => ?_⟩
  have hcoord := congrArg (fun z => coordinates (Set.univ : Set X) 2 z f) hqa
  rw [hqa', map_smul, hqz, map_smul] at hcoord
  simpa only [aC, LinearEquiv.apply_symm_apply, zC, coordinates,
    fundamentalCellularCycle, LinearEquiv.trans_apply, Iso.toLinearEquiv_apply,
    eqToIso.hom,
    Finsupp.linearEquivFunOnFinite_apply, Pi.smul_apply, smul_eq_mul,
    ← ConcreteCategory.comp_apply, eqToHom_trans, eqToHom_refl,
    ModuleCat.id_apply] using hcoord.symm

/-- The displayed coefficients form a cycle for the actual cellular face boundary. -/
theorem fundamentalCellularCycle_closed (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n))
    (e : cell (Set.univ : Set X) 1) :
    ∑ f, TauCeti.cellularIncidence (Set.univ : Set X) ℝ 1 e f *
      fundamentalCellularCycle hS hdim f = 0 := by
  have h := congrArg
    (fun a => (TauCeti.cellularChainBasis (Set.univ : Set X) ℝ 1).repr a e)
    (fundamentalChain_closed hS hdim)
  rw [map_zero, Finsupp.zero_apply] at h
  rw [boundary_coefficient_sum] at h
  exact h

/-- A two-dimensional CW sphere really has a face; this is derived from its top homology. -/
theorem nonempty_faces (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n)) :
    Nonempty (cell (Set.univ : Set X) 2) := by
  by_contra h
  haveI : IsEmpty (cell (Set.univ : Set X) 2) := not_nonempty_iff.mp h
  apply fundamentalChain_ne_zero hS hdim
  apply (TauCeti.cellularChainBasis (Set.univ : Set X) ℝ 2).repr.injective
  ext f
  exact isEmptyElim f

end StressFlex.Cellular

/-! ### Source fragment: StressFlex/SphereLocalFundamental.lean -/

open CategoryTheory Limits Topology Topology.RelCWComplex

namespace StressFlex.Cellular

variable {X : Type} [TopologicalSpace X] [T2Space X]

/-- The genuine global fundamental class, projected into homology relative to a complement. -/
def localFundamentalClass (hS : X ≃ₜ TopCat.sphere.{0} 2) (S : Set X) :
    TauCeti.localHomology (A := ModuleCat.{0} ℝ) Coeff S 2 :=
  (TopPair.ofSubset (X := TopCat.of X) (Sᶜ : Set X)).singularHomologyπ (C := ModuleCat.{0} ℝ) Coeff 2
    ((singularTopIso hS).inv 1)

set_option backward.isDefEq.respectTransparency false in
theorem restrict_localFundamentalClass (hS : X ≃ₜ TopCat.sphere.{0} 2)
    {S T : Set X} (hST : S ⊆ T) :
    TauCeti.localHomologyRestriction Coeff hST 2 (localFundamentalClass hS T) =
      localFundamentalClass hS S := by
  have hn := TopPair.singularHomologyπ_naturality (C := ModuleCat.{0} ℝ)
    (TopPair.ofSubsetMap (𝟙 (TopCat.of X)) (Set.compl_subset_compl.mpr hST))
      (R := Coeff) 2
  erw [TopPair.ofSubsetMap_fst, CategoryTheory.Functor.map_id, SSet.homologyMap_id,
    Category.id_comp] at hn
  have hv := ConcreteCategory.congr_hom (C := ModuleCat.{0} ℝ) hn
    ((singularTopIso hS).inv 1)
  simp only [ConcreteCategory.comp_apply] at hv
  rw [TauCeti.localHomologyRestriction_def]
  unfold localFundamentalClass
  exact hv.symm

def localFundamentalIso (hS : X ≃ₜ TopCat.sphere.{0} 2) (x : X) :
    Coeff ≅ TauCeti.localHomology (A := ModuleCat.{0} ℝ) Coeff ({x} : Set X) 2 := by
  let p : TopHomology X ⟶
      TauCeti.localHomology (A := ModuleCat.{0} ℝ) Coeff ({x} : Set X) 2 :=
    (TopPair.ofSubset (X := TopCat.of X) ({x}ᶜ : Set X)).singularHomologyπ
      (C := ModuleCat.{0} ℝ) Coeff 2
  haveI : IsIso p := global_to_local_isIso hS x
  exact (singularTopIso hS).symm ≪≫ asIso p

set_option backward.isDefEq.respectTransparency false in
theorem localFundamentalIso_one (hS : X ≃ₜ TopCat.sphere.{0} 2) (x : X) :
    (localFundamentalIso hS x).hom 1 = localFundamentalClass hS ({x} : Set X) := by
  simp only [localFundamentalIso, localFundamentalClass, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, ConcreteCategory.comp_apply] <;> rfl

theorem localFundamentalClass_ne_zero (hS : X ≃ₜ TopCat.sphere.{0} 2) (x : X) :
    localFundamentalClass hS ({x} : Set X) ≠ 0 := by
  rw [← localFundamentalIso_one]
  intro hz
  have h := congrArg (localFundamentalIso hS x).inv hz
  have h10 : (1 : ℝ) = 0 := by
    simpa only [Iso.hom_inv_id_apply, map_zero] using h
  exact one_ne_zero h10

theorem localFundamentalClass_spans (hS : X ≃ₜ TopCat.sphere.{0} 2) (x : X)
    (a : TauCeti.localHomology (A := ModuleCat.{0} ℝ) Coeff ({x} : Set X) 2) :
    ∃ c : ℝ, a = c • localFundamentalClass hS ({x} : Set X) := by
  let I := localFundamentalIso hS x
  refine ⟨I.inv a, ?_⟩
  calc
    a = I.hom (I.inv a) := (Iso.inv_hom_id_apply I a).symm
    _ = I.inv a • I.hom 1 := by rw [← map_smul]; simp
    _ = I.inv a • localFundamentalClass hS ({x} : Set X) := by
      rw [localFundamentalIso_one]

variable [CWComplex (Set.univ : Set X)]

/-- The chosen skeletal generator is exactly the ambient global generator under inclusion. -/
theorem skeletal_generator_to_space (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n)) :
    SSet.homologyMap
      (TopCat.toSSet.map (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ :
        C(TauCeti.skeletonObj (Set.univ : Set X) 3, X)))) Coeff 2
      ((skeletalTopIso hS hdim).inv 1) =
      (singularTopIso hS).inv 1 := by
  rw [← TauCeti.singularHomologyFunctor_obj_map]
  let H := (AlgebraicTopology.singularHomologyFunctor.{0} (ModuleCat.{0} ℝ) 2).obj Coeff
  let J := H.mapIso (TopCat.isoOfHomeo
    (X := TauCeti.skeletonObj (Set.univ : Set X) 3) (Y := TopCat.of X)
      (skeletonToSpaceHomeomorph (X := X) hdim))
  change J.hom (J.inv ((singularTopIso hS).inv 1)) = _
  exact Iso.inv_hom_id_apply J _

set_option backward.isDefEq.respectTransparency false in
/-- Projecting the genuine skeletal fundamental class gives the genuine ambient local class. -/
theorem skeletal_base_generator_to_local (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n)) (S : Set X) :
    TopPair.singularHomologyMap (C := ModuleCat.{0} ℝ)
      (Ambient.basePairToLocal (Set.univ : Set X) 2 S (Set.empty_subset _)) Coeff 2
      ((TauCeti.skeletonBasePair (Set.univ : Set X) 2).singularHomologyπ (C := ModuleCat.{0} ℝ) Coeff 2
        ((skeletalTopIso hS hdim).inv 1)) =
      localFundamentalClass hS S := by
  have hn := TopPair.singularHomologyπ_naturality (C := ModuleCat.{0} ℝ)
    (Ambient.basePairToLocal (Set.univ : Set X) 2 S (Set.empty_subset _)) (R := Coeff) 2
  rw [Ambient.basePairToLocal_fst] at hn
  have h := ConcreteCategory.congr_hom (C := ModuleCat.{0} ℝ) hn
    ((skeletalTopIso hS hdim).inv 1)
  simp only [ConcreteCategory.comp_apply] at h
  erw [skeletal_generator_to_space hS hdim] at h
  unfold localFundamentalClass
  exact h.symm

end StressFlex.Cellular

/-! ### Source fragment: StressFlex/SphericalLiftingBridge.lean -/

open CategoryTheory Limits Topology Topology.RelCWComplex Matrix
open scoped BigOperators

namespace StressFlex.Cellular.Relative

variable {X : Type} [TopologicalSpace X] [T2Space X]
  (C : Set X) [CWComplex C] (K : CWComplex.Subcomplex C)

def baseToLocal (n : ℕ) (S : Set X) (hKS : (K : Set X) ⊆ Sᶜ) :
    baseGroup C K n ⟶ TauCeti.localHomology (A := ModuleCat.{0} ℝ) Coeff S n := by
  letI : RelCWComplex C (K : Set X) := K.relCWComplex
  exact TopPair.singularHomologyMap
    (Ambient.basePairToLocal (D := (K : Set X)) C n S hKS) Coeff n

theorem quotientBase_toLocal (n : ℕ) (S : Set X) (hKS : (K : Set X) ⊆ Sᶜ) :
    quotientBase C K n ≫ baseToLocal C K n S hKS =
      TopPair.singularHomologyMap
        (Ambient.basePairToLocal C n S (Set.empty_subset _)) Coeff n := by
  rw [quotientBase, baseToLocal, ← TopPair.singularHomologyMap_comp]
  congr 1

/-- Two relative classes are read against the very same characteristic-disk generator. -/
theorem read_two_base_classes (S : Set X) (hKS : (K : Set X) ⊆ Sᶜ)
    {n : ℕ} (f : cell C n) (hf : f ∉ K.I n) (x : X)
    (hx : x ∈ openCell n f) (hxS : x ∈ S)
    (h g : baseGroup C K n) :
    ∃ γ : TauCeti.localHomology (A := ModuleCat.{0} ℝ) Coeff ({x} : Set X) n,
      LocalCoefficient.restrictPoint Coeff n hxS (baseToLocal C K n S hKS h) =
        (basis C K n).repr (baseToChains C K n h) (keptCell C K f hf) • γ ∧
      LocalCoefficient.restrictPoint Coeff n hxS (baseToLocal C K n S hKS g) =
        (basis C K n).repr (baseToChains C K n g) (keptCell C K f hf) • γ := by
  let f' : RelCell C K n := keptCell C K f hf
  have hx' : x ∈ @openCell X _ C (K : Set X) K.relCWComplex n f' := by
    simpa only [f', keptCell, Subcomplex.openCell_relCWComplex, Equiv.apply_symm_apply] using hx
  letI : RelCWComplex C (K : Set X) := K.relCWComplex
  refine ⟨Ambient.cellClass (D := (K : Set X)) C f' x hx' 1, ?_, ?_⟩
  all_goals
    have hn := ConcreteCategory.congr_hom
      (Ambient.basePairToLocal_comp_restriction (D := (K : Set X)) C S hKS x hxS
        (TauCeti.notMem_skeletonLT_of_mem_openCell n hx'))
    first
    | exact (hn h).trans (Ambient.read_coefficient (D := (K : Set X)) C f' x hx' _)
    | exact (hn g).trans (Ambient.read_coefficient (D := (K : Set X)) C f' x hx' _)

end StressFlex.Cellular.Relative

namespace StressFlex.Spherical

variable {X : Type} [TopologicalSpace X] [T2Space X]
  [CWComplex (Set.univ : Set X)]
  [Fintype (Vertex X)] [Fintype (Edge X)] [Fintype (Face X)]
  [DecidableEq (Vertex X)]

open Cellular

/-- An ordinary finite scalar face vector as an actual cellular two-chain. -/
def scalarFaceChain (b : Face X → ℝ) :
    TauCeti.cellularChainGroup (A := ModuleCat.{0} ℝ) (Set.univ : Set X) Coeff 2 :=
  ∑ f, b f • TauCeti.cellularChainBasis (Set.univ : Set X) ℝ 2 f

theorem scalarFaceChain_coefficient (b : Face X → ℝ) (f : Face X) :
    (TauCeti.cellularChainBasis (Set.univ : Set X) ℝ 2).repr (scalarFaceChain b) f = b f := by
  exact congrFun ((TauCeti.cellularChainBasis (Set.univ : Set X) ℝ 2).repr_sum_self b) f

theorem scalarFaceChain_boundary (b : Face X → ℝ) (e : Edge X) :
    (TauCeti.cellularChainBasis (Set.univ : Set X) ℝ 1).repr
      (TauCeti.cellularDifferential (Set.univ : Set X) Coeff 1 (scalarFaceChain b)) e =
      ∑ f, faceBoundary e f * b f := by
  rw [Cellular.boundary_coefficient_sum]
  change (∑ f : Face X, faceBoundary e f *
    (TauCeti.cellularChainBasis (Set.univ : Set X) ℝ 2).repr (scalarFaceChain b) f) = _
  simp only [scalarFaceChain_coefficient]

/-- The scalar stress-potential chain is a genuine relative cycle at each vertex. -/
theorem potential_relative_cycle (p : Vertex X → Geometric.Vec)
    (a : Face X → Geometric.Vec)
    (hperp : ∀ e, p (tail e) ⬝ᵥ Geometric.boundary faceBoundary a e = 0 ∧
      p (head e) ⬝ᵥ Geometric.boundary faceBoundary a e = 0) (v : Vertex X) :
    @TauCeti.cellularDifferential X _ _ (oppositeGraph v : Set X)
      (Set.univ : Set X) (oppositeGraph v).relCWComplex (ModuleCat.{0} ℝ) _ _ _ Coeff 1
      (Relative.quotientChains (Set.univ : Set X) (oppositeGraph v) 2
        (scalarFaceChain (fun f => a f ⬝ᵥ p v))) = 0 := by
  let K := oppositeGraph v
  let b := scalarFaceChain (fun f => a f ⬝ᵥ p v)
  apply (Relative.basis (Set.univ : Set X) K 1).repr.injective
  ext j
  rw [map_zero, Finsupp.zero_apply]
  have hcomp := ConcreteCategory.congr_hom
    (Relative.quotientChains_d (Set.univ : Set X) K 1) b
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hcomp
  rw [hcomp]
  let e := (K.relCWComplexCellEquiv 1 j).val
  have he : e ∉ K.I 1 := (K.relCWComplexCellEquiv 1 j).property
  have hj : Relative.keptCell (Set.univ : Set X) K e he = j :=
    (K.relCWComplexCellEquiv 1).symm_apply_apply j
  rw [← hj, Relative.quotientChains_coordinate, scalarFaceChain_boundary]
  have hdot : Geometric.boundary faceBoundary a e ⬝ᵥ p v = 0 := by
    by_cases hs : tail e = v
    · simpa only [hs, dotProduct_comm] using (hperp e).1
    · have ht : head e = v := by
        by_contra ht
        exact he ⟨hs, ht⟩
      simpa only [ht, dotProduct_comm] using (hperp e).2
  simpa only [Geometric.boundary, dot_sum_left, dot_smul_left] using hdot

/-- A fundamental base-pair class after the actual absolute-to-relative map. -/
def relativeFundamentalBase (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n)) (v : Vertex X) :
    Relative.baseGroup (Set.univ : Set X) (oppositeGraph v) 2 :=
  Relative.quotientBase (Set.univ : Set X) (oppositeGraph v) 2
    ((TauCeti.skeletonBasePair (Set.univ : Set X) 2).singularHomologyπ Coeff 2
      ((skeletalTopIso hS hdim).inv 1))

theorem relativeFundamentalBase_chain (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n)) (v : Vertex X) :
    Relative.baseToChains (Set.univ : Set X) (oppositeGraph v) 2
      (relativeFundamentalBase hS hdim v) =
      Relative.quotientChains (Set.univ : Set X) (oppositeGraph v) 2
        (fundamentalChain hS hdim) := by
  have hm : (TauCeti.skeletonBasePair (Set.univ : Set X) 2).singularHomologyπ
      (C := ModuleCat.{0} ℝ) Coeff 2 ≫
      Relative.quotientBase (Set.univ : Set X) (oppositeGraph v) 2 ≫
      Relative.baseToChains (Set.univ : Set X) (oppositeGraph v) 2 =
      TauCeti.skeletonPairπ (Set.univ : Set X) Coeff 2 ≫
      Relative.quotientChains (Set.univ : Set X) (oppositeGraph v) 2 := by
    rw [Relative.quotientBase_comp, ← Category.assoc, base_projection_comp] <;> rfl
  exact ConcreteCategory.congr_hom hm ((skeletalTopIso hS hdim).inv 1)

theorem relativeFundamentalBase_to_local (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n)) (v : Vertex X)
    (S : Set X) (hKS : (oppositeGraph v : Set X) ⊆ Sᶜ) :
    Relative.baseToLocal (Set.univ : Set X) (oppositeGraph v) 2 S hKS
      (relativeFundamentalBase hS hdim v) = localFundamentalClass hS S := by
  have h := ConcreteCategory.congr_hom
    (Relative.quotientBase_toLocal (Set.univ : Set X) (oppositeGraph v) 2 S hKS)
      ((TauCeti.skeletonBasePair (Set.univ : Set X) 2).singularHomologyπ Coeff 2
        ((skeletalTopIso hS hdim).inv 1))
  change Relative.baseToLocal (Set.univ : Set X) (oppositeGraph v) 2 S hKS
      (relativeFundamentalBase hS hdim v) =
      TopPair.singularHomologyMap
        (Ambient.basePairToLocal (Set.univ : Set X) 2 S (Set.empty_subset _)) Coeff 2
        ((TauCeti.skeletonBasePair (Set.univ : Set X) 2).singularHomologyπ Coeff 2
          ((skeletalTopIso hS hdim).inv 1)) at h
  exact h.trans (skeletal_base_generator_to_local hS hdim S)

/-- Face potentials perpendicular to both ends of each edge define genuine vertex heights.
The proof uses the actual relative CW pair at each vertex and ambient local homology. -/
theorem potential_defines_lifting_heights (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n))
    (p : Vertex X → Geometric.Vec) (a : Face X → Geometric.Vec)
    (hperp : ∀ e, p (tail e) ⬝ᵥ Geometric.boundary faceBoundary a e = 0 ∧
      p (head e) ⬝ᵥ Geometric.boundary faceBoundary a e = 0) :
    ∃ H : Vertex X → ℝ, ∀ f v, vertexPoint v ∈ closedCell 2 f →
      a f ⬝ᵥ p v = fundamentalCellularCycle hS hdim f * H v := by
  classical
  have hv (v : Vertex X) : ∃ c : ℝ, ∀ f : Face X,
      vertexPoint v ∈ closedCell 2 f →
        a f ⬝ᵥ p v = fundamentalCellularCycle hS hdim f * c := by
    let K := oppositeGraph v
    let S : Set X := (K : Set X)ᶜ
    have hKS : (K : Set X) ⊆ Sᶜ := by intro x hx hnot; exact hnot hx
    have hxS : vertexPoint v ∈ S := vertex_not_mem_oppositeGraph v
    have hSn : S ∈ nhds (vertexPoint v) := K.closed.isOpen_compl.mem_nhds hxS
    let b := scalarFaceChain (fun f => a f ⬝ᵥ p v)
    let br := Relative.quotientChains (Set.univ : Set X) K 2 b
    obtain ⟨h, hchain⟩ :
        ∃ h : Relative.baseGroup (Set.univ : Set X) K 2,
          Relative.baseToChains (Set.univ : Set X) K 2 h = br := by
      letI : RelCWComplex (Set.univ : Set X) (K : Set X) := K.relCWComplex
      exact Ambient.exists_base_class (D := (K : Set X)) (Set.univ : Set X) 1 br
        (potential_relative_cycle p a hperp v)
    let g := relativeFundamentalBase hS hdim v
    let H : TauCeti.localHomology (A := ModuleCat.{0} ℝ) Coeff S 2 :=
      Relative.baseToLocal (Set.univ : Set X) K 2 S hKS h
    let G : TauCeti.localHomology (A := ModuleCat.{0} ℝ) Coeff S 2 :=
      Relative.baseToLocal (Set.univ : Set X) K 2 S hKS g
    have hg : G = localFundamentalClass hS S :=
      relativeFundamentalBase_to_local hS hdim v S hKS
    obtain ⟨c, hc⟩ := localFundamentalClass_spans hS (vertexPoint v)
      (LocalCoefficient.restrictPoint Coeff 2 hxS H)
    have hc' : LocalCoefficient.restrictPoint Coeff 2 hxS H =
        c • LocalCoefficient.restrictPoint Coeff 2 hxS G := by
      simpa only [LocalCoefficient.restrictPoint, hg, restrict_localFundamentalClass] using hc
    refine ⟨c, fun f hfv => ?_⟩
    have hfK : f ∉ K.I 2 := by simp [K, oppositeGraph]
    have hTS : openCell 2 f ⊆ S := by
      intro y hy
      exact (openFace_disjoint_oppositeGraph v f).notMem_of_mem_left hy
    have hxT : vertexPoint v ∈ closure (openCell 2 f) := by
      rwa [closure_openCell_eq_closedCell]
    have hz : fundamentalCellularCycle hS hdim f ≠ 0 :=
      fundamentalCellularCycle_ne_zero hS hdim f
    have hread (y : X) (hy : y ∈ openCell 2 f) :
        ∃ γ : TauCeti.localHomology (A := ModuleCat.{0} ℝ) Coeff ({y} : Set X) 2,
          LocalCoefficient.restrictPoint Coeff 2 (hTS hy) H =
            (a f ⬝ᵥ p v) • γ ∧
          LocalCoefficient.restrictPoint Coeff 2 (hTS hy) G =
            fundamentalCellularCycle hS hdim f • γ := by
      obtain ⟨γ, hh, hgg⟩ := Relative.read_two_base_classes
        (Set.univ : Set X) K S hKS f hfK y hy (hTS hy) h g
      rw [hchain, Relative.quotientChains_coordinate, scalarFaceChain_coefficient] at hh
      rw [relativeFundamentalBase_chain hS hdim v, Relative.quotientChains_coordinate] at hgg
      exact ⟨γ, hh, hgg⟩
    have hTEq (y : X) (hy : y ∈ openCell 2 f) :
        LocalCoefficient.restrictPoint Coeff 2 (hTS hy) H =
          ((a f ⬝ᵥ p v) / fundamentalCellularCycle hS hdim f) •
            LocalCoefficient.restrictPoint Coeff 2 (hTS hy) G := by
      obtain ⟨γ, hh, hgg⟩ := hread y hy
      rw [hh, hgg, smul_smul, div_mul_cancel₀ _ hz]
    have hTne (y : X) (hy : y ∈ openCell 2 f) :
        LocalCoefficient.restrictPoint Coeff 2 (hTS hy) G ≠ 0 := by
      simpa only [LocalCoefficient.restrictPoint, hg, restrict_localFundamentalClass] using
        localFundamentalClass_ne_zero hS y
    have heq := LocalCoefficient.coefficient_eq_of_mem_closure Coeff 2
      hSn hTS hxT H G ((a f ⬝ᵥ p v) / fundamentalCellularCycle hS hdim f) c
      hc' hTEq hTne
    simpa only [mul_comm] using (div_eq_iff hz).mp heq
  choose H hH using hv
  exact ⟨H, fun f v hfv => hH v f hfv⟩

/-- The actual lifting gradients are the face potentials divided by the nonzero fundamental
cellular coefficients. No coherent-orientation convention z_f = 1 is assumed. -/
theorem potential_defines_linear_lifting (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n))
    (p : Vertex X → Geometric.Vec) (a : Face X → Geometric.Vec)
    (hperp : ∀ e, p (tail e) ⬝ᵥ Geometric.boundary faceBoundary a e = 0 ∧
      p (head e) ⬝ᵥ Geometric.boundary faceBoundary a e = 0) :
    ∃ H : Liftings.linearLiftings p
      (fun (f : Face X) (v : Vertex X) => vertexPoint v ∈ closedCell 2 f),
      ∀ f v, vertexPoint v ∈ closedCell 2 f →
        H v = ((fundamentalCellularCycle hS hdim f)⁻¹ • a f) ⬝ᵥ p v := by
  obtain ⟨H, hH⟩ := potential_defines_lifting_heights hS hdim p a hperp
  have heval (f : Face X) (v : Vertex X) (hv : vertexPoint v ∈ closedCell 2 f) :
      H v = ((fundamentalCellularCycle hS hdim f)⁻¹ • a f) ⬝ᵥ p v := by
    rw [dot_smul_left, hH f v hv, ← mul_assoc,
      inv_mul_cancel₀ (fundamentalCellularCycle_ne_zero hS hdim f), one_mul]
  exact ⟨⟨H, fun f => ⟨(fundamentalCellularCycle hS hdim f)⁻¹ • a f,
    fun v hv => heval f v hv⟩⟩, heval⟩

end StressFlex.Spherical

/-! ### Source fragment: StressFlex/LiftingAlgebra.lean -/

open Matrix
open scoped BigOperators

namespace StressFlex.Liftings

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F] [DecidableEq V]

def forceLinear (p : V → Vec) (s t : E → V) : (E → ℝ) →ₗ[ℝ] (V → Vec) where
  toFun := Geometric.force p s t
  map_add' a b := by
    ext v k
    simp only [Geometric.force, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    ext v k
    simp only [Geometric.force, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    ring

def radialLinear (p : V → Vec) : (V → ℝ) →ₗ[ℝ] (V → Vec) where
  toFun c v := c v • p v
  map_add' a b := by ext v k; simp [add_mul]
  map_smul' c a := by ext v k; simp [mul_assoc]

def equilibriumLinear (p : V → Vec) (s t : E → V) :
    ((E → ℝ) × (V → ℝ)) →ₗ[ℝ] (V → Vec) :=
  (forceLinear p s t).comp (LinearMap.fst ℝ (E → ℝ) (V → ℝ)) +
    (radialLinear p).comp (LinearMap.snd ℝ (E → ℝ) (V → ℝ))

/-- The full coned stress space, encoded by one scalar per original edge and cone edge.
The original-vertex equations imply the apex equation by the verified summation identity. -/
def stresses (p : V → Vec) (s t : E → V) :
    Submodule ℝ ((E → ℝ) × (V → ℝ)) := (equilibriumLinear p s t).ker

theorem mem_stresses_iff (p : V → Vec) (s t : E → V) (q : (E → ℝ) × (V → ℝ)) :
    q ∈ stresses p s t ↔ Geometric.IsStress p s t 0 q.1 q.2 := by
  change (fun v => Geometric.force p s t q.1 v + q.2 v • p v) = 0 ↔ _
  simp only [funext_iff, Pi.zero_apply, Geometric.IsStress, sub_zero, add_comm]

def boundaryLinear (B : E → F → ℝ) : (F → Vec) →ₗ[ℝ] (E → Vec) where
  toFun := Geometric.boundary B
  map_add' a b := by
    ext e k
    simp only [Geometric.boundary, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, mul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    ext e k
    simp only [Geometric.boundary, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f hf
    ring

def edgeLinear (p : V → Vec) (s t : E → V) (B : E → F → ℝ) :
    (F → Vec) →ₗ[ℝ] (E → ℝ) where
  toFun a e := (boundaryLinear B a e ⬝ᵥ (p (s e) ⨯₃ p (t e))) /
    ((p (s e) ⨯₃ p (t e)) ⬝ᵥ (p (s e) ⨯₃ p (t e)))
  map_add' a b := by
    ext e
    rw [map_add, Pi.add_apply, add_dotProduct, add_div] <;> rfl
  map_smul' c a := by
    ext e
    rw [map_smul, Pi.smul_apply, dot_smul_left]
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

def coneLinear (p : V → Vec) (s t : E → V) : (E → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun w v := -(forceLinear p s t w v ⬝ᵥ p v) / (p v ⬝ᵥ p v)
  map_add' a b := by
    ext v
    rw [map_add, Pi.add_apply, add_dotProduct]
    simp only [Pi.add_apply]
    ring
  map_smul' c a := by
    ext v
    rw [map_smul, Pi.smul_apply, dot_smul_left]
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

def fullFromPotential (p : V → Vec) (s t : E → V) (B : E → F → ℝ) :
    (F → Vec) →ₗ[ℝ] ((E → ℝ) × (V → ℝ)) :=
  (edgeLinear p s t B).prod ((coneLinear p s t).comp (edgeLinear p s t B))

theorem edgeLinear_reconstruct (p : V → Vec) (s t : E → V) (B : E → F → ℝ)
    (a : F → Vec) (hq : ∀ e, p (s e) ⨯₃ p (t e) ≠ 0)
    (hperp : ∀ e, p (s e) ⬝ᵥ Geometric.boundary B a e = 0 ∧
      p (t e) ⬝ᵥ Geometric.boundary B a e = 0) (e : E) :
    edgeLinear p s t B a e • (p (s e) ⨯₃ p (t e)) = Geometric.boundary B a e :=
  (Geometric.perpendicular_decomposition (hq e) (hperp e).1 (hperp e).2).symm

theorem fullFromPotential_mem_stresses
    (p : V → Vec) (s t : E → V) (B : E → F → ℝ)
    (a : F → Vec) (hB : Geometric.BoundarySquaredZero s t B)
    (hp : ∀ v, p v ≠ 0) (hq : ∀ e, p (s e) ⨯₃ p (t e) ≠ 0)
    (hperp : ∀ e, p (s e) ⬝ᵥ Geometric.boundary B a e = 0 ∧
      p (t e) ⬝ᵥ Geometric.boundary B a e = 0) :
    fullFromPotential p s t B a ∈ stresses p s t := by
  rw [mem_stresses_iff]
  intro v
  have hcross : p v ⨯₃ Geometric.force p s t (edgeLinear p s t B a) v = 0 := by
    rw [Geometric.cross_force p s t (edgeLinear p s t B a) v]
    simp_rw [edgeLinear_reconstruct p s t B a hq hperp]
    exact Geometric.boundary_closed s t B hB a v
  have hpar := Geometric.parallel_of_cross_zero (hp v) hcross
  change (-(Geometric.force p s t (edgeLinear p s t B a) v ⬝ᵥ p v) /
    (p v ⬝ᵥ p v)) • (p v - 0) + Geometric.force p s t (edgeLinear p s t B a) v = 0
  rw [sub_zero, neg_div, neg_smul, ← hpar, neg_add_cancel]

variable (p : V → Vec) (face : F → V → Prop)
  (hunique : ∀ f (a b : Vec),
    (∀ v, face f v → a ⬝ᵥ p v = b ⬝ᵥ p v) → a = b)

def weightFaces (z : F → ℝ) : (F → Vec) →ₗ[ℝ] (F → Vec) where
  toFun a f := z f • a f
  map_add' a b := by ext f k; simp [mul_add]
  map_smul' c a := by ext f k; simp [mul_comm, mul_left_comm]

def heightPotentials (z : F → ℝ) :
    linearLiftings p face →ₗ[ℝ] (F → Vec) :=
  (weightFaces z).comp (faceForms p face hunique)

theorem heightPotentials_evaluation (z : F → ℝ) (h : linearLiftings p face)
    (f : F) (v : V) (hv : face f v) :
    heightPotentials p face hunique z h f ⬝ᵥ p v = z f * h v := by
  change (z f • faceForm p face h f) ⬝ᵥ p v = _
  rw [dot_smul_left, faceForm_spec p face h f v hv]

theorem heightPotentials_perpendicular (s t : E → V) (B : E → F → ℝ) (z : F → ℝ)
    (hfaces : ∀ e f, B e f ≠ 0 → face f (s e) ∧ face f (t e))
    (hz : ∀ e, ∑ f, B e f * z f = 0) (h : linearLiftings p face) :
    ∀ e, p (s e) ⬝ᵥ Geometric.boundary B (heightPotentials p face hunique z h) e = 0 ∧
      p (t e) ⬝ᵥ Geometric.boundary B (heightPotentials p face hunique z h) e = 0 := by
  classical
  intro e
  have he (v : V) (hv : ∀ f, B e f ≠ 0 → face f v) :
      Geometric.boundary B (heightPotentials p face hunique z h) e ⬝ᵥ p v = 0 := by
    simp only [Geometric.boundary, dot_sum_left, dot_smul_left]
    calc
      (∑ f, B e f * (heightPotentials p face hunique z h f ⬝ᵥ p v)) =
          ∑ f, (B e f * z f) * h v := by
        apply Finset.sum_congr rfl
        intro f hf
        by_cases hB : B e f = 0
        · simp only [hB, zero_mul]
        · rw [heightPotentials_evaluation p face hunique z h f v (hv f hB)]
          ring
      _ = 0 := by rw [← Finset.sum_mul, hz e, zero_mul]
  constructor
  · rw [dotProduct_comm]
    exact he (s e) (fun f hf => (hfaces e f hf).1)
  · rw [dotProduct_comm]
    exact he (t e) (fun f hf => (hfaces e f hf).2)

def stressFromHeight (s t : E → V) (B : E → F → ℝ) (z : F → ℝ)
    (hB : Geometric.BoundarySquaredZero s t B)
    (hp : ∀ v, p v ≠ 0) (hq : ∀ e, p (s e) ⨯₃ p (t e) ≠ 0)
    (hfaces : ∀ e f, B e f ≠ 0 → face f (s e) ∧ face f (t e))
    (hz : ∀ e, ∑ f, B e f * z f = 0) :
    linearLiftings p face →ₗ[ℝ] stresses p s t :=
  ((fullFromPotential p s t B).comp (heightPotentials p face hunique z)).codRestrict
    (stresses p s t) (fun h => fullFromPotential_mem_stresses p s t B _
      hB hp hq (heightPotentials_perpendicular p face hunique s t B z hfaces hz h))

/-- A potential representing a given full equilibrium stress recovers exactly that stress. -/
theorem fullFromPotential_of_boundary (s t : E → V) (B : E → F → ℝ)
    (hp : ∀ v, p v ≠ 0) (hq : ∀ e, p (s e) ⨯₃ p (t e) ≠ 0)
    (a : F → Vec) (q : stresses p s t)
    (ha : ∀ e, Geometric.boundary B a e = q.1.1 e • (p (s e) ⨯₃ p (t e))) :
    fullFromPotential p s t B a = q.1 := by
  have he : edgeLinear p s t B a = q.1.1 := by
    funext e
    change (Geometric.boundary B a e ⬝ᵥ _) / _ = _
    rw [ha e, dot_smul_left]
    exact mul_div_cancel_right₀ _ (Geometric.dot_self_ne_zero (hq e))
  apply Prod.ext
  · exact he
  · change coneLinear p s t (edgeLinear p s t B a) = q.1.2
    rw [he]
    funext v
    have hv := (mem_stresses_iff p s t q.1).mp q.2 v
    have h := congrArg (fun a : Vec => a ⬝ᵥ p v) hv
    simp only [Geometric.IsStress, sub_zero, add_dotProduct, dot_smul_left,
      zero_dotProduct] at h
    change -(Geometric.force p s t q.1.1 v ⬝ᵥ p v) / (p v ⬝ᵥ p v) = q.1.2 v
    apply (div_eq_iff (Geometric.dot_self_ne_zero (hp v))).mpr
    linarith

section Quotient

variable (s t : E → V) (B : E → F → ℝ) (z : F → ℝ)
  (hB : Geometric.BoundarySquaredZero s t B)
  (hp : ∀ v, p v ≠ 0) (hq : ∀ e, p (s e) ⨯₃ p (t e) ≠ 0)
  (hfaces : ∀ e f, B e f ≠ 0 → face f (s e) ∧ face f (t e))
  (hz : ∀ e, ∑ f, B e f * z f = 0)
  (hz0 : ∀ f, z f ≠ 0)
  (hcover : ∀ v, ∃ f, face f v)

local notation "T" => stressFromHeight p face hunique s t B z hB hp hq hfaces hz

theorem globalLinear_mem_kernel (b : Vec) :
    T (globalLinear p face b) = 0 := by
  apply Subtype.ext
  have ha : Geometric.boundary B
      (heightPotentials p face hunique z (globalLinear p face b)) = 0 := by
    ext e k
    simp only [Geometric.boundary, heightPotentials, LinearMap.comp_apply, weightFaces,
      LinearMap.coe_mk, AddHom.coe_mk, faceForms_globalLinear, Pi.smul_apply,
      Finset.sum_apply, smul_eq_mul, Pi.zero_apply]
    calc
      (∑ f, B e f * (z f * b k)) = (∑ f, B e f * z f) * b k := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro f hf
        ring
      _ = 0 := by rw [hz e, zero_mul]
  have he : edgeLinear p s t B
      (heightPotentials p face hunique z (globalLinear p face b)) = 0 := by
    funext e
    change (Geometric.boundary B _ e ⬝ᵥ _) / _ = 0
    rw [ha, Pi.zero_apply, zero_dotProduct, zero_div]
  change (edgeLinear p s t B _, coneLinear p s t (edgeLinear p s t B _)) = (0, 0)
  rw [he, map_zero]

include hz0 hcover in
/-- The kernel calculation uses the actual scalar top-cycle theorem, separately proved from H₂. -/
theorem kernel_eq_globalLinear
    (hcycle : ∀ a : F → ℝ, (∀ e, ∑ f, B e f * a f = 0) →
      ∃ c : ℝ, ∀ f, a f = c * z f) :
    (T).ker = (globalLinear p face).range := by
  apply Submodule.ext
  intro h
  constructor
  · intro hh
    have he : edgeLinear p s t B (heightPotentials p face hunique z h) = 0 :=
      congrArg (fun q : stresses p s t => q.1.1) hh
    have ha : Geometric.boundary B (heightPotentials p face hunique z h) = 0 := by
      funext e
      rw [← edgeLinear_reconstruct p s t B _ hq
        (heightPotentials_perpendicular p face hunique s t B z hfaces hz h) e,
        he, Pi.zero_apply, zero_smul, Pi.zero_apply]
    have hc (k : Fin 3) :
        ∃ c : ℝ, ∀ f, heightPotentials p face hunique z h f k = c * z f := by
      apply hcycle
      intro e
      have heq := congrArg (fun q : E → Vec => q e k) ha
      simpa only [Geometric.boundary, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, Pi.zero_apply] using heq
    choose b hb using hc
    have hform (f : F) : faceForms p face hunique h f = b := by
      ext k
      have hcoord := hb k f
      change z f * faceForms p face hunique h f k = b k * z f at hcoord
      apply (mul_left_cancel₀ (hz0 f))
      simpa only [mul_comm] using hcoord
    refine ⟨b, ?_⟩
    ext v
    obtain ⟨f, hf⟩ := hcover v
    change b ⬝ᵥ p v = h v
    rw [← hform f]
    exact faceForm_spec p face h f v hf
  · rintro ⟨b, rfl⟩
    exact globalLinear_mem_kernel p face hunique s t B z hB hp hq hfaces hz b

include hz0 in
/-- Surjectivity is reduced to the explicit face-potential and local-height lemmas,
whose sphere instances are established using cellular and local singular homology. -/
theorem stressFromHeight_surjective
    (hpotential : ∀ q : stresses p s t, ∃ a : F → Vec,
      ∀ e, Geometric.boundary B a e = q.1.1 e • (p (s e) ⨯₃ p (t e)))
    (hheight : ∀ a : F → Vec,
      (∀ e, p (s e) ⬝ᵥ Geometric.boundary B a e = 0 ∧
        p (t e) ⬝ᵥ Geometric.boundary B a e = 0) →
      ∃ h : V → ℝ, ∀ f v, face f v → a f ⬝ᵥ p v = z f * h v) :
    Function.Surjective T := by
  intro q
  obtain ⟨a, ha⟩ := hpotential q
  have hperp : ∀ e, p (s e) ⬝ᵥ Geometric.boundary B a e = 0 ∧
      p (t e) ⬝ᵥ Geometric.boundary B a e = 0 := by
    intro e
    rw [ha e]
    simp only [dot_smul_right, dot_self_cross, dot_cross_self,
      mul_zero, and_self]
  obtain ⟨h, hh⟩ := hheight a hperp
  have hh' : h ∈ linearLiftings p face := by
    intro f
    refine ⟨(z f)⁻¹ • a f, fun v hv => ?_⟩
    rw [dot_smul_left, hh f v hv]
    field_simp [hz0 f]
  let H : linearLiftings p face := ⟨h, hh'⟩
  have hpot : heightPotentials p face hunique z H = a := by
    funext f
    apply hunique f
    intro v hv
    rw [heightPotentials_evaluation p face hunique z H f v hv, hh f v hv]
  refine ⟨H, ?_⟩
  apply Subtype.ext
  change fullFromPotential p s t B (heightPotentials p face hunique z H) = q.1
  rw [hpot]
  exact fullFromPotential_of_boundary p s t B hp hq a q ha

/-- The quotient equivalence is the ordinary first isomorphism theorem applied to the
height-to-stress map, with its entire kernel explicitly identified. -/
def liftingQuotientEquiv
    (hcycle : ∀ a : F → ℝ, (∀ e, ∑ f, B e f * a f = 0) →
      ∃ c : ℝ, ∀ f, a f = c * z f)
    (hpotential : ∀ q : stresses p s t, ∃ a : F → Vec,
      ∀ e, Geometric.boundary B a e = q.1.1 e • (p (s e) ⨯₃ p (t e)))
    (hheight : ∀ a : F → Vec,
      (∀ e, p (s e) ⬝ᵥ Geometric.boundary B a e = 0 ∧
        p (t e) ⬝ᵥ Geometric.boundary B a e = 0) →
      ∃ h : V → ℝ, ∀ f v, face f v → a f ⬝ᵥ p v = z f * h v) :
    (linearLiftings p face ⧸ (globalLinear p face).range) ≃ₗ[ℝ] stresses p s t :=
  (Submodule.quotEquivOfEq _ _
    (kernel_eq_globalLinear p face hunique s t B z hB hp hq hfaces hz hz0 hcover hcycle).symm).trans
      ((T).quotKerEquivOfSurjective
        (stressFromHeight_surjective p face hunique s t B z hB hp hq hfaces hz hz0
          hpotential hheight))

include hunique hB hp hq hfaces hz hz0 hcover in
theorem finrank_stresses
    (hcycle : ∀ a : F → ℝ, (∀ e, ∑ f, B e f * a f = 0) →
      ∃ c : ℝ, ∀ f, a f = c * z f)
    (hpotential : ∀ q : stresses p s t, ∃ a : F → Vec,
      ∀ e, Geometric.boundary B a e = q.1.1 e • (p (s e) ⨯₃ p (t e)))
    (hheight : ∀ a : F → Vec,
      (∀ e, p (s e) ⬝ᵥ Geometric.boundary B a e = 0 ∧
        p (t e) ⬝ᵥ Geometric.boundary B a e = 0) →
      ∃ h : V → ℝ, ∀ f v, face f v → a f ⬝ᵥ p v = z f * h v)
    [Nonempty F] :
    Module.finrank ℝ (stresses p s t) =
      Module.finrank ℝ (linearLiftings p face) - 3 := by
  have hinj : Function.Injective (globalLinear p face) := by
    intro a b hab
    apply hunique (Classical.choice (inferInstance : Nonempty F))
    intro v hv
    exact congrArg (fun h : linearLiftings p face => h v) hab
  have hd : Module.finrank ℝ (globalLinear p face).range = 3 := by
    rw [LinearMap.finrank_range_of_inj hinj]
    simp [Vec]
  rw [← (liftingQuotientEquiv p face hunique s t B z hB hp hq hfaces hz hz0
      hcover hcycle hpotential hheight).finrank_eq]
  rw [Submodule.finrank_quotient, hd]

end Quotient

end StressFlex.Liftings

/-! ### Source fragment: StressFlex/SphericalLiftings.lean -/

open CategoryTheory Topology Topology.RelCWComplex Matrix
open scoped BigOperators

namespace StressFlex.Spherical

variable {X : Type} [TopologicalSpace X] [T2Space X]
  [CWComplex (Set.univ : Set X)]
  [Fintype (Vertex X)] [Fintype (Edge X)] [Fintype (Face X)]
  [DecidableEq (Vertex X)]

def faceContains (f : Face X) (v : Vertex X) : Prop :=
  vertexPoint v ∈ closedCell 2 f

/-- The paper's explicit noncollinearity hypothesis on each face. -/
def NoncollinearFaces (p : Vertex X → Geometric.Vec) : Prop :=
  ∀ f : Face X, ∃ i j k : Vertex X,
    faceContains f i ∧ faceContains f j ∧ faceContains f k ∧
      (p j - p i) ⨯₃ (p k - p i) ≠ 0

theorem face_functional_unique (P : NormalizedRealization (X := X))
    (hnoncol : NoncollinearFaces P.position) (f : Face X) (a b : Geometric.Vec)
    (h : ∀ v, faceContains f v → a ⬝ᵥ P.position v = b ⬝ᵥ P.position v) :
    a = b := by
  obtain ⟨i, j, k, hi, hj, hk, hc⟩ := hnoncol f
  apply sub_eq_zero.mp
  apply Liftings.functional_eq_zero_of_three_points
    (P.normal f) (P.position i) (P.position j) (P.position k) (a - b)
    (P.planar f i hi) (P.planar f j hj) (P.planar f k hk) hc
  · rw [sub_dotProduct, h i hi, sub_self]
  · rw [sub_dotProduct, h j hj, sub_self]
  · rw [sub_dotProduct, h k hk, sub_self]

theorem faceBoundary_endpoints (e : Edge X) (f : Face X) (h : faceBoundary e f ≠ 0) :
    faceContains f (tail e) ∧ faceContains f (head e) := by
  have hs := closedEdge_subset_closedFace e f h
  exact ⟨hs (endpoint_mem_closedEdge e).1, hs (endpoint_mem_closedEdge e).2⟩

/-- The paper's affine height space equals the linear-functional representation used in the proof. -/
theorem affine_liftings_eq_linear (P : NormalizedRealization (X := X)) :
    Liftings.affineLiftings P.position faceContains = Liftings.linearLiftings P.position faceContains :=
  Liftings.affineLiftings_eq_linearLiftings P.position faceContains P.normal P.planar

/-- The full, explicit stress/lifting quotient equivalence of Proposition 3 in normalised coordinates. -/
def liftingStressEquiv (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n))
    (P : NormalizedRealization (X := X)) (hnoncol : NoncollinearFaces P.position) :
    (Liftings.linearLiftings P.position faceContains ⧸
      (Liftings.globalLinear P.position faceContains).range) ≃ₗ[ℝ]
      Liftings.stresses P.position tail head :=
  Liftings.liftingQuotientEquiv P.position faceContains (face_functional_unique P hnoncol)
    tail head faceBoundary (Cellular.fundamentalCellularCycle hS hdim)
    boundarySquaredZero (positions_ne_zero P) (edge_cross_ne_zero P) faceBoundary_endpoints
    (Cellular.fundamentalCellularCycle_closed hS hdim)
    (Cellular.fundamentalCellularCycle_ne_zero hS hdim) P.vertex_in_face
    (Cellular.face_cycle_is_scalar_fundamental hS hdim)
    (fun q => exists_vector_face_chain hS P q.1.1 q.1.2
      ((Liftings.mem_stresses_iff P.position tail head q.1).mp q.2))
    (potential_defines_lifting_heights hS hdim P.position)

/-- The dimension statement uses the genuine affine-on-faces lifting space. -/
theorem stress_dimension (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n))
    (P : NormalizedRealization (X := X)) (hnoncol : NoncollinearFaces P.position) :
    Module.finrank ℝ (Liftings.stresses P.position tail head) =
      Module.finrank ℝ (Liftings.affineLiftings P.position faceContains) - 3 := by
  letI : Nonempty (Face X) := Cellular.nonempty_faces hS hdim
  rw [affine_liftings_eq_linear P]
  exact Liftings.finrank_stresses P.position faceContains (face_functional_unique P hnoncol)
    tail head faceBoundary (Cellular.fundamentalCellularCycle hS hdim)
    boundarySquaredZero (positions_ne_zero P) (edge_cross_ne_zero P) faceBoundary_endpoints
    (Cellular.fundamentalCellularCycle_closed hS hdim)
    (Cellular.fundamentalCellularCycle_ne_zero hS hdim) P.vertex_in_face
    (Cellular.face_cycle_is_scalar_fundamental hS hdim)
    (fun q => exists_vector_face_chain hS P q.1.1 q.1.2
      ((Liftings.mem_stresses_iff P.position tail head q.1).mp q.2))
    (potential_defines_lifting_heights hS hdim P.position)

theorem NoncollinearFaces.translate {p : Vertex X → Geometric.Vec}
    (h : NoncollinearFaces p) (x : Geometric.Vec) :
    NoncollinearFaces (fun v => p v - x) := by
  intro f
  obtain ⟨i, j, k, hi, hj, hk, hc⟩ := h f
  exact ⟨i, j, k, hi, hj, hk, by simpa only [sub_sub_sub_cancel_right] using hc⟩

/-- Affine-on-faces heights are unchanged by translating the entire spatial realisation. -/
theorem affineLiftings_translate (p : Vertex X → Geometric.Vec) (x : Geometric.Vec) :
    Liftings.affineLiftings (fun v => p v - x) faceContains =
      Liftings.affineLiftings p faceContains := by
  ext h
  constructor
  · intro hh f
    obtain ⟨a, d, ha⟩ := hh f
    refine ⟨a, d - a ⬝ᵥ x, fun v hv => ?_⟩
    rw [ha v hv, dotProduct_sub]
    ring
  · intro hh f
    obtain ⟨a, d, ha⟩ := hh f
    refine ⟨a, d + a ⬝ᵥ x, fun v hv => ?_⟩
    rw [ha v hv, dotProduct_sub]
    ring

/-- The actual stress space at an arbitrary cone point, represented by its unchanged edge weights. -/
def stressesAt (P : AffineRealization (X := X)) (x : Geometric.Vec) :=
  Liftings.stresses (fun v => P.position v - x) tail head

theorem mem_stressesAt_iff (P : AffineRealization (X := X)) (x : Geometric.Vec)
    (q : (Edge X → ℝ) × (Vertex X → ℝ)) :
    q ∈ stressesAt P x ↔ Geometric.IsStress P.position tail head x q.1 q.2 := by
  rw [stressesAt, Liftings.mem_stresses_iff]
  simp only [Geometric.IsStress, sub_zero, Geometric.force_shift]

/-- The quotient isomorphism at the original arbitrary apex. The quotient's height space is
identified with the paper's L(S) by the two preceding equality theorems. -/
def liftingStressEquivAt (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n))
    (P : AffineRealization (X := X)) (hnoncol : NoncollinearFaces P.position)
    (x : Geometric.Vec) (hx : ∀ f, P.normal f ⬝ᵥ x ≠ P.level f) :
    (Liftings.linearLiftings (fun v => P.position v - x) faceContains ⧸
      (Liftings.globalLinear (fun v => P.position v - x) faceContains).range) ≃ₗ[ℝ]
      stressesAt P x :=
  liftingStressEquiv hS hdim (P.normalized x hx) (hnoncol.translate x)

theorem stress_dimension_at_apex (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n))
    (P : AffineRealization (X := X)) (hnoncol : NoncollinearFaces P.position)
    (x : Geometric.Vec) (hx : ∀ f, P.normal f ⬝ᵥ x ≠ P.level f) :
    Module.finrank ℝ (stressesAt P x) =
      Module.finrank ℝ (Liftings.affineLiftings P.position faceContains) - 3 := by
  have h := stress_dimension hS hdim (P.normalized x hx) (hnoncol.translate x)
  change Module.finrank ℝ (Liftings.stresses (fun v => P.position v - x) tail head) =
    Module.finrank ℝ (Liftings.affineLiftings (fun v => P.position v - x) faceContains) - 3 at h
  rw [affineLiftings_translate P.position x] at h
  exact h

/-- Exact equality of the quotient presentation's height space with the paper's affine lifting space. -/
theorem paper_height_space_eq_at_apex
    (P : AffineRealization (X := X)) (x : Geometric.Vec)
    (hx : ∀ f, P.normal f ⬝ᵥ x ≠ P.level f) :
    Liftings.affineLiftings P.position faceContains =
      Liftings.linearLiftings (fun v => P.position v - x) faceContains := by
  rw [← affineLiftings_translate P.position x]
  exact affine_liftings_eq_linear (P.normalized x hx)

/-- The algebraic stress space includes the apex equilibrium equation exactly. -/
theorem mem_stressesAt_iff_full (P : AffineRealization (X := X)) (x : Geometric.Vec)
    (q : (Edge X → ℝ) × (Vertex X → ℝ)) :
    q ∈ stressesAt P x ↔
      Geometric.IsStress P.position tail head x q.1 q.2 ∧
        (∑ v, q.2 v • (P.position v - x)) = 0 := by
  rw [mem_stressesAt_iff]
  exact ⟨fun h => ⟨h, Geometric.apex_equilibrium P.position tail head x q.1 q.2 h⟩,
    fun h => h.1⟩

/-- An additive dimension equality makes explicit that no truncated-subtraction issue is present. -/
theorem stress_dimension_add_three (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n))
    (P : NormalizedRealization (X := X)) (hnoncol : NoncollinearFaces P.position) :
    Module.finrank ℝ (Liftings.stresses P.position tail head) + 3 =
      Module.finrank ℝ (Liftings.affineLiftings P.position faceContains) := by
  letI : Nonempty (Face X) := Cellular.nonempty_faces hS hdim
  have hinj : Function.Injective (Liftings.globalLinear P.position faceContains) := by
    intro a b hab
    apply face_functional_unique P hnoncol (Classical.choice (inferInstance : Nonempty (Face X)))
    intro v hv
    exact congrArg (fun h : Liftings.linearLiftings P.position faceContains => h v) hab
  have hd : Module.finrank ℝ (Liftings.globalLinear P.position faceContains).range = 3 := by
    rw [LinearMap.finrank_range_of_inj hinj]
    simp [Liftings.Vec]
  have hdimQ := (Liftings.globalLinear P.position faceContains).range.finrank_quotient_add_finrank
  rw [(liftingStressEquiv hS hdim P hnoncol).finrank_eq, hd] at hdimQ
  rw [affine_liftings_eq_linear P]
  exact hdimQ

theorem stress_dimension_add_three_at_apex (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n))
    (P : AffineRealization (X := X)) (hnoncol : NoncollinearFaces P.position)
    (x : Geometric.Vec) (hx : ∀ f, P.normal f ⬝ᵥ x ≠ P.level f) :
    Module.finrank ℝ (stressesAt P x) + 3 =
      Module.finrank ℝ (Liftings.affineLiftings P.position faceContains) := by
  have h := stress_dimension_add_three hS hdim (P.normalized x hx) (hnoncol.translate x)
  change Module.finrank ℝ (Liftings.stresses (fun v => P.position v - x) tail head) + 3 =
    Module.finrank ℝ (Liftings.affineLiftings (fun v => P.position v - x) faceContains) at h
  rw [affineLiftings_translate P.position x] at h
  exact h

/-- All assertions of Proposition 3, with the exact affine-height correspondence and both
outer and apex equilibrium explicitly available in the surrounding declarations. -/
theorem proposition_three (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n))
    (P : AffineRealization (X := X)) (hnoncol : NoncollinearFaces P.position)
    (x : Geometric.Vec) (hx : ∀ f, P.normal f ⬝ᵥ x ≠ P.level f) :
    Nonempty ((Liftings.linearLiftings (fun v => P.position v - x) faceContains ⧸
      (Liftings.globalLinear (fun v => P.position v - x) faceContains).range) ≃ₗ[ℝ]
        stressesAt P x) ∧
    Liftings.affineLiftings P.position faceContains =
      Liftings.linearLiftings (fun v => P.position v - x) faceContains ∧
    Module.finrank ℝ (stressesAt P x) + 3 =
      Module.finrank ℝ (Liftings.affineLiftings P.position faceContains) ∧
    ∀ q : stressesAt P x,
      ∃ (U : Set Geometric.Vec) (W : Geometric.Vec → Edge X → ℝ)
        (C : Geometric.Vec → Vertex X → ℝ),
        IsOpen U ∧ x ∈ U ∧ W x = q.1.1 ∧ C x = q.1.2 ∧
        AnalyticOnNhd ℝ W U ∧ AnalyticOnNhd ℝ C U ∧
        ∀ y ∈ U, Geometric.IsStress P.position tail head y (W y) (C y) := by
  refine ⟨⟨liftingStressEquivAt hS hdim P hnoncol x hx⟩,
    paper_height_space_eq_at_apex P x hx,
    stress_dimension_add_three_at_apex hS hdim P hnoncol x hx, ?_⟩
  intro q
  exact analytic_stress_extension_at_apex hS P x hx q.1.1 q.1.2
    ((mem_stressesAt_iff P x q.1).mp q.2)

/-- The one-skeleton has no parallel unoriented edges. Absence of loops is already
part of `AffineRealization.edge_injective`, by `edge_attaching_injective_iff`. -/
def SimpleOneSkeleton : Prop :=
  ∀ e e' : Edge X,
    ((tail e = tail e' ∧ head e = head e') ∨
      (tail e = head e' ∧ head e = tail e')) → e = e'

/-- The spherical assertion of Theorem 1 under the paper's full stated hypotheses.
The stronger checked transport theorem does not need noncollinearity or simplicity,
but both are retained here for direct statement correspondence. -/
theorem theorem_one_spherical (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n))
    (P : AffineRealization (X := X)) (hnoncol : NoncollinearFaces P.position)
    (hsimple : SimpleOneSkeleton (X := X))
    (x : Geometric.Vec) (hx : ∀ f, P.normal f ⬝ᵥ x ≠ P.level f)
    (w : Edge X → ℝ) (c : Vertex X → ℝ) (u : Vertex X → Geometric.Vec)
    (hc : Geometric.IsStress P.position tail head x w c)
    (hu : Geometric.IsMotion (fun v => P.position v - x) tail head u) :
    ∑ v, c v • u v = 0 :=
  stress_flex_orthogonality_at_apex hS P x hx w c u hc hu

end StressFlex.Spherical

/-! ### Source fragment: notes/stress_flex/OpenFaceDensityDraft.lean -/

open CategoryTheory Limits Topology Topology.RelCWComplex Metric Set

namespace StressFlex.Spherical

variable {X : Type} [TopologicalSpace X] [T2Space X]
  [CWComplex (Set.univ : Set X)]

/-- The interior of a cell, when nonempty, is an actual ambient chart.
The chart has no claim that an arbitrary open cell is ambient-open. -/
def cellInteriorChart (n : ℕ) (i : cell (Set.univ : Set X) n) :
    OpenPartialHomeomorph X (Fin n → ℝ) where
  toFun := (map n i).symm
  invFun := map n i
  source := interior (openCell n i)
  target := ball 0 1 ∩ (map n i) ⁻¹' interior (openCell n i)
  map_source' x hx := by
    refine ⟨TauCeti.map_symm_mem_ball n (interior_subset hx), ?_⟩
    change map n i ((map n i).symm x) ∈ interior (openCell n i)
    rw [TauCeti.map_map_symm n (interior_subset hx)]
    exact hx
  map_target' y hy := hy.2
  left_inv' x hx := TauCeti.map_map_symm n (interior_subset hx)
  right_inv' y hy := (map n i).left_inv (by
    rw [source_eq]
    exact hy.1)
  open_source := isOpen_interior
  open_target := ((continuousOn n i).mono ball_subset_closedBall).isOpen_inter_preimage
    isOpen_ball isOpen_interior
  continuousOn_toFun := (continuousOn_symm n i).mono (by
    rw [TauCeti.target_map_eq_openCell]
    exact interior_subset)
  continuousOn_invFun := (continuousOn n i).mono (fun _ h =>
    ball_subset_closedBall h.1)

theorem interior_openCell_eq_empty_of_ne_two
    (hS : X ≃ₜ TopCat.sphere.{0} 2) (n : ℕ)
    (hn : n ≠ 2) (i : cell (Set.univ : Set X) n) :
    interior (openCell n i) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hz := TauCeti.isZero_singularHomology_complSingleton_of_ne
    (A := ModuleCat.{0} ℝ) Cellular.Coeff (cellInteriorChart n i) hx
    (n := n) (k := 2) (by simp) hn.symm
  letI : Subsingleton
      (TauCeti.localHomology (A := ModuleCat.{0} ℝ) Cellular.Coeff ({x} : Set X) 2) :=
    ModuleCat.subsingleton_of_isZero hz
  exact Cellular.localFundamentalClass_ne_zero hS x (Subsingleton.elim _ _)

theorem interior_closedCell_zero_eq_empty
    (hS : X ≃ₜ TopCat.sphere.{0} 2) (v : Vertex X) :
    interior (closedCell 0 v) = ∅ := by
  simpa only [closedCell_zero_eq_singleton, openCell_zero_eq_singleton] using
    interior_openCell_eq_empty_of_ne_two hS 0 (by decide) v

variable [Fintype (Vertex X)] [Fintype (Edge X)] [Fintype (Face X)]
  [DecidableEq (Vertex X)]

theorem interior_closedCell_edge_eq_empty
    (hS : X ≃ₜ TopCat.sphere.{0} 2) (e : Edge X) :
    interior (closedCell 1 e) = ∅ := by
  have hv (v : Vertex X) : interior ({vertexPoint v} : Set X) = ∅ := by
    simpa only [closedCell_zero_eq_singleton, vertexPoint] using
      interior_closedCell_zero_eq_empty hS v
  have hp : interior ({vertexPoint (tail e), vertexPoint (head e)} : Set X) = ∅ := by
    change interior (({vertexPoint (tail e)} : Set X) ∪ {vertexPoint (head e)}) = ∅
    rw [interior_union_isClosed_of_interior_empty isClosed_singleton (hv (head e))]
    exact hv (tail e)
  have hpc : IsClosed ({vertexPoint (tail e), vertexPoint (head e)} : Set X) := by
    change IsClosed (({vertexPoint (tail e)} : Set X) ∪ {vertexPoint (head e)})
    exact isClosed_singleton.union isClosed_singleton
  rw [closedCell_edge,
    interior_union_isClosed_of_interior_empty hpc
      (interior_openCell_eq_empty_of_ne_two hS 1 (by decide) e)]
  exact hp

/-- This finite-union argument does not require the Baire theorem. -/
theorem interior_finite_iUnion_eq_empty {ι : Type} [Fintype ι]
    (s : ι → Set X) (hc : ∀ i, IsClosed (s i))
    (hi : ∀ i, interior (s i) = ∅) : interior (⋃ i, s i) = ∅ := by
  classical
  suffices h : ∀ t : Finset ι, interior (⋃ i ∈ t, s i) = ∅ by
    simpa using h Finset.univ
  intro t
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
    rw [Finset.set_biUnion_insert,
      interior_union_isClosed_of_interior_empty (hc a) ih]
    exact hi a

/-- In a finite two-dimensional CW decomposition of an actual topological
two-sphere, the union of the open faces is dense. Distinct edge endpoints are
not needed for this statement. -/
theorem dense_iUnion_openFace
    (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n)) :
    Dense (⋃ f : Face X, openCell 2 f) := by
  classical
  let s : (Vertex X ⊕ Edge X) → Set X
    | .inl v => closedCell 0 v
    | .inr e => closedCell 1 e
  have hc (i : Vertex X ⊕ Edge X) : IsClosed (s i) := by
    cases i <;> exact isClosed_closedCell
  have hi (i : Vertex X ⊕ Edge X) : interior (s i) = ∅ := by
    cases i with
    | inl v => exact interior_closedCell_zero_eq_empty hS v
    | inr e => exact interior_closedCell_edge_eq_empty hS e
  have hd : Dense (⋃ i, s i)ᶜ :=
    interior_eq_empty_iff_dense_compl.mp (interior_finite_iUnion_eq_empty s hc hi)
  apply hd.mono
  intro x hx
  have hxall : x ∈ ⋃ (n : ℕ) (i : cell (Set.univ : Set X) n), openCell n i := by
    rw [CWComplex.iUnion_openCell_eq_complex]
    exact Set.mem_univ x
  rcases Set.mem_iUnion.mp hxall with ⟨n, hxn⟩
  rcases Set.mem_iUnion.mp hxn with ⟨i, hxi⟩
  by_cases hn0 : n = 0
  · subst n
    exact False.elim (hx (Set.mem_iUnion.mpr
      ⟨Sum.inl i, openCell_subset_closedCell 0 i hxi⟩))
  by_cases hn1 : n = 1
  · subst n
    exact False.elim (hx (Set.mem_iUnion.mpr
      ⟨Sum.inr i, openCell_subset_closedCell 1 i hxi⟩))
  by_cases hn2 : n = 2
  · subst n
    exact Set.mem_iUnion.mpr ⟨i, hxi⟩
  haveI := hdim n (by omega)
  exact isEmptyElim i

theorem iUnion_closedFace_eq_univ
    (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n)) :
    (⋃ f : Face X, closedCell 2 f) = Set.univ := by
  have hc : IsClosed (⋃ f : Face X, closedCell 2 f) :=
    isClosed_iUnion_of_finite (fun _ => isClosed_closedCell)
  have hd : Dense (⋃ f : Face X, closedCell 2 f) :=
    (dense_iUnion_openFace hS hdim).mono (Set.iUnion_mono fun f =>
      openCell_subset_closedCell 2 f)
  apply Set.Subset.antisymm (Set.subset_univ _)
  intro x _
  have hx := hd x
  rwa [hc.closure_eq] at hx

theorem point_in_closedFace
    (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n)) (x : X) :
    ∃ f : Face X, x ∈ closedCell 2 f := by
  apply Set.mem_iUnion.mp
  rw [iUnion_closedFace_eq_univ hS hdim]
  exact Set.mem_univ x

end StressFlex.Spherical

/-! ### Source fragment: notes/stress_flex/DimensionTwoDraft.lean -/

open Set Topology Topology.RelCWComplex

namespace StressFlex.Spherical

variable {X : Type} [TopologicalSpace X] [T2Space X]
  [CWComplex (Set.univ : Set X)]

/-- No cell of dimension at least three can occur in a finite-dimensional CW
structure on an actual topological two-sphere. A top-dimensional nonempty
cell would be ambient-open, contradicting the already proved local-homology
obstruction to the interior of a cell of the wrong dimension. -/
theorem isEmpty_cell_ge_three_of_finiteDimensional
    [CWComplex.FiniteDimensional (Set.univ : Set X)]
    (hS : X ≃ₜ TopCat.sphere.{0} 2) :
    ∀ m : ℕ, 3 ≤ m → IsEmpty (cell (Set.univ : Set X) m) := by
  have descend : ∀ k : ℕ,
      (∀ m : ℕ, k ≤ m → IsEmpty (cell (Set.univ : Set X) m)) →
      ∀ m : ℕ, 3 ≤ m → IsEmpty (cell (Set.univ : Set X) m) := by
    intro k
    induction k with
    | zero =>
      intro hk m hm
      exact hk m (Nat.zero_le m)
    | succ k ih =>
      intro hk
      by_cases h3 : 3 ≤ k
      · have hk0 : IsEmpty (cell (Set.univ : Set X) k) := by
          refine ⟨fun i => ?_⟩
          have hskel := TauCeti.skeletonLT_eq_complex_of_isEmpty_cell
            (Set.univ : Set X) (k + 1) hk
          have htrace := TauCeti.isOpen_preimage_val_openCell
            (C := (Set.univ : Set X)) (S := (Set.univ : Set X)) k
            (by rw [hskel]) i
          have hopen : IsOpen (openCell k i) := by
            simpa using htrace.preimage (Homeomorph.Set.univ X).symm.continuous
          have hne := openCell_nonempty (C := (Set.univ : Set X)) k i
          rw [← hopen.interior_eq,
            interior_openCell_eq_empty_of_ne_two hS k (by omega) i] at hne
          exact Set.not_nonempty_empty hne
        apply ih
        intro m hm
        rcases eq_or_lt_of_le hm with rfl | hm
        · exact hk0
        · exact hk m (Nat.succ_le_of_lt hm)
      · intro m hm
        exact hk m (by omega)
  have hbound : ∀ᶠ n in Filter.atTop, IsEmpty (cell (Set.univ : Set X) n) :=
    @RelCWComplex.FiniteDimensional.eventually_isEmpty_cell X _
      (Set.univ : Set X) (∅ : Set X) _ inferInstance
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp hbound
  exact descend k hk


/-- Compactness of the actual sphere supplies a finite CW-dimensional bound;
no finiteness of the family of cells is assumed in this step. -/
theorem cwFiniteDimensional_of_sphere
    (hS : X ≃ₜ TopCat.sphere.{0} 2) :
    CWComplex.FiniteDimensional (Set.univ : Set X) := by
  letI : CompactSpace (TopCat.sphere.{0} 2) := by
    change CompactSpace (TopCat.diskBoundary.{0} 3)
    infer_instance
  letI : CompactSpace X := hS.symm.compactSpace
  obtain ⟨N, hN⟩ := TauCeti.exists_subset_skeletonLT_of_isCompact
    (C := (Set.univ : Set X)) isCompact_univ Set.Subset.rfl
  refine ⟨Filter.eventually_atTop.mpr ⟨N, ?_⟩⟩
  intro m hm
  refine ⟨fun i => ?_⟩
  obtain ⟨x, hx⟩ := openCell_nonempty (C := (Set.univ : Set X)) m i
  exact (disjoint_skeletonLT_openCell (C := (Set.univ : Set X))
    (n := (N : ℕ∞)) (m := m) (j := i) (by exact_mod_cast hm)).notMem_of_mem_left
      (hN (Set.mem_univ x)) hx

/-- A CW decomposition of an actual two-sphere has no cells above dimension
two. Both the eventual dimension bound and its descent are derived. -/
theorem isEmpty_cell_ge_three_of_sphere
    (hS : X ≃ₜ TopCat.sphere.{0} 2) :
    ∀ m : ℕ, 3 ≤ m → IsEmpty (cell (Set.univ : Set X) m) := by
  letI : CWComplex.FiniteDimensional (Set.univ : Set X) :=
    cwFiniteDimensional_of_sphere hS
  exact isEmpty_cell_ge_three_of_finiteDimensional hS

end StressFlex.Spherical

/-! ### Source fragment: notes/stress_flex/LocalCoefficientConstancyDraft.lean -/

open CategoryTheory Limits Set Topology

namespace StressFlex.Cellular

variable {X : Type} [TopologicalSpace X] [T2Space X]

def localCoefficient (hS : X ≃ₜ TopCat.sphere.{0} 2) {S : Set X}
    (h : (TauCeti.localHomology (A := ModuleCat.{0} ℝ) Coeff S 2 : ModuleCat.{0} ℝ))
    (x : S) : ℝ :=
  (localFundamentalIso hS x.1).inv
    (LocalCoefficient.restrictPoint Coeff 2 x.2 h)

theorem restrictPoint_eq_localCoefficient_smul
    (hS : X ≃ₜ TopCat.sphere.{0} 2) {S : Set X}
    (h : (TauCeti.localHomology (A := ModuleCat.{0} ℝ) Coeff S 2 : ModuleCat.{0} ℝ))
    (x : S) :
    LocalCoefficient.restrictPoint Coeff 2 x.2 h =
      localCoefficient hS h x • localFundamentalClass hS ({x.1} : Set X) := by
  let I := localFundamentalIso hS x.1
  calc
    LocalCoefficient.restrictPoint Coeff 2 x.2 h =
        I.hom (I.inv (LocalCoefficient.restrictPoint Coeff 2 x.2 h)) :=
      (Iso.inv_hom_id_apply I _).symm
    _ = localCoefficient hS h x • I.hom 1 := by
      rw [← map_smul]
      simp only [smul_eq_mul, mul_one, localCoefficient, I]
    _ = localCoefficient hS h x • localFundamentalClass hS ({x.1} : Set X) := by
      rw [localFundamentalIso_one]

theorem localCoefficient_exists_open
    (hS : X ≃ₜ TopCat.sphere.{0} 2) {S : Set X} (hSo : IsOpen S)
    (h : (TauCeti.localHomology (A := ModuleCat.{0} ℝ) Coeff S 2 : ModuleCat.{0} ℝ)) :
    ∀ x : S, ∃ U : Set S, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, localCoefficient hS h y = localCoefficient hS h x := by
  intro x
  have hSnh : S ∈ 𝓝ˢ ({x.1} : Set X) := by
    simpa using hSo.mem_nhds x.2
  let g := localFundamentalClass hS S
  let c : ℝ := localCoefficient hS h x
  have hz : TauCeti.localHomologyRestriction Coeff
      (subset_of_mem_nhdsSet hSnh) 2 (h - c • g) = 0 := by
    change LocalCoefficient.restrictPoint Coeff 2 x.2 (h - c • g) = 0
    rw [map_sub, map_smul, restrictPoint_eq_localCoefficient_smul]
    change localCoefficient hS h x • localFundamentalClass hS {x.1} -
      c • TauCeti.localHomologyRestriction Coeff
        (singleton_subset_iff.mpr x.2) 2 (localFundamentalClass hS S) = 0
    rw [restrict_localFundamentalClass]
    exact sub_self _
  obtain ⟨W, hWnh, hWS, hzW⟩ :=
    TauCeti.exists_mem_nhdsSet_localHomologyRestriction_eq_zero Coeff 2
      hSnh (h - c • g) hz
  have hWnh' : W ∈ 𝓝 x.1 := by simpa using hWnh
  obtain ⟨U, hUW, hUo, hxU⟩ := mem_nhds_iff.mp hWnh'
  refine ⟨Subtype.val ⁻¹' U, hUo.preimage continuous_subtype_val, hxU, ?_⟩
  intro y hy
  have hyW : y.1 ∈ W := hUW hy
  have hzY : LocalCoefficient.restrictPoint Coeff 2 y.2 (h - c • g) = 0 := by
    have hcomp := ConcreteCategory.congr_hom
      (TauCeti.localHomologyRestriction_comp Coeff
        (singleton_subset_iff.mpr hyW) hWS 2) (h - c • g)
    calc
      LocalCoefficient.restrictPoint Coeff 2 y.2 (h - c • g) =
          LocalCoefficient.restrictPoint Coeff 2 hyW
            (TauCeti.localHomologyRestriction Coeff hWS 2 (h - c • g)) := by
        simpa only [ConcreteCategory.comp_apply] using hcomp.symm
      _ = 0 := by rw [hzW, map_zero]
  have hEq : localCoefficient hS h y • localFundamentalClass hS {y.1} =
      c • localFundamentalClass hS {y.1} := by
    rw [← restrictPoint_eq_localCoefficient_smul]
    have hg : LocalCoefficient.restrictPoint Coeff 2 y.2 g =
        localFundamentalClass hS ({y.1} : Set X) :=
      restrict_localFundamentalClass hS (singleton_subset_iff.mpr y.2)
    simpa only [map_sub, map_smul, hg, sub_eq_zero] using hzY
  have hsmul : (localCoefficient hS h y - c) •
      localFundamentalClass hS ({y.1} : Set X) = 0 := by
    rw [sub_smul, hEq, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hsmul).resolve_right
    (localFundamentalClass_ne_zero hS y.1))

/-- Every coefficient preimage is open, the intrinsic local-constancy property.
The proof uses only the neighbourhood API already available in this module. -/
theorem isOpen_localCoefficient_preimage
    (hS : X ≃ₜ TopCat.sphere.{0} 2) {S : Set X} (hSo : IsOpen S)
    (h : (TauCeti.localHomology (A := ModuleCat.{0} ℝ) Coeff S 2 : ModuleCat.{0} ℝ))
    (T : Set ℝ) : IsOpen (localCoefficient hS h ⁻¹' T) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨U, hUo, hxU, hU⟩ := localCoefficient_exists_open hS hSo h x
  apply Filter.mem_of_superset (hUo.mem_nhds hxU)
  intro y hy
  change localCoefficient hS h y ∈ T
  rw [hU y hy]
  exact hx

theorem isOpen_localCoefficient_fiber
    (hS : X ≃ₜ TopCat.sphere.{0} 2) {S : Set X} (hSo : IsOpen S)
    (h : (TauCeti.localHomology (A := ModuleCat.{0} ℝ) Coeff S 2 : ModuleCat.{0} ℝ))
    (c : ℝ) : IsOpen {x : S | localCoefficient hS h x = c} :=
  isOpen_localCoefficient_preimage hS hSo h {c}

/-- A continuous parameterization from any preconnected domain transports the
locally constant coefficient to a single coefficient. In particular the
domain can be the actual open interval parameterizing an open one-cell. -/
theorem localCoefficient_eq_along_preconnected
    (hS : X ≃ₜ TopCat.sphere.{0} 2) {S : Set X} (hSo : IsOpen S)
    (h : (TauCeti.localHomology (A := ModuleCat.{0} ℝ) Coeff S 2 : ModuleCat.{0} ℝ))
    {Y : Type} [TopologicalSpace Y] [PreconnectedSpace Y]
    (f : Y → S) (hf : Continuous f) (x y : Y) :
    localCoefficient hS h (f x) = localCoefficient hS h (f y) := by
  classical
  let F : Y → ℝ := fun z => localCoefficient hS h (f z)
  have hF (T : Set ℝ) : IsOpen (F ⁻¹' T) :=
    hf.isOpen_preimage _ (isOpen_localCoefficient_preimage hS hSo h T)
  let U : Set Y := F ⁻¹' {F y}
  have hU : IsOpen U := hF {F y}
  have hUc : IsOpen Uᶜ := by
    simpa only [U, Set.preimage_compl] using hF ({F y}ᶜ : Set ℝ)
  by_contra hxy
  have hxUc : x ∈ Uᶜ := hxy
  have hyU : y ∈ U := rfl
  have hc := isPreconnected_univ U Uᶜ hU hUc
    (by simp only [union_compl_self, Set.subset_univ])
    ⟨y, Set.mem_univ _, hyU⟩ ⟨x, Set.mem_univ _, hxUc⟩
  simpa only [Set.inter_compl_self, Set.inter_empty, Set.not_nonempty_empty] using hc

end StressFlex.Cellular

/-! ### Source fragment: notes/stress_flex/OppositeEdgeDraft.lean -/

open CategoryTheory Limits Topology Topology.RelCWComplex Metric Set

namespace StressFlex.Spherical

variable {X : Type} [TopologicalSpace X] [T2Space X]
  [CWComplex (Set.univ : Set X)]
  [Fintype (Vertex X)] [Fintype (Edge X)] [Fintype (Face X)]
  [DecidableEq (Vertex X)]

def oppositeEdge (e : Edge X) : CWComplex.Subcomplex (Set.univ : Set X) := by
  classical
  exact {
    carrier := (⋃ v : Vertex X, closedCell 0 v) ∪
      ⋃ j : {j : Edge X // j ≠ e}, closedCell 1 j.1
    I
      | 0 => Set.univ
      | 1 => {j | j ≠ e}
      | _ + 2 => ∅
    closed' := (isClosed_iUnion_of_finite fun _ => isClosed_closedCell).union
      (isClosed_iUnion_of_finite fun _ => isClosed_closedCell)
    union' := by
      ext x
      simp only [Set.empty_union, Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq,
        Set.mem_empty_iff_false]
      constructor
      · rintro ⟨n, j, hx⟩
        cases n with
        | zero => exact Or.inl ⟨j.1, openCell_subset_closedCell 0 j.1 hx⟩
        | succ n =>
          cases n with
          | zero => exact Or.inr ⟨j, openCell_subset_closedCell 1 j.1 hx⟩
          | succ n => exact False.elim j.2
      · rintro (⟨v, hv⟩ | ⟨j, hj⟩)
        · refine ⟨0, ⟨v, Set.mem_univ _⟩, ?_⟩
          simpa only [closedCell_zero_eq_singleton, openCell_zero_eq_singleton] using hv
        · rw [closedCell_edge] at hj
          rcases hj with hj | hj
          · rcases Set.mem_insert_iff.mp hj with hj | hj
            · refine ⟨0, ⟨tail j.1, Set.mem_univ _⟩, ?_⟩
              simpa only [openCell_zero_eq_singleton, Set.mem_singleton_iff, vertexPoint]
                using hj
            · refine ⟨0, ⟨head j.1, Set.mem_univ _⟩, ?_⟩
              simpa only [openCell_zero_eq_singleton, Set.mem_singleton_iff, vertexPoint]
                using hj
          · exact ⟨1, j, hj⟩ }

theorem openEdge_subset_compl_oppositeEdge (e : Edge X) :
    openCell 1 e ⊆ (oppositeEdge e : Set X)ᶜ := by
  have hd := (oppositeEdge e).disjoint_openCell_subcomplex_of_notMem
    (show e ∉ (oppositeEdge e).I 1 by simp [oppositeEdge])
  intro x hx
  exact hd.notMem_of_mem_left hx

theorem openFace_subset_compl_oppositeEdge (e : Edge X) (f : Face X) :
    openCell 2 f ⊆ (oppositeEdge e : Set X)ᶜ := by
  have hd := (oppositeEdge e).disjoint_openCell_subcomplex_of_notMem
    (show f ∉ (oppositeEdge e).I 2 by simp [oppositeEdge])
  intro x hx
  exact hd.notMem_of_mem_left hx

theorem isOpen_compl_oppositeEdge (e : Edge X) :
    IsOpen (oppositeEdge e : Set X)ᶜ := (oppositeEdge e).closed.isOpen_compl

def oppositeEdgeRelOne (e : Edge X) :
    Cellular.Relative.RelCell (Set.univ : Set X) (oppositeEdge e) 1 :=
  Cellular.Relative.keptCell (Set.univ : Set X) (oppositeEdge e) e
    (by simp [oppositeEdge])

/-- The sole relative one-cell is the omitted edge, with its original
characteristic map and orientation. -/
def oppositeEdgeRelOneEquiv (e : Edge X) :
    Cellular.Relative.RelCell (Set.univ : Set X) (oppositeEdge e) 1 ≃ Unit where
  toFun _ := ()
  invFun _ := oppositeEdgeRelOne e
  left_inv j := by
    apply ((oppositeEdge e).relCWComplexCellEquiv 1).injective
    apply Subtype.ext
    have hj : ((oppositeEdge e).relCWComplexCellEquiv 1 j).val = e := by
      have h := ((oppositeEdge e).relCWComplexCellEquiv 1 j).property
      simpa [oppositeEdge] using h
    simpa only [oppositeEdgeRelOne, Cellular.Relative.keptCell, Equiv.apply_symm_apply]
      using hj.symm
  right_inv u := by cases u; rfl

theorem oppositeEdge_relZero_isEmpty (e : Edge X) :
    IsEmpty (Cellular.Relative.RelCell (Set.univ : Set X) (oppositeEdge e) 0) := by
  refine ⟨fun j => ?_⟩
  have h := ((oppositeEdge e).relCWComplexCellEquiv 0 j).property
  simpa [oppositeEdge] using h

/-- Every absolute face is retained in the relative pair. -/
def oppositeEdgeRelFaceEquiv (e : Edge X) :
    Cellular.Relative.RelCell (Set.univ : Set X) (oppositeEdge e) 2 ≃ Face X where
  toFun j := ((oppositeEdge e).relCWComplexCellEquiv 2 j).val
  invFun f := Cellular.Relative.keptCell (Set.univ : Set X) (oppositeEdge e) f
    (by simp [oppositeEdge])
  left_inv j := by
    apply ((oppositeEdge e).relCWComplexCellEquiv 2).injective
    apply Subtype.ext
    simp only [Cellular.Relative.keptCell, Equiv.apply_symm_apply]
  right_inv f := by
    simp only [Cellular.Relative.keptCell, Equiv.apply_symm_apply]

/-- The genuine open-cell homeomorphism, followed by the inclusion into the
ambient-open complement of the opposite-edge graph. -/
def openEdgeInComplement (e : Edge X) :
    ball (0 : Fin 1 → ℝ) 1 → ↥((oppositeEdge e : Set X)ᶜ) := fun t =>
  ⟨(TauCeti.openCellHomeomorph 1 e t).1,
    openEdge_subset_compl_oppositeEdge e (TauCeti.openCellHomeomorph 1 e t).2⟩

theorem continuous_openEdgeInComplement (e : Edge X) :
    Continuous (openEdgeInComplement e) :=
  (continuous_subtype_val.comp (TauCeti.openCellHomeomorph 1 e).continuous).subtype_mk _

theorem openEdgeInComplement_surjective_on_edge (e : Edge X) (x : X)
    (hx : x ∈ openCell 1 e) :
    ∃ t : ball (0 : Fin 1 → ℝ) 1, (openEdgeInComplement e t).1 = x := by
  refine ⟨(TauCeti.openCellHomeomorph 1 e).symm ⟨x,hx⟩, ?_⟩
  change (TauCeti.openCellHomeomorph 1 e
    ((TauCeti.openCellHomeomorph 1 e).symm ⟨x,hx⟩)).1 = x
  rw [Homeomorph.apply_symm_apply]

theorem preconnected_openEdgeParameter :
    PreconnectedSpace (ball (0 : Fin 1 → ℝ) 1) :=
  isPreconnected_iff_preconnectedSpace.mp isPreconnected_ball

end StressFlex.Spherical

/-! ### Source fragment: notes/stress_flex/FaceSupportDraft.lean -/

open CategoryTheory Limits Set Topology Topology.RelCWComplex

namespace StressFlex.Spherical

variable {X : Type} [TopologicalSpace X] [T2Space X]
  [CWComplex (Set.univ : Set X)]
  [Fintype (Vertex X)] [Fintype (Edge X)] [Fintype (Face X)]
  [DecidableEq (Vertex X)]

open Cellular

/-- The support of a single-face relative homology class lies in the actual
closure of that face. This follows from density and local constancy, and does
not assume that a face characteristic map is injective on its boundary. -/
theorem localCoefficient_eq_zero_outside_closedFace
    (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n))
    {S : Set X} (hSo : IsOpen S)
    (h : TauCeti.localHomology (A := ModuleCat.{0} ℝ) Coeff S 2)
    (f : Face X)
    (hother : ∀ g : Face X, g ≠ f → ∀ y : S, y.1 ∈ openCell 2 g →
      LocalCoefficient.restrictPoint Coeff 2 y.2 h = 0)
    (x : S) (hx : x.1 ∉ closedCell 2 f) :
    localCoefficient hS h x = 0 := by
  let D : Set S := Subtype.val ⁻¹' (⋃ g : Face X, openCell 2 g)
  have hD : Dense D :=
    (dense_iUnion_openFace hS hdim).preimage hSo.isOpenMap_subtype_val
  let U : Set S :=
    {y | localCoefficient hS h y = localCoefficient hS h x} ∩
      Subtype.val ⁻¹' (closedCell 2 f)ᶜ
  have hU : IsOpen U :=
    (isOpen_localCoefficient_fiber hS hSo h _).inter
      (isClosed_closedCell.isOpen_compl.preimage continuous_subtype_val)
  have hxU : x ∈ U := ⟨rfl, hx⟩
  obtain ⟨y, hyU, hyD⟩ := hD.inter_open_nonempty U hU ⟨x, hxU⟩
  obtain ⟨g, hyg⟩ := Set.mem_iUnion.mp hyD
  have hgf : g ≠ f := by
    intro hgf
    subst g
    exact hyU.2 (openCell_subset_closedCell 2 f hyg)
  have hy0 : localCoefficient hS h y = 0 := by
    unfold localCoefficient
    rw [hother g hgf y hyg, map_zero]
  exact hyU.1.symm.trans hy0

/-- A class supported on a single face and nonzero at a point must meet that
face's actual closure. -/
theorem mem_closedFace_of_localCoefficient_ne_zero
    (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n))
    {S : Set X} (hSo : IsOpen S)
    (h : TauCeti.localHomology (A := ModuleCat.{0} ℝ) Coeff S 2)
    (f : Face X)
    (hother : ∀ g : Face X, g ≠ f → ∀ y : S, y.1 ∈ openCell 2 g →
      LocalCoefficient.restrictPoint Coeff 2 y.2 h = 0)
    (x : S) (hx : localCoefficient hS h x ≠ 0) :
    x.1 ∈ closedCell 2 f := by
  by_contra hnot
  exact hx (localCoefficient_eq_zero_outside_closedFace hS hdim hSo h f hother x hnot)

end StressFlex.Spherical

/-! ### Source fragment: notes/stress_flex/ZeroIncidenceCoverageDraft.lean -/

open CategoryTheory Limits Set Topology Topology.RelCWComplex Metric
open scoped BigOperators

namespace StressFlex.Cellular.Relative

variable {X : Type} [TopologicalSpace X] [T2Space X]
  (C : Set X) [CWComplex C] (K : CWComplex.Subcomplex C)

theorem baseToChains_injective (n : ℕ) :
    Function.Injective (baseToChains C K n) := by
  letI : RelCWComplex C (K : Set X) := K.relCWComplex
  change Function.Injective (TopPair.singularHomologyMap
    (TauCeti.skeletonBasePairToSkeletonPair (D := (K : Set X)) C n) Coeff n)
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

end StressFlex.Cellular.Relative

namespace StressFlex.Spherical

variable {X : Type} [TopologicalSpace X] [T2Space X]
  [CWComplex (Set.univ : Set X)]
  [Fintype (Vertex X)] [Fintype (Edge X)] [Fintype (Face X)]
  [DecidableEq (Vertex X)]

open Cellular

theorem relative_single_face_cycle_of_zero_row (e : Edge X)
    (he : ∀ f : Face X, faceBoundary e f = 0) (f : Face X) :
    @TauCeti.cellularDifferential X _ _ (oppositeEdge e : Set X)
      (Set.univ : Set X) (oppositeEdge e).relCWComplex (ModuleCat.{0} ℝ) _ _ _ Coeff 1
      (Relative.quotientChains (Set.univ : Set X) (oppositeEdge e) 2
        (TauCeti.cellularChainBasis (Set.univ : Set X) ℝ 2 f)) = 0 := by
  let K := oppositeEdge e
  let b := TauCeti.cellularChainBasis (Set.univ : Set X) ℝ 2 f
  apply (Relative.basis (Set.univ : Set X) K 1).repr.injective
  ext j
  rw [map_zero, Finsupp.zero_apply]
  have hcomp := ConcreteCategory.congr_hom
    (Relative.quotientChains_d (Set.univ : Set X) K 1) b
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hcomp
  rw [hcomp]
  have hi : e ∉ K.I 1 := by simp [K, oppositeEdge]
  have hj : Relative.keptCell (Set.univ : Set X) K e hi = j := by
    apply (oppositeEdgeRelOneEquiv e).injective
    exact Subsingleton.elim _ _
  rw [← hj, Relative.quotientChains_coordinate]
  simpa only [faceBoundary, TauCeti.cellularIncidence_def, b] using he f

theorem exists_single_face_base_of_zero_row (e : Edge X)
    (he : ∀ f : Face X, faceBoundary e f = 0) (f : Face X) :
    ∃ h : Relative.baseGroup (Set.univ : Set X) (oppositeEdge e) 2,
      Relative.baseToChains (Set.univ : Set X) (oppositeEdge e) 2 h =
        Relative.quotientChains (Set.univ : Set X) (oppositeEdge e) 2
          (TauCeti.cellularChainBasis (Set.univ : Set X) ℝ 2 f) := by
  letI : RelCWComplex (Set.univ : Set X) (oppositeEdge e : Set X) :=
    (oppositeEdge e).relCWComplex
  exact Ambient.exists_base_class (D := (oppositeEdge e : Set X)) (Set.univ : Set X) 1 _
    (relative_single_face_cycle_of_zero_row e he f)

/-- A face basis lift has zero local value in every other open face. -/
theorem single_face_base_local_zero (e : Edge X) (f : Face X)
    (h : Relative.baseGroup (Set.univ : Set X) (oppositeEdge e) 2)
    (hh : Relative.baseToChains (Set.univ : Set X) (oppositeEdge e) 2 h =
      Relative.quotientChains (Set.univ : Set X) (oppositeEdge e) 2
        (TauCeti.cellularChainBasis (Set.univ : Set X) ℝ 2 f))
    (g : Face X) (hgf : g ≠ f)
    (y : {y : X // y ∉ (oppositeEdge e : Set X)}) (hy : y.1 ∈ openCell 2 g) :
    LocalCoefficient.restrictPoint Coeff 2 y.2
      (Relative.baseToLocal (Set.univ : Set X) (oppositeEdge e) 2
        (oppositeEdge e : Set X)ᶜ (by simp) h) = 0 := by
  have hg : g ∉ (oppositeEdge e).I 2 := by simp [oppositeEdge]
  obtain ⟨γ, hread, _⟩ := Relative.read_two_base_classes
    (Set.univ : Set X) (oppositeEdge e) (oppositeEdge e : Set X)ᶜ (by simp)
      g hg y.1 hy y.2 h h
  rw [hh, Relative.quotientChains_coordinate, Module.Basis.repr_self] at hread
  simpa [hgf, Ne.symm hgf] using hread

/-- The actual relative fundamental class is the finite sum of the individual
face basis lifts, with the actual (possibly signed) fundamental coefficients. -/
theorem fundamental_relative_expansion
    (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n))
    (e : Edge X)
    (h : Face X → Relative.baseGroup (Set.univ : Set X) (oppositeEdge e) 2)
    (hh : ∀ f, Relative.baseToChains (Set.univ : Set X) (oppositeEdge e) 2 (h f) =
      Relative.quotientChains (Set.univ : Set X) (oppositeEdge e) 2
        (TauCeti.cellularChainBasis (Set.univ : Set X) ℝ 2 f)) :
    Relative.quotientBase (Set.univ : Set X) (oppositeEdge e) 2
      ((TauCeti.skeletonBasePair (Set.univ : Set X) 2).singularHomologyπ Coeff 2
        ((skeletalTopIso hS hdim).inv 1)) =
      ∑ f, fundamentalCellularCycle hS hdim f • h f := by
  apply Relative.baseToChains_injective (Set.univ : Set X) (oppositeEdge e) 2
  have hm : (TauCeti.skeletonBasePair (Set.univ : Set X) 2).singularHomologyπ
      (C := ModuleCat.{0} ℝ) Coeff 2 ≫
      Relative.quotientBase (Set.univ : Set X) (oppositeEdge e) 2 ≫
      Relative.baseToChains (Set.univ : Set X) (oppositeEdge e) 2 =
      TauCeti.skeletonPairπ (Set.univ : Set X) Coeff 2 ≫
      Relative.quotientChains (Set.univ : Set X) (oppositeEdge e) 2 := by
    rw [Relative.quotientBase_comp, ← Category.assoc, base_projection_comp] <;> rfl
  have hq := ConcreteCategory.congr_hom hm ((skeletalTopIso hS hdim).inv 1)
  change Relative.baseToChains (Set.univ : Set X) (oppositeEdge e) 2
      (Relative.quotientBase (Set.univ : Set X) (oppositeEdge e) 2
        ((TauCeti.skeletonBasePair (Set.univ : Set X) 2).singularHomologyπ Coeff 2
          ((skeletalTopIso hS hdim).inv 1))) =
      Relative.quotientChains (Set.univ : Set X) (oppositeEdge e) 2
        (fundamentalChain hS hdim) at hq
  rw [hq]
  change Relative.quotientChains (Set.univ : Set X) (oppositeEdge e) 2
      (fundamentalChain hS hdim) = _
  conv_lhs => rw [← (TauCeti.cellularChainBasis (Set.univ : Set X) ℝ 2).sum_repr
    (fundamentalChain hS hdim)]
  simp only [map_sum, map_smul, hh, fundamentalCellularCycle]

theorem closedEdge_in_face_of_zero_row
    (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n))
    (e : Edge X) (he : ∀ f : Face X, faceBoundary e f = 0) :
    ∃ f : Face X, closedCell 1 e ⊆ closedCell 2 f := by
  classical
  choose h hh using exists_single_face_base_of_zero_row e he
  let S : Set X := (oppositeEdge e : Set X)ᶜ
  have hKS : (oppositeEdge e : Set X) ⊆ Sᶜ := by simp [S]
  let H (f : Face X) : TauCeti.localHomology (A := ModuleCat.{0} ℝ) Coeff S 2 :=
    Relative.baseToLocal (Set.univ : Set X) (oppositeEdge e) 2 S hKS (h f)
  have hsum : localFundamentalClass hS S =
      ∑ f, fundamentalCellularCycle hS hdim f • H f := by
    have hr := fundamental_relative_expansion hS hdim e h hh
    have hq := ConcreteCategory.congr_hom
      (Relative.quotientBase_toLocal (Set.univ : Set X) (oppositeEdge e) 2 S hKS)
        ((TauCeti.skeletonBasePair (Set.univ : Set X) 2).singularHomologyπ Coeff 2
          ((skeletalTopIso hS hdim).inv 1))
    change Relative.baseToLocal (Set.univ : Set X) (oppositeEdge e) 2 S hKS
        (Relative.quotientBase (Set.univ : Set X) (oppositeEdge e) 2
          ((TauCeti.skeletonBasePair (Set.univ : Set X) 2).singularHomologyπ Coeff 2
            ((skeletalTopIso hS hdim).inv 1))) =
        TopPair.singularHomologyMap
          (Ambient.basePairToLocal (Set.univ : Set X) 2 S (Set.empty_subset _)) Coeff 2
          ((TauCeti.skeletonBasePair (Set.univ : Set X) 2).singularHomologyπ Coeff 2
            ((skeletalTopIso hS hdim).inv 1)) at hq
    have hm := congrArg
      (Relative.baseToLocal (Set.univ : Set X) (oppositeEdge e) 2 S hKS) hr
    rw [hq.trans (skeletal_base_generator_to_local hS hdim S)] at hm
    simpa only [map_sum, map_smul, H] using hm
  obtain ⟨x, hx⟩ := openCell_nonempty (C := (Set.univ : Set X)) 1 e
  let xS : S := ⟨x, openEdge_subset_compl_oppositeEdge e hx⟩
  have hex : ∃ f, localCoefficient hS (H f) xS ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    have hz : LocalCoefficient.restrictPoint Coeff 2 xS.2
        (localFundamentalClass hS S) = 0 := by
      rw [hsum, map_sum]
      apply Finset.sum_eq_zero
      intro f hf
      rw [map_smul, restrictPoint_eq_localCoefficient_smul, hnone f, zero_smul, smul_zero]
    rw [LocalCoefficient.restrictPoint, restrict_localFundamentalClass] at hz
    exact localFundamentalClass_ne_zero hS x hz
  obtain ⟨f, hf⟩ := hex
  refine ⟨f, ?_⟩
  rw [← closure_openCell_eq_closedCell]
  apply closure_minimal _ isClosed_closedCell
  intro y hy
  let yS : S := ⟨y, openEdge_subset_compl_oppositeEdge e hy⟩
  have hyf : localCoefficient hS (H f) yS ≠ 0 := by
    obtain ⟨tx, htx⟩ := openEdgeInComplement_surjective_on_edge e x hx
    obtain ⟨ty, hty⟩ := openEdgeInComplement_surjective_on_edge e y hy
    letI := preconnected_openEdgeParameter
    have hconst := localCoefficient_eq_along_preconnected hS
      (isOpen_compl_oppositeEdge e) (H f) (openEdgeInComplement e)
        (continuous_openEdgeInComplement e) ty tx
    have htx' : openEdgeInComplement e tx = xS := Subtype.ext htx
    have hty' : openEdgeInComplement e ty = yS := Subtype.ext hty
    rw [htx', hty'] at hconst
    exact fun hz => hf (hconst.symm.trans hz)
  exact mem_closedFace_of_localCoefficient_ne_zero hS hdim
    (isOpen_compl_oppositeEdge e) (H f) f
      (fun g hgf z hz => single_face_base_local_zero e f (h f) (hh f) g hgf z hz)
      yS hyf

/-- Whole-edge face coverage is a theorem of the actual CW sphere, including
edges whose entire cellular incidence row vanishes. -/
theorem every_closedEdge_in_closedFace
    (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n))
    (e : Edge X) :
    ∃ f : Face X, closedCell 1 e ⊆ closedCell 2 f := by
  classical
  by_cases he : ∀ f : Face X, faceBoundary e f = 0
  · exact closedEdge_in_face_of_zero_row hS hdim e he
  · push_neg at he
    obtain ⟨f, hf⟩ := he
    exact ⟨f, closedEdge_subset_closedFace e f hf⟩

end StressFlex.Spherical

/-! ### Source fragment: notes/stress_flex/PaperStatementsDraft.lean -/

open CategoryTheory Topology Topology.RelCWComplex Matrix
open scoped BigOperators

namespace StressFlex.Spherical

variable {X : Type} [TopologicalSpace X] [T2Space X]
  [CWComplex (Set.univ : Set X)]
  [Fintype (Vertex X)] [Fintype (Edge X)] [Fintype (Face X)]
  [DecidableEq (Vertex X)]

/-- Exactly the paper's geometric vertex, face-plane and simple-graph data.
Neither face coverage nor injectivity of any two-cell characteristic map is
part of this structure. The geometric image may cross itself. -/
structure PaperRealization where
  position : Vertex X → Geometric.Vec
  injective_position : Function.Injective position
  normal : Face X → Geometric.Vec
  level : Face X → ℝ
  planar : ∀ f v, faceContains f v → normal f ⬝ᵥ position v = level f
  noncollinear : NoncollinearFaces position
  no_loops : ∀ e : Edge X, tail e ≠ head e
  no_parallel_edges : SimpleOneSkeleton (X := X)

/-- The incidence conditions required internally are theorems of a genuine
CW sphere, including bridges with zero cellular incidence. -/
def PaperRealization.toAffine
    (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (hdim : ∀ n, 3 ≤ n → IsEmpty (cell (Set.univ : Set X) n))
    (P : PaperRealization (X := X)) : AffineRealization (X := X) where
  position := P.position
  injective_position := P.injective_position
  normal := P.normal
  level := P.level
  planar := P.planar
  vertex_in_face := fun v => point_in_closedFace hS hdim (vertexPoint v)
  edge_in_face := every_closedEdge_in_closedFace hS hdim
  edge_injective := fun e => (edge_attaching_injective_iff e).mpr (P.no_loops e)

/-- The spherical clause of Theorem 1 with no unproved incidence-coverage
premise and no geometric embeddedness premise. -/
theorem paper_theorem_one_spherical
    (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (P : PaperRealization (X := X))
    (x : Geometric.Vec) (hx : ∀ f, P.normal f ⬝ᵥ x ≠ P.level f)
    (w : Edge X → ℝ) (c : Vertex X → ℝ) (u : Vertex X → Geometric.Vec)
    (hc : Geometric.IsStress P.position tail head x w c)
    (hu : Geometric.IsMotion (fun v => P.position v - x) tail head u) :
    ∑ v, c v • u v = 0 := by
  let hdim := isEmpty_cell_ge_three_of_sphere hS
  exact theorem_one_spherical hS hdim (P.toAffine hS hdim) P.noncollinear
    P.no_parallel_edges x hx w c u hc hu

/-- Proposition 3 for the paper's exact geometric input. The height space is
the actual affine-on-faces space, the quotient kills exactly global linear
functionals relative to the apex, and every stress has a genuine analytic
continuation. -/
theorem paper_proposition_three
    (hS : X ≃ₜ TopCat.sphere.{0} 2)
    (P : PaperRealization (X := X))
    (x : Geometric.Vec) (hx : ∀ f, P.normal f ⬝ᵥ x ≠ P.level f) :
    Nonempty ((Liftings.linearLiftings (fun v => P.position v - x) faceContains ⧸
      (Liftings.globalLinear (fun v => P.position v - x) faceContains).range) ≃ₗ[ℝ]
        Liftings.stresses (fun v => P.position v - x) tail head) ∧
    Liftings.affineLiftings P.position faceContains =
      Liftings.linearLiftings (fun v => P.position v - x) faceContains ∧
    Module.finrank ℝ (Liftings.stresses (fun v => P.position v - x) tail head) + 3 =
      Module.finrank ℝ (Liftings.affineLiftings P.position faceContains) ∧
    ∀ q : Liftings.stresses (fun v => P.position v - x) tail head,
      ∃ (U : Set Geometric.Vec) (W : Geometric.Vec → Edge X → ℝ)
        (C : Geometric.Vec → Vertex X → ℝ),
        IsOpen U ∧ x ∈ U ∧ W x = q.1.1 ∧ C x = q.1.2 ∧
        AnalyticOnNhd ℝ W U ∧ AnalyticOnNhd ℝ C U ∧
        ∀ y ∈ U, Geometric.IsStress P.position tail head y (W y) (C y) := by
  let hdim := isEmpty_cell_ge_three_of_sphere hS
  exact proposition_three hS hdim (P.toAffine hS hdim) P.noncollinear x hx

end StressFlex.Spherical

#print axioms StressFlex.Spherical.theorem_one_spherical

#print axioms StressFlex.Liftings.mem_affineLiftings_iff_affineMap

#print axioms StressFlex.Spherical.potential_defines_linear_lifting

#print axioms StressFlex.Spherical.liftingStressEquivAt

#print axioms StressFlex.Spherical.mem_stressesAt_iff_full

#print axioms StressFlex.Spherical.stress_dimension_add_three_at_apex

#print axioms StressFlex.Spherical.proposition_three

#print axioms StressFlex.Spherical.every_closedEdge_in_closedFace

#print axioms StressFlex.Spherical.isEmpty_cell_ge_three_of_finiteDimensional

#print axioms StressFlex.Spherical.isEmpty_cell_ge_three_of_sphere

#print axioms StressFlex.Spherical.paper_theorem_one_spherical

#print axioms StressFlex.Spherical.paper_proposition_three

/- Read-only dependency audit. This command does not add declarations or modify
   the environment; it inspects already kernel-checked constants. -/
run_cmd do
  let env ← Lean.getEnv
  let roots : Array Lean.Name := #[`StressFlex.continuation_orthogonality, `StressFlex.Spherical.theorem_one_spherical, `StressFlex.Spherical.proposition_three, `StressFlex.Torus.stress_flex_counterexample, `StressFlex.Spherical.paper_height_space_eq_at_apex, `StressFlex.Liftings.mem_affineLiftings_iff_affineMap, `StressFlex.Spherical.mem_stressesAt_iff_full, `StressFlex.Spherical.potential_defines_linear_lifting, `StressFlex.Spherical.vertex_in_face_of_edge_coverage, `StressFlex.Spherical.every_closedEdge_in_closedFace, `StressFlex.Spherical.point_in_closedFace, `StressFlex.Spherical.isEmpty_cell_ge_three_of_finiteDimensional, `StressFlex.Spherical.isEmpty_cell_ge_three_of_sphere, `StressFlex.Spherical.paper_theorem_one_spherical, `StressFlex.Spherical.paper_proposition_three]
  let mut pending := roots
  let mut cursor := 0
  let mut visited : Lean.NameSet := {}
  let mut rows : Array Lean.Json := #[]
  while cursor < pending.size do
    let name := pending[cursor]!
    cursor := cursor + 1
    if visited.contains name then
      continue
    visited := visited.insert name
    if let some idx := env.getModuleIdxFor? name then
      rows := rows.push (Lean.Json.mkObj [
        ("name", Lean.Json.str name.toString),
        ("status", Lean.Json.str "imported checked dependency"),
        ("module", Lean.Json.str env.header.moduleNames[idx.toNat]!.toString)])
    else
      let some info := env.checked.get.find? name |
        throwError "Missing kernel declaration in dependency audit: {name}"
      let typeDependencies := info.type.getUsedConstants
      let valueDependencies := match info.value? (allowOpaque := true) with
        | some value => value.getUsedConstants
        | none => #[]
      let allDependencies := info.getUsedConstantsAsSet.toArray
      pending := pending ++ allDependencies
      let mut fields := [
        ("name", Lean.Json.str name.toString),
        ("status", Lean.Json.str "current module kernel declaration"),
        ("type_dependencies", Lean.toJson (typeDependencies.map Lean.Name.toString)),
        ("value_dependencies", Lean.toJson (valueDependencies.map Lean.Name.toString)),
        ("all_dependencies", Lean.toJson (allDependencies.map Lean.Name.toString))]
      if roots.contains name then
        let fullType ← Lean.Elab.Command.liftTermElabM do
          Lean.withOptions (fun options => options.setBool `pp.universes true)
            (Lean.Meta.ppExpr info.type)
        fields := fields ++ [("root_type", Lean.Json.str fullType.pretty)]
      rows := rows.push (Lean.Json.mkObj fields)
  let graph := Lean.Json.mkObj [
    ("module", Lean.Json.str env.mainModule.toString),
    ("roots", Lean.toJson (roots.map Lean.Name.toString)),
    ("nodes", Lean.Json.arr rows),
    ("boundary", Lean.Json.str "Imported constants are the verified-library boundary; current-module dependencies are expanded transitively.")]
  Lean.logInfo ("KERNEL_DEPENDENCY_GRAPH " ++ graph.compress)
