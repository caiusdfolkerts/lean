module
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega

@[expose] public section
noncomputable section

namespace Papers.RationalityTen.MultiaffineDensity

open Set Filter Topology MvPolynomial

def RationalVector {ι : Type*} (x : ι → ℝ) : Prop :=
  ∀ i, ∃ q : ℚ, (q : ℝ) = x i

theorem rationalVector_dense {ι : Type*} :
    Dense {x : ι → ℝ | RationalVector x} := by
  have h : DenseRange (fun q : ι → ℚ => fun i => (q i : ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  apply h.mono
  rintro _ ⟨q,rfl⟩ i
  exact ⟨q i,rfl⟩

theorem rationalVector_update {ι : Type*} [DecidableEq ι]
    {x : ι → ℝ} (hx : RationalVector x) (i : ι)
    (a : ℚ) : RationalVector (Function.update x i (a : ℝ)) := by
  intro j
  by_cases hji : j=i
  · subst j
    exact ⟨a,by simp⟩
  · simpa only [Function.update_of_ne hji] using hx j

def axisSlope {ι : Type*} [DecidableEq ι]
    (f : (ι → ℝ) → ℝ) (i : ι) (x : ι → ℝ) : ℝ :=
  f (Function.update x i 1) - f (Function.update x i 0)

def AffineIn {ι : Type*} [DecidableEq ι]
    (f : (ι → ℝ) → ℝ) (i : ι) : Prop :=
  ∀ x t, f (Function.update x i t) =
    f (Function.update x i 0) + t * axisSlope f i x

theorem regular_axis_rational_density {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℝ) (hc : Continuous f)
    (hrat : ∀ x, RationalVector x → ∃ q : ℚ, (q : ℝ) = f x)
    (i : ι) (haff : AffineIn f i)
    (x : ι → ℝ) (hx : f x=0) (hslope : axisSlope f i x≠0) :
    x∈closure {q | RationalVector q ∧ f q=0} := by
  let a := axisSlope f i
  let b := fun q : ι → ℝ => f (Function.update q i 0)
  let T := fun q : ι → ℝ => Function.update q i (- b q / a q)
  have ha : Continuous a :=
    (hc.comp (continuous_id.update i continuous_const)).sub
      (hc.comp (continuous_id.update i continuous_const))
  have hb : Continuous b := hc.comp (continuous_id.update i continuous_const)
  have hTc : ContinuousAt T x :=
    continuousAt_id.update i ((hb.continuousAt.neg).div ha.continuousAt hslope)
  have hTx : T x=x := by
    have hfx := haff x (x i)
    rw [Function.update_eq_self,hx] at hfx
    have hroot : - b x / a x=x i := by
      apply (div_eq_iff hslope).mpr
      dsimp [a,b] at *
      linarith
    simp only [T,hroot,Function.update_eq_self]
  have hnear : x∈closure ({q | RationalVector q} ∩ {q | a q≠0}) := by
    have h := rationalVector_dense x
    rw [mem_closure_iff_frequently] at h ⊢
    exact h.and_eventually (ha.continuousAt.eventually_ne hslope)
  have hT := mem_closure_image hTc hnear
  rw [hTx] at hT
  apply closure_mono ?_ hT
  rintro _ ⟨q,⟨hq,haq⟩,rfl⟩
  constructor
  · obtain ⟨u,hu⟩ := hrat (Function.update q i 0) (by simpa using rationalVector_update hq i 0)
    obtain ⟨v,hv⟩ := hrat (Function.update q i 1) (by simpa using rationalVector_update hq i 1)
    have hr : ((-u/(v-u) : ℚ) : ℝ) = - b q / a q := by
      simp only [Rat.cast_div,Rat.cast_neg,Rat.cast_sub,hu,hv]
      rfl
    rw [show T q=Function.update q i (((-u/(v-u) : ℚ) : ℝ)) by rw [hr]]
    exact rationalVector_update hq i _
  · change f (Function.update q i (-b q/a q))=0
    rw [haff]
    change b q+(-b q/a q)*a q=0
    rw [div_mul_cancel₀ _ haq]
    ring

theorem polynomial_nonzero_near {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p≠0) (x : Fin n → ℝ) (ε : ℝ) (hε : 0<ε) :
    ∃ y : Fin n → ℝ, (∀ i, dist (y i) (x i)<ε) ∧ eval y p≠0 := by
  classical
  by_contra h
  have hz : ∀ y : Fin n → ℝ, (∀ i, dist (y i) (x i)<ε) → eval y p=0 := by
    intro y hy
    by_contra hy0
    exact h ⟨y,hy,hy0⟩
  apply hp
  apply MvPolynomial.funext_set (fun i => Ioo (x i-ε) (x i+ε))
    (fun i => Set.Ioo_infinite (by linarith))
  intro y hy
  rw [map_zero]
  apply hz
  intro i
  have hi := hy i (mem_univ i)
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith [hi.1],by linarith [hi.2]⟩

def coordinatePath {n : ℕ} (x : Option (Fin n) → ℝ)
    (y : Fin n → ℝ) (k : ℕ) : Option (Fin n) → ℝ
  | none => x none
  | some i => if i.val<k then y i else x (some i)

@[simp] theorem coordinatePath_zero {n : ℕ} (x : Option (Fin n) → ℝ)
    (y : Fin n → ℝ) : coordinatePath x y 0=x := by
  funext i
  cases i <;> simp [coordinatePath]

@[simp] theorem coordinatePath_end {n : ℕ} (x : Option (Fin n) → ℝ)
    (y : Fin n → ℝ) : coordinatePath x y n=Option.elim' (x none) y := by
  funext i
  cases i with
  | none => rfl
  | some i => simp [coordinatePath,i.isLt]

theorem coordinatePath_step {n k : ℕ} (x : Option (Fin n) → ℝ)
    (y : Fin n → ℝ) (hk : k<n) :
    coordinatePath x y (k+1) =
      Function.update (coordinatePath x y k) (some ⟨k,hk⟩) (y ⟨k,hk⟩) := by
  funext i
  cases i with
  | none => simp [coordinatePath]
  | some i =>
    by_cases hi : i.val=k
    · have he : i=⟨k,hk⟩ := Fin.ext hi
      subst i
      simp [coordinatePath]
    · have hne : some i≠some (⟨k,hk⟩ : Fin n) := by
        intro h
        exact hi (congrArg Fin.val (Option.some.inj h))
      rw [Function.update_of_ne hne]
      dsimp [coordinatePath]
      have hb : (i.val<k+1) ↔ i.val<k := by omega
      simp only [hb]

theorem coordinatePath_near {n : ℕ} (x : Option (Fin n) → ℝ)
    (y : Fin n → ℝ) (k : ℕ) (ε : ℝ) (hε : 0<ε)
    (hy : ∀ i, dist (y i) (x (some i))<ε) :
    dist (coordinatePath x y k) x<ε := by
  apply (dist_pi_lt_iff hε).mpr
  intro i
  cases i with
  | none => simpa only [coordinatePath,dist_self] using hε
  | some i =>
    dsimp [coordinatePath]
    split_ifs <;> simp_all

/-- Every zero of a nonzero multiaffine fiber is approached by zeros
having a nonzero derivative in one of the affine coordinates. -/
theorem regular_zeros_dense_in_fiber {n : ℕ}
    (f : (Option (Fin n) → ℝ) → ℝ)
    (haff : ∀ i : Fin n, AffineIn f (some i))
    (x : Option (Fin n) → ℝ) (hx : f x=0)
    (p : MvPolynomial (Fin n) ℝ) (hp : p≠0)
    (heval : ∀ y, eval y p=f (Option.elim' (x none) y)) :
    x∈closure {q | f q=0 ∧ ∃ i : Fin n, axisSlope f (some i) q≠0} := by
  classical
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨y,hy,hyp⟩ := polynomial_nonzero_near p hp (fun i=>x (some i)) ε hε
  have hyf : f (coordinatePath x y n)≠0 := by
    rw [coordinatePath_end,← heval]
    exact hyp
  have hex : ∃ k : ℕ, k≤n ∧ f (coordinatePath x y k)≠0 := ⟨n,le_rfl,hyf⟩
  let m := Nat.find hex
  have hm : m≤n ∧ f (coordinatePath x y m)≠0 := Nat.find_spec hex
  have hmpos : 0<m := by
    by_contra h
    have hmzero : m=0 := by omega
    exact hm.2 (by simpa only [hmzero,coordinatePath_zero] using hx)
  have hk : m-1<n := by omega
  have hz : f (coordinatePath x y (m-1))=0 := by
    by_contra h
    have hmin := Nat.find_min' hex (show m-1≤n ∧ f (coordinatePath x y (m-1))≠0 from ⟨by omega,h⟩)
    change m≤m-1 at hmin
    omega
  let i : Fin n := ⟨m-1,hk⟩
  let u := coordinatePath x y (m-1)
  have hslope : axisSlope f (some i) u≠0 := by
    intro hs
    have hstep := coordinatePath_step x y hk
    have hm_eq : m-1+1=m := by omega
    rw [hm_eq] at hstep
    have h1 := haff i u (y i)
    have h0 := haff i u (u (some i))
    rw [Function.update_eq_self] at h0
    have hstep0 : f (Function.update u (some i) (y i))=0 := by
      rw [hs,mul_zero,add_zero] at h1 h0
      exact h1.trans (h0.symm.trans hz)
    apply hm.2
    rw [hstep]
    exact hstep0
  refine ⟨u,⟨hz,i,hslope⟩,?_⟩
  change dist x (coordinatePath x y (m-1)) < ε
  rw [dist_comm]
  exact coordinatePath_near x y (m-1) ε hε hy

theorem rational_zeros_dense_of_multiaffine_fiber {n : ℕ}
    (f : (Option (Fin n) → ℝ) → ℝ) (hc : Continuous f)
    (hrat : ∀ x, RationalVector x → ∃ q : ℚ, (q : ℝ)=f x)
    (haff : ∀ i : Fin n, AffineIn f (some i))
    (x : Option (Fin n) → ℝ) (hx : f x=0)
    (p : MvPolynomial (Fin n) ℝ) (hp : p≠0)
    (heval : ∀ y, eval y p=f (Option.elim' (x none) y)) :
    x∈closure {q | RationalVector q ∧ f q=0} := by
  have hreg := regular_zeros_dense_in_fiber f haff x hx p hp heval
  have hsub : {q | f q=0 ∧ ∃ i : Fin n, axisSlope f (some i) q≠0} ⊆
      closure {q | RationalVector q ∧ f q=0} := by
    rintro q ⟨hq,i,hi⟩
    exact regular_axis_rational_density f hc hrat (some i) (haff i) q hq hi
  have h := closure_mono hsub hreg
  rwa [closure_closure] at h

end Papers.RationalityTen.MultiaffineDensity
