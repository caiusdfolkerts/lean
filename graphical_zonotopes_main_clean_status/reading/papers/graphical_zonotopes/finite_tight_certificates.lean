module

public import Papers.GraphicalZonotopes.GraphicalCone
public import Papers.GraphicalZonotopes.Lattice
public import Mathlib.Data.Matrix.Basic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace FiniteTight
open Finset
open scoped BigOperators Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A row is either an actual value coordinate or an actual elemental
difference. It cannot contain an arbitrary unverified linear assertion. -/
inductive Row (V : Type*) where
  | value (S : Finset V)
  | elemental (u v : V) (S : Finset V)
  deriving DecidableEq

def Row.coefficient (r : Row V) (C : Finset V) : ℚ :=
  match r with
  | .value S => if C=S then 1 else 0
  | .elemental u v S =>
      (if C=insert u (insert v S) then 1 else 0)-
      (if C=insert u S then 1 else 0)-
      (if C=insert v S then 1 else 0)+(if C=S then 1 else 0)

def Row.eval (r : Row V) (f : SetFunction V) : ℝ :=
  match r with
  | .value S => f S
  | .elemental u v S => delta f u v S

def integerDelta (z : Finset V → ℤ) (u v : V) (S : Finset V) : ℤ :=
  z (insert u (insert v S))-z (insert u S)-z (insert v S)+z S

def realFunction (z : Finset V → ℤ) : SetFunction V := fun S => (z S : ℝ)

theorem delta_realFunction (z : Finset V → ℤ) (u v : V) (S : Finset V) :
    delta (realFunction z) u v S=(integerDelta z u v S : ℝ) := by
  simp only [delta,realFunction,integerDelta,Int.cast_sub,Int.cast_add]

theorem Row.eval_eq_sum (r : Row V) (f : SetFunction V) :
    r.eval f=∑ C : Finset V,(r.coefficient C : ℝ)*f C := by
  cases r with
  | value S => simp [Row.eval,Row.coefficient,apply_ite,ite_mul]
  | elemental u v S =>
    have hcast (p : Prop) [Decidable p] :
        ((↑(if p then (1 : ℚ) else 0)) : ℝ) = if p then 1 else 0 := by
      split_ifs <;> norm_num
    simp only [Row.eval,Row.coefficient,delta,Rat.cast_add,Rat.cast_sub,hcast,
      sub_mul,add_mul,sum_sub_distrib,sum_add_distrib,ite_mul,one_mul,zero_mul]
    simp <;> ring

@[simp] theorem Row.eval_sub (r : Row V) (f g : SetFunction V) :
    r.eval (f-g)=r.eval f-r.eval g := by cases r <;> simp [Row.eval]

@[simp] theorem Row.eval_smul (r : Row V) (c : ℝ) (f : SetFunction V) :
    r.eval (c • f)=c*r.eval f := by cases r <;> simp [Row.eval]

/-- Each nonpivot certificate row is justified by translation normalization
or by one of the literal tight elemental equations of the proposed function. -/
def Row.valid (z : Finset V → ℤ) (r : Row V) : Prop :=
  match r with
  | .value S => S=∅ ∨ ∃ v : V,S={v}
  | .elemental u v S => u≠v ∧ u∉S ∧ v∉S ∧ integerDelta z u v S=0

instance (z : Finset V → ℤ) (r : Row V) : Decidable (r.valid z) := by
  cases r <;> unfold Row.valid <;> infer_instance

theorem Row.eval_zero_of_valid {z : Finset V → ℤ} {r : Row V}
    (hr : r.valid z) (f : SetFunction V) (hfn : TranslationNormalized f)
    (hzero : ∀ u v,u≠v → ∀ S : Finset V,u∉S → v∉S →
      delta (realFunction z) u v S=0 → delta f u v S=0) : r.eval f=0 := by
  cases r with
  | value S =>
    rcases hr with rfl | ⟨v,rfl⟩
    · exact hfn.1
    · exact hfn.2 v
  | elemental u v S =>
    exact hzero u v hr.1 S hr.2.1 hr.2.2.1 (by
      rw [delta_realFunction,hr.2.2.2]
      norm_num)

theorem realFunction_normalized {z : Finset V → ℤ}
    (h0 : z ∅=0) (h1 : ∀ v,z {v}=0) : TranslationNormalized (realFunction z) := by
  exact ⟨by simp [Normalized,realFunction,h0],fun v => by simp [realFunction,h1 v]⟩

theorem realFunction_supermodular {z : Finset V → ℤ}
    (hz : ∀ u v,u≠v → ∀ S : Finset V,u∉S → v∉S →
      integerDelta z u v S=0 ∨ integerDelta z u v S=1) : Supermodular (realFunction z) := by
  apply ElementallyNonnegative.supermodular
  intro u v huv S hu hv
  rw [delta_realFunction]
  rcases hz u v huv S hu hv with he | he <;> rw [he] <;> norm_num

theorem realFunction_integerValued (z : Finset V → ℤ) : IntegerValued (realFunction z) :=
  fun S => ⟨z S,rfl⟩

theorem pair_sum_of_integer_differences (G : SimpleGraph V) [DecidableRel G.Adj]
    (z w : Finset V → ℤ) (hz0 : z ∅=0) (hz1 : ∀ v,z {v}=0)
    (hw0 : w ∅=0) (hw1 : ∀ v,w {v}=0)
    (hdelta : ∀ u v,u≠v → ∀ S : Finset V,u∉S → v∉S →
      integerDelta z u v S+integerDelta w u v S=if G.Adj u v then 1 else 0) :
    realFunction z+realFunction w=graphFunction G := by
  have hzn := realFunction_normalized hz0 hz1
  have hwn := realFunction_normalized hw0 hw1
  have hgn := graphFunction_translationNormalized G
  apply sub_eq_zero.mp
  apply normalized_zero_elemental_eq_zero
  · refine ⟨?_,?_⟩
    · change realFunction z ∅+realFunction w ∅-graphFunction G ∅=0
      rw [hzn.1,hwn.1,hgn.1]
      ring
    · intro v
      change realFunction z {v}+realFunction w {v}-graphFunction G {v}=0
      rw [hzn.2 v,hwn.2 v,hgn.2 v]
      ring
  · intro u v huv S hu hv
    rw [delta_sub,delta_add,delta_realFunction,delta_realFunction,
      graphFunction_delta G huv hu hv]
    have h : (integerDelta z u v S : ℝ)+(integerDelta w u v S : ℝ)=
        if G.Adj u v then 1 else 0 := by exact_mod_cast hdelta u v huv S hu hv
    by_cases he : G.Adj u v
    · simpa only [if_pos he] using sub_eq_zero.mpr h
    · simpa only [if_neg he] using sub_eq_zero.mpr h

def matrix {k : ℕ} (rows : Fin (k+1) → Row V) : Matrix (Fin (k+1)) (Finset V) ℚ :=
  fun i C => (rows i).coefficient C

/-- An exact rational left inverse proves the full real tight kernel is a
line. The certificate entries are checked identities; all variables of the
kernel theorem remain arbitrary real set functions. -/
theorem tight_kernel_of_left_inverse {k : ℕ} (z : Finset V → ℤ)
    (rows : Fin (k+1) → Row V) (B : Matrix (Finset V) (Fin (k+1)) ℚ)
    (pivot : Finset V) (hpivot : z pivot=1) (hrow0 : rows 0=.value pivot)
    (hvalid : ∀ i : Fin (k+1),i≠0 → (rows i).valid z)
    (hinverse : B*matrix rows=1) (hn : TranslationNormalized (realFunction z))
    (f : SetFunction V) (hfn : TranslationNormalized f)
    (hzero : ∀ u v,u≠v → ∀ S : Finset V,u∉S → v∉S →
      delta (realFunction z) u v S=0 → delta f u v S=0) :
    ∃ t : ℝ,f=t • realFunction z := by
  let A' : Matrix (Fin (k+1)) (Finset V) ℝ := fun i C => (matrix rows i C : ℝ)
  let B' : Matrix (Finset V) (Fin (k+1)) ℝ := fun C i => (B C i : ℝ)
  have hBA : B'*A'=1 := by
    ext C D
    have h : (∑ i : Fin (k+1),B C i*matrix rows i D)=if C=D then 1 else 0 := by
      simpa only [Matrix.mul_apply,Matrix.one_apply] using congrFun (congrFun hinverse C) D
    have hc := congrArg (fun q : ℚ => (q : ℝ)) h
    simp only [Rat.cast_sum, Rat.cast_mul, apply_ite, Rat.cast_one, Rat.cast_zero] at hc
    change (∑ i : Fin (k+1),(B C i : ℝ)*(matrix rows i D : ℝ)) = if C=D then 1 else 0
    by_cases he : C=D
    · simpa only [if_pos he] using hc
    · simpa only [if_neg he] using hc

  let w : SetFunction V := f-f pivot • realFunction z
  have hw : A' *ᵥ w=0 := by
    funext i
    change (∑ C : Finset V,(matrix rows i C : ℝ)*w C)=0
    rw [show (∑ C : Finset V,(matrix rows i C : ℝ)*w C)=(rows i).eval w from
      (Row.eval_eq_sum (rows i) w).symm]
    by_cases hi : i=0
    · subst i
      rw [hrow0]
      change f pivot-f pivot*(z pivot : ℝ)=0
      rw [hpivot]
      norm_num
    · rw [show w=f-f pivot • realFunction z from rfl,Row.eval_sub,Row.eval_smul,
        Row.eval_zero_of_valid (hvalid i hi) f hfn hzero,
        Row.eval_zero_of_valid (hvalid i hi) (realFunction z) hn
          (fun _ _ _ _ _ _ he => he)]
      ring
  have h := congrArg (fun v => B' *ᵥ v) hw
  rw [Matrix.mulVec_mulVec,hBA,Matrix.one_mulVec,Matrix.mulVec_zero] at h
  exact ⟨f pivot,sub_eq_zero.mp h⟩

theorem extreme_of_left_inverse {k : ℕ} (z : Finset V → ℤ)
    (rows : Fin (k+1) → Row V) (B : Matrix (Finset V) (Fin (k+1)) ℚ)
    (pivot : Finset V) (hpivot : z pivot=1) (hrow0 : rows 0=.value pivot)
    (hvalid : ∀ i : Fin (k+1),i≠0 → (rows i).valid z)
    (hinverse : B*matrix rows=1) (h0 : z ∅=0) (h1 : ∀ v,z {v}=0)
    (hbool : ∀ u v,u≠v → ∀ S : Finset V,u∉S → v∉S →
      integerDelta z u v S=0 ∨ integerDelta z u v S=1) :
    ExtremeSupermodular (realFunction z) := by
  have hn := realFunction_normalized h0 h1
  apply extremeSupermodular_of_tightEquations hn (realFunction_supermodular hbool)
  · intro he
    have h := congrFun he pivot
    simp [realFunction,hpivot] at h
  · exact tight_kernel_of_left_inverse z rows B pivot hpivot hrow0 hvalid hinverse hn


/-- A checked real kernel certificate for the literal normalized/tight rows
is sufficient; no matrix computation or floating-point rank oracle is used. -/
theorem tight_kernel_of_row_kernel {k : ℕ} (z : Finset V → ℤ)
    (rows : Fin (k+1) → Row V) (pivot : Finset V)
    (hpivot : z pivot=1) (hrow0 : rows 0=.value pivot)
    (hvalid : ∀ i : Fin (k+1),i≠0 → (rows i).valid z)
    (hkernel : ∀ w : SetFunction V,(∀ i,(rows i).eval w=0) → w=0)
    (hn : TranslationNormalized (realFunction z))
    (f : SetFunction V) (hfn : TranslationNormalized f)
    (hzero : ∀ u v,u≠v → ∀ S : Finset V,u∉S → v∉S →
      delta (realFunction z) u v S=0 → delta f u v S=0) :
    ∃ t : ℝ,f=t • realFunction z := by
  let w : SetFunction V := f-f pivot • realFunction z
  have hw : ∀ i,(rows i).eval w=0 := by
    intro i
    by_cases hi : i=0
    · subst i
      rw [hrow0]
      change f pivot-f pivot*(z pivot : ℝ)=0
      rw [hpivot]
      norm_num
    · rw [show w=f-f pivot • realFunction z from rfl,Row.eval_sub,Row.eval_smul,
        Row.eval_zero_of_valid (hvalid i hi) f hfn hzero,
        Row.eval_zero_of_valid (hvalid i hi) (realFunction z) hn
          (fun _ _ _ _ _ _ he => he)]
      ring
  exact ⟨f pivot,sub_eq_zero.mp (hkernel w hw)⟩

theorem extreme_of_row_kernel {k : ℕ} (z : Finset V → ℤ)
    (rows : Fin (k+1) → Row V) (pivot : Finset V)
    (hpivot : z pivot=1) (hrow0 : rows 0=.value pivot)
    (hvalid : ∀ i : Fin (k+1),i≠0 → (rows i).valid z)
    (hkernel : ∀ w : SetFunction V,(∀ i,(rows i).eval w=0) → w=0)
    (h0 : z ∅=0) (h1 : ∀ v,z {v}=0)
    (hbool : ∀ u v,u≠v → ∀ S : Finset V,u∉S → v∉S →
      integerDelta z u v S=0 ∨ integerDelta z u v S=1) :
    ExtremeSupermodular (realFunction z) := by
  have hn := realFunction_normalized h0 h1
  apply extremeSupermodular_of_tightEquations hn (realFunction_supermodular hbool)
  · intro he
    have h := congrFun he pivot
    simp [realFunction,hpivot] at h
  · exact tight_kernel_of_row_kernel z rows pivot hpivot hrow0 hvalid hkernel hn

end FiniteTight
end GraphicalZonotopes
