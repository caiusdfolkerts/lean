module

public import PaperVerification.FermionEndpointHomogeneity
public import Mathlib.Data.List.Forall2
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# The complete list of endpoint degrees

The lists below are paired with the actual generators, in their actual order.
Their length is the number of polynomial variables. Their degree product is
the product of the path bounds, proved by a height-potential identity rather
than by assuming a matching of the up-steps and down-steps.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Endpoint

open scoped BigOperators

/-- The exact degrees of the one or two relations at an index. -/
def stepDegrees (W s h l r : ℕ) : Mark → List ℕ
  | .unmarked => []
  | .theta => [r + W * h]
  | .xi => [l + W * h]
  | .double => [W * h, W * (s + h - 1)]

def allDegrees (W s : ℕ) (height l r : ℕ → ℕ) (marks : ℕ → Mark) : ℕ → List ℕ
  | 0 => []
  | k + 1 => allDegrees W s height l r marks k ++
      stepDegrees W s (height k) (l k) (r k) (marks k)

def generatorDegrees (W s : ℕ) (height l r : ℕ → ℕ) (marks : ℕ → Mark) (n : ℕ) : List ℕ :=
  allDegrees W s height l r marks n ++
    List.ofFn (fun j : Fin (height n) ↦ W * (s + height n - 1 - (j : ℕ)))

/-- The polynomial bound multiplied by the integer weight of its variable. -/
def localBoundDegree (W s h l r : ℕ) : Mark → ℕ
  | .unmarked => W * (s + h)
  | .theta => W * h + r
  | .xi => W * h + l
  | .double => W * h

def heightPotential (W s h : ℕ) : ℕ := W ^ h * s.ascFactorial h

theorem step_degree_product (W s h h' l r : ℕ) (m : Mark)
    (hstep : HeightStep m h h') :
    (stepDegrees W s h l r m).prod * heightPotential W s h' =
      localBoundDegree W s h l r m * heightPotential W s h := by
  cases m with
  | unmarked =>
    have hh : h' = h + 1 := hstep
    subst h'
    simp only [stepDegrees, List.prod_nil, one_mul, localBoundDegree,
      heightPotential, pow_succ, Nat.ascFactorial_succ]
    ring
  | theta =>
    have hh : h' = h := hstep
    subst h'
    simp only [stepDegrees, List.prod_cons, List.prod_nil, mul_one, localBoundDegree]
    rw [Nat.add_comm r]
  | xi =>
    have hh : h' = h := hstep
    subst h'
    simp only [stepDegrees, List.prod_cons, List.prod_nil, mul_one, localBoundDegree]
    rw [Nat.add_comm l]
  | double =>
    have hh : h = h' + 1 := hstep
    subst h
    simp only [stepDegrees, List.prod_cons, List.prod_nil, mul_one, localBoundDegree,
      heightPotential, pow_succ, Nat.ascFactorial_succ]
    rw [show s + (h' + 1) - 1 = s + h' by omega]
    ring

theorem all_degree_product (W s : ℕ) (height l r : ℕ → ℕ) (marks : ℕ → Mark)
    (hzero : height 0 = 0) (n : ℕ)
    (hsteps : ∀ j < n, HeightStep (marks j) (height j) (height (j + 1))) :
    (allDegrees W s height l r marks n).prod * heightPotential W s (height n) =
      ∏ i : Fin n, localBoundDegree W s (height i) (l i) (r i) (marks i) := by
  revert hsteps
  induction n with
  | zero => intro hsteps; simp [allDegrees, heightPotential, hzero]
  | succ n ih =>
    intro hsteps
    rw [allDegrees, List.prod_append, Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [mul_assoc, step_degree_product W s (height n) (height (n + 1))
      (l n) (r n) (marks n) (hsteps n (Nat.lt_succ_self n))]
    calc
      _ = ((allDegrees W s height l r marks n).prod * heightPotential W s (height n)) *
          localBoundDegree W s (height n) (l n) (r n) (marks n) := by ac_rfl
      _ = _ := by rw [ih (fun j hj ↦ hsteps j (Nat.lt_succ_of_lt hj))]

theorem terminal_degree_product (W s c : ℕ) :
    (List.ofFn (fun j : Fin c ↦ W * (s + c - 1 - (j : ℕ)))).prod =
      heightPotential W s c := by
  rw [List.prod_ofFn]
  calc
    _ = ∏ j : Fin c, W * (s + (Fin.revPerm j : ℕ)) := by
      apply Finset.prod_congr rfl
      intro j hj
      congr 1
      simp only [Fin.revPerm_apply, Fin.val_rev]
      have := j.isLt
      omega
    _ = ∏ j : Fin c, W * (s + (j : ℕ)) :=
      Equiv.prod_comp Fin.revPerm (fun j : Fin c ↦ W * (s + (j : ℕ)))
    _ = heightPotential W s c := by
      rw [Finset.prod_mul_distrib, Fin.prod_const, Fin.prod_univ_eq_prod_range,
        ← Nat.ascFactorial_eq_prod_range]
      rfl

/-- The complete degree product equals the complete path-bound product,
for arbitrary path length and arbitrary two-colour choices. -/
theorem generator_degree_product (W s : ℕ) (height l r : ℕ → ℕ) (marks : ℕ → Mark)
    (hzero : height 0 = 0) (n : ℕ)
    (hsteps : ∀ j < n, HeightStep (marks j) (height j) (height (j + 1))) :
    (generatorDegrees W s height l r marks n).prod =
      ∏ i : Fin n, localBoundDegree W s (height i) (l i) (r i) (marks i) := by
  rw [generatorDegrees, List.prod_append, terminal_degree_product]
  exact all_degree_product W s height l r marks hzero n hsteps

theorem step_degrees_positive (W s h h' l r : ℕ) (m : Mark)
    (hW : 0 < W) (hs : 0 < s) (hstep : HeightStep m h h')
    (hbound : 0 < localBoundDegree W s h l r m) :
    ∀ d ∈ stepDegrees W s h l r m, 0 < d := by
  cases m with
  | unmarked => simp [stepDegrees]
  | theta => simpa [stepDegrees, localBoundDegree, Nat.add_comm] using hbound
  | xi => simpa [stepDegrees, localBoundDegree, Nat.add_comm] using hbound
  | double =>
    have hh : h = h' + 1 := hstep
    have hsecond : 0 < W * (s + h - 1) := Nat.mul_pos hW (by omega)
    intro d hd
    simp only [stepDegrees, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact hbound
    · exact hsecond

theorem all_degrees_positive (W s : ℕ) (height l r : ℕ → ℕ) (marks : ℕ → Mark)
    (hW : 0 < W) (hs : 0 < s) (n : ℕ)
    (hsteps : ∀ j < n, HeightStep (marks j) (height j) (height (j + 1)))
    (hbound : ∀ j < n, 0 < localBoundDegree W s (height j) (l j) (r j) (marks j)) :
    ∀ d ∈ allDegrees W s height l r marks n, 0 < d := by
  revert hsteps hbound
  induction n with
  | zero => simp [allDegrees]
  | succ n ih =>
    intro hsteps hbound d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact ih (fun j hj ↦ hsteps j (Nat.lt_succ_of_lt hj))
        (fun j hj ↦ hbound j (Nat.lt_succ_of_lt hj)) d hd
    · exact step_degrees_positive W s (height n) (height (n + 1)) (l n) (r n) (marks n)
        hW hs (hsteps n (Nat.lt_succ_self n)) (hbound n (Nat.lt_succ_self n)) d hd

theorem generator_degrees_positive (W s : ℕ) (height l r : ℕ → ℕ) (marks : ℕ → Mark)
    (hW : 0 < W) (hs : 0 < s) (n : ℕ)
    (hsteps : ∀ j < n, HeightStep (marks j) (height j) (height (j + 1)))
    (hbound : ∀ j < n, 0 < localBoundDegree W s (height j) (l j) (r j) (marks j)) :
    ∀ d ∈ generatorDegrees W s height l r marks n, 0 < d := by
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · exact all_degrees_positive W s height l r marks hW hs n hsteps hbound d hd
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hd
    exact Nat.mul_pos hW (by have := j.isLt; omega)

section LiteralGenerators

variable {R : Type*} [CommRing R]

/-- The relation count and the current path height sum to the prefix length. -/
theorem allRelations_length_add_height (data : ℕ → Datum R) (height : ℕ → ℕ)
    (hzero : height 0 = 0) (n : ℕ)
    (hsteps : ∀ j < n, HeightStep (data j).mark (height j) (height (j + 1))) :
    (allRelations data n).length + height n = n := by
  revert hsteps
  induction n with
  | zero => intro hsteps; simp [allRelations, hzero]
  | succ n ih =>
    intro hsteps
    have hp := ih (fun j hj ↦ hsteps j (Nat.lt_succ_of_lt hj))
    have hs := hsteps n (Nat.lt_succ_self n)
    rw [allRelations, List.length_append]
    cases hm : (data n).mark <;>
      simp only [relations, hm, HeightStep, List.length_nil, List.length_cons] at hs ⊢ <;>
      omega

/-- There are exactly `n` actual endpoint generators. -/
theorem generators_length (data : ℕ → Datum R) (height : ℕ → ℕ)
    (hzero : height 0 = 0) (n : ℕ)
    (hsteps : ∀ j < n, HeightStep (data j).mark (height j) (height (j + 1))) :
    (generators data n (height n)).length = n := by
  rw [generators, List.length_append, List.length_ofFn]
  exact allRelations_length_add_height data height hzero n hsteps

end LiteralGenerators

section Homogeneity

variable {K ι : Type*} [Field K]

local notation "P" => MvPolynomial ι K

theorem relations_homogeneous (w : ι → ℕ) (W s h h' l r : ℕ) (hs : 0 < s)
    (T : State P) (d : Datum P)
    (hy : d.node.IsWeightedHomogeneous w W)
    (hγ : d.weight.IsWeightedHomogeneous w (W * s))
    (hl : d.leftFactor.IsWeightedHomogeneous w l)
    (hr : d.rightFactor.IsWeightedHomogeneous w r)
    (hA : HomogeneousPolynomial w W h T.A)
    (hB : HomogeneousPolynomial w W (s + h - 1) T.B)
    (hstep : HeightStep d.mark h h') :
    List.Forall₂ (fun p e ↦ p.IsWeightedHomogeneous w e)
      (relations T d) (stepDegrees W s h l r d.mark) := by
  cases hm : d.mark with
  | unmarked =>
    simp only [relations, stepDegrees, hm]
    exact .nil
  | theta =>
    simp only [relations, stepDegrees, hm]
    exact .cons (hr.mul (hA.eval d.node hy)) .nil
  | xi =>
    simp only [relations, stepDegrees, hm]
    exact .cons (hl.mul (hA.eval d.node hy)) .nil
  | double =>
    have hh : h = h' + 1 := by simpa only [HeightStep, hm] using hstep
    have hmiddle : HomogeneousPolynomial w W (s + h - 1)
        (T.B - Polynomial.C d.weight * quotient T.A d.node) := by
      apply hB.sub
      convert (hA.quotient d.node hy).C_mul d.weight hγ using 1 <;> congr 1 <;> omega
    simp only [relations, stepDegrees, hm]
    exact .cons (hA.eval d.node hy) (.cons (hmiddle.eval d.node hy) .nil)

theorem allRelations_homogeneous (w : ι → ℕ) (W s : ℕ) (hs : 0 < s)
    (data : ℕ → Datum P) (height l r : ℕ → ℕ) (hzero : height 0 = 0) (n : ℕ)
    (hy : ∀ j < n, (data j).node.IsWeightedHomogeneous w W)
    (hγ : ∀ j < n, (data j).weight.IsWeightedHomogeneous w (W * s))
    (hl : ∀ j < n, (data j).leftFactor.IsWeightedHomogeneous w (l j))
    (hr : ∀ j < n, (data j).rightFactor.IsWeightedHomogeneous w (r j))
    (hsteps : ∀ j < n, HeightStep (data j).mark (height j) (height (j + 1))) :
    List.Forall₂ (fun p e ↦ p.IsWeightedHomogeneous w e) (allRelations data n)
      (allDegrees W s height l r (fun j ↦ (data j).mark) n) := by
  revert hy hγ hl hr hsteps
  induction n with
  | zero => intro hy hγ hl hr hsteps; exact .nil
  | succ n ih =>
    intro hy hγ hl hr hsteps
    have hpre := ih
      (fun j hj ↦ hy j (Nat.lt_succ_of_lt hj))
      (fun j hj ↦ hγ j (Nat.lt_succ_of_lt hj))
      (fun j hj ↦ hl j (Nat.lt_succ_of_lt hj))
      (fun j hj ↦ hr j (Nat.lt_succ_of_lt hj))
      (fun j hj ↦ hsteps j (Nat.lt_succ_of_lt hj))
    obtain ⟨hA, hB⟩ := run_homogeneous w W s hs data height hzero n
      (fun j hj ↦ hy j (Nat.lt_succ_of_lt hj))
      (fun j hj ↦ hγ j (Nat.lt_succ_of_lt hj))
      (fun j hj ↦ hsteps j (Nat.lt_succ_of_lt hj))
    exact List.rel_append hpre
      (relations_homogeneous w W s (height n) (height (n + 1)) (l n) (r n) hs
        (run data n) (data n) (hy n (Nat.lt_succ_self n)) (hγ n (Nat.lt_succ_self n))
        (hl n (Nat.lt_succ_self n)) (hr n (Nat.lt_succ_self n)) hA hB
        (hsteps n (Nat.lt_succ_self n)))

theorem generators_homogeneous (w : ι → ℕ) (W s : ℕ) (hs : 0 < s)
    (data : ℕ → Datum P) (height l r : ℕ → ℕ) (hzero : height 0 = 0) (n : ℕ)
    (hy : ∀ j < n, (data j).node.IsWeightedHomogeneous w W)
    (hγ : ∀ j < n, (data j).weight.IsWeightedHomogeneous w (W * s))
    (hl : ∀ j < n, (data j).leftFactor.IsWeightedHomogeneous w (l j))
    (hr : ∀ j < n, (data j).rightFactor.IsWeightedHomogeneous w (r j))
    (hsteps : ∀ j < n, HeightStep (data j).mark (height j) (height (j + 1))) :
    List.Forall₂ (fun p e ↦ p.IsWeightedHomogeneous w e) (generators data n (height n))
      (generatorDegrees W s height l r (fun j ↦ (data j).mark) n) := by
  apply List.rel_append
  · exact allRelations_homogeneous w W s hs data height l r hzero n hy hγ hl hr hsteps
  · apply List.forall₂_of_length_eq_of_get (by simp)
    intro j hj₁ hj₂
    have hj : j < height n := by simpa only [List.length_ofFn] using hj₁
    have hB := (run_homogeneous w W s hs data height hzero n hy hγ hsteps).2
    simpa only [List.get_ofFn, Fin.cast_mk] using hB.1 j (by omega)

end Homogeneity

end PaperVerification.Fermion.Endpoint
