module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Tauto
public import Aesop

@[expose] public section

/-! Real set functions, elemental differences, and their genuine lower base polytopes. -/

noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev SetFunction (V : Type*) := Finset V → ℝ

def Supermodular (z : SetFunction V) : Prop :=
  ∀ A B, z A + z B ≤ z (A ∪ B) + z (A ∩ B)

def Normalized (z : SetFunction V) : Prop := z ∅ = 0

def TranslationNormalized (z : SetFunction V) : Prop :=
  Normalized z ∧ ∀ v, z {v} = 0

def delta (z : SetFunction V) (u v : V) (S : Finset V) : ℝ :=
  z (insert u (insert v S)) - z (insert u S) - z (insert v S) + z S

def ElementallyNonnegative (z : SetFunction V) : Prop :=
  ∀ u v, u ≠ v → ∀ S, u ∉ S → v ∉ S → 0 ≤ delta z u v S

def subsetSum (x : V → ℝ) (S : Finset V) : ℝ := ∑ v ∈ S, x v

def basePolytope (z : SetFunction V) : Set (V → ℝ) :=
  {x | subsetSum x univ = z univ ∧ ∀ S, z S ≤ subsetSum x S}

@[simp] theorem subsetSum_empty (x : V → ℝ) : subsetSum x ∅ = 0 := by
  simp [subsetSum]

@[simp] theorem subsetSum_insert {x : V → ℝ} {v : V} {S : Finset V} (hv : v ∉ S) :
    subsetSum x (insert v S) = x v + subsetSum x S := by simp [subsetSum, hv]

@[simp] theorem subsetSum_add (x y : V → ℝ) (S : Finset V) :
    subsetSum (x + y) S = subsetSum x S + subsetSum y S := by
  simp [subsetSum, sum_add_distrib]

@[simp] theorem subsetSum_smul (a : ℝ) (x : V → ℝ) (S : Finset V) :
    subsetSum (a • x) S = a * subsetSum x S := by simp [subsetSum, mul_sum]

theorem Supermodular.marginal {z : SetFunction V} (hz : Supermodular z)
    {A B : Finset V} (hAB : A ⊆ B) {v : V} (hv : v ∉ B) :
    z (insert v A) - z A ≤ z (insert v B) - z B := by
  have hu : insert v A ∪ B = insert v B := by ext x; simp; aesop
  have hi : insert v A ∩ B = A := by ext x; simp; aesop
  have h := hz (insert v A) B
  rw [hu, hi] at h
  linarith

theorem Supermodular.elemental {z : SetFunction V} (hz : Supermodular z) :
    ElementallyNonnegative z := by
  intro u v huv S hu hv
  have h := hz.marginal (subset_insert v S) (show u ∉ insert v S by simp [huv, hu])
  dsimp [delta]
  linarith

theorem ElementallyNonnegative.marginal {z : SetFunction V}
    (hz : ElementallyNonnegative z) {A B : Finset V} (hAB : A ⊆ B)
    {v : V} (hv : v ∉ B) :
    z (insert v A) - z A ≤ z (insert v B) - z B := by
  classical
  have aux : ∀ D : Finset V, v ∉ A ∪ D →
      z (insert v A) - z A ≤ z (insert v (A ∪ D)) - z (A ∪ D) := by
    intro D
    induction D using Finset.induction_on with
    | empty => simp
    | @insert b D hb ih =>
      intro hvAD
      rw [union_insert] at hvAD ⊢
      have hvD : v ∉ A ∪ D := fun h => hvAD (mem_insert_of_mem h)
      have hvb : v ≠ b := by intro h; subst v; exact hvAD (mem_insert_self _ _)
      by_cases hbAD : b ∈ A ∪ D
      · simpa [insert_eq_of_mem hbAD] using ih hvD
      · have h1 := ih hvD
        have h2 := hz v b hvb (A ∪ D) hvD hbAD
        dsimp [delta] at h2
        linarith
  have he : A ∪ (B \ A) = B := union_sdiff_of_subset hAB
  simpa [he] using aux (B \ A) (by simpa [he] using hv)

theorem basePolytope_convex (z : SetFunction V) : Convex ℝ (basePolytope z) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_⟩
  · rw [subsetSum_add, subsetSum_smul, subsetSum_smul, hx.1, hy.1,
      ← add_mul, hab, one_mul]
  · intro S
    rw [subsetSum_add, subsetSum_smul, subsetSum_smul]
    have h1 := mul_le_mul_of_nonneg_left (hx.2 S) ha
    have h2 := mul_le_mul_of_nonneg_left (hy.2 S) hb
    have he : a * z S + b * z S = z S := by rw [← add_mul, hab, one_mul]
    linarith

def orderPrefix {n : ℕ} (e : Fin n ≃ V) (j : ℕ) : Finset V :=
  univ.filter (fun v => (e.symm v).val < j)

@[simp] theorem orderPrefix_zero {n : ℕ} (e : Fin n ≃ V) : orderPrefix e 0 = ∅ := by
  ext v; simp [orderPrefix]

@[simp] theorem orderPrefix_full {n : ℕ} (e : Fin n ≃ V) : orderPrefix e n = univ := by
  ext v; simp [orderPrefix, (e.symm v).isLt]

theorem orderPrefix_mono {n : ℕ} (e : Fin n ≃ V) : Monotone (orderPrefix e) := by
  intro j k hjk v hv
  exact mem_filter.mpr ⟨mem_univ _, lt_of_lt_of_le (mem_filter.mp hv).2 hjk⟩

@[simp] theorem not_mem_orderPrefix {n : ℕ} (e : Fin n ≃ V) (j : Fin n) :
    e j ∉ orderPrefix e j.val := by simp [orderPrefix]

theorem orderPrefix_succ {n : ℕ} (e : Fin n ≃ V) (j : Fin n) :
    orderPrefix e (j.val + 1) = insert (e j) (orderPrefix e j.val) := by
  ext v
  simp only [orderPrefix, mem_filter, mem_univ, true_and, mem_insert]
  constructor
  · intro h
    by_cases he : (e.symm v).val = j.val
    · left
      have hfin : e.symm v = j := Fin.ext he
      simpa using congrArg e hfin
    · right; omega
  · rintro (rfl | h)
    · simp
    · omega

def greedyPoint {n : ℕ} (z : SetFunction V) (e : Fin n ≃ V) (v : V) : ℝ :=
  z (orderPrefix e ((e.symm v).val + 1)) - z (orderPrefix e (e.symm v).val)

@[simp] theorem greedyPoint_apply {n : ℕ} (z : SetFunction V) (e : Fin n ≃ V)
    (j : Fin n) :
    greedyPoint z e (e j) = z (insert (e j) (orderPrefix e j.val)) -
      z (orderPrefix e j.val) := by simp [greedyPoint, orderPrefix_succ]

theorem greedyPoint_prefix {n : ℕ} (z : SetFunction V) (hz : Normalized z)
    (e : Fin n ≃ V) (j : ℕ) (hj : j ≤ n) :
    subsetSum (greedyPoint z e) (orderPrefix e j) = z (orderPrefix e j) := by
  induction j with
  | zero => simpa [Normalized] using hz.symm
  | succ j ih =>
    have hjn : j < n := by omega
    rw [orderPrefix_succ e ⟨j, hjn⟩, subsetSum_insert (not_mem_orderPrefix e _),
      greedyPoint_apply, ih (by omega)]
    ring

theorem greedyPoint_subset_prefix {n : ℕ} {z : SetFunction V} (hz : Normalized z)
    (hs : Supermodular z) (e : Fin n ≃ V) (S : Finset V) (j : ℕ) (hj : j ≤ n) :
    z (S ∩ orderPrefix e j) ≤ subsetSum (greedyPoint z e) (S ∩ orderPrefix e j) := by
  induction j with
  | zero => simp [Normalized] at hz; simpa using le_of_eq hz
  | succ j ih =>
    have hjn : j < n := by omega
    let v := e ⟨j, hjn⟩
    have hvP : v ∉ orderPrefix e j := not_mem_orderPrefix e _
    rw [orderPrefix_succ e ⟨j, hjn⟩]
    by_cases hvS : v ∈ S
    · have he : S ∩ insert v (orderPrefix e j) = insert v (S ∩ orderPrefix e j) := by
        ext x; simp; aesop
      rw [he, subsetSum_insert (by simp [hvP])]
      have h1 := hs.marginal (inter_subset_right : S ∩ orderPrefix e j ⊆ _) hvP
      have h2 := ih (by omega)
      have h3 : greedyPoint z e v = z (insert v (orderPrefix e j)) - z (orderPrefix e j) :=
        greedyPoint_apply z e ⟨j, hjn⟩
      linarith
    · have he : S ∩ insert v (orderPrefix e j) = S ∩ orderPrefix e j := by
        ext x; simp; aesop
      rw [he]
      exact ih (by omega)

theorem greedyPoint_mem_basePolytope {n : ℕ} {z : SetFunction V}
    (hz : Normalized z) (hs : Supermodular z) (e : Fin n ≃ V) :
    greedyPoint z e ∈ basePolytope z := by
  refine ⟨?_, ?_⟩
  · simpa using greedyPoint_prefix z hz e n le_rfl
  · intro S
    simpa using greedyPoint_subset_prefix hz hs e S n le_rfl

theorem basePolytope_nonempty {z : SetFunction V} (hz : Normalized z)
    (hs : Supermodular z) : (basePolytope z).Nonempty :=
  ⟨_, greedyPoint_mem_basePolytope hz hs (Fintype.equivFin V).symm⟩

end GraphicalZonotopes
