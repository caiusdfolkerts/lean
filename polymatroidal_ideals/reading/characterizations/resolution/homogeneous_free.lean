import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Common
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! # Homogeneous maps and lifts between genuine finite free polynomial modules -/

noncomputable section
local instance (priority := 2000) classicalBasisDecidableEqHomogeneousFree (α : Type*) [Fintype α] : DecidableEq α := Classical.decEq α
namespace Characterizations.Resolution
open Classical Finset MvPolynomial
universe u v w
variable {V k : Type u} {J : Type v} {L : Type w} [CommRing k] [Fintype J] [Fintype L]

abbrev Polynomial := MvPolynomial V k
abbrev Free (J : Type v) := J → Polynomial (V := V) (k := k)

def IsHomogeneousVector (x : Free (V := V) (k := k) J) (d : ℕ) : Prop :=
  ∀ j, (x j).IsHomogeneous d

def component (d : ℕ) (x : Free (V := V) (k := k) J) : Free (V := V) (k := k) J :=
  fun j => homogeneousComponent d (x j)

lemma component_homogeneous (d : ℕ) (x : Free (V := V) (k := k) J) :
    IsHomogeneousVector (component d x) d :=
  fun j => homogeneousComponent_isHomogeneous d (x j)

lemma component_eq_self {x : Free (V := V) (k := k) J} {d : ℕ}
    (hx : IsHomogeneousVector x d) : component d x = x := by
  funext j
  exact homogeneousComponent_eq_self (hx j)

lemma component_mul_of_homogeneous {a : Polynomial (V := V) (k := k)} {r : ℕ}
    (ha : a.IsHomogeneous r) (b : Polynomial (V := V) (k := k)) (t : ℕ) :
    homogeneousComponent (r + t) (a * b) = a * homogeneousComponent t b := by
  induction b using MvPolynomial.induction_on' with
  | monomial e c =>
    have hb : (monomial e c : Polynomial (V := V) (k := k)).IsHomogeneous e.degree :=
      isHomogeneous_monomial c rfl
    rw [homogeneousComponent_of_mem (ha.mul hb), homogeneousComponent_of_mem hb]
    by_cases he : t = e.degree <;> simp [he]
  | add p q hp hq => simp [mul_add, map_add, hp, hq]

/-- All entries of the matrix of the actual polynomial-linear map have degree `r`. -/
def IsHomogeneousMap (f : Free (V := V) (k := k) J →ₗ[Polynomial (V := V) (k := k)]
    Free (V := V) (k := k) L) (r : ℕ) : Prop :=
  ∀ a b, (f (Pi.single b 1) a).IsHomogeneous r

lemma linearMap_apply_eq_sum (f : Free (V := V) (k := k) J →ₗ[Polynomial (V := V) (k := k)]
    Free (V := V) (k := k) L) (x : Free (V := V) (k := k) J) (a : L) :
    f x a = ∑ b, x b * f (Pi.single b 1) a := by
  have hx : x = ∑ b, x b • Pi.single b (1 : Polynomial (V := V) (k := k)) := by
    funext b
    simp [Pi.single_apply]
  conv_lhs => rw [hx]
  simp

lemma homogeneousMap_component (f : Free (V := V) (k := k) J →ₗ[Polynomial (V := V) (k := k)]
    Free (V := V) (k := k) L) {r : ℕ} (hf : IsHomogeneousMap f r)
    (x : Free (V := V) (k := k) J) (t : ℕ) :
    component (r + t) (f x) = f (component t x) := by
  funext a
  rw [component, linearMap_apply_eq_sum, map_sum, linearMap_apply_eq_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [mul_comm (x b), component_mul_of_homogeneous (hf a b), mul_comm]
  rfl

lemma homogeneousMap_apply (f : Free (V := V) (k := k) J →ₗ[Polynomial (V := V) (k := k)]
    Free (V := V) (k := k) L) {r t : ℕ} (hf : IsHomogeneousMap f r)
    {x : Free (V := V) (k := k) J} (hx : IsHomogeneousVector x t) :
    IsHomogeneousVector (f x) (r + t) := by
  have he : component (r + t) (f x) = f x := by
    rw [homogeneousMap_component f hf, component_eq_self hx]
  rw [← he]
  exact component_homogeneous _ _

/-- Exactness supplies a homogeneous preimage of the required degree, with no
assumption that a chosen ungraded lift happened to preserve degrees. -/
lemma exists_homogeneous_lift
    (f : Free (V := V) (k := k) J →ₗ[Polynomial (V := V) (k := k)] Free (V := V) (k := k) L)
    {r t : ℕ} (hf : IsHomogeneousMap f r)
    {y : Free (V := V) (k := k) L} (hy : IsHomogeneousVector y (r + t))
    (hmem : y ∈ LinearMap.range f) :
    ∃ x, IsHomogeneousVector x t ∧ f x = y := by
  obtain ⟨x, rfl⟩ := hmem
  refine ⟨component t x, component_homogeneous _ _, ?_⟩
  rw [← homogeneousMap_component f hf, component_eq_self hy]

end Characterizations.Resolution
