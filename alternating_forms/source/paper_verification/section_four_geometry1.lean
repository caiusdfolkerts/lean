module

public import paper_verification.literal001
import all paper_verification.literal001
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring.Basic
import Lean.Elab.Tactic.Omega
public import paper_verification.literal005
import all paper_verification.literal005
public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.AffineSpace
public import paper_verification.literal000
import all paper_verification.literal000
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.RingHom.Locally
public import paper_verification.literal014
import all paper_verification.literal014
public import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.Tactic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import paper_verification.literal015
import all paper_verification.literal015
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension
public import paper_verification.literal003
import all paper_verification.literal003
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import paper_verification.literal004
import all paper_verification.literal004
import Mathlib.Tactic.FinCases
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

section ComponentSource_0
/- Original module: PaperVerification.AlternatingFormsOddChartScalarExtension -/


/-!
# The odd chart equations over arbitrary coefficient algebras

The square constant coefficient block in the odd isotropic chart is the
map proved invertible in `AlternatingFormsChart`.  Here its invertibility
is extended to every commutative algebra over the ground field, including
polynomial rings and nonreduced quotient rings.  The extension is an actual
base change of a proved linear equivalence, not an assumed determinant.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open scoped TensorProduct

section CoordinateBaseChange

variable {K R α β : Type*} [CommRing K] [CommRing R] [Algebra K R]
  [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Extend a finite coordinate equivalence to an arbitrary coefficient
algebra by the ordinary tensor-product base change. -/
def coordinateScalarExtendEquiv (e : (α → K) ≃ₗ[K] (β → K)) :
    (α → R) ≃ₗ[R] (β → R) :=
  (TensorProduct.piScalarRight K R R α).symm.trans
    ((e.baseChange K R _ _).trans (TensorProduct.piScalarRight K R R β))

theorem coordinateScalarExtendEquiv_single
    (e : (α → K) ≃ₗ[K] (β → K)) (i : α) (j : β) :
    coordinateScalarExtendEquiv (R := R) e (Pi.single i 1) j =
      algebraMap K R (e (Pi.single i 1) j) := by
  simp only [coordinateScalarExtendEquiv, LinearEquiv.trans_apply,
    TensorProduct.piScalarRight_symm_single, LinearEquiv.baseChange_tmul,
    TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
    Algebra.smul_def, mul_one]

end CoordinateBaseChange

section RingChart

variable {R S : Type*} [CommRing R] [CommRing S]

theorem chartPad_add_ring {k : ℕ}
    (T U : Fin k → Fin (k + 1) → R) (i j : ℕ) :
    chartPad (T + U) i j = chartPad T i j + chartPad U i j := by
  simp only [chartPad]
  split_ifs <;> simp

theorem chartPad_smul_ring {k : ℕ} (c : R)
    (T : Fin k → Fin (k + 1) → R) (i j : ℕ) :
    chartPad (c • T) i j = c • chartPad T i j := by
  simp only [chartPad]
  split_ifs <;> simp

theorem chartPad_map_ring {k : ℕ} (φ : R →+* S)
    (T : Fin k → Fin (k + 1) → R) (i j : ℕ) :
    chartPad (fun a b => φ (T a b)) i j = φ (chartPad T i j) := by
  simp only [chartPad]
  split_ifs <;> simp

abbrev OddChartHead (r : ℕ) := Fin r × Fin (r + 1)
abbrev OddChartEquation (r : ℕ) := StrictPairs (r + 1) ⊕ StrictPairs (r + 1)

/-- The same padded difference map with flattened coordinates.  The
definition is valid over arbitrary commutative rings. -/
def oddChartFlatMap (r : ℕ) :
    (OddChartHead r → R) →ₗ[R] (OddChartEquation r → R) where
  toFun T := Sum.elim
    (fun p => chartPad (fun a b => T (a,b)) p.val.1.val p.val.2.val -
      chartPad (fun a b => T (a,b)) p.val.2.val p.val.1.val)
    (fun p => chartPad (fun a b => T (a,b)) (p.val.1.val + 1) p.val.2.val -
      chartPad (fun a b => T (a,b)) (p.val.2.val + 1) p.val.1.val)
  map_add' T U := by
    funext z
    cases z <;> dsimp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply]
    all_goals
      change chartPad ((fun a b => T (a,b)) + (fun a b => U (a,b))) _ _ -
          chartPad ((fun a b => T (a,b)) + (fun a b => U (a,b))) _ _ = _
      rw [chartPad_add_ring, chartPad_add_ring]
      abel
  map_smul' c T := by
    funext z
    cases z <;> dsimp only [Sum.elim_inl, Sum.elim_inr, Pi.smul_apply]
    all_goals
      change chartPad (c • (fun a b => T (a,b))) _ _ -
          chartPad (c • (fun a b => T (a,b))) _ _ = _
      rw [chartPad_smul_ring, chartPad_smul_ring]
      exact (smul_sub c _ _).symm

theorem oddChartFlatMap_map (r : ℕ) (φ : R →+* S)
    (T : OddChartHead r → R) (z : OddChartEquation r) :
    oddChartFlatMap r (fun i => φ (T i)) z = φ (oddChartFlatMap r T z) := by
  cases z <;>
    simp only [oddChartFlatMap, LinearMap.coe_mk, AddHom.coe_mk,
      Sum.elim_inl, Sum.elim_inr, chartPad_map_ring, map_sub]

end RingChart

section AlgebraChart

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

/-- Flatten the already proved field-valued chart equivalence. -/
def oddChartFlatEquiv (r : ℕ) :
    (OddChartHead r → K) ≃ₗ[K] (OddChartEquation r → K) :=
  (LinearEquiv.curry K K (Fin r) (Fin (r+1))).trans
    ((chartEquiv r).trans
      (LinearEquiv.sumArrowLequivProdArrow (StrictPairs (r+1))
        (StrictPairs (r+1)) K K).symm)

theorem oddChartFlatEquiv_apply (r : ℕ) (T : OddChartHead r → K) :
    oddChartFlatEquiv r T = oddChartFlatMap r T := by
  funext z
  cases z <;> rfl

/-- A proved inverse for the constant coefficient block over every
commutative algebra over `K`. -/
def oddChartFlatEquivOver (r : ℕ) :
    (OddChartHead r → R) ≃ₗ[R] (OddChartEquation r → R) :=
  coordinateScalarExtendEquiv (oddChartFlatEquiv (K := K) r)

theorem oddChartFlatEquivOver_toLinearMap (r : ℕ) :
    (oddChartFlatEquivOver (K := K) (R := R) r).toLinearMap =
      oddChartFlatMap r := by
  apply (Pi.basisFun R (OddChartHead r)).ext
  intro i
  funext z
  simp only [Pi.basisFun_apply, oddChartFlatEquivOver,
    LinearEquiv.coe_coe, coordinateScalarExtendEquiv_single,
    oddChartFlatEquiv_apply]
  have hs : (Pi.single i (1 : R) : OddChartHead r → R) =
      fun j => algebraMap K R (((Pi.single i (1 : K)) : OddChartHead r → K) j) := by
    funext j
    simp [Pi.single_apply]
  rw [hs, oddChartFlatMap_map]

theorem oddChartFlatEquivOver_apply (r : ℕ) (T : OddChartHead r → R) :
    oddChartFlatEquivOver (K := K) (R := R) r T = oddChartFlatMap r T :=
  congrArg (fun L : (OddChartHead r → R) →ₗ[R] (OddChartEquation r → R) => L T)
    (oddChartFlatEquivOver_toLinearMap r)

include K in
theorem oddChartFlatMap_bijective_over (r : ℕ) :
    Function.Bijective (oddChartFlatMap (R := R) r) := by
  rw [← oddChartFlatEquivOver_toLinearMap (K := K) (R := R) r]
  exact (oddChartFlatEquivOver r).bijective

/-- Unflattened equations: the inverse remains available over polynomial
rings and over the actual isotropic chart quotient ring. -/
def oddChartEquivOver (r : ℕ) :
    (Fin r → Fin (r+1) → R) ≃ₗ[R]
      ((StrictPairs (r+1) → R) × (StrictPairs (r+1) → R)) :=
  (LinearEquiv.curry R R (Fin r) (Fin (r+1))).symm.trans
    ((oddChartFlatEquivOver (K := K) r).trans
      (LinearEquiv.sumArrowLequivProdArrow (StrictPairs (r+1))
        (StrictPairs (r+1)) R R))

theorem oddChartEquivOver_apply (r : ℕ) (T : Fin r → Fin (r+1) → R) :
    oddChartEquivOver (K := K) r T =
      (fun p => chartPad T p.val.1.val p.val.2.val -
          chartPad T p.val.2.val p.val.1.val,
       fun p => chartPad T (p.val.1.val+1) p.val.2.val -
          chartPad T (p.val.2.val+1) p.val.1.val) := by
  simp only [oddChartEquivOver, LinearEquiv.trans_apply,
    oddChartFlatEquivOver_apply]
  rfl

end AlgebraChart

end PaperVerification.AlternatingForms
end
end
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsOddChartScalarExtension"

section ComponentSource_1
/- Original module: PaperVerification.AlternatingFormsOddAffineHead -/


/-!
# The constant invertible block in the odd isotropic big cell

On the chart with pivot columns `b₀,…,bᵣ`, vary the entries in
`a₁,…,aᵣ` and keep all other entries fixed.  The change in the two
isotropy equations is exactly the constant chart map, independently of
the remaining entries.  This is the polynomial elimination step behind
the rationality argument.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open scoped BigOperators

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

def oddAffineEvenVertex (k : ℕ) (i : Fin (k+1)) : Fin (2*k+1) :=
  ⟨2*i.val, by have := i.isLt; omega⟩

def oddAffineOddVertex (k : ℕ) (i : Fin k) : Fin (2*k+1) :=
  ⟨2*i.val+1, by have := i.isLt; omega⟩

def oddAffinePivot (k r : ℕ) (h : r ≤ k) : PluckerIndex (r+1) (2*k+1) :=
  ⟨fun i => ⟨2*i.val, by have := i.isLt; omega⟩, by
    intro i j hij
    change 2*i.val < 2*j.val
    exact Nat.mul_lt_mul_of_pos_left hij (by decide)⟩

def oddAffineHeadVertex (k r : ℕ) (h : r ≤ k) (i : Fin r) : Fin (2*k+1) :=
  ⟨2*i.val+1, by have := i.isLt; omega⟩

def oddAffineIsHead (r : ℕ) {k : ℕ} (j : Fin (2*k+1)) : Prop :=
  j.val % 2 = 1 ∧ j.val / 2 < r

instance (r k : ℕ) : DecidablePred (oddAffineIsHead r (k := k)) :=
  by
    intro j
    unfold oddAffineIsHead
    infer_instance

/-- The matrix supported precisely in the first `r` nonpivot odd columns. -/
def oddAffineHeadMatrix (k r : ℕ) (T : Fin r → Fin (r+1) → R) :
    Matrix (Fin (r+1)) (Fin (2*k+1)) R :=
  fun i j => if j.val % 2 = 1 then chartPad T (j.val/2+1) i.val else 0

theorem oddAffineHeadMatrix_even (k r : ℕ)
    (T : Fin r → Fin (r+1) → R) (i : Fin (r+1)) (a : Fin (k+1)) :
    oddAffineHeadMatrix k r T i (oddAffineEvenVertex k a) = 0 := by
  have h : (2*a.val) % 2 ≠ 1 := by omega
  simp only [oddAffineHeadMatrix, oddAffineEvenVertex, h, ite_false]

theorem oddAffineHeadMatrix_odd (k r : ℕ)
    (T : Fin r → Fin (r+1) → R) (i : Fin (r+1)) (a : Fin k) :
    oddAffineHeadMatrix k r T i (oddAffineOddVertex k a) =
      chartPad T (a.val+1) i.val := by
  have h : (2*a.val+1) % 2 = 1 := by omega
  have hd : (2*a.val+1) / 2 = a.val := by omega
  simp only [oddAffineHeadMatrix, oddAffineOddVertex, h, hd, ite_true]

theorem oddAffineHeadMatrix_head (k r : ℕ) (h : r ≤ k)
    (T : Fin r → Fin (r+1) → R) (i : Fin (r+1)) (a : Fin r) :
    oddAffineHeadMatrix k r T i (oddAffineHeadVertex k r h a) = T a i := by
  change oddAffineHeadMatrix k r T i
      (oddAffineOddVertex k ⟨a.val, lt_of_lt_of_le a.isLt h⟩) = _
  rw [oddAffineHeadMatrix_odd]
  exact chartPad_entry T a i

theorem oddAffineHeadMatrix_pivot (k r : ℕ) (h : r ≤ k)
    (T : Fin r → Fin (r+1) → R) (i j : Fin (r+1)) :
    oddAffineHeadMatrix k r T i ((oddAffinePivot k r h).val j) = 0 := by
  change oddAffineHeadMatrix k r T i
    (oddAffineEvenVertex k ⟨j.val, by have := j.isLt; omega⟩) = 0
  exact oddAffineHeadMatrix_even k r T i _

theorem oddAffineHeadMatrix_off_head (k r : ℕ)
    (T : Fin r → Fin (r+1) → R) (i : Fin (r+1)) (j : Fin (2*k+1))
    (hj : ¬oddAffineIsHead r j) : oddAffineHeadMatrix k r T i j = 0 := by
  simp only [oddAffineHeadMatrix]
  split_ifs with ho
  · have hb : ¬j.val/2 < r := fun hb => hj ⟨ho,hb⟩
    simp only [chartPad]
    split_ifs with hp
    · omega
    · rfl
  · rfl

def oddMatrixFirstPair {s k : ℕ}
    (A : Matrix (Fin s) (Fin (2*k+1)) R) (i j : Fin s) : R :=
  ∑ a : Fin k, (A i (oddAffineEvenVertex k a.castSucc) * A j (oddAffineOddVertex k a) -
    A i (oddAffineOddVertex k a) * A j (oddAffineEvenVertex k a.castSucc))

def oddMatrixSecondPair {s k : ℕ}
    (A : Matrix (Fin s) (Fin (2*k+1)) R) (i j : Fin s) : R :=
  ∑ a : Fin k, (A i (oddAffineOddVertex k a) * A j (oddAffineEvenVertex k a.succ) -
    A i (oddAffineEvenVertex k a.succ) * A j (oddAffineOddVertex k a))

theorem oddMatrixPair_eq_alternatingRowPair {t k : ℕ}
    (A : Matrix (Fin (t+2)) (Fin (2*k+1)) R) (i j : Fin (t+2)) (l : Fin 2) :
    alternatingRowPair (oddPluckerForms (K := K) k l) A i j =
      ∑ a : Fin k, (A i (oddPluckerEdge k l a).val.1 * A j (oddPluckerEdge k l a).val.2 -
        A i (oddPluckerEdge k l a).val.2 * A j (oddPluckerEdge k l a).val.1) := by
  classical
  simp only [alternatingRowPair, oddPluckerForms, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem oddMatrixFirstPair_eq {t k : ℕ}
    (A : Matrix (Fin (t+2)) (Fin (2*k+1)) R) (i j : Fin (t+2)) :
    alternatingRowPair (oddPluckerForms (K := K) k 0) A i j =
      oddMatrixFirstPair A i j := by
  rw [oddMatrixPair_eq_alternatingRowPair]
  rfl

theorem oddMatrixSecondPair_eq {t k : ℕ}
    (A : Matrix (Fin (t+2)) (Fin (2*k+1)) R) (i j : Fin (t+2)) :
    alternatingRowPair (oddPluckerForms (K := K) k 1) A i j =
      oddMatrixSecondPair A i j := by
  rw [oddMatrixPair_eq_alternatingRowPair]
  rfl

private theorem oddAffine_pivot_entry {k r : ℕ} {h : r ≤ k}
    (A : Matrix (Fin (r+1)) (Fin (2*k+1)) R)
    (hA : A.submatrix id (oddAffinePivot k r h).val = 1) (i j : Fin (r+1)) :
    A i ((oddAffinePivot k r h).val j) = if i=j then 1 else 0 := by
  exact congrArg (fun B : Matrix (Fin (r+1)) (Fin (r+1)) R => B i j) hA

private theorem oddAffine_first_product_sum {k r : ℕ} (h : r ≤ k)
    (A : Matrix (Fin (r+1)) (Fin (2*k+1)) R)
    (hA : A.submatrix id (oddAffinePivot k r h).val = 1)
    (T : Fin r → Fin (r+1) → R) (i j : Fin (r+1)) :
    (∑ a : Fin k, A i (oddAffineEvenVertex k a.castSucc) *
      chartPad T (a.val+1) j.val) = chartPad T (i.val+1) j.val := by
  classical
  have hoff (a : Fin k) (hai : a.val ≠ i.val) :
      A i (oddAffineEvenVertex k a.castSucc) * chartPad T (a.val+1) j.val = 0 := by
    by_cases har : a.val < r+1
    · change A i ((oddAffinePivot k r h).val ⟨a.val,har⟩) * _ = 0
      rw [oddAffine_pivot_entry A hA]
      have hne : i ≠ (⟨a.val,har⟩ : Fin (r+1)) := by
        intro he
        exact hai (congrArg Fin.val he).symm
      simp only [hne, ite_false, zero_mul]
    · have hz : chartPad T (a.val+1) j.val = 0 := by
        simp only [chartPad]
        split_ifs with hc
        · omega
        · rfl
      rw [hz, mul_zero]
  by_cases hik : i.val < k
  · let a₀ : Fin k := ⟨i.val,hik⟩
    calc
      _ = A i (oddAffineEvenVertex k a₀.castSucc) *
          chartPad T (a₀.val+1) j.val := by
        apply Finset.sum_eq_single a₀
        · intro a ha hne
          exact hoff a (fun he => hne (Fin.ext he))
        · simp
      _ = _ := by
        change A i ((oddAffinePivot k r h).val i) * chartPad T (i.val+1) j.val = _
        rw [oddAffine_pivot_entry A hA]
        simp
  · have hir : i.val = r := by have := i.isLt; omega
    rw [hir, chartPad_last]
    apply Finset.sum_eq_zero
    intro a ha
    exact hoff a (by have := a.isLt; omega)

private theorem oddAffine_second_product_sum {k r : ℕ} (h : r ≤ k)
    (A : Matrix (Fin (r+1)) (Fin (2*k+1)) R)
    (hA : A.submatrix id (oddAffinePivot k r h).val = 1)
    (T : Fin r → Fin (r+1) → R) (i j : Fin (r+1)) :
    (∑ a : Fin k, A i (oddAffineEvenVertex k a.succ) *
      chartPad T (a.val+1) j.val) = chartPad T i.val j.val := by
  classical
  have hoff (a : Fin k) (hai : a.val+1 ≠ i.val) :
      A i (oddAffineEvenVertex k a.succ) * chartPad T (a.val+1) j.val = 0 := by
    by_cases har : a.val+1 < r+1
    · change A i ((oddAffinePivot k r h).val ⟨a.val+1,har⟩) * _ = 0
      rw [oddAffine_pivot_entry A hA]
      have hne : i ≠ (⟨a.val+1,har⟩ : Fin (r+1)) := by
        intro he
        exact hai (congrArg Fin.val he).symm
      simp only [hne, ite_false, zero_mul]
    · have hz : chartPad T (a.val+1) j.val = 0 := by
        simp only [chartPad]
        split_ifs with hc
        · omega
        · rfl
      rw [hz, mul_zero]
  by_cases hi : i.val = 0
  · rw [hi, chartPad_first]
    apply Finset.sum_eq_zero
    intro a ha
    exact hoff a (by omega)
  · let a₀ : Fin k := ⟨i.val-1, by have := i.isLt; omega⟩
    have ha₀ : a₀.val+1 = i.val := by dsimp [a₀]; omega
    calc
      _ = A i (oddAffineEvenVertex k a₀.succ) * chartPad T (a₀.val+1) j.val := by
        apply Finset.sum_eq_single a₀
        · intro a ha hne
          apply hoff
          intro he
          apply hne
          apply Fin.ext
          dsimp [a₀]
          omega
        · simp
      _ = _ := by
        have hv : oddAffineEvenVertex k a₀.succ = (oddAffinePivot k r h).val i := by
          apply Fin.ext
          simp only [oddAffineEvenVertex, oddAffinePivot, Fin.val_succ, ha₀]
        rw [hv, ha₀, oddAffine_pivot_entry A hA]
        simp

/-- Adding the head matrix changes the first isotropy equation by the
second component of the constant chart map. -/
theorem oddMatrixFirstPair_add_head {k r : ℕ} (h : r ≤ k)
    (A : Matrix (Fin (r+1)) (Fin (2*k+1)) R)
    (hA : A.submatrix id (oddAffinePivot k r h).val = 1)
    (T : Fin r → Fin (r+1) → R) (i j : Fin (r+1)) :
    oddMatrixFirstPair (A + oddAffineHeadMatrix k r T) i j =
      oddMatrixFirstPair A i j +
        (chartPad T (i.val+1) j.val - chartPad T (j.val+1) i.val) := by
  have he : oddMatrixFirstPair (A + oddAffineHeadMatrix k r T) i j =
      oddMatrixFirstPair A i j +
        ((∑ a : Fin k, A i (oddAffineEvenVertex k a.castSucc) * chartPad T (a.val+1) j.val) -
         (∑ a : Fin k, A j (oddAffineEvenVertex k a.castSucc) * chartPad T (a.val+1) i.val)) := by
    simp only [oddMatrixFirstPair, Matrix.add_apply, oddAffineHeadMatrix_even,
      oddAffineHeadMatrix_odd, add_zero, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  rw [he, oddAffine_first_product_sum h A hA, oddAffine_first_product_sum h A hA]

/-- Adding the head matrix changes the second equation by minus the first
component of the same constant chart map. -/
theorem oddMatrixSecondPair_add_head {k r : ℕ} (h : r ≤ k)
    (A : Matrix (Fin (r+1)) (Fin (2*k+1)) R)
    (hA : A.submatrix id (oddAffinePivot k r h).val = 1)
    (T : Fin r → Fin (r+1) → R) (i j : Fin (r+1)) :
    oddMatrixSecondPair (A + oddAffineHeadMatrix k r T) i j =
      oddMatrixSecondPair A i j +
        (chartPad T j.val i.val - chartPad T i.val j.val) := by
  have he : oddMatrixSecondPair (A + oddAffineHeadMatrix k r T) i j =
      oddMatrixSecondPair A i j +
        ((∑ a : Fin k, A j (oddAffineEvenVertex k a.succ) * chartPad T (a.val+1) i.val) -
         (∑ a : Fin k, A i (oddAffineEvenVertex k a.succ) * chartPad T (a.val+1) j.val)) := by
    simp only [oddMatrixSecondPair, Matrix.add_apply, oddAffineHeadMatrix_even,
      oddAffineHeadMatrix_odd, add_zero, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  rw [he, oddAffine_second_product_sum h A hA, oddAffine_second_product_sum h A hA]

end PaperVerification.AlternatingForms
end
end
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsOddAffineHead"

section ComponentSource_2
/- Original module: PaperVerification.AlternatingFormsOddAffineCompletion -/


/-!
# Polynomial completion and uniqueness in the odd isotropic chart

Every pivot-normalized matrix can be made simultaneously isotropic by
changing only its first `r` odd columns.  The required entries are given
by the inverse of a constant linear equivalence.  Consequently the
completion is polynomial in the remaining entries.  Uniqueness is proved
over every commutative coefficient algebra.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open scoped BigOperators

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

theorem oddMatrixFirstPair_self {s k : ℕ}
    (A : Matrix (Fin s) (Fin (2*k+1)) R) (i : Fin s) :
    oddMatrixFirstPair A i i = 0 := by
  simp [oddMatrixFirstPair, mul_comm]

theorem oddMatrixSecondPair_self {s k : ℕ}
    (A : Matrix (Fin s) (Fin (2*k+1)) R) (i : Fin s) :
    oddMatrixSecondPair A i i = 0 := by
  simp [oddMatrixSecondPair, mul_comm]

theorem oddMatrixFirstPair_swap {s k : ℕ}
    (A : Matrix (Fin s) (Fin (2*k+1)) R) (i j : Fin s) :
    oddMatrixFirstPair A j i = -oddMatrixFirstPair A i j := by
  simp only [oddMatrixFirstPair, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem oddMatrixSecondPair_swap {s k : ℕ}
    (A : Matrix (Fin s) (Fin (2*k+1)) R) (i j : Fin s) :
    oddMatrixSecondPair A j i = -oddMatrixSecondPair A i j := by
  simp only [oddMatrixSecondPair, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- The unique head correction that kills the two row-isotropy equations. -/
def oddAffineHeadSolution {k r : ℕ}
    (A : Matrix (Fin (r+1)) (Fin (2*k+1)) R) : Fin r → Fin (r+1) → R :=
  (oddChartEquivOver (K := K) (R := R) r).symm
    (fun p => oddMatrixSecondPair A p.val.1 p.val.2,
     fun p => -oddMatrixFirstPair A p.val.1 p.val.2)

def oddAffineCompletion {k r : ℕ}
    (A : Matrix (Fin (r+1)) (Fin (2*k+1)) R) :
    Matrix (Fin (r+1)) (Fin (2*k+1)) R :=
  A + oddAffineHeadMatrix k r (oddAffineHeadSolution (K := K) A)

theorem oddAffineCompletion_pivot {k r : ℕ} (h : r ≤ k)
    (A : Matrix (Fin (r+1)) (Fin (2*k+1)) R)
    (hA : A.submatrix id (oddAffinePivot k r h).val = 1) :
    (oddAffineCompletion (K := K) A).submatrix id (oddAffinePivot k r h).val = 1 := by
  ext i j
  have hp := congrArg (fun B : Matrix (Fin (r+1)) (Fin (r+1)) R => B i j) hA
  change A i ((oddAffinePivot k r h).val j) +
    oddAffineHeadMatrix k r (oddAffineHeadSolution (K := K) A) i
      ((oddAffinePivot k r h).val j) = _
  rw [oddAffineHeadMatrix_pivot, add_zero]
  exact hp

theorem oddAffineCompletion_first {k r : ℕ} (h : r ≤ k)
    (A : Matrix (Fin (r+1)) (Fin (2*k+1)) R)
    (hA : A.submatrix id (oddAffinePivot k r h).val = 1) (i j : Fin (r+1)) :
    oddMatrixFirstPair (oddAffineCompletion (K := K) A) i j = 0 := by
  have hs (p : StrictPairs (r+1)) :
      oddMatrixFirstPair (oddAffineCompletion (K := K) A) p.val.1 p.val.2 = 0 := by
    have hsolve := congrArg (fun Z : (StrictPairs (r+1) → R) × (StrictPairs (r+1) → R) => Z.2 p)
      ((oddChartEquivOver (K := K) (R := R) r).apply_symm_apply
        (fun q => oddMatrixSecondPair A q.val.1 q.val.2,
         fun q => -oddMatrixFirstPair A q.val.1 q.val.2))
    change (oddChartEquivOver (K := K) r (oddAffineHeadSolution (K := K) A)).2 p =
      -oddMatrixFirstPair A p.val.1 p.val.2 at hsolve
    rw [oddChartEquivOver_apply] at hsolve
    dsimp only at hsolve
    rw [oddAffineCompletion, oddMatrixFirstPair_add_head h A hA, hsolve, add_neg_cancel]
  rcases lt_trichotomy i j with hij | hij | hij
  · exact hs ⟨(i,j),hij⟩
  · subst j
    exact oddMatrixFirstPair_self _ i
  · rw [oddMatrixFirstPair_swap, hs ⟨(j,i),hij⟩, neg_zero]

theorem oddAffineCompletion_second {k r : ℕ} (h : r ≤ k)
    (A : Matrix (Fin (r+1)) (Fin (2*k+1)) R)
    (hA : A.submatrix id (oddAffinePivot k r h).val = 1) (i j : Fin (r+1)) :
    oddMatrixSecondPair (oddAffineCompletion (K := K) A) i j = 0 := by
  have hs (p : StrictPairs (r+1)) :
      oddMatrixSecondPair (oddAffineCompletion (K := K) A) p.val.1 p.val.2 = 0 := by
    have hsolve := congrArg (fun Z : (StrictPairs (r+1) → R) × (StrictPairs (r+1) → R) => Z.1 p)
      ((oddChartEquivOver (K := K) (R := R) r).apply_symm_apply
        (fun q => oddMatrixSecondPair A q.val.1 q.val.2,
         fun q => -oddMatrixFirstPair A q.val.1 q.val.2))
    change (oddChartEquivOver (K := K) r (oddAffineHeadSolution (K := K) A)).1 p =
      oddMatrixSecondPair A p.val.1 p.val.2 at hsolve
    rw [oddChartEquivOver_apply] at hsolve
    dsimp only at hsolve
    rw [oddAffineCompletion, oddMatrixSecondPair_add_head h A hA,
      ← neg_sub, hsolve, add_neg_cancel]
  rcases lt_trichotomy i j with hij | hij | hij
  · exact hs ⟨(i,j),hij⟩
  · subst j
    exact oddMatrixSecondPair_self _ i
  · rw [oddMatrixSecondPair_swap, hs ⟨(j,i),hij⟩, neg_zero]

theorem oddAffineCompletion_off_head {k r : ℕ}
    (A : Matrix (Fin (r+1)) (Fin (2*k+1)) R)
    (i : Fin (r+1)) (j : Fin (2*k+1)) (hj : ¬oddAffineIsHead r j) :
    oddAffineCompletion (K := K) A i j = A i j := by
  change A i j + oddAffineHeadMatrix k r (oddAffineHeadSolution (K := K) A) i j = _
  rw [oddAffineHeadMatrix_off_head k r _ i j hj, add_zero]

/-- Two head corrections of the same normalized matrix which give
isotropic rows necessarily coincide. -/
theorem oddAffineHeadSolution_unique {k r : ℕ} (h : r ≤ k)
    (A : Matrix (Fin (r+1)) (Fin (2*k+1)) R)
    (hA : A.submatrix id (oddAffinePivot k r h).val = 1)
    (T : Fin r → Fin (r+1) → R)
    (hF : ∀ i j, oddMatrixFirstPair (A + oddAffineHeadMatrix k r T) i j = 0)
    (hG : ∀ i j, oddMatrixSecondPair (A + oddAffineHeadMatrix k r T) i j = 0) :
    T = oddAffineHeadSolution (K := K) A := by
  apply (oddChartEquivOver (K := K) (R := R) r).injective
  rw [oddAffineHeadSolution, LinearEquiv.apply_symm_apply, oddChartEquivOver_apply]
  apply Prod.ext <;> funext p
  · have hg := hG p.val.1 p.val.2
    rw [oddMatrixSecondPair_add_head h A hA, ← neg_sub, ← sub_eq_add_neg] at hg
    exact (sub_eq_zero.mp hg).symm
  · have hf := hF p.val.1 p.val.2
    rw [oddMatrixFirstPair_add_head h A hA] at hf
    exact eq_neg_of_add_eq_zero_right hf

def oddAffineHeadCoordinates {k r : ℕ} (h : r ≤ k)
    (A : Matrix (Fin (r+1)) (Fin (2*k+1)) R) : Fin r → Fin (r+1) → R :=
  fun a i => A i (oddAffineHeadVertex k r h a)

theorem oddAffine_matrix_eq_add_head {k r : ℕ} (h : r ≤ k)
    (A B : Matrix (Fin (r+1)) (Fin (2*k+1)) R)
    (hoff : ∀ i j, ¬oddAffineIsHead r j → A i j = B i j) :
    A = B + oddAffineHeadMatrix k r (oddAffineHeadCoordinates h (A-B)) := by
  ext i j
  by_cases hj : oddAffineIsHead r j
  · let a : Fin r := ⟨j.val/2,hj.2⟩
    have hv : oddAffineHeadVertex k r h a = j := by
      apply Fin.ext
      dsimp [oddAffineHeadVertex, a]
      have hm := Nat.mod_add_div j.val 2
      have hodd : j.val % 2 = 1 := hj.1
      omega
    rw [← hv]
    change A i (oddAffineHeadVertex k r h a) = B i (oddAffineHeadVertex k r h a) + _
    rw [oddAffineHeadMatrix_head]
    change A i (oddAffineHeadVertex k r h a) = B i (oddAffineHeadVertex k r h a) +
      (A i (oddAffineHeadVertex k r h a) - B i (oddAffineHeadVertex k r h a))
    ring
  · change A i j = B i j + _
    rw [oddAffineHeadMatrix_off_head k r _ i j hj, add_zero]
    exact hoff i j hj

theorem oddAffineHeadMatrix_zero (k r : ℕ) :
    oddAffineHeadMatrix (R := R) k r 0 = 0 := by
  ext i j
  simp [oddAffineHeadMatrix, chartPad]

include K in
/-- Isotropy and the non-head entries determine the whole normalized
matrix, over arbitrary commutative algebras. -/
theorem oddAffine_isotropic_ext {k r : ℕ} (h : r ≤ k)
    (A B : Matrix (Fin (r+1)) (Fin (2*k+1)) R)
    (hB : B.submatrix id (oddAffinePivot k r h).val = 1)
    (hAF : ∀ i j, oddMatrixFirstPair A i j = 0)
    (hAG : ∀ i j, oddMatrixSecondPair A i j = 0)
    (hBF : ∀ i j, oddMatrixFirstPair B i j = 0)
    (hBG : ∀ i j, oddMatrixSecondPair B i j = 0)
    (hoff : ∀ i j, ¬oddAffineIsHead r j → A i j = B i j) : A = B := by
  let T := oddAffineHeadCoordinates h (A-B)
  have hAB : A = B + oddAffineHeadMatrix k r T := oddAffine_matrix_eq_add_head h A B hoff
  have hT := oddAffineHeadSolution_unique (K := K) h B hB T
    (fun i j => hAB ▸ hAF i j) (fun i j => hAB ▸ hAG i j)
  have h0 := oddAffineHeadSolution_unique (K := K) h B hB 0
    (by simpa only [oddAffineHeadMatrix_zero, add_zero] using hBF)
    (by simpa only [oddAffineHeadMatrix_zero, add_zero] using hBG)
  have hz : T = 0 := hT.trans h0.symm
  rw [hAB, hz, oddAffineHeadMatrix_zero, add_zero]

end PaperVerification.AlternatingForms
end
end
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsOddAffineCompletion"

section ComponentSource_3
/- Original module: PaperVerification.AlternatingFormsOddAffineChart -/


/-!
# A polynomial coordinate ring for the odd common-isotropic big cell

The nonpivot entries outside the head columns are free coordinates.
The constant-block completion constructs the other entries as actual
polynomials in these coordinates.  The resulting two algebra maps are
proved inverse using uniqueness over arbitrary coefficient algebras.
Thus the displayed chart ring is a polynomial algebra, without reduction,
localization at an additional determinant, or a smoothness assumption.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial

variable {K : Type*} [Field K]

abbrev OddAffineFreeVariable (k r : ℕ) (h : r ≤ k) :=
  {a : PluckerChartVariable (oddAffinePivot k r h) //
    ¬oddAffineIsHead r a.2.val}

def oddAffineFreeAssignment (k r : ℕ) (h : r ≤ k)
    (a : PluckerChartVariable (oddAffinePivot k r h)) :
    MvPolynomial (OddAffineFreeVariable k r h) K :=
  if ha : ¬oddAffineIsHead r a.2.val then X ⟨a,ha⟩ else 0

def oddAffineFreeEvaluation (k r : ℕ) (h : r ≤ k) :
    MvPolynomial (PluckerChartVariable (oddAffinePivot k r h)) K →ₐ[K]
      MvPolynomial (OddAffineFreeVariable k r h) K :=
  aeval (oddAffineFreeAssignment k r h)

def oddAffineFreeMatrix (k r : ℕ) (h : r ≤ k) :
    Matrix (Fin (r+1)) (Fin (2*k+1))
      (MvPolynomial (OddAffineFreeVariable k r h) K) :=
  (pluckerChartMatrix (K := K) (oddAffinePivot k r h)).map
    (oddAffineFreeEvaluation (K := K) k r h)

theorem oddAffineFreeMatrix_pivot (k r : ℕ) (h : r ≤ k) :
    (oddAffineFreeMatrix (K := K) k r h).submatrix id (oddAffinePivot k r h).val = 1 := by
  apply Matrix.ext
  intro i j
  change oddAffineFreeEvaluation (K := K) k r h
      (pluckerChartMatrix (K := K) (oddAffinePivot k r h) i
        ((oddAffinePivot k r h).val j)) = _
  have hp := congrArg
    (fun B : Matrix (Fin (r+1)) (Fin (r+1))
      (MvPolynomial (PluckerChartVariable (oddAffinePivot k r h)) K) => B i j)
    (pluckerChartMatrix_pivot (K := K) (oddAffinePivot k r h))
  simp only [Matrix.of_apply] at hp
  rw [hp]
  simp only [Matrix.one_apply, apply_ite, map_one, map_zero]
  split_ifs <;> rfl

theorem oddAffineFreeMatrix_free (k r : ℕ) (h : r ≤ k)
    (a : OddAffineFreeVariable k r h) :
    oddAffineFreeMatrix (K := K) k r h a.val.1 a.val.2.val = X a := by
  change oddAffineFreeEvaluation (K := K) k r h
      (pluckerChartMatrix (K := K) (oddAffinePivot k r h) a.val.1 a.val.2.val) = _
  rw [pluckerChartMatrix_nonpivot]
  simp only [oddAffineFreeEvaluation, aeval_X, oddAffineFreeAssignment, dif_pos a.property]

theorem oddAffine_head_not_pivot (k r : ℕ) (h : r ≤ k) (j : Fin (2*k+1))
    (hj : oddAffineIsHead r j) : j ∉ Set.range (oddAffinePivot k r h).val := by
  rintro ⟨i,hi⟩
  have hv := congrArg Fin.val hi
  dsimp [oddAffinePivot] at hv
  have := hj.1
  omega

theorem oddAffineFreeMatrix_head (k r : ℕ) (h : r ≤ k)
    (i : Fin (r+1)) (j : Fin (2*k+1)) (hj : oddAffineIsHead r j) :
    oddAffineFreeMatrix (K := K) k r h i j = 0 := by
  have hnp := oddAffine_head_not_pivot k r h j hj
  change oddAffineFreeEvaluation (K := K) k r h
    (pluckerChartMatrix (K := K) (oddAffinePivot k r h) i j) = 0
  rw [pluckerChartMatrix_nonpivot (oddAffinePivot k r h) i ⟨j,hnp⟩]
  simp only [oddAffineFreeEvaluation, aeval_X, oddAffineFreeAssignment,
    dif_neg (not_not.mpr hj)]

/-- An actual polynomial family of normalized common-isotropic matrices. -/
def oddAffineParamMatrix (k r : ℕ) (h : r ≤ k) :
    Matrix (Fin (r+1)) (Fin (2*k+1))
      (MvPolynomial (OddAffineFreeVariable k r h) K) :=
  oddAffineCompletion (K := K) (oddAffineFreeMatrix k r h)

theorem oddAffineParamMatrix_pivot (k r : ℕ) (h : r ≤ k) :
    (oddAffineParamMatrix (K := K) k r h).submatrix id (oddAffinePivot k r h).val = 1 :=
  oddAffineCompletion_pivot h _ (oddAffineFreeMatrix_pivot k r h)

theorem oddAffineParamMatrix_free (k r : ℕ) (h : r ≤ k)
    (a : OddAffineFreeVariable k r h) :
    oddAffineParamMatrix (K := K) k r h a.val.1 a.val.2.val = X a := by
  rw [oddAffineParamMatrix,
    oddAffineCompletion_off_head _ _ _ a.property, oddAffineFreeMatrix_free]

def oddAffineParamPoint (k t : ℕ) (h : t+1 ≤ k) :
    IsotropicChartPoint (oddAffinePivot k (t+1) h) (oddPluckerForms (K := K) k)
      (MvPolynomial (OddAffineFreeVariable k (t+1) h) K) where
  matrix := oddAffineParamMatrix k (t+1) h
  pivot := oddAffineParamMatrix_pivot k (t+1) h
  isotropic := by
    intro l i j
    fin_cases l
    · exact (oddMatrixFirstPair_eq (K := K) (oddAffineParamMatrix (K := K) k (t+1) h) i j).trans
        (oddAffineCompletion_first h _ (oddAffineFreeMatrix_pivot k (t+1) h) i j)
    · exact (oddMatrixSecondPair_eq (K := K) (oddAffineParamMatrix (K := K) k (t+1) h) i j).trans
        (oddAffineCompletion_second h _ (oddAffineFreeMatrix_pivot k (t+1) h) i j)

/-- On this actual chart, the free entries determine an isotropic point
over every commutative `K`-algebra. -/
theorem oddAffineChartPoint_ext_free
    {R : Type*} [CommRing R] [Algebra K R] (k t : ℕ) (h : t+1 ≤ k)
    (A B : IsotropicChartPoint (oddAffinePivot k (t+1) h)
      (oddPluckerForms (K := K) k) R)
    (hfree : ∀ a : OddAffineFreeVariable k (t+1) h,
      A.matrix a.val.1 a.val.2.val = B.matrix a.val.1 a.val.2.val) : A = B := by
  apply IsotropicChartPoint.ext_matrix
  apply oddAffine_isotropic_ext (K := K) h A.matrix B.matrix B.pivot
  · intro i j
    exact (oddMatrixFirstPair_eq (K := K) A.matrix i j).symm.trans
      (A.isotropic 0 i j)
  · intro i j
    exact (oddMatrixSecondPair_eq (K := K) A.matrix i j).symm.trans
      (A.isotropic 1 i j)
  · intro i j
    exact (oddMatrixFirstPair_eq (K := K) B.matrix i j).symm.trans
      (B.isotropic 0 i j)
  · intro i j
    exact (oddMatrixSecondPair_eq (K := K) B.matrix i j).symm.trans
      (B.isotropic 1 i j)
  · intro i j hj
    by_cases hp : j ∈ Set.range (oddAffinePivot k (t+1) h).val
    · obtain ⟨a,rfl⟩ := hp
      have hA := congrArg (fun C : Matrix (Fin (t+2)) (Fin (t+2)) R => C i a) A.pivot
      have hB := congrArg (fun C : Matrix (Fin (t+2)) (Fin (t+2)) R => C i a) B.pivot
      exact hA.trans hB.symm
    · exact hfree ⟨(i,⟨j,hp⟩),hj⟩

def oddAffineChartToPolynomial (k t : ℕ) (h : t+1 ≤ k) :
    IsotropicChartRing (oddAffinePivot k (t+1) h) (oddPluckerForms (K := K) k) →ₐ[K]
      MvPolynomial (OddAffineFreeVariable k (t+1) h) K :=
  (oddAffineParamPoint k t h).toAlgHom

def oddAffinePolynomialToChart (k t : ℕ) (h : t+1 ≤ k) :
    MvPolynomial (OddAffineFreeVariable k (t+1) h) K →ₐ[K]
      IsotropicChartRing (oddAffinePivot k (t+1) h) (oddPluckerForms (K := K) k) :=
  aeval (fun a => Ideal.Quotient.mk _ (X a.val))

theorem oddAffineChartToPolynomial_free (k t : ℕ) (h : t+1 ≤ k)
    (a : OddAffineFreeVariable k (t+1) h) :
    oddAffineChartToPolynomial (K := K) k t h (Ideal.Quotient.mk _ (X a.val)) = X a := by
  rw [← pluckerChartMatrix_nonpivot (oddAffinePivot k (t+1) h) a.val.1 a.val.2]
  change (oddAffineParamPoint (K := K) k t h).toAlgHom (Ideal.Quotient.mk _ _) = _
  rw [IsotropicChartPoint.toAlgHom_entry]
  exact oddAffineParamMatrix_free k (t+1) h a

theorem oddAffineChartToPolynomial_rightInverse (k t : ℕ) (h : t+1 ≤ k) :
    (oddAffineChartToPolynomial (K := K) k t h).comp (oddAffinePolynomialToChart k t h) =
      AlgHom.id K (MvPolynomial (OddAffineFreeVariable k (t+1) h) K) := by
  apply MvPolynomial.algHom_ext
  intro a
  change oddAffineChartToPolynomial k t h (oddAffinePolynomialToChart k t h (X a)) = X a
  rw [oddAffinePolynomialToChart, aeval_X, oddAffineChartToPolynomial_free]

theorem oddAffineChartToPolynomial_leftInverse (k t : ℕ) (h : t+1 ≤ k) :
    (oddAffinePolynomialToChart (K := K) k t h).comp (oddAffineChartToPolynomial k t h) =
      AlgHom.id K (IsotropicChartRing (oddAffinePivot k (t+1) h) (oddPluckerForms k)) := by
  apply (isotropicChartPointEquiv (oddAffinePivot k (t+1) h) (oddPluckerForms k)).injective
  apply oddAffineChartPoint_ext_free k t h
  intro a
  change oddAffinePolynomialToChart k t h
      (oddAffineChartToPolynomial k t h
        (Ideal.Quotient.mk _ (pluckerChartMatrix (oddAffinePivot k (t+1) h)
          a.val.1 a.val.2.val))) =
      Ideal.Quotient.mk _ (pluckerChartMatrix (oddAffinePivot k (t+1) h)
        a.val.1 a.val.2.val)
  rw [pluckerChartMatrix_nonpivot, oddAffineChartToPolynomial_free]
  simp only [oddAffinePolynomialToChart, aeval_X]

/-- The original row-isotropy quotient is a polynomial algebra in the
remaining nonpivot entries.  Both maps above have their literal meanings. -/
def oddAffineChartEquiv (k t : ℕ) (h : t+1 ≤ k) :
    IsotropicChartRing (oddAffinePivot k (t+1) h) (oddPluckerForms (K := K) k) ≃ₐ[K]
      MvPolynomial (OddAffineFreeVariable k (t+1) h) K :=
  AlgEquiv.ofAlgHom (oddAffineChartToPolynomial k t h) (oddAffinePolynomialToChart k t h)
    (oddAffineChartToPolynomial_rightInverse k t h) (oddAffineChartToPolynomial_leftInverse k t h)

end PaperVerification.AlternatingForms
end
end
end ComponentSource_3

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsOddAffineChart"

section ComponentSource_4
/- Original module: PaperVerification.AlternatingFormsProjRationality -/


/-!
# Dense affine charts and genuine scheme rationality

These general lemmas use Mathlib's actual projective spectrum, partial
scheme isomorphisms, and `Scheme.IsRationalOver`.  Density of a nonempty
basic open in the projective spectrum of a domain is proved from the
homogeneous zero prime, rather than taken as an application hypothesis.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open AlgebraicGeometry CategoryTheory

universe u

section ProjectiveDensity

variable {A σ : Type u} [CommRing A] [IsDomain A]
  [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A nonempty basic open of the actual projective spectrum of a domain
is dense.  The proof constructs and uses the homogeneous zero prime. -/
theorem projective_basicOpen_dense_of_nonempty (f : A)
    (h : (Proj.basicOpen 𝒜 f : Set (Proj 𝒜)).Nonempty) :
    Dense (Proj.basicOpen 𝒜 f : Set (Proj 𝒜)) := by
  obtain ⟨x,hx⟩ := h
  let η : ProjectiveSpectrum 𝒜 :=
    { asHomogeneousIdeal := ⊥
      isPrime := by simpa only [HomogeneousIdeal.toIdeal_bot] using
        (inferInstance : (⊥ : Ideal A).IsPrime)
      not_irrelevant_le := fun hi => x.not_irrelevant_le (hi.trans bot_le) }
  have hηdense : Dense ({η} : Set (ProjectiveSpectrum 𝒜)) := by
    rw [dense_iff_closure_eq, ← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      ProjectiveSpectrum.vanishingIdeal_singleton]
    change ProjectiveSpectrum.zeroLocus 𝒜 ((⊥ : Ideal A) : Set A) = Set.univ
    exact ProjectiveSpectrum.zeroLocus_bot 𝒜
  apply hηdense.mono
  intro y hy
  obtain rfl := Set.mem_singleton_iff.mp hy
  change f ∉ (⊥ : HomogeneousIdeal 𝒜)
  intro hf
  have hf0 : f = 0 := Ideal.mem_bot.mp hf
  apply hx
  rw [hf0]
  exact x.asHomogeneousIdeal.toIdeal.zero_mem

end ProjectiveDensity

section Birationality

variable {S X Y : Scheme.{u}}

theorem scheme_birationalOver_of_iso (sX : X ⟶ S) (sY : Y ⟶ S)
    (e : X ≅ Y) (h : e.hom ≫ sY = sX) : Scheme.BirationalOver sX sY := by
  refine ⟨Scheme.PartialIso.ofIso e, ?_⟩
  simp [Scheme.PartialIso.IsOver, Scheme.PartialIso.ofIso, h]

/-- The actual birational correspondence with the displayed affine space.
Keeping its index explicit lets finite-dimensional rationality be stated
without relying on the more permissive `IsRationalOver` class. -/
theorem scheme_birationalOver_affine_of_dense_chart
    (sX : X ⟶ S) (U : X.Opens) (hU : Dense (U : Set X)) (n : Type u)
    (e : U.toScheme ≅ 𝔸(n; S))
    (he : e.hom ≫ (𝔸(n; S) ↘ S) = U.ι ≫ sX) :
    Scheme.BirationalOver sX (𝔸(n; S) ↘ S) :=
  (U.birationalOver_of_dense sX hU).symm.trans
    (scheme_birationalOver_of_iso (U.ι ≫ sX) (𝔸(n; S) ↘ S) e he)

/-- A dense open with an affine-space isomorphism over the base yields
the standard scheme-theoretic rationality property. -/
theorem scheme_isRationalOver_of_dense_affine_chart
    (sX : X ⟶ S) (U : X.Opens) (hU : Dense (U : Set X)) (n : Type u)
    (e : U.toScheme ≅ 𝔸(n; S))
    (he : e.hom ≫ (𝔸(n; S) ↘ S) = U.ι ≫ sX) :
    Scheme.IsRationalOver sX := by
  exact ⟨n, scheme_birationalOver_affine_of_dense_chart sX U hU n e he⟩

end Birationality

end PaperVerification.AlternatingForms
end
end
end ComponentSource_4

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsProjRationality"

section ComponentSource_5
/- Original module: PaperVerification.HomogeneousQuotientChartOver -/


/-!
# The homogeneous quotient charts preserve the ground field

The existing chart comparison is a ring equivalence.  Its constant-term
formula proves that the associated scheme chart isomorphism lies over
the canonical map to the spectrum of the ground field.  This keeps the
base field explicit in later birationality statements.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.HomogeneousQuotientCharts

open AlgebraicGeometry CategoryTheory _root_.HomogeneousLocalization MvPolynomial
open PaperVerification.HomogeneousChartDehomogenization

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K ι : Type} [Field K]
  (Q : Ideal (MvPolynomial ι K))
  (hQ : Q.IsHomogeneous (homogeneousSubmodule ι K)) (p : ι)

local notation "P" => MvPolynomial ι K
local notation "𝒜" => HomogeneousQuotientProjective.grading Q hQ

/-- The canonical structure map of the actual homogeneous quotient Proj
to the original coefficient field. -/
def structureMap : Proj 𝒜 ⟶ Spec (CommRingCat.of K) :=
  Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap K (𝒜 0)))

include hQ in
theorem awayQuotientChartEquiv_constant (c : K) :
    awayQuotientChartEquiv Q hQ p
      (fromZeroRingHom 𝒜 (Submonoid.powers (Ideal.Quotient.mk Q (X p)))
        (algebraMap K (𝒜 0) c)) =
      algebraMap K (P ⧸ (Q ⊔ Ideal.span {X p-1})) c := by
  let hf := HomogeneousQuotientProjective.quotient_X_mem_one Q hQ p
  have hz : fromZeroRingHom 𝒜 (Submonoid.powers (Ideal.Quotient.mk Q (X p)))
      (algebraMap K (𝒜 0) c) =
      fraction 𝒜 hf 0 (algebraMap K (𝒜 0) c) := by
    apply HomogeneousLocalization.val_injective
    simp only [fromZeroRingHom, HomogeneousLocalization.val_mk,
      fraction_val, pow_zero]
    rfl
  rw [hz, awayQuotientChartEquiv, RingEquiv.trans_apply,
    awayEquivNormalized_fraction]
  change normalizedQuotientEquiv Q p
      (quotientMap (Ideal.Quotient.mk Q (X p)) (Ideal.Quotient.mk Q (C c))) = _
  rw [normalizedQuotientEquiv_class]
  rfl

include hQ in
/-- The normalized chart isomorphism is a morphism over `Spec K`. -/
theorem projectiveBasicOpenIsoNormalized_inv_over :
    (projectiveBasicOpenIsoNormalized Q hQ p).inv ≫
      (Proj.basicOpen 𝒜 (Ideal.Quotient.mk Q (X p))).ι ≫ structureMap Q hQ =
      Spec.map (CommRingCat.ofHom (algebraMap K (P ⧸ (Q ⊔ Ideal.span {X p-1})))) := by
  simp only [projectiveBasicOpenIsoNormalized, structureMap, Iso.trans_inv,
    Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map, Quiver.Hom.unop_op,
    Category.assoc, Proj.basicOpenIsoSpec_inv_ι_assoc, Proj.awayι_toSpecZero_assoc]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext c
  exact awayQuotientChartEquiv_constant Q hQ p c

include hQ in
theorem projectiveBasicOpenIsoNormalized_hom_over :
    (projectiveBasicOpenIsoNormalized Q hQ p).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (P ⧸ (Q ⊔ Ideal.span {X p-1})))) =
      (Proj.basicOpen 𝒜 (Ideal.Quotient.mk Q (X p))).ι ≫ structureMap Q hQ := by
  rw [← projectiveBasicOpenIsoNormalized_inv_over Q hQ p,
    Iso.hom_inv_id_assoc]

end PaperVerification.HomogeneousQuotientCharts
end
end
end ComponentSource_5

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.HomogeneousQuotientChartOver"

section ComponentSource_6
/- Original module: PaperVerification.AlternatingFormsProjOver -/


/-!
# The ground-field structure map of common-isotropic Proj

The chart identifications commute with the genuine structure map to the
original coefficient field. These lemmas are independent of odd-dimensional
rationality and can also be used for smoothness on the complete chart cover.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type} [Field K] [CharZero K]

theorem specAlgEquiv_hom_over
    {R S : Type} [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (e : R ≃ₐ[K] S) :
    (Scheme.Spec.mapIso e.symm.toRingEquiv.toCommRingCatIso.op).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K S)) =
      Spec.map (CommRingCat.ofHom (algebraMap K R)) := by
  simp only [Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map, Quiver.Hom.unop_op]
  rw [← Spec.map_comp]
  congr 1
  ext c
  exact e.symm.commutes c

def isotropicStructureMap {t n m : ℕ} (forms : Fin m → StrictPairs n → K) :
    Proj (isotropicProjectiveGrading (t := t) forms) ⟶ Spec (CommRingCat.of K) :=
  HomogeneousQuotientCharts.structureMap (isotropicPluckerIdeal forms)
    (isotropicPluckerIdeal_isHomogeneous forms)

theorem isotropicProjBasicOpenIso_hom_over {t n m : ℕ}
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K) :
    (isotropicProjBasicOpenIso p forms).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (IsotropicChartRing p forms))) =
      (Proj.basicOpen (isotropicProjectiveGrading (t := t) forms)
        (Ideal.Quotient.mk (isotropicPluckerIdeal forms) (X p))).ι ≫
          isotropicStructureMap forms := by
  let e₁ := HomogeneousQuotientCharts.projectiveBasicOpenIsoNormalized
    (isotropicPluckerIdeal forms) (isotropicPluckerIdeal_isHomogeneous forms) p
  let e₂ := Scheme.Spec.mapIso (isotropicPluckerBigCellEquiv p forms).symm.toRingEquiv.toCommRingCatIso.op
  exact (Category.assoc e₁.hom e₂.hom _).trans
    ((congrArg (fun f ↦ e₁.hom ≫ f)
      (specAlgEquiv_hom_over (isotropicPluckerBigCellEquiv p forms))).trans
      (HomogeneousQuotientCharts.projectiveBasicOpenIsoNormalized_hom_over
        (isotropicPluckerIdeal forms) (isotropicPluckerIdeal_isHomogeneous forms) p))

end PaperVerification.AlternatingForms
end
end
end ComponentSource_6

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsProjOver"

section ComponentSource_7
/- Original module: PaperVerification.HomogeneousQuotientAffineChartOver -/


/-! A normalized polynomial chart is an affine-space chart over the original field. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.HomogeneousQuotientCharts

open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K ι N : Type} [Field K] [CharZero K]
  (Q : Ideal (MvPolynomial ι K))
  (hQ : Q.IsHomogeneous (homogeneousSubmodule ι K)) (p : ι)
  (e : (MvPolynomial ι K ⧸ (Q ⊔ Ideal.span {X p-1})) ≃ₐ[K] MvPolynomial N K)

def polynomialChartIso :
    (Proj.basicOpen (HomogeneousQuotientProjective.grading Q hQ)
      (Ideal.Quotient.mk Q (X p))).toScheme ≅
      𝔸(N; Spec (CommRingCat.of K)) :=
  projectiveBasicOpenIsoNormalized Q hQ p ≪≫
    Scheme.Spec.mapIso e.symm.toRingEquiv.toCommRingCatIso.op ≪≫
    (AffineSpace.SpecIso N (CommRingCat.of K)).symm

theorem polynomialChartIso_hom_over :
    (polynomialChartIso Q hQ p e).hom ≫
      (𝔸(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) =
      (Proj.basicOpen (HomogeneousQuotientProjective.grading Q hQ)
        (Ideal.Quotient.mk Q (X p))).ι ≫ structureMap Q hQ := by
  simp only [polynomialChartIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, AffineSpace.SpecIso_inv_over]
  have he := AlternatingForms.specAlgEquiv_hom_over e
  simp only [MvPolynomial.algebraMap_eq] at he
  exact (congrArg (fun f ↦ (projectiveBasicOpenIsoNormalized Q hQ p).hom ≫ f) he).trans
    (projectiveBasicOpenIsoNormalized_hom_over Q hQ p)

end PaperVerification.HomogeneousQuotientCharts
end
end
end ComponentSource_7

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.HomogeneousQuotientAffineChartOver"

section ComponentSource_8
/- Original module: PaperVerification.AlternatingFormsOddRationality -/


/-!
# Rationality of the actual odd common-isotropic schemes

The displayed basic open of the genuine Proj is isomorphic over `Spec K`
to affine space.  The coordinate-ring primality theorem proves that this
nonempty open is dense.  The conclusion is Mathlib's
`Scheme.IsRationalOver`, with the canonical ground-field structure map.
The one-plane boundary is handled by its ordinary Plucker big cell.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] [CharZero K]

def oddIsotropicBigCellPolynomialIso (k t : ℕ) (h : t+1 ≤ k) :
    (Proj.basicOpen (isotropicProjectiveGrading (t := t) (oddPluckerForms (K := K) k))
      (Ideal.Quotient.mk (isotropicPluckerIdeal (oddPluckerForms k))
        (X (oddAffinePivot k (t+1) h)))).toScheme ≅
      Spec (CommRingCat.of (MvPolynomial (OddAffineFreeVariable k (t+1) h) K)) :=
  isotropicProjBasicOpenIso (oddAffinePivot k (t+1) h) (oddPluckerForms k) ≪≫
    Scheme.Spec.mapIso (oddAffineChartEquiv k t h).symm.toRingEquiv.toCommRingCatIso.op

/-- The actual common-isotropic open chart is affine space over the
original coefficient field, through explicitly constructed polynomials. -/
def oddIsotropicBigCellAffineIso (k t : ℕ) (h : t+1 ≤ k) :
    (Proj.basicOpen (isotropicProjectiveGrading (t := t) (oddPluckerForms (K := K) k))
      (Ideal.Quotient.mk (isotropicPluckerIdeal (oddPluckerForms k))
        (X (oddAffinePivot k (t+1) h)))).toScheme ≅
      𝔸(OddAffineFreeVariable k (t+1) h; Spec (CommRingCat.of K)) :=
  oddIsotropicBigCellPolynomialIso k t h ≪≫
    (AffineSpace.SpecIso (OddAffineFreeVariable k (t+1) h) (CommRingCat.of K)).symm

theorem oddIsotropicBigCellAffineIso_over (k t : ℕ) (h : t+1 ≤ k) :
    (oddIsotropicBigCellAffineIso (K := K) k t h).hom ≫
      (𝔸(OddAffineFreeVariable k (t+1) h; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) =
      (Proj.basicOpen (isotropicProjectiveGrading (t := t) (oddPluckerForms (K := K) k))
        (Ideal.Quotient.mk (isotropicPluckerIdeal (oddPluckerForms k))
          (X (oddAffinePivot k (t+1) h)))).ι ≫ isotropicStructureMap (oddPluckerForms k) := by
  simp only [oddIsotropicBigCellAffineIso, oddIsotropicBigCellPolynomialIso,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, AffineSpace.SpecIso_inv_over]
  exact (congrArg (fun f ↦
      (isotropicProjBasicOpenIso (oddAffinePivot k (t+1) h) (oddPluckerForms k)).hom ≫ f)
      (specAlgEquiv_hom_over (oddAffineChartEquiv k t h))).trans
    (isotropicProjBasicOpenIso_hom_over (oddAffinePivot k (t+1) h) (oddPluckerForms k))

theorem oddIsotropicBigCell_nonempty (k t : ℕ) (h : t+1 ≤ k) :
    (Proj.basicOpen (isotropicProjectiveGrading (t := t) (oddPluckerForms (K := K) k))
      (Ideal.Quotient.mk (isotropicPluckerIdeal (oddPluckerForms k))
        (X (oddAffinePivot k (t+1) h)))).carrier.Nonempty := by
  let x : Spec (CommRingCat.of (MvPolynomial (OddAffineFreeVariable k (t+1) h) K)) :=
    Classical.arbitrary _
  let y := (oddIsotropicBigCellPolynomialIso (K := K) k t h).inv x
  exact ⟨y.val,y.property⟩

theorem oddIsotropicBigCell_dense (k t : ℕ) (h : t+1 ≤ k) :
    Dense (Proj.basicOpen
      (isotropicProjectiveGrading (t := t) (oddPluckerForms (K := K) k))
      (Ideal.Quotient.mk (isotropicPluckerIdeal (oddPluckerForms k))
        (X (oddAffinePivot k (t+1) h)))).carrier := by
  letI : (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k)).IsPrime :=
    odd_isotropicPluckerIdeal_isPrime k t (by omega)
  exact projective_basicOpen_dense_of_nonempty _ _ (oddIsotropicBigCell_nonempty k t h)

/-- The rationality clause of Theorem 4.1 in every odd ambient dimension
and every common-isotropic plane dimension at least two in its full range. -/
theorem paper_theorem_4_1_rationality_at_least_two (k t : ℕ) (h : t+1 ≤ k) :
    Scheme.IsRationalOver
      (isotropicStructureMap (t := t) (oddPluckerForms (K := K) k)) :=
  scheme_isRationalOver_of_dense_affine_chart _ _
    (oddIsotropicBigCell_dense k t h) (OddAffineFreeVariable k (t+1) h)
    (oddIsotropicBigCellAffineIso k t h) (oddIsotropicBigCellAffineIso_over k t h)

/-- Classical rationality with an explicitly finite affine-space witness.
Mathlib's `IsRationalOver` alone does not require its index to be finite. -/
theorem paper_theorem_4_1_finite_rationality_at_least_two
    (k t : ℕ) (h : t+1 ≤ k) :
    ∃ N : Type, Finite N ∧ Scheme.BirationalOver
      (isotropicStructureMap (t := t) (oddPluckerForms (K := K) k))
      (𝔸(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) := by
  refine ⟨OddAffineFreeVariable k (t+1) h, inferInstance, ?_⟩
  exact scheme_birationalOver_affine_of_dense_chart _ _
    (oddIsotropicBigCell_dense k t h) (OddAffineFreeVariable k (t+1) h)
    (oddIsotropicBigCellAffineIso k t h) (oddIsotropicBigCellAffineIso_over k t h)

/-- The same canonical structure map for the one-plane boundary. -/
def onePlaneStructureMap (k : ℕ) :
    Proj (HomogeneousQuotientProjective.grading
      (matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1))
      (matrixPluckerIdeal_isHomogeneous (by decide : 0<1))) ⟶ Spec (CommRingCat.of K) :=
  HomogeneousQuotientCharts.structureMap _ _

def onePlaneAffineIso (k : ℕ) (p : PluckerIndex 1 (2*k+1)) :
    (Proj.basicOpen
      (HomogeneousQuotientProjective.grading (matrixPluckerIdeal (K := K))
        (matrixPluckerIdeal_isHomogeneous (by decide : 0<1)))
      (Ideal.Quotient.mk matrixPluckerIdeal (X p))).toScheme ≅
      𝔸(PluckerChartVariable p; Spec (CommRingCat.of K)) :=
  HomogeneousQuotientCharts.polynomialChartIso
    matrixPluckerIdeal (matrixPluckerIdeal_isHomogeneous (by decide : 0<1)) p
    (pluckerBigCellEquiv (K := K) p)

theorem onePlaneAffineIso_over (k : ℕ) (p : PluckerIndex 1 (2*k+1)) :
    (onePlaneAffineIso (K := K) k p).hom ≫
      (𝔸(PluckerChartVariable p; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) =
      (Proj.basicOpen
        (HomogeneousQuotientProjective.grading (matrixPluckerIdeal (K := K))
          (matrixPluckerIdeal_isHomogeneous (by decide : 0<1)))
        (Ideal.Quotient.mk matrixPluckerIdeal (X p))).ι ≫ onePlaneStructureMap k :=
  HomogeneousQuotientCharts.polynomialChartIso_hom_over
    matrixPluckerIdeal (matrixPluckerIdeal_isHomogeneous (by decide : 0<1)) p
    (pluckerBigCellEquiv (K := K) p)

/-- The one-plane case, including ambient dimension one, completes the
boundary of the rationality clause. -/
theorem paper_theorem_4_1_finite_rationality_one_plane (k : ℕ) :
    ∃ N : Type, Finite N ∧ Scheme.BirationalOver
      (onePlaneStructureMap (K := K) k)
      (𝔸(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) := by
  let p := onePlaneIndex (0 : Fin (2*k+1))
  let U := Proj.basicOpen
    (HomogeneousQuotientProjective.grading (matrixPluckerIdeal (K := K))
      (matrixPluckerIdeal_isHomogeneous (by decide : 0<1)))
    (Ideal.Quotient.mk matrixPluckerIdeal (X p))
  letI : (matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1)).IsPrime :=
    onePlane_ideal_isPrime _
  have hU : U.carrier.Nonempty := by
    let x : Spec (CommRingCat.of (MvPolynomial (PluckerChartVariable p) K)) :=
      Classical.arbitrary _
    let a := (AffineSpace.SpecIso (PluckerChartVariable p) (CommRingCat.of K)).inv x
    let y := (onePlaneAffineIso (K := K) k p).inv a
    exact ⟨y.val,y.property⟩
  refine ⟨PluckerChartVariable p, inferInstance, ?_⟩
  exact scheme_birationalOver_affine_of_dense_chart _ U
    (projective_basicOpen_dense_of_nonempty _ _ hU) (PluckerChartVariable p)
    (onePlaneAffineIso k p) (onePlaneAffineIso_over k p)

/-- The standard library rationality class follows from the stronger
finite-dimensional statement. -/
theorem paper_theorem_4_1_rationality_one_plane (k : ℕ) :
    Scheme.IsRationalOver (onePlaneStructureMap (K := K) k) := by
  obtain ⟨N, _, hN⟩ := paper_theorem_4_1_finite_rationality_one_plane (K := K) k
  exact ⟨N, hN⟩

end PaperVerification.AlternatingForms
end
end
end ComponentSource_8

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsOddRationality"

section ComponentSource_9
/- Original module: PaperVerification.AlternatingFormsOddAffineDimension -/


/-!
# The number of coordinates in the odd rational chart

The remaining columns are exactly those numbered at least `2*r+1` in the
zero-based path convention.  Their entries form a rectangular array with
`r+1` rows and `2*(k-r)` columns.  The resulting birationality witness has
precisely the paper's dimension `2*s*(k+1-s)`, where `s=r+1`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

private theorem oddAffine_free_column_ge (k r : ℕ) (h : r ≤ k)
    (j : Fin (2*k+1)) (hnp : j ∉ Set.range (oddAffinePivot k r h).val)
    (hnh : ¬oddAffineIsHead r j) : 2*r+1 ≤ j.val := by
  by_contra hj
  by_cases heven : j.val % 2 = 0
  · apply hnp
    refine ⟨⟨j.val/2, by omega⟩, ?_⟩
    apply Fin.ext
    change 2 * (j.val / 2) = j.val
    omega
  · apply hnh
    exact ⟨by omega, by omega⟩

/-- The free chart entries are literally a rectangular array. -/
def oddAffineFreeVariableEquiv (k r : ℕ) (h : r ≤ k) :
    OddAffineFreeVariable k r h ≃ Fin (r+1) × Fin (2*(k-r)) where
  toFun a := (a.val.1, ⟨a.val.2.val.val - (2*r+1), by
    have ht := oddAffine_free_column_ge k r h a.val.2.val a.val.2.property a.property
    have hj := a.val.2.val.isLt
    omega⟩)
  invFun a := ⟨(a.1, ⟨⟨2*r+1+a.2.val, by have := a.2.isLt; omega⟩, by
    rintro ⟨i, hi⟩
    have hi' := congrArg Fin.val hi
    change 2*i.val = 2*r+1+a.2.val at hi'
    have := i.isLt
    omega⟩), by
      intro hh
      have := hh.2
      change (2*r+1+a.2.val)/2 < r at this
      omega⟩
  left_inv a := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      apply Fin.ext
      have ht := oddAffine_free_column_ge k r h a.val.2.val a.val.2.property a.property
      dsimp only
      omega
  right_inv a := by
    apply Prod.ext
    · rfl
    · apply Fin.ext
      dsimp only
      omega

/-- The chart has the full expected number of independent polynomial variables. -/
theorem card_oddAffineFreeVariable (k r : ℕ) (h : r ≤ k) :
    Fintype.card (OddAffineFreeVariable k r h) = 2*(r+1)*(k-r) := by
  rw [Fintype.card_congr (oddAffineFreeVariableEquiv k r h),
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  ring

variable {K : Type} [Field K] [CharZero K]

/-- Rationality with a finite affine witness of exactly the paper's dimension.
The morphisms still commute with the original structure map to `Spec K`. -/
theorem paper_theorem_4_1_rationality_with_dimension_at_least_two
    (k t : ℕ) (h : t+1 ≤ k) :
    ∃ N : Type, Finite N ∧ Nat.card N = 2*(t+2)*(k-(t+1)) ∧ Scheme.BirationalOver
      (isotropicStructureMap (t := t) (oddPluckerForms (K := K) k))
      (𝔸(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) := by
  refine ⟨OddAffineFreeVariable k (t+1) h, inferInstance, ?_, ?_⟩
  · simpa only [Nat.card_eq_fintype_card, Nat.add_assoc] using
      card_oddAffineFreeVariable k (t+1) h
  · exact scheme_birationalOver_affine_of_dense_chart _ _
      (oddIsotropicBigCell_dense k t h) (OddAffineFreeVariable k (t+1) h)
      (oddIsotropicBigCellAffineIso k t h) (oddIsotropicBigCellAffineIso_over k t h)

end PaperVerification.AlternatingForms
end
end
end ComponentSource_9

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsOddAffineDimension"

section ComponentSource_10
/- Original module: PaperVerification.AlternatingFormsSectionFourCoordinates -/


/-!
# The coordinate convention in Section 4

In path coordinates `(b₀,a₁,b₁,…,aₖ,bₖ)`, the Section 4 pair `(f,g)` is
`(G,-F)`. The displayed exterior sums and equality of the actual homogeneous
isotropy ideals make this coordinate identification explicit.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial
open scoped BigOperators

variable {K : Type*} [Field K]

/-- The Section 4 forms, written in the interleaved path coordinate order. -/
def sectionFourPluckerForms (k : ℕ) (l : Fin 2) : StrictPairs (2*k+1) → K :=
  if l = 0 then oddPluckerForms k 1 else -oddPluckerForms k 0

theorem twoFormOfCoefficients_neg_form {M : Type*} [AddCommGroup M] [Module K M]
    {n : ℕ} (f : StrictPairs n → K) (z : Fin n → M) :
    twoFormOfCoefficients (-f) z = -twoFormOfCoefficients f z := by
  unfold twoFormOfCoefficients
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  change (-f a) • exteriorPair (z a.val.1) (z a.val.2) =
    -(f a • exteriorPair (z a.val.1) (z a.val.2))
  exact _root_.neg_smul (f a) (exteriorPair (z a.val.1) (z a.val.2))

private theorem sectionFour_exteriorPair_swap {M : Type*}
    [AddCommGroup M] [Module K M] (u v : M) :
    exteriorPair (K := K) u v = -exteriorPair v u := by
  apply Subtype.ext
  simp only [exteriorPair_coe, Submodule.coe_neg]
  exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap u v)

/-- The first form is literally `Σ aᵢ ∧ bᵢ`. -/
theorem sectionFour_first_coefficients {M : Type*} [AddCommGroup M] [Module K M]
    (k : ℕ) (z : Fin (2*k+1) → M) :
    twoFormOfCoefficients (sectionFourPluckerForms (K := K) k 0) z =
      ∑ i : Fin k, exteriorPair (z (oddAffineOddVertex k i))
        (z (oddAffineEvenVertex k i.succ)) := by
  rw [sectionFourPluckerForms, if_pos rfl, oddPluckerForms_twoForm]
  rfl

/-- The second form is literally `Σ aᵢ ∧ bᵢ₋₁`. -/
theorem sectionFour_second_coefficients {M : Type*} [AddCommGroup M] [Module K M]
    (k : ℕ) (z : Fin (2*k+1) → M) :
    twoFormOfCoefficients (sectionFourPluckerForms (K := K) k 1) z =
      ∑ i : Fin k, exteriorPair (z (oddAffineOddVertex k i))
        (z (oddAffineEvenVertex k i.castSucc)) := by
  rw [sectionFourPluckerForms, if_neg (by decide : (1 : Fin 2) ≠ 0),
    twoFormOfCoefficients_neg_form, oddPluckerForms_twoForm, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact (sectionFour_exteriorPair_swap _ _).symm

theorem pluckerIsotropyEquation_neg_form {t n : ℕ}
    (f : StrictPairs n → K) (J : Fin t → Fin n) :
    pluckerIsotropyEquation (-f) J = -pluckerIsotropyEquation f J := by
  simp only [pluckerIsotropyEquation, Pi.neg_apply, _root_.neg_smul, Finset.sum_neg_distrib]

private theorem isotropy_equation_mem {t n m : ℕ}
    (forms : Fin m → StrictPairs n → K) (l : Fin m) (J : Fin t → Fin n) :
    pluckerIsotropyEquation (forms l) J ∈ isotropicPluckerIdeal forms :=
by
  apply (show Ideal.span (Set.range fun a : Fin m × (Fin t → Fin n) =>
    pluckerIsotropyEquation (forms a.1) a.2) ≤ isotropicPluckerIdeal forms from
      le_sup_right)
  exact Ideal.subset_span ⟨(l,J), rfl⟩

/-- Changing `(F,G)` to the literal Section 4 pair `(G,-F)` preserves the
actual homogeneous ideal, hence the projective zero scheme with its scheme structure. -/
theorem sectionFour_isotropicPluckerIdeal (k t : ℕ) :
    isotropicPluckerIdeal (t := t) (sectionFourPluckerForms (K := K) k) =
      isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k) := by
  apply le_antisymm
  · refine sup_le le_sup_left (Ideal.span_le.mpr ?_)
    rintro q ⟨⟨l,J⟩,rfl⟩
    fin_cases l
    · simpa [sectionFourPluckerForms] using
        isotropy_equation_mem (oddPluckerForms (K := K) k) 1 J
    · simpa [sectionFourPluckerForms, pluckerIsotropyEquation_neg_form] using
        (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)).neg_mem
          (isotropy_equation_mem (oddPluckerForms (K := K) k) 0 J)
  · refine sup_le le_sup_left (Ideal.span_le.mpr ?_)
    rintro q ⟨⟨l,J⟩,rfl⟩
    fin_cases l
    · simpa [sectionFourPluckerForms, pluckerIsotropyEquation_neg_form] using
        (isotropicPluckerIdeal (t := t) (sectionFourPluckerForms (K := K) k)).neg_mem
          (isotropy_equation_mem (sectionFourPluckerForms (K := K) k) 1 J)
    · simpa [sectionFourPluckerForms] using
        isotropy_equation_mem (sectionFourPluckerForms (K := K) k) 0 J

end PaperVerification.AlternatingForms
end
end
end ComponentSource_10

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsSectionFourCoordinates"

section ComponentSource_11
/- Original module: PaperVerification.AlternatingFormsLiteralSectionFourRationality -/


/-!
# Rationality for the literal Section 4 coefficients

The existing coordinate comparison proves equality of the two actual
homogeneous ideals. Packaging an ideal together with its homogeneity proof
lets that equality transport the full scheme-theoretic birationality
statement, including its original ground-field structure morphism.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] [CharZero K]

/-- The finite-dimensional rationality assertion for the literal pair of
forms printed in Section 4, with no implicit coordinate convention left
for the reader to transport. -/
theorem paper_theorem_4_1_section_four_finite_rationality
    (k t : ℕ) (h : t+1 ≤ k) :
    ∃ N : Type, Finite N ∧ Nat.card N = 2*(t+2)*(k-(t+1)) ∧ Scheme.BirationalOver
      (isotropicStructureMap (t := t) (sectionFourPluckerForms (K := K) k))
      (𝔸(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) := by
  let H := {Q : Ideal (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K) //
    Q.IsHomogeneous (homogeneousSubmodule (PluckerIndex (t+2) (2*k+1)) K)}
  let P : H → Prop := fun Q =>
    ∃ N : Type, Finite N ∧ Nat.card N = 2*(t+2)*(k-(t+1)) ∧ Scheme.BirationalOver
      (HomogeneousQuotientCharts.structureMap Q.val Q.property)
      (𝔸(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K))
  let Q₁ : H := ⟨isotropicPluckerIdeal (t := t) (sectionFourPluckerForms (K := K) k),
    isotropicPluckerIdeal_isHomogeneous (sectionFourPluckerForms k)⟩
  let Q₂ : H := ⟨isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k),
    isotropicPluckerIdeal_isHomogeneous (oddPluckerForms k)⟩
  have hQ : Q₁ = Q₂ := Subtype.ext (sectionFour_isotropicPluckerIdeal k t)
  change P Q₁
  rw [hQ]
  exact paper_theorem_4_1_rationality_with_dimension_at_least_two k t h

/-- The standard rationality property follows from the stronger finite
birational witness for the exact Section 4 pair. -/
theorem paper_theorem_4_1_section_four_rationality
    (k t : ℕ) (h : t+1 ≤ k) :
    Scheme.IsRationalOver
      (isotropicStructureMap (t := t) (sectionFourPluckerForms (K := K) k)) := by
  obtain ⟨N, _, _, hN⟩ := paper_theorem_4_1_section_four_finite_rationality (K := K) k t h
  exact ⟨N, hN⟩

end PaperVerification.AlternatingForms
end
end
end ComponentSource_11

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsLiteralSectionFourRationality"

section ComponentSource_12
/- Original module: PaperVerification.JacobianRelativeDimension -/


/-!
# The relative dimension of a quotient with independent Jacobian rows

The minors used here belong to the original polynomial presentation. Inverting
one such minor gives a standard smooth presentation with exactly the expected
number of free coordinates. Independence over every maximal residue field makes
these principal opens cover the entire spectrum, including nonreduced bases.
-/

@[expose] public section
noncomputable section

universe u v w
open Algebra MvPolynomial
open scoped Matrix

namespace PaperVerification.JacobianRelativeDimension

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {ι : Type*} {κ : Type*} [Fintype ι] [Fintype κ]

/-- Localizing the chosen Jacobian minor turns the original presentation into a
standard smooth presentation of its original dimension. -/
theorem standardSmooth_away_jacobian (P : PreSubmersivePresentation R S ι κ) :
    IsStandardSmoothOfRelativeDimension (Fintype.card ι - Fintype.card κ)
      R (Localization.Away P.jacobian) := by
  classical
  let T := Localization.Away P.jacobian
  let Q := PreSubmersivePresentation.localizationAway T P.jacobian
  have hunit : IsUnit ((Q.comp P).jacobian) := by
    rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.smul_def]
    exact (IsLocalization.Away.algebraMap_isUnit P.jacobian).mul
      (by simpa only [Q, PreSubmersivePresentation.localizationAway_jacobian] using
        (IsLocalization.Away.algebraMap_isUnit P.jacobian :
          IsUnit (algebraMap S T P.jacobian)))
  let E : SubmersivePresentation R T (Unit ⊕ ι) (Unit ⊕ κ) :=
    { Q.comp P with jacobian_isUnit := hunit }
  apply E.isStandardSmoothOfRelativeDimension
  change (Q.comp P).dimension = _
  rw [PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension]
  simp [Q, Presentation.dimension, Nat.card_eq_fintype_card]

/-- The maximal minors generate the unit ideal when the rows are independent in
every maximal residue field. -/
theorem span_maximalMinors_eq_top [DecidableEq κ] (A : Matrix κ ι S)
    (hA : ∀ (J : Ideal S) [J.IsMaximal],
      LinearIndependent (S ⧸ J) (A.map (Ideal.Quotient.mk J))) :
    Ideal.span (Set.range (fun e : κ ↪ ι ↦ (A.submatrix id e).det)) = ⊤ := by
  classical
  by_contra h
  obtain ⟨J, hJ, hle⟩ := Ideal.exists_le_maximal _ h
  letI : J.IsMaximal := hJ
  letI : Field (S ⧸ J) := Ideal.Quotient.field J
  obtain ⟨e, he⟩ := Matrix.linearIndependent_row_iff_exists_det_submatrix_ne_zero.mp (hA J)
  have hmem : (A.submatrix id e).det ∈ J :=
    hle (Ideal.subset_span (Set.mem_range_self e))
  have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  apply he
  have hm : (Matrix.of (fun i j ↦ (Ideal.Quotient.mk J) (A i j))).submatrix id e =
      (Ideal.Quotient.mk J).mapMatrix (A.submatrix id e) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.map_apply, Matrix.of_apply,
      RingHom.mapMatrix_apply] <;> rfl
  rw [hm, ← RingHom.map_det]
  exact hz

variable {K : Type u} [CommRing K] {τ : Type u} {σ : Type u}
  [Fintype τ] [Fintype σ] [DecidableEq σ]

/-- The literal Jacobian of the literal quotient by the supplied polynomials. -/
def quotientJacobian (f : σ → MvPolynomial τ K) :
    Matrix σ τ (MvPolynomial τ K ⧸ Ideal.span (Set.range f)) :=
  fun j t ↦ Ideal.Quotient.mk _ (pderiv t (f j))

/-- The chosen pre-submersive Jacobian is precisely the corresponding original
maximal minor; its transpose has the same determinant. -/
theorem naive_jacobian_eq_minor (f : σ → MvPolynomial τ K) (e : σ ↪ τ) :
    (PreSubmersivePresentation.naive (v := f) e e.injective).jacobian =
      ((quotientJacobian f).submatrix id e).det := by
  classical
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    RingHom.map_det]
  let P := PreSubmersivePresentation.naive (v := f) e e.injective
  have hmatrix : (algebraMap P.Ring (MvPolynomial τ K ⧸ Ideal.span (Set.range f))).mapMatrix
      P.jacobiMatrix = ((quotientJacobian f).submatrix id e).transpose := by
    ext i j
    simp only [P, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      PreSubmersivePresentation.jacobiMatrix_naive, Matrix.transpose_apply,
      Matrix.submatrix_apply, id_eq, quotientJacobian] <;> rfl
  exact (congrArg Matrix.det hmatrix).trans (Matrix.det_transpose _)

/-- A polynomial quotient whose original Jacobian rows are independent in every
maximal residue field is locally standard smooth of the full expected relative
dimension. No reducedness or regular-sequence hypothesis is introduced. -/
theorem locally_standardSmoothOfRelativeDimension
    (f : σ → MvPolynomial τ K)
    (hJ : ∀ (J : Ideal (MvPolynomial τ K ⧸ Ideal.span (Set.range f))) [J.IsMaximal],
      LinearIndependent ((MvPolynomial τ K ⧸ Ideal.span (Set.range f)) ⧸ J)
        ((quotientJacobian f).map (Ideal.Quotient.mk J))) :
    RingHom.Locally
      (RingHom.IsStandardSmoothOfRelativeDimension (Fintype.card τ - Fintype.card σ))
      (algebraMap K (MvPolynomial τ K ⧸ Ideal.span (Set.range f))) := by
  classical
  let S := MvPolynomial τ K ⧸ Ideal.span (Set.range f)
  let minor : (σ ↪ τ) → S := fun e ↦ ((quotientJacobian f).submatrix id e).det
  refine ⟨Set.range minor, span_maximalMinors_eq_top _ hJ, ?_⟩
  rintro z ⟨e, rfl⟩
  rw [← IsScalarTower.algebraMap_eq K S (Localization.Away (minor e)),
    RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  have h := standardSmooth_away_jacobian
    (PreSubmersivePresentation.naive (v := f) e e.injective)
  have he : (PreSubmersivePresentation.naive (v := f) e e.injective).jacobian = minor e :=
    naive_jacobian_eq_minor f e
  rw [he] at h
  exact h

end PaperVerification.JacobianRelativeDimension
end
end
end ComponentSource_12

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.JacobianRelativeDimension"

section ComponentSource_13
/- Original module: PaperVerification.GenericSectionResidueJacobian -/


/-!
# Residue-field Jacobian rows on the same generic parameter open

This exposes the residue calculation used inside generic smoothness. The
avoidance polynomial and the literal defining equations are unchanged.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open KaehlerDifferential

namespace PaperVerification.GenericSectionDifferentials

variable {K R ι κ τ : Type*} [Field K] [CharZero K] [CommRing R]
  [Algebra K R] [Fintype ι] [Fintype κ] [Fintype τ] [DecidableEq κ]

/-- The defining Jacobian has independent rows in every residue field on the
already constructed principal open; no smoothness of the quotient is assumed. -/
theorem linearSection_residue_gradient_rows [Algebra.FiniteType K R]
    (b : Module.Basis τ R Ω[R⁄K]) (v : Matrix κ ι R)
    (u : Matrix ι κ R) (hvu : v * u = 1) (a : ι → K)
    (ha : MvPolynomial.aeval a (criticalAvoidancePolynomial b v u hvu) ≠ 0)
    (J : Ideal (R ⧸ Ideal.span (Set.range (linearSection v a)))) [J.IsMaximal] :
    LinearIndependent ((R ⧸ Ideal.span (Set.range (linearSection v a))) ⧸ J)
      (Matrix.map (fun j t => Ideal.Quotient.mk (Ideal.span (Set.range (linearSection v a)))
        (b.repr (D K R (linearSection v a j)) t) :
          Matrix κ τ (R ⧸ Ideal.span (Set.range (linearSection v a))))
            (Ideal.Quotient.mk J)) := by
  classical
  let I := Ideal.span (Set.range (linearSection v a))
  let S := R ⧸ I
  let L := S ⧸ J
  letI : Field L := Ideal.Quotient.field J
  let χ : R →ₐ[K] L := (Ideal.Quotient.mkₐ K J).comp (Ideal.Quotient.mkₐ K I)
  let a' : ι → L := fun i => algebraMap K L (a i)
  have ha' : MvPolynomial.aeval a' (criticalAvoidancePolynomial b v u hvu) ≠ 0 := by
    have he : algebraMap K L (MvPolynomial.aeval a (criticalAvoidancePolynomial b v u hvu)) =
        MvPolynomial.aeval a' (criticalAvoidancePolynomial b v u hvu) := by
      simpa only [Algebra.ofId_apply,a'] using
        (MvPolynomial.comp_aeval_apply a (Algebra.ofId K L)
          (criticalAvoidancePolynomial b v u hvu))
    rw [← he]
    intro h
    exact ha ((algebraMap K L).injective (h.trans (map_zero _).symm))
  have hz : ∀ j, ∑ i, a' i * χ (v j i) = 0 := by
    intro j
    have hz' : algebraMap R S (linearSection v a j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self j))
    have h : χ (linearSection v a j) = 0 := by
      change Ideal.Quotient.mk J (algebraMap R S (linearSection v a j)) = 0
      rw [hz',map_zero]
    simpa only [linearSection,map_sum,Algebra.smul_def,map_mul,AlgHom.commutes,a'] using h
  have hind := specialized_gradient_linearIndependent b v u hvu χ a' ha' hz
  convert hind using 1
  funext j t
  change χ (b.repr (D K R (linearSection v a j)) t) = _
  rw [linearSection_gradient]
  simp only [map_sum,a',Algebra.smul_def,map_mul,AlgHom.commutes]

/-- For a polynomial chart, these are exactly the rows of the matrix of
formal partial derivatives of the original equations. -/
theorem linearSection_residue_pderiv_rows
    (v : Matrix κ ι (MvPolynomial τ K))
    (u : Matrix ι κ (MvPolynomial τ K)) (hvu : v * u = 1) (a : ι → K)
    (ha : MvPolynomial.aeval a (criticalAvoidancePolynomial
      (KaehlerDifferential.mvPolynomialBasis K τ) v u hvu) ≠ 0)
    (J : Ideal (MvPolynomial τ K ⧸ Ideal.span (Set.range (linearSection v a))))
    [J.IsMaximal] :
    LinearIndependent ((MvPolynomial τ K ⧸ Ideal.span (Set.range (linearSection v a))) ⧸ J)
      (Matrix.map (fun j t => Ideal.Quotient.mk (Ideal.span (Set.range (linearSection v a)))
        (MvPolynomial.pderiv t (linearSection v a j)) :
          Matrix κ τ (MvPolynomial τ K ⧸ Ideal.span (Set.range (linearSection v a))))
            (Ideal.Quotient.mk J)) := by
  simpa only [KaehlerDifferential.mvPolynomialBasis_repr_apply] using
    linearSection_residue_gradient_rows
      (KaehlerDifferential.mvPolynomialBasis K τ) v u hvu a ha J

end PaperVerification.GenericSectionDifferentials
end
end
end ComponentSource_13

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.GenericSectionResidueJacobian"

section ComponentSource_14
/- Original module: PaperVerification.GenericPolynomialSectionDimension -/


/-!
# Expected relative dimension on the actual generic parameter open

The avoidance polynomial is the same one used for generic smoothness. The
result applies to the literal ideal quotient by the original specialized
equations, with no regularity or dimension assumption on that quotient.
-/

@[expose] public section
noncomputable section

universe u

namespace PaperVerification.GenericSectionDifferentials

variable {K ι κ τ : Type u} [Field K] [CharZero K]
  [Fintype ι] [Fintype κ] [Fintype τ] [DecidableEq κ]

/-- The same nonempty principal parameter open gives smooth quotients of the
full expected relative dimension, not merely smooth quotients. -/
theorem linearSection_quotient_locally_standardSmoothOfRelativeDimension
    (v : Matrix κ ι (MvPolynomial τ K))
    (u : Matrix ι κ (MvPolynomial τ K)) (hvu : v * u = 1) (a : ι → K)
    (ha : MvPolynomial.aeval a (criticalAvoidancePolynomial
      (KaehlerDifferential.mvPolynomialBasis K τ) v u hvu) ≠ 0) :
    RingHom.Locally
      (RingHom.IsStandardSmoothOfRelativeDimension (Fintype.card τ - Fintype.card κ))
      (algebraMap K (MvPolynomial τ K ⧸ Ideal.span (Set.range (linearSection v a)))) := by
  apply JacobianRelativeDimension.locally_standardSmoothOfRelativeDimension
  intro J hJ
  exact linearSection_residue_pderiv_rows v u hvu a ha J

end PaperVerification.GenericSectionDifferentials
end
end
end ComponentSource_14

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.GenericPolynomialSectionDimension"

section ComponentSource_15
/- Original module: PaperVerification.AlternatingFormsChartEvaluation -/


/-!
# Split evaluation on every Grassmannian chart

The independent coefficients of every alternating form are the parameters.
On a Plücker chart the pivot columns are the identity. Restricting the ambient
coordinate two-forms supported on pairs of pivot columns therefore gives all
coordinate two-forms on the tautological plane. The matrices below record this
splitting for any finite number of alternating forms.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Matrix

namespace PaperVerification.AlternatingForms

variable {K : Type*} [Field K] {t n m : ℕ}

/-- A pair of row indices determines the corresponding pair of pivot columns. -/
def chartPivotPair (p : PluckerIndex (t+2) n) (a : StrictPairs (t+2)) : StrictPairs n :=
  ⟨(p.val a.val.1,p.val a.val.2),p.property a.property⟩

/-- Restriction of a pivot-coordinate two-form to the row-reduced plane. -/
lemma chart_pivot_twoByTwo (p : PluckerIndex (t+2) n)
    (a b : StrictPairs (t+2)) :
    pluckerChartMatrix (K:=K) p a.val.1 (p.val b.val.1) *
        pluckerChartMatrix (K:=K) p a.val.2 (p.val b.val.2) -
      pluckerChartMatrix (K:=K) p a.val.1 (p.val b.val.2) *
        pluckerChartMatrix (K:=K) p a.val.2 (p.val b.val.1) =
      if a=b then 1 else 0 := by
  classical
  have he (i j : Fin (t+2)) : pluckerChartMatrix (K:=K) p i (p.val j) =
      (1 : Matrix (Fin (t+2)) (Fin (t+2))
        (MvPolynomial (PluckerChartVariable p) K)) i j :=
    congrFun (congrFun (pluckerChartMatrix_pivot (K:=K) p) i) j
  simp only [he,Matrix.one_apply]
  by_cases hab : a=b
  · subst b
    simp [a.property.ne,a.property.ne.symm]
  · have hdiag : ¬ (a.val.1=b.val.1 ∧ a.val.2=b.val.2) := by
      rintro ⟨h₁,h₂⟩
      exact hab (Subtype.ext (Prod.ext h₁ h₂))
    have hrev : ¬ (a.val.1=b.val.2 ∧ a.val.2=b.val.1) := by
      rintro ⟨h₁,h₂⟩
      have ha := a.property
      rw [h₁,h₂] at ha
      exact lt_asymm ha b.property
    simp only [if_neg hab]
    split_ifs <;> simp_all

/-- Evaluation of all ambient alternating-form coefficients on the chart. -/
def chartSectionEvaluation (p : PluckerIndex (t+2) n) :
    Matrix (Fin m × StrictPairs (t+2)) (Fin m × StrictPairs n)
      (MvPolynomial (PluckerChartVariable p) K) :=
  fun a b => if a.1=b.1 then
    pluckerChartMatrix p a.2.val.1 b.2.val.1 *
        pluckerChartMatrix p a.2.val.2 b.2.val.2 -
      pluckerChartMatrix p a.2.val.1 b.2.val.2 *
        pluckerChartMatrix p a.2.val.2 b.2.val.1
    else 0

/-- Extending a row-coordinate two-form by its pivot-coordinate two-form. -/
def chartSectionExtension (p : PluckerIndex (t+2) n) :
    Matrix (Fin m × StrictPairs n) (Fin m × StrictPairs (t+2))
      (MvPolynomial (PluckerChartVariable p) K) :=
  fun b a => if b=(a.1,chartPivotPair p a.2) then 1 else 0

lemma chartSectionEvaluation_pivot (p : PluckerIndex (t+2) n)
    (a b : Fin m × StrictPairs (t+2)) :
    chartSectionEvaluation (K:=K) p a (b.1,chartPivotPair p b.2) =
      if a=b then 1 else 0 := by
  classical
  simp only [chartSectionEvaluation,chartPivotPair,chart_pivot_twoByTwo]
  by_cases h₁ : a.1=b.1 <;> by_cases h₂ : a.2=b.2 <;>
    simp_all [Prod.ext_iff]

/-- The evaluation map is split surjective over the entire affine chart. -/
theorem chartSectionEvaluation_rightInverse (p : PluckerIndex (t+2) n) :
    chartSectionEvaluation (K:=K) (m:=m) p * chartSectionExtension (K:=K) (m:=m) p = 1 := by
  classical
  ext a b
  simp only [Matrix.mul_apply,chartSectionExtension,mul_ite,mul_one,mul_zero]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true,
    chartSectionEvaluation_pivot,Matrix.one_apply]

/-- The corresponding linear section is exactly the original row-isotropy
equation, with every ambient coefficient retained as a free parameter. -/
theorem chartSectionEvaluation_sum (p : PluckerIndex (t+2) n)
    (a : (Fin m × StrictPairs n) → K) (j : Fin m × StrictPairs (t+2)) :
    (∑ i, a i • chartSectionEvaluation (K:=K) p j i) =
      alternatingRowPair (fun b => a (j.1,b)) (pluckerChartMatrix p)
        j.2.val.1 j.2.val.2 := by
  classical
  simp only [Fintype.sum_prod_type,chartSectionEvaluation,smul_ite,smul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true,alternatingRowPair]

end PaperVerification.AlternatingForms
end
end
end ComponentSource_15

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsChartEvaluation"

section ComponentSource_16
/- Original module: PaperVerification.AlternatingFormsGenericChartSmoothness -/


/-!
# A genuine generic-smoothness polynomial for all isotropic charts

The parameter space is the full space of `m` alternating forms. For fixed
ambient and plane dimensions, one nonzero polynomial works simultaneously on
every Plücker chart. The quotient rings are the original row-isotropy rings;
their ideals are neither radicalized nor replaced by simplified equations.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open KaehlerDifferential

namespace PaperVerification.AlternatingForms

open GenericSectionDifferentials

variable {K : Type*} [Field K] [CharZero K] {t n m : ℕ}

/-- The bad-parameter polynomial on one standard Grassmannian chart. -/
def isotropicChartSmoothnessPolynomial (p : PluckerIndex (t+2) n) :
    MvPolynomial (Fin m × StrictPairs n) K :=
  criticalAvoidancePolynomial
    (KaehlerDifferential.mvPolynomialBasis K (PluckerChartVariable p))
    (chartSectionEvaluation (K:=K) (m:=m) p) (chartSectionExtension (K:=K) (m:=m) p)
    (chartSectionEvaluation_rightInverse (K:=K) (m:=m) p)

theorem isotropicChartSmoothnessPolynomial_ne_zero (p : PluckerIndex (t+2) n) :
    isotropicChartSmoothnessPolynomial (K:=K) (m:=m) p ≠ 0 :=
  criticalAvoidancePolynomial_ne_zero _ _ _ _

/-- Nonvanishing of the chart polynomial implies actual algebraic smoothness. -/
theorem isotropicChartRing_smooth_of_polynomial
    (p : PluckerIndex (t+2) n) (a : (Fin m × StrictPairs n) → K)
    (ha : MvPolynomial.aeval a (isotropicChartSmoothnessPolynomial (K:=K) (m:=m) p) ≠ 0) :
    Algebra.Smooth K (IsotropicChartRing p (fun l i => a (l,i))) := by
  classical
  have h := linearSection_quotient_smooth
    (KaehlerDifferential.mvPolynomialBasis K (PluckerChartVariable p))
    (chartSectionEvaluation (K:=K) (m:=m) p) (chartSectionExtension (K:=K) (m:=m) p)
    (chartSectionEvaluation_rightInverse (K:=K) (m:=m) p) a ha
  have hf : linearSection (chartSectionEvaluation (K:=K) (m:=m) p) a =
      fun j : Fin m × StrictPairs (t+2) =>
        alternatingRowPair (fun i => a (j.1,i)) (pluckerChartMatrix (K:=K) p)
          j.2.val.1 j.2.val.2 := by
    funext j
    exact chartSectionEvaluation_sum p a j
  rw [hf] at h
  exact h

/-- One polynomial for the entire finite Grassmannian atlas. -/
def isotropicSmoothnessPolynomial (t n m : ℕ) :
    MvPolynomial (Fin m × StrictPairs n) K :=
  ∏ p : PluckerIndex (t+2) n, isotropicChartSmoothnessPolynomial (K:=K) (m:=m) p

theorem isotropicSmoothnessPolynomial_ne_zero (t n m : ℕ) :
    isotropicSmoothnessPolynomial (K:=K) t n m ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact isotropicChartSmoothnessPolynomial_ne_zero p

/-- Every original affine chart of the common-isotropic scheme is smooth on
the same principal open of the full coefficient space. -/
theorem isotropic_all_charts_smooth (t n m : ℕ)
    (a : (Fin m × StrictPairs n) → K)
    (ha : MvPolynomial.aeval a (isotropicSmoothnessPolynomial (K:=K) t n m) ≠ 0) :
    ∀ p : PluckerIndex (t+2) n,
      Algebra.Smooth K (IsotropicChartRing p (fun l i => a (l,i))) := by
  classical
  intro p
  apply isotropicChartRing_smooth_of_polynomial p a
  rw [isotropicSmoothnessPolynomial,map_prod] at ha
  exact (Finset.prod_ne_zero_iff.mp ha) p (Finset.mem_univ p)

/-- The simultaneous good locus has a point over the original field. -/
theorem exists_isotropic_all_charts_smooth (t n m : ℕ) :
    ∃ a : (Fin m × StrictPairs n) → K,
      MvPolynomial.aeval a (isotropicSmoothnessPolynomial (K:=K) t n m) ≠ 0 ∧
      ∀ p : PluckerIndex (t+2) n,
        Algebra.Smooth K (IsotropicChartRing p (fun l i => a (l,i))) := by
  classical
  letI : Infinite K := Infinite.of_injective Nat.cast Nat.cast_injective
  have hex : ∃ a : (Fin m × StrictPairs n) → K,
      MvPolynomial.aeval a (isotropicSmoothnessPolynomial (K:=K) t n m) ≠ 0 := by
    by_contra h
    push Not at h
    apply isotropicSmoothnessPolynomial_ne_zero (K:=K) t n m
    apply MvPolynomial.funext
    intro a
    simpa only [map_zero,MvPolynomial.aeval_eq_eval] using h a
  obtain ⟨a,ha⟩ := hex
  exact ⟨a,ha,isotropic_all_charts_smooth t n m a ha⟩

end PaperVerification.AlternatingForms
end
end
end ComponentSource_16

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsGenericChartSmoothness"

section ComponentSource_17
/- Original module: PaperVerification.AlternatingFormsGenericSmoothness -/


/-!
# Generic smoothness of the actual common-isotropic projective scheme

The affine chart theorem is transported along the original chart isomorphisms,
which commute with the canonical map to `Spec K`. Smoothness is then descended
along their proved open cover. The parameter polynomial belongs to the full
coefficient space of all alternating forms.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory MvPolynomial

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K] [CharZero K]

/-- A nonzero polynomial in all form coefficients ensures that the genuine
common-isotropic scheme is smooth over its original coefficient field. -/
theorem isotropicStructureMap_smooth (t n m : ℕ)
    (a : (Fin m × StrictPairs n) → K)
    (ha : MvPolynomial.aeval a (isotropicSmoothnessPolynomial (K:=K) t n m) ≠ 0) :
    Smooth (isotropicStructureMap (t:=t) (fun l i => a (l,i))) := by
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P:=@AlgebraicGeometry.Smooth.{0})
    (fun p : PluckerIndex (t+2) n =>
      Proj.basicOpen (isotropicProjectiveGrading (t:=t) (fun l i => a (l,i)))
        (Ideal.Quotient.mk (isotropicPluckerIdeal (fun l i => a (l,i))) (X p)))
    (isotropicProjBasicOpen_cover (t:=t) (fun l i => a (l,i)))
  intro p
  rw [← isotropicProjBasicOpenIso_hom_over]
  letI : Algebra.Smooth K (IsotropicChartRing p (fun l i => a (l,i))) :=
    isotropic_all_charts_smooth t n m a ha p
  haveI : Smooth (Spec.map (CommRingCat.ofHom
      (algebraMap K (IsotropicChartRing p (fun l i => a (l,i)))))) :=
    (HasRingHomProperty.Spec_iff (P:=@Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr inferInstance)
  infer_instance

/-- The complete principal-open statement for any number of alternating
forms and any plane dimension at least two. Smoothness allows an empty zero
scheme; nonemptiness and expected dimension are separate conclusions. -/
theorem generic_commonIsotropic_smooth (t n m : ℕ) :
    ∃ Q : MvPolynomial (Fin m × StrictPairs n) K, Q ≠ 0 ∧
      (∃ a : (Fin m × StrictPairs n) → K, MvPolynomial.aeval a Q ≠ 0) ∧
      ∀ a : (Fin m × StrictPairs n) → K, MvPolynomial.aeval a Q ≠ 0 →
        Smooth (isotropicStructureMap (t:=t) (fun l i => a (l,i))) := by
  refine ⟨isotropicSmoothnessPolynomial (K:=K) t n m,
    isotropicSmoothnessPolynomial_ne_zero (K:=K) t n m, ?_, ?_⟩
  · obtain ⟨a,ha,_⟩ := exists_isotropic_all_charts_smooth (K:=K) t n m
    exact ⟨a,ha⟩
  · exact isotropicStructureMap_smooth t n m

end PaperVerification.AlternatingForms
end
end
end ComponentSource_17

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsGenericSmoothness"

section ComponentSource_18
/- Original module: PaperVerification.AlternatingFormsGenericNegativeDimension -/


/-!
# Generic emptiness in negative expected dimension

For any number of alternating forms, the expected dimension is the number
of Grassmannian chart variables minus the number of row-isotropy equations.
If it is negative, the generic section has the unit ideal on every chart.
The genuine projective common-isotropic scheme is consequently empty.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open AlgebraicGeometry MvPolynomial

namespace PaperVerification.AlternatingForms

open GenericSectionDifferentials

variable {K : Type*} [Field K] [CharZero K] {t n m : ℕ}

private lemma chart_variable_count (p : PluckerIndex (t+2) n) :
    Fintype.card (PluckerChartVariable p) = (t+2)*(n-(t+2)) := by
  classical
  have h : Fintype.card (Set.range p.val)=t+2 := by
    simpa only [Fintype.card_fin] using
      (Fintype.card_congr (Equiv.ofInjective p.val p.property.injective)).symm
  rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_subtype_compl,Fintype.card_fin,h]

/-- The original chart ideal is the unit ideal, without passing to its radical. -/
theorem isotropicChartIdeal_eq_top_of_negative_dimension
    (p : PluckerIndex (t+2) n) (a : (Fin m × StrictPairs n) → K)
    (ha : MvPolynomial.aeval a (isotropicChartSmoothnessPolynomial (K:=K) (m:=m) p) ≠ 0)
    (hd : (t+2)*(n-(t+2)) < m*(t+2).choose 2) :
    isotropicChartIdeal p (fun l i => a (l,i)) = ⊤ := by
  classical
  have hc : Fintype.card (PluckerChartVariable p) <
      Fintype.card (Fin m × StrictPairs (t+2)) := by
    rw [chart_variable_count, Fintype.card_prod, Fintype.card_fin, card_strictPairs]
    exact hd
  have h := linearSection_ideal_eq_top_of_more_equations
    (KaehlerDifferential.mvPolynomialBasis K (PluckerChartVariable p))
    (chartSectionEvaluation (K:=K) (m:=m) p) (chartSectionExtension (K:=K) (m:=m) p)
    (chartSectionEvaluation_rightInverse (K:=K) (m:=m) p) a ha hc
  have hf : linearSection (chartSectionEvaluation (K:=K) (m:=m) p) a =
      fun j : Fin m × StrictPairs (t+2) =>
        alternatingRowPair (fun i => a (j.1,i)) (pluckerChartMatrix (K:=K) p)
          j.2.val.1 j.2.val.2 := by
    funext j
    exact chartSectionEvaluation_sum p a j
  rw [hf] at h
  exact h

/-- Empty original affine charts force the actual homogeneous-quotient Proj
to be empty by its established basic-open cover. -/
theorem isotropicProj_isEmpty_of_chartIdeals_eq_top
    (forms : Fin m → StrictPairs n → K)
    (h : ∀ p : PluckerIndex (t+2) n, isotropicChartIdeal p forms=⊤) :
    IsEmpty (Proj (isotropicProjectiveGrading (t:=t) forms)) := by
  classical
  constructor
  intro x
  have hx : x ∈ (⨆ p : PluckerIndex (t+2) n,
      Proj.basicOpen (isotropicProjectiveGrading (t:=t) forms)
        (Ideal.Quotient.mk (isotropicPluckerIdeal forms) (X p))) := by
    rw [isotropicProjBasicOpen_cover]
    trivial
  obtain ⟨p,hp⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  letI : Subsingleton (IsotropicChartRing p forms) :=
    Ideal.Quotient.subsingleton_iff.mpr (h p)
  let x' : PrimeSpectrum (IsotropicChartRing p forms) :=
    (isotropicProjBasicOpenIso p forms).hom ⟨x,hp⟩
  exact isEmptyElim x'

/-- A single nonempty principal open in the complete coefficient space has
empty common-isotropic scheme whenever its expected dimension is negative. -/
theorem generic_commonIsotropic_empty_of_negative_dimension (t n m : ℕ)
    (hd : (t+2)*(n-(t+2)) < m*(t+2).choose 2) :
    ∃ Q : MvPolynomial (Fin m × StrictPairs n) K, Q≠0 ∧
      (∃ a : (Fin m × StrictPairs n) → K, MvPolynomial.aeval a Q≠0) ∧
      ∀ a : (Fin m × StrictPairs n) → K, MvPolynomial.aeval a Q≠0 →
        IsEmpty (Proj (isotropicProjectiveGrading (t:=t) (fun l i => a (l,i)))) := by
  classical
  refine ⟨isotropicSmoothnessPolynomial (K:=K) t n m,
    isotropicSmoothnessPolynomial_ne_zero (K:=K) t n m, ?_, ?_⟩
  · obtain ⟨a,ha,_⟩ := exists_isotropic_all_charts_smooth (K:=K) t n m
    exact ⟨a,ha⟩
  · intro a ha
    apply isotropicProj_isEmpty_of_chartIdeals_eq_top
    intro p
    apply isotropicChartIdeal_eq_top_of_negative_dimension p a _ hd
    rw [isotropicSmoothnessPolynomial,map_prod] at ha
    exact (Finset.prod_ne_zero_iff.mp ha) p (Finset.mem_univ p)

end PaperVerification.AlternatingForms
end
end
end ComponentSource_18

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsGenericNegativeDimension"

section ComponentSource_19
/- Original module: PaperVerification.CommonIsotropicSubspace -/


/-!
# Common isotropic subspaces for two alternating forms

Any two alternating bilinear forms on an `n`-dimensional vector space over a field
of characteristic different from two have a common isotropic subspace of dimension
at least `ceil(n/2)`. The argument does not assume that the pencil is generic.

In odd dimension an alternating form has a nonzero radical vector. In even
dimension any nonzero vector suffices. Intersect its common orthogonal space with
a transverse hyperplane, apply dimension induction there, and add the chosen line.
-/

@[expose] public section
noncomputable section

universe u v
open Module
open LinearMap (BilinForm)
open scoped Matrix

namespace PaperVerification.CommonIsotropicSubspace

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]

/-- The usual total isotropy condition, including both arguments in the subspace. -/
def Isotropic (B : BilinForm K V) (U : Submodule K V) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, B x y = 0

/-- An alternating form on an odd-dimensional space has a nonzero radical vector. -/
theorem exists_radical_of_odd [FiniteDimensional K V] (h₂ : (2 : K) ≠ 0)
    (B : BilinForm K V) (hB : B.IsAlt) (hodd : Odd (finrank K V)) :
    ∃ v : V, v ≠ 0 ∧ ∀ w : V, B v w = 0 := by
  classical
  let b := Module.finBasis K V
  let A := BilinForm.toMatrix b B
  have hskew : A.transpose = -A := by
    ext i j
    simpa only [A, Matrix.transpose_apply, Matrix.neg_apply,
      BilinForm.toMatrix_apply] using (hB.neg_eq (b i) (b j)).symm
  have hdet : A.det = -A.det := by
    calc
      A.det = A.transpose.det := (Matrix.det_transpose A).symm
      _ = (-A).det := congrArg Matrix.det hskew
      _ = -A.det := by rw [Matrix.det_neg]; simp [hodd.neg_one_pow]
  have hz : A.det = 0 := by
    have h : (2 : K) * A.det = 0 := by linear_combination hdet
    exact (mul_eq_zero.mp h).resolve_left h₂
  by_contra h
  have hsep : B.SeparatingLeft := by
    intro v hv
    by_contra hv₀
    exact h ⟨v, hv₀, hv⟩
  exact (Matrix.separatingLeft_iff_det_ne_zero.mp
    (BilinForm.SeparatingLeft.toMatrix hsep b)) hz

/-- A line orthogonal to an isotropic space extends that space isotropically. -/
theorem isotropic_sup_span (B : BilinForm K V) (hB : B.IsAlt)
    {U : Submodule K V} (hU : Isotropic B U) {v : V}
    (hv : ∀ x ∈ U, B v x = 0) : Isotropic B (U ⊔ K ∙ v) := by
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hb
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hd
  have hav : B a v = 0 := by rw [← hB.neg_eq v a, hv a ha, neg_zero]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    hU a ha c hc, hav, hv c hc, hB.self_eq_zero v, smul_zero, zero_add, add_zero]

/-- The full dimension bound for every pair of alternating forms. -/
theorem exists_common_isotropic [FiniteDimensional K V] (h₂ : (2 : K) ≠ 0)
    (B C : BilinForm K V) (hB : B.IsAlt) (hC : C.IsAlt) :
    ∃ U : Submodule K V, (finrank K V + 1) / 2 ≤ finrank K U ∧
      Isotropic B U ∧ Isotropic C U := by
  classical
  suffices h : ∀ n : ℕ, ∀ (W : Type v) [AddCommGroup W] [Module K W]
      [FiniteDimensional K W], finrank K W = n →
      ∀ (B C : BilinForm K W), B.IsAlt → C.IsAlt →
      ∃ U : Submodule K W, (n + 1) / 2 ≤ finrank K U ∧
        Isotropic B U ∧ Isotropic C U by
    exact h (finrank K V) V rfl B C hB hC
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W _ _ _ hn B C hB hC
    by_cases hn₀ : n = 0
    · subst n
      refine ⟨⊥, by simp [hn₀], ?_, ?_⟩ <;>
        intro x hx y hy <;> simp only [Submodule.mem_bot] at hx hy <;>
        subst x <;> subst y <;> simp
    have step (v : W) (T : Submodule K W) (hv : v ∉ T)
        (hBT : ∀ w : T, B v w = 0) (hCT : ∀ w : T, C v w = 0)
        (hbound : (n + 1) / 2 ≤ (finrank K T + 1) / 2 + 1) :
        ∃ U : Submodule K W, (n + 1) / 2 ≤ finrank K U ∧
          Isotropic B U ∧ Isotropic C U := by
      have hsmall : finrank K T < n := by
        rw [← hn]
        exact Submodule.finrank_lt (by
          intro h
          apply hv
          rw [h]
          exact Submodule.mem_top)
      obtain ⟨U, hdim, hBU, hCU⟩ := ih (finrank K T) hsmall T rfl
        (B.restrict T) (C.restrict T) (fun w ↦ hB w) (fun w ↦ hC w)
      let U' := U.map T.subtype
      have hle : U' ≤ T := by
        rintro _ ⟨x, hx, rfl⟩
        exact x.property
      have hv' : v ∉ U' := fun h ↦ hv (hle h)
      have hB' : Isotropic B U' := by
        rintro x ⟨x', hx', rfl⟩ y ⟨y', hy', rfl⟩
        exact hBU x' hx' y' hy'
      have hC' : Isotropic C U' := by
        rintro x ⟨x', hx', rfl⟩ y ⟨y', hy', rfl⟩
        exact hCU x' hx' y' hy'
      refine ⟨U' ⊔ K ∙ v, ?_, isotropic_sup_span B hB hB' ?_,
        isotropic_sup_span C hC hC' ?_⟩
      · rw [Submodule.finrank_sup_span_singleton hv']
        have hdim' : finrank K U' = finrank K U := Submodule.finrank_map_subtype_eq T U
        omega
      · exact fun x hx ↦ hBT ⟨x, hle hx⟩
      · exact fun x hx ↦ hCT ⟨x, hle hx⟩
    by_cases hodd : Odd n
    · obtain ⟨v, hv₀, hvB⟩ := exists_radical_of_odd h₂ B hB (by simpa only [hn] using hodd)
      obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K hv₀
      let F : W →ₗ[K] K × K := φ.prod (C v)
      let T := LinearMap.ker F
      have hv : v ∉ T := by
        intro hv
        have h := congrArg Prod.fst (show F v = 0 from hv)
        simpa [F, hφ] using h
      have hdim : n ≤ finrank K T + 2 := by
        have hnull := F.finrank_range_add_finrank_ker
        have hle := Submodule.finrank_le (LinearMap.range F)
        simp only [Module.finrank_prod, Module.finrank_self] at hle
        change finrank K (LinearMap.range F) + finrank K T = finrank K W at hnull
        omega
      apply step v T hv (fun w ↦ hvB w) (fun w ↦ ?_) (by omega)
      exact congrArg Prod.snd (show F w = 0 from w.property)
    · obtain ⟨v, hv₀⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (show 0 < finrank K W by omega)
      obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K hv₀
      let F : W →ₗ[K] K × (K × K) := φ.prod ((B v).prod (C v))
      let T := LinearMap.ker F
      have hv : v ∉ T := by
        intro hv
        have h := congrArg Prod.fst (show F v = 0 from hv)
        simpa [F, hφ] using h
      have hdim : n ≤ finrank K T + 3 := by
        have hnull := F.finrank_range_add_finrank_ker
        have hle := Submodule.finrank_le (LinearMap.range F)
        simp only [Module.finrank_prod, Module.finrank_self] at hle
        change finrank K (LinearMap.range F) + finrank K T = finrank K W at hnull
        omega
      have heven : n % 2 = 0 := Nat.even_iff.mp (Nat.not_odd_iff_even.mp hodd)
      apply step v T hv (fun w ↦ ?_) (fun w ↦ ?_) (by omega)
      · exact congrArg (fun z : K × (K × K) ↦ z.2.1) (show F w = 0 from w.property)
      · exact congrArg (fun z : K × (K × K) ↦ z.2.2) (show F w = 0 from w.property)

/-- Every allowed number of vectors can be chosen independently and simultaneously
isotropic for the two original forms. -/
theorem exists_common_isotropic_vectors [FiniteDimensional K V] (h₂ : (2 : K) ≠ 0)
    (B C : BilinForm K V) (hB : B.IsAlt) (hC : C.IsAlt)
    (s : ℕ) (hs : s ≤ (finrank K V + 1) / 2) :
    ∃ v : Fin s → V, LinearIndependent K v ∧
      (∀ i j, B (v i) (v j) = 0) ∧ (∀ i j, C (v i) (v j) = 0) := by
  obtain ⟨U, hdim, hBU, hCU⟩ := exists_common_isotropic h₂ B C hB hC
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (hs.trans hdim)
  refine ⟨fun i ↦ (v i : U), hv.map' U.subtype (LinearMap.ker_eq_bot.mpr U.injective_subtype), ?_, ?_⟩
  · exact fun i j ↦ hBU _ (v i).property _ (v j).property
  · exact fun i j ↦ hCU _ (v i).property _ (v j).property

end PaperVerification.CommonIsotropicSubspace
end
end
end ComponentSource_19

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.CommonIsotropicSubspace"

section ComponentSource_20
/- Original module: PaperVerification.CommonIsotropicChartPoints -/


/-!
# Actual normalized chart points for every pair of alternating forms

The abstract common-isotropic vectors are converted into the original coefficient
and row-chart conventions. A nonzero maximal minor is sorted and inverted, giving
an actual pivot-normalized matrix over the coefficient field. The original
row-isotropy equations are preserved because each new row is a linear combination
of the old rows.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Module Matrix MvPolynomial
open LinearMap (BilinForm)
open scoped BigOperators

namespace PaperVerification.AlternatingForms

variable {K : Type*} [Field K] {s n t m : ℕ}

/-- The alternating bilinear form with the literal strictly increasing coefficients. -/
def coefficientBilinear (f : StrictPairs n → K) : BilinForm K (Fin n → K) :=
  ∑ a : StrictPairs n, f a •
    ((LinearMap.mul K K).compl₁₂ (LinearMap.proj a.val.1) (LinearMap.proj a.val.2) -
      (LinearMap.mul K K).compl₁₂ (LinearMap.proj a.val.2) (LinearMap.proj a.val.1))

@[simp] theorem coefficientBilinear_apply (f : StrictPairs n → K) (v w : Fin n → K) :
    coefficientBilinear f v w =
      ∑ a : StrictPairs n, f a • (v a.val.1 * w a.val.2 - v a.val.2 * w a.val.1) := by
  simp [coefficientBilinear, LinearMap.sum_apply, LinearMap.smul_apply]

theorem coefficientBilinear_isAlt (f : StrictPairs n → K) :
    (coefficientBilinear f).IsAlt := by
  intro v
  simp [coefficientBilinear_apply, mul_comm]

@[simp] theorem coefficientBilinear_rows (f : StrictPairs n → K)
    (A : Matrix (Fin (t + 2)) (Fin n) K) (i j : Fin (t + 2)) :
    coefficientBilinear f (A i) (A j) = alternatingRowPair f A i j := by
  rw [coefficientBilinear_apply]
  rfl

/-- Linear independence produces a nonzero minor with the original increasing
Plücker index convention. -/
theorem exists_plucker_minor_ne_zero (A : Matrix (Fin s) (Fin n) K)
    (hA : LinearIndependent K A) :
    ∃ p : PluckerIndex s n, (A.submatrix id p.val).det ≠ 0 := by
  classical
  obtain ⟨e, he⟩ :=
    (Matrix.linearIndependent_row_iff_exists_det_submatrix_ne_zero (A := A)).mp hA
  let p := sortedPluckerIndex e e.injective
  refine ⟨p, ?_⟩
  intro hz
  have hperm := Matrix.det_permute' (Tuple.sort (e : Fin s → Fin n)).symm
    (A.submatrix id p.val)
  have hm : (A.submatrix id p.val).submatrix id (Tuple.sort (e : Fin s → Fin n)).symm =
      A.submatrix id e := by
    ext i j
    simp only [Matrix.submatrix_apply, id_eq, p, sortedPluckerIndex,
      Function.comp_apply, Equiv.apply_symm_apply]
  rw [hm, hz, mul_zero] at hperm
  exact he hperm

/-- Row operations preserve total isotropy for the actual bilinear form. -/
theorem bilinear_zero_on_mul_rows (B : BilinForm K (Fin n → K))
    (A : Matrix (Fin s) (Fin n) K) (P : Matrix (Fin s) (Fin s) K)
    (hA : ∀ i j, B (A i) (A j) = 0) (i j : Fin s) :
    B ((P * A) i) ((P * A) j) = 0 := by
  have hrow (i : Fin s) : (P * A) i = ∑ k, P i k • A k := by
    funext l
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hrow, hrow]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    hA, smul_zero, Finset.sum_const_zero]

/-- An independent isotropic row matrix gives a point of one of the literal
original affine charts. No genericity or rank condition on the forms is used. -/
theorem exists_isotropicChartPoint_of_rows
    (forms : Fin m → StrictPairs n → K) (A : Matrix (Fin (t + 2)) (Fin n) K)
    (hA : LinearIndependent K A)
    (hiso : ∀ l i j, alternatingRowPair (forms l) A i j = 0) :
    ∃ p : PluckerIndex (t + 2) n, Nonempty (IsotropicChartPoint p forms K) := by
  classical
  obtain ⟨p, hp⟩ := exists_plucker_minor_ne_zero A hA
  let M := A.submatrix id p.val
  refine ⟨p, ⟨{ matrix := M⁻¹ * A, pivot := ?_, isotropic := ?_ }⟩⟩
  · have h : (M⁻¹ * A).submatrix id p.val = M⁻¹ * M := by
      ext i j
      rfl
    rw [h]
    exact Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hp)
  · intro l i j
    rw [← coefficientBilinear_rows]
    exact bilinear_zero_on_mul_rows (coefficientBilinear (forms l)) A M⁻¹
      (fun i j ↦ (coefficientBilinear_rows (forms l) A i j).trans (hiso l i j)) i j

/-- For every pair, every allowed plane dimension occurs in an actual isotropic chart. -/
theorem exists_common_isotropic_chartPoint (h₂ : (2 : K) ≠ 0)
    (forms : Fin 2 → StrictPairs n → K) (hs : t + 2 ≤ (n + 1) / 2) :
    ∃ p : PluckerIndex (t + 2) n, Nonempty (IsotropicChartPoint p forms K) := by
  obtain ⟨A, hA, h₀, h₁⟩ := CommonIsotropicSubspace.exists_common_isotropic_vectors h₂
    (coefficientBilinear (forms 0)) (coefficientBilinear (forms 1))
    (coefficientBilinear_isAlt _) (coefficientBilinear_isAlt _) (t + 2)
    (by simpa using hs)
  apply exists_isotropicChartPoint_of_rows forms A hA
  intro l i j
  fin_cases l
  · exact (coefficientBilinear_rows (forms 0) A i j).symm.trans (h₀ i j)
  · exact (coefficientBilinear_rows (forms 1) A i j).symm.trans (h₁ i j)

end PaperVerification.AlternatingForms
end
end
end ComponentSource_20

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.CommonIsotropicChartPoints"

section ComponentSource_21
/- Original module: PaperVerification.CommonIsotropicProjectiveNonempty -/


/-!
# Nonemptiness of the actual common-isotropic projective scheme

The point is obtained from the field-valued point of an original affine chart
and transported through the proved isomorphism to an actual basic open of Proj.
-/

@[expose] public section
noncomputable section
open AlgebraicGeometry CategoryTheory

namespace PaperVerification.AlternatingForms
variable {K : Type*} [Field K] [CharZero K] {t n : ℕ}

/-- The actual projective zero scheme is nonempty for every pair in the full
numerically allowed range. This strengthens the nonemptiness part of Theorem1.2. -/
theorem commonIsotropicProj_nonempty
    (forms : Fin 2 → StrictPairs n → K) (hs : t + 2 ≤ (n + 1) / 2) :
    Nonempty (Proj (isotropicProjectiveGrading (t := t) forms)) := by
  obtain ⟨p, ⟨A⟩⟩ := exists_common_isotropic_chartPoint (by exact two_ne_zero) forms hs
  let x : PrimeSpectrum K := ⟨⊥, inferInstance⟩
  let y : PrimeSpectrum (IsotropicChartRing p forms) :=
    PrimeSpectrum.comap A.toAlgHom.toRingHom x
  exact ⟨((isotropicProjBasicOpenIso p forms).inv y).val⟩

/-- The usual numerical nonemptiness range, without a division in its hypothesis. -/
theorem commonIsotropicProj_nonempty_of_dimension
    (forms : Fin 2 → StrictPairs n → K) (hs : 2 * (t + 2) ≤ n + 1) :
    Nonempty (Proj (isotropicProjectiveGrading (t := t) forms)) :=
  commonIsotropicProj_nonempty forms (by omega)

/-- The original one-plane Plücker grading in arbitrary ambient dimension. -/
def onePlaneOriginalGrading (n : ℕ) :=
  HomogeneousQuotientProjective.grading
    (matrixPluckerIdeal (K := K) (s := 1) (n := n))
    (matrixPluckerIdeal_isHomogeneous (by decide : 0 < 1))

instance onePlaneOriginalGradedAlgebra (n : ℕ) :
    GradedAlgebra (onePlaneOriginalGrading (K := K) n) :=
  HomogeneousQuotientProjective.quotientGradedAlgebra _ _

/-- The one-plane boundary is nonempty in every positive ambient dimension. -/
theorem onePlaneOriginalProj_nonempty (n : ℕ) (hn : 0 < n) :
    Nonempty (Proj (onePlaneOriginalGrading (K := K) n)) := by
  let p : PluckerIndex 1 n := ⟨fun _ ↦ ⟨0, hn⟩, by
    intro i j hij
    have h : i = j := Subsingleton.elim _ _
    subst j
    exact ((lt_irrefl i) hij).elim⟩
  let e := HomogeneousQuotientCharts.projectiveBasicOpenIsoNormalized
      (matrixPluckerIdeal (K := K) (s := 1) (n := n))
      (matrixPluckerIdeal_isHomogeneous (by decide : 0 < 1)) p ≪≫
    Scheme.Spec.mapIso (pluckerBigCellEquiv (K := K) p).symm.toRingEquiv.toCommRingCatIso.op
  let φ : MvPolynomial (PluckerChartVariable p) K →ₐ[K] K :=
    MvPolynomial.aeval (fun _ ↦ 0)
  let y : PrimeSpectrum (MvPolynomial (PluckerChartVariable p) K) :=
    PrimeSpectrum.comap φ.toRingHom ⟨⊥, inferInstance⟩
  exact ⟨(e.inv y).val⟩

end PaperVerification.AlternatingForms
end
end
end ComponentSource_21

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.CommonIsotropicProjectiveNonempty"

section ComponentSource_22
/- Original module: PaperVerification.AlternatingFormsGenericRelativeDimension -/


/-!
# The actual generic common-isotropic scheme has the expected relative dimension

The dimension is established using the original affine quotient presentations
and their full Jacobian-minor cover. The same parameter polynomial works for
every Plücker chart. The pair case combines this with an actual field-valued
point supplied by the common-isotropic induction, in every ambient dimension.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped BigOperators

namespace PaperVerification.AlternatingForms

open GenericSectionDifferentials

variable {K : Type} [Field K] [CharZero K] {t n m : ℕ}

private lemma relativeDimension_chart_variable_count (p : PluckerIndex (t + 2) n) :
    Fintype.card (PluckerChartVariable p) = (t + 2) * (n - (t + 2)) := by
  classical
  have h : Fintype.card (Set.range p.val) = t + 2 := by
    simpa only [Fintype.card_fin] using
      (Fintype.card_congr (Equiv.ofInjective p.val p.property.injective)).symm
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_subtype_compl,
    Fintype.card_fin, h]

/-- The original quotient chart is locally standard smooth with exactly the
number of matrix variables minus the number of row-isotropy equations. -/
theorem isotropicChartRing_locally_standardSmoothOfRelativeDimension
    (p : PluckerIndex (t + 2) n) (a : (Fin m × StrictPairs n) → K)
    (ha : MvPolynomial.aeval a
      (isotropicChartSmoothnessPolynomial (K := K) (m := m) p) ≠ 0) :
    RingHom.Locally
      (RingHom.IsStandardSmoothOfRelativeDimension
        ((t + 2) * (n - (t + 2)) - m * (t + 2).choose 2))
      (algebraMap K (IsotropicChartRing p (fun l i ↦ a (l, i)))) := by
  classical
  have h := linearSection_quotient_locally_standardSmoothOfRelativeDimension
    (chartSectionEvaluation (K:=K) (m:=m) p) (chartSectionExtension (K:=K) (m:=m) p)
    (chartSectionEvaluation_rightInverse (K:=K) (m:=m) p) a ha
  have hf : linearSection (chartSectionEvaluation (K:=K) (m:=m) p) a =
      fun j : Fin m × StrictPairs (t + 2) ↦
        alternatingRowPair (fun i ↦ a (j.1, i)) (pluckerChartMatrix (K:=K) p)
          j.2.val.1 j.2.val.2 := by
    funext j
    exact chartSectionEvaluation_sum p a j
  rw [hf] at h
  rw [relativeDimension_chart_variable_count, Fintype.card_prod,
    Fintype.card_fin, card_strictPairs] at h
  exact h

/-- Every original chart, on the same nonempty parameter open, has the same
expected smooth relative dimension. -/
theorem isotropic_all_charts_relativeDimension (t n m : ℕ)
    (a : (Fin m × StrictPairs n) → K)
    (ha : MvPolynomial.aeval a (isotropicSmoothnessPolynomial (K := K) t n m) ≠ 0)
    (p : PluckerIndex (t + 2) n) :
    RingHom.Locally
      (RingHom.IsStandardSmoothOfRelativeDimension
        ((t + 2) * (n - (t + 2)) - m * (t + 2).choose 2))
      (algebraMap K (IsotropicChartRing p (fun l i ↦ a (l, i)))) := by
  classical
  apply isotropicChartRing_locally_standardSmoothOfRelativeDimension p a
  rw [isotropicSmoothnessPolynomial, map_prod] at ha
  exact (Finset.prod_ne_zero_iff.mp ha) p (Finset.mem_univ p)

/-- The native fixed-relative-dimension property descends from the proved
original affine chart cover to the genuine common-isotropic Proj scheme. -/
theorem isotropicStructureMap_smoothOfRelativeDimension (t n m : ℕ)
    (a : (Fin m × StrictPairs n) → K)
    (ha : MvPolynomial.aeval a (isotropicSmoothnessPolynomial (K := K) t n m) ≠ 0) :
    SmoothOfRelativeDimension
      ((t + 2) * (n - (t + 2)) - m * (t + 2).choose 2)
      (isotropicStructureMap (t := t) (fun l i ↦ a (l, i))) := by
  let d := (t + 2) * (n - (t + 2)) - m * (t + 2).choose 2
  apply IsZariskiLocalAtSource.of_iSup_eq_top
    (P:=@AlgebraicGeometry.SmoothOfRelativeDimension.{0} d)
    (fun p : PluckerIndex (t + 2) n ↦
      Proj.basicOpen (isotropicProjectiveGrading (t := t) (fun l i ↦ a (l, i)))
        (Ideal.Quotient.mk (isotropicPluckerIdeal (fun l i ↦ a (l, i))) (X p)))
    (isotropicProjBasicOpen_cover (t := t) (fun l i ↦ a (l, i)))
  intro p
  rw [← isotropicProjBasicOpenIso_hom_over]
  letI : SmoothOfRelativeDimension d (Spec.map (CommRingCat.ofHom
      (algebraMap K (IsotropicChartRing p (fun l i ↦ a (l, i)))))) :=
    (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d)).mpr
      (isotropic_all_charts_relativeDimension t n m a ha p)
  have h : SmoothOfRelativeDimension (0 + d)
      ((isotropicProjBasicOpenIso p (fun l i ↦ a (l, i))).hom ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap K (IsotropicChartRing p (fun l i ↦ a (l, i)))))) := inferInstance
  simpa only [Nat.zero_add] using h

/-- The presentation dimension in the pair case is precisely the paper's
`D = s*(n+1-2*s)` throughout its full nonempty parameter range. -/
theorem pair_expected_dimension (t n : ℕ) (hs : 2 * (t + 2) ≤ n + 1) :
    (t + 2) * (n - (t + 2)) - 2 * (t + 2).choose 2 =
      (t + 2) * (n + 1 - 2 * (t + 2)) := by
  have hchoose := two_mul_choose_two_add (t + 2)
  have h₁ : n - (t + 2) + (t + 2) = n := by omega
  have h₂ : n + 1 - 2 * (t + 2) + 2 * (t + 2) = n + 1 := by omega
  have hnum : (t + 2) * (n - (t + 2)) =
      (t + 2) * (n + 1 - 2 * (t + 2)) + 2 * (t + 2).choose 2 := by nlinarith
  rw [hnum, Nat.add_sub_cancel]

/-- The complete nonempty generic-smooth locus for pairs, with the actual
expected smooth relative dimension and the original coefficient parameter space. -/
theorem generic_pair_commonIsotropic_smooth_nonempty (t n : ℕ)
    (hs : 2 * (t + 2) ≤ n + 1) :
    ∃ Q : MvPolynomial (Fin 2 × StrictPairs n) K, Q ≠ 0 ∧
      (∃ a : (Fin 2 × StrictPairs n) → K, MvPolynomial.aeval a Q ≠ 0) ∧
      ∀ a : (Fin 2 × StrictPairs n) → K, MvPolynomial.aeval a Q ≠ 0 →
        Nonempty (Proj (isotropicProjectiveGrading (t := t) (fun l i ↦ a (l, i)))) ∧
        SmoothOfRelativeDimension ((t + 2) * (n + 1 - 2 * (t + 2)))
          (isotropicStructureMap (t := t) (fun l i ↦ a (l, i))) := by
  refine ⟨isotropicSmoothnessPolynomial (K := K) t n 2,
    isotropicSmoothnessPolynomial_ne_zero (K := K) t n 2, ?_, ?_⟩
  · obtain ⟨a, ha, _⟩ := exists_isotropic_all_charts_smooth (K := K) t n 2
    exact ⟨a, ha⟩
  · intro a ha
    refine ⟨commonIsotropicProj_nonempty_of_dimension _ hs, ?_⟩
    rw [← pair_expected_dimension t n hs]
    exact isotropicStructureMap_smoothOfRelativeDimension t n 2 a ha

/-- The complementary range in the paper has empty general zero scheme,
including cases with no Grassmannian charts at all. -/
theorem generic_pair_commonIsotropic_empty (t n : ℕ)
    (hs : n + 1 < 2 * (t + 2)) :
    ∃ Q : MvPolynomial (Fin 2 × StrictPairs n) K, Q ≠ 0 ∧
      (∃ a : (Fin 2 × StrictPairs n) → K, MvPolynomial.aeval a Q ≠ 0) ∧
      ∀ a : (Fin 2 × StrictPairs n) → K, MvPolynomial.aeval a Q ≠ 0 →
        IsEmpty (Proj (isotropicProjectiveGrading (t := t) (fun l i ↦ a (l, i)))) := by
  apply generic_commonIsotropic_empty_of_negative_dimension t n 2
  have hchoose := two_mul_choose_two_add (t + 2)
  have hnum : 2 * (t + 2).choose 2 = (t + 2) * (t + 1) := by nlinarith
  rw [hnum]
  exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)

end PaperVerification.AlternatingForms
end
end
end ComponentSource_22

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsGenericRelativeDimension"

section ComponentSource_23
/- Original module: PaperVerification.OnePlaneProjectiveGeometry -/


/-!
# The one-plane boundary in every ambient dimension

Alternating forms vanish on lines. The original one-plane Plücker scheme has
normalized affine-space charts of dimension `n-1`; these prove its native
smooth relative dimension and nonemptiness for every positive `n`.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K] [CharZero K]

/-- The structure morphism of the original one-plane Plücker scheme. -/
def onePlaneOriginalStructureMap (n : ℕ) :
    Proj (onePlaneOriginalGrading (K := K) n) ⟶ Spec (CommRingCat.of K) :=
  HomogeneousQuotientCharts.structureMap _ _

/-- The normalized original Plücker chart is an actual affine space. -/
def onePlaneOriginalAffineIso {n : ℕ} (p : PluckerIndex 1 n) :
    (Proj.basicOpen (onePlaneOriginalGrading (K := K) n)
      (Ideal.Quotient.mk (matrixPluckerIdeal (K := K)) (X p))).toScheme ≅
      𝔸(PluckerChartVariable p; Spec (CommRingCat.of K)) :=
  HomogeneousQuotientCharts.polynomialChartIso matrixPluckerIdeal
    (matrixPluckerIdeal_isHomogeneous (by decide : 0 < 1)) p
    (pluckerBigCellEquiv (K := K) p)

theorem onePlaneOriginalAffineIso_over {n : ℕ} (p : PluckerIndex 1 n) :
    (onePlaneOriginalAffineIso (K := K) p).hom ≫
      (𝔸(PluckerChartVariable p; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) =
      (Proj.basicOpen (onePlaneOriginalGrading (K := K) n)
        (Ideal.Quotient.mk (matrixPluckerIdeal (K := K)) (X p))).ι ≫
          onePlaneOriginalStructureMap n :=
  HomogeneousQuotientCharts.polynomialChartIso_hom_over matrixPluckerIdeal
    (matrixPluckerIdeal_isHomogeneous (by decide : 0 < 1)) p
    (pluckerBigCellEquiv (K := K) p)

/-- The original one-row normalized charts cover the whole projective scheme. -/
theorem onePlaneOriginal_basicOpen_cover (n : ℕ) :
    (⨆ p : PluckerIndex 1 n,
      Proj.basicOpen (onePlaneOriginalGrading (K := K) n)
        (Ideal.Quotient.mk (matrixPluckerIdeal (K := K)) (X p))) = ⊤ :=
  HomogeneousQuotientProjective.presentation_basicOpen_cover
    (matrixPluckerIdeal (K := K) (s := 1) (n := n))
    (matrixPluckerIdeal_isHomogeneous (by decide : 0 < 1))
    (Ideal.Quotient.mkₐ K _) Ideal.Quotient.mk_surjective
    (HomogeneousQuotientProjective.quotient_X_mem_one _ _)

/-- Smoothness with the expected relative dimension includes the complete
one-plane boundary; it is not restricted to odd-dimensional pencils. -/
theorem onePlaneOriginalStructureMap_smoothOfRelativeDimension (n : ℕ) :
    SmoothOfRelativeDimension (n - 1) (onePlaneOriginalStructureMap (K := K) n) := by
  apply IsZariskiLocalAtSource.of_iSup_eq_top
    (P := @AlgebraicGeometry.SmoothOfRelativeDimension.{0} (n - 1))
    (fun p : PluckerIndex 1 n ↦ Proj.basicOpen (onePlaneOriginalGrading (K := K) n)
      (Ideal.Quotient.mk (matrixPluckerIdeal (K := K)) (X p)))
    (onePlaneOriginal_basicOpen_cover n)
  intro p
  rw [← onePlaneOriginalAffineIso_over]
  have hcard : Nat.card (PluckerChartVariable p) = n - 1 := by
    classical
    have hrange : Fintype.card (Set.range p.val) = 1 := by
      simpa only [Fintype.card_fin] using
        (Fintype.card_congr (Equiv.ofInjective p.val p.property.injective)).symm
    rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_subtype_compl, Fintype.card_fin, hrange, one_mul]
  letI : SmoothOfRelativeDimension (n - 1)
      (𝔸(PluckerChartVariable p; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) :=
    AffineSpace.smoothOfRelativeDimension_of_card_eq _ hcard
  have h : SmoothOfRelativeDimension (0 + (n - 1))
      ((onePlaneOriginalAffineIso (K := K) p).hom ≫
        (𝔸(PluckerChartVariable p; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K))) :=
    inferInstance
  simpa only [Nat.zero_add] using h

/-- The nonempty smooth projective one-plane scheme, for every `1 ≤ n`. -/
theorem onePlaneOriginal_nonempty_smooth (n : ℕ) (hn : 0 < n) :
    Nonempty (Proj (onePlaneOriginalGrading (K := K) n)) ∧
      SmoothOfRelativeDimension (n - 1) (onePlaneOriginalStructureMap (K := K) n) :=
  ⟨onePlaneOriginalProj_nonempty n hn,
    onePlaneOriginalStructureMap_smoothOfRelativeDimension n⟩

/-- The zero-dimensional ambient vector space has no one-dimensional planes. -/
theorem onePlaneOriginalProj_zero_empty :
    IsEmpty (Proj (onePlaneOriginalGrading (K := K) 0)) := by
  constructor
  intro x
  have hx : x ∈ (⨆ p : PluckerIndex 1 0,
      Proj.basicOpen (onePlaneOriginalGrading (K := K) 0)
        (Ideal.Quotient.mk (matrixPluckerIdeal (K := K)) (X p))) := by
    rw [onePlaneOriginal_basicOpen_cover]
    trivial
  obtain ⟨p, _⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact Fin.elim0 (p.val 0)

end PaperVerification.AlternatingForms
end
end
end ComponentSource_23

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.OnePlaneProjectiveGeometry"

section ComponentSource_24
/- Original module: PaperVerification.StandardSmoothKrullDimension -/
/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
See https://www.apache.org/licenses/LICENSE-2.0 for the license.

Adapted from openai/math, commit 4eaee87548250b2682affda7d05d947c05554bae,
OAI/Algebra/RingTheory/SmoothKrullDimension.lean. This version generalizes the
field statement from complex numbers to every field and uses current Mathlib
imports. All proofs are included and must pass the same kernel audit.
-/


/-!
# Standard smooth dimension is actual Krull dimension over a field

A standard smooth algebra of relative dimension d is étale over a polynomial
algebra in d variables. Quasi-finiteness bounds prime chains from above; flat
going-down preserves prime heights. A maximal ideal over the polynomial base
therefore supplies the matching lower bound whenever the algebra is nonzero.
-/

@[expose] public section
noncomputable section

open Algebra MvPolynomial RingHom

namespace PaperVerification.StandardSmoothKrullDimension

section QuasiFinite

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem quasiFinite_strictMono_comap [QuasiFinite R S] :
    StrictMono (PrimeSpectrum.comap (algebraMap R S)) := by
  intro P Q hPQ
  have hle : P.asIdeal.under R ≤ Q.asIdeal.under R := Ideal.comap_mono hPQ.le
  refine lt_of_le_of_ne hle ?_
  intro heq
  have heq' : P.asIdeal.under R = Q.asIdeal.under R := by
    simpa [Ideal.under] using congrArg PrimeSpectrum.asIdeal heq
  have hPQeq : P.asIdeal = Q.asIdeal :=
    QuasiFinite.eq_of_le_of_under_eq (R := R) P.asIdeal Q.asIdeal hPQ.le heq'
  exact hPQ.ne (PrimeSpectrum.ext hPQeq)

theorem quasiFinite_ringKrullDim_le [QuasiFinite R S] :
    ringKrullDim S ≤ ringKrullDim R := by
  rw [ringKrullDim, ringKrullDim]
  exact Order.krullDim_le_of_strictMono _ quasiFinite_strictMono_comap

theorem quasiFinite_height_eq_under [QuasiFinite R S] [Module.Flat R S]
    (P : Ideal S) [P.IsPrime] : P.height = (P.under R).height := by
  calc
    P.height = Order.height (⟨P, inferInstance⟩ : PrimeSpectrum S) :=
      PrimeSpectrum.height_eq_orderHeight (⟨P, inferInstance⟩ : PrimeSpectrum S)
    _ = Order.height
        (PrimeSpectrum.comap (algebraMap R S) (⟨P, inferInstance⟩ : PrimeSpectrum S)) := by
      apply Order.height_eq_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
        quasiFinite_strictMono_comap
      intro Q p hp
      have hp' : p.asIdeal < Q.asIdeal.under R := by
        have hp'' : p.asIdeal < (PrimeSpectrum.comap (algebraMap R S) Q).asIdeal := hp
        simpa only [Ideal.under, PrimeSpectrum.comap_asIdeal] using hp''
      obtain ⟨Q', hQ'Q, hQ'prime, hQ'over⟩ :=
        Q.asIdeal.exists_ideal_lt_liesOver_of_lt
          (R := R) (p := p.asIdeal) (q := Q.asIdeal.under R) hp'
      refine ⟨⟨Q', hQ'prime⟩, hQ'Q, ?_⟩
      apply PrimeSpectrum.ext
      simpa [Ideal.under] using hQ'over.over.symm
    _ = (P.under R).height := by
      rw [show (P.under R) =
        (PrimeSpectrum.comap (algebraMap R S)
          (⟨P, inferInstance⟩ : PrimeSpectrum S)).asIdeal from rfl]
      exact (PrimeSpectrum.height_eq_orderHeight
        (PrimeSpectrum.comap (algebraMap R S)
          (⟨P, inferInstance⟩ : PrimeSpectrum S))).symm

end QuasiFinite

theorem finiteType_maximal_comap {R S : Type*} [CommRing R] [CommRing S]
    [IsJacobsonRing R] {f : R →+* S} (hf : f.FiniteType)
    (P : Ideal S) [P.IsMaximal] : (P.comap f).IsMaximal := by
  let L := S ⧸ P
  let q : S →+* L := Ideal.Quotient.mk P
  letI : Field L := Ideal.Quotient.field P
  have hft : (q.comp f).FiniteType := hf.comp_surjective Ideal.Quotient.mk_surjective
  have hfin : (q.comp f).Finite := RingHom.finite_iff_finiteType_of_isJacobsonRing.mpr hft
  have hmax : ((⊥ : Ideal L).comap (q.comp f)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (q.comp f) hfin.to_isIntegral ⊥
  change (((⊥ : Ideal L).comap q).comap f).IsMaximal at hmax
  have hq : (⊥ : Ideal L).comap q = P := by
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  rwa [hq] at hmax

/-- A maximal ideal of a polynomial algebra over any field has the full height. -/
theorem polynomial_maximal_height (K : Type*) [Field K] (d : ℕ)
    (P : Ideal (MvPolynomial (Fin d) K)) [P.IsMaximal] : P.height = d := by
  induction d with
  | zero =>
      have hle : (↑P.height : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin 0) K) :=
        Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
      simp only [MvPolynomial.ringKrullDim_of_isNoetherianRing,
        ringKrullDim_eq_zero_of_field, ENat.card_eq_coe_fintype_card, Fintype.card_fin,
        Nat.cast_zero, WithBot.coe_zero, zero_add] at hle
      exact le_antisymm (WithBot.coe_le_coe.mp hle) bot_le
  | succ n ih =>
      let e : MvPolynomial (Fin (n + 1)) K ≃+* Polynomial (MvPolynomial (Fin n) K) :=
        (MvPolynomial.finSuccEquiv K n).toRingEquiv
      let Q : Ideal (Polynomial (MvPolynomial (Fin n) K)) := P.map e
      letI : Q.IsMaximal := Ideal.map_isMaximal_of_equiv e
      letI : (Q.under (MvPolynomial (Fin n) K)).IsMaximal := by
        change (Q.comap (Polynomial.C : MvPolynomial (Fin n) K →+*
          Polynomial (MvPolynomial (Fin n) K))).IsMaximal
        exact Polynomial.isMaximal_comap_C_of_isJacobsonRing Q
      calc
        P.height = Q.height := (RingEquiv.height_map e P).symm
        _ = (Q.under (MvPolynomial (Fin n) K)).height + 1 :=
          Polynomial.height_eq_height_add_one _ Q
        _ = n + 1 := by rw [ih (Q.under (MvPolynomial (Fin n) K))]

variable {K S : Type*} [Field K] [CommRing S] {f : K →+* S} {d : ℕ}

/-- Standard smooth relative dimension is a genuine upper bound on prime chains. -/
theorem standardSmooth_ringKrullDim_le (hf : f.IsStandardSmoothOfRelativeDimension d) :
    ringKrullDim S ≤ (d : ℕ) := by
  obtain ⟨g, _, hg⟩ := hf.exists_etale_mvPolynomial
  letI : Algebra (MvPolynomial (Fin d) K) S := g.toAlgebra
  letI : Algebra.Etale (MvPolynomial (Fin d) K) S := RingHom.etale_algebraMap.mp hg
  calc
    ringKrullDim S ≤ ringKrullDim (MvPolynomial (Fin d) K) := quasiFinite_ringKrullDim_le
    _ = (d : ℕ) := by simp

/-- Every nonzero standard smooth algebra over a field has exactly the
relative dimension given by its presentation. -/
theorem standardSmooth_ringKrullDim_eq [Nontrivial S]
    (hf : f.IsStandardSmoothOfRelativeDimension d) : ringKrullDim S = (d : ℕ) := by
  obtain ⟨g, _, hg⟩ := hf.exists_etale_mvPolynomial
  letI : Algebra (MvPolynomial (Fin d) K) S := g.toAlgebra
  letI : Algebra.Etale (MvPolynomial (Fin d) K) S := RingHom.etale_algebraMap.mp hg
  obtain ⟨P, hP⟩ := Ideal.exists_maximal S
  letI : P.IsMaximal := hP
  have hfiniteType : (algebraMap (MvPolynomial (Fin d) K) S).FiniteType :=
    RingHom.finiteType_algebraMap.mpr inferInstance
  letI : (P.under (MvPolynomial (Fin d) K)).IsMaximal :=
    finiteType_maximal_comap hfiniteType P
  have hheight : P.height = d := by
    rw [quasiFinite_height_eq_under (R := MvPolynomial (Fin d) K)]
    exact polynomial_maximal_height K d (P.under (MvPolynomial (Fin d) K))
  apply le_antisymm (standardSmooth_ringKrullDim_le hf)
  change (↑(d : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim S
  have hlower : (↑P.height : WithBot ℕ∞) ≤ ringKrullDim S :=
    Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
  rwa [← hheight]

end PaperVerification.StandardSmoothKrullDimension
end
end
end ComponentSource_24

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.StandardSmoothKrullDimension"

section ComponentSource_25
/- Original module: PaperVerification.SmoothSchemeKrullDimension -/
/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
See https://www.apache.org/licenses/LICENSE-2.0 for the license.

Parts adapted from the pinned openai/math proofs in Smooth/DimensionFormula,
Smooth/PointwiseDimension, and Smooth/FieldAffineChartDimension. The theorem
below uses only nonemptiness, and holds over every field. No integrality or
irreducibility assumption is added to the paper's geometric statement.
-/


/-!
# Smooth relative dimension agrees with actual scheme dimension

The comparison uses the ordinary topological Krull dimension, defined through
chains of irreducible closed subsets. Local standard smooth presentations give
the upper bound on every chain. Any nonempty affine standard smooth chart
supplies the lower bound. Disconnected and reducible schemes are allowed.
-/

@[expose] public section
noncomputable section

universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace Order

namespace PaperVerification.SmoothSchemeKrullDimension

variable {X : Scheme.{u}}

theorem topologicalKrullDim_eq_orderKrullDim (X : Scheme.{u}) :
    topologicalKrullDim X = Order.krullDim X :=
  Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))

theorem affineOpen_orderKrullDim_eq_ringKrullDim (U : X.Opens) (hU : IsAffineOpen U) :
    Order.krullDim U = ringKrullDim Γ(X, U) := by
  calc
    Order.krullDim U = topologicalKrullDim U :=
      (topologicalKrullDim_eq_orderKrullDim U.toScheme).symm
    _ = topologicalKrullDim (PrimeSpectrum Γ(X, U)) :=
      hU.isoSpec.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq
    _ = ringKrullDim Γ(X, U) := PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _

/-- A specialization chain lies in any open neighborhood of its least point. -/
theorem orderKrullDim_le_of_open_neighborhoods (X : Scheme.{u}) (d : ℕ)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ Order.krullDim U ≤ (d : ℕ)) :
    Order.krullDim X ≤ (d : ℕ) := by
  cases isEmpty_or_nonempty X with
  | inl hX =>
      letI := hX
      rw [Order.krullDim_eq_bot]
      exact bot_le
  | inr hX =>
      letI := hX
      rw [Order.krullDim_eq_iSup_length]
      refine WithBot.coe_le_coe.mpr (iSup_le fun l ↦ ?_)
      obtain ⟨U, hhead, hU⟩ := h l.head
      have hmem (i : Fin (l.length + 1)) : l i ∈ U := by
        have hle : l.head ≤ l i := l.monotone (Fin.zero_le i)
        rw [Scheme.le_iff_specializes] at hle
        exact hle.mem_open U.isOpen hhead
      have hlt (a b : U.toScheme) (hab : U.ι.base a < U.ι.base b) : a < b := by
        rw [lt_iff_le_not_ge]
        constructor
        · rw [Scheme.le_iff_specializes]
          apply U.isOpenEmbedding.isInducing.specializes_iff.mp
          rw [← Scheme.le_iff_specializes]
          exact hab.le
        · intro hback
          apply not_le_of_gt hab
          rw [Scheme.le_iff_specializes] at hback ⊢
          exact U.isOpenEmbedding.isInducing.specializes_iff.mpr hback
      let lU : LTSeries U :=
        { length := l.length
          toFun := fun i ↦ ⟨l i, hmem i⟩
          step := fun i ↦ by
            simpa only [Set.mem_ofPred_eq] using
              hlt (⟨l i.castSucc, hmem i.castSucc⟩ : U.toScheme)
                (⟨l i.succ, hmem i.succ⟩ : U.toScheme) (l.step i) }
      have hlength : (l.length : WithBot ℕ∞) ≤ Order.krullDim U :=
        Order.le_krullDim_iff.mpr ⟨lU, rfl⟩
      exact WithBot.coe_le_coe.mp (hlength.trans hU)

variable {K : Type u} [Field K] {d : ℕ}

/-- Over a field the affine target neighborhood in the definition of smooth
relative dimension is necessarily the whole field spectrum. -/
theorem exists_affine_field_chart (p : X ⟶ Spec (.of K))
    [SmoothOfRelativeDimension d p] (x : X) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : x ∈ U),
      RingHom.IsStandardSmoothOfRelativeDimension d
        ((p.appTop ≫ X.presheaf.map U.leTop.op).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom) := by
  obtain ⟨V, _, U, hU, hx, e, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := d) (f := p) x
  have hV : V = ⊤ := by
    apply top_unique
    intro y _
    have hy : p x = y := Subsingleton.elim _ _
    exact hy ▸ e hx
  subst V
  have hzero : (Scheme.ΓSpecIso (.of K)).inv.hom.IsStandardSmoothOfRelativeDimension 0 :=
    RingHom.IsStandardSmoothOfRelativeDimension.equiv
      (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  refine ⟨U, hU, hx, ?_⟩
  have happ : p.appLE ⊤ U e = p.appTop ≫ X.presheaf.map U.leTop.op := rfl
  simpa only [Nat.add_zero, happ] using hstd.comp hzero

/-- Native smooth relative dimension bounds the actual topological dimension. -/
theorem topologicalKrullDim_le (p : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension d p] :
    topologicalKrullDim X ≤ (d : ℕ) := by
  rw [topologicalKrullDim_eq_orderKrullDim]
  apply orderKrullDim_le_of_open_neighborhoods X d
  intro x
  obtain ⟨U, hU, hx, hstd⟩ := exists_affine_field_chart (d := d) p x
  refine ⟨U, hx, ?_⟩
  rw [affineOpen_orderKrullDim_eq_ringKrullDim U hU]
  exact StandardSmoothKrullDimension.standardSmooth_ringKrullDim_le hstd

/-- A nonempty scheme smooth of relative dimension d over a field has
topological Krull dimension exactly d, without an irreducibility assumption. -/
theorem topologicalKrullDim_eq [Nonempty X] (p : X ⟶ Spec (.of K))
    [SmoothOfRelativeDimension d p] : topologicalKrullDim X = (d : ℕ) := by
  apply le_antisymm (topologicalKrullDim_le (d := d) p)
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨U, hU, hx, hstd⟩ := exists_affine_field_chart (d := d) p x
  letI : Nonempty U := ⟨⟨x, hx⟩⟩
  have hUdim : topologicalKrullDim U = (d : ℕ) := by
    rw [topologicalKrullDim_eq_orderKrullDim U.toScheme,
      affineOpen_orderKrullDim_eq_ringKrullDim U hU]
    exact StandardSmoothKrullDimension.standardSmooth_ringKrullDim_eq hstd
  rw [← hUdim]
  exact topologicalKrullDim_subspace_le X (U : Set X)

end PaperVerification.SmoothSchemeKrullDimension
end
end
end ComponentSource_25

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.SmoothSchemeKrullDimension"

section ComponentSource_26
/- Original module: PaperVerification.AlternatingFormsGenericKrullDimension -/


/-!
# The geometric clause of Theorem 1.2 in actual Krull dimension

The dimension is Mathlib's `topologicalKrullDim`, not an equation count used
as a definition. The separate presentation-to-Krull comparison supplies the
required equality for every nonempty scheme on the proved generic open.
-/

@[expose] public section
noncomputable section
open AlgebraicGeometry

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K] [CharZero K]

/-- General pairs in the full nonempty range define actual smooth nonempty
projective schemes of the expected topological Krull dimension. -/
theorem generic_pair_commonIsotropic_geometry (t n : ℕ)
    (hs : 2 * (t + 2) ≤ n + 1) :
    ∃ Q : MvPolynomial (Fin 2 × StrictPairs n) K, Q ≠ 0 ∧
      (∃ a : (Fin 2 × StrictPairs n) → K, MvPolynomial.aeval a Q ≠ 0) ∧
      ∀ a : (Fin 2 × StrictPairs n) → K, MvPolynomial.aeval a Q ≠ 0 →
        Nonempty (Proj (isotropicProjectiveGrading (t := t) (fun l i ↦ a (l, i)))) ∧
        Smooth (isotropicStructureMap (t := t) (fun l i ↦ a (l, i))) ∧
        topologicalKrullDim
          (Proj (isotropicProjectiveGrading (t := t) (fun l i ↦ a (l, i)))) =
          (((t + 2) * (n + 1 - 2 * (t + 2)) : ℕ) : WithBot ℕ∞) := by
  obtain ⟨Q, hQ, hpoint, hgood⟩ := generic_pair_commonIsotropic_smooth_nonempty (K := K) t n hs
  refine ⟨Q, hQ, hpoint, ?_⟩
  intro a ha
  obtain ⟨hX, hdim⟩ := hgood a ha
  letI := hX
  letI := hdim
  exact ⟨hX, SmoothOfRelativeDimension.smooth
      ((t + 2) * (n + 1 - 2 * (t + 2)))
      (isotropicStructureMap (t := t) (fun l i ↦ a (l, i))),
    SmoothSchemeKrullDimension.topologicalKrullDim_eq
      (d := (t + 2) * (n + 1 - 2 * (t + 2)))
      (isotropicStructureMap (t := t) (fun l i ↦ a (l, i)))⟩

/-- The one-plane boundary has its actual dimension n−1 in every ambient
dimension, including n=1. -/
theorem onePlaneOriginal_geometry (n : ℕ) (hn : 0 < n) :
    Nonempty (Proj (onePlaneOriginalGrading (K := K) n)) ∧
      Smooth (onePlaneOriginalStructureMap (K := K) n) ∧
      topologicalKrullDim (Proj (onePlaneOriginalGrading (K := K) n)) =
        ((n - 1 : ℕ) : WithBot ℕ∞) := by
  obtain ⟨hX, hdim⟩ := onePlaneOriginal_nonempty_smooth (K := K) n hn
  letI := hX
  letI := hdim
  exact ⟨hX, SmoothOfRelativeDimension.smooth (n - 1)
      (onePlaneOriginalStructureMap (K := K) n),
    SmoothSchemeKrullDimension.topologicalKrullDim_eq (d := n - 1)
      (onePlaneOriginalStructureMap (K := K) n)⟩

end PaperVerification.AlternatingForms
end
end
end ComponentSource_26

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsGenericKrullDimension"

section ComponentSource_27
/- Original module: PaperVerification.OnePlaneIsotropyComparison -/


/-!
# The actual one-plane isotropy equations impose no additional ideal

The existing row-evaluation definition is indexed by ranks `t+2`. We extend
the same literal expression to arbitrary rank, prove agreement in that range,
and use every basis-row pair in rank one. These are actual restriction
polynomials, not a definition by an empty list of equations. Their vanishing
holds over every commutative coefficient algebra, including nonreduced algebras.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K] [CharZero K] {n m s t : ℕ}

/-- The original alternating row evaluation, with its row rank left arbitrary. -/
def alternatingRowPairAtRank {R : Type*} [CommRing R] [Algebra K R]
    (f : StrictPairs n → K) (A : Matrix (Fin s) (Fin n) R) (i j : Fin s) : R :=
  ∑ a : StrictPairs n, f a •
    (A i a.val.1 * A j a.val.2 - A i a.val.2 * A j a.val.1)

@[simp] theorem alternatingRowPairAtRank_eq {R : Type*} [CommRing R] [Algebra K R]
    (f : StrictPairs n → K) (A : Matrix (Fin (t + 2)) (Fin n) R)
    (i j : Fin (t + 2)) :
    alternatingRowPairAtRank f A i j = alternatingRowPair f A i j := rfl

@[simp] theorem alternatingRowPairAtRank_self {R : Type*} [CommRing R] [Algebra K R]
    (f : StrictPairs n → K) (A : Matrix (Fin s) (Fin n) R) (i : Fin s) :
    alternatingRowPairAtRank f A i i = 0 := by
  simp [alternatingRowPairAtRank, mul_comm]

/-- Vanishing holds on every pair of scalar multiples of a line generator.
This is the literal argument of the recovered `onePlane_row_isotropic` theorem. -/
theorem onePlane_restriction_multiples {R : Type*} [CommRing R] [Algebra K R]
    (f : StrictPairs n → K) (u : Fin n → R) (a b : R) :
    (∑ ij : StrictPairs n, f ij •
      ((a * u ij.val.1) * (b * u ij.val.2) -
        (a * u ij.val.2) * (b * u ij.val.1))) = 0 := by
  apply Finset.sum_eq_zero
  intro ij _
  have h : (a * u ij.val.1) * (b * u ij.val.2) =
      (a * u ij.val.2) * (b * u ij.val.1) := by ring
  rw [h, sub_self, smul_zero]

/-- All restrictions to pairs of basis rows in the original normalized chart. -/
def isotropicChartIdealAtRank (p : PluckerIndex s n)
    (forms : Fin m → StrictPairs n → K) :
    Ideal (MvPolynomial (PluckerChartVariable p) K) :=
  Ideal.span (Set.range fun a : Fin m × Fin s × Fin s ↦
    alternatingRowPairAtRank (forms a.1) (pluckerChartMatrix p) a.2.1 a.2.2)

/-- In the existing rank range this is exactly the original defining ideal. -/
theorem isotropicChartIdealAtRank_eq (p : PluckerIndex (t + 2) n)
    (forms : Fin m → StrictPairs n → K) :
    isotropicChartIdealAtRank p forms = isotropicChartIdeal p forms := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨l, i, j⟩, rfl⟩
    exact alternatingRowPair_mem_chartIdeal p forms l i j
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨l, ij⟩, rfl⟩
    exact Ideal.subset_span ⟨(l, ij.val.1, ij.val.2), rfl⟩

/-- The actual one-row restriction ideal is zero, over the full chart ring. -/
theorem onePlaneChartRestrictionIdeal_eq_bot (p : PluckerIndex 1 n)
    (forms : Fin m → StrictPairs n → K) : isotropicChartIdealAtRank p forms = ⊥ := by
  apply le_antisymm ?_ bot_le
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨l, i, j⟩, rfl⟩
  have hij : i = j := Subsingleton.elim _ _
  subst j
  change alternatingRowPairAtRank (forms l) (pluckerChartMatrix p) i i ∈
    (⊥ : Ideal (MvPolynomial (PluckerChartVariable p) K))
  rw [alternatingRowPairAtRank_self]
  exact Ideal.zero_mem _

/-- Quotienting by the actual line-restriction equations leaves the original
polynomial chart, through the canonical quotient-by-zero equivalence. -/
def onePlaneRestrictionChartEquiv (p : PluckerIndex 1 n)
    (forms : Fin m → StrictPairs n → K) :
    (MvPolynomial (PluckerChartVariable p) K ⧸ isotropicChartIdealAtRank p forms) ≃ₐ[K]
      MvPolynomial (PluckerChartVariable p) K :=
  (Ideal.quotientEquivAlgOfEq K (onePlaneChartRestrictionIdeal_eq_bot p forms)).trans
    (AlgEquiv.quotientBot K _)

/-- The one-entry Plücker index of a coordinate of the universal row. -/
def oneRowPluckerIndex (i : Fin n) : PluckerIndex 1 n :=
  ⟨fun _ ↦ i, by
    intro a b hab
    exact ((ne_of_lt hab) (Subsingleton.elim _ _)).elim⟩

/-- These are the original universal matrix entries under the one-row minor map. -/
theorem oneRowPluckerIndex_genericMinor (i : Fin n) :
    genericPluckerMinor (K := K) (oneRowPluckerIndex i) = X (0, i) := by
  simp only [genericPluckerMinor, Matrix.det_fin_one, Matrix.of_apply, oneRowPluckerIndex]

/-- Restrict every form to every pair of rows of the universal one-row matrix.
The entries are the actual one-row Plücker coordinates. -/
def onePlaneHomogeneousRestrictionIdeal (forms : Fin m → StrictPairs n → K) :
    Ideal (MvPolynomial (PluckerIndex 1 n) K) :=
  Ideal.span (Set.range fun a : Fin m × Fin 1 × Fin 1 ↦
    alternatingRowPairAtRank (forms a.1)
      (Matrix.of fun (_ : Fin 1) i ↦ X (oneRowPluckerIndex i)) a.2.1 a.2.2)

theorem onePlaneHomogeneousRestrictionIdeal_eq_bot
    (forms : Fin m → StrictPairs n → K) : onePlaneHomogeneousRestrictionIdeal forms = ⊥ := by
  apply le_antisymm ?_ bot_le
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨l, i, j⟩, rfl⟩
  have hij : i = j := Subsingleton.elim _ _
  subst j
  change alternatingRowPairAtRank (forms l)
    (Matrix.of fun (_ : Fin 1) i ↦ X (oneRowPluckerIndex i)) i i ∈
    (⊥ : Ideal (MvPolynomial (PluckerIndex 1 n) K))
  rw [alternatingRowPairAtRank_self]
  exact Ideal.zero_mem _

/-- The original Plücker ideal together with the literal line restrictions. -/
def onePlaneIsotropicPluckerIdeal (forms : Fin m → StrictPairs n → K) :
    Ideal (MvPolynomial (PluckerIndex 1 n) K) :=
  matrixPluckerIdeal ⊔ onePlaneHomogeneousRestrictionIdeal forms

theorem onePlaneIsotropicPluckerIdeal_eq (forms : Fin m → StrictPairs n → K) :
    onePlaneIsotropicPluckerIdeal forms = matrixPluckerIdeal := by
  rw [onePlaneIsotropicPluckerIdeal, onePlaneHomogeneousRestrictionIdeal_eq_bot, sup_bot_eq]

theorem onePlaneIsotropicPluckerIdeal_isHomogeneous
    (forms : Fin m → StrictPairs n → K) :
    (onePlaneIsotropicPluckerIdeal forms).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (PluckerIndex 1 n) K) := by
  rw [onePlaneIsotropicPluckerIdeal_eq]
  exact matrixPluckerIdeal_isHomogeneous (by decide : 0 < 1)

/-- The genuine projective quotient, with its structure morphism over the field. -/
def onePlaneIsotropicOver (forms : Fin m → StrictPairs n → K) : Over (Spec (.of K)) :=
  Over.mk (HomogeneousQuotientCharts.structureMap (onePlaneIsotropicPluckerIdeal forms)
    (onePlaneIsotropicPluckerIdeal_isHomogeneous forms))

/-- Equality retains both the actual scheme and its original map to `Spec K`. -/
theorem onePlaneIsotropicOver_eq (forms : Fin m → StrictPairs n → K) :
    onePlaneIsotropicOver forms = Over.mk (onePlaneOriginalStructureMap (K := K) n) := by
  let F : { Q : Ideal (MvPolynomial (PluckerIndex 1 n) K) //
      Q.IsHomogeneous (MvPolynomial.homogeneousSubmodule (PluckerIndex 1 n) K) } → Over (Spec (.of K)) :=
    fun Q ↦ Over.mk (HomogeneousQuotientCharts.structureMap Q.val Q.property)
  change F ⟨onePlaneIsotropicPluckerIdeal forms,
      onePlaneIsotropicPluckerIdeal_isHomogeneous forms⟩ =
    F ⟨matrixPluckerIdeal, matrixPluckerIdeal_isHomogeneous (by decide : 0 < 1)⟩
  exact congrArg F (Subtype.ext (onePlaneIsotropicPluckerIdeal_eq forms))

/-- The accepted one-plane geometry now applies to the scheme defined by the
actual restriction equations, for every collection of alternating forms. -/
theorem onePlaneIsotropic_geometry (forms : Fin m → StrictPairs n → K) (hn : 0 < n) :
    Nonempty (onePlaneIsotropicOver forms).left ∧
      Smooth (onePlaneIsotropicOver forms).hom ∧
      topologicalKrullDim (onePlaneIsotropicOver forms).left =
        ((n - 1 : ℕ) : WithBot ℕ∞) := by
  rw [onePlaneIsotropicOver_eq]
  exact onePlaneOriginal_geometry n hn

theorem onePlaneIsotropic_zero_empty (forms : Fin m → StrictPairs 0 → K) :
    IsEmpty (onePlaneIsotropicOver forms).left := by
  rw [onePlaneIsotropicOver_eq]
  exact onePlaneOriginalProj_zero_empty

end PaperVerification.AlternatingForms
end
end
end ComponentSource_27

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.OnePlaneIsotropyComparison"

section ComponentSource_28
/- Original module: PaperVerification.AlternatingFormsOnePlaneRationality -/


/-!
# Rationality for the literal one-plane isotropy scheme

The one-plane rationality theorem is transported across the proved equality
of schemes over the original field.  The equation ideal contains every
restriction to every pair of universal rows; its vanishing was proved over
arbitrary coefficient algebras in `OnePlaneIsotropyComparison`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K] [CharZero K] {m : ℕ}

/-- The rationality conclusion includes the original scheme equations and
base morphism, for every finite family of forms in odd ambient dimension. -/
theorem onePlaneIsotropic_finite_rationality (k : ℕ)
    (forms : Fin m → StrictPairs (2 * k + 1) → K) :
    ∃ N : Type, Finite N ∧ Scheme.BirationalOver
      (onePlaneIsotropicOver forms).hom
      (𝔸(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) := by
  rw [onePlaneIsotropicOver_eq]
  exact paper_theorem_4_1_finite_rationality_one_plane (K := K) k

end PaperVerification.AlternatingForms
end
end
end ComponentSource_28

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsOnePlaneRationality"

section ComponentSource_29
/- Original module: PaperVerification.AlternatingFormsPluckerLinearAction -/


/-!
# Linear changes of the actual Plücker coordinates

The coordinate substitution is induced by the ordinary exterior power of a
linear map.  Its compatibility with maximal minors is proved over every
commutative coefficient algebra.  In particular it preserves the universal
Grassmannian ideal, with its complete scheme structure.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial Matrix
open scoped BigOperators

variable {K : Type*} [Field K] {s n : ℕ}

/-- The literal substitution on Plücker variables induced by an exterior power. -/
def pluckerLinearAction (e : (Fin n → K) →ₗ[K] (Fin n → K)) (s : ℕ) :
    MvPolynomial (PluckerIndex s n) K →ₐ[K] MvPolynomial (PluckerIndex s n) K :=
  aeval fun I => exteriorPluckerCoordinates s n
    (exteriorPower.map s e (exteriorPluckerBasis s n I))

@[simp] theorem pluckerLinearAction_X
    (e : (Fin n → K) →ₗ[K] (Fin n → K)) (I : PluckerIndex s n) :
    pluckerLinearAction e s (X I) = exteriorPluckerCoordinates s n
      (exteriorPower.map s e (exteriorPluckerBasis s n I)) := by
  simp only [pluckerLinearAction, aeval_X]

/-- The substitution acts on every exterior vector by the intended exterior map. -/
theorem pluckerLinearAction_coordinates
    (e : (Fin n → K) →ₗ[K] (Fin n → K)) (x : ⋀[K]^s (Fin n → K)) :
    pluckerLinearAction e s (exteriorPluckerCoordinates s n x) =
      exteriorPluckerCoordinates s n (exteriorPower.map s e x) := by
  have h : (pluckerLinearAction e s).toLinearMap.comp
      (exteriorPluckerCoordinates s n) =
      (exteriorPluckerCoordinates s n).comp (exteriorPower.map s e) := by
    apply (exteriorPluckerBasis s n).ext
    intro I
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      exteriorPluckerCoordinates_basis, pluckerLinearAction_X]
  exact congrArg (fun f => f x) h

theorem pluckerLinearAction_comp
    (e f : (Fin n → K) →ₗ[K] (Fin n → K)) (s : ℕ) :
    (pluckerLinearAction e s).comp (pluckerLinearAction f s) =
      pluckerLinearAction (e.comp f) s := by
  apply MvPolynomial.algHom_ext
  intro I
  simp only [AlgHom.comp_apply, pluckerLinearAction_X,
    pluckerLinearAction_coordinates, exteriorPower.map_comp, LinearMap.comp_apply]

@[simp] theorem pluckerLinearAction_id (s : ℕ) :
    pluckerLinearAction (LinearMap.id : (Fin n → K) →ₗ[K] (Fin n → K)) s =
      AlgHom.id K (MvPolynomial (PluckerIndex s n) K) := by
  apply MvPolynomial.algHom_ext
  intro I
  simp only [pluckerLinearAction_X, exteriorPower.map_id, LinearMap.id_apply,
    exteriorPluckerCoordinates_basis, AlgHom.id_apply]

/-- Invertible linear changes give invertible substitutions on the full polynomial ring. -/
def pluckerLinearEquiv (e : (Fin n → K) ≃ₗ[K] (Fin n → K)) (s : ℕ) :
    MvPolynomial (PluckerIndex s n) K ≃ₐ[K] MvPolynomial (PluckerIndex s n) K :=
  AlgEquiv.ofAlgHom (pluckerLinearAction e.toLinearMap s)
    (pluckerLinearAction e.symm.toLinearMap s)
    (by rw [pluckerLinearAction_comp, e.comp_symm, pluckerLinearAction_id])
    (by rw [pluckerLinearAction_comp, e.symm_comp, pluckerLinearAction_id])

/-- Evaluation of a covector against a row of an arbitrary coefficient matrix. -/
def matrixCovectorEvaluation {R : Type*} [CommRing R] [Algebra K R]
    (A : Matrix (Fin s) (Fin n) R) : (Fin n → K) →ₗ[K] (Fin s → R) where
  toFun v i := ∑ j, (v j) • A i j
  map_add' v w := by
    ext i
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

@[simp] theorem matrixCovectorEvaluation_basis {R : Type*} [CommRing R] [Algebra K R]
    (A : Matrix (Fin s) (Fin n) R) (j : Fin n) :
    matrixCovectorEvaluation A (Pi.basisFun K (Fin n) j) = fun i => A i j := by
  ext i
  simp [matrixCovectorEvaluation, Pi.basisFun_apply, Pi.single_apply]

/-- Determinants of evaluated covectors, regarded as a K-alternating map. -/
def matrixCovectorDeterminant {R : Type*} [CommRing R] [Algebra K R]
    (A : Matrix (Fin s) (Fin n) R) : (Fin n → K) [⋀^Fin s]→ₗ[K] R where
  toMultilinearMap :=
    ((Matrix.detRowAlternating : (Fin s → R) [⋀^Fin s]→ₗ[R] R).toMultilinearMap.restrictScalars K).compLinearMap
      (fun _ => matrixCovectorEvaluation A)
  map_eq_zero_of_eq' := by
    intro v i j hv hij
    exact (Matrix.detRowAlternating : (Fin s → R) [⋀^Fin s]→ₗ[R] R).map_eq_zero_of_eq
      (fun k => matrixCovectorEvaluation A (v k)) (congrArg (matrixCovectorEvaluation A) hv) hij

/-- Universal minor evaluation agrees with the determinant of arbitrary covectors. -/
theorem matrixMinorEvaluation_exterior_word
    {R : Type*} [CommRing R] [Algebra K R]
    (A : Matrix (Fin s) (Fin n) R) (v : Fin s → (Fin n → K)) :
    matrixMinorEvaluation A (exteriorPluckerCoordinates s n (exteriorPower.ιMulti K s v)) =
      Matrix.det (fun i j => ∑ l, v j l • A i l) := by
  let f := ((matrixMinorEvaluation (K := K) A).toLinearMap.comp
    (exteriorPluckerCoordinates s n)).compAlternatingMap (exteriorPower.ιMulti K s)
  have h : f = matrixCovectorDeterminant A := by
    apply (Pi.basisFun K (Fin n)).ext_alternating
    intro I hI
    change matrixMinorEvaluation A
      (exteriorPluckerCoordinates s n
        (exteriorPower.ιMulti K s (fun i => Pi.basisFun K (Fin n) (I i)))) = _
    rw [exteriorPluckerCoordinates_word, matrixMinorEvaluation_orderedCoordinate]
    change Matrix.det (fun i j => A i (I j)) =
      Matrix.det (fun j => matrixCovectorEvaluation A (Pi.basisFun K (Fin n) (I j)))
    simp only [matrixCovectorEvaluation_basis]
    exact Matrix.det_transpose _ |>.symm
  have hv := congrArg (fun a => a v) h
  change matrixMinorEvaluation A
    (exteriorPluckerCoordinates s n (exteriorPower.ιMulti K s v)) =
    Matrix.det (fun j i => ∑ l, v j l • A i l) at hv
  rw [hv]
  exact Matrix.det_transpose _

/-- The transformed row matrix has exactly the pullback entries under the linear map. -/
def matrixLinearChange {R : Type*} [CommRing R] [Algebra K R]
    (e : (Fin n → K) →ₗ[K] (Fin n → K)) (A : Matrix (Fin s) (Fin n) R) :
    Matrix (Fin s) (Fin n) R :=
  fun i j => ∑ l, (e (Pi.basisFun K (Fin n) j) l) • A i l

theorem matrixMinorEvaluation_pluckerLinearAction
    {R : Type*} [CommRing R] [Algebra K R]
    (e : (Fin n → K) →ₗ[K] (Fin n → K)) (A : Matrix (Fin s) (Fin n) R) :
    (matrixMinorEvaluation A).comp (pluckerLinearAction e s) =
      matrixMinorEvaluation (matrixLinearChange e A) := by
  apply MvPolynomial.algHom_ext
  intro I
  simp only [AlgHom.comp_apply, pluckerLinearAction_X, exteriorPluckerBasis_apply,
    exteriorPower.map_apply_ιMulti, matrixMinorEvaluation_exterior_word]
  simp only [matrixMinorEvaluation, aeval_X, matrixLinearChange]
  rfl

theorem pluckerLinearAction_preserves_matrixIdeal
    (e : (Fin n → K) →ₗ[K] (Fin n → K))
    (p : MvPolynomial (PluckerIndex s n) K) (hp : p ∈ matrixPluckerIdeal) :
    pluckerLinearAction e s p ∈ matrixPluckerIdeal := by
  let A : Matrix (Fin s) (Fin n) (MvPolynomial (Fin s × Fin n) K) :=
    fun i j => X (i,j)
  have he : matrixMinorEvaluation (K := K) A = genericPluckerMap := rfl
  change genericPluckerMap (pluckerLinearAction e s p) = 0
  rw [← he, ← AlgHom.comp_apply, matrixMinorEvaluation_pluckerLinearAction]
  exact matrixPluckerIdeal_le_matrixMinorKernel (matrixLinearChange e A) hp

end PaperVerification.AlternatingForms
end
end
end ComponentSource_29

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsPluckerLinearAction"

section ComponentSource_30
/- Original module: PaperVerification.AlternatingFormsIsotropicLinearAction -/


/-!
# Change of basis of the full isotropic Plücker ideal

The exterior naturality identity transports the entire ideal of isotropy
equations.  The resulting quotient equivalence retains the actual ideal;
no reducedness, saturation, or equality of closed points is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.AlternatingForms

open MvPolynomial
open scoped BigOperators

variable {K : Type*} [Field K] {t n m : ℕ}

/-- The isotropic scheme depends on the span of the two forms, with its
full original homogeneous ideal retained. -/
theorem pair_isotropicIdeal_eq_of_quadraticSpan_eq
    (f g f' g' : StrictPairs n → K)
    (h : Submodule.span K
      ({twoFormOfCoefficients f (Pi.basisFun K (Fin n)),
        twoFormOfCoefficients g (Pi.basisFun K (Fin n))} :
          Set (⋀[K]^2 (Fin n → K))) =
      Submodule.span K
      ({twoFormOfCoefficients f' (Pi.basisFun K (Fin n)),
        twoFormOfCoefficients g' (Pi.basisFun K (Fin n))} :
          Set (⋀[K]^2 (Fin n → K)))) :
    isotropicPluckerIdeal (t := t) (pairCoefficientForms f g) =
      isotropicPluckerIdeal (pairCoefficientForms f' g') := by
  rw [pair_isotropicIdeal_eq_linearIdeal, pair_isotropicIdeal_eq_linearIdeal,
    coefficientPairRelations_eq_exterior, coefficientPairRelations_eq_exterior]
  have he := exteriorRelationIdeal_eq_of_quadraticSpan_eq _ _ _ _ h
  simp only [exteriorDegreeRelations, he]

theorem coefficientWedge_linearMap
    (e : (Fin n → K) →ₗ[K] (Fin n → K))
    (f f' : StrictPairs n → K)
    (hf : exteriorPower.map 2 e (twoFormOfCoefficients f (Pi.basisFun K (Fin n))) =
      twoFormOfCoefficients f' (Pi.basisFun K (Fin n)))
    (x : ⋀[K]^t (Fin n → K)) :
    exteriorPower.map (t+2) e (coefficientWedge f x) =
      coefficientWedge f' (exteriorPower.map t e x) := by
  have hf' := congrArg Subtype.val hf
  simp only [exteriorPower.coe_map] at hf'
  apply Subtype.ext
  simp only [exteriorPower.coe_map]
  change (ExteriorAlgebra.map e)
      ((twoFormOfCoefficients f (Pi.basisFun K (Fin n)) :
        ExteriorAlgebra K (Fin n → K)) * (x : ExteriorAlgebra K (Fin n → K))) =
    (twoFormOfCoefficients f' (Pi.basisFun K (Fin n)) :
      ExteriorAlgebra K (Fin n → K)) *
        ((exteriorPower.map t e x) : ExteriorAlgebra K (Fin n → K))
  rw [map_mul, hf', exteriorPower.coe_map]

/-- Forward transport of every equation under the actual linear coordinate map. -/
theorem pluckerLinearAction_preserves_isotropicIdeal
    (e : (Fin n → K) →ₗ[K] (Fin n → K))
    (forms forms' : Fin m → StrictPairs n → K)
    (hforms : ∀ l, exteriorPower.map 2 e
      (twoFormOfCoefficients (forms l) (Pi.basisFun K (Fin n))) =
        twoFormOfCoefficients (forms' l) (Pi.basisFun K (Fin n))) :
    isotropicPluckerIdeal (t := t) forms ≤
      Ideal.comap (pluckerLinearAction e (t+2)).toRingHom
        (isotropicPluckerIdeal forms') := by
  rw [isotropicPluckerIdeal_eq_wedgeCoordinates]
  apply sup_le
  · intro p hp
    rw [Ideal.mem_comap, isotropicPluckerIdeal_eq_wedgeCoordinates]
    exact Ideal.mem_sup_left (pluckerLinearAction_preserves_matrixIdeal e p hp)
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨l,x⟩,rfl⟩
    change exteriorPluckerCoordinates (t+2) n (coefficientWedge (forms l) x) ∈
      Ideal.comap (pluckerLinearAction e (t+2)).toRingHom
        (isotropicPluckerIdeal forms')
    rw [Ideal.mem_comap]
    change pluckerLinearAction e (t+2)
      (exteriorPluckerCoordinates (t+2) n (coefficientWedge (forms l) x)) ∈ _
    rw [pluckerLinearAction_coordinates, coefficientWedge_linearMap e _ _ (hforms l)]
    rw [isotropicPluckerIdeal_eq_wedgeCoordinates]
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨(l,exteriorPower.map t e x),rfl⟩)

theorem twoForm_linearEquiv_reverse
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (f f' : StrictPairs n → K)
    (hf : exteriorPower.map 2 e.toLinearMap
      (twoFormOfCoefficients f (Pi.basisFun K (Fin n))) =
      twoFormOfCoefficients f' (Pi.basisFun K (Fin n))) :
    exteriorPower.map 2 e.symm.toLinearMap
      (twoFormOfCoefficients f' (Pi.basisFun K (Fin n))) =
      twoFormOfCoefficients f (Pi.basisFun K (Fin n)) := by
  rw [← hf]
  exact (exteriorPowerLinearEquiv e 2).symm_apply_apply _

/-- Exact equality of the original scheme ideals after an invertible coordinate change. -/
theorem pluckerLinearEquiv_map_isotropicIdeal
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (forms forms' : Fin m → StrictPairs n → K)
    (hforms : ∀ l, exteriorPower.map 2 e.toLinearMap
      (twoFormOfCoefficients (forms l) (Pi.basisFun K (Fin n))) =
        twoFormOfCoefficients (forms' l) (Pi.basisFun K (Fin n))) :
    Ideal.map (pluckerLinearEquiv e (t+2)).toRingHom
      (isotropicPluckerIdeal (t := t) forms) = isotropicPluckerIdeal forms' := by
  apply le_antisymm
  · exact Ideal.map_le_iff_le_comap.mpr
      (pluckerLinearAction_preserves_isotropicIdeal e.toLinearMap forms forms' hforms)
  · intro p hp
    let g := pluckerLinearEquiv e (t+2)
    have hg : g.symm p ∈ isotropicPluckerIdeal (t := t) forms :=
      pluckerLinearAction_preserves_isotropicIdeal e.symm.toLinearMap forms' forms
        (fun l => twoForm_linearEquiv_reverse e _ _ (hforms l)) hp
    have hm : g (g.symm p) ∈ Ideal.map g.toRingHom
        (isotropicPluckerIdeal (t := t) forms) :=
      Ideal.mem_map_of_mem g.toRingHom hg
    simpa only [AlgEquiv.apply_symm_apply] using hm

/-- The actual coordinate rings of linearly equivalent tuples of forms are equivalent. -/
def isotropicPluckerLinearEquiv
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (forms forms' : Fin m → StrictPairs n → K)
    (hforms : ∀ l, exteriorPower.map 2 e.toLinearMap
      (twoFormOfCoefficients (forms l) (Pi.basisFun K (Fin n))) =
        twoFormOfCoefficients (forms' l) (Pi.basisFun K (Fin n))) :
    (MvPolynomial (PluckerIndex (t+2) n) K ⧸ isotropicPluckerIdeal forms) ≃ₐ[K]
      (MvPolynomial (PluckerIndex (t+2) n) K ⧸ isotropicPluckerIdeal forms') :=
  Ideal.quotientEquivAlg _ _ (pluckerLinearEquiv e (t+2))
    (pluckerLinearEquiv_map_isotropicIdeal e forms forms' hforms).symm

@[simp] theorem isotropicPluckerLinearEquiv_mk
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (forms forms' : Fin m → StrictPairs n → K)
    (hforms : ∀ l, exteriorPower.map 2 e.toLinearMap
      (twoFormOfCoefficients (forms l) (Pi.basisFun K (Fin n))) =
        twoFormOfCoefficients (forms' l) (Pi.basisFun K (Fin n)))
    (p : MvPolynomial (PluckerIndex (t+2) n) K) :
    isotropicPluckerLinearEquiv e forms forms' hforms (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (pluckerLinearAction e.toLinearMap (t+2) p) := rfl

theorem pluckerLinearAction_homogeneous
    (e : (Fin n → K) →ₗ[K] (Fin n → K))
    (p : MvPolynomial (PluckerIndex (t+2) n) K) (d : ℕ)
    (hp : p.IsHomogeneous d) :
    (pluckerLinearAction e (t+2) p).IsHomogeneous d := by
  simpa only [pluckerLinearAction, one_mul] using hp.aeval
    (fun I => exteriorPluckerCoordinates (t+2) n
      (exteriorPower.map (t+2) e (exteriorPluckerBasis (t+2) n I)))
    (fun I => exteriorPluckerCoordinates_isHomogeneous _)

end PaperVerification.AlternatingForms
end
end
end ComponentSource_30

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsIsotropicLinearAction"

section ComponentSource_31
/- Original module: PaperVerification.AlternatingFormsIsotropicProjLinearAction -/


/-!
# Scheme isomorphisms induced by linear changes of the alternating forms

The coordinate-ring equivalence is graded in both directions.  Functoriality
of Mathlib's actual projective spectrum therefore supplies an isomorphism of
the original common-isotropic projective schemes.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory HomogeneousIdeal
open scoped HomogeneousIdeal

namespace PaperVerification

section GradedEquivalence

variable {K A B : Type} [CommRing K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]
  {𝒜 : ℕ → Submodule K A} {ℬ : ℕ → Submodule K B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

def gradedRingHomOfEquiv (e : A ≃ₐ[K] B)
    (he : ∀ d x, x ∈ 𝒜 d → e x ∈ ℬ d) : 𝒜 →+*ᵍ ℬ where
  __ := e.toRingHom
  map_mem hx := he _ _ hx

theorem irrelevant_le_map_of_inverse
    (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (hfg : ∀ x, f (g x) = x) : ℬ₊ ≤ 𝒜₊.map f := by
  apply toIdeal_le_toIdeal_iff.mp
  apply (HomogeneousIdeal.toIdeal_irrelevant_le ℬ).mpr
  intro d hd x hx
  have hg : g x ∈ 𝒜₊ :=
    HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hd (g.map_mem hx)
  change x ∈ (𝒜₊.map f).toIdeal
  rw [HomogeneousIdeal.toIdeal_map, ← hfg x]
  exact Ideal.mem_map_of_mem f hg

/-- A graded algebra equivalence induces an isomorphism of the actual schemes Proj. -/
def projIsoOfGradedAlgEquiv (e : A ≃ₐ[K] B)
    (he : ∀ d x, x ∈ 𝒜 d → e x ∈ ℬ d)
    (hi : ∀ d x, x ∈ ℬ d → e.symm x ∈ 𝒜 d) : Proj ℬ ≅ Proj 𝒜 := by
  let f := gradedRingHomOfEquiv e he
  let g := gradedRingHomOfEquiv e.symm hi
  have hf : ℬ₊ ≤ 𝒜₊.map f :=
    irrelevant_le_map_of_inverse f g e.apply_symm_apply
  have hg : 𝒜₊ ≤ ℬ₊.map g :=
    irrelevant_le_map_of_inverse g f e.symm_apply_apply
  have hfg : f.comp g = GradedRingHom.id ℬ := by
    ext x
    exact e.apply_symm_apply x
  have hgf : g.comp f = GradedRingHom.id 𝒜 := by
    ext x
    exact e.symm_apply_apply x
  refine ⟨Proj.map f hf, Proj.map g hg, ?_, ?_⟩
  · rw [← Proj.map_comp]
    simpa only [hfg] using (Proj.map_id (𝒜 := ℬ))
  · rw [← Proj.map_comp]
    simpa only [hgf] using (Proj.map_id (𝒜 := 𝒜))

end GradedEquivalence

namespace AlternatingForms

open MvPolynomial

variable {K : Type} [Field K] [CharZero K] {t n m : ℕ}

@[simp] theorem isotropicPluckerLinearEquiv_symm_mk
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (forms forms' : Fin m → StrictPairs n → K)
    (hforms : ∀ l, exteriorPower.map 2 e.toLinearMap
      (twoFormOfCoefficients (forms l) (Pi.basisFun K (Fin n))) =
        twoFormOfCoefficients (forms' l) (Pi.basisFun K (Fin n)))
    (p : MvPolynomial (PluckerIndex (t+2) n) K) :
    (isotropicPluckerLinearEquiv e forms forms' hforms).symm (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (pluckerLinearAction e.symm.toLinearMap (t+2) p) := rfl

theorem isotropicPluckerLinearEquiv_graded
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (forms forms' : Fin m → StrictPairs n → K)
    (hforms : ∀ l, exteriorPower.map 2 e.toLinearMap
      (twoFormOfCoefficients (forms l) (Pi.basisFun K (Fin n))) =
        twoFormOfCoefficients (forms' l) (Pi.basisFun K (Fin n)))
    (d : ℕ) (x : MvPolynomial (PluckerIndex (t+2) n) K ⧸ isotropicPluckerIdeal forms)
    (hx : x ∈ isotropicProjectiveGrading forms d) :
    isotropicPluckerLinearEquiv e forms forms' hforms x ∈
      isotropicProjectiveGrading forms' d := by
  change x ∈ HomogeneousQuotientProjective.grading _ _ d at hx
  rw [HomogeneousQuotientProjective.grading_eq_piece] at hx
  obtain ⟨p,hp,rfl⟩ := hx
  change _ ∈ HomogeneousQuotientProjective.grading _ _ d
  rw [HomogeneousQuotientProjective.grading_eq_piece]
  exact ⟨pluckerLinearAction e.toLinearMap (t+2) p,
    pluckerLinearAction_homogeneous e.toLinearMap p d hp,rfl⟩

theorem isotropicPluckerLinearEquiv_symm_graded
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (forms forms' : Fin m → StrictPairs n → K)
    (hforms : ∀ l, exteriorPower.map 2 e.toLinearMap
      (twoFormOfCoefficients (forms l) (Pi.basisFun K (Fin n))) =
        twoFormOfCoefficients (forms' l) (Pi.basisFun K (Fin n)))
    (d : ℕ) (x : MvPolynomial (PluckerIndex (t+2) n) K ⧸ isotropicPluckerIdeal forms')
    (hx : x ∈ isotropicProjectiveGrading forms' d) :
    (isotropicPluckerLinearEquiv e forms forms' hforms).symm x ∈
      isotropicProjectiveGrading forms d := by
  change x ∈ HomogeneousQuotientProjective.grading _ _ d at hx
  rw [HomogeneousQuotientProjective.grading_eq_piece] at hx
  obtain ⟨p,hp,rfl⟩ := hx
  change _ ∈ HomogeneousQuotientProjective.grading _ _ d
  rw [HomogeneousQuotientProjective.grading_eq_piece]
  exact ⟨pluckerLinearAction e.symm.toLinearMap (t+2) p,
    pluckerLinearAction_homogeneous e.symm.toLinearMap p d hp,rfl⟩

/-- Linearly equivalent tuples define isomorphic genuine common-isotropic schemes. -/
def isotropicProjLinearIso
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (forms forms' : Fin m → StrictPairs n → K)
    (hforms : ∀ l, exteriorPower.map 2 e.toLinearMap
      (twoFormOfCoefficients (forms l) (Pi.basisFun K (Fin n))) =
        twoFormOfCoefficients (forms' l) (Pi.basisFun K (Fin n))) :
    Proj (isotropicProjectiveGrading (t := t) forms') ≅
      Proj (isotropicProjectiveGrading (t := t) forms) :=
  projIsoOfGradedAlgEquiv (isotropicPluckerLinearEquiv e forms forms' hforms)
    (isotropicPluckerLinearEquiv_graded e forms forms' hforms)
    (isotropicPluckerLinearEquiv_symm_graded e forms forms' hforms)

end AlternatingForms
end PaperVerification
end
end
end ComponentSource_31

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsIsotropicProjLinearAction"

section ComponentSource_32
/- Original module: PaperVerification.ProjGradedAlgEquivOver -/


/-!
# Proj functoriality over the coefficient algebra

The structure morphism is the standard morphism through the degree-zero
part of the graded algebra.  A graded algebra equivalence preserves this
morphism, so geometric properties over the coefficient field transport.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory HomogeneousIdeal _root_.HomogeneousLocalization
open scoped HomogeneousIdeal

namespace PaperVerification

variable {K A B : Type} [CommRing K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]
  {𝒜 : ℕ → Submodule K A} {ℬ : ℕ → Submodule K B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

def gradedProjStructureMap (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜] :
    Proj 𝒜 ⟶ Spec (CommRingCat.of K) :=
  Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap K (𝒜 0)))

theorem gradedAwayMap_constant (e : A ≃ₐ[K] B)
    (he : ∀ d x, x ∈ 𝒜 d → e x ∈ ℬ d) (s : A) (c : K) :
    Away.map (gradedRingHomOfEquiv e he) s
      (fromZeroRingHom 𝒜 _ (algebraMap K (𝒜 0) c)) =
      fromZeroRingHom ℬ _ (algebraMap K (ℬ 0) c) := by
  apply _root_.HomogeneousLocalization.val_injective
  change Localization.mk (e (algebraMap K A c)) ⟨e 1, _⟩ =
    Localization.mk (algebraMap K B c) ⟨1, _⟩
  simp only [map_one, e.commutes]

/-- Every graded algebra morphism arising from an equivalence is over Spec K. -/
theorem gradedProjMap_over (e : A ≃ₐ[K] B)
    (he : ∀ d x, x ∈ 𝒜 d → e x ∈ ℬ d)
    (hf : ℬ₊ ≤ 𝒜₊.map (gradedRingHomOfEquiv e he)) :
    Proj.map (gradedRingHomOfEquiv e he) hf ≫ gradedProjStructureMap 𝒜 =
      gradedProjStructureMap ℬ := by
  let f := gradedRingHomOfEquiv e he
  apply (Proj.mapAffineOpenCover f hf).openCover.hom_ext
  intro s
  change Proj.awayι ℬ (f s.2.1) (f.map_mem s.2.2) s.1.2 ≫
      Proj.map f hf ≫ gradedProjStructureMap 𝒜 =
    Proj.awayι ℬ (f s.2.1) (f.map_mem s.2.2) s.1.2 ≫ gradedProjStructureMap ℬ
  simp only [gradedProjStructureMap, Category.assoc,
    Proj.awayι_comp_map_assoc f hf s.1.2 s.2.1 s.2.2,
    Proj.awayι_toSpecZero_assoc, Proj.awayι_toSpecZero]
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext c
  exact congrArg _root_.HomogeneousLocalization.val
    (gradedAwayMap_constant e he s.2.1 c)

theorem projIsoOfGradedAlgEquiv_hom_over (e : A ≃ₐ[K] B)
    (he : ∀ d x, x ∈ 𝒜 d → e x ∈ ℬ d)
    (hi : ∀ d x, x ∈ ℬ d → e.symm x ∈ 𝒜 d) :
    (projIsoOfGradedAlgEquiv e he hi).hom ≫ gradedProjStructureMap 𝒜 =
      gradedProjStructureMap ℬ :=
  gradedProjMap_over e he _

theorem projIsoOfGradedAlgEquiv_inv_over (e : A ≃ₐ[K] B)
    (he : ∀ d x, x ∈ 𝒜 d → e x ∈ ℬ d)
    (hi : ∀ d x, x ∈ ℬ d → e.symm x ∈ 𝒜 d) :
    (projIsoOfGradedAlgEquiv e he hi).inv ≫ gradedProjStructureMap ℬ =
      gradedProjStructureMap 𝒜 := by
  rw [← projIsoOfGradedAlgEquiv_hom_over e he hi, Iso.inv_hom_id_assoc]

end PaperVerification
end
end
end ComponentSource_32

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.ProjGradedAlgEquivOver"

section ComponentSource_33
/- Original module: PaperVerification.DominantPrincipalIntersection -/


/-!
# A dominant orbit meets every nonempty principal open

This supplies the precise existence step needed to combine an explicit
surjective orbit Jacobian with a generic geometric property.  It requires
neither an orbit-classification theorem nor algebraic closedness.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial

variable {K σ ι : Type*} [CommRing K] [IsDomain K] [Infinite K]
  [Fintype σ] [Finite ι]

/-- Every nonempty target principal open meets the image of a nonempty
source principal open under a polynomial parametrization with a surjective Jacobian. -/
theorem exists_dominant_principal_intersection
    (p : ι → MvPolynomial σ K) (v : σ → K)
    (hJ : (TauCeti.jacobiMatrixAt p v).mulVec.Surjective)
    (g : MvPolynomial σ K) (hg : g ≠ 0)
    (q : MvPolynomial ι K) (hq : q ≠ 0) :
    ∃ x : σ → K, eval x g ≠ 0 ∧
      eval (fun i => eval x (p i)) q ≠ 0 := by
  by_contra h
  apply hq
  apply polynomial_eq_zero_of_dominant_open_vanish hJ hg
  intro x hx
  by_contra hqx
  exact h ⟨x,hx,hqx⟩

end PaperVerification.AlternatingForms
end
end
end ComponentSource_33

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.DominantPrincipalIntersection"

section ComponentSource_34
/- Original module: PaperVerification.AlternatingFormsCoefficientFrames -/


/-!
# Full coefficient spaces and dominant orbit intersections

Increasing coordinate pairs give all coefficients of an alternating form.
The comparison with the blockwise odd-orbit coefficients is a proved linear
equivalence, so pulling back a nonzero genericity polynomial loses no points
or parameter directions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial
open scoped BigOperators Classical

variable {K : Type*} [Field K]

theorem strictPairSlots (n : ℕ) :
    OrbitPairSlots (fun a : StrictPairs n => a.val.1) (fun a => a.val.2) where
  injective := by
    intro a b hab
    exact Subtype.ext hab
  no_reverse := by
    intro a b h
    have ha := a.property
    have hb := b.property
    rw [h.1, h.2] at ha
    exact (not_lt_of_ge hb.le) ha
  covers := by
    intro u v huv
    rcases lt_or_gt_of_ne huv with h | h
    · exact ⟨⟨(u,v),h⟩,Or.inl ⟨rfl,rfl⟩⟩
    · exact ⟨⟨(v,u),h⟩,Or.inr ⟨rfl,rfl⟩⟩

/-- All increasing-pair coefficients, with the actual exterior two-form as value. -/
def strictCoefficientExteriorEquiv (n : ℕ) :
    (StrictPairs n → K) ≃ₗ[K] (⋀[K]^2 (Fin n → K)) :=
  orbitSlotLinearEquiv (strictPairSlots n)

@[simp] theorem strictCoefficientExteriorEquiv_apply (n : ℕ)
    (f : StrictPairs n → K) :
    strictCoefficientExteriorEquiv (K := K) n f =
      twoFormOfCoefficients f (Pi.basisFun K (Fin n)) := rfl

/-- The complete coefficient space used by generic smoothness parametrizes
every ordered pair of alternating forms bijectively. -/
def pairCoefficientExteriorEquiv (n : ℕ) :
    ((Fin 2 × StrictPairs n) → K) ≃ₗ[K]
      ((⋀[K]^2 (Fin n → K)) × (⋀[K]^2 (Fin n → K))) :=
  ((LinearEquiv.curry K K (Fin 2) (StrictPairs n)).trans
    (LinearEquiv.piCongrRight (fun _ : Fin 2 => strictCoefficientExteriorEquiv n))).trans
      (LinearEquiv.finTwoArrow K (⋀[K]^2 (Fin n → K)))

@[simp] theorem pairCoefficientExteriorEquiv_apply (n : ℕ)
    (a : (Fin 2 × StrictPairs n) → K) :
    pairCoefficientExteriorEquiv n a =
      (twoFormOfCoefficients (fun i => a (0,i)) (Pi.basisFun K (Fin n)),
       twoFormOfCoefficients (fun i => a (1,i)) (Pi.basisFun K (Fin n))) := rfl

/-- The actual permutation from the block orbit basis to path coordinates. -/
def oddOrbitToPathEquiv (t : ℕ) :
    (OddOrbitMode t → K) ≃ₗ[K] (Fin (2*(t+1)+1) → K) :=
  (standardBasisEquiv (oddOrbitInterleavedBasis t)).symm

/-- An invertible linear comparison of the two complete parameter spaces. -/
def oddOrbitToPairCoefficients (t : ℕ) :
    ((OddOrbitSlot t ⊕ OddOrbitSlot t) → K) ≃ₗ[K]
      ((Fin 2 × StrictPairs (2*(t+1)+1)) → K) :=
  (orbitPairCoordinateEquiv (oddOrbitExteriorBasis t)).trans
    (((exteriorPowerLinearEquiv (oddOrbitToPathEquiv t) 2).prodCongr
        (exteriorPowerLinearEquiv (oddOrbitToPathEquiv t) 2)).trans
      (pairCoefficientExteriorEquiv (2*(t+1)+1)).symm)

theorem oddOrbitToPairCoefficients_forms (t : ℕ)
    (y : (OddOrbitSlot t ⊕ OddOrbitSlot t) → K) :
    pairCoefficientExteriorEquiv (2*(t+1)+1)
        (oddOrbitToPairCoefficients t y) =
      (exteriorPower.map 2 (oddOrbitToPathEquiv t).toLinearMap
        (orbitFormsFromCoordinates (oddOrbitExteriorBasis t) y).1,
       exteriorPower.map 2 (oddOrbitToPathEquiv t).toLinearMap
        (orbitFormsFromCoordinates (oddOrbitExteriorBasis t) y).2) := by
  simp only [oddOrbitToPairCoefficients, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, LinearEquiv.prodCongr_apply,
    orbitPairCoordinateEquiv_apply, exteriorPowerLinearEquiv_apply]

section PolynomialPullback

variable {σ ι : Type*} [Fintype σ]

/-- The literal linear polynomials of a linear map between affine coefficient spaces. -/
def linearCoefficientPolynomials (L : (σ → K) →ₗ[K] (ι → K)) :
    ι → MvPolynomial σ K :=
  fun i => ∑ j, (L (Pi.basisFun K σ j) i) • X j

theorem linearCoefficientPolynomials_eval (L : (σ → K) →ₗ[K] (ι → K))
    (x : σ → K) (i : ι) :
    eval x (linearCoefficientPolynomials L i) = L x i := by
  simp only [linearCoefficientPolynomials, Algebra.smul_def, MvPolynomial.algebraMap_eq,
    map_sum, map_mul, eval_C, eval_X]
  have hx := (Pi.basisFun K σ).sum_repr x
  have h := congrArg (fun v => L v i) hx
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    Pi.basisFun_repr, smul_eq_mul] at h
  simpa only [mul_comm] using h

def linearCoefficientPullback (L : (σ → K) →ₗ[K] (ι → K)) :
    MvPolynomial ι K →ₐ[K] MvPolynomial σ K :=
  aeval (linearCoefficientPolynomials L)

theorem linearCoefficientPullback_eval (L : (σ → K) →ₗ[K] (ι → K))
    (q : MvPolynomial ι K) (x : σ → K) :
    eval x (linearCoefficientPullback L q) = eval (L x) q := by
  change eval x (aeval (linearCoefficientPolynomials L) q) = eval (L x) q
  rw [aeval_eq_bind₁]
  simpa only [aeval_eq_eval, linearCoefficientPolynomials_eval] using
    aeval_bind₁ x (linearCoefficientPolynomials L) q

/-- A surjective linear coordinate change pulls a nonzero polynomial back nontrivially. -/
theorem linearCoefficientPullback_ne_zero [Infinite K]
    (L : (σ → K) →ₗ[K] (ι → K)) (hL : Function.Surjective L)
    (q : MvPolynomial ι K) (hq : q ≠ 0) :
    linearCoefficientPullback L q ≠ 0 := by
  intro h
  apply hq
  apply MvPolynomial.funext
  intro y
  obtain ⟨x,rfl⟩ := hL y
  rw [← linearCoefficientPullback_eval, h, map_zero, map_zero]

end PolynomialPullback

/-- Every nonzero polynomial in the full ordinary pair-coefficient space
is nonzero at an invertible point of the actual canonical odd orbit. -/
theorem oddOrbit_meets_principal_open [Infinite K] (t : ℕ)
    (q : MvPolynomial (Fin 2 × StrictPairs (2*(t+1)+1)) K) (hq : q ≠ 0) :
    ∃ x : (OddOrbitMode t × OddOrbitMode t) → K,
      eval x (orbitDeterminant (K := K) (ν := OddOrbitMode t)) ≠ 0 ∧
      eval (oddOrbitToPairCoefficients t
        (fun i => eval x (orbitPairPolynomialCoordinates
          (actualOrbitPolynomials (row := oddOrbitSlotRow t) (col := oddOrbitSlotCol t)
            (oddOrbitFirstForm t) (oddOrbitSecondForm t)) i))) q ≠ 0 := by
  let p := actualOrbitPolynomials (row := oddOrbitSlotRow t) (col := oddOrbitSlotCol t)
    (oddOrbitFirstForm (K := K) t) (oddOrbitSecondForm t)
  let L := (oddOrbitToPairCoefficients (K := K) t).toLinearMap
  have hJ := jacobian_surjective_reindex p orbitIdentityPoint
    (Equiv.boolProdEquivSum (OddOrbitSlot t)).symm (oddOrbit_actual_jacobian_surjective t)
  obtain ⟨x,hx,hqx⟩ := exists_dominant_principal_intersection
    (orbitPairPolynomialCoordinates p) orbitIdentityPoint hJ
    orbitDeterminant orbitDeterminant_ne_zero (linearCoefficientPullback L q)
    (linearCoefficientPullback_ne_zero L (oddOrbitToPairCoefficients t).surjective q hq)
  refine ⟨x,hx,?_⟩
  rw [linearCoefficientPullback_eval] at hqx
  simpa only [L, p, LinearEquiv.coe_coe] using hqx

end PaperVerification.AlternatingForms
end
end
end ComponentSource_34

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsCoefficientFrames"

section ComponentSource_35
/- Original module: PaperVerification.AlternatingFormsCanonicalOddSmoothness -/


/-!
# Smoothness of the actual canonical odd common-isotropic scheme

An explicit surjective orbit Jacobian makes the invertible odd orbit meet
the proved generic-smoothness open.  The genuine Proj isomorphism transports
smoothness to the canonical pair.  This is independent of a classification
of pencils, a Borel fixed-point theorem, or a reduced-point interpretation.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped BigOperators Classical

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] [CharZero K] {t n m : ℕ}

theorem isotropicProjLinearIso_hom_over
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (forms forms' : Fin m → StrictPairs n → K)
    (hforms : ∀ l, exteriorPower.map 2 e.toLinearMap
      (twoFormOfCoefficients (forms l) (Pi.basisFun K (Fin n))) =
        twoFormOfCoefficients (forms' l) (Pi.basisFun K (Fin n))) :
    (isotropicProjLinearIso (t := t) e forms forms' hforms).hom ≫
      isotropicStructureMap forms = isotropicStructureMap forms' :=
  projIsoOfGradedAlgEquiv_hom_over _ _ _

theorem isotropicProjLinearIso_inv_over
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (forms forms' : Fin m → StrictPairs n → K)
    (hforms : ∀ l, exteriorPower.map 2 e.toLinearMap
      (twoFormOfCoefficients (forms l) (Pi.basisFun K (Fin n))) =
        twoFormOfCoefficients (forms' l) (Pi.basisFun K (Fin n))) :
    (isotropicProjLinearIso (t := t) e forms forms' hforms).inv ≫
      isotropicStructureMap forms' = isotropicStructureMap forms :=
  projIsoOfGradedAlgEquiv_inv_over _ _ _

/-- Smoothness transports over the original coefficient field. -/
theorem isotropicStructureMap_smooth_linearEquiv
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (forms forms' : Fin m → StrictPairs n → K)
    (hforms : ∀ l, exteriorPower.map 2 e.toLinearMap
      (twoFormOfCoefficients (forms l) (Pi.basisFun K (Fin n))) =
        twoFormOfCoefficients (forms' l) (Pi.basisFun K (Fin n))) :
    Smooth (isotropicStructureMap (t := t) forms) ↔
      Smooth (isotropicStructureMap (t := t) forms') := by
  constructor
  · intro h
    letI := h
    rw [← isotropicProjLinearIso_hom_over e forms forms' hforms]
    infer_instance
  · intro h
    letI := h
    rw [← isotropicProjLinearIso_inv_over e forms forms' hforms]
    infer_instance

theorem isotropicStructureMap_smooth_of_ideal_eq
    (forms forms' : Fin m → StrictPairs n → K)
    (hI : isotropicPluckerIdeal (t := t) forms = isotropicPluckerIdeal forms') :
    Smooth (isotropicStructureMap (t := t) forms) ↔
      Smooth (isotropicStructureMap (t := t) forms') := by
  have h (Q Q' : Ideal (MvPolynomial (PluckerIndex (t+2) n) K))
      (hQ : Q.IsHomogeneous (homogeneousSubmodule _ K))
      (hQ' : Q'.IsHomogeneous (homogeneousSubmodule _ K)) (he : Q = Q') :
      Smooth (HomogeneousQuotientCharts.structureMap Q hQ) ↔
        Smooth (HomogeneousQuotientCharts.structureMap Q' hQ') := by
    subst Q'
    rfl
  exact h _ _ _ _ hI

theorem oddOrbitToPath_first (k : ℕ) :
    exteriorPower.map 2 (oddOrbitToPathEquiv (K := K) k).toLinearMap
      (oddOrbitFirstForm k) =
    twoFormOfCoefficients (oddPluckerForms (k+1) 1)
      (Pi.basisFun K (Fin (2*(k+1)+1))) := by
  rw [oddOrbitFirstForm_eq_path, oddPluckerForms_second]
  rw [oddPathSecondQuadratic_map]
  congr 1
  funext i
  change (standardBasisEquiv (oddOrbitInterleavedBasis (K := K) k)).symm
    (oddOrbitInterleavedBasis k i) = Pi.basisFun K (Fin (2*(k+1)+1)) i
  apply (standardBasisEquiv (oddOrbitInterleavedBasis (K := K) k)).injective
  rw [LinearEquiv.apply_symm_apply, standardBasisEquiv_basisFun]

theorem oddOrbitToPath_second (k : ℕ) :
    exteriorPower.map 2 (oddOrbitToPathEquiv (K := K) k).toLinearMap
      (oddOrbitSecondForm k) =
    -twoFormOfCoefficients (oddPluckerForms (k+1) 0)
      (Pi.basisFun K (Fin (2*(k+1)+1))) := by
  rw [oddOrbitSecondForm_eq_path, map_neg, oddPluckerForms_first]
  congr 1
  rw [oddPathFirstQuadratic_map]
  congr 1
  funext i
  change (standardBasisEquiv (oddOrbitInterleavedBasis (K := K) k)).symm
    (oddOrbitInterleavedBasis k i) = Pi.basisFun K (Fin (2*(k+1)+1)) i
  apply (standardBasisEquiv (oddOrbitInterleavedBasis (K := K) k)).injective
  rw [LinearEquiv.apply_symm_apply, standardBasisEquiv_basisFun]

/-- Conjugating the ambient linear action commutes with every exterior power. -/
theorem exteriorPower_conjugate_apply
    {M N : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (e : M ≃ₗ[K] N) (g : M ≃ₗ[K] M) (d : ℕ) (x : ⋀[K]^d M) :
    exteriorPower.map d (e.symm.trans (g.trans e)).toLinearMap
      (exteriorPower.map d e.toLinearMap x) =
      exteriorPower.map d e.toLinearMap (exteriorPower.map d g.toLinearMap x) := by
  have he : (e.symm.trans (g.trans e)).toLinearMap.comp e.toLinearMap =
      e.toLinearMap.comp g.toLinearMap := by
    ext v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply]
  change ((exteriorPower.map d (e.symm.trans (g.trans e)).toLinearMap).comp
    (exteriorPower.map d e.toLinearMap)) x = _
  rw [← exteriorPower.map_comp, he, exteriorPower.map_comp]
  rfl

/-- The actual canonical odd common-isotropic scheme is smooth, in every
ambient odd dimension at least three and for every plane dimension at least two. -/
theorem canonicalOdd_isotropicStructureMap_smooth_succ (k t : ℕ) :
    Smooth (isotropicStructureMap (t := t) (oddPluckerForms (K := K) (k+1))) := by
  letI : Infinite K := Infinite.of_injective Nat.cast Nat.cast_injective
  let n := 2*(k+1)+1
  obtain ⟨Q,hQ,_,hsmooth⟩ := generic_commonIsotropic_smooth (K := K) t n 2
  obtain ⟨x,hx,hQx⟩ := oddOrbit_meets_principal_open k Q hQ
  let p := actualOrbitPolynomials (row := oddOrbitSlotRow k) (col := oddOrbitSlotCol k)
    (oddOrbitFirstForm (K := K) k) (oddOrbitSecondForm k)
  let base := orbitPairCoefficientPoint
    (actualOrbitBasePoint (row := oddOrbitSlotRow k) (col := oddOrbitSlotCol k)
      (oddOrbitFirstForm (K := K) k) (oddOrbitSecondForm k))
  let y := fun i => eval x (orbitPairPolynomialCoordinates p i)
  let a := oddOrbitToPairCoefficients k y
  let b := oddOrbitToPairCoefficients k base
  let forms : Fin 2 → StrictPairs n → K := fun l i => b (l,i)
  let forms' : Fin 2 → StrictPairs n → K := fun l i => a (l,i)
  have hs : Smooth (isotropicStructureMap (t := t) forms') :=
    hsmooth a (by simpa only [aeval_eq_eval] using hQx)
  let X : Matrix (OddOrbitMode k) (OddOrbitMode k) K := Matrix.of (fun i j => x (i,j))
  have hX : X.det ≠ 0 := by simpa only [X, orbitDeterminant_eval] using hx
  let g := orbitTransposeEquiv X hX
  let e := oddOrbitToPathEquiv (K := K) k
  let E := e.symm.trans (g.trans e)
  have hb : (twoFormOfCoefficients (forms 0) (Pi.basisFun K (Fin n)),
      twoFormOfCoefficients (forms 1) (Pi.basisFun K (Fin n))) =
      (exteriorPower.map 2 e.toLinearMap (oddOrbitFirstForm k),
       exteriorPower.map 2 e.toLinearMap (oddOrbitSecondForm k)) := by
    change pairCoefficientExteriorEquiv n b = _
    rw [oddOrbitToPairCoefficients_forms]
    dsimp only [base, oddOrbitExteriorBasis]
    rw [actualOrbitBasePoint_forms]
  have ha : (twoFormOfCoefficients (forms' 0) (Pi.basisFun K (Fin n)),
      twoFormOfCoefficients (forms' 1) (Pi.basisFun K (Fin n))) =
      (exteriorPower.map 2 e.toLinearMap
        (exteriorPower.map 2 g.toLinearMap (oddOrbitFirstForm k)),
       exteriorPower.map 2 e.toLinearMap
        (exteriorPower.map 2 g.toLinearMap (oddOrbitSecondForm k))) := by
    change pairCoefficientExteriorEquiv n a = _
    rw [oddOrbitToPairCoefficients_forms]
    dsimp only [y, p, oddOrbitExteriorBasis]
    rw [actualOrbitPolynomials_forms_eval (oddOrbitPairSlots k)]
    rfl
  have hforms (l : Fin 2) : exteriorPower.map 2 E.toLinearMap
      (twoFormOfCoefficients (forms l) (Pi.basisFun K (Fin n))) =
        twoFormOfCoefficients (forms' l) (Pi.basisFun K (Fin n)) := by
    fin_cases l
    · change exteriorPower.map 2 E.toLinearMap
        (twoFormOfCoefficients (forms 0) (Pi.basisFun K (Fin n))) =
          twoFormOfCoefficients (forms' 0) (Pi.basisFun K (Fin n))
      rw [show twoFormOfCoefficients (forms 0) (Pi.basisFun K (Fin n)) = _ from
        congrArg Prod.fst hb,
        show twoFormOfCoefficients (forms' 0) (Pi.basisFun K (Fin n)) = _ from
          congrArg Prod.fst ha]
      exact exteriorPower_conjugate_apply e g 2 (oddOrbitFirstForm k)
    · change exteriorPower.map 2 E.toLinearMap
        (twoFormOfCoefficients (forms 1) (Pi.basisFun K (Fin n))) =
          twoFormOfCoefficients (forms' 1) (Pi.basisFun K (Fin n))
      rw [show twoFormOfCoefficients (forms 1) (Pi.basisFun K (Fin n)) = _ from
        congrArg Prod.snd hb,
        show twoFormOfCoefficients (forms' 1) (Pi.basisFun K (Fin n)) = _ from
          congrArg Prod.snd ha]
      exact exteriorPower_conjugate_apply e g 2 (oddOrbitSecondForm k)
  have hsbase := (isotropicStructureMap_smooth_linearEquiv
    (t := t) E forms forms' hforms).mpr hs
  have hb₀ := congrArg Prod.fst hb
  have hb₁ := congrArg Prod.snd hb
  change twoFormOfCoefficients (forms 0) (Pi.basisFun K (Fin n)) =
    exteriorPower.map 2 (oddOrbitToPathEquiv k).toLinearMap (oddOrbitFirstForm k) at hb₀
  change twoFormOfCoefficients (forms 1) (Pi.basisFun K (Fin n)) =
    exteriorPower.map 2 (oddOrbitToPathEquiv k).toLinearMap (oddOrbitSecondForm k) at hb₁
  rw [oddOrbitToPath_first] at hb₀
  rw [oddOrbitToPath_second] at hb₁
  have heForms : forms = pairCoefficientForms (forms 0) (forms 1) := by
    funext l
    fin_cases l <;> rfl
  have heCanonical : oddPluckerForms (K := K) (k+1) =
      pairCoefficientForms (oddPluckerForms (k+1) 0) (oddPluckerForms (k+1) 1) := by
    funext l
    fin_cases l <;> rfl
  have hI : isotropicPluckerIdeal (t := t) forms =
      isotropicPluckerIdeal (oddPluckerForms (K := K) (k+1)) := by
    rw [heForms,heCanonical]
    apply pair_isotropicIdeal_eq_of_quadraticSpan_eq
    rw [hb₀,hb₁]
    exact (quadraticSpan_swap_neg _ _).symm
  exact (isotropicStructureMap_smooth_of_ideal_eq forms _ hI).mp hsbase

/-- The dimension-one boundary has a unique coefficient tuple; generic
smoothness therefore applies to that tuple itself. -/
theorem canonicalOdd_isotropicStructureMap_smooth_zero (t : ℕ) :
    Smooth (isotropicStructureMap (t := t) (oddPluckerForms (K := K) 0)) := by
  obtain ⟨Q,hQ,⟨a,ha⟩,hsmooth⟩ := generic_commonIsotropic_smooth (K := K) t 1 2
  have he : (fun l i => a (l,i)) = oddPluckerForms (K := K) 0 := by
    funext l i
    have hi := i.property
    have h₀ := i.val.1.isLt
    have h₁ := i.val.2.isLt
    change i.val.1.val < i.val.2.val at hi
    omega
  exact (congrArg (fun forms : Fin 2 → StrictPairs 1 → K =>
    Smooth (isotropicStructureMap (t := t) forms)) he).mp (hsmooth a ha)

/-- Uniform canonical odd smoothness with no omitted ambient dimension. -/
theorem canonicalOdd_isotropicStructureMap_smooth (k t : ℕ) :
    Smooth (isotropicStructureMap (t := t) (oddPluckerForms (K := K) k)) := by
  cases k with
  | zero => exact canonicalOdd_isotropicStructureMap_smooth_zero t
  | succ k => exact canonicalOdd_isotropicStructureMap_smooth_succ k t

/-- An actual isotropic row chart over the coefficient field supplies a point
of the original projective scheme. -/
theorem isotropicProj_nonempty_of_chart_point
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K)
    (A : IsotropicChartPoint p forms K) :
    Nonempty (Proj (isotropicProjectiveGrading (t := t) forms)) := by
  let x : Spec (CommRingCat.of K) := Classical.arbitrary _
  let z := (Spec.map (CommRingCat.ofHom A.toAlgHom.toRingHom)) x
  let y := (isotropicProjBasicOpenIso p forms).inv z
  exact ⟨y.val⟩

/-- The canonical odd scheme is nonempty throughout the paper's entire
plane range. Its witness is the original coordinate plane on even path vertices. -/
theorem canonicalOdd_isotropicProj_nonempty (k t : ℕ) (h : t+2 ≤ k+1) :
    Nonempty (Proj (isotropicProjectiveGrading (t := t) (oddPluckerForms (K := K) k))) := by
  let p := oddCoordinatePivot k t h
  apply isotropicProj_nonempty_of_chart_point p (oddPluckerForms k)
  refine ⟨pluckerCoordinatePlane p, ?_, oddCoordinatePlane_isotropic k t h⟩
  ext i j
  simp only [Matrix.submatrix_apply, id_eq, pluckerCoordinatePlane, Matrix.one_apply,
    p.property.injective.eq_iff, eq_comm]

/-- Smoothness and nonemptiness for every canonical odd case of plane
dimension at least two occurring in Section 4. -/
theorem canonicalOdd_isotropicProj_nonempty_smooth
    (k t : ℕ) (h : t+2 ≤ k+1) :
    Nonempty (Proj (isotropicProjectiveGrading (t := t) (oddPluckerForms (K := K) k))) ∧
      Smooth (isotropicStructureMap (t := t) (oddPluckerForms (K := K) k)) :=
  ⟨canonicalOdd_isotropicProj_nonempty k t h,
    canonicalOdd_isotropicStructureMap_smooth k t⟩

end PaperVerification.AlternatingForms
end
end
end ComponentSource_35

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsCanonicalOddSmoothness"

section ComponentSource_36
/- Original module: PaperVerification.AlternatingFormsSectionFourGeometry -/


/-!
# The geometric clauses of Section 4 in the paper's coordinates

The Section 4 pair is literally `(G, -F)` in path coordinates. Equality of
the homogeneous defining ideals transports smoothness and nonemptiness,
as it already transports the finite-dimensional rationality witness.

`sectionFourPositiveRankOver k r` is the original scheme of `(r+1)`-planes.
Its two branches are the actual one-plane restriction ideal and the actual
rank-`t+2` restriction ideal. The branch equalities below make this indexing
explicit. The final theorem covers every `1 ≤ s ≤ k+1`, including `k = 0`.
It concerns the geometric clauses; it does not assert a cohomology or Chow
presentation.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] [CharZero K]

/-- The smoothness statement uses exactly the two forms printed in Section 4. -/
theorem sectionFour_isotropicStructureMap_smooth (k t : ℕ) :
    Smooth (isotropicStructureMap (t := t) (sectionFourPluckerForms (K := K) k)) :=
  (isotropicStructureMap_smooth_of_ideal_eq _ _
    (sectionFour_isotropicPluckerIdeal k t)).mpr
      (canonicalOdd_isotropicStructureMap_smooth k t)

/-- Equality of homogeneous ideals preserves the actual Proj and its points. -/
theorem sectionFour_isotropicProj_nonempty (k t : ℕ) (h : t+2 ≤ k+1) :
    Nonempty (Proj
      (isotropicProjectiveGrading (t := t) (sectionFourPluckerForms (K := K) k))) := by
  let H := {Q : Ideal (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K) //
    Q.IsHomogeneous (homogeneousSubmodule (PluckerIndex (t+2) (2*k+1)) K)}
  let P : H → Prop := fun Q =>
    Nonempty (Proj (HomogeneousQuotientProjective.grading Q.val Q.property))
  let Q₁ : H := ⟨isotropicPluckerIdeal (t := t) (sectionFourPluckerForms (K := K) k),
    isotropicPluckerIdeal_isHomogeneous (sectionFourPluckerForms k)⟩
  let Q₂ : H := ⟨isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k),
    isotropicPluckerIdeal_isHomogeneous (oddPluckerForms k)⟩
  have hQ : Q₁ = Q₂ := Subtype.ext (sectionFour_isotropicPluckerIdeal k t)
  change P Q₁
  rw [hQ]
  exact canonicalOdd_isotropicProj_nonempty k t h

/-- The actual Section 4 common-isotropic scheme of `(r+1)`-planes over `K`. -/
def sectionFourPositiveRankOver (k : ℕ) : ℕ → Over (Spec (CommRingCat.of K))
  | 0 => onePlaneIsotropicOver (sectionFourPluckerForms k)
  | t+1 => Over.mk (isotropicStructureMap (t := t) (sectionFourPluckerForms k))

@[simp] theorem sectionFourPositiveRankOver_zero (k : ℕ) :
    sectionFourPositiveRankOver (K := K) k 0 =
      onePlaneIsotropicOver (sectionFourPluckerForms k) := rfl

@[simp] theorem sectionFourPositiveRankOver_succ (k t : ℕ) :
    sectionFourPositiveRankOver (K := K) k (t+1) =
      Over.mk (isotropicStructureMap (t := t) (sectionFourPluckerForms k)) := rfl

/-- Nonemptiness, smoothness, and a finite affine birational witness in every
positive plane rank allowed in Section 4. All maps are over the original field. -/
theorem sectionFour_positive_rank_geometry (k r : ℕ) (hr : r ≤ k) :
    Nonempty (sectionFourPositiveRankOver (K := K) k r).left ∧
      Smooth (sectionFourPositiveRankOver (K := K) k r).hom ∧
      ∃ N : Type, Finite N ∧ Scheme.BirationalOver
        (sectionFourPositiveRankOver (K := K) k r).hom
        (𝔸(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) := by
  cases r with
  | zero =>
      have hg := onePlaneIsotropic_geometry (sectionFourPluckerForms (K := K) k)
        (by omega : 0 < 2*k+1)
      exact ⟨hg.1, hg.2.1,
        onePlaneIsotropic_finite_rationality k (sectionFourPluckerForms k)⟩
  | succ t =>
      obtain ⟨N, hN, _, hbir⟩ :=
        paper_theorem_4_1_section_four_finite_rationality (K := K) k t hr
      exact ⟨sectionFour_isotropicProj_nonempty k t (by omega),
        sectionFour_isotropicStructureMap_smooth k t, N, hN, hbir⟩

/-- The shift in the uniform positive-rank indexing recovers the paper's rank. -/
theorem sectionFour_paper_rank (s : ℕ) (hs : 1 ≤ s) : s-1+1 = s := by omega

/-- The complete range of the smoothness and rationality clauses, stated with
the paper's parameters `k` and `s`. The represented plane rank is exactly `s`
by `sectionFour_paper_rank`; the case `s = 1` uses the proved line equations. -/
theorem paper_theorem_4_1_geometric_clauses
    (k s : ℕ) (hs : 1 ≤ s) (hsk : s ≤ k+1) :
    Nonempty (sectionFourPositiveRankOver (K := K) k (s-1)).left ∧
      Smooth (sectionFourPositiveRankOver (K := K) k (s-1)).hom ∧
      ∃ N : Type, Finite N ∧ Scheme.BirationalOver
        (sectionFourPositiveRankOver (K := K) k (s-1)).hom
        (𝔸(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) :=
  sectionFour_positive_rank_geometry k (s-1) (by omega)

end PaperVerification.AlternatingForms
end
end
end ComponentSource_36

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsSectionFourGeometry"


set_option pp.explicit false
set_option pp.proofs false
set_option pp.deepTerms false
set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let opts ← getOptions
  if true && env.header.trustLevel != 0 then
    throwError "The final environment has nonzero kernel trust level"
  if Lean.debug.skipKernelTC.get opts then
    throwError "The final environment disabled kernel type checking"
  if Lean.Elab.inServer.get opts then
    throwError "The final environment unexpectedly uses server mode"
  let required : Array (Name × String) := #[
    (`PaperVerification.GenericSectionDifferentials.section_differentials_linearIndependent, "theorem"),
    (`PaperVerification.GenericSectionDifferentials.critical_parameters_polynomial_image, "theorem"),
    (`PaperVerification.GenericSectionDifferentials.critical_incidence_polynomial, "theorem"),
    (`PaperVerification.GenericSectionDifferentials.formallySmooth_of_dual_derivations, "theorem"),
    (`PaperVerification.GenericSectionDifferentials.formallySmooth_of_jacobian_rightInverse, "theorem"),
    (`PaperVerification.GenericSectionDifferentials.universal_critical_parameter_polynomial, "theorem"),
    (`PaperVerification.GenericSectionDifferentials.critical_specialization_polynomial_zero, "theorem"),
    (`PaperVerification.GenericSectionDifferentials.specialized_gradient_linearIndependent, "theorem"),
    (`PaperVerification.GenericSectionDifferentials.matrix_rightInverse_of_residue_rows, "theorem"),
    (`PaperVerification.GenericSectionDifferentials.linearSection_quotient_smooth, "theorem"),
    (`PaperVerification.GenericSectionDifferentials.exists_linearSection_smooth, "theorem"),
    (`PaperVerification.GenericSectionDifferentials.linearSection_card_le_of_point, "theorem"),
    (`PaperVerification.GenericSectionDifferentials.linearSection_ideal_eq_top_of_more_equations, "theorem"),
    (`PaperVerification.AlternatingForms.chartSectionEvaluation_rightInverse, "theorem"),
    (`PaperVerification.AlternatingForms.chartSectionEvaluation_sum, "theorem"),
    (`PaperVerification.AlternatingForms.isotropicChartRing_smooth_of_polynomial, "theorem"),
    (`PaperVerification.AlternatingForms.isotropicStructureMap_smooth, "theorem"),
    (`PaperVerification.AlternatingForms.generic_commonIsotropic_smooth, "theorem"),
    (`PaperVerification.AlternatingForms.isotropicChartIdeal_eq_top_of_negative_dimension, "theorem"),
    (`PaperVerification.AlternatingForms.generic_commonIsotropic_empty_of_negative_dimension, "theorem"),
    (`PaperVerification.CommonIsotropicSubspace.exists_common_isotropic_vectors, "theorem"),
    (`PaperVerification.AlternatingForms.commonIsotropicProj_nonempty_of_dimension, "theorem"),
    (`PaperVerification.AlternatingForms.onePlaneOriginalProj_nonempty, "theorem"),
    (`PaperVerification.GenericSectionDifferentials.linearSection_residue_pderiv_rows, "theorem"),
    (`PaperVerification.GenericSectionDifferentials.linearSection_quotient_locally_standardSmoothOfRelativeDimension, "theorem"),
    (`PaperVerification.AlternatingForms.isotropicStructureMap_smoothOfRelativeDimension, "theorem"),
    (`PaperVerification.AlternatingForms.generic_pair_commonIsotropic_smooth_nonempty, "theorem"),
    (`PaperVerification.AlternatingForms.generic_pair_commonIsotropic_empty, "theorem"),
    (`PaperVerification.AlternatingForms.generic_pair_commonIsotropic_geometry, "theorem"),
    (`PaperVerification.AlternatingForms.onePlaneOriginal_geometry, "theorem"),
    (`PaperVerification.AlternatingForms.onePlaneOriginalProj_zero_empty, "theorem"),
    (`PaperVerification.AlternatingForms.isotropicChartIdealAtRank_eq, "theorem"),
    (`PaperVerification.AlternatingForms.onePlane_restriction_multiples, "theorem"),
    (`PaperVerification.AlternatingForms.onePlaneChartRestrictionIdeal_eq_bot, "theorem"),
    (`PaperVerification.AlternatingForms.onePlaneHomogeneousRestrictionIdeal_eq_bot, "theorem"),
    (`PaperVerification.AlternatingForms.onePlaneIsotropicOver_eq, "theorem"),
    (`PaperVerification.AlternatingForms.onePlaneIsotropic_geometry, "theorem"),
    (`PaperVerification.AlternatingForms.onePlaneIsotropic_zero_empty, "theorem"),
    (`PaperVerification.AlternatingForms.paper_theorem_4_1_finite_rationality_at_least_two, "theorem"),
    (`PaperVerification.AlternatingForms.paper_theorem_4_1_finite_rationality_one_plane, "theorem"),
    (`PaperVerification.AlternatingForms.oddIsotropicBigCellAffineIso, "definition"),
    (`PaperVerification.AlternatingForms.oddIsotropicBigCellAffineIso_over, "theorem"),
    (`PaperVerification.AlternatingForms.card_oddAffineFreeVariable, "theorem"),
    (`PaperVerification.AlternatingForms.paper_theorem_4_1_rationality_with_dimension_at_least_two, "theorem"),
    (`PaperVerification.AlternatingForms.sectionFour_first_coefficients, "theorem"),
    (`PaperVerification.AlternatingForms.sectionFour_second_coefficients, "theorem"),
    (`PaperVerification.AlternatingForms.sectionFour_isotropicPluckerIdeal, "theorem"),
    (`PaperVerification.AlternatingForms.paper_theorem_4_1_section_four_finite_rationality, "theorem"),
    (`PaperVerification.AlternatingForms.paper_theorem_4_1_section_four_rationality, "theorem"),
    (`PaperVerification.AlternatingForms.onePlaneIsotropic_finite_rationality, "theorem"),
    (`PaperVerification.AlternatingForms.isotropicSmoothnessPolynomial, "definition"),
    (`PaperVerification.AlternatingForms.isotropicSmoothnessPolynomial_ne_zero, "theorem"),
    (`PaperVerification.AlternatingForms.isotropic_all_charts_smooth, "theorem"),
    (`PaperVerification.AlternatingForms.exists_isotropic_all_charts_smooth, "theorem"),
    (`PaperVerification.AlternatingForms.isotropicStructureMap, "definition"),
    (`PaperVerification.AlternatingForms.isotropicProjBasicOpenIso_hom_over, "theorem"),
    (`PaperVerification.CommonIsotropicSubspace.exists_common_isotropic, "theorem"),
    (`PaperVerification.AlternatingForms.onePlaneOriginalStructureMap, "definition"),
    (`PaperVerification.AlternatingForms.onePlaneOriginalAffineIso, "definition"),
    (`PaperVerification.AlternatingForms.onePlaneOriginalAffineIso_over, "theorem"),
    (`PaperVerification.AlternatingForms.onePlaneOriginal_basicOpen_cover, "theorem"),
    (`PaperVerification.AlternatingForms.onePlaneOriginalStructureMap_smoothOfRelativeDimension, "theorem"),
    (`PaperVerification.AlternatingForms.onePlaneOriginal_nonempty_smooth, "theorem"),
    (`PaperVerification.HomogeneousQuotientCharts.polynomialChartIso, "definition"),
    (`PaperVerification.HomogeneousQuotientCharts.polynomialChartIso_hom_over, "theorem"),
    (`PaperVerification.AlternatingForms.sectionFour_isotropicStructureMap_smooth, "theorem"),
    (`PaperVerification.AlternatingForms.sectionFour_isotropicProj_nonempty, "theorem"),
    (`PaperVerification.AlternatingForms.sectionFourPositiveRankOver, "definition"),
    (`PaperVerification.AlternatingForms.sectionFourPositiveRankOver_zero, "theorem"),
    (`PaperVerification.AlternatingForms.sectionFourPositiveRankOver_succ, "theorem"),
    (`PaperVerification.AlternatingForms.sectionFour_positive_rank_geometry, "theorem"),
    (`PaperVerification.AlternatingForms.sectionFour_paper_rank, "theorem"),
    (`PaperVerification.AlternatingForms.paper_theorem_4_1_geometric_clauses, "theorem"),
    (`PaperVerification.AlternatingForms.canonicalOdd_isotropicStructureMap_smooth, "theorem"),
    (`PaperVerification.AlternatingForms.canonicalOdd_isotropicProj_nonempty, "theorem")
  ]
  let localNames := env.checked.get.constants.foldStage2 (fun acc name _ => acc.push name) (#[] : Array Name)
  if localNames.isEmpty then throwError "Empty authored declaration audit"
  let mut names := localNames
  for (name, _) in required do
    unless names.contains name do names := names.push name
  let mut rows : Array Json := #[]
  for name in names do
    let some info := env.checked.get.find? name | throwError "Missing checked declaration {name}"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient primitive"
    if kind == "axiom" then throwError "Authored axiom {name}"
    let value := info.value? (allowOpaque := true)
    if kind == "theorem" || kind == "definition" || kind == "opaque" then
      unless value.isSome do throwError "No actual body {name}"
    for (requiredName, expectedKind) in required do
      if name == requiredName && kind != expectedKind then
        throwError "Endpoint kind mismatch {name}: expected {expectedKind}, got {kind}"
    let axioms ← collectAxioms name
    for ax in axioms do
      if ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound then
        throwError "Unapproved transitive axiom {name}: {ax}"
    let mut fields := [("name", toJson name.toString), ("kind", toJson kind),
      ("actual_body_available", toJson value.isSome),
      ("universe_parameters", toJson (info.levelParams.map Name.toString)),
      ("type_dependencies", toJson (info.type.getUsedConstants.map Name.toString)),
      ("body_dependencies", toJson ((value.map Expr.getUsedConstants).getD #[] |>.map Name.toString)),
      ("transitive_axioms", toJson (axioms.map Name.toString))]
    if required.any (fun e => e.1 == name) then
      let typeText ← liftTermElabM <| return (← Meta.ppExpr info.type).pretty
      fields := fields ++ [("readable_type", toJson typeText)]
    rows := rows.push (Json.mkObj fields)
  IO.FS.createDirAll ".lake/reports"
  let path := ".lake/reports/" ++ (← getEnv).mainModule.toString ++ ".json"
  IO.FS.writeFile path (Json.mkObj [("accepted", toJson true),
    ("nonce", toJson "fda38d233490ece474737db2bb80b568"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:fda38d233490ece474737db2bb80b568"
