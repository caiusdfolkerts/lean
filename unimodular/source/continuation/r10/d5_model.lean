module

public import Continuation.R10.Data
public import Continuation.Runtime.R10MatroidData
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! # Equivalence with the paper's D₅ representation of R₁₀

The paper uses the ten vectors e_i+e_j in the basis
`e₁-e₅, e₂-e₅, e₃-e₅, e₄-e₅, 2e₅` of D₅.  The displayed matrix has
determinant one and takes these coordinate columns to the standard `[I₅|B]`
columns, up to a permutation and unit signs.
-/

noncomputable section
open Matrix
open scoped BigOperators

namespace Unimodular.ExplicitR10

/-- The even-sum lattice used in the paper, with its actual submodule structure. -/
def evenLattice : Submodule ℤ (Fin 5 → ℤ) where
  carrier := {x | Even (∑ i, x i)}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change Even (∑ i, (x + y) i)
    simpa only [Pi.add_apply, Finset.sum_add_distrib] using hx.add hy
  smul_mem' := by
    intro a x hx
    change Even (∑ i, a * x i)
    rw [← Finset.mul_sum]
    exact hx.mul_left a

def evenCoordinates (x : Fin 5 → ℤ) : Fin 5 → ℤ :=
  ![x 0, x 1, x 2, x 3, 2 * x 4 - x 0 - x 1 - x 2 - x 3]

theorem evenCoordinates_sum (x : Fin 5 → ℤ) :
    (∑ i, evenCoordinates x i) = 2 * x 4 := by
  simp [evenCoordinates, Fin.sum_univ_succ] <;> ring

def toEvenLattice : (Fin 5 → ℤ) →ₗ[ℤ] evenLattice where
  toFun x := ⟨evenCoordinates x, by
    change Even (∑ i, evenCoordinates x i)
    rw [evenCoordinates_sum]
    exact ⟨x 4, by ring⟩⟩
  map_add' x y := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [evenCoordinates] <;> ring
  map_smul' a x := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [evenCoordinates] <;> ring

theorem toEvenLattice_injective : Function.Injective toEvenLattice := by
  intro x y h
  have he : evenCoordinates x = evenCoordinates y := congrArg Subtype.val h
  have h0 := congrFun he (0 : Fin 5)
  have h1 := congrFun he (1 : Fin 5)
  have h2 := congrFun he (2 : Fin 5)
  have h3 := congrFun he (3 : Fin 5)
  have h4 := congrFun he (4 : Fin 5)
  norm_num [evenCoordinates] at h0 h1 h2 h3 h4
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · change x 4 = y 4
    linarith

theorem toEvenLattice_surjective : Function.Surjective toEvenLattice := by
  intro x
  obtain ⟨m, hm⟩ := x.property
  have hm' : x.val 0 + x.val 1 + x.val 2 + x.val 3 + x.val 4 = 2 * m := by
    simpa [Fin.sum_univ_succ, add_assoc, two_mul] using hm
  refine ⟨![x.val 0, x.val 1, x.val 2, x.val 3, m], ?_⟩
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [toEvenLattice, evenCoordinates] <;> linarith

/-- The claimed coordinate basis is an actual integral lattice equivalence. -/
def evenLatticeEquiv : (Fin 5 → ℤ) ≃ₗ[ℤ] evenLattice :=
  LinearEquiv.ofBijective toEvenLattice
    ⟨toEvenLattice_injective, toEvenLattice_surjective⟩

def edgeEndpoints : Fin 10 → Fin 5 × Fin 5 :=
  ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

theorem evenCoordinates_columns (i : Fin 10) :
    evenCoordinates (r10Columns i) =
      Pi.single (edgeEndpoints i).1 1 + Pi.single (edgeEndpoints i).2 1 := by
  fin_cases i <;> decide

def canonicalMatrix : Matrix (Fin 5) (Fin 5) ℤ :=
  ![![-1,-1,0,0,1], ![0,0,0,1,0], ![-1,0,-1,0,1],
    ![-1,-1,-1,-1,2], ![-1,0,0,0,1]]

theorem canonicalMatrix_det : canonicalMatrix.det = 1 := by decide

def canonicalPermutation : Fin 10 → Fin 10 := ![0,2,1,3,4,6,7,5,8,9]

theorem canonicalPermutation_bijective : Function.Bijective canonicalPermutation := by decide

def canonicalSigns : Fin 10 → ℤˣ := ![-1,-1,1,1,1,1,1,1,1,1]

def canonicalEquiv : (Fin 5 → ℤ) ≃ₗ[ℤ] (Fin 5 → ℤ) :=
  Matrix.toLinearEquiv (Pi.basisFun ℤ (Fin 5)) canonicalMatrix
    (by rw [canonicalMatrix_det]; exact isUnit_one)

theorem canonicalEquiv_columns (i : Fin 10) :
    canonicalEquiv (r10Columns i) =
      canonicalSigns i • R10Maximality.rays (canonicalPermutation i) := by
  simp only [canonicalEquiv, Matrix.toLinearEquiv_apply,
    Matrix.toLin_eq_toLin', Matrix.toLin'_apply]
  fin_cases i <;> decide

/-- Explicit integral equivalence of the two R₁₀ configurations, including
every column and the complete label permutation. -/
theorem d5_standard_configuration_equivalence :
    ∃ φ : (Fin 5 → ℤ) ≃ₗ[ℤ] (Fin 5 → ℤ), ∃ σ : Fin 10 ≃ Fin 10,
      ∃ ε : Fin 10 → ℤˣ, ∀ i,
        φ (r10Columns i) = ε i • R10Maximality.rays (σ i) := by
  exact ⟨canonicalEquiv, Equiv.ofBijective canonicalPermutation canonicalPermutation_bijective,
    canonicalSigns, canonicalEquiv_columns⟩

/-- Real coordinates of the paper's ten D₅ columns. -/
def realPaperColumns (i : Fin 10) (j : Fin 5) : ℝ := (r10Columns i j : ℝ)

def realCanonicalSigns : Fin 10 → ℝˣ := ![-1,-1,1,1,1,1,1,1,1,1]

def canonicalLabelEquiv : Fin 10 ≃ Fin 10 :=
  Equiv.ofBijective canonicalPermutation canonicalPermutation_bijective

def realCanonicalEquiv : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ) :=
  Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin 5))
    (canonicalMatrix.map (Int.cast : ℤ → ℝ))
    (by
      rw [← Int.cast_det, canonicalMatrix_det, Int.cast_one]
      exact (isUnit_one : IsUnit (1 : ℝ)))

theorem realCanonicalEquiv_columns (i : Fin 10) :
    realCanonicalEquiv (realPaperColumns i) =
      realCanonicalSigns i • R10Maximality.realRays (canonicalLabelEquiv i) := by
  simp only [realCanonicalEquiv, Matrix.toLinearEquiv_apply,
    Matrix.toLin_eq_toLin', Matrix.toLin'_apply]
  change (fun j : Fin 5 =>
      ∑ k : Fin 5, (canonicalMatrix j k : ℝ) * realPaperColumns i k) =
    realCanonicalSigns i • R10Maximality.realRays (canonicalLabelEquiv i)
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [canonicalMatrix, realPaperColumns, r10Columns, Matrix.mulVec, Matrix.map_apply,
      dotProduct, Fin.sum_univ_succ, realCanonicalSigns, Units.smul_def,
      R10Maximality.realRays, R10Maximality.rays, canonicalLabelEquiv,
      canonicalPermutation]

/-- The actual ordinary real vector matroid of the D₅ coordinate columns is
isomorphic, by the displayed full label permutation, to the chosen R₁₀ matroid. -/
theorem paper_matroid_map_eq_r10 :
    (VectorMatroid.ofFamily (K := ℝ) realPaperColumns).mapEquiv canonicalLabelEquiv =
      R10Maximality.r10Matroid := by
  let w : Fin 10 → Fin 5 → ℝ := fun i ↦ R10Maximality.realRays (canonicalLabelEquiv i)
  have heq : VectorMatroid.ofFamily (K := ℝ) realPaperColumns =
      VectorMatroid.ofFamily (K := ℝ) w := by
    apply (VectorMatroid.ofFamily_eq_iff (K := ℝ) realPaperColumns w).2
    intro I
    have hli := realCanonicalEquiv.toLinearMap.linearIndepOn_iff_of_injOn
      (v := realPaperColumns) (s := I) realCanonicalEquiv.injective.injOn
    have hfamily : realCanonicalEquiv ∘ realPaperColumns =
        fun i ↦ realCanonicalSigns i • w i := funext realCanonicalEquiv_columns
    change LinearIndepOn ℝ (realCanonicalEquiv ∘ realPaperColumns) I ↔
      LinearIndepOn ℝ realPaperColumns I at hli
    rw [hfamily] at hli
    exact hli.symm.trans (LinearIndependent.units_smul_iff
      (fun i : I ↦ w i.val) (fun i : I ↦ realCanonicalSigns i.val))
  rw [heq]
  have hmap := VectorMatroid.ofFamily_mapEmbedding_eq_onSet (K := ℝ) w R10Maximality.realRays
    canonicalLabelEquiv.toEmbedding (fun _ ↦ rfl)
  have hrange : Set.range canonicalLabelEquiv.toEmbedding = Set.univ :=
    canonicalLabelEquiv.surjective.range_eq
  rw [hrange] at hmap
  exact hmap

#print axioms paper_matroid_map_eq_r10

#print axioms evenLatticeEquiv
#print axioms d5_standard_configuration_equivalence
end Unimodular.ExplicitR10
