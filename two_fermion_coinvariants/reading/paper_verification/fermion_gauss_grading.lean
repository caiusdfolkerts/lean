module

public import PaperVerification.FermionGauss
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

/-!
# Exterior-degree extraction in the diagonal Gauss identity

The projection used here is the genuine graded-algebra projection. In particular,
its vanishing on a different exterior degree is independent of characteristic;
comparing eigenvalues of the number operator would not suffice in finite
characteristic.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Exterior

open scoped BigOperators

variable {R V I : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [Fintype I] [DecidableEq I]

local notation "E" => ExteriorAlgebra R V

/-- Projection to the actual homogeneous exterior-degree summand. -/
def exteriorDegreeProjection (k : ℕ) : Module.End R E :=
  GradedAlgebra.proj (fun j : ℕ ↦ ⋀[R]^j V) k

 theorem exteriorDegreeProjection_self {k : ℕ} {w : E} (hw : w ∈ ⋀[R]^k V) :
    exteriorDegreeProjection k w = w :=
  DirectSum.decompose_of_mem_same (fun j : ℕ ↦ ⋀[R]^j V) hw

 theorem exteriorDegreeProjection_zero {j k : ℕ} {w : E}
    (hw : w ∈ ⋀[R]^j V) (hjk : j ≠ k) : exteriorDegreeProjection k w = 0 :=
  DirectSum.decompose_of_mem_ne (fun j : ℕ ↦ ⋀[R]^j V) hw hjk

variable (b : Module.Basis (I ⊕ I) R V)

 theorem pairRaise_mem_add_two (i : I) {k : ℕ} {w : E} (hw : w ∈ ⋀[R]^k V) :
    pairRaise b i w ∈ ⋀[R]^(k + 2) V := by
  exact creation_mem_succ (b (.inl i)) (creation_mem_succ (b (.inr i)) hw)

 theorem occupation_mem (i : I ⊕ I) {k : ℕ} {w : E} (hw : w ∈ ⋀[R]^k V) :
    occupation b i w ∈ ⋀[R]^k V := by
  cases k with
  | zero =>
    have hz : annihilation (b.coord i) w = 0 :=
      TauCeti.ExteriorAlgebra.contractLeft_eq_zero_of_mem_exteriorPower_zero (b.coord i) hw
    change creation (b i) (annihilation (b.coord i) w) ∈ _
    rw [hz, map_zero]
    exact zero_mem _
  | succ k =>
    exact creation_mem_succ (b i)
      (TauCeti.ExteriorAlgebra.contractLeft_mem_exteriorPower (b.coord i) hw)

 theorem pairRaise_pairLower_mem (i : I) {k : ℕ} {w : E} (hw : w ∈ ⋀[R]^k V) :
    (pairRaise b i * pairLower b i) w ∈ ⋀[R]^k V := by
  rw [← occupation_pair, Module.End.mul_apply]
  exact occupation_mem b (.inl i) (occupation_mem b (.inr i) hw)

 theorem pairLower_pairRaise_mem (i : I) {k : ℕ} {w : E} (hw : w ∈ ⋀[R]^k V) :
    (pairLower b i * pairRaise b i) w ∈ ⋀[R]^k V := by
  have hcomm : pairLower b i * pairRaise b i =
      pairRaise b i * pairLower b i + (1 - occupation b (.inl i) - occupation b (.inr i)) := by
    exact pair_operator_commutator _ _ _ _
      (by simpa using annihilation_creation (b.coord (.inl i)) (b (.inl i)))
      (by simpa using annihilation_creation (b.coord (.inr i)) (b (.inr i)))
      (by simpa using annihilation_creation (b.coord (.inl i)) (b (.inr i)))
      (by simpa using annihilation_creation (b.coord (.inr i)) (b (.inl i)))
  rw [hcomm, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.sub_apply,
    Module.End.one_apply]
  exact add_mem (pairRaise_pairLower_mem b i hw)
    (sub_mem (sub_mem hw (occupation_mem b (.inl i) hw)) (occupation_mem b (.inr i) hw))

 theorem pairGaussDiagonal_mem (i : I) (a c d : R) {k : ℕ} {w : E}
    (hw : w ∈ ⋀[R]^k V) :
    pairGaussDiagonal a c d (pairLower b i) (pairRaise b i) w ∈ ⋀[R]^k V := by
  simp only [pairGaussDiagonal, LinearMap.sub_apply, LinearMap.add_apply,
    Module.End.one_apply, LinearMap.smul_apply]
  exact sub_mem (add_mem hw (Submodule.smul_mem _ _ (pairLower_pairRaise_mem b i hw)))
    (Submodule.smul_mem _ _ (pairRaise_pairLower_mem b i hw))

 theorem diagonalProduct_mem (l : List I) (a c d : I → R) {k : ℕ} {w : E}
    (hw : w ∈ ⋀[R]^k V) :
    (l.map (fun i ↦ pairGaussDiagonal (a i) (c i) (d i)
      (pairLower b i) (pairRaise b i))).prod w ∈ ⋀[R]^k V := by
  induction l with
  | nil => simpa using hw
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    exact pairGaussDiagonal_mem b i (a i) (c i) (d i) ih

/-- Every elementary raising coefficient has its literal exterior degree. -/
theorem elementary_raising_mem (l : List I) (a : I → R) (j k : ℕ) (w : E)
    (hw : w ∈ ⋀[R]^k V) :
    elementaryOperator (l.map (fun i ↦ a i • pairRaise b i)) j w ∈ ⋀[R]^(k + 2 * j) V := by
  induction l generalizing j with
  | nil =>
    cases j with
    | zero => simpa [elementaryOperator] using hw
    | succ j => simp [elementaryOperator]
  | cons i l ih =>
    cases j with
    | zero => simpa [elementaryOperator] using hw
    | succ j =>
      simp only [List.map_cons, elementaryOperator, LinearMap.add_apply,
        Module.End.mul_apply, LinearMap.smul_apply]
      apply add_mem (ih (j + 1))
      apply Submodule.smul_mem
      have h := pairRaise_mem_add_two b i (ih j)
      convert h using 1 <;> congr 1 <;> omega

/-- Positive raising order disappears under projection back to the input degree. -/
theorem degreeProjection_raising_product (l : List I) (a : I → R)
    {k : ℕ} {w : E} (hw : w ∈ ⋀[R]^k V) :
    exteriorDegreeProjection k
      ((l.map fun i ↦ 1 + a i • pairRaise b i).prod w) = w := by
  have hexp := prod_one_add_eq_sum_elementary (l.map (fun i ↦ a i • pairRaise b i))
  simp only [List.map_map, Function.comp_def] at hexp
  rw [hexp, LinearMap.sum_apply, map_sum]
  rw [Finset.sum_eq_single 0]
  · simpa [elementaryOperator_zero] using exteriorDegreeProjection_self hw
  · intro j hj hne
    exact exteriorDegreeProjection_zero (elementary_raising_mem b l a j k w hw) (by omega)
  · simp

/-- Applying the genuine exterior-degree projection removes the first raising
factor. This is the equal-degree extraction step in the diagonal case of
Lemma 3.1, with every factor acting on the literal exterior algebra. -/
theorem diagonal_gauss_equal_degree
    (y : I → R) (u v : R) (N : ℕ) (hy : ∀ i, ((-u * v) * y i) ^ N = 0)
    (hfac : IsUnit ((Fintype.card I).factorial : R))
    (k : ℕ) (w : E) (hwdegree : w ∈ ⋀[R]^k V)
    (hw : ∀ p : Polynomial R, (∑ i, p.eval (y i) • pairLower b i) w = 0) :
    ((Finset.univ.toList.map fun i ↦
      pairGaussDiagonal (u * y i) v (gaussNilpotentInverse u v (y i) N)
        (pairLower b i) (pairRaise b i)).prod) w =
    exteriorDegreeProjection k
      (((Finset.univ.toList.map fun i ↦ 1 + (u * y i) • pairLower b i).prod)
        (((Finset.univ.toList.map fun i ↦ 1 + v • pairRaise b i).prod) w)) := by
  rw [diagonal_gauss_apply_primitive b y u v N hy hfac w hw]
  symm
  exact degreeProjection_raising_product b _ _
    (diagonalProduct_mem b _ _ _ _ hwdegree)

/-- The coefficient obtained by the exact exterior-degree projection. It is
independent of the scalar parameter in the diagonal Gauss product. -/
def diagonalGaussCoefficient (y : I → R) (k : ℕ) (w : E) (j : ℕ) : E :=
  exteriorDegreeProjection k
    (((Finset.univ.toList.map fun i ↦ 1 + y i • pairLower b i).prod)
      (elementaryOperator (Finset.univ.toList.map (pairRaise b)) j w))

/-- A finite scalar-polynomial expression for the full diagonal factor on a
primitive homogeneous vector. It holds over every allowed coefficient ring.
The same formula can be used after scalar extension to a polynomial ring to
obtain a literal polynomial identity; equality of functions on a finite ring
is not used to infer equality of polynomials. -/
theorem diagonal_gauss_bounded_expression
    (y : I → R) (v : R) (N : ℕ) (hy : ∀ i, ((-1 * v) * y i) ^ N = 0)
    (hfac : IsUnit ((Fintype.card I).factorial : R))
    (k : ℕ) (w : E) (hwdegree : w ∈ ⋀[R]^k V) (hk : k ≤ Fintype.card I)
    (hw : ∀ p : Polynomial R, (∑ i, p.eval (y i) • pairLower b i) w = 0) :
    ((Finset.univ.toList.map fun i ↦
      pairGaussDiagonal (y i) v (gaussNilpotentInverse 1 v (y i) N)
        (pairLower b i) (pairRaise b i)).prod) w =
      ∑ j ∈ Finset.range (Fintype.card I - k + 1),
        v ^ j • diagonalGaussCoefficient b y k w j := by
  have he : lowering b w = 0 := by
    have h := hw 1
    simpa only [Polynomial.eval_one, one_smul, lowering] using h
  have heq := diagonal_gauss_equal_degree b y 1 v N hy hfac k w hwdegree hw
  simp only [one_mul] at heq
  rw [heq]
  have hexp := prod_one_add_smul_eq_sum
    (Finset.univ.toList.map (pairRaise b)) v
  simp only [List.map_map, Function.comp_def, List.length_map,
    Finset.length_toList, Finset.card_univ] at hexp
  rw [hexp, LinearMap.sum_apply, map_sum, map_sum]
  simp only [LinearMap.smul_apply, map_smul]
  change (∑ j ∈ Finset.range (Fintype.card I + 1),
    v ^ j • diagonalGaussCoefficient b y k w j) = _
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro j hj hnot
  have hj' : Fintype.card I - k < j := by
    simp only [Finset.mem_range] at hnot
    omega
  simp only [diagonalGaussCoefficient,
    primitive_elementary_raising_eq_zero b hfac k w hwdegree he hk j hj',
    map_zero, smul_zero]

end PaperVerification.Fermion.Exterior
