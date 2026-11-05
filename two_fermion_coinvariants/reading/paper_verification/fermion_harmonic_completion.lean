module

public import PaperVerification.FermionHarmonicOccupation

/-!
# The missing-colour prefix cutoff

The actual prefix creators preserve the mixed equations. At the last index,
colex maximality identifies their selected coefficient with the required
single-mark factor, up to a unit sign. The diagonal Gauss bound then gives the
exact completed occupation cutoff; no ordinary prefix moment is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Exterior

open scoped BigOperators
open Polynomial
open Colex
open Endpoint

section OccupationInsert

variable {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]
  [DecidableEq (I ⊕ I)]

theorem gaussOccupationPolynomial_insert_inl (y : I → R) (N : ℕ)
    (T : Finset (I ⊕ I)) (i : I) (hθ : Sum.inl i ∉ T) (hξ : Sum.inr i ∈ T) :
    gaussOccupationPolynomial y N (insert (Sum.inl i) T) =
      gaussNilpotentInverse 1 X (C (y i)) N * gaussOccupationPolynomial y N T := by
  have hfactor (j : I) :
      diagonalOccupationFactor (fun j ↦ C (y j)) (fun _ ↦ X)
        (fun j ↦ gaussNilpotentInverse 1 X (C (y j)) N) (insert (Sum.inl i) T) j =
      (if j = i then gaussNilpotentInverse 1 X (C (y i)) N else 1) *
        diagonalOccupationFactor (fun j ↦ C (y j)) (fun _ ↦ X)
          (fun j ↦ gaussNilpotentInverse 1 X (C (y j)) N) T j := by
    by_cases hji : j = i
    · subst j
      simp [diagonalOccupationFactor, hθ, hξ]
    · simp only [diagonalOccupationFactor, Finset.mem_insert, Sum.inl.injEq,
        Sum.inr_ne_inl, hji, false_or, if_false, one_mul]
  simp only [gaussOccupationPolynomial, hfactor, Finset.prod_mul_distrib]
  simp

theorem gaussOccupationPolynomial_insert_inr (y : I → R) (N : ℕ)
    (T : Finset (I ⊕ I)) (i : I) (hθ : Sum.inl i ∈ T) (hξ : Sum.inr i ∉ T) :
    gaussOccupationPolynomial y N (insert (Sum.inr i) T) =
      gaussNilpotentInverse 1 X (C (y i)) N * gaussOccupationPolynomial y N T := by
  have hfactor (j : I) :
      diagonalOccupationFactor (fun j ↦ C (y j)) (fun _ ↦ X)
        (fun j ↦ gaussNilpotentInverse 1 X (C (y j)) N) (insert (Sum.inr i) T) j =
      (if j = i then gaussNilpotentInverse 1 X (C (y i)) N else 1) *
        diagonalOccupationFactor (fun j ↦ C (y j)) (fun _ ↦ X)
          (fun j ↦ gaussNilpotentInverse 1 X (C (y j)) N) T j := by
    by_cases hji : j = i
    · subst j
      simp [diagonalOccupationFactor, hθ, hξ]
    · simp only [diagonalOccupationFactor, Finset.mem_insert, Sum.inr.injEq,
        Sum.inl_ne_inr, hji, false_or, if_false, one_mul]
  simp only [gaussOccupationPolynomial, hfactor, Finset.prod_mul_distrib]
  simp

end OccupationInsert

section GeneralCompletion

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}
    [LinearOrder (Fin n ⊕ Fin n)]
    [DecidableEq (Fin n ⊕ Fin n)]
variable (b : Module.Basis (Fin n ⊕ Fin n) R V)

def completedWordPolynomial (φ : Fin n → R) (N : ℕ)
    (a : R) (T : Finset (Fin n ⊕ Fin n)) (F : R) (i : Fin n) : R[X] :=
  C a * inverseLinear (φ i) N * gaussOccupationPolynomial (fun j ↦ -φ j) N T * C F

/-- This is the diagonal Gauss cutoff applied to the actual completed
exterior vector. Both the negative-weight and nonnegative-weight cases are
included, so a zero path height is handled without a degree convention. -/
theorem completedWordPolynomial_bound
    (φ : Fin n → R) (N : ℕ) (hφ : ∀ j, φ j ^ N = 0)
    (hfac : IsUnit (n.factorial : R))
    (k : ℕ) (hk : k ≤ n) (w : ExteriorAlgebra R V) (v : V)
    (hwdegree : w ∈ ⋀[R]^k V)
    (hmixed : ∀ p : Polynomial R, mixedCurrent b φ p (creation v w) = 0)
    (T : Finset (Fin n ⊕ Fin n)) (i : Fin n) (p : Fin n ⊕ Fin n)
    (a : R) (u : ℤˣ)
    (hfactor : gaussOccupationPolynomial (fun j ↦ -φ j) N (insert p T) =
      inverseLinear (φ i) N * gaussOccupationPolynomial (fun j ↦ -φ j) N T)
    (hcoefficient : b.ExteriorAlgebra.repr (creation v w) (insert p T) =
      u • (a * b.ExteriorAlgebra.repr w T)) :
    CoefficientBound (completedWordPolynomial φ N a T (b.ExteriorAlgebra.repr w T) i) (n - k) := by
  have hscale : diagonalCoefficientPolynomial b (fun j ↦ -φ j) N (insert p T) (creation v w) =
      u • completedWordPolynomial φ N a T (b.ExteriorAlgebra.repr w T) i := by
    rw [diagonalCoefficientPolynomial, hfactor, hcoefficient, map_zsmul_unit,
      mul_smul_comm, completedWordPolynomial, map_mul]
    congr 1
    ring
  have hneg : ∀ q : Polynomial R,
      (∑ j, q.eval (-φ j) • pairLower b j) (creation v w) = 0 := by
    intro q
    simpa only [mixedCurrent, Polynomial.eval_comp, Polynomial.eval_neg,
      Polynomial.eval_X] using hmixed (q.comp (-X))
  have hnil : ∀ j, (-φ j) ^ N = 0 := by
    intro j
    rw [neg_pow, hφ j, mul_zero]
  have hdegree := creation_mem_succ v hwdegree
  by_cases htop : k = n
  · have hz : creation v w = 0 := by
      apply primitive_degree_bound b (by simpa only [Fintype.card_fin] using hfac)
        (k + 1) _ hdegree
      · simpa only [mixedCurrent, Polynomial.eval_one, one_smul, lowering] using hmixed 1
      · simp only [Fintype.card_fin]
        omega
    apply coefficientBound_of_unit_smul u _ _ hscale
    rw [hz]
    simp only [diagonalCoefficientPolynomial, map_zero, Finsupp.zero_apply,
      map_zero, mul_zero]
    exact coefficientBound_zero _
  · have hk' : k + 1 ≤ Fintype.card (Fin n) := by rw [Fintype.card_fin]; omega
    have hd := diagonalCoefficientPolynomial_natDegree_le b (fun j ↦ -φ j) N hnil
      (by simpa only [Fintype.card_fin] using hfac) (k + 1) (creation v w) hdegree hk'
      hneg (insert p T)
    apply coefficientBound_of_unit_smul u _ _ hscale
    intro j hj
    apply coeff_eq_zero_of_natDegree_lt
    apply lt_of_le_of_lt hd
    simp only [Fintype.card_fin]
    omega

end GeneralCompletion

section LastIndex

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}

local instance FermionHarmonicCompletion_localInst_1 (m : ℕ) : LinearOrder (Fin m ⊕ Fin m) := interleavedOddOrder m
local instance FermionHarmonicCompletion_localInst_2 (m : ℕ) : PartialOrder (Fin m ⊕ Fin m) := (interleavedOddOrder m).toPartialOrder
local instance FermionHarmonicCompletion_localInst_3 (m : ℕ) : Preorder (Fin m ⊕ Fin m) := (interleavedOddOrder m).toPreorder
local instance FermionHarmonicCompletion_localInst_4 (m : ℕ) : LE (Fin m ⊕ Fin m) := (interleavedOddOrder m).toLE
local instance FermionHarmonicCompletion_localInst_5 (m : ℕ) : LT (Fin m ⊕ Fin m) := (interleavedOddOrder m).toLT
local instance FermionHarmonicCompletion_localInst_6 (m : ℕ) : DecidableEq (Fin m ⊕ Fin m) := (interleavedOddOrder m).toDecidableEq

variable (b : Module.Basis (Fin (n + 1) ⊕ Fin (n + 1)) R V)

/-- Completing a theta-only last index gives the exact right-factor cutoff. -/
theorem thetaOnly_last_completion_bound
    (φ β a c : Fin (n + 1) → R) (N : ℕ) (hφ : ∀ j, φ j ^ N = 0)
    (hfac : IsUnit ((n + 1).factorial : R))
    (k : ℕ) (hk : k ≤ n + 1) (w : ExteriorAlgebra R V) (hwdegree : w ∈ ⋀[R]^k V)
    (hw : IsHarmonic b φ β a c w) (T : Finset (Fin (n + 1) ⊕ Fin (n + 1)))
    (hmax : ∀ U, b.ExteriorAlgebra.repr w U ≠ 0 → toColex U ≤ toColex T)
    (hθ : Sum.inl (Fin.last n) ∈ T) (hξ : Sum.inr (Fin.last n) ∉ T) :
    CoefficientBound (completedWordPolynomial φ N (c (Fin.last n)) T
      (b.ExteriorAlgebra.repr w T) (Fin.last n)) ((n + 1) - k) := by
  let v := xiCreatorVector b φ c 1
  have hv : ∀ j, Sum.inr (Fin.last n) < j → b.repr v j = 0 := by
    intro j hj
    cases j with
    | inl j => exact coord_xiCreatorVector_left b φ c 1 j
    | inr j =>
      change interleavedOddRank (.inr (Fin.last n)) < interleavedOddRank (.inr j) at hj
      simp only [interleavedOddRank, Fin.val_last] at hj
      have hjlt := j.isLt
      omega
  have hcoef := completion_coefficient b w T hmax (.inr (Fin.last n)) hξ v hv
  have hcoef' : b.ExteriorAlgebra.repr (creation v w) (insert (.inr (Fin.last n)) T) =
      TauCeti.ExteriorAlgebra.basisEraseSign (.inr (Fin.last n))
        (insert (.inr (Fin.last n)) T) • (c (Fin.last n) * b.ExteriorAlgebra.repr w T) := by
    rw [show b.repr v (.inr (Fin.last n)) = c (Fin.last n) by
      simpa only [v, Module.Basis.coord_apply, Polynomial.eval_one, mul_one] using
        coord_xiCreatorVector_right b φ c 1 (Fin.last n)] at hcoef
    simpa only [smul_comm (c (Fin.last n)), smul_eq_mul] using hcoef
  exact completedWordPolynomial_bound b φ N hφ hfac k hk w v hwdegree
    (xiCompletion_preserves_mixed b φ c w hw.2.2 hw.1) T (Fin.last n) (.inr (Fin.last n))
    (c (Fin.last n)) _
    (gaussOccupationPolynomial_insert_inr (fun j ↦ -φ j) N T (Fin.last n) hθ hξ) hcoef'

/-- The symmetric completion first produces `βᵢ aᵢ`; the singleton subset
sum is a unit, so it gives exactly the left factor required by the endpoint. -/
theorem xiOnly_last_completion_bound
    (φ β a c : Fin (n + 1) → R) (N : ℕ) (hφ : ∀ j, φ j ^ N = 0)
    (hfac : IsUnit ((n + 1).factorial : R)) (hβ : IsUnit (β (Fin.last n)))
    (k : ℕ) (hk : k ≤ n + 1) (w : ExteriorAlgebra R V) (hwdegree : w ∈ ⋀[R]^k V)
    (hw : IsHarmonic b φ β a c w) (T : Finset (Fin (n + 1) ⊕ Fin (n + 1)))
    (hmax : ∀ U, b.ExteriorAlgebra.repr w U ≠ 0 → toColex U ≤ toColex T)
    (hθ : Sum.inl (Fin.last n) ∉ T) (hξ : Sum.inr (Fin.last n) ∈ T) :
    CoefficientBound (completedWordPolynomial φ N (a (Fin.last n)) T
      (b.ExteriorAlgebra.repr w T) (Fin.last n)) ((n + 1) - k) := by
  let v := thetaCreatorVector b φ β a 1
  have hv : ∀ j, Sum.inl (Fin.last n) < j → b.repr v j = 0 := by
    intro j hj
    cases j with
    | inr j => exact coord_thetaCreatorVector_right b φ β a 1 j
    | inl j =>
      change interleavedOddRank (.inl (Fin.last n)) < interleavedOddRank (.inl j) at hj
      simp only [interleavedOddRank, Fin.val_last] at hj
      have hjlt := j.isLt
      omega
  have hcoef := completion_coefficient b w T hmax (.inl (Fin.last n)) hθ v hv
  have hcoef' : b.ExteriorAlgebra.repr (creation v w) (insert (.inl (Fin.last n)) T) =
      TauCeti.ExteriorAlgebra.basisEraseSign (.inl (Fin.last n))
        (insert (.inl (Fin.last n)) T) •
          (β (Fin.last n) * a (Fin.last n) * b.ExteriorAlgebra.repr w T) := by
    rw [show b.repr v (.inl (Fin.last n)) = β (Fin.last n) * a (Fin.last n) by
      simpa only [v, Module.Basis.coord_apply, Polynomial.eval_one, mul_one] using
        coord_thetaCreatorVector_left b φ β a 1 (Fin.last n)] at hcoef
    simpa only [smul_comm (β (Fin.last n) * a (Fin.last n)), smul_eq_mul] using hcoef
  have hb := completedWordPolynomial_bound b φ N hφ hfac k hk w v hwdegree
    (thetaCompletion_preserves_mixed b φ β a w hw.2.2 hw.2.1) T (Fin.last n) (.inl (Fin.last n))
    (β (Fin.last n) * a (Fin.last n)) _
    (gaussOccupationPolynomial_insert_inl (fun j ↦ -φ j) N T (Fin.last n) hθ hξ) hcoef'
  have hpoly : completedWordPolynomial φ N (β (Fin.last n) * a (Fin.last n)) T
      (b.ExteriorAlgebra.repr w T) (Fin.last n) =
      C (β (Fin.last n)) * completedWordPolynomial φ N (a (Fin.last n)) T
        (b.ExteriorAlgebra.repr w T) (Fin.last n) := by
    simp only [completedWordPolynomial, map_mul, mul_assoc]
  intro j hj
  have hh := hb j hj
  rw [hpoly, coeff_C_mul] at hh
  exact hβ.mul_right_eq_zero.mp hh

end LastIndex

section FullPrefix

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}

local instance FermionHarmonicCompletion_localInst_7 (m : ℕ) : LinearOrder (Fin m ⊕ Fin m) := interleavedOddOrder m
local instance FermionHarmonicCompletion_localInst_8 (m : ℕ) : PartialOrder (Fin m ⊕ Fin m) := (interleavedOddOrder m).toPartialOrder
local instance FermionHarmonicCompletion_localInst_9 (m : ℕ) : Preorder (Fin m ⊕ Fin m) := (interleavedOddOrder m).toPreorder
local instance FermionHarmonicCompletion_localInst_10 (m : ℕ) : LE (Fin m ⊕ Fin m) := (interleavedOddOrder m).toLE
local instance FermionHarmonicCompletion_localInst_11 (m : ℕ) : LT (Fin m ⊕ Fin m) := (interleavedOddOrder m).toLT
local instance FermionHarmonicCompletion_localInst_12 (m : ℕ) : DecidableEq (Fin m ⊕ Fin m) := (interleavedOddOrder m).toDecidableEq

variable (b : Module.Basis (Fin n ⊕ Fin n) R V)

theorem prefix_completedWordPolynomial (φ β a c : Fin n → R)
    (T : Finset (Fin n ⊕ Fin n)) (N : ℕ) (w : ExteriorAlgebra R V)
    (hmax : ∀ U, b.ExteriorAlgebra.repr w U ≠ 0 → toColex U ≤ toColex T)
    (i : ℕ) (hi : i < n) (d : R) :
    completedWordPolynomial (φ ∘ Fin.castLE (Nat.succ_le_iff.mpr hi)) N d
      (prefixWord (Nat.succ_le_iff.mpr hi) T)
      ((pairedPrefixBasis R (Nat.succ_le_iff.mpr hi)).ExteriorAlgebra.repr
        (extractedPrefix b (Nat.succ_le_iff.mpr hi) T w)
        (prefixWord (Nat.succ_le_iff.mpr hi) T)) (Fin.last i) =
      contractionSign (T \ pairedPrefix n (i + 1)).toList T •
        completedOccupation (harmonicData φ β a c T) N (b.ExteriorAlgebra.repr w T) d i := by
  rw [completedWordPolynomial, extractedPrefix_coefficient b _ T w hmax,
    map_zsmul_unit, mul_smul_comm, completedOccupation, scalarOccupation,
    prefix_occupation_eq_gauss (Nat.succ_le_iff.mpr hi)]
  have hnode : (harmonicData φ β a c T i).node = φ ((Fin.last i).castLE (Nat.succ_le_iff.mpr hi)) := by
    simp only [harmonicData, dataFromFin, dif_pos hi, harmonicDatum, Function.comp_apply]
    rfl
  rw [hnode]
  simp only [Function.comp_def]
  congr 1
  ring

/-- Every actual single-mark prefix has the completed occupation cutoff
required by the endpoint annihilation theorem. -/
theorem largest_coefficient_completion_occupation_bound
    (φ β a c : Fin n → R) (N : ℕ) (hφ : ∀ j, φ j ^ N = 0)
    (hfac : IsUnit (n.factorial : R)) (hβ : ∀ j, IsUnit (β j))
    (k : ℕ) (w : ExteriorAlgebra R V) (hwdegree : w ∈ ⋀[R]^k V)
    (hw : IsHarmonic b φ β a c w)
    (T : Finset (Fin n ⊕ Fin n)) (hT : b.ExteriorAlgebra.repr w T ≠ 0)
    (hmax : ∀ U, b.ExteriorAlgebra.repr w U ≠ 0 → toColex U ≤ toColex T)
    (i : ℕ) (hi : i < n) (d : R)
    (hd : ((harmonicData φ β a c T i).mark = .theta ∧
        d = (harmonicData φ β a c T i).rightFactor) ∨
      ((harmonicData φ β a c T i).mark = .xi ∧
        d = (harmonicData φ β a c T i).leftFactor)) :
    CoefficientBound
      (completedOccupation (harmonicData φ β a c T) N (b.ExteriorAlgebra.repr w T) d i)
      ((i + 1) - (T ∩ pairedPrefix n (i + 1)).card) := by
  let hi' : i + 1 ≤ n := Nat.succ_le_iff.mpr hi
  let x := extractedPrefix b hi' T w
  let S := prefixWord hi' T
  let b' := pairedPrefixBasis R hi'
  have hx := extractedPrefix_harmonic b hi' T φ β a c w hw hmax
  have hxmax := extractedPrefix_largest b hi' T w hmax
  have hxdegree := extractedPrefix_degree b hi' T k w hwdegree hT
  have hcard : S.card ≤ i + 1 := by
    rw [show S.card = (T ∩ pairedPrefix n (i + 1)).card from card_prefixWord hi' T]
    exact largest_harmonic_term_prefix_card_le b φ β a c hfac k w hwdegree hw T hT hmax (i + 1) hi'
  have hfac' : IsUnit ((i + 1).factorial : R) := unit_factorialCast_of_le hfac hi'
  have hφ' : ∀ j : Fin (i + 1), (φ ∘ Fin.castLE hi') j ^ N = 0 := fun j ↦ hφ _
  have hdata : harmonicData φ β a c T i =
      harmonicDatum (φ ∘ Fin.castLE hi') (β ∘ Fin.castLE hi')
        (a ∘ Fin.castLE hi') (c ∘ Fin.castLE hi') S (Fin.last i) := by
    exact harmonicData_prefix hi' φ β a c T (Fin.last i)
  rw [hdata] at hd
  simp only [harmonicDatum] at hd
  have hbound : CoefficientBound
      (completedWordPolynomial (φ ∘ Fin.castLE hi') N d S
        (b'.ExteriorAlgebra.repr x S) (Fin.last i)) ((i + 1) - S.card) := by
    rcases hd with ⟨hmark, rfl⟩ | ⟨hmark, rfl⟩
    · obtain ⟨hθ, hξ⟩ := (wordMark_eq_theta_iff S (Fin.last i)).mp hmark
      exact thetaOnly_last_completion_bound b' _ _ _ _ N hφ' hfac'
        S.card hcard x hxdegree hx S hxmax hθ hξ
    · obtain ⟨hθ, hξ⟩ := (wordMark_eq_xi_iff S (Fin.last i)).mp hmark
      exact xiOnly_last_completion_bound b' _ _ _ _ N hφ' hfac' (hβ _)
        S.card hcard x hxdegree hx S hxmax hθ hξ
  apply coefficientBound_of_unit_smul
    (contractionSign (T \ pairedPrefix n (i + 1)).toList T) _ _
    (prefix_completedWordPolynomial b φ β a c T N w hmax i hi d)
  simpa only [S, card_prefixWord] using hbound

end FullPrefix

end PaperVerification.Fermion.Exterior
