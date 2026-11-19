module

public import PaperVerification.FermionExterior
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Full symplectic prefix division

This file proves surjectivity of exterior multiplication by the standard
paired two-form from degree `d-1` to degree `d+1` in `2d` variables.  It is
the existence assertion in Lemma 3.1, for every size and every homogeneous
element, using the literal exterior operators.  The explicit Boolean
inverse is developed separately in `AlternatingFormsBoolean` and
`AlternatingFormsExteriorStraightening`.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open PaperVerification.Fermion
open PaperVerification.Fermion.Exterior
open scoped BigOperators

section DegreeLowering

variable {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [Fintype ι] [DecidableEq ι]
variable (b : Module.Basis (ι ⊕ ι) R V)

local notation "E" => ExteriorAlgebra R V

theorem lowering_eq_zero_of_degree_lt_two {r : ℕ} {w : E}
    (hw : w ∈ ⋀[R]^r V) (hr : r < 2) : lowering b w = 0 := by
  rw [lowering, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R V)) (b.coord (.inr i))
    (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R V)) (b.coord (.inl i)) w) = 0
  rcases r with _ | r
  · have hz := TauCeti.ExteriorAlgebra.contractLeft_eq_zero_of_mem_exteriorPower_zero
      (b.coord (.inl i)) hw
    rw [hz, map_zero]
  · have hr0 : r = 0 := by omega
    subst r
    exact TauCeti.ExteriorAlgebra.contractLeft_eq_zero_of_mem_exteriorPower_zero
      (b.coord (.inr i))
      (TauCeti.ExteriorAlgebra.contractLeft_mem_exteriorPower (b.coord (.inl i)) hw)

theorem lowering_mem_sub_two {r : ℕ} {w : E} (hw : w ∈ ⋀[R]^r V) :
    lowering b w ∈ ⋀[R]^(r - 2) V := by
  by_cases hr : r < 2
  · rw [lowering_eq_zero_of_degree_lt_two b hw hr]
    exact zero_mem _
  · have hr' : r = (r - 2) + 1 + 1 := by omega
    rw [lowering, LinearMap.sum_apply]
    apply Submodule.sum_mem
    intro i hi
    change annihilation (b.coord (.inr i)) (annihilation (b.coord (.inl i)) w) ∈ _
    apply TauCeti.ExteriorAlgebra.contractLeft_mem_exteriorPower
    apply TauCeti.ExteriorAlgebra.contractLeft_mem_exteriorPower
    simpa only [← hr'] using hw

theorem lowering_pow_mem {r : ℕ} {w : E} (hw : w ∈ ⋀[R]^r V) (j : ℕ) :
    (lowering b ^ j) w ∈ ⋀[R]^(r - 2 * j) V := by
  induction j with
  | zero => simpa using hw
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    convert lowering_mem_sub_two b ih using 1 <;> congr 1 <;> omega

/-- Actual degree lowering proves nilpotence; it is not postulated as an
extra property of the exterior representation. -/
theorem lowering_pow_eq_zero_of_degree_lt {r : ℕ} {w : E}
    (hw : w ∈ ⋀[R]^r V) (j : ℕ) (hrj : r < 2 * j) : (lowering b ^ j) w = 0 := by
  induction j with
  | zero => omega
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    by_cases hr : r < 2 * j
    · rw [ih hr, map_zero]
    · exact lowering_eq_zero_of_degree_lt_two b (lowering_pow_mem b hw j) (by omega)

/-- The second orientation of the actual `sl₂` relations. -/
theorem swappedRaisingLowering :
    RaisingLowering (raising b) (lowering b) (-weight b) :=
  PaperVerification.Fermion.Exterior.loweringRaising b

/-- Exterior multiplication by the symplectic two-form is injective below
the middle degree.  The factorial hypothesis is sufficient over arbitrary
commutative coefficient rings and is automatic in characteristic zero
fields. -/
theorem raising_injective_below_middle
    (hfac : IsUnit ((Fintype.card ι).factorial : R))
    {r : ℕ} (hr : r < Fintype.card ι) {w : E}
    (hw : w ∈ ⋀[R]^r V) (hraise : raising b w = 0) : w = 0 := by
  let d := Fintype.card ι
  have hr2 : r ≤ 2 * d := by dsimp [d]; omega
  apply primitive_eq_zero_of_degree_gt (raising b) (lowering b) (-weight b)
    (swappedRaisingLowering b) d (2 * d - r) hfac (by dsimp [d]; omega)
    w hraise
  · rw [LinearMap.neg_apply, weight_homogeneous b r w hw, ← neg_smul]
    congr 1
    dsimp [d]
    rw [Nat.cast_sub hr2, Nat.cast_mul, Nat.cast_ofNat]
    ring
  · intro j hj
    apply lowering_pow_eq_zero_of_degree_lt b hw j
    omega

end DegreeLowering

section PrefixDivision

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]
variable (b : Module.Basis (ι ⊕ ι) K V)

local notation "E" => ExteriorAlgebra K V

/-- The standard paired two-form in the genuine second exterior power. -/
noncomputable def symplecticTwoForm : ⋀[K]^2 V :=
  ∑ i, exteriorPower.ιMulti K 2 ![b (.inl i), b (.inr i)]

theorem raising_eq_symplecticTwoForm_mul (w : E) :
    raising b w = (symplecticTwoForm b : E) * w := by
  simp only [raising, pairRaise, LinearMap.sum_apply, Module.End.mul_apply,
    creation_apply, symplecticTwoForm, Submodule.coe_sum,
    exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply]
  simp only [List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_succ, mul_one, Finset.sum_mul, mul_assoc]

/-- Exterior multiplication with its true homogeneous domain and codomain. -/
noncomputable def raisingDegreeMap (r : ℕ) : (⋀[K]^r V) →ₗ[K] ⋀[K]^(r + 2) V :=
  (raising b).restrict fun _ hw => raising_mem_add_two b hw

theorem raisingDegreeMap_injective
    (hfac : IsUnit ((Fintype.card ι).factorial : K))
    (r : ℕ) (hr : r < Fintype.card ι) :
    Function.Injective (raisingDegreeMap b r) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply Subtype.ext
  apply raising_injective_below_middle b hfac hr (x - y).property
  rw [Submodule.coe_sub, map_sub]
  exact sub_eq_zero.mpr (congrArg Subtype.val hxy)

include b in
/-- The middle complementary exterior powers have the same dimension. -/
theorem prefix_wedge_dimensions (hd : 0 < Fintype.card ι) :
    Module.finrank K (⋀[K]^(Fintype.card ι - 1) V) =
      Module.finrank K (⋀[K]^(Fintype.card ι - 1 + 2) V) := by
  letI : Module.Finite K V := Module.Finite.of_basis b
  rw [exteriorPower.finrank_eq, exteriorPower.finrank_eq,
    Module.finrank_eq_card_basis b, Fintype.card_sum]
  have hle : Fintype.card ι - 1 + 2 ≤ Fintype.card ι + Fintype.card ι := by omega
  have hsub : Fintype.card ι + Fintype.card ι - (Fintype.card ι - 1 + 2) =
      Fintype.card ι - 1 := by omega
  simpa only [hsub] using Nat.choose_symm hle

/-- The complete prefix map is an isomorphism, for every positive number
of pairs. -/
theorem prefix_wedge_bijective (hd : 0 < Fintype.card ι)
    (hfac : IsUnit ((Fintype.card ι).factorial : K)) :
    Function.Bijective (raisingDegreeMap b (Fintype.card ι - 1)) := by
  letI : Module.Finite K V := Module.Finite.of_basis b
  have hinj := raisingDegreeMap_injective b hfac (Fintype.card ι - 1) (by omega)
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (prefix_wedge_dimensions b hd)).mp hinj⟩

/-- Lemma 3.1's division existence for every homogeneous prefix element,
including every squarefree monomial, over every characteristic-zero field.
No bound is imposed on the number of variables. -/
theorem prefix_division_exists [CharZero K] (w : ⋀[K]^(Fintype.card ι + 1) V) :
    ∃ η : ⋀[K]^(Fintype.card ι - 1) V,
      (symplecticTwoForm b : E) * η = (w : E) := by
  by_cases hd : 0 < Fintype.card ι
  · have hfac : IsUnit ((Fintype.card ι).factorial : K) :=
      isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
    let w' : ⋀[K]^(Fintype.card ι - 1 + 2) V :=
      ⟨w, by convert w.property using 1 <;> congr 1 <;> omega⟩
    obtain ⟨η, hη⟩ := (prefix_wedge_bijective b hd hfac).surjective w'
    refine ⟨η, ?_⟩
    rw [← raising_eq_symplecticTwoForm_mul]
    exact congrArg Subtype.val hη
  · have hd0 : Fintype.card ι = 0 := by omega
    have hw0 : (w : E) = 0 := homogeneous_eq_zero_of_card_lt b
      (Fintype.card ι + 1) (by simp [Fintype.card_sum, hd0]) w w.property
    exact ⟨0, by simp [hw0]⟩

/-- Prefix division remains inside the prefix variables after inclusion
in any larger vector space.  The witness is the image of an element of the
smaller exterior power, not an arbitrary ambient quotient representative. -/
theorem prefix_division_map_exists [CharZero K]
    {M : Type*} [AddCommGroup M] [Module K M] (φ : V →ₗ[K] M)
    (w : ⋀[K]^(Fintype.card ι + 1) V) :
    ∃ η : ⋀[K]^(Fintype.card ι - 1) V,
      (ExteriorAlgebra.map φ (symplecticTwoForm b) : ExteriorAlgebra K M) *
          ExteriorAlgebra.map φ η = ExteriorAlgebra.map φ w := by
  obtain ⟨η, hη⟩ := prefix_division_exists b w
  exact ⟨η, by simpa only [map_mul] using congrArg (ExteriorAlgebra.map φ) hη⟩

end PrefixDivision

section PrefixMonomials

variable {K M ι : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M]
  [Fintype ι] [DecidableEq ι]

/-- Evaluation of the formal paired generators at arbitrary ambient
vectors.  In the application the vectors are the first `2h` path variables. -/
noncomputable def pairedEvaluation (u v : ι → M) : (ι ⊕ ι → K) →ₗ[K] M :=
  (Pi.basisFun K (ι ⊕ ι)).constr K (Sum.elim u v)

@[simp] theorem pairedEvaluation_basis (u v : ι → M) (i : ι ⊕ ι) :
    pairedEvaluation u v (Pi.basisFun K (ι ⊕ ι) i) = Sum.elim u v i := by
  simp [pairedEvaluation]

/-- Evaluation carries the literal paired quadratic to the literal ambient
matching quadratic.  The finite sum is evaluated term by term. -/
theorem pairedEvaluation_symplectic (u v : ι → M) :
    ExteriorAlgebra.map (pairedEvaluation (K := K) u v)
      (symplecticTwoForm (Pi.basisFun K (ι ⊕ ι)) :
        ExteriorAlgebra K (ι ⊕ ι → K))=
      ∑ i,ExteriorAlgebra.ι K (u i)*ExteriorAlgebra.ι K (v i) := by
  simp only [symplecticTwoForm,Submodule.coe_sum,map_sum,
    exteriorPower.ιMulti_apply_coe,ExteriorAlgebra.map_apply_ιMulti]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [ExteriorAlgebra.ιMulti_apply,List.ofFn_succ,List.ofFn_zero,
    List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.cons_val_one,pairedEvaluation_basis,Sum.elim_inl,Sum.elim_inr,mul_one]

set_option maxHeartbeats 1000000 in
/-- The full squarefree-monomial assertion of Lemma 3.1, expressed without
an arbitrary choice of ordering of the odd and even halves.  The tuple may
even repeat variables; the alternating product then vanishes.  The witness
is explicitly required to use only the prescribed prefix variables. -/
theorem prefix_monomial_division (u v : ι → M)
    (a : Fin (Fintype.card ι + 1) → ι ⊕ ι) :
    ∃ η : ⋀[K]^(Fintype.card ι - 1) M,
      η ∈ LinearMap.range (exteriorPower.map (Fintype.card ι - 1) (pairedEvaluation u v)) ∧
      (∑ i, ExteriorAlgebra.ι K (u i) * ExteriorAlgebra.ι K (v i)) * η =
        ExteriorAlgebra.ιMulti K (Fintype.card ι + 1) (Sum.elim u v ∘ a) := by
  let b := Pi.basisFun K (ι ⊕ ι)
  let w : ⋀[K]^(Fintype.card ι + 1) (ι ⊕ ι → K) :=
    exteriorPower.ιMulti K (Fintype.card ι + 1) (b ∘ a)
  let φ : (ι ⊕ ι → K) →ₗ[K] M := pairedEvaluation (K := K) u v
  obtain ⟨η, hη⟩ := prefix_division_map_exists b φ w
  let e : (⋀[K]^(Fintype.card ι - 1) (ι ⊕ ι → K)) →ₗ[K]
      (⋀[K]^(Fintype.card ι - 1) M) := exteriorPower.map (Fintype.card ι - 1) φ
  refine ⟨e η,LinearMap.mem_range_self e η,?_⟩
  change (∑ i, ExteriorAlgebra.ι K (u i) * ExteriorAlgebra.ι K (v i)) *
    (exteriorPower.map (Fintype.card ι - 1) φ η : ExteriorAlgebra K M)=_
  have hform := pairedEvaluation_symplectic (K := K) u v
  change (ExteriorAlgebra.map (pairedEvaluation (K := K) u v)
      (symplecticTwoForm b) : ExteriorAlgebra K M) *
        ExteriorAlgebra.map (pairedEvaluation (K := K) u v) η=
      ExteriorAlgebra.map (pairedEvaluation (K := K) u v) w at hη
  rw [hform] at hη
  simpa only [exteriorPower.coe_map, w, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.map_apply_ιMulti, Function.comp_def, b, φ,
    pairedEvaluation_basis] using hη

end PrefixMonomials

end PaperVerification.AlternatingForms
