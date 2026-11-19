module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Order.Rearrangement
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.OfFn
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Actual band minors and their distinct diagonal leading terms

The matrix entries are independent polynomial variables at the allowed band
positions and zero at all other positions. The expansion and leading-term
statements concern their actual determinants. This supplies the independence
half of the interval standard-monomial argument in Lemma 2.2; the separate
Plücker straightening theorem is still required to identify the full kernel.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Matrix
open scoped BigOperators

namespace PaperVerification.AlternatingForms

section PolynomialLeading

variable {K σ ι : Type*} [Field K] [Fintype ι]

/-- A polynomial has the displayed monomial with coefficient one, and every
other monomial of at least that weight has coefficient zero. -/
def IsWeightMonic (w : σ → ℤ) (p : MvPolynomial σ K) (a : σ →₀ ℕ) : Prop :=
  p.coeff a = 1 ∧ ∀ b, b ≠ a → Finsupp.weight w a ≤ Finsupp.weight w b → p.coeff b = 0

theorem isWeightMonic_of_finite_expansion
    (w : σ → ℤ) (p : MvPolynomial σ K) (a : ι → σ →₀ ℕ) (c : ι → K) (i₀ : ι)
    (hp : p = ∑ i, monomial (a i) (c i)) (hc : c i₀ = 1)
    (hlt : ∀ i, i ≠ i₀ → Finsupp.weight w (a i) < Finsupp.weight w (a i₀)) :
    IsWeightMonic w p (a i₀) := by
  classical
  constructor
  · rw [hp,coeff_sum,Finset.sum_eq_single i₀]
    · simp only [coeff_monomial,if_pos rfl,hc,ite_true]
    · intro i hi hne
      have ha : a i ≠ a i₀ := by
        intro he
        have h := hlt i hne
        rw [he] at h
        exact (lt_irrefl _ h)
      simp only [coeff_monomial,if_neg ha]
    · intro hi
      exact (hi (Finset.mem_univ _)).elim
  · intro b hba hweight
    rw [hp,coeff_sum]
    apply Finset.sum_eq_zero
    intro i hi
    have hab : a i ≠ b := by
      intro he
      by_cases hei : i=i₀
      · subst i
        exact hba he.symm
      · have h := hlt i hei
        rw [he] at h
        exact (not_lt_of_ge hweight h)
    simp only [coeff_monomial,if_neg hab]

/-- Distinct greatest-weight monomials prove independence without assuming
any Gröbner or standard-monomial theorem. -/
theorem linearIndependent_of_weightMonic
    (w : σ → ℤ) (p : ι → MvPolynomial σ K) (a : ι → σ →₀ ℕ)
    (ha : Function.Injective a) (hp : ∀ i, IsWeightMonic w (p i) (a i)) :
    LinearIndependent K p := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hsum i
  by_contra hci
  let S := (Finset.univ : Finset ι).filter fun j => c j ≠ 0
  have hS : S.Nonempty := ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hci⟩⟩
  obtain ⟨j,hj,hmax⟩ := S.exists_max_image (fun j => Finsupp.weight w (a j)) hS
  have hcj : c j ≠ 0 := (Finset.mem_filter.mp hj).2
  have hc := congrArg (fun q : MvPolynomial σ K => q.coeff (a j)) hsum
  rw [coeff_sum,Finset.sum_eq_single j] at hc
  · rw [coeff_smul,(hp j).1,smul_eq_mul,mul_one,MvPolynomial.coeff_zero,Finsupp.zero_apply] at hc
    exact hcj hc
  · intro k hk hkj
    by_cases hck : c k=0
    · simp only [hck,zero_smul,MvPolynomial.coeff_zero,Finsupp.zero_apply]
    · have hle := hmax k (Finset.mem_filter.mpr ⟨hk,hck⟩)
      rw [coeff_smul,(hp k).2 (a j) (fun he => hkj (ha he.symm)) hle,smul_zero]
  · intro hj'
    exact (hj' (Finset.mem_univ _)).elim

theorem prod_monomial_eq_monomial_sum
    {J : Type*} [Fintype J] (a : J → σ →₀ ℕ) (c : J → K) :
    (∏ j, monomial (a j) (c j) : MvPolynomial σ K) = monomial (∑ j, a j) (∏ j, c j) := by
  classical
  have h (S : Finset J) : (∏ j ∈ S, monomial (a j) (c j) : MvPolynomial σ K) =
      monomial (∑ j ∈ S, a j) (∏ j ∈ S, c j) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert j S hj ih =>
      rw [Finset.prod_insert hj,Finset.sum_insert hj,Finset.prod_insert hj,ih,monomial_mul]
  exact h Finset.univ

end PolynomialLeading

section BandMatrix

variable {K : Type*} [Field K] {s n : ℕ}

def bandEntryCoefficient (α β : Fin s → Fin n) (i : Fin s) (j : Fin n) : K :=
  if α i ≤ j ∧ j ≤ β i then 1 else 0

def bandMatrix (α β : Fin s → Fin n) :
    Matrix (Fin s) (Fin n) (MvPolynomial (Fin s × Fin n) K) :=
  fun i j => monomial (Finsupp.single (i,j) 1) (bandEntryCoefficient α β i j)

theorem bandMatrix_apply (α β : Fin s → Fin n) (i : Fin s) (j : Fin n) :
    bandMatrix (K := K) α β i j =
      if α i ≤ j ∧ j ≤ β i then X (i,j) else 0 := by
  unfold bandMatrix bandEntryCoefficient
  split_ifs <;> simp only [X,monomial_zero]

def bandMinor (α β I : Fin s → Fin n) : MvPolynomial (Fin s × Fin n) K :=
  ((bandMatrix (K := K) α β).submatrix id I).det

def minorTermExponent (I : Fin s → Fin n) (σ : Equiv.Perm (Fin s)) :
    (Fin s × Fin n) →₀ ℕ := ∑ i, Finsupp.single (σ i,I i) 1

def minorTermCoefficient (α β I : Fin s → Fin n) (σ : Equiv.Perm (Fin s)) : K :=
  Equiv.Perm.sign σ • ∏ i, bandEntryCoefficient α β (σ i) (I i)

theorem bandMinor_expansion (α β I : Fin s → Fin n) :
    bandMinor (K := K) α β I =
      ∑ σ : Equiv.Perm (Fin s), monomial (minorTermExponent I σ) (minorTermCoefficient α β I σ) := by
  rw [bandMinor,Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ hσ
  simp only [Matrix.submatrix_apply,id_eq,bandMatrix,prod_monomial_eq_monomial_sum,
    smul_monomial,minorTermExponent,minorTermCoefficient]

def bandEntryWeight (s n : ℕ) (a : Fin s × Fin n) : ℤ :=
  (a.1.val : ℤ) * (a.2.val : ℤ)

theorem minorTermExponent_weight (I : Fin s → Fin n) (σ : Equiv.Perm (Fin s)) :
    Finsupp.weight (bandEntryWeight s n) (minorTermExponent I σ) =
      ∑ i, ((σ i).val : ℤ) * ((I i).val : ℤ) := by
  simp only [minorTermExponent,map_sum,Finsupp.weight_single,one_smul,bandEntryWeight]

/-- The strict rearrangement inequality is precisely the uncrossing weight
calculation: the diagonal matching is uniquely greatest. -/
theorem minorTermExponent_weight_lt_diagonal
    (I : Fin s → Fin n) (hI : StrictMono I) (σ : Equiv.Perm (Fin s)) (hσ : σ ≠ 1) :
    Finsupp.weight (bandEntryWeight s n) (minorTermExponent I σ) <
      Finsupp.weight (bandEntryWeight s n) (minorTermExponent I 1) := by
  rw [minorTermExponent_weight,minorTermExponent_weight]
  simp only [Equiv.Perm.one_apply]
  have hmono : Monovary (fun i : Fin s => (i.val : ℤ)) (fun i => ((I i).val : ℤ)) := by
    intro i j hij
    change ((I i).val : ℤ) < ((I j).val : ℤ) at hij
    have hIj : I i < I j := Int.ofNat_lt.mp hij
    have hij' : i < j := hI.lt_iff_lt.mp hIj
    exact Int.ofNat_le.mpr hij'.le
  apply hmono.sum_comp_perm_mul_lt_sum_mul_iff.mpr
  intro hcross
  apply hσ
  apply (Equiv.Perm.monotone_iff σ).mp
  intro i j hij
  rcases hij.eq_or_lt with he | hij
  · exact le_of_eq (congrArg σ he)
  · have hi : ((I i).val : ℤ) < ((I j).val : ℤ) := by exact_mod_cast hI hij
    have h := hcross hi
    change ((σ i).val : ℤ) ≤ ((σ j).val : ℤ) at h
    exact Int.ofNat_le.mp h

theorem minorTermCoefficient_diagonal (α β I : Fin s → Fin n)
    (hI : ∀ i, α i ≤ I i ∧ I i ≤ β i) : minorTermCoefficient (K := K) α β I 1 = 1 := by
  simp only [minorTermCoefficient,Equiv.Perm.sign_one,one_smul,Equiv.Perm.one_apply,
    bandEntryCoefficient,hI,and_self,ite_true,Finset.prod_const_one]

theorem bandMinor_weightMonic (α β I : Fin s → Fin n) (hI : StrictMono I)
    (hband : ∀ i, α i ≤ I i ∧ I i ≤ β i) :
    IsWeightMonic (bandEntryWeight s n) (bandMinor (K := K) α β I) (minorTermExponent I 1) :=
  isWeightMonic_of_finite_expansion _ _ _ _ 1 (bandMinor_expansion α β I)
    (minorTermCoefficient_diagonal α β I hband) (minorTermExponent_weight_lt_diagonal I hI)

theorem bandMinor_ne_zero (α β I : Fin s → Fin n) (hI : StrictMono I)
    (hband : ∀ i, α i ≤ I i ∧ I i ≤ β i) : bandMinor (K := K) α β I ≠ 0 := by
  intro hz
  have h := (bandMinor_weightMonic (K := K) α β I hI hband).1
  rw [hz,MvPolynomial.coeff_zero,Finsupp.zero_apply] at h
  exact zero_ne_one h

end BandMatrix

section StandardProducts

variable {K : Type*} [Field K] {s n r : ℕ}

/-- Actual length-`r` multichains of increasing subsets in the band interval. -/
def BandChain (α β : Fin s → Fin n) (r : ℕ) :=
  {I : Fin r → Fin s → Fin n //
    (∀ t, StrictMono (I t)) ∧ (∀ t i, α i ≤ I t i ∧ I t i ≤ β i) ∧ Monotone I}

instance bandChain_fintype (α β : Fin s → Fin n) (r : ℕ) : Fintype (BandChain α β r) := by
  classical
  unfold BandChain
  infer_instance

def bandStandardProduct (α β : Fin s → Fin n) (C : BandChain α β r) :
    MvPolynomial (Fin s × Fin n) K := ∏ t, bandMinor α β (C.val t)

def chainTermExponent (I : Fin r → Fin s → Fin n)
    (σ : Fin r → Equiv.Perm (Fin s)) : (Fin s × Fin n) →₀ ℕ :=
  ∑ t, minorTermExponent (I t) (σ t)

def chainTermCoefficient (α β : Fin s → Fin n) (I : Fin r → Fin s → Fin n)
    (σ : Fin r → Equiv.Perm (Fin s)) : K :=
  ∏ t, minorTermCoefficient α β (I t) (σ t)

def chainDiagonalExponent (I : Fin r → Fin s → Fin n) : (Fin s × Fin n) →₀ ℕ :=
  chainTermExponent I (fun _ => 1)

theorem bandStandardProduct_expansion (α β : Fin s → Fin n) (C : BandChain α β r) :
    bandStandardProduct (K := K) α β C =
      ∑ σ : Fin r → Equiv.Perm (Fin s),
        monomial (chainTermExponent C.val σ) (chainTermCoefficient α β C.val σ) := by
  classical
  simp only [bandStandardProduct,bandMinor_expansion]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  exact prod_monomial_eq_monomial_sum _ _

theorem chainTermExponent_weight_lt_diagonal
    (I : Fin r → Fin s → Fin n) (hI : ∀ t, StrictMono (I t))
    (σ : Fin r → Equiv.Perm (Fin s)) (hσ : σ ≠ fun _ => 1) :
    Finsupp.weight (bandEntryWeight s n) (chainTermExponent I σ) <
      Finsupp.weight (bandEntryWeight s n) (chainDiagonalExponent I) := by
  classical
  obtain ⟨t,ht⟩ : ∃ t, σ t ≠ 1 := by
    by_contra h
    apply hσ
    funext t
    exact not_ne_iff.mp (not_exists.mp h t)
  simp only [chainDiagonalExponent,chainTermExponent,map_sum]
  apply Finset.sum_lt_sum
  · intro a ha
    by_cases hσa : σ a=1
    · rw [hσa]
    · exact (minorTermExponent_weight_lt_diagonal (I a) (hI a) (σ a) hσa).le
  · exact ⟨t,Finset.mem_univ _,minorTermExponent_weight_lt_diagonal (I t) (hI t) (σ t) ht⟩

theorem bandStandardProduct_weightMonic (α β : Fin s → Fin n) (C : BandChain α β r) :
    IsWeightMonic (bandEntryWeight s n) (bandStandardProduct (K := K) α β C)
      (chainDiagonalExponent C.val) := by
  apply isWeightMonic_of_finite_expansion _ _ _ _ (fun _ => 1)
    (bandStandardProduct_expansion α β C)
  · simp only [chainTermCoefficient,minorTermCoefficient_diagonal α β _ (C.property.2.1 _),
      Finset.prod_const_one]
  · exact chainTermExponent_weight_lt_diagonal C.val C.property.1

theorem sum_boole_eq_count_ofFn {A : Type*} [DecidableEq A] (f : Fin r → A) (a : A) :
    (∑ t, if f t=a then 1 else 0 : ℕ) = (List.ofFn f).count a := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Fin.sum_univ_succ,List.ofFn_succ,List.count_cons]
    rw [ih]
    simp only [beq_iff_eq,Nat.add_comm]

/-- A row of the diagonal exponent records exactly the multiplicities of its
sorted column list. This retains repetitions in a multichain. -/
theorem chainDiagonalExponent_apply (I : Fin r → Fin s → Fin n) (i : Fin s) (j : Fin n) :
    chainDiagonalExponent I (i,j) = (List.ofFn fun t => I t i).count j := by
  classical
  rw [← sum_boole_eq_count_ofFn]
  simp only [chainDiagonalExponent,chainTermExponent,minorTermExponent,
    Finset.sum_apply',Equiv.Perm.one_apply]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.sum_eq_single i]
  · simp only [Finsupp.single_apply,Prod.mk.injEq,true_and]
  · intro a ha hai
    simp only [Finsupp.single_apply,Prod.mk.injEq,hai,false_and,ite_false]
  · intro hi
    exact (hi (Finset.mem_univ _)).elim

/-- The diagonal monomial determines a multichain uniquely, by recovering
the sorted list in each row. This is the exact independence argument in
Lemma 2.2, including arbitrary length and every repeated interval element. -/
theorem chainDiagonalExponent_injective (α β : Fin s → Fin n) :
    Function.Injective (fun C : BandChain α β r => chainDiagonalExponent C.val) := by
  classical
  intro C D h
  apply Subtype.ext
  funext t i
  have hperm : (List.ofFn fun t => C.val t i).Perm (List.ofFn fun t => D.val t i) := by
    apply List.perm_iff_count.mpr
    intro j
    simpa only [chainDiagonalExponent_apply] using congrArg (fun a => a (i,j)) h
  have hC : (List.ofFn fun t => C.val t i).Pairwise (· ≤ ·) :=
    ((show Monotone (fun t => C.val t i) from fun a b hab => C.property.2.2 hab i).sortedLE_ofFn).pairwise
  have hD : (List.ofFn fun t => D.val t i).Pairwise (· ≤ ·) :=
    ((show Monotone (fun t => D.val t i) from fun a b hab => D.property.2.2 hab i).sortedLE_ofFn).pairwise
  have he := List.Perm.eq_of_pairwise' hC hD hperm
  exact congrFun (List.ofFn_injective he) t

/-- All actual products of band minors indexed by interval multichains are
linearly independent over every field, in every degree. -/
theorem bandStandardProducts_linearIndependent (α β : Fin s → Fin n) (r : ℕ) :
    LinearIndependent K (bandStandardProduct (K := K) (r := r) α β) :=
  linearIndependent_of_weightMonic (bandEntryWeight s n) _ _
    (chainDiagonalExponent_injective α β) (bandStandardProduct_weightMonic α β)

end StandardProducts

end PaperVerification.AlternatingForms
