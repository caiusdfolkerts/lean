module

public import Recovery.Unimodular.GraphicSectionRing.Energy
public import Recovery.Unimodular.GraphicSectionRing.WeightedOrder
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder

/-!
# Actual toric fibers and the leading exponent of a kernel polynomial

The toric map is the additive-monoid-algebra homomorphism sending a variable
at a lattice point `p` to the Laurent monomial with exponent `(1,p)`.
Thus the kernel here is the usual homogeneous lattice-point toric ideal.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators MonomialOrder

namespace Unimodular.GraphicSectionRing

variable {n : ℕ} {σ : Type*}

def monomialPoints (p : σ → Lattice n) (u : σ →₀ ℕ) : Multiset (Lattice n) :=
  u.toMultiset.map p

@[simp] theorem monomialPoints_zero (p : σ → Lattice n) : monomialPoints p 0 = 0 := by
  simp [monomialPoints]

@[simp] theorem monomialPoints_add (p : σ → Lattice n) (u v : σ →₀ ℕ) :
    monomialPoints p (u + v) = monomialPoints p u + monomialPoints p v := by
  simp [monomialPoints, Finsupp.toMultiset_add, Multiset.map_add]

@[simp] theorem monomialPoints_single (p : σ → Lattice n) (a : σ) :
    monomialPoints p (Finsupp.single a 1) = {p a} := by
  simp [monomialPoints, Finsupp.toMultiset_single]

theorem monomialPoints_injective {p : σ → Lattice n} (hp : Function.Injective p) :
    Function.Injective (monomialPoints p) := by
  classical
  intro u v h
  have hm := Multiset.map_injective hp h
  have hf := congrArg Multiset.toFinsupp hm
  simpa only [Finsupp.toMultiset_toFinsupp] using hf

/-- The actual exponent of the image Laurent monomial, including its degree. -/
def toricDegree (p : σ → Lattice n) : (σ →₀ ℕ) →+ (ℕ × Lattice n) where
  toFun u := ((monomialPoints p u).card, (monomialPoints p u).sum)
  map_zero' := by simp
  map_add' u v := by
    ext <;> simp [monomialPoints_add, Multiset.card_add, Multiset.sum_add]

@[simp] theorem toricDegree_single (p : σ → Lattice n) (a : σ) :
    toricDegree p (Finsupp.single a 1) = (1, p a) := by
  simp [toricDegree]

def monomialWeight (p : σ → Lattice n) : (σ →₀ ℕ) →+ ℕ where
  toFun u := totalHeightNat (monomialPoints p u)
  map_zero' := by simp [totalHeightNat]
  map_add' u v := by
    simp [totalHeightNat, monomialPoints_add, Multiset.map_add, Multiset.sum_add]

@[simp] theorem monomialWeight_single (p : σ → Lattice n) (a : σ) :
    monomialWeight p (Finsupp.single a 1) = (height (p a)).toNat := by
  simp [monomialWeight, totalHeightNat]

def StandardExponent (p : σ → Lattice n) (u : σ →₀ ℕ) : Prop :=
  Standard (monomialPoints p u)

theorem standard_exponent_unique {p : σ → Lattice n} (hp : Function.Injective p)
    {u v : σ →₀ ℕ} (hu : StandardExponent p u) (hv : StandardExponent p v)
    (h : toricDegree p u = toricDegree p v) : u = v := by
  apply monomialPoints_injective hp
  apply standard_unique _ _ hu hv
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

/-- A standard exponent is strictly height-minimal among the other actual
exponents in its toric fiber. -/
theorem standard_exponent_weight_lt {p : σ → Lattice n} (hp : Function.Injective p)
    {u v : σ →₀ ℕ} (hu : StandardExponent p u)
    (h : toricDegree p u = toricDegree p v) (hne : u ≠ v) :
    monomialWeight p u < monomialWeight p v := by
  apply totalHeightNat_lt.mpr
  apply standard_height_lt_of_ne _ _ hu
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h
  · exact fun he => hne (monomialPoints_injective hp he)

/-- The genuine lattice-point monomial algebra map. -/
def toricMap (p : σ → Lattice n) (K : Type*) [CommSemiring K] :
    MvPolynomial σ K →ₐ[K] AddMonoidAlgebra K (ℕ × Lattice n) :=
  AddMonoidAlgebra.mapDomainAlgHom K K (toricDegree p)

@[simp] theorem toricMap_monomial (p : σ → Lattice n) (K : Type*) [CommSemiring K]
    (u : σ →₀ ℕ) (c : K) :
    toricMap p K (MvPolynomial.monomial u c) =
      AddMonoidAlgebra.single (toricDegree p u) c := by
  exact AddMonoidAlgebra.mapDomain_single

@[simp] theorem toricMap_X (p : σ → Lattice n) (K : Type*) [CommSemiring K] (a : σ) :
    toricMap p K (MvPolynomial.X a) = AddMonoidAlgebra.single (1, p a) 1 := by
  simpa only [MvPolynomial.X, toricDegree_single] using toricMap_monomial p K (Finsupp.single a 1) 1

/-- This is the usual toric ideal, with no normal-form property built into its definition. -/
def toricIdeal (p : σ → Lattice n) (K : Type*) [CommSemiring K] : Ideal (MvPolynomial σ K) :=
  RingHom.ker (toricMap p K).toRingHom

/-- Every nonzero kernel polynomial has a forbidden pair in its leading exponent. -/
theorem not_standard_leading_exponent {p : σ → Lattice n} (hp : Function.Injective p)
    (K : Type*) [CommSemiring K] (base : MonomialOrder σ)
    {f : MvPolynomial σ K} (hf : f ∈ toricIdeal p K) (hne : f ≠ 0) :
    ¬ StandardExponent p ((WeightedOrder.refine (monomialWeight p) base).degree f) := by
  classical
  let m := WeightedOrder.refine (monomialWeight p) base
  let d := m.degree f
  intro hstd
  have hcoeff : f.coeff d ≠ 0 := m.leadingCoeff_ne_zero_iff.mpr hne
  have hmax : ∀ b ∈ f.support, b ≼[m] d := fun b hb => m.le_degree hb
  have hsum : (toricMap p K f).coeff (toricDegree p d) = f.coeff d := by
    change (Finsupp.mapDomain (toricDegree p) f.coeff) (toricDegree p d) = f.coeff d
    rw [Finsupp.mapDomain_apply, Finsupp.sum]
    rw [Finset.sum_eq_single d]
    · simp
    · intro b hb hbd
      by_cases hdeg : toricDegree p b = toricDegree p d
      · have hweight := standard_exponent_weight_lt hp hstd hdeg.symm (Ne.symm hbd)
        have hlt : d ≺[m] b := WeightedOrder.lt_of_weight_lt _ _ hweight
        exact (not_lt_of_ge (hmax b hb) hlt).elim
      · simp [Finsupp.single_apply, hdeg]
    · intro hd
      exact (hd (MvPolynomial.mem_support_iff.mpr hcoeff)).elim
  have hz : toricMap p K f = 0 := hf
  rw [hz] at hsum
  exact hcoeff hsum.symm

#print axioms standard_exponent_weight_lt
#print axioms toricMap
#print axioms not_standard_leading_exponent

end Unimodular.GraphicSectionRing
