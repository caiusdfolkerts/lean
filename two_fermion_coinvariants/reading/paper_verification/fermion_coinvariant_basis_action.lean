module

public import PaperVerification.FermionCoinvariantMonomials
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Actual monomial actions and cyclic-compatible coefficients

The diagonal eigenvalue and pointwise-support
stabilizer formulas are derived from the actual local factorization. The
augmentation coefficient is proved from the original augmentation. Primitive
roots then force precisely the printed coordinatewise divisibilities over a
field, without assuming an invariant-basis theorem.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.Fermion.Coinvariants

variable {R : Type*} [CommRing R] {n : ℕ}

local instance coinvariantBasisActionOrder : LinearOrder (OddIndex n) :=
  LinearOrder.lift' Exterior.modeRank Exterior.modeRank_injective

def emptyIndex : SuperMonomialIndex n := (0,∅)

@[simp] theorem occupied_eq_empty (z : SuperMonomialIndex n) :
    occupied z=∅ ↔ z=emptyIndex := by
  rw [occupied,Finset.union_eq_empty,Finset.image_eq_empty,Finsupp.support_eq_empty]
  constructor
  · intro h
    exact Prod.ext h.1 h.2
  · intro h
    subst z
    exact ⟨rfl,rfl⟩

@[simp] theorem emptyIndex_basis : superMonomialBasis (K := R) (emptyIndex (n := n))=1 := by
  rw [superMonomialBasis_apply]
  simp [emptyIndex,Module.Basis.exteriorAlgebra_eq_prod_map_sort,
    Algebra.TensorProduct.one_def]

/-- A permutation fixing every occupied original index fixes the actual word,
including its exterior ordering and polynomial exponents. -/
theorem permutation_basis_of_fix (z : SuperMonomialIndex n)
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ i∈occupied z,σ i=i) :
    permutation (R := R) σ (superMonomialBasis z)=superMonomialBasis z := by
  suffices h : ∀ k : ℕ,∀ z : SuperMonomialIndex n,(occupied z).card=k →
      ∀ σ : Equiv.Perm (Fin n),(∀ i∈occupied z,σ i=i) →
        permutation (R := R) σ (superMonomialBasis z)=superMonomialBasis z from
    h _ z rfl σ hσ
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      intro z hk σ hσ
      by_cases hz : occupied z=∅
      · rw [(occupied_eq_empty z).mp hz,emptyIndex_basis,map_one]
      obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr hz
      obtain ⟨ε,hε⟩ := local_factorization (R := R) z i
      have hr : (occupied (eraseIndex z i)).card<k := by
        rw [occupied_eraseIndex,←hk]
        exact Finset.card_erase_lt_of_mem hi
      have hs : ∀ j∈occupied (eraseIndex z i),σ j=j := by
        rw [occupied_eraseIndex]
        intro j hj
        exact hσ j (Finset.mem_erase.mp hj).2
      have H := congrArg (permutation (R := R) σ) hε
      rw [map_mul,permutation_localBlock,hσ i hi,
        ih _ hr _ rfl σ hs,map_smul] at H
      apply ε.isUnit.smul_left_cancel.mp
      exact H.symm.trans hε

/-- The original augmentation kills every nonconstant original basis vector. -/
theorem augmentation_basis_nonempty (z : SuperMonomialIndex n)
    (hz : (occupied z).Nonempty) : augmentation (superMonomialBasis (K := R) z)=0 := by
  obtain ⟨i,hi⟩ := hz
  obtain ⟨ε,hε⟩ := local_factorization (R := R) z i
  have H := congrArg (augmentation (R := R) (n := n)) hε
  rw [map_mul,augmentation_localBlock _ _ _ (localKind_positive hi),
    zero_mul,map_smul] at H
  apply ε.isUnit.smul_left_cancel.mp
  exact H.symm.trans (smul_zero _).symm

/-- Positivity is exactly vanishing of the original constant basis coefficient. -/
theorem augmentation_eq_empty_coefficient (x : SuperRing R n) :
    augmentation x=(superMonomialBasis (K := R)).repr x emptyIndex := by
  have he : (augmentation (R := R) (n := n)).toLinearMap=
      (superMonomialBasis (K := R)).coord emptyIndex := by
    apply (superMonomialBasis (K := R)).ext
    intro z
    by_cases hz : z=emptyIndex
    · subst z
      rw [AlgHom.toLinearMap_apply,Module.Basis.coord_apply,
        Module.Basis.repr_self,Finsupp.single_eq_same,emptyIndex_basis,map_one]
    · have hn : (occupied z).Nonempty := Finset.nonempty_iff_ne_empty.mpr
        (fun h ↦ hz ((occupied_eq_empty z).mp h))
      rw [AlgHom.toLinearMap_apply,augmentation_basis_nonempty z hn,
        Module.Basis.coord_apply,Module.Basis.repr_self,Finsupp.single_apply,if_neg hz]
  exact LinearMap.congr_fun he x

def diagonalAt (c : Rˣ) (i : Fin n) : Fin n → Rˣ := fun j ↦ if j=i then c else 1

theorem diagonalAt_localBlock (p q : ℕ) (c : Rˣ) (i j : Fin n)
    (d : ℕ) (a : MomentKind) :
    diagonal p q (diagonalAt c i) (localBlock (R := R) d a j)=
      (c : R)^(if j=i then d+oddWeight p q a else 0) • localBlock d a j := by
  rw [diagonal_localBlock]
  by_cases h : j=i <;> simp [diagonalAt,h]

/-- The diagonal eigenvalue is the actual local character exponent. -/
theorem diagonalAt_basis (p q : ℕ) (c : Rˣ) (i : Fin n) (z : SuperMonomialIndex n) :
    diagonal p q (diagonalAt c i) (superMonomialBasis (K := R) z)=
      (c : R)^localDegree p q z i • superMonomialBasis z := by
  suffices h : ∀ k : ℕ,∀ z : SuperMonomialIndex n,(occupied z).card=k →
      diagonal p q (diagonalAt c i) (superMonomialBasis (K := R) z)=
        (c : R)^localDegree p q z i • superMonomialBasis z from h _ z rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      intro z hk
      by_cases hz : occupied z=∅
      · rw [(occupied_eq_empty z).mp hz,emptyIndex_basis,map_one]
        simp [localDegree,emptyIndex]
      obtain ⟨j,hj⟩ := Finset.nonempty_iff_ne_empty.mpr hz
      obtain ⟨ε,hε⟩ := local_factorization (R := R) z j
      have hr : (occupied (eraseIndex z j)).card<k := by
        rw [occupied_eraseIndex,←hk]
        exact Finset.card_erase_lt_of_mem hj
      have hd : localDegree p q z i=
          (if j=i then z.1 j+oddWeight p q (localKind z.2 j) else 0)+
            localDegree p q (eraseIndex z j) i := by
        have he := localDegree_join p q
          (localIndex (z.1 j) (localKind z.2 j) j) (eraseIndex z j)
          (localIndex_disjoint_erase z j) i
        simpa only [join_local_erase,localDegree_localIndex] using he
      have H := congrArg (diagonal p q (diagonalAt c i)) hε
      rw [map_mul,diagonalAt_localBlock,ih _ hr _ rfl,smul_mul_smul_comm,
        ←pow_add,←hd,hε,map_smul] at H
      apply ε.isUnit.smul_left_cancel.mp
      exact H.symm.trans (smul_comm _ _ _)

/-- The literal coordinate functional sees the same diagonal eigenvalue. -/
theorem diagonalAt_coefficient (p q : ℕ) (c : Rˣ) (i : Fin n)
    (z : SuperMonomialIndex n) (x : SuperRing R n) :
    (superMonomialBasis (K := R)).repr (diagonal p q (diagonalAt c i) x) z=
      (c : R)^localDegree p q z i*(superMonomialBasis (K := R)).repr x z := by
  let b := superMonomialBasis (K := R) (n := n)
  have he : (b.coord z).comp (diagonal p q (diagonalAt c i)).toLinearMap=
      (c : R)^localDegree p q z i • b.coord z := by
    apply b.ext
    intro t
    change b.repr (diagonal p q (diagonalAt c i) (b t)) z=
      (c : R)^localDegree p q z i*b.repr (b t) z
    rw [diagonalAt_basis,map_smul,Module.Basis.repr_self,Finsupp.smul_apply,
      Finsupp.single_apply]
    by_cases ht : t=z
    · subst t; simp
    · simp [ht]
  exact LinearMap.congr_fun he x

theorem wreath_invariant_permutation {r p q : ℕ} {x : SuperRing R n}
    (hx : ∀ g : WreathGroup R n r,wreathAction p q g x=x)
    (σ : Equiv.Perm (Fin n)) : permutation σ x=x := by
  have h := hx ⟨1,σ⟩
  change diagonal p q (fun i ↦ ((1 : Fin n → rootsOfUnity r R) i : Rˣ))
    (permutation σ x)=x at h
  simp only [Pi.one_apply,OneMemClass.coe_one] at h
  change diagonal p q (1 : Fin n → Rˣ) (permutation σ x)=x at h
  rwa [diagonal_one,AlgEquiv.one_apply] at h

theorem wreath_invariant_diagonalAt {r p q : ℕ} {x : SuperRing R n}
    (hx : ∀ g : WreathGroup R n r,wreathAction p q g x=x)
    (c : rootsOfUnity r R) (i : Fin n) : diagonal p q (diagonalAt (c : Rˣ) i) x=x := by
  have h := hx ⟨(fun j ↦ if j=i then c else 1),1⟩
  change diagonal p q (fun j ↦ ((if j=i then c else 1 : rootsOfUnity r R) : Rˣ))
    (permutation 1 x)=x at h
  rw [permutation_one,AlgEquiv.one_apply] at h
  have he : (fun j ↦ ((if j=i then c else 1 : rootsOfUnity r R) : Rˣ))=
      diagonalAt (c : Rˣ) i := by
    funext j
    by_cases hj : j=i <;> simp [diagonalAt,hj]
  rwa [he] at h

section Field

variable {F : Type*} [Field F] {r p q : ℕ}

/-- A nonzero coefficient of a true invariant has every required cyclic
weight divisible by r. The only field step cancels that nonzero coefficient. -/
theorem invariant_coefficient_compatible (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) r)
    (x : SuperRing F n) (hx : ∀ g : WreathGroup F n r,wreathAction p q g x=x)
    (z : SuperMonomialIndex n) (hz : (superMonomialBasis (K := F)).repr x z≠0)
    (i : Fin n) : r∣localDegree p q z i := by
  let c : rootsOfUnity r F := ⟨ζ,(mem_rootsOfUnity' r ζ).mpr hζ.pow_eq_one⟩
  have he := congrArg (fun y : SuperRing F n ↦ (superMonomialBasis (K := F)).repr y z)
    (wreath_invariant_diagonalAt hx c i)
  rw [diagonalAt_coefficient] at he
  have hpow : (ζ : F)^localDegree p q z i=1 := by
    apply mul_right_cancel₀ hz
    simpa only [one_mul] using he
  exact (hζ.pow_eq_one_iff_dvd _).mp hpow

end Field
end PaperVerification.Fermion.Coinvariants
