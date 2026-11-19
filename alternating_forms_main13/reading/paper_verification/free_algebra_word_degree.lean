module

public import PaperVerification.QuadraticWordFunctionals
public import Mathlib.LinearAlgebra.FreeAlgebra
import all Mathlib.LinearAlgebra.FreeAlgebra
public import Mathlib.Algebra.Algebra.Operations

/-!
# Original generator degree in the actual free algebra

The canonical word basis is multiplicative. Its length-n span equals the
nth power of the original generator space, including degree zero. These
identities connect homogeneous quadratic quotient functionals with the
usual generator grading rather than an auxiliary weight convention.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical Pointwise

namespace PaperVerification.QuadraticWordFunctionals

variable {K A J : Type*} [Field K] [Ring A] [Algebra K A]
  (B : Module.Basis (List J) K A)
  (hmul : ∀ L M,B (L++M)=B L*B M) (hunit : B []=1)

include hunit in
theorem degreeSpace_zero : degreeSpace B 0=1 := by
  have hs : B '' {L | L.length=0}=({1} : Set A) := by
    ext x
    constructor
    · rintro ⟨L,hL,rfl⟩
      have he : L=[] := List.length_eq_zero_iff.mp hL
      simpa only [he,hunit,Set.mem_singleton_iff]
    · intro hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact ⟨[],rfl,hunit⟩
  rw [degreeSpace,hs,←Submodule.one_eq_span]

include hmul in
theorem degreeSpace_succ (n : ℕ) :
    degreeSpace B (n+1)=degreeSpace B 1*degreeSpace B n := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨L,hL,rfl⟩
    change L.length=n+1 at hL
    cases L with
    | nil => simp only [List.length_nil] at hL; omega
    | cons i L =>
        have hlen : L.length=n := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hL
        rw [show i::L=[i]++L from rfl,hmul]
        apply Submodule.mul_mem_mul
        · exact basis_mem_degreeSpace B [i]
        · simpa only [hlen] using basis_mem_degreeSpace B L
  · apply Submodule.mul_le.mpr
    intro x hx y hy
    simpa only [Nat.add_comm 1 n] using degree_mul B hmul hx hy

include hmul hunit in
theorem degreeSpace_eq_power (n : ℕ) : degreeSpace B n=(degreeSpace B 1)^n := by
  induction n with
  | zero => rw [degreeSpace_zero B hunit,pow_zero]
  | succ n ih => rw [degreeSpace_succ B hmul,ih,pow_succ']

include hmul hunit in
theorem quotientPiece_eq_power (S : Submodule K A) (n : ℕ) :
    quotientPiece B S n=(quotientPiece B S 1)^n := by
  rw [quotientPiece,degreeSpace_eq_power B hmul hunit,Submodule.map_pow]
  rfl

end PaperVerification.QuadraticWordFunctionals

namespace PaperVerification.FreeAlgebraWordDegree

variable {K J : Type*} [Field K]

abbrev basis : Module.Basis (List J) K (FreeAlgebra K J) :=
  (FreeAlgebra.basisFreeMonoid K J).reindex FreeMonoid.toList

local notation "E" => (FreeAlgebra.equivMonoidAlgebraFreeMonoid :
  FreeAlgebra K J ≃ₐ[K] MonoidAlgebra K (FreeMonoid J))

@[simp] theorem basis_single (L : List J) :
    basis (K := K) L=(E).symm (MonoidAlgebra.single (FreeMonoid.ofList L) (1 : K)) := by
  rw [basis,Module.Basis.reindex_apply]
  change FreeAlgebra.basisFreeMonoid K J (FreeMonoid.ofList L)=_
  rw [FreeAlgebra.basisFreeMonoid,Module.Basis.map_apply,Finsupp.coe_basisSingleOne]
  rfl

@[simp] theorem map_basis (L : List J) :
    E (basis (K := K) L)=MonoidAlgebra.single (FreeMonoid.ofList L) (1 : K) := by
  rw [basis_single,AlgEquiv.apply_symm_apply]

theorem basis_append (L M : List J) :
    basis (K := K) (L++M)=basis (K := K) L*basis (K := K) M := by
  apply (E).injective
  rw [map_mul,map_basis,map_basis,map_basis,MonoidAlgebra.single_mul_single,one_mul,
    FreeMonoid.ofList_append]

@[simp] theorem basis_nil : basis (K := K) (J := J) []=1 := by
  apply (E).injective
  rw [map_basis,map_one,FreeMonoid.ofList_nil,MonoidAlgebra.one_def]

@[simp] theorem basis_singleton (i : J) : basis (K := K) [i]=FreeAlgebra.ι K i := by
  apply (E).injective
  rw [map_basis]
  change MonoidAlgebra.single (FreeMonoid.ofList [i]) (1 : K)=
    FreeAlgebra.lift K (fun j ↦ MonoidAlgebra.of K (FreeMonoid J) (FreeMonoid.of j))
      (FreeAlgebra.ι K i)
  rw [FreeAlgebra.lift_ι_apply]
  rfl

def generatorSpace : Submodule K (FreeAlgebra K J) :=
  Submodule.span K (Set.range (FreeAlgebra.ι K : J → FreeAlgebra K J))

theorem degreeSpace_one :
    QuadraticWordFunctionals.degreeSpace (basis (K := K) (J := J)) 1=generatorSpace := by
  apply congrArg (Submodule.span K)
  ext x
  constructor
  · rintro ⟨L,hL,rfl⟩
    obtain ⟨i,rfl⟩ := List.length_eq_one_iff.mp hL
    exact ⟨i,(basis_singleton i).symm⟩
  · rintro ⟨i,rfl⟩
    exact ⟨[i],rfl,basis_singleton i⟩

theorem degreeSpace_eq_generatorPower (n : ℕ) :
    QuadraticWordFunctionals.degreeSpace (basis (K := K) (J := J)) n=generatorSpace^n := by
  rw [QuadraticWordFunctionals.degreeSpace_eq_power basis basis_append basis_nil,degreeSpace_one]

end PaperVerification.FreeAlgebraWordDegree
