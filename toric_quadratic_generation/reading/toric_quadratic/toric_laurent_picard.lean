module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.PicardGroup

@[expose] public section

/-!
# The actual split-torus coordinate ring has trivial Picard group

The group algebra of Z^n is identified, recursively and explicitly, with
an iterated Laurent polynomial ring. Polynomial unique factorization and
localization preserve unique factorization. Mathlib's class-group/Picard
equivalence then trivializes every actual invertible module over this ring.
The passage from invertible sheaves on its spectrum to modules is separate.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open scoped Polynomial nonZeroDivisors

def latticeSuccCoordinates (n : ℕ) :
    (Fin (n + 1) → ℤ) ≃+ ℤ × (Fin n → ℤ) where
  toFun x := (x 0, fun i => x i.succ)
  invFun x := Fin.cons x.1 x.2
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv x := by
    apply Prod.ext
    · rfl
    · funext i
      rfl
  map_add' _ _ := rfl

abbrev torusCoordinateRing (k : Type*) [CommRing k] (n : ℕ) :=
  AddMonoidAlgebra k (Fin n → ℤ)

variable (k : Type*) [Field k]

/-- Separating the first character coordinate gives an actual algebra
equivalence with a one-variable Laurent extension of the smaller torus. -/
def torusCoordinateRingSucc (n : ℕ) :
    torusCoordinateRing k (n + 1) ≃ₐ[k]
      AddMonoidAlgebra (torusCoordinateRing k n) ℤ :=
  (AddMonoidAlgebra.domCongr k k (latticeSuccCoordinates n)).trans
    (AddMonoidAlgebra.curryAlgEquiv k)

theorem torusCoordinateRing_isDomain (n : ℕ) : IsDomain (torusCoordinateRing k n) := by
  induction n with
  | zero =>
      exact MulEquiv.isDomain k
        (AddMonoidAlgebra.uniqueAlgEquiv k (Fin 0 → ℤ)).toMulEquiv
  | succ n ih =>
      letI := ih
      exact MulEquiv.isDomain (AddMonoidAlgebra (torusCoordinateRing k n) ℤ)
        (torusCoordinateRingSucc k n).toMulEquiv

/-- Laurent extension preserves unique factorization by its literal
localization presentation at powers of the polynomial variable. -/
theorem laurent_uniqueFactorization (A : Type*) [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] : UniqueFactorizationMonoid (AddMonoidAlgebra A ℤ) :=
  UniqueFactorizationMonoid.of_isLocalization
    (Submonoid.powers (Polynomial.X : Polynomial A)) (AddMonoidAlgebra A ℤ)

theorem torusCoordinateRing_uniqueFactorization (n : ℕ) :
    UniqueFactorizationMonoid (torusCoordinateRing k n) := by
  induction n with
  | zero =>
      exact ((AddMonoidAlgebra.uniqueAlgEquiv k (Fin 0 → ℤ)).symm.toMulEquiv).uniqueFactorizationMonoid
        inferInstance
  | succ n ih =>
      letI := ih
      letI := torusCoordinateRing_isDomain k n
      letI := laurent_uniqueFactorization (torusCoordinateRing k n)
      exact ((torusCoordinateRingSucc k n).symm.toMulEquiv).uniqueFactorizationMonoid inferInstance

/-- The Picard group here is Mathlib's actual group of invertible
modules under tensor product, not a fan-defined substitute. -/
theorem torusPic_subsingleton (n : ℕ) :
    Subsingleton (CommRing.Pic (torusCoordinateRing k n)) := by
  letI := torusCoordinateRing_isDomain k n
  letI := torusCoordinateRing_uniqueFactorization k n
  infer_instance

/-- Every invertible module over the actual split-torus coordinate
ring admits a global rank-one trivialization. -/
def torusInvertibleModuleEquiv (n : ℕ) (V : Type*)
    [AddCommGroup V] [Module (torusCoordinateRing k n) V]
    [Module.Invertible (torusCoordinateRing k n) V] :
    V ≃ₗ[torusCoordinateRing k n] torusCoordinateRing k n := by
  letI := torusPic_subsingleton k n
  exact Classical.choice (Module.Invertible.free_iff_linearEquiv.mp inferInstance)

theorem torusFractionalIdeal_principal (n : ℕ)
    (I : FractionalIdeal (torusCoordinateRing k n)⁰
      (FractionRing (torusCoordinateRing k n))) (hI : IsUnit I) :
    (I : Submodule (torusCoordinateRing k n) (FractionRing (torusCoordinateRing k n))).IsPrincipal := by
  letI := torusCoordinateRing_isDomain k n
  letI := torusCoordinateRing_uniqueFactorization k n
  exact ClassGroup.isPrincipal_coeSubmodule_of_isUnit I hI

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.torusCoordinateRing_uniqueFactorization
#print axioms PaperVerification.ToricCharacters.torusInvertibleModuleEquiv
