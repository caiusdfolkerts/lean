module

public import PaperVerification.ToricCharacterRegularity
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.LinearAlgebra.Basis.Basic

@[expose] public section

/-!
# Actual polynomial and Laurent coordinates on a smooth semigroup chart

The nonnegative coordinates of a subset of an integral basis form the
actual dual-cone semigroup. The remaining coordinates are unrestricted
integers. An explicit additive equivalence identifies this semigroup with
N^I × Z^(I-complement), and hence identifies its semigroup algebra with a
polynomial ring over the corresponding Laurent-character algebra.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open Set AddMonoidAlgebra
open scoped BigOperators Classical

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup E] [Module ℤ E]

abbrev FreeCoordinate (I : Finset ι) := {i : ι // i ∉ I}

def coordinateConeMonoid (b : Module.Basis ι ℤ E) (I : Finset ι) : AddSubmonoid E where
  carrier := {x | ∀ i ∈ I, 0 ≤ b.repr x i}
  zero_mem' := by intro i hi; simp
  add_mem' := by
    intro x y hx hy i hi
    simpa only [map_add, Finsupp.add_apply] using add_nonneg (hx i hi) (hy i hi)

def assembleConeCoordinates (b : Module.Basis ι ℤ E) (I : Finset ι)
    (x : (I → ℕ) × (FreeCoordinate I → ℤ)) : E :=
  b.equivFun.symm (fun i => if hi : i ∈ I then (x.1 ⟨i, hi⟩ : ℤ) else x.2 ⟨i, hi⟩)

theorem assembleConeCoordinates_repr (b : Module.Basis ι ℤ E) (I : Finset ι)
    (x : (I → ℕ) × (FreeCoordinate I → ℤ)) (i : ι) :
    b.repr (assembleConeCoordinates b I x) i =
      if hi : i ∈ I then (x.1 ⟨i, hi⟩ : ℤ) else x.2 ⟨i, hi⟩ := by
  change b.equivFun (b.equivFun.symm _) i = _
  rw [b.equivFun.apply_symm_apply]

theorem assembleConeCoordinates_mem (b : Module.Basis ι ℤ E) (I : Finset ι)
    (x : (I → ℕ) × (FreeCoordinate I → ℤ)) :
    assembleConeCoordinates b I x ∈ coordinateConeMonoid b I := by
  intro i hi
  rw [assembleConeCoordinates_repr, dif_pos hi]
  exact Int.natCast_nonneg _

/-- The semigroup equivalence is integral and explicit in both directions. -/
def coordinateConeEquiv (b : Module.Basis ι ℤ E) (I : Finset ι) :
    coordinateConeMonoid b I ≃+ (I → ℕ) × (FreeCoordinate I → ℤ) where
  toFun x := (fun i => (b.repr (x : E) i).toNat, fun i => b.repr (x : E) i)
  invFun x := ⟨assembleConeCoordinates b I x, assembleConeCoordinates_mem b I x⟩
  left_inv x := by
    apply Subtype.ext
    apply b.equivFun.injective
    funext i
    rw [Module.Basis.equivFun_apply, assembleConeCoordinates_repr,
      Module.Basis.equivFun_apply]
    split_ifs with hi
    · exact Int.toNat_of_nonneg (x.property i hi)
    · rfl
  right_inv x := by
    apply Prod.ext
    · funext i
      change (b.repr (assembleConeCoordinates b I x) i).toNat = x.1 i
      rw [assembleConeCoordinates_repr, dif_pos i.property]
      exact Int.toNat_natCast _
    · funext i
      change b.repr (assembleConeCoordinates b I x) i = x.2 i
      rw [assembleConeCoordinates_repr, dif_neg i.property]
  map_add' x y := by
    apply Prod.ext
    · funext i
      change (b.repr ((x : E) + (y : E)) i).toNat =
        (b.repr (x : E) i).toNat + (b.repr (y : E) i).toNat
      rw [map_add, Finsupp.add_apply,
        Int.toNat_add (x.property i i.property) (y.property i i.property)]
    · funext i
      exact congrArg (fun z : ι →₀ ℤ => z i) (b.repr.map_add (x : E) (y : E))

def naturalFunctionFinsuppEquiv (J : Type*) [Finite J] : (J → ℕ) ≃+ (J →₀ ℕ) :=
  (Finsupp.linearEquivFunOnFinite ℕ ℕ J).symm.toAddEquiv

def polynomialConeEquiv (b : Module.Basis ι ℤ E) (I : Finset ι) :
    coordinateConeMonoid b I ≃+ (I →₀ ℕ) × (FreeCoordinate I → ℤ) :=
  (coordinateConeEquiv b I).trans
    ((naturalFunctionFinsuppEquiv I).prodCongr (AddEquiv.refl (FreeCoordinate I → ℤ)))

variable (k : Type*) [CommSemiring k]

/-- The intrinsic semigroup chart algebra is a polynomial ring over a
Laurent-character algebra. This includes the zero cone and full cones. -/
def smoothSemigroupAlgebraEquiv (b : Module.Basis ι ℤ E) (I : Finset ι) :
    AddMonoidAlgebra k (coordinateConeMonoid b I) ≃ₐ[k]
      MvPolynomial I (AddMonoidAlgebra k (FreeCoordinate I → ℤ)) :=
  (AddMonoidAlgebra.domCongr k k (polynomialConeEquiv b I)).trans
    (AddMonoidAlgebra.curryAlgEquiv k)

/-- The same algebra equivalence for the actual subalgebra of k[E]
used by a chart. The inclusion into k[E] was proved injective separately. -/
def smoothChartAlgebraEquiv (b : Module.Basis ι ℤ E) (I : Finset ι) :
    monoidChartAlgebra k (coordinateConeMonoid b I) ≃ₐ[k]
      MvPolynomial I (AddMonoidAlgebra k (FreeCoordinate I → ℤ)) :=
  (monoidChartAlgebraEquiv k (coordinateConeMonoid b I)).symm.trans
    (smoothSemigroupAlgebraEquiv k b I)

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.smoothChartAlgebraEquiv
