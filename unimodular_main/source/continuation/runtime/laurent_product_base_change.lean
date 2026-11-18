module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

/-!
# Laurent products and an arbitrary affine comparison

Monoid algebras commute with base change. Applying `Spec` to the genuine
pushout identifies the product with a split torus as the base change of the
Laurent extension along any compatible affine comparison map. In particular,
this applies to the affinization map of a scheme before affineness has been
proved.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open AlgebraicGeometry CategoryTheory Limits
open scoped AlgebraMonoidAlgebra

namespace PaperVerification.ToricSchemes

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
    (M : Type) [AddCommMonoid M]

/-- The affine Laurent extension is the actual base change of the original
monoid algebra. -/
theorem laurentSpectrum_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap (AddMonoidAlgebra k M)
        (AddMonoidAlgebra R M))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R M))))
      (Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k M))))
      (Spec.map (CommRingCat.ofHom (algebraMap k R))) :=
  ((CommRingCat.isPushout_of_isPushout k (AddMonoidAlgebra k M) R
    (AddMonoidAlgebra R M)).op.map Scheme.Spec).flip

variable {X : Scheme.{u}} (i : X ⟶ Spec (CommRingCat.of k))
    (η : X ⟶ Spec (CommRingCat.of R))
    (hη : η ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = i)

local notation "a" => Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k M)))
local notation "τ" => Spec.map (CommRingCat.ofHom (algebraMap
  (AddMonoidAlgebra k M) (AddMonoidAlgebra R M)))
local notation "σ" => Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R M)))

/-- The product's comparison to the spectrum of the extended coefficient
ring, constructed from the cartesian affine square. -/
def laurentProductComparison : pullback a i ⟶
    Spec (CommRingCat.of (AddMonoidAlgebra R M)) :=
  pullback.lift (pullback.fst a i) (pullback.snd a i ≫ η)
    (by rw [Category.assoc, hη]; exact pullback.condition) ≫
      (laurentSpectrum_isPullback k R M).isoPullback.inv

@[reassoc (attr := simp)]
theorem laurentProductComparison_first :
    laurentProductComparison k R M i η hη ≫ τ = pullback.fst a i := by
  simp only [laurentProductComparison, Category.assoc,
    IsPullback.isoPullback_inv_fst, pullback.lift_fst]

@[reassoc (attr := simp)]
theorem laurentProductComparison_second :
    laurentProductComparison k R M i η hη ≫ σ = pullback.snd a i ≫ η := by
  simp only [laurentProductComparison, Category.assoc,
    IsPullback.isoPullback_inv_snd, pullback.lift_snd]

/-- This comparison is cartesian over the original affine comparison, with
no affineness or projectivity hypothesis on `X`. -/
theorem laurentProductComparison_isPullback :
    IsPullback (laurentProductComparison k R M i η hη)
      (pullback.snd a i) σ η := by
  have houter : IsPullback
      (laurentProductComparison k R M i η hη ≫ τ)
      (pullback.snd a i) a
      (η ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) := by
    rw [laurentProductComparison_first, hη]
    exact IsPullback.of_hasPullback a i
  exact houter.of_right
    (laurentProductComparison_second k R M i η hη)
    (laurentSpectrum_isPullback k R M)

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.laurentProductComparison_isPullback
