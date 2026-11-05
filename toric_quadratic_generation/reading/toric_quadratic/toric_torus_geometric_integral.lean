module

public import PaperVerification.ToricTorusAction
public import PaperVerification.ToricLaurentPicard
public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

@[expose] public section

/-!
# Geometric integrality of the actual split torus

The proof uses arbitrary field-valued base changes of schemes.  It makes
no appeal to the density of rational points.  The affine coordinate-ring
calculation is the literal scalar extension of the group algebra.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Limits
open PaperVerification.ToricCharacters
open scoped TensorProduct

variable (k : Type u) [Field k] (n : ℕ)

instance splitTorus_integral : IsIntegral (splitTorus k (Fin n→ℤ)) := by
  letI := torusCoordinateRing_isDomain k n
  change IsIntegral (Spec (CommRingCat.of (torusCoordinateRing k n)))
  infer_instance

/-- The coordinate algebra of the actual base change of the torus. -/
def torusBaseChangeAlgEquiv (K : Type u) [Field K] [Algebra k K] :
    torusCoordinateRing k n ⊗[k] K ≃ₐ[k] torusCoordinateRing K n :=
  (Algebra.TensorProduct.comm k (torusCoordinateRing k n) K).trans
    ((AddMonoidAlgebra.scalarTensorEquiv k K (M := Fin n → ℤ)).restrictScalars k)

/-- Every field extension gives the actual torus over that field. -/
def torusBaseChangeIso (K : Type u) [Field K] [Algebra k K] :
    pullback (splitTorusOver k (Fin n → ℤ)).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≅
        splitTorus K (Fin n → ℤ) :=
  pullbackSpecIso k (torusCoordinateRing k n) K ≪≫
    Scheme.Spec.mapIso (torusBaseChangeAlgEquiv k n K).toRingEquiv.toCommRingCatIso.symm.op

/-- Geometric integrality is derived from the actual affine base change,
including extensions that are not algebraically closed. -/
instance splitTorus_geometricallyIntegral :
    GeometricallyIntegral (splitTorusOver k (Fin n → ℤ)).hom := by
  constructor
  rw [geometrically_iff_of_commRing]
  intro K _ _ Y fst snd h
  letI := torusCoordinateRing_isDomain K n
  have hT : IsIntegral (splitTorus K (Fin n → ℤ)) := by
    change IsIntegral (Spec (CommRingCat.of (torusCoordinateRing K n)))
    infer_instance
  let e := h.isoPullback ≪≫ torusBaseChangeIso k n K
  exact IsIntegral.of_isIso e.inv

/-- The torus projection is open and has geometrically irreducible
fibres. Consequently every irreducible subset has irreducible preimage. -/
theorem torusProjection_isIrreducible_preimage
    (X : Over (Spec (CommRingCat.of k))) {Z : Set X.left}
    (hZ : IsIrreducible Z) :
    IsIrreducible ((pullback.snd (splitTorusOver k (Fin n → ℤ)).hom X.hom) ⁻¹' Z) := by
  exact (pullback.snd (splitTorusOver k (Fin n → ℤ)).hom X.hom).isIrreducible_preimage
    (Scheme.Hom.isOpenMap _) hZ

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.splitTorus_geometricallyIntegral
