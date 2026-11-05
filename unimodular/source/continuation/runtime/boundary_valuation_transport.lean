module

public import Continuation.Runtime.IntrinsicReconstruction
public import Continuation.Fano.ActualBoundaryRayDictionary

/-! Actual boundary primes, character orders and unit-boundary inequalities
are transported by an actual torus-preserving scheme isomorphism. These are
the exact recovered candidate proof bodies; no periodic-arrangement theory
is imported or assumed. -/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

open PaperVerification.ToricCharacters
open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricGeometry
open scoped BigOperators

variable {k : Type u} [Field k] {n : ℕ}
    {X Y : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [ModObj (splitTorusOver k (Fin n → ℤ)) Y]
    [IsIntegral X.left] [IsIntegral Y.left]

variable (T : SplitToricEmbedding k n X)

variable [IsLocallyNoetherian X.left]

section Transport

variable [IsLocallyNoetherian Y.left]

variable (U : SplitToricEmbedding k n Y) (e : X ≅ Y)
    (htorus : T.torus ≫ e.hom = U.torus)

include htorus in
theorem intrinsicCharacter_pullback (m : Lattice n) :
    dominantFunctionFieldMap e.hom.left (U.intrinsicCharacter m) =
      T.intrinsicCharacter m := by
  let R := CommRingCat.of (torusCoordinateRing k n)
  letI : IsDomain R := torusCoordinateRing_isDomain k n
  change dominantFunctionFieldMap e.hom.left
      (affineOpenCoordinateMap R U.torus.left (AddMonoidAlgebra.single m 1)) =
    affineOpenCoordinateMap R T.torus.left (AddMonoidAlgebra.single m 1)
  apply dominantFunctionFieldMap_affineCoordinate R R U.torus.left T.torus.left
    e.hom.left (𝟙 R)
  rw [Spec.map_id, Category.id_comp]
  exact congrArg (fun f => f.left) htorus

include htorus in
theorem boundary_mem_map_iff (x : X.left) :
    e.hom.left x ∈ U.boundary ↔ x ∈ T.boundary := by
  change (¬∃ z, U.torus.left z = e.hom.left x) ↔
    (¬∃ z, T.torus.left z = x)
  apply not_congr
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, e.hom.left.isOpenEmbedding.injective ?_⟩
    calc
      e.hom.left (T.torus.left z) = U.torus.left z :=
        congrArg (fun f => f.left z) htorus
      _ = e.hom.left x := hz
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    calc
      U.torus.left z = e.hom.left (T.torus.left z) :=
        (congrArg (fun f => f.left z) htorus).symm
      _ = e.hom.left x := congrArg e.hom.left hz

include htorus in
theorem torus_preserving_inverse : U.torus ≫ e.inv = T.torus := by
  rw [← htorus, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- All actual boundary prime divisors are transported, including any that
were not selected in a particular affine cover. -/
def boundaryPrimeEquiv : T.BoundaryPrime ≃ U.BoundaryPrime where
  toFun p := ⟨e.hom.left p.val,
    (coheight_eq_of_isOpenImmersion e.hom.left).trans p.property.1,
    (T.boundary_mem_map_iff U e htorus p.val).mpr p.property.2⟩
  invFun q := ⟨e.inv.left q.val,
    (coheight_eq_of_isOpenImmersion e.inv.left).trans q.property.1,
    (U.boundary_mem_map_iff T e.symm
      (T.torus_preserving_inverse U e htorus) q.val).mpr q.property.2⟩
  left_inv p := by
    apply Subtype.ext
    exact congrArg (fun f : X ⟶ X => f.left p.val) e.hom_inv_id
  right_inv q := by
    apply Subtype.ext
    exact congrArg (fun f : Y ⟶ Y => f.left q.val) e.inv_hom_id

variable [IsLocallyNoetherian Y.left]

include htorus in
theorem valuationVector_map (x : X.left) :
    U.valuationVector (e.hom.left x) = T.valuationVector x := by
  ext i
  letI : IsIntegral ((Over.forget (Spec (CommRingCat.of k))).obj Y) := ‹IsIntegral Y.left›
  letI : IsLocallyNoetherian ((Over.forget (Spec (CommRingCat.of k))).obj Y) := ‹IsLocallyNoetherian Y.left›
  letI : IsIntegral ((Over.forget (Spec (CommRingCat.of k))).obj X) := ‹IsIntegral X.left›
  letI : IsLocallyNoetherian ((Over.forget (Spec (CommRingCat.of k))).obj X) := ‹IsLocallyNoetherian X.left›
  have h := schemeOrder_iso ((Over.forget _).mapIso e) x
    (U.intrinsicCharacter (Pi.single i 1))
  change Scheme.ord (dominantFunctionFieldMap e.hom.left (U.intrinsicCharacter (Pi.single i 1))) x =
    Scheme.ord (U.intrinsicCharacter (Pi.single i 1)) (e.hom.left x) at h
  rw [T.intrinsicCharacter_pullback U e htorus] at h
  exact h.symm

theorem boundaryValuation_equiv (p : T.BoundaryPrime) :
    U.boundaryValuation (T.boundaryPrimeEquiv U e htorus p) =
      T.boundaryValuation p :=
  T.valuationVector_map U e htorus p.val

theorem boundaryForm_equiv (p : T.BoundaryPrime) :
    U.boundaryForm (T.boundaryPrimeEquiv U e htorus p) = T.boundaryForm p := by
  simp only [boundaryForm, T.boundaryValuation_equiv U e htorus]

include htorus in
theorem unitBoundaryPolyhedron_eq : U.unitBoundaryPolyhedron = T.unitBoundaryPolyhedron := by
  ext x
  change (∀ q : U.BoundaryPrime, U.boundaryForm q x ≤ 1) ↔
    ∀ p : T.BoundaryPrime, T.boundaryForm p x ≤ 1
  constructor
  · intro h p
    simpa only [T.boundaryForm_equiv U e htorus] using
      h (T.boundaryPrimeEquiv U e htorus p)
  · intro h q
    obtain ⟨p, rfl⟩ := (T.boundaryPrimeEquiv U e htorus).surjective q
    simpa only [T.boundaryForm_equiv U e htorus] using h p

end Transport
end PaperVerification.ToricSchemes.SplitToricEmbedding
end
end

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.boundaryPrimeEquiv
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.boundaryValuation_equiv
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.unitBoundaryPolyhedron_eq
