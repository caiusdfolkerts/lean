module

public import Continuation.Runtime.InvariantAffineAlgebra
public import Continuation.Runtime.InvariantAffineNeighbourhoods
public import Continuation.Runtime.CoordinateChartCover

/-!
# A finite actual coordinate-chart cover of the original toric scheme

An invariant affine open is identified with its literal character subalgebra
inside the original Laurent ring.  The spectrum map below is induced by that
identification.  Its composite with the original character-torus inclusion is
proved equal to the specified torus map, using restriction of regular sections.

Compactness then extracts finitely many of the invariant affine neighbourhoods.
The result is a `CoordinateChartCover`, without an assumed fan, projective
embedding, overlap description, or completeness condition on cones.

This source candidate still awaits native checking of its full dependency chain.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory
open PaperVerification.ToricCharacters PaperVerification.ToricGeometry
open scoped Classical PaperVerification.ToricSchemes.BaseSections

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [IsIntegral X.left] [IsNoetherian X.left] [Smooth X.hom]
    [X.left.IsSeparated]
    (T : SplitToricEmbedding k n X)

section AffineOpen

variable (U : X.left.Opens) [Nonempty U]

/-- The recovered Laurent restriction is exactly the actual restriction of
sections along the specified torus map, followed by the affine global-section
isomorphism. -/
theorem invariantAffineLaurentHom_eq_appLE (hT : T.torusOpen ≤ U)
    (hpre : (⊤ : (splitTorus k (Fin n → ℤ)).Opens) ≤ T.torus.left ⁻¹ᵁ U) :
    CommRingCat.ofHom (T.invariantAffineLaurentHom U hT).toRingHom =
      T.torus.left.appLE U ⊤ hpre ≫
        (Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).hom := by
  let R := CommRingCat.of (torusCoordinateRing k n)
  letI : IsDomain R := torusCoordinateRing_isDomain k n
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  have hg : (splitTorus k (Fin n → ℤ)).germToFunctionField ⊤
        (T.torus.left.appLE U ⊤ hpre r) =
      (splitTorus k (Fin n → ℤ)).germToFunctionField ⊤
        ((Scheme.ΓSpecIso R).inv (T.invariantAffineLaurentHom U hT r)) := by
    calc
      _ = dominantFunctionFieldMap T.torus.left
          (X.left.germToFunctionField U r) :=
        dominantFunctionFieldMap_appLE_value T.torus.left U ⊤ hpre r
      _ = dominantFunctionFieldMap T.torus.left
          (openTorusRationalAlgHom k n X.left T.torus.left
            (T.invariantAffineLaurentHom U hT r)) := by
        rw [T.invariantAffineLaurentHom_value U hT r]
      _ = torusCoordinateValueAlgHom k n (T.invariantAffineLaurentHom U hT r) :=
        openTorusRationalAlgHom_pullback k n X.left T.torus.left _
      _ = _ := torusCoordinateValueAlgHom_eq_germ k n _
  have hr := (splitTorus k (Fin n → ℤ)).germToFunctionField_injective ⊤ hg
  change T.invariantAffineLaurentHom U hT r =
    (Scheme.ΓSpecIso R).hom (T.torus.left.appLE U ⊤ hpre r)
  rw [hr, Iso.inv_hom_id_apply]

/-- The coordinate algebra of this actual open, expressed in the original
character lattice and with the original scalar map. -/
def invariantCoordinateAlgebraEquiv (hT : T.torusOpen ≤ U)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hA : T.invariantAffineCharacterAlgebra U =
      monoidChartAlgebra k (coordinateConeMonoid b I)) :
    Γ(X.left, U) ≃ₐ[k] monoidChartAlgebra k (coordinateConeMonoid b I) :=
  (T.invariantAffineCoordinateEquiv U hT).trans
    (Subalgebra.equivOfEq _ _ hA)

/-- The actual affine open is isomorphic to its recovered coordinate chart. -/
def invariantCoordinateChartIso (hU : IsAffineOpen U) (hT : T.torusOpen ≤ U)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hA : T.invariantAffineCharacterAlgebra U =
      monoidChartAlgebra k (coordinateConeMonoid b I)) :
    U.toScheme ≅ monoidChartScheme k (coordinateConeMonoid b I) :=
  hU.isoSpec ≪≫ Scheme.Spec.mapIso
    (T.invariantCoordinateAlgebraEquiv U hT b I hA).symm.toRingEquiv.toCommRingCatIso.op

/-- An actual open immersion into the original scheme, rather than an
abstract chart or an assumed chart presentation. -/
def invariantCoordinateChartMap (hU : IsAffineOpen U) (hT : T.torusOpen ≤ U)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hA : T.invariantAffineCharacterAlgebra U =
      monoidChartAlgebra k (coordinateConeMonoid b I)) :
    monoidChartScheme k (coordinateConeMonoid b I) ⟶ X.left :=
  (T.invariantCoordinateChartIso U hU hT b I hA).inv ≫ U.ι

instance invariantCoordinateChartMap_isOpenImmersion
    (hU : IsAffineOpen U) (hT : T.torusOpen ≤ U)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hA : T.invariantAffineCharacterAlgebra U =
      monoidChartAlgebra k (coordinateConeMonoid b I)) :
    IsOpenImmersion (T.invariantCoordinateChartMap U hU hT b I hA) := by
  dsimp only [invariantCoordinateChartMap]
  infer_instance

theorem invariantCoordinateChartMap_eq (hU : IsAffineOpen U) (hT : T.torusOpen ≤ U)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hA : T.invariantAffineCharacterAlgebra U =
      monoidChartAlgebra k (coordinateConeMonoid b I)) :
    T.invariantCoordinateChartMap U hU hT b I hA =
      Spec.map (CommRingCat.ofHom
        (T.invariantCoordinateAlgebraEquiv U hT b I hA).toRingHom) ≫ hU.fromSpec := by
  change (Spec.map (CommRingCat.ofHom
      (T.invariantCoordinateAlgebraEquiv U hT b I hA).toRingHom) ≫
      hU.isoSpec.inv) ≫ U.ι = _
  exact Category.assoc _ _ _

@[simp] theorem invariantCoordinateChartMap_opensRange
    (hU : IsAffineOpen U) (hT : T.torusOpen ≤ U)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hA : T.invariantAffineCharacterAlgebra U =
      monoidChartAlgebra k (coordinateConeMonoid b I)) :
    (T.invariantCoordinateChartMap U hU hT b I hA).opensRange = U := by
  dsimp only [invariantCoordinateChartMap]
  rw [Scheme.Hom.opensRange_comp_of_isIso,
    Scheme.Opens.opensRange_ι]

/-- The chart embedding retains the original torus map literally, including
its original character coordinates. -/
@[reassoc] theorem invariantCoordinateChartMap_torus
    (hU : IsAffineOpen U) (hT : T.torusOpen ≤ U)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hA : T.invariantAffineCharacterAlgebra U =
      monoidChartAlgebra k (coordinateConeMonoid b I)) :
    characterChartTorusMap k (coordinateConeMonoid b I) ≫
      T.invariantCoordinateChartMap U hU hT b I hA = T.torus.left := by
  let R := CommRingCat.of (torusCoordinateRing k n)
  let A := monoidChartAlgebra k (coordinateConeMonoid b I)
  let e := T.invariantCoordinateAlgebraEquiv U hT b I hA
  have hpre : (⊤ : (splitTorus k (Fin n → ℤ)).Opens) ≤ T.torus.left ⁻¹ᵁ U := by
    intro p hp
    exact hT ⟨p, rfl⟩
  have he : CommRingCat.ofHom e.toRingHom ≫ CommRingCat.ofHom A.val.toRingHom =
      CommRingCat.ofHom (T.invariantAffineLaurentHom U hT).toRingHom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    rfl
  calc
    _ = Spec.map (CommRingCat.ofHom e.toRingHom ≫
          CommRingCat.ofHom A.val.toRingHom) ≫ hU.fromSpec := by
      rw [T.invariantCoordinateChartMap_eq U hU hT b I hA,
        characterChartTorusMap, ← Spec.map_comp_assoc]
    _ = Spec.map (T.torus.left.appLE U ⊤ hpre ≫ (Scheme.ΓSpecIso R).hom) ≫
        hU.fromSpec := by
      rw [he, T.invariantAffineLaurentHom_eq_appLE U hT hpre]
    _ = Spec.map (Scheme.ΓSpecIso R).hom ≫
        (isAffineOpen_top (Spec R)).fromSpec ≫ T.torus.left := by
      rw [Spec.map_comp, Category.assoc,
        IsAffineOpen.SpecMap_appLE_fromSpec T.torus.left hU
          (isAffineOpen_top (Spec R)) hpre]
    _ = T.torus.left := by
      rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv,
        ← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id, Category.id_comp]

end AffineOpen

/-- The original smooth toric scheme has a finite cover by actual coordinate
charts, with all torus factors allowed and all torus inclusions identified. -/
theorem nonempty_coordinateChartCover :
    Nonempty (CoordinateChartCover k n X.left T.torus.left) := by
  classical
  choose U hxU hU hT hInv using T.exists_invariant_affine_neighbourhood
  letI (x : X.left) : Nonempty (U x) := ⟨⟨x, hxU x⟩⟩
  choose b I hA using fun x : X.left =>
    T.invariantAffineCharacterAlgebra_coordinateCone (U x) (hU x) (hInv x)
  have hcover : (Set.univ : Set X.left) ⊆ ⋃ x, (U x : Set X.left) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨x, hxU x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X.left => (U x : Set X.left)) (fun x => (U x).isOpen) hcover
  refine ⟨{
    Index := s
    finiteIndex := inferInstance
    basis := fun i => b i.val
    coordinates := fun i => I i.val
    map := fun i => T.invariantCoordinateChartMap (U i.val) (hU i.val)
      (hT i.val) (b i.val) (I i.val) (hA i.val)
    isOpenImmersion := fun i => inferInstance
    torus_eq := fun i => T.invariantCoordinateChartMap_torus (U i.val) (hU i.val)
      (hT i.val) (b i.val) (I i.val) (hA i.val)
    covers := ?_ }⟩
  intro x
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ x))
  obtain ⟨his, hxi⟩ := Set.mem_iUnion.mp hxi
  have hrange : x ∈
      (T.invariantCoordinateChartMap (U i) (hU i) (hT i) (b i) (I i) (hA i)).opensRange := by
    rwa [T.invariantCoordinateChartMap_opensRange]
  obtain ⟨z, hz⟩ := hrange
  exact ⟨⟨i, his⟩, z, hz⟩

end PaperVerification.ToricSchemes.SplitToricEmbedding

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.invariantCoordinateChartMap_torus
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.nonempty_coordinateChartCover
