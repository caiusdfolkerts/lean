module

public import PaperVerification.ToricTorusAction
public import PaperVerification.ToricChartOpenImmersions

@[expose] public section

/-!
# Equivariance of the actual affine chart inclusions

The chart subalgebra and its semigroup algebra are identified by the
proved range equivalence. The action is transported across that actual
affine scheme isomorphism. Face maps are equivariant because they arise
from semigroup homomorphisms commuting with inclusion in the character
lattice. All actions and equations are in schemes over Spec(k).
-/

noncomputable section

universe u v

open CategoryTheory MonoidalCategory MonObj

namespace PaperVerification.ToricSchemes

section Categorical

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {T A B : C} [MonObj T] [MonObj A] [MonObj B]

/-- A commuting triangle of monoid maps is equivariant for the
restrictions of the actual regular monoid actions. -/
theorem restrictedRegular_isModHom (iA : T ⟶ A) (iB : T ⟶ B) (f : A ⟶ B)
    [IsMonHom iA] [IsMonHom iB] [IsMonHom f] (h : iA ≫ f = iB) :
    letI : ModObj A A := ModObj.regular A
    letI : ModObj B B := ModObj.regular B
    letI : ModObj T A := Mod.scalarRestriction iA A
    letI : ModObj T B := Mod.scalarRestriction iB B
    IsModHom T f := by
  letI : ModObj A A := ModObj.regular A
  letI : ModObj B B := ModObj.regular B
  letI : ModObj T A := Mod.scalarRestriction iA A
  letI : ModObj T B := Mod.scalarRestriction iB B
  refine ⟨?_⟩
  change (iA ▷ A ≫ μ[A]) ≫ f = T ◁ f ≫ (iB ▷ B ≫ μ[B])
  calc
    (iA ▷ A ≫ μ[A]) ≫ f = (iA ⊗ₘ 𝟙 A) ≫ (f ⊗ₘ f) ≫ μ[B] := by
      rw [Category.assoc, IsMonHom.mul_hom, tensorHom_id]
    _ = (iB ⊗ₘ f) ≫ μ[B] := by
      rw [← Category.assoc, tensorHom_comp_tensorHom, h, Category.id_comp]
    _ = _ := by rw [tensorHom_def', Category.assoc]

end Categorical

open AlgebraicGeometry Opposite
open PaperVerification.ToricCharacters

variable (k : Type (max u v)) [CommRing k] {M : Type v} [AddCommGroup M]

def semigroupFaceMapOver {S T : AddSubmonoid M} (hST : S≤T) :
    semigroupChartOver k T ⟶ semigroupChartOver k S :=
  (algSpec (CommRingCat.of k)).map
    (CommAlgCat.ofHom (AddMonoidAlgebra.mapDomainBialgHom k
      (AddSubmonoid.inclusion hST)).toAlgHom).op

instance semigroupFaceMapOver_isMonHom {S T : AddSubmonoid M} (hST : S≤T) :
    IsMonHom (semigroupFaceMapOver k hST) := by
  change IsMonHom (((bialgSpec (CommRingCat.of k)).map
    (CommBialgCat.ofHom (AddMonoidAlgebra.mapDomainBialgHom k
      (AddSubmonoid.inclusion hST))).op).hom)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem torusToSemigroupChartOver_faceMap {S T : AddSubmonoid M} (hST : S≤T) :
    torusToSemigroupChartOver k T ≫ semigroupFaceMapOver k hST =
      torusToSemigroupChartOver k S := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom
      (AddMonoidAlgebra.mapDomainBialgHom k T.subtype).toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (AddMonoidAlgebra.mapDomainBialgHom k
          (AddSubmonoid.inclusion hST)).toAlgHom.toRingHom) =
    Spec.map (CommRingCat.ofHom
      (AddMonoidAlgebra.mapDomainBialgHom k S.subtype).toAlgHom.toRingHom)
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro f
  change AddMonoidAlgebra.mapDomainBialgHom k T.subtype
      (AddMonoidAlgebra.mapDomainBialgHom k (AddSubmonoid.inclusion hST) f) =
    AddMonoidAlgebra.mapDomainBialgHom k S.subtype f
  rw [AddMonoidAlgebra.mapDomainBialgHom_mapDomainBialgHom]
  rfl

instance semigroupFaceMapOver_isModHom {S T : AddSubmonoid M} (hST : S≤T) :
    IsModHom (splitTorusOver k M) (semigroupFaceMapOver k hST) :=
  restrictedRegular_isModHom (torusToSemigroupChartOver k T)
    (torusToSemigroupChartOver k S) (semigroupFaceMapOver k hST)
    (torusToSemigroupChartOver_faceMap k hST)

instance monoidChartScheme_isOver (S : AddSubmonoid M) :
    (monoidChartScheme k S).Over (Spec (CommRingCat.of k)) := by
  dsimp only [monoidChartScheme]
  infer_instance

abbrev monoidChartSchemeOver (S : AddSubmonoid M) : Over (Spec (CommRingCat.of k)) :=
  (monoidChartScheme k S).asOver (Spec (CommRingCat.of k))

/-- The actual chart subalgebra spectrum is isomorphic over k to the
semigroup spectrum. Contravariance gives this displayed direction. -/
def monoidChartSchemeOverIso (S : AddSubmonoid M) :
    monoidChartSchemeOver k S ≅ semigroupChartOver k S :=
  (algSpec (CommRingCat.of k)).mapIso
    (CommAlgCat.isoMk (monoidChartAlgebraEquiv k S)).op

instance monoidChartScheme_torusAction (S : AddSubmonoid M) :
    ModObj (splitTorusOver k M) (monoidChartSchemeOver k S) := by
  letI : IsMonHom (Iso.refl (splitTorusOver k M)).hom := by
    change IsMonHom (𝟙 (splitTorusOver k M))
    infer_instance
  exact ModObj.ofIso (Iso.refl (splitTorusOver k M)) (monoidChartSchemeOverIso k S).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
instance monoidChartSchemeOverIso_isModHom (S : AddSubmonoid M) :
    IsModHom (splitTorusOver k M) (monoidChartSchemeOverIso k S).hom where
  smul_hom := by
    change ((𝟙 _ ⊗ₘ (monoidChartSchemeOverIso k S).hom) ≫
      γ[splitTorusOver k M,semigroupChartOver k S] ≫
        (monoidChartSchemeOverIso k S).inv) ≫
      (monoidChartSchemeOverIso k S).hom = _
    simp

instance monoidChartSpecMap_isOver {S T : AddSubmonoid M} (hST : S≤T) :
    (monoidChartSpecMap k hST).IsOver (Spec (CommRingCat.of k)) := by
  constructor
  change Spec.map (CommRingCat.ofHom (monoidChartInclusion k hST).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (monoidChartAlgebra k S))) =
    Spec.map (CommRingCat.ofHom (algebraMap k (monoidChartAlgebra k T)))
  rw [← Spec.map_comp]
  congr 1

abbrev monoidChartSpecMapOver {S T : AddSubmonoid M} (hST : S≤T) :
    monoidChartSchemeOver k T ⟶ monoidChartSchemeOver k S :=
  (monoidChartSpecMap k hST).asOver (Spec (CommRingCat.of k))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem monoidChartSpecMapOver_conjugate {S T : AddSubmonoid M} (hST : S≤T) :
    monoidChartSpecMapOver k hST =
      (monoidChartSchemeOverIso k T).hom ≫ semigroupFaceMapOver k hST ≫
        (monoidChartSchemeOverIso k S).inv := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (monoidChartInclusion k hST).toRingHom) =
    Spec.map (CommRingCat.ofHom (monoidChartAlgebraEquiv k T).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (AddMonoidAlgebra.mapDomainBialgHom k
          (AddSubmonoid.inclusion hST)).toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (monoidChartAlgebraEquiv k S).symm.toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro f
  change monoidChartInclusion k hST f =
    monoidChartAlgebraEquiv k T
      (AddMonoidAlgebra.mapDomainBialgHom k (AddSubmonoid.inclusion hST)
        ((monoidChartAlgebraEquiv k S).symm f))
  apply Subtype.ext
  obtain ⟨g,rfl⟩ := (monoidChartAlgebraEquiv k S).surjective f
  rw [AlgEquiv.symm_apply_apply]
  change AddMonoidAlgebra.mapDomainBialgHom k S.subtype g =
    AddMonoidAlgebra.mapDomainBialgHom k T.subtype
      (AddMonoidAlgebra.mapDomainBialgHom k (AddSubmonoid.inclusion hST) g)
  rw [AddMonoidAlgebra.mapDomainBialgHom_mapDomainBialgHom]
  rfl

/-- Literal face inclusions of actual chart spectra are equivariant. -/
instance monoidChartSpecMapOver_isModHom {S T : AddSubmonoid M} (hST : S≤T) :
    IsModHom (splitTorusOver k M) (monoidChartSpecMapOver k hST) := by
  rw [monoidChartSpecMapOver_conjugate]
  infer_instance

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.monoidChartSpecMapOver_isModHom
