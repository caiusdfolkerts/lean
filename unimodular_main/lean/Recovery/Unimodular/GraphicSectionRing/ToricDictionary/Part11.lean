module

public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.Part10
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.Topology.Sheaves.LocallySurjective

@[expose] public section
set_option autoImplicit false

section
-- BEGIN PaperVerification.ToricChartActions



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
    _ = _ := by rw [MonoidalCategory.tensorHom_def', Category.assoc]

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
end
-- END PaperVerification.ToricChartActions
end

section
-- BEGIN PaperVerification.ToricFanAction



/-!
# The actual split-torus action on the glued fan scheme

Every chart action is the spectrum of the character coaction. Its face
inclusions are equivariant, and the actual directed affine open cover
glues these maps into a group-scheme action. The embedded dense torus
inherits its genuine multiplication map.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory MonObj
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes

theorem action_extends_mul_comp {C : Type*} [Category C] [MonoidalCategory C]
    (G A B : C) [MonObj G] [ModObj G A] [ModObj G B]
    (f : G ⟶ A) (g : A ⟶ B) [IsModHom G g]
    (hf : μ[G] ≫ f = G ◁ f ≫ γ[G,A]) :
    μ[G] ≫ (f ≫ g) = G ◁ (f ≫ g) ≫ γ[G,B] := by
  have hg : γ[G,A] ≫ g = G ◁ g ≫ γ[G,B] :=
    IsModHom.smul_hom (A := G) (f := g)
  calc
    μ[G] ≫ (f ≫ g) = (μ[G] ≫ f) ≫ g := (Category.assoc _ _ _).symm
    _ = (G ◁ f ≫ γ[G,A]) ≫ g := congrArg (fun h => h ≫ g) hf
    _ = G ◁ f ≫ (γ[G,A] ≫ g) := Category.assoc _ _ _
    _ = G ◁ f ≫ (G ◁ g ≫ γ[G,B]) := congrArg (fun h => G ◁ f ≫ h) hg
    _ = (G ◁ f ≫ G ◁ g) ≫ γ[G,B] := (Category.assoc _ _ _).symm
    _ = G ◁ (f ≫ g) ≫ γ[G,B] :=
      congrArg (fun h => h ≫ γ[G,B]) (whiskerLeft_comp G f g).symm

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [CommRing k]

instance coneChart_isOver (s : Finset (Lattice n)) :
    (coneChart k s).Over (Spec (CommRingCat.of k)) := by
  change (monoidChartScheme k (dualConeMonoid s)).Over _
  infer_instance

instance coneChartFaceMap_isOver {s t : Finset (Lattice n)} (hts : t ⊆ s) :
    (coneChartFaceMap k hts).IsOver (Spec (CommRingCat.of k)) := by
  change (monoidChartSpecMap k (dualConeMonoid_antitone hts)).IsOver _
  infer_instance

/-- The actual structure morphism to the field spectrum is glued from
its specified algebra structures on every semigroup chart. -/
def fanSchemeBaseCocone : Cocone («Σ».coneDiagram k) where
  pt := Spec (CommRingCat.of k)
  «ι» := {
    app := fun s => coneChart k s.val ↘ Spec (CommRingCat.of k)
    naturality := by
      intro s t h
      change coneChartFaceMap k (leOfHom h) ≫
        (coneChart k t.val ↘ Spec (CommRingCat.of k)) =
          (coneChart k s.val ↘ Spec (CommRingCat.of k)) ≫ 𝟙 _
      simpa only [Category.comp_id] using
        (comp_over (coneChartFaceMap k (leOfHom h)) (Spec (CommRingCat.of k))) }

def fanSchemeStructureMap : «Σ».fanScheme k ⟶ Spec (CommRingCat.of k) :=
  colimit.desc («Σ».coneDiagram k) («Σ».fanSchemeBaseCocone k)

instance fanScheme_isOver : («Σ».fanScheme k).Over (Spec (CommRingCat.of k)) where
  hom := «Σ».fanSchemeStructureMap k

instance fanChartMap_isOver (s : «Σ».ConeIndex) :
    («Σ».fanChartMap k s).IsOver (Spec (CommRingCat.of k)) where
  comp_over := by
    change colimit.ι («Σ».coneDiagram k) s ≫
      colimit.desc («Σ».coneDiagram k) («Σ».fanSchemeBaseCocone k) = _
    exact colimit.ι_desc («Σ».fanSchemeBaseCocone k) s

instance fanSchemeOpenCover_preorder : Preorder («Σ».fanSchemeOpenCover k).I₀ :=
  inferInstanceAs (Preorder «Σ».ConeIndex)

instance fanSchemeOpenCover_category : Category («Σ».fanSchemeOpenCover k).I₀ :=
  inferInstanceAs (Category «Σ».ConeIndex)

instance fanSchemeOpenCover_isOver :
    («Σ».fanSchemeOpenCover k).Over (Spec (CommRingCat.of k)) where
  over s := coneChart_isOver k s.val
  isOver_map s := «Σ».fanChartMap_isOver k s

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The common-face pullback supplies actual local directedness of the
chosen affine cover, including its residue-field-compatible point lifting. -/
instance fanSchemeOpenCover_locallyDirected : («Σ».fanSchemeOpenCover k).LocallyDirected where
  trans {s t} h := coneChartFaceMap k (leOfHom h)
  trans_id s := coneChartFaceMap_self k s.val
  trans_comp hst htu := (coneChartFaceMap_comp k (leOfHom htu) (leOfHom hst)).symm
  w h := «Σ».fanChartMap_naturality k (leOfHom h)
  directed {s t} x := by
    let l : «Σ».ConeIndex :=
      ⟨t.val ∩ s.val, «Σ».downward t.val t.property _ Finset.inter_subset_left⟩
    let H := «Σ».fanChart_inter_isPullback k t s
    refine ⟨l,homOfLE Finset.inter_subset_right,homOfLE Finset.inter_subset_left,
      H.isoPullback.inv x,?_⟩
    have heq : pullback.lift
        (coneChartFaceMap k (Finset.inter_subset_right : t.val∩s.val ⊆ s.val))
        (coneChartFaceMap k (Finset.inter_subset_left : t.val∩s.val ⊆ t.val))
        ((«Σ».fanChartMap_naturality k (s := l) (t := s)
          Finset.inter_subset_right).trans
            («Σ».fanChartMap_naturality k (s := l) (t := t)
              Finset.inter_subset_left).symm) =
        H.isoPullback.hom := by
      apply pullback.hom_ext <;> simp
    change (pullback.lift
      (coneChartFaceMap k (Finset.inter_subset_right : t.val∩s.val ⊆ s.val))
      (coneChartFaceMap k (Finset.inter_subset_left : t.val∩s.val ⊆ t.val)) _)
        (H.isoPullback.inv x) = x
    have hpoint := congrArg
      (fun f : coneChart k (t.val∩s.val) ⟶
        pullback («Σ».fanChartMap k s) («Σ».fanChartMap k t) =>
          f (H.isoPullback.inv x)) heq
    have hcancel := congrArg
      (fun f : pullback («Σ».fanChartMap k s) («Σ».fanChartMap k t) ⟶
        pullback («Σ».fanChartMap k s) («Σ».fanChartMap k t) => f x)
      H.isoPullback.inv_hom_id
    change H.isoPullback.hom (H.isoPullback.inv x) = x at hcancel
    exact hpoint.trans hcancel
  property_trans {s t} h :=
    «Σ».coneChartFaceMap_isOpenImmersion k t.val s.val t.property (leOfHom h)

abbrev fanSchemeOver : Over (Spec (CommRingCat.of k)) :=
  («Σ».fanScheme k).asOver (Spec (CommRingCat.of k))

instance coneChart_torusAction (s : Finset (Lattice n)) :
    ModObj (ToricSchemes.splitTorusOver k (Lattice n))
      ((coneChart k s).asOver (Spec (CommRingCat.of k))) := by
  change ModObj (ToricSchemes.splitTorusOver k (Lattice n))
    (monoidChartSchemeOver k (dualConeMonoid s))
  infer_instance

instance coneChartFaceMap_isModHom {s t : Finset (Lattice n)} (hts : t ⊆ s) :
    IsModHom (ToricSchemes.splitTorusOver k (Lattice n))
      ((coneChartFaceMap k hts).asOver (Spec (CommRingCat.of k))) := by
  change IsModHom (ToricSchemes.splitTorusOver k (Lattice n))
    (monoidChartSpecMapOver k (dualConeMonoid_antitone hts))
  infer_instance

/-- Genuine action of the split group scheme on the actual glued scheme. -/
instance fanScheme_torusAction :
    ModObj (ToricSchemes.splitTorusOver k (Lattice n)) («Σ».fanSchemeOver k) := by
  letI : ∀ i : («Σ».fanSchemeOpenCover k).I₀,
      ModObj (ToricSchemes.splitTorusOver k (Lattice n))
        (((«Σ».fanSchemeOpenCover k).X i).asOver (Spec (CommRingCat.of k))) :=
    fun i => coneChart_torusAction k i.val
  exact gluedModObj («Σ».fanSchemeOpenCover k)
    (ToricSchemes.splitTorusOver k (Lattice n)) (fun {i j} h => by
      change IsModHom (ToricSchemes.splitTorusOver k (Lattice n))
        ((coneChartFaceMap k (leOfHom h)).asOver (Spec (CommRingCat.of k)))
      exact coneChartFaceMap_isModHom k (leOfHom h))

instance fanChartMap_isModHom (s : «Σ».ConeIndex) :
    IsModHom (ToricSchemes.splitTorusOver k (Lattice n))
      ((«Σ».fanChartMap k s).asOver (Spec (CommRingCat.of k))) := by
  letI : ∀ i : («Σ».fanSchemeOpenCover k).I₀,
      ModObj (ToricSchemes.splitTorusOver k (Lattice n))
        (((«Σ».fanSchemeOpenCover k).X i).asOver (Spec (CommRingCat.of k))) :=
    fun i => coneChart_torusAction k i.val
  exact gluedModObj_chart («Σ».fanSchemeOpenCover k)
    (ToricSchemes.splitTorusOver k (Lattice n)) (fun {i j} h => by
      change IsModHom (ToricSchemes.splitTorusOver k (Lattice n))
        ((coneChartFaceMap k (leOfHom h)).asOver (Spec (CommRingCat.of k)))
      exact coneChartFaceMap_isModHom k (leOfHom h)) s

/-- Actual torus-to-chart morphism, with its specified algebra map. -/
def torusChartMapOver («Σ» : SmoothCompleteFan n) (s : Finset (Lattice n)) :
    ToricSchemes.splitTorusOver k (Lattice n) ⟶
      (coneChart k s).asOver (Spec (CommRingCat.of k)) :=
  torusToSemigroupChartOver k (dualConeMonoid s) ≫
    (monoidChartSchemeOverIso k (dualConeMonoid s)).inv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc] theorem torusChartMapOver_action (s : Finset (Lattice n)) :
    μ[ToricSchemes.splitTorusOver k (Lattice n)] ≫ «Σ».torusChartMapOver k s =
      ToricSchemes.splitTorusOver k (Lattice n) ◁ «Σ».torusChartMapOver k s ≫
        γ[ToricSchemes.splitTorusOver k (Lattice n),
          (coneChart k s).asOver (Spec (CommRingCat.of k))] := by
  change μ[ToricSchemes.splitTorusOver k (Lattice n)] ≫
      (torusToSemigroupChartOver k (dualConeMonoid s) ≫
        (monoidChartSchemeOverIso k (dualConeMonoid s)).inv) =
    ToricSchemes.splitTorusOver k (Lattice n) ◁
      (torusToSemigroupChartOver k (dualConeMonoid s) ≫
        (monoidChartSchemeOverIso k (dualConeMonoid s)).inv) ≫
      γ[ToricSchemes.splitTorusOver k (Lattice n),
        monoidChartSchemeOver k (dualConeMonoid s)]
  apply action_extends_mul_comp
  simpa only [id_tensorHom] using
    (semigroupChart_action_extends_torus k (dualConeMonoid s)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem torusChartMapOver_zero :
    («Σ».torusChartMapOver k (∅ : Finset (Lattice n))).left =
      (zeroConeChartIso k n).inv := by
  change Spec.map (CommRingCat.ofHom (monoidChartMap k (dualConeMonoid ∅)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (monoidChartAlgebraEquiv k (dualConeMonoid ∅)).symm.toRingHom) =
    Spec.map (CommRingCat.ofHom (zeroConeChartAlgEquiv k n).toRingHom)
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro f
  exact congrArg Subtype.val
    ((monoidChartAlgebraEquiv k (dualConeMonoid (∅ : Finset (Lattice n)))).apply_symm_apply f)

instance geometricSplitTorus_isOver :
    (PaperVerification.ToricGeometry.splitTorus k n).Over (Spec (CommRingCat.of k)) := by
  change (ToricSchemes.splitTorus k (Lattice n)).Over _
  infer_instance

instance torusOpenMap_isOver :
    («Σ».torusOpenMap k).IsOver (Spec (CommRingCat.of k)) := by
  change («Σ».fanChartMap k «Σ».zeroConeIndex).IsOver _
  exact «Σ».fanChartMap_isOver k «Σ».zeroConeIndex

instance splitTorusOpenMap_isOver :
    («Σ».splitTorusOpenMap k).IsOver (Spec (CommRingCat.of k)) := by
  constructor
  change ((zeroConeChartIso k n).inv ≫ «Σ».torusOpenMap k) ≫
      («Σ».fanScheme k ↘ Spec (CommRingCat.of k)) = _
  rw [Category.assoc,comp_over]
  exact (congrArg (fun f => f ≫ (coneChart k (∅ : Finset (Lattice n)) ↘
    Spec (CommRingCat.of k))) («Σ».torusChartMapOver_zero k).symm).trans
      (Over.w («Σ».torusChartMapOver k ∅))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The global action restricts to the actual torus multiplication.
This equality is over Spec(k), not just on k-rational points. -/
theorem fanScheme_action_extends_torus :
    μ[ToricSchemes.splitTorusOver k (Lattice n)] ≫
        («Σ».splitTorusOpenMap k).asOver (Spec (CommRingCat.of k)) =
      ToricSchemes.splitTorusOver k (Lattice n) ◁
        («Σ».splitTorusOpenMap k).asOver (Spec (CommRingCat.of k)) ≫
          γ[ToricSchemes.splitTorusOver k (Lattice n),«Σ».fanSchemeOver k] := by
  have hmap : («Σ».splitTorusOpenMap k).asOver (Spec (CommRingCat.of k)) =
      «Σ».torusChartMapOver k ∅ ≫
        («Σ».fanChartMap k «Σ».zeroConeIndex).asOver (Spec (CommRingCat.of k)) := by
    apply Over.OverMorphism.ext
    change (zeroConeChartIso k n).inv ≫ «Σ».torusOpenMap k =
      («Σ».torusChartMapOver k ∅).left ≫ «Σ».fanChartMap k «Σ».zeroConeIndex
    rw [«Σ».torusChartMapOver_zero]
    rfl
  erw [hmap]
  exact action_extends_mul_comp
    (ToricSchemes.splitTorusOver k (Lattice n))
    ((coneChart k ∅).asOver (Spec (CommRingCat.of k))) («Σ».fanSchemeOver k)
    («Σ».torusChartMapOver k ∅)
    ((«Σ».fanChartMap k «Σ».zeroConeIndex).asOver (Spec (CommRingCat.of k)))
    («Σ».torusChartMapOver_action k ∅)

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanScheme_torusAction
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanScheme_action_extends_torus
end
-- END PaperVerification.ToricFanAction
end

section
-- BEGIN PaperVerification.ToricDominantFunctionField



/-! # Actual function-field pullback along a dominant morphism -/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory TopologicalSpace

/-- A nonempty actual open subscheme of a preirreducible scheme is
dominant. This is a topological consequence of the open immersion, not
an additional density assumption on a chart. -/
instance (priority := 80) openImmersion_isDominant_of_preirreducible
    {U X : Scheme.{u}} [Nonempty U] [PreirreducibleSpace X]
    (j : U ⟶ X) [IsOpenImmersion j] : IsDominant j :=
  ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace j
    j.isOpenEmbedding.isOpenMap⟩

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsDominant f]
    [IrreducibleSpace X] [IrreducibleSpace Y]

theorem genericPoint_eq_of_isDominant :
    f (genericPoint X)=genericPoint Y := by
  apply ((genericPoint_spec Y).eq _).symm
  simpa only [Set.image_univ,f.denseRange.closure_range] using
    (genericPoint_spec X).image f.continuous

/-- This is the genuine map on generic stalks, with generic points
identified by dominance. No fraction-field embedding is postulated. -/
def dominantFunctionFieldMap : Y.functionField →+* X.functionField :=
  ((Y.presheaf.stalkCongr
      (.of_eq (genericPoint_eq_of_isDominant f).symm)).hom ≫
    f.stalkMap (genericPoint X)).hom

theorem dominant_preimage_nonempty (U : Y.Opens) [Nonempty U] :
    Nonempty (f ⁻¹ᵁ U) := by
  refine ⟨⟨genericPoint X,?_⟩⟩
  change f (genericPoint X)∈U
  rw [genericPoint_eq_of_isDominant]
  exact ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr
    (by simpa using (show Nonempty U from inferInstance))

set_option backward.isDefEq.respectTransparency.types false in
theorem dominantFunctionFieldMap_germ_hom (U : Y.Opens) [Nonempty U]
    [Nonempty (f ⁻¹ᵁ U)] :
    Y.germToFunctionField U ≫ CommRingCat.ofHom (dominantFunctionFieldMap f) =
      f.app U ≫ X.germToFunctionField (f ⁻¹ᵁ U) := by
  change Y.germToFunctionField U ≫
    ((Y.presheaf.stalkCongr
      (.of_eq (genericPoint_eq_of_isDominant f).symm)).hom ≫
      f.stalkMap (genericPoint X)) = _
  simp only [Scheme.germToFunctionField,TopCat.Presheaf.stalkCongr_hom,
    ← Category.assoc]
  rw [TopCat.Presheaf.germ_stalkSpecializes]
  exact f.germ_stalkMap U (genericPoint X) _

@[simp] theorem dominantFunctionFieldMap_germ (U : Y.Opens) [Nonempty U]
    [Nonempty (f ⁻¹ᵁ U)] (a : Γ(Y,U)) :
    dominantFunctionFieldMap f (Y.germToFunctionField U a) =
      X.germToFunctionField (f ⁻¹ᵁ U) (f.app U a) :=
  congrArg (fun g=>g a) (dominantFunctionFieldMap_germ_hom f U)

set_option backward.isDefEq.respectTransparency.types false in
theorem dominantFunctionFieldMap_comp {Z : Scheme.{u}} [IrreducibleSpace Z]
    (g : Y ⟶ Z) [IsDominant g] :
    dominantFunctionFieldMap (f ≫ g) =
      (dominantFunctionFieldMap f).comp (dominantFunctionFieldMap g) := by
  apply CommRingCat.hom_ext_iff.mp
  apply Z.presheaf.stalk_hom_ext
  intro U hU
  letI : Nonempty U := ⟨⟨genericPoint Z,hU⟩⟩
  letI : Nonempty (g ⁻¹ᵁ U) := dominant_preimage_nonempty g U
  letI : Nonempty (f ⁻¹ᵁ (g ⁻¹ᵁ U)) :=
    dominant_preimage_nonempty f (g ⁻¹ᵁ U)
  letI : Nonempty ((f ≫ g) ⁻¹ᵁ U) := dominant_preimage_nonempty (f ≫ g) U
  change Z.germToFunctionField U ≫ CommRingCat.ofHom (dominantFunctionFieldMap (f≫g)) =
    Z.germToFunctionField U ≫
      (CommRingCat.ofHom (dominantFunctionFieldMap g) ≫
        CommRingCat.ofHom (dominantFunctionFieldMap f))
  calc
    _ = (g.app U ≫ f.app (g ⁻¹ᵁ U)) ≫
        X.germToFunctionField (f ⁻¹ᵁ (g ⁻¹ᵁ U)) :=
      dominantFunctionFieldMap_germ_hom (f ≫ g) U
    _ = g.app U ≫ (f.app (g ⁻¹ᵁ U) ≫
        X.germToFunctionField (f ⁻¹ᵁ (g ⁻¹ᵁ U))) := Category.assoc _ _ _
    _ = g.app U ≫ (Y.germToFunctionField (g ⁻¹ᵁ U) ≫
        CommRingCat.ofHom (dominantFunctionFieldMap f)) :=
      congrArg (fun h : Γ(Y,g ⁻¹ᵁ U) ⟶ X.functionField => g.app U ≫ h)
        (dominantFunctionFieldMap_germ_hom f (g ⁻¹ᵁ U)).symm
    _ = (g.app U ≫ Y.germToFunctionField (g ⁻¹ᵁ U)) ≫
        CommRingCat.ofHom (dominantFunctionFieldMap f) := (Category.assoc _ _ _).symm
    _ = (Z.germToFunctionField U ≫ CommRingCat.ofHom (dominantFunctionFieldMap g)) ≫
        CommRingCat.ofHom (dominantFunctionFieldMap f) :=
      congrArg (fun h : Γ(Z,U) ⟶ Y.functionField =>
        h ≫ CommRingCat.ofHom (dominantFunctionFieldMap f))
        (dominantFunctionFieldMap_germ_hom g U).symm
    _ = _ := Category.assoc _ _ _

theorem dominantFunctionFieldMap_injective [IsIntegral X] [IsIntegral Y] :
    Function.Injective (dominantFunctionFieldMap f) :=
  (dominantFunctionFieldMap f).injective

theorem dominantFunctionFieldMap_eq_openImmersion [IsOpenImmersion f] :
    dominantFunctionFieldMap f=(openImmersionFunctionFieldEquiv f).toRingHom := rfl

/-- Compatibility with every actual local ring, not just global regular
functions. This is the basic regularity input for Cartier pullback. -/
theorem dominantFunctionFieldMap_stalk [IsIntegral X] [IsIntegral Y]
    (x : X) (a : Y.presheaf.stalk (f x)) :
    dominantFunctionFieldMap f
        (algebraMap (Y.presheaf.stalk (f x)) Y.functionField a) =
      algebraMap (X.presheaf.stalk x) X.functionField (f.stalkMap x a) := by
  obtain ⟨U,hx,s,rfl⟩ := Y.presheaf.exists_germ_eq a
  letI : Nonempty U := ⟨⟨f x,hx⟩⟩
  letI : Nonempty (f ⁻¹ᵁ U) := ⟨⟨x,hx⟩⟩
  rw [Y.algebraMap_germ_eq_germToFunctionField hx s,
    dominantFunctionFieldMap_germ,f.germ_stalkMap_apply,
    X.algebraMap_germ_eq_germToFunctionField hx (f.app U s)]

theorem dominantFunctionFieldMap_mem_regularAt [IsIntegral X] [IsIntegral Y]
    (x : X) (a : Y.functionField) (ha : a∈regularAtSubring Y (f x)) :
    dominantFunctionFieldMap f a∈regularAtSubring X x := by
  obtain ⟨s,rfl⟩ := ha
  exact ⟨f.stalkMap x s,(dominantFunctionFieldMap_stalk f x s).symm⟩

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.dominantFunctionFieldMap_stalk
end
-- END PaperVerification.ToricDominantFunctionField
end

section
-- BEGIN PaperVerification.ToricBaseSectionNaturality



/-! # Base scalars in actual regular and rational sections -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite

namespace PaperVerification.ToricSchemes.BaseSections

variable (k : Type u) [CommRing k]

theorem scalarMap_top_natural {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k))] (c : k) :
    f.appTop (scalarMap k Y ⊤ c)=scalarMap k X ⊤ c := by
  have h := congrArg
    (fun g : X ⟶ Spec (CommRingCat.of k)=>g.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c))
    (comp_over f (Spec (CommRingCat.of k)))
  simpa only [scalarMap,RingHom.comp_apply,homOfLE_refl,op_id,
    X.presheaf.map_id (op (⊤ : X.Opens)),Y.presheaf.map_id (op (⊤ : Y.Opens)),
    CommRingCat.hom_id,RingHom.id_apply,Scheme.Hom.comp_appTop,
    ConcreteCategory.comp_apply] using h

theorem scalarMap_affine_top (A : Type u) [CommRing A] [Algebra k A] (c : k) :
    scalarMap k (Spec (CommRingCat.of A)) ⊤ c =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv (algebraMap k A c) := by
  have h := congrArg
    (fun f : CommRingCat.of k ⟶ Γ(Spec (CommRingCat.of A),⊤) => f.hom c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k A)))
  simpa only [scalarMap,RingHom.comp_apply,homOfLE_refl,op_id,
    (Spec (CommRingCat.of A)).presheaf.map_id (op (⊤ : (Spec (CommRingCat.of A)).Opens)),
    CommRingCat.hom_id,RingHom.id_apply,specOverSpec_over,
    CommRingCat.hom_comp,CommRingCat.hom_ofHom] using h.symm

theorem scalarMap_restrict {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] {U V : X.Opens} (h : V≤U) (c : k) :
    X.presheaf.map (homOfLE h).op (scalarMap k X U c)=scalarMap k X V c := by
  simp only [scalarMap,RingHom.comp_apply]
  exact congrArg (fun f=>f (((X ↘ Spec (CommRingCat.of k)).appTop).hom
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)))
      (X.presheaf.map_comp (homOfLE le_top).op (homOfLE h).op).symm

open scoped BaseSections

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]

theorem germ_scalarMap (U : X.Opens) [Nonempty U] (c : k) :
    X.germToFunctionField U (scalarMap k X U c)=algebraMap k X.functionField c := by
  have h := scalarMap_restrict k (X:=X) (U:=⊤) (V:=U) le_top c
  rw [← h,germToFunctionField_restrict]
  rfl

/-- The scalar-compatible regular-function embedding in the actual
generic stalk, on every nonempty open. -/
def regularValueAlgHom (U : X.Opens) [Nonempty U] :
    Γ(X,U) →ₐ[k] X.functionField where
  __ := (X.germToFunctionField U).hom
  commutes' := germ_scalarMap k U

/-- Dominant pullback preserves the scalars from the actual structure
morphisms. -/
def dominantFunctionFieldAlgHom (f : X ⟶ Y) [IsDominant f]
    [f.IsOver (Spec (CommRingCat.of k))] : Y.functionField →ₐ[k] X.functionField where
  __ := dominantFunctionFieldMap f
  commutes' c := by
    letI : Nonempty (f ⁻¹ᵁ (⊤ : Y.Opens)) := dominant_preimage_nonempty f ⊤
    change dominantFunctionFieldMap f
      (Y.germToFunctionField ⊤ (scalarMap k Y ⊤ c)) = _
    rw [dominantFunctionFieldMap_germ]
    change X.germToFunctionField ⊤ (f.appTop (scalarMap k Y ⊤ c)) = _
    rw [scalarMap_top_natural]
    rfl

end PaperVerification.ToricSchemes.BaseSections
end
-- END PaperVerification.ToricBaseSectionNaturality
end

section
-- BEGIN PaperVerification.ToricFanSectionCoordinates



/-!
# The actual base-linear character coordinates of global sections

The scalar maps are induced by the actual structural morphism to Spec(k).
The resulting isomorphism therefore concerns the ordinary vector space
of genuine global sections over the base field, with its true rational
value map.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite



namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped BaseSections Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

local instance fanSectionCoordinates_splitTorus_integral : IsIntegral (ToricGeometry.splitTorus k n) := by
  letI := torusCoordinateRing_isDomain k n
  change IsIntegral (Spec (CommRingCat.of (torusCoordinateRing k n)))
  infer_instance

/-- Constants in the character algebra agree with constants from the
actual structural morphism of the glued scheme. -/
theorem rationalScalar_eq_algebraMap (c : k) :
    «Σ».rationalScalar k c=algebraMap k («Σ».fanScheme k).functionField c := by
  let j := «Σ».splitTorusOpenMap k
  let A := AddMonoidAlgebra k (Lattice n)
  have hconst : j.appTop (BaseSections.scalarMap k («Σ».fanScheme k) ⊤ c) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv (algebraMap k A c) := by
    calc
      j.appTop (BaseSections.scalarMap k («Σ».fanScheme k) ⊤ c) =
          BaseSections.scalarMap k (ToricGeometry.splitTorus k n) ⊤ c :=
        BaseSections.scalarMap_top_natural k j c
      _ = _ := by
        change BaseSections.scalarMap k (Spec (CommRingCat.of A)) ⊤ c = _
        exact BaseSections.scalarMap_affine_top k A c
  change «Σ».torusRationalMap k (algebraMap k A c) =
    («Σ».fanScheme k).germToFunctionField ⊤ (BaseSections.scalarMap k («Σ».fanScheme k) ⊤ c)
  rw [«Σ».torusRationalMap_eq_openImmersion]
  letI : Nonempty (j ⁻¹ᵁ (⊤ : («Σ».fanScheme k).Opens)) :=
    openImmersion_preimage_nonempty j ⊤
  apply (openImmersionFunctionFieldEquiv j).injective
  change (openImmersionFunctionFieldEquiv j)
    ((openImmersionFunctionFieldEquiv j).symm
      ((ToricGeometry.splitTorus k n).germToFunctionField ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (algebraMap k A c)))) = _
  rw [RingEquiv.apply_symm_apply]
  exact (congrArg (fun a : Γ(ToricGeometry.splitTorus k n, ⊤) =>
    (ToricGeometry.splitTorus k n).germToFunctionField ⊤ a) hconst.symm).trans
    (openImmersionFunctionFieldEquiv_germ j ⊤
      (BaseSections.scalarMap k («Σ».fanScheme k) ⊤ c)).symm

/-- The actual Laurent embedding is an algebra map over the true base. -/
def torusRationalAlgHom : AddMonoidAlgebra k (Lattice n) →ₐ[k]
    («Σ».fanScheme k).functionField where
  __ := «Σ».torusRationalMap k
  commutes' := «Σ».rationalScalar_eq_algebraMap k

theorem torusRationalAlgHom_injective : Function.Injective («Σ».torusRationalAlgHom k) :=
  «Σ».torusRationalMap_injective k

/-- Base-linear Laurent evaluation on the allowed exponent submodule. -/
def fanCharacterValue (a : Lattice n→ℤ) :
    characterModule k («Σ».fanIntegralExponents a) →ₗ[k] («Σ».fanScheme k).functionField :=
  («Σ».torusRationalAlgHom k).toLinearMap.comp
    (characterModule k («Σ».fanIntegralExponents a)).subtype

theorem fanCharacterValue_injective (a : Lattice n→ℤ) :
    Function.Injective («Σ».fanCharacterValue k a) :=
  («Σ».torusRationalMap_injective k).comp Subtype.val_injective

theorem fanCartier_globalSectionValue_range (hpure : «Σ».IsPure) (a : Lattice n→ℤ) :
    ((«Σ».fanCartierData k hpure a).globalSectionValue k).range =
      («Σ».fanCharacterValue k a).range := by
  apply SetLike.coe_injective
  change Set.range ((«Σ».fanCartierData k hpure a).sectionValue ⊤) = _
  rw [«Σ».fanCartier_globalRange]
  ext r
  constructor
  · rintro ⟨f,hf,rfl⟩
    exact ⟨⟨f,hf⟩,rfl⟩
  · rintro ⟨f,rfl⟩
    exact ⟨f.val,f.property,rfl⟩

/-- The actual global-section vector space is canonically identified by
its rational values with the literal finite-support character module. -/
def fanCartierSectionCoordinates (hpure : «Σ».IsPure) (a : Lattice n→ℤ) :
    Γ((«Σ».fanCartierData k hpure a).sheaf,⊤) ≃ₗ[k]
      characterModule k («Σ».fanIntegralExponents a) :=
  (LinearEquiv.ofInjective ((«Σ».fanCartierData k hpure a).globalSectionValue k)
    ((«Σ».fanCartierData k hpure a).globalSectionValue_injective k)).trans
    ((LinearEquiv.ofEq _ _ («Σ».fanCartier_globalSectionValue_range k hpure a)).trans
      (LinearEquiv.ofInjective («Σ».fanCharacterValue k a)
        («Σ».fanCharacterValue_injective k a)).symm)

theorem fanCartierSectionCoordinates_value (hpure : «Σ».IsPure) (a : Lattice n→ℤ)
    (s : Γ((«Σ».fanCartierData k hpure a).sheaf,⊤)) :
    «Σ».torusRationalMap k ((«Σ».fanCartierSectionCoordinates k hpure a s).val) =
      («Σ».fanCartierData k hpure a).globalSectionValue k s := by
  change «Σ».fanCharacterValue k a («Σ».fanCartierSectionCoordinates k hpure a s)=_
  simp only [fanCartierSectionCoordinates,LinearEquiv.trans_apply,
    LinearEquiv.ofInjective_symm_apply,LinearEquiv.coe_ofEq_apply,
    LinearEquiv.ofInjective_apply]

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.rationalScalar_eq_algebraMap
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanCartierSectionCoordinates
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanCartierSectionCoordinates_value
end
-- END PaperVerification.ToricFanSectionCoordinates
end

section
-- BEGIN PaperVerification.ToricCartierAmpleDescent



/-!
# Intrinsic ampleness is independent of Cartier presentation

The proof transports the actual positive-power sections and proves equality
of their genuine nonvanishing open subsets. Thus the intrinsic affine-open
criterion is preserved by the established equality of fractional sheaves.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace PaperVerification.ToricSchemes.RationalCartierCocycle

variable {X : Scheme.{u}} [IsIntegral X] (C D : RationalCartierCocycle X)

theorem mem_nonvanishingOpen_iff_rational (i : C.index) (s : Γ(C.sheaf,⊤))
    (x : X) (hxi : x∈C.openSet i) :
    x∈C.nonvanishingOpen s ↔
      C.toCartierData.sectionValue ⊤ s≠0 ∧
        (C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ s ∈
          regularAtSubring X x := by
  rw [C.mem_nonvanishingOpen_iff i s x hxi,
    ← X.mem_basicOpen (C.localCoefficient i s) x hxi,
    C.mem_localNonvanishing_iff i s x hxi]

/-- The actual section iso preserving fractional values preserves the
ordinary nonvanishing open, including at zeros of the section. -/
theorem nonvanishingOpen_sameGenerator
    (hCD : C.GeneratorRatioRegular D) (hDC : D.GeneratorRatioRegular C)
    (s : Γ(C.sheaf,⊤)) :
    D.nonvanishingOpen (C.sameGeneratorSheafLinearEquiv D hCD hDC ⊤ s) =
      C.nonvanishingOpen s := by
  ext x
  change x∈D.nonvanishingOpen (C.sameGeneratorSheafLinearEquiv D hCD hDC ⊤ s) ↔
    x∈C.nonvanishingOpen s
  obtain ⟨i,hxi⟩ := C.covers x
  obtain ⟨j,hxj⟩ := D.covers x
  rw [D.mem_nonvanishingOpen_iff_rational j _ x hxj,
    C.mem_nonvanishingOpen_iff_rational i s x hxi]
  have hv : D.toCartierData.sectionValue ⊤
      (C.sameGeneratorSheafLinearEquiv D hCD hDC ⊤ s) =
        C.toCartierData.sectionValue ⊤ s := rfl
  rw [hv]
  constructor
  · rintro ⟨hr,h⟩
    refine ⟨hr,?_⟩
    have hh := (regularAtSubring X x).mul_mem (hCD i j x hxi hxj) h
    have he : ((C.generator i : X.functionField)/(D.generator j : X.functionField)) *
        ((D.generator j : X.functionField)/C.toCartierData.sectionValue ⊤ s) =
        (C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ s := by
      field_simp [Units.ne_zero,hr]
    simpa only [he] using hh
  · rintro ⟨hr,h⟩
    refine ⟨hr,?_⟩
    have hh := (regularAtSubring X x).mul_mem (hDC j i x hxj hxi) h
    have he : ((D.generator j : X.functionField)/(C.generator i : X.functionField)) *
        ((C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ s) =
        (D.generator j : X.functionField)/C.toCartierData.sectionValue ⊤ s := by
      field_simp [Units.ne_zero,hr]
    simpa only [he] using hh

theorem isAmple_of_generatorRatios
    (hCD : C.GeneratorRatioRegular D) (hDC : D.GeneratorRatioRegular C)
    (hC : C.IsAmple) : D.IsAmple := by
  refine ⟨hC.1,?_⟩
  intro x
  obtain ⟨n,hn,s,hx,ha⟩ := hC.2 x
  let hpowCD := GeneratorRatioRegular.pow C D hCD n
  let hpowDC := GeneratorRatioRegular.pow D C hDC n
  let t := (C.pow n).sameGeneratorSheafLinearEquiv (D.pow n) hpowCD hpowDC ⊤ s
  have hopen : (D.pow n).nonvanishingOpen t=(C.pow n).nonvanishingOpen s :=
    (C.pow n).nonvanishingOpen_sameGenerator (D.pow n) hpowCD hpowDC s
  exact ⟨n,hn,t,by simpa only [hopen] using hx,by simpa only [hopen] using ha⟩

theorem isAmple_iff_of_generatorRatios
    (hCD : C.GeneratorRatioRegular D) (hDC : D.GeneratorRatioRegular C) :
    C.IsAmple ↔ D.IsAmple :=
  ⟨C.isAmple_of_generatorRatios D hCD hDC,D.isAmple_of_generatorRatios C hDC hCD⟩

end PaperVerification.ToricSchemes.RationalCartierCocycle

namespace PaperVerification.ToricSchemes.CartierData

variable {X : Scheme.{u}} [IsIntegral X] (D E : CartierData X)

theorem isAmple_iff_of_equivalent (h : D.Equivalent E) : D.IsAmple ↔ E.IsAmple :=
  D.localCocycle.isAmple_iff_of_generatorRatios E.localCocycle
    (D.localCocycle_generatorRatios E h)
    (E.localCocycle_generatorRatios D (D.equivalent_symm E h))

end PaperVerification.ToricSchemes.CartierData

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open PaperVerification.ToricSchemes

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

/-- The recovered integral invariant divisor preserves the original
intrinsic ampleness condition on the actual scheme. -/
theorem fanCartier_isAmple_iff (hpure : «Σ».IsPure)
    (D : CartierData («Σ».fanScheme k)) :
    («Σ».fanCartierData k hpure («Σ».cartierCoefficients k hpure D)).IsAmple ↔ D.IsAmple := by
  rw [← («Σ».normalizedCartier k D).isAmple_iff_of_equivalent _
    («Σ».normalizedCartier_equivalent_fanCartier k hpure D)]
  exact «Σ».normalizedCartier_isAmple_iff k D

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricSchemes.CartierData.isAmple_iff_of_equivalent
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanCartier_isAmple_iff
end
-- END PaperVerification.ToricCartierAmpleDescent
end

section
-- BEGIN PaperVerification.ToricFanCartierArithmetic



/-! # Addition of integral coefficients and actual Cartier sheaf products -/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical Pointwise

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

theorem cartierLatticePoint_add_coefficients (a b : Lattice n→ℤ) (s : «Σ».fullCones) :
    «Σ».cartierLatticePoint (a+b) s=«Σ».cartierLatticePoint a s+«Σ».cartierLatticePoint b s := by
  symm
  apply «Σ».eq_cartierLatticePoint_of_pairings
  intro v hv
  rw [integerPairing_add,«Σ».cartierLatticePoint_pairing a s v hv,
    «Σ».cartierLatticePoint_pairing b s v hv]
  simp only [Pi.add_apply]
  omega

theorem fanIntegralExponents_add_subset (a b : Lattice n→ℤ) :
    «Σ».fanIntegralExponents a+«Σ».fanIntegralExponents b ⊆ «Σ».fanIntegralExponents (a+b) := by
  rintro m ⟨p,hp,q,hq,rfl⟩ v hv
  have hpv := hp v hv
  have hqv := hq v hv
  change -((a v+b v : ℤ):ℝ) ≤
    (dotProductEquiv ℝ (Fin n) (embed n v)) (embed n (p+q))
  rw [map_add,LinearMap.map_add,Int.cast_add]
  linarith

theorem fanCartierCocycle_mul_ratios (hpure : «Σ».IsPure) (a b : Lattice n→ℤ) :
    ((«Σ».fanCartierCocycle k hpure a).mul («Σ».fanCartierCocycle k hpure b)).GeneratorRatioRegular
      («Σ».fanCartierCocycle k hpure (a+b)) ∧
    («Σ».fanCartierCocycle k hpure (a+b)).GeneratorRatioRegular
      ((«Σ».fanCartierCocycle k hpure a).mul («Σ».fanCartierCocycle k hpure b)) := by
  constructor
  · intro i j x hxi hxj
    have ha := («Σ».fanCartierCocycle k hpure a).transition i.1 j x hxi.1 hxj
    have hb := («Σ».fanCartierCocycle k hpure b).transition i.2 j x hxi.2 hxj
    have h := (regularAtSubring («Σ».fanScheme k) x).mul_mem ha hb
    simpa only [RationalCartierCocycle.mul,fanCartierCocycle,Units.val_mul,
      «Σ».cartierLatticePoint_add_coefficients,«Σ».rationalCharacter_add k,
      div_mul_div_comm] using h
  · intro i j x hxi hxj
    have ha := («Σ».fanCartierCocycle k hpure a).transition i j.1 x hxi hxj.1
    have hb := («Σ».fanCartierCocycle k hpure b).transition i j.2 x hxi hxj.2
    have h := (regularAtSubring («Σ».fanScheme k) x).mul_mem ha hb
    simpa only [RationalCartierCocycle.mul,fanCartierCocycle,Units.val_mul,
      «Σ».cartierLatticePoint_add_coefficients,«Σ».rationalCharacter_add k,
      div_mul_div_comm] using h

/-- The true product Cartier sheaf is the sheaf of the sum of integral
support coefficients, with the same actual rational-function embedding. -/
theorem fanCartierData_add_equivalent (hpure : «Σ».IsPure) (a b : Lattice n→ℤ) :
    ((«Σ».fanCartierData k hpure a).add («Σ».fanCartierData k hpure b)).Equivalent
      («Σ».fanCartierData k hpure (a+b)) := by
  let C := «Σ».fanCartierCocycle k hpure a
  let D := «Σ».fanCartierCocycle k hpure b
  have h := (C.mul D).equivalent_of_generatorRatios
    («Σ».fanCartierCocycle k hpure (a+b))
    («Σ».fanCartierCocycle_mul_ratios k hpure a b).1
    («Σ».fanCartierCocycle_mul_ratios k hpure a b).2
  exact (C.toCartierData.add D.toCartierData).equivalent_trans
    (C.mul D).toCartierData («Σ».fanCartierData k hpure (a+b))
    (C.toCartierData_add_equivalent D) h

open scoped BaseSections

theorem fanCartierSum_globalSectionValue_range (hpure : «Σ».IsPure) (a b : Lattice n→ℤ) :
    (((«Σ».fanCartierData k hpure a).add («Σ».fanCartierData k hpure b)).globalSectionValue k).range =
      («Σ».fanCharacterValue k (a+b)).range := by
  let F := («Σ».fanCartierData k hpure a).add («Σ».fanCartierData k hpure b)
  have h := F.equivalent_sectionValueRange («Σ».fanCartierData k hpure (a+b))
    («Σ».fanCartierData_add_equivalent k hpure a b) ⊤
  have he : (F.globalSectionValue k).range =
      ((«Σ».fanCartierData k hpure (a+b)).globalSectionValue k).range := by
    apply SetLike.coe_injective
    change Set.range (F.sectionValue ⊤) =
      Set.range ((«Σ».fanCartierData k hpure (a+b)).sectionValue ⊤)
    exact congrArg (fun P : Submodule Γ(«Σ».fanScheme k, ⊤) («Σ».fanScheme k).functionField =>
      (P : Set («Σ».fanScheme k).functionField)) h
  exact he.trans («Σ».fanCartier_globalSectionValue_range k hpure (a+b))

/-- Character coordinates on the actual product sheaf, without replacing
its tensor/product construction by a formal support-set definition. -/
def fanCartierSumSectionCoordinates (hpure : «Σ».IsPure) (a b : Lattice n→ℤ) :
    Γ(((«Σ».fanCartierData k hpure a).add («Σ».fanCartierData k hpure b)).sheaf,⊤) ≃ₗ[k]
      characterModule k («Σ».fanIntegralExponents (a+b)) :=
  (LinearEquiv.ofInjective
    (((«Σ».fanCartierData k hpure a).add («Σ».fanCartierData k hpure b)).globalSectionValue k)
    (((«Σ».fanCartierData k hpure a).add («Σ».fanCartierData k hpure b)).globalSectionValue_injective k)).trans
    ((LinearEquiv.ofEq _ _ («Σ».fanCartierSum_globalSectionValue_range k hpure a b)).trans
      (LinearEquiv.ofInjective («Σ».fanCharacterValue k (a+b))
        («Σ».fanCharacterValue_injective k (a+b))).symm)

theorem fanCartierSumSectionCoordinates_value (hpure : «Σ».IsPure) (a b : Lattice n→ℤ)
    (s : Γ(((«Σ».fanCartierData k hpure a).add («Σ».fanCartierData k hpure b)).sheaf,⊤)) :
    «Σ».torusRationalMap k («Σ».fanCartierSumSectionCoordinates k hpure a b s).val =
      ((«Σ».fanCartierData k hpure a).add («Σ».fanCartierData k hpure b)).globalSectionValue k s := by
  change «Σ».fanCharacterValue k (a+b) («Σ».fanCartierSumSectionCoordinates k hpure a b s)=_
  simp only [fanCartierSumSectionCoordinates,LinearEquiv.trans_apply,
    LinearEquiv.ofInjective_symm_apply,LinearEquiv.coe_ofEq_apply,
    LinearEquiv.ofInjective_apply]

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanCartierData_add_equivalent
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanCartierSumSectionCoordinates
end
-- END PaperVerification.ToricFanCartierArithmetic
end

section
-- BEGIN PaperVerification.ToricFanSectionMultiplication



/-!
# Actual section multiplication is the character multiplication map

Both sides are maps between the actual base-field tensor products. The
identity is proved after embedding in the scheme's genuine function
field, where multiplication is literal multiplication. Its surjectivity
is consequently equivalent to the complete lattice-point sum assertion.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical Pointwise TensorProduct BaseSections

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

theorem fanSectionMultiplication_coordinates (hpure : «Σ».IsPure) (a b : Lattice n→ℤ) :
    («Σ».fanCartierSumSectionCoordinates k hpure a b).toLinearMap.comp
      ((«Σ».fanCartierData k hpure a).sectionMultiplicationOver k
        («Σ».fanCartierData k hpure b)) =
      (characterMultiplication k («Σ».fanIntegralExponents a) («Σ».fanIntegralExponents b)
        («Σ».fanIntegralExponents (a+b)) («Σ».fanIntegralExponents_add_subset a b)).comp
          (TensorProduct.map
            («Σ».fanCartierSectionCoordinates k hpure a).toLinearMap
            («Σ».fanCartierSectionCoordinates k hpure b).toLinearMap) := by
  apply TensorProduct.ext'
  intro s t
  apply Subtype.ext
  apply «Σ».torusRationalMap_injective k
  change «Σ».torusRationalMap k
      («Σ».fanCartierSumSectionCoordinates k hpure a b
        ((«Σ».fanCartierData k hpure a).sectionMultiplicationOver k
          («Σ».fanCartierData k hpure b) (s ⊗ₜ[k] t))).val =
    «Σ».torusRationalMap k
      ((«Σ».fanCartierSectionCoordinates k hpure a s).val *
        («Σ».fanCartierSectionCoordinates k hpure b t).val)
  rw [«Σ».fanCartierSumSectionCoordinates_value,
    CartierData.sectionMultiplicationOver_value_tmul,map_mul,
    «Σ».fanCartierSectionCoordinates_value,«Σ».fanCartierSectionCoordinates_value]

theorem fanSectionMultiplication_surjective_iff_characters (hpure : «Σ».IsPure)
    (a b : Lattice n→ℤ) :
    Function.Surjective ((«Σ».fanCartierData k hpure a).sectionMultiplicationOver k
      («Σ».fanCartierData k hpure b)) ↔
    Function.Surjective
      (characterMultiplication k («Σ».fanIntegralExponents a) («Σ».fanIntegralExponents b)
        («Σ».fanIntegralExponents (a+b)) («Σ».fanIntegralExponents_add_subset a b)) := by
  let ea := «Σ».fanCartierSectionCoordinates k hpure a
  let eb := «Σ».fanCartierSectionCoordinates k hpure b
  let ec := «Σ».fanCartierSumSectionCoordinates k hpure a b
  let et := TensorProduct.congr ea eb
  let μ := («Σ».fanCartierData k hpure a).sectionMultiplicationOver k
    («Σ».fanCartierData k hpure b)
  let ν := characterMultiplication k («Σ».fanIntegralExponents a) («Σ».fanIntegralExponents b)
    («Σ».fanIntegralExponents (a+b)) («Σ».fanIntegralExponents_add_subset a b)
  have hcomp (x) : ec (μ x)=ν (et x) :=
    congrArg (fun f=>f x) («Σ».fanSectionMultiplication_coordinates k hpure a b)
  constructor
  · intro hμ y
    obtain ⟨s,hs⟩ := ec.surjective y
    obtain ⟨x,hx⟩ := hμ s
    exact ⟨et x,(hcomp x).symm.trans (by rw [hx,hs])⟩
  · intro hν s
    obtain ⟨y,hy⟩ := hν (ec s)
    obtain ⟨x,hx⟩ := et.surjective y
    refine ⟨x,ec.injective ?_⟩
    rw [hcomp x,hx,hy]

/-- The exact scheme-section dictionary required for multiplication:
surjectivity of the actual global-section tensor map is equivalent to
decomposition of every integral point in the whole sum-support polytope. -/
theorem fanSectionMultiplication_surjective_iff (hpure : «Σ».IsPure) (a b : Lattice n→ℤ) :
    Function.Surjective ((«Σ».fanCartierData k hpure a).sectionMultiplicationOver k
      («Σ».fanCartierData k hpure b)) ↔
      «Σ».fanIntegralExponents (a+b) =
        «Σ».fanIntegralExponents a + «Σ».fanIntegralExponents b := by
  rw [«Σ».fanSectionMultiplication_surjective_iff_characters k hpure a b,
    characterMultiplication_surjective_iff]

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanSectionMultiplication_coordinates
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanSectionMultiplication_surjective_iff
end
-- END PaperVerification.ToricFanSectionMultiplication
end

section
-- BEGIN PaperVerification.ToricSectionMultiplicationTransport



/-!
# Actual section multiplication under Cartier equivalence

Presentation equality and an explicit principal translation induce
isomorphisms of genuine section spaces. Their compatibility with the
actual multiplication map is proved through the injective rational
values, so surjectivity transports without a chosen character basis.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct

namespace PaperVerification.ToricSchemes.CartierData

open scoped BaseSections

variable (k : Type u) [CommRing k] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of k))] (D D' E E' : CartierData X)

def equivalentGlobalSections (h : D.Equivalent D') :
    Γ(D.sheaf,⊤) ≃ₗ[k] Γ(D'.sheaf,⊤) := by
  let e : Γ(D.sheaf,⊤) ≃ₗ[Γ(X,⊤)] Γ(D'.sheaf,⊤) :=
    (((PresheafOfModules.evaluation X.ringCatSheaf.obj (op ⊤)).mapIso
      ((SheafOfModules.forget _).mapIso h.choose)).toLinearEquiv)
  exact e.restrictScalars k

theorem equivalentGlobalSections_value (h : D.Equivalent D') (s : Γ(D.sheaf,⊤)) :
    D'.globalSectionValue k (D.equivalentGlobalSections k D' h s)=D.globalSectionValue k s := by
  have he := congrArg (fun f=>f.app ⊤ s) h.choose_spec
  change rationalValue X ⊤ (D'.inclusion.app ⊤ (h.choose.hom.app ⊤ s)) =
    rationalValue X ⊤ (D.inclusion.app ⊤ s)
  exact congrArg (rationalValue X ⊤) he

theorem sectionMultiplicationOver_equivalent (hD : D.Equivalent D')
    (hE : E.Equivalent E') :
    ((D.add E).equivalentGlobalSections k (D'.add E')
      (D.add_equivalent_add D' E E' hD hE)).toLinearMap.comp
        (D.sectionMultiplicationOver k E) =
      (D'.sectionMultiplicationOver k E').comp
        (TensorProduct.map (D.equivalentGlobalSections k D' hD).toLinearMap
          (E.equivalentGlobalSections k E' hE).toLinearMap) := by
  apply TensorProduct.ext'
  intro s t
  apply (D'.add E').globalSectionValue_injective k
  change (D'.add E').globalSectionValue k
      ((D.add E).equivalentGlobalSections k (D'.add E') _
        (D.sectionMultiplicationOver k E (s⊗ₜ[k]t))) =
    (D'.add E').globalSectionValue k
      (D'.sectionMultiplicationOver k E'
        (D.equivalentGlobalSections k D' hD s ⊗ₜ[k]
          E.equivalentGlobalSections k E' hE t))
  rw [equivalentGlobalSections_value,sectionMultiplicationOver_value_tmul,
    sectionMultiplicationOver_value_tmul,equivalentGlobalSections_value,
    equivalentGlobalSections_value]

theorem sectionMultiplicationOver_surjective_iff_equivalent
    (hD : D.Equivalent D') (hE : E.Equivalent E') :
    Function.Surjective (D.sectionMultiplicationOver k E) ↔
      Function.Surjective (D'.sectionMultiplicationOver k E') := by
  let es := TensorProduct.congr (D.equivalentGlobalSections k D' hD)
    (E.equivalentGlobalSections k E' hE)
  let et := (D.add E).equivalentGlobalSections k (D'.add E')
    (D.add_equivalent_add D' E E' hD hE)
  have he (z) : et (D.sectionMultiplicationOver k E z)=
      D'.sectionMultiplicationOver k E' (es z) :=
    congrArg (fun f=>f z) (D.sectionMultiplicationOver_equivalent k D' E E' hD hE)
  constructor
  · intro h y
    obtain ⟨t,ht⟩ := et.surjective y
    obtain ⟨z,hz⟩ := h t
    exact ⟨es z,(he z).symm.trans (by rw [hz,ht])⟩
  · intro h t
    obtain ⟨y,hy⟩ := h (et t)
    obtain ⟨z,hz⟩ := es.surjective y
    refine ⟨z,et.injective ?_⟩
    rw [he,hz,hy]

theorem scale_globalSectionValue (q : X.functionFieldˣ) (s : Γ(D.sheaf,⊤)) :
    (D.scale q).globalSectionValue k s = (q : X.functionField) * D.globalSectionValue k s :=
  D.scale_sectionValue q ⊤ s

theorem sectionMultiplicationOver_scale (q r : X.functionFieldˣ) :
    (((D.scale q).add (E.scale r)).equivalentGlobalSections k ((D.add E).scale (q*r))
      (D.scale_add_equivalent q E r)).toLinearMap.comp
        ((D.scale q).sectionMultiplicationOver k (E.scale r)) =
      D.sectionMultiplicationOver k E := by
  apply TensorProduct.ext'
  intro s t
  apply (D.add E).globalSectionValue_injective k
  apply mul_left_cancel₀ (Units.ne_zero (q*r))
  have hv := ((D.scale q).add (E.scale r)).equivalentGlobalSections_value k
    ((D.add E).scale (q*r)) (D.scale_add_equivalent q E r)
    ((D.scale q).sectionMultiplicationOver k (E.scale r) (s⊗ₜ[k]t))
  change ((q*r : X.functionFieldˣ):X.functionField) *
      (D.add E).globalSectionValue k
        (((D.scale q).add (E.scale r)).equivalentGlobalSections k
          ((D.add E).scale (q*r)) _
          ((D.scale q).sectionMultiplicationOver k (E.scale r) (s⊗ₜ[k]t))) = _
  calc
    _ = ((D.add E).scale (q*r)).globalSectionValue k
        (((D.scale q).add (E.scale r)).equivalentGlobalSections k
          ((D.add E).scale (q*r)) _
          ((D.scale q).sectionMultiplicationOver k (E.scale r) (s⊗ₜ[k]t))) :=
      ((D.add E).scale_globalSectionValue k (q*r) _).symm
    _ = ((D.scale q).add (E.scale r)).globalSectionValue k
        ((D.scale q).sectionMultiplicationOver k (E.scale r) (s⊗ₜ[k]t)) := hv
    _ = (D.scale q).globalSectionValue k s * (E.scale r).globalSectionValue k t :=
      (D.scale q).sectionMultiplicationOver_value_tmul k (E.scale r) s t
    _ = ((q : X.functionField) * D.globalSectionValue k s) *
        ((r : X.functionField) * E.globalSectionValue k t) :=
      congrArg₂ (fun a b : X.functionField => a*b)
        (D.scale_globalSectionValue k q s) (E.scale_globalSectionValue k r t)
    _ = ((q*r : X.functionFieldˣ) : X.functionField) *
        (D.globalSectionValue k s * E.globalSectionValue k t) := by
      simp only [Units.val_mul]
      ring
    _ = _ := congrArg (fun a : X.functionField =>
      ((q*r : X.functionFieldˣ) : X.functionField) * a)
        (D.sectionMultiplicationOver_value_tmul k E s t).symm

/-- An explicit rational principal translation does not affect
surjectivity of the genuine section multiplication map. -/
theorem sectionMultiplicationOver_surjective_iff_scale (q r : X.functionFieldˣ) :
    Function.Surjective ((D.scale q).sectionMultiplicationOver k (E.scale r)) ↔
      Function.Surjective (D.sectionMultiplicationOver k E) := by
  let e := ((D.scale q).add (E.scale r)).equivalentGlobalSections k
    ((D.add E).scale (q*r)) (D.scale_add_equivalent q E r)
  have he (z) : e ((D.scale q).sectionMultiplicationOver k (E.scale r) z)=
      D.sectionMultiplicationOver k E z :=
    congrArg (fun f=>f z) (D.sectionMultiplicationOver_scale k E q r)
  constructor
  · intro h t
    obtain ⟨s,hs⟩ := e.surjective t
    obtain ⟨z,hz⟩ := h s
    exact ⟨z,(he z).symm.trans (by rw [hz,hs])⟩
  · intro h s
    obtain ⟨z,hz⟩ := h (e s)
    exact ⟨z,e.injective ((he z).trans hz)⟩

end PaperVerification.ToricSchemes.CartierData

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open PaperVerification.ToricSchemes
open scoped Pointwise BaseSections

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

/-- The full section-multiplication dictionary for arbitrary Cartier
divisors on the actual fan scheme, with no invariant presentation premise. -/
theorem arbitraryCartier_sectionMultiplication_surjective_iff (hpure : «Σ».IsPure)
    (D E : CartierData («Σ».fanScheme k)) :
    Function.Surjective (D.sectionMultiplicationOver k E) ↔
      «Σ».fanIntegralExponents («Σ».cartierCoefficients k hpure D + «Σ».cartierCoefficients k hpure E) =
        «Σ».fanIntegralExponents («Σ».cartierCoefficients k hpure D) +
          «Σ».fanIntegralExponents («Σ».cartierCoefficients k hpure E) := by
  letI : IsOpenImmersion («Σ».splitTorusOpenMap k) :=
    ToricGeometry.SmoothCompleteFan.splitTorusOpenMap_isOpenImmersion k «Σ»
  letI : IsOpenImmersion
      (show ToricSchemes.splitTorus k (Fin n → ℤ) ⟶ «Σ».fanScheme k from
        «Σ».splitTorusOpenMap k) := «Σ».splitTorusOpenMap_isOpenImmersion k
  have hscale : Function.Surjective
      ((«Σ».normalizedCartier k D).sectionMultiplicationOver k («Σ».normalizedCartier k E)) ↔
        Function.Surjective (D.sectionMultiplicationOver k E) :=
    D.sectionMultiplicationOver_surjective_iff_scale k E
      (torusCartierGenerator k n («Σ».fanScheme k) («Σ».splitTorusOpenMap k) D)⁻¹
      (torusCartierGenerator k n («Σ».fanScheme k) («Σ».splitTorusOpenMap k) E)⁻¹
  rw [← hscale]
  rw [(«Σ».normalizedCartier k D).sectionMultiplicationOver_surjective_iff_equivalent k
    («Σ».fanCartierData k hpure («Σ».cartierCoefficients k hpure D))
    («Σ».normalizedCartier k E)
    («Σ».fanCartierData k hpure («Σ».cartierCoefficients k hpure E))
    («Σ».normalizedCartier_equivalent_fanCartier k hpure D)
    («Σ».normalizedCartier_equivalent_fanCartier k hpure E)]
  exact «Σ».fanSectionMultiplication_surjective_iff k hpure _ _

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricSchemes.CartierData.sectionMultiplicationOver_surjective_iff_scale
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.arbitraryCartier_sectionMultiplication_surjective_iff
end
-- END PaperVerification.ToricSectionMultiplicationTransport
end

section
-- BEGIN PaperVerification.ToricCartierTensor



/-!
# The genuine tensor sheaf of two fractional Cartier sheaves

The tensor sheaf is the sheafification of the ordinary sectionwise
module tensor product. Multiplication of rational functions defines a
natural map to the fractional sheaf with multiplied local generators.
On a common trivializing open, this map is the usual rank-one tensor
isomorphism. Consequently the presheaf map is locally bijective, so its
sheafification is an actual sheaf isomorphism. No tensor-product or
section-space identification is inserted into the Cartier definitions.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open MonoidalCategory
open scoped TensorProduct

variable {X : Scheme.{u}}

/-- The ordinary sectionwise tensor presheaf over the structure sheaf. -/
def tensorPresheaf (F G : X.Modules) : PresheafOfModules X.ringCatSheaf.obj :=
  PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) F.val G.val

/-- The usual tensor product of sheaves of modules, defined by the
standard sheafification construction. -/
def tensorSheaf (F G : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (tensorPresheaf F G)

/-- The canonical map of the sectionwise tensor presheaf into its sheaf. -/
def tensorSheafUnit (F G : X.Modules) :
    tensorPresheaf F G ⟶ (tensorSheaf F G).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app _

/-- Actual sheaf isomorphisms induce the usual tensor-sheaf isomorphism. -/
def tensorSheafIso {F F' G G' : X.Modules} (e : F ≅ F') (f : G ≅ G') :
    tensorSheaf F G ≅ tensorSheaf F' G' := by
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing X.presheaf))
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (MonoidalCategory.tensorIso ((SheafOfModules.forget _).mapIso e)
      ((SheafOfModules.forget _).mapIso f))

variable [IsIntegral X]

namespace RationalCartierCocycle

variable (C D : RationalCartierCocycle X)

/-- In genuine local frames, rational multiplication is ordinary
multiplication of the two regular coefficients. -/
theorem localCoordinates_sectionProduct (i : C.index) (j : D.index)
    (U : X.Opens) (hU : U≤C.openSet i⊓D.openSet j)
    (s : Γ(C.sheaf,U)) (t : Γ(D.sheaf,U)) :
    (C.mul D).localCoordinates (i,j) U hU (C.sectionProduct D U s t) =
      C.localCoordinates i U (hU.trans inf_le_left) s *
        D.localCoordinates j U (hU.trans inf_le_right) t := by
  classical
  by_cases hnonempty : Nonempty U
  · letI := hnonempty
    apply X.germToFunctionField_injective U
    calc
      X.germToFunctionField U
          ((C.mul D).localCoordinates (i,j) U hU (C.sectionProduct D U s t)) =
          rationalValue X U (C.sectionProduct D U s t).val /
            ((C.mul D).generator (i,j) : X.functionField) :=
        (C.mul D).localCoordinates_value (i,j) U hU (C.sectionProduct D U s t)
      _ = (rationalValue X U s.val / (C.generator i : X.functionField)) *
          (rationalValue X U t.val / (D.generator j : X.functionField)) := by
        change rationalValue X U (rationalMul U s.val t.val) /
          ((C.generator i : X.functionField)*(D.generator j : X.functionField)) = _
        rw [rationalValue_mul, div_mul_div_comm]
      _ = X.germToFunctionField U
          (C.localCoordinates i U (hU.trans inf_le_left) s) *
          X.germToFunctionField U
            (D.localCoordinates j U (hU.trans inf_le_right) t) :=
        congrArg₂ (· * ·)
          (C.localCoordinates_value i U (hU.trans inf_le_left) s).symm
          (D.localCoordinates_value j U (hU.trans inf_le_right) t).symm
      _ = X.germToFunctionField U
          (C.localCoordinates i U (hU.trans inf_le_left) s *
            D.localCoordinates j U (hU.trans inf_le_right) t) :=
        (map_mul (X.germToFunctionField U).hom _ _).symm
  · have hbot : U=⊥ := by
      apply le_antisymm
      · intro x hx
        exact False.elim (hnonempty ⟨⟨x,hx⟩⟩)
      · exact bot_le
    letI := regularSections_subsingleton_of_empty X U hbot
    exact Subsingleton.elim _ _

/-- The explicit rank-one tensor isomorphism on a common trivializing
open, obtained from the independently constructed local frames. -/
def localTensorEquiv (i : C.index) (j : D.index)
    (U : X.Opens) (hU : U≤C.openSet i⊓D.openSet j) :
    Γ(C.sheaf,U) ⊗[Γ(X,U)] Γ(D.sheaf,U) ≃ₗ[Γ(X,U)] Γ((C.mul D).sheaf,U) :=
  ((TensorProduct.congr
    (C.localCoordinates i U (hU.trans inf_le_left))
    (D.localCoordinates j U (hU.trans inf_le_right))).trans
      (TensorProduct.lid Γ(X,U) Γ(X,U))).trans
        ((C.mul D).localCoordinates (i,j) U hU).symm

theorem sectionMultiplication_eq_localTensorEquiv (i : C.index) (j : D.index)
    (U : X.Opens) (hU : U≤C.openSet i⊓D.openSet j) :
    C.sectionMultiplication D U = (C.localTensorEquiv D i j U hU).toLinearMap := by
  apply TensorProduct.ext'
  intro s t
  apply ((C.mul D).localCoordinates (i,j) U hU).injective
  simp only [sectionMultiplication_tmul, localCoordinates_sectionProduct,
    localTensorEquiv, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, TensorProduct.lid_tmul,
    LinearEquiv.apply_symm_apply, smul_eq_mul]

theorem sectionMultiplication_bijective_on (i : C.index) (j : D.index)
    (U : X.Opens) (hU : U≤C.openSet i⊓D.openSet j) :
    Function.Bijective (C.sectionMultiplication D U) := by
  rw [C.sectionMultiplication_eq_localTensorEquiv D i j U hU]
  exact (C.localTensorEquiv D i j U hU).bijective

/-- Rational multiplication is a morphism of the actual sectionwise
tensor presheaf, since it commutes with actual restrictions. -/
def tensorPresheafMultiplication :
    tensorPresheaf C.sheaf D.sheaf ⟶ (C.mul D).sheaf.val :=
  PresheafOfModulesOfCommRing.homMk (R := X.presheaf)
    (M₁ := tensorPresheaf C.sheaf D.sheaf) (M₂ := (C.mul D).sheaf.val)
    (fun U => ModuleCat.ofHom
      (X := (tensorPresheaf C.sheaf D.sheaf).obj U)
      (Y := ((C.mul D).sheaf.val).obj U)
      (C.sectionMultiplication D U.unop))
    (by
      intro U V f
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro s t
      change C.sectionMultiplication D V.unop
          ((tensorPresheaf C.sheaf D.sheaf).map f (s ⊗ₜ[Γ(X,U.unop)] t)) =
        (C.mul D).sheaf.presheaf.map f (C.sectionMultiplication D U.unop
          (s ⊗ₜ[Γ(X,U.unop)] t))
      have hm : (tensorPresheaf C.sheaf D.sheaf).map f
          (s ⊗ₜ[Γ(X,U.unop)] t) =
          C.sheaf.val.map f s ⊗ₜ[Γ(X,V.unop)] D.sheaf.val.map f t :=
        PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul
          (R := X.presheaf) (M₁ := C.sheaf.val) (M₂ := D.sheaf.val) f s t
      exact (congrArg (C.sectionMultiplication D V.unop) hm).trans
        (C.sectionProduct_restrict D f.unop s t).symm)

@[simp] theorem tensorPresheafMultiplication_app (U : X.Opens)
    (z : Γ(C.sheaf,U) ⊗[Γ(X,U)] Γ(D.sheaf,U)) :
    (C.tensorPresheafMultiplication D).app (op U) z =
      C.sectionMultiplication D U z := rfl

/-- Local frames prove local injectivity of the presheaf multiplication. -/
instance tensorPresheafMultiplication_locallyInjective :
    CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (C.tensorPresheafMultiplication D)) where
  equalizerSieve_mem {U} s t h := by
    intro x hx
    obtain ⟨i,hi⟩ := C.covers x
    obtain ⟨j,hj⟩ := D.covers x
    let V : X.Opens := U.unop ⊓ (C.openSet i ⊓ D.openSet j)
    let f : V ⟶ U.unop := homOfLE inf_le_left
    refine ⟨V,f,?_,⟨hx,hi,hj⟩⟩
    change (tensorPresheaf C.sheaf D.sheaf).presheaf.map f.op s =
      (tensorPresheaf C.sheaf D.sheaf).presheaf.map f.op t
    apply (C.sectionMultiplication_bijective_on D i j V inf_le_right).injective
    change (C.tensorPresheafMultiplication D).app (op V)
        ((tensorPresheaf C.sheaf D.sheaf).map f.op s) =
      (C.tensorPresheafMultiplication D).app (op V)
        ((tensorPresheaf C.sheaf D.sheaf).map f.op t)
    rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply]
    exact congrArg ((C.mul D).sheaf.presheaf.map f.op) h

/-- Local frames prove local surjectivity of the presheaf multiplication. -/
instance tensorPresheafMultiplication_locallySurjective :
    CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (C.tensorPresheafMultiplication D)) where
  imageSieve_mem {U} s := by
    intro x hx
    obtain ⟨i,hi⟩ := C.covers x
    obtain ⟨j,hj⟩ := D.covers x
    let V : X.Opens := U ⊓ (C.openSet i ⊓ D.openSet j)
    let f : V ⟶ U := homOfLE inf_le_left
    obtain ⟨t,ht⟩ := (C.sectionMultiplication_bijective_on D i j V inf_le_right).surjective
      ((C.mul D).sheaf.presheaf.map f.op s)
    exact ⟨V,f,⟨t,ht⟩,⟨hx,hi,hj⟩⟩

instance tensorPresheafMultiplication_sheafification_isIso :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (C.tensorPresheafMultiplication D)) := by
  have hW := (Opens.grothendieckTopology X).W_of_isLocallyBijective
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
      (C.tensorPresheafMultiplication D))
  change ((Opens.grothendieckTopology X).W.inverseImage
    (PresheafOfModules.toPresheaf X.ringCatSheaf.obj))
      (C.tensorPresheafMultiplication D) at hW
  rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (𝟙 X.ringCatSheaf.obj)] at hW
  exact hW

/-- The genuine sheaf tensor product is canonically isomorphic to the
fractional sheaf obtained by multiplying the actual local equations. -/
def tensorSheafMulIso : tensorSheaf C.sheaf D.sheaf ≅ (C.mul D).sheaf := by
  letI := C.tensorPresheafMultiplication_sheafification_isIso D
  exact asIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (C.tensorPresheafMultiplication D)) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit).app (C.mul D).sheaf

/-- The tensor isomorphism is the sheafification of the original
multiplication map, so its map on pure section tensors is the prescribed
actual rational multiplication. -/
theorem tensorSheafMulIso_unit :
    tensorSheafUnit C.sheaf D.sheaf ≫ (C.tensorSheafMulIso D).hom.val =
      C.tensorPresheafMultiplication D := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  have h : (adj.homEquiv (tensorPresheaf C.sheaf D.sheaf) (C.mul D).sheaf).symm
      (C.tensorPresheafMultiplication D) = (C.tensorSheafMulIso D).hom := by
    rw [Adjunction.homEquiv_counit]
    rfl
  have he := congrArg
    (adj.homEquiv (tensorPresheaf C.sheaf D.sheaf) (C.mul D).sheaf) h
  ext U s
  have he' := congrArg (fun φ => φ.app U s) he
  simp only [Equiv.apply_symm_apply,Adjunction.homEquiv_unit,
    PresheafOfModules.comp_app,ConcreteCategory.comp_apply] at he'
  dsimp only [Functor.comp_obj,Functor.comp_map,SheafOfModules.forget,
    PresheafOfModules.restrictScalars,PresheafOfModules.restrictScalarsObj,
    ModuleCat.restrictScalars,ModuleCat.RestrictScalars.obj',
    ModuleCat.RestrictScalars.map'] at he'
  exact he'.symm

@[simp] theorem tensorSheafMulIso_pure_sections (U : X.Opens)
    (s : Γ(C.sheaf,U)) (t : Γ(D.sheaf,U)) :
    (C.tensorSheafMulIso D).hom.app U
      ((tensorSheafUnit C.sheaf D.sheaf).app (op U) (s ⊗ₜ[Γ(X,U)] t)) =
        C.sectionProduct D U s t := by
  have h := congrArg (fun f => f.app (op U) (s ⊗ₜ[Γ(X,U)] t))
    (C.tensorSheafMulIso_unit D)
  simp only [PresheafOfModules.comp_app,ConcreteCategory.comp_apply,
    tensorPresheafMultiplication_app] at h
  change (C.tensorSheafMulIso D).hom.app U
    ((tensorSheafUnit C.sheaf D.sheaf).app (op U) (s ⊗ₜ[Γ(X,U)] t)) =
      C.sectionMultiplication D U (s ⊗ₜ[Γ(X,U)] t) at h
  exact h.trans (C.sectionMultiplication_tmul D U s t)

end RationalCartierCocycle

namespace CartierData

variable (D E : CartierData X)

/-- The addition of arbitrary actual fractional Cartier presentations
agrees with the ordinary tensor product of their actual sheaves. -/
def tensorSheafAddIso : tensorSheaf D.sheaf E.sheaf ≅ (D.add E).sheaf :=
  tensorSheafIso D.presentationIso E.presentationIso ≪≫
    D.localCocycle.tensorSheafMulIso E.localCocycle

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.tensorSheafMulIso
#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.tensorSheafMulIso_pure_sections
#print axioms PaperVerification.ToricSchemes.CartierData.tensorSheafAddIso
end
-- END PaperVerification.ToricCartierTensor
end

section
-- BEGIN PaperVerification.ToricSectionTensorNaturality



/-!
# Actual section multiplication under arbitrary line-bundle isomorphisms

The tensor sheaf is the genuine sheafification of sectionwise tensor
products. Naturality of its sheafification unit proves compatibility on
pure sections. Consequently arbitrary isomorphisms of the two line
bundles induce a commuting square for their actual section multiplication,
without any compatibility assumption on fractional embeddings.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite MonoidalCategory
open scoped TensorProduct

variable {X : Scheme.{u}}

theorem tensorSheafIso_pure_sections {M M' N N' : X.Modules}
    (F : M ≅ M') (G : N ≅ N') (U : X.Opens)
    (s : Γ(M,U)) (t : Γ(N,U)) :
    (tensorSheafIso F G).hom.app U
      ((tensorSheafUnit M N).app (op U) (s ⊗ₜ[Γ(X,U)] t)) =
      (tensorSheafUnit M' N').app (op U)
        (F.hom.app U s ⊗ₜ[Γ(X,U)] G.hom.app U t) := by
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing X.presheaf))
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let h := ((SheafOfModules.forget _).map F.hom) ⊗ₘ
    ((SheafOfModules.forget _).map G.hom)
  have he := congrArg (fun a=>a.app (op U) (s ⊗ₜ[Γ(X,U)] t))
    (adj.unit.naturality h)
  exact he.symm

variable [IsIntegral X]

namespace CartierData

variable (D D' E E' : CartierData X)

theorem tensorSheafAddIso_pure_sections (U : X.Opens)
    (s : Γ(D.sheaf,U)) (t : Γ(E.sheaf,U)) :
    (D.tensorSheafAddIso E).hom.app U
      ((tensorSheafUnit D.sheaf E.sheaf).app (op U) (s ⊗ₜ[Γ(X,U)] t)) =
        D.sectionProduct E U s t := by
  change (D.localCocycle.tensorSheafMulIso E.localCocycle).hom.app U
    ((tensorSheafIso D.presentationIso E.presentationIso).hom.app U
      ((tensorSheafUnit D.sheaf E.sheaf).app (op U) (s ⊗ₜ[Γ(X,U)] t))) = _
  rw [tensorSheafIso_pure_sections,RationalCartierCocycle.tensorSheafMulIso_pure_sections]
  rfl

def addSheafIso (F : D.sheaf ≅ D'.sheaf) (G : E.sheaf ≅ E'.sheaf) :
    (D.add E).sheaf ≅ (D'.add E').sheaf :=
  (D.tensorSheafAddIso E).symm ≪≫ tensorSheafIso F G ≪≫ D'.tensorSheafAddIso E'

theorem addSheafIso_sectionProduct
    (F : D.sheaf ≅ D'.sheaf) (G : E.sheaf ≅ E'.sheaf)
    (U : X.Opens) (s : Γ(D.sheaf,U)) (t : Γ(E.sheaf,U)) :
    (D.addSheafIso D' E E' F G).hom.app U (D.sectionProduct E U s t) =
      D'.sectionProduct E' U (F.hom.app U s) (G.hom.app U t) := by
  rw [← D.tensorSheafAddIso_pure_sections E U s t]
  change (D'.tensorSheafAddIso E').hom.app U
    ((tensorSheafIso F G).hom.app U
      ((D.tensorSheafAddIso E).inv.app U
        ((D.tensorSheafAddIso E).hom.app U
          ((tensorSheafUnit D.sheaf E.sheaf).app (op U) (s⊗ₜ[Γ(X,U)]t))))) = _
  have he : (D.tensorSheafAddIso E).inv.app U
      ((D.tensorSheafAddIso E).hom.app U
        ((tensorSheafUnit D.sheaf E.sheaf).app (op U) (s⊗ₜ[Γ(X,U)]t))) =
      (tensorSheafUnit D.sheaf E.sheaf).app (op U) (s⊗ₜ[Γ(X,U)]t) := by
    exact congrArg (fun h=>h.app U
      ((tensorSheafUnit D.sheaf E.sheaf).app (op U) (s⊗ₜ[Γ(X,U)]t)))
      (D.tensorSheafAddIso E).hom_inv_id
  rw [he,tensorSheafIso_pure_sections,tensorSheafAddIso_pure_sections]

end CartierData

namespace BaseSections

open scoped BaseSections

variable (k : Type u) [CommRing k] [X.Over (Spec (CommRingCat.of k))]

def globalSectionsIso {M N : X.Modules} (F : M ≅ N) : Γ(M,⊤) ≃ₗ[k] Γ(N,⊤) := by
  let e : Γ(M,⊤) ≃ₗ[Γ(X,⊤)] Γ(N,⊤) :=
    ((PresheafOfModules.evaluation X.ringCatSheaf.obj (op ⊤)).mapIso
      ((SheafOfModules.forget _).mapIso F)).toLinearEquiv
  exact e.restrictScalars k

@[simp] theorem globalSectionsIso_apply {M N : X.Modules} (F : M ≅ N) (s : Γ(M,⊤)) :
    globalSectionsIso k F s=F.hom.app ⊤ s := rfl

end BaseSections

namespace CartierData

open scoped BaseSections

variable (k : Type u) [CommRing k] [X.Over (Spec (CommRingCat.of k))]
    (D D' E E' : CartierData X)
    (F : D.sheaf ≅ D'.sheaf) (G : E.sheaf ≅ E'.sheaf)

theorem sectionMultiplicationOver_sheafIso :
    (BaseSections.globalSectionsIso k (D.addSheafIso D' E E' F G)).toLinearMap.comp
      (D.sectionMultiplicationOver k E) =
    (D'.sectionMultiplicationOver k E').comp
      (TensorProduct.map (BaseSections.globalSectionsIso k F).toLinearMap
        (BaseSections.globalSectionsIso k G).toLinearMap) := by
  apply TensorProduct.ext'
  intro s t
  change BaseSections.globalSectionsIso k (D.addSheafIso D' E E' F G)
      (D.sectionProduct E ⊤ s t) =
    D'.sectionProduct E' ⊤ (BaseSections.globalSectionsIso k F s)
      (BaseSections.globalSectionsIso k G t)
  exact D.addSheafIso_sectionProduct D' E E' F G ⊤ s t

include F G in
/-- Surjectivity of the actual tensor multiplication is an invariant of
the actual line bundles, independently of fractional presentations. -/
theorem sectionMultiplicationOver_surjective_iff_sheafIso :
    Function.Surjective (D.sectionMultiplicationOver k E) ↔
      Function.Surjective (D'.sectionMultiplicationOver k E') := by
  let es := TensorProduct.congr (BaseSections.globalSectionsIso k F)
    (BaseSections.globalSectionsIso k G)
  let et := BaseSections.globalSectionsIso k (D.addSheafIso D' E E' F G)
  have he (z) : et (D.sectionMultiplicationOver k E z)=
      D'.sectionMultiplicationOver k E' (es z) :=
    congrArg (fun h=>h z) (D.sectionMultiplicationOver_sheafIso k D' E E' F G)
  constructor
  · intro h y
    obtain ⟨t,ht⟩ := et.surjective y
    obtain ⟨z,hz⟩ := h t
    exact ⟨es z,(he z).symm.trans (by rw [hz,ht])⟩
  · intro h t
    obtain ⟨y,hy⟩ := h (et t)
    obtain ⟨z,hz⟩ := es.surjective y
    exact ⟨z,et.injective (by rw [he,hz,hy])⟩

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.CartierData.sectionMultiplicationOver_surjective_iff_sheafIso
end
-- END PaperVerification.ToricSectionTensorNaturality
end

#eval "TORIC_DICTIONARY_PART_11_EOF"
