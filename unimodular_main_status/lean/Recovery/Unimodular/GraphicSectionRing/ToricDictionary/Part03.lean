module

public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.Part02
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Algebra.MonoidAlgebra.Support
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Logic.Relation
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.MonoidAlgebra.Ideal
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum

@[expose] public section
set_option autoImplicit false

section
-- BEGIN PaperVerification.ToricTorusAction



/-!
# The actual split torus and its action on semigroup charts

The torus is the spectrum of the genuine group Hopf algebra. A semigroup
chart is already a monoid scheme. Restriction of its regular monoid action
along the actual torus-to-chart morphism supplies the group action, with
unit and associativity proved in the category of schemes over the field.
Its actual comorphism is the character coaction, over arbitrary fields.
-/

noncomputable section

universe u v w

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory MonObj
open scoped TensorProduct

variable (k : Type (max u v)) [CommRing k] (M : Type v) [AddCommGroup M]

/-- The actual spectrum of the group algebra, with its canonical Hopf
algebra group structure. For a rank-n free group this is the split n-torus. -/
def splitTorus : Scheme.{max u v} := Spec (CommRingCat.of (AddMonoidAlgebra k M))

instance splitTorus_isOver : (splitTorus k M).Over (Spec (CommRingCat.of k)) := by
  dsimp only [splitTorus]
  infer_instance

abbrev splitTorusOver : Over (Spec (CommRingCat.of k)) :=
  (splitTorus k M).asOver (Spec (CommRingCat.of k))

instance splitTorus_monObj : MonObj (splitTorusOver k M) := by
  dsimp only [splitTorusOver, splitTorus]
  exact AlgebraicGeometry.instMonObjSpecAsOverSpec
    (R := CommRingCat.of k) (A := CommRingCat.of (AddMonoidAlgebra k M))

instance splitTorus_grpObj : GrpObj (splitTorusOver k M) := by
  dsimp only [splitTorusOver, splitTorus]
  exact AlgebraicGeometry.instGrpObjSpecAsOverSpec
    (R := CommRingCat.of k) (A := CommRingCat.of (AddMonoidAlgebra k M))

instance splitTorus_commGrpObj : CommGrpObj (splitTorusOver k M) := by
  dsimp only [splitTorusOver, splitTorus]
  infer_instance

/-- The bundled actual group scheme, not an action of rational points. -/
def splitTorusGroup : Grp (Over (Spec (CommRingCat.of k))) :=
  Grp.mk (splitTorusOver k M)

instance splitTorusGroup_isCommMonObj : IsCommMonObj (splitTorusGroup.{u, v} k M).X := by
  change IsCommMonObj (splitTorusOver k M)
  dsimp only [splitTorusOver, splitTorus]
  exact AlgebraicGeometry.isCommMonObj_spec_asOver_spec
    (R := CommRingCat.of k) (A := CommRingCat.of (AddMonoidAlgebra k M))

/-- Algebra maps from the torus coordinate ring are exactly characters
of the lattice valued in units of the test algebra. This statement is
valid for every test algebra, including nonreduced algebras. -/
def torusCharacterPointsEquiv (A : Type (max u v)) [CommRing A] [Algebra k A] :
    (AddMonoidAlgebra k M →ₐ[k] A) ≃ (Multiplicative M →* Aˣ) :=
  (AddMonoidAlgebra.lift k A M).symm.trans MonoidHom.toHomUnitsMulEquiv.toEquiv

@[simp] theorem torusCharacterPointsEquiv_apply (A : Type (max u v))
    [CommRing A] [Algebra k A] (f : AddMonoidAlgebra k M →ₐ[k] A) (m : M) :
    ((torusCharacterPointsEquiv k M A f (Multiplicative.ofAdd m) : Aˣ) : A) =
      f (AddMonoidAlgebra.single m 1) := rfl

variable {M} (S : AddSubmonoid M)

/-- The actual affine semigroup chart. -/
def semigroupChart : Scheme.{max u v} :=
  Spec (CommRingCat.of (AddMonoidAlgebra k S))

instance semigroupChart_isOver : (semigroupChart k S).Over (Spec (CommRingCat.of k)) := by
  dsimp only [semigroupChart]
  infer_instance

abbrev semigroupChartOver : Over (Spec (CommRingCat.of k)) :=
  (semigroupChart k S).asOver (Spec (CommRingCat.of k))

instance semigroupChart_monObj : MonObj (semigroupChartOver k S) := by
  dsimp only [semigroupChartOver, semigroupChart]
  infer_instance

/-- The actual morphism induced by inclusion of exponents S→M. Openness
and dominance require the appropriate saturated generating semigroup and
are proved separately from this group-action construction. -/
def torusToSemigroupChart : splitTorus k M ⟶ semigroupChart k S :=
  Spec.map (CommRingCat.ofHom
    (AddMonoidAlgebra.mapDomainBialgHom k S.subtype).toAlgHom.toRingHom)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
instance torusToSemigroupChart_isOver :
    (torusToSemigroupChart k S).IsOver (Spec (CommRingCat.of k)) := by
  dsimp only [torusToSemigroupChart, splitTorus, semigroupChart]
  infer_instance

abbrev torusToSemigroupChartOver :
    splitTorusOver k M ⟶ semigroupChartOver k S :=
  (torusToSemigroupChart k S).asOver (Spec (CommRingCat.of k))

instance torusToSemigroupChart_isMonHom :
    IsMonHom (torusToSemigroupChartOver k S) := by
  change IsMonHom (((bialgSpec (CommRingCat.of k)).map
    (CommBialgCat.ofHom (AddMonoidAlgebra.mapDomainBialgHom k S.subtype)).op).hom)
  infer_instance

/-- The genuine torus action, obtained by restriction of the regular
monoid-scheme action. -/
instance semigroupChart_torusAction :
    ModObj (splitTorusOver k M) (semigroupChartOver k S) := by
  letI : ModObj (semigroupChartOver k S) (semigroupChartOver k S) :=
    ModObj.regular (semigroupChartOver k S)
  exact Mod.scalarRestriction (torusToSemigroupChartOver k S) (semigroupChartOver k S)

/-- This action really extends multiplication on the embedded torus. -/
theorem semigroupChart_action_extends_torus :
    (𝟙 (splitTorusOver k M) ⊗ₘ torusToSemigroupChartOver k S) ≫
      γ[splitTorusOver k M, semigroupChartOver k S] =
      μ[splitTorusOver k M] ≫ torusToSemigroupChartOver k S := by
  change ((splitTorusOver k M) ◁ torusToSemigroupChartOver k S) ≫
      (torusToSemigroupChartOver k S ▷ semigroupChartOver k S) ≫
        μ[semigroupChartOver k S] = _
  rw [← Category.assoc, ← MonoidalCategory.tensorHom_def']
  exact (IsMonHom.mul_hom (f := torusToSemigroupChartOver k S)).symm

/-- The coaction on the actual coordinate algebra. -/
def semigroupChartCoaction : AddMonoidAlgebra k S →ₐ[k]
    AddMonoidAlgebra k M ⊗[k] AddMonoidAlgebra k S :=
  (Algebra.TensorProduct.map
    (AddMonoidAlgebra.mapDomainBialgHom k S.subtype).toAlgHom
    (AlgHom.id k (AddMonoidAlgebra k S))).comp
      (Bialgebra.comulAlgHom k (AddMonoidAlgebra k S))

@[simp] theorem semigroupChartCoaction_single (s : S) (c : k) :
    semigroupChartCoaction k S (AddMonoidAlgebra.single s c) =
      AddMonoidAlgebra.single (s : M) 1 ⊗ₜ[k] AddMonoidAlgebra.single s c := by
  simp only [semigroupChartCoaction, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply,
    AddMonoidAlgebra.comul_single, CommSemiring.comul_apply,
    TensorProduct.map_tmul, AddMonoidAlgebra.lsingle_apply,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, BialgHom.coe_toAlgHom,
    AddMonoidAlgebra.mapDomainBialgHom_single]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The action's actual scheme comorphism is exactly the displayed
character coaction. The tensor-to-fiber-product isomorphism is Mathlib's
proved affine-scheme tensor-product identification. -/
theorem semigroupChart_action_spec :
    (γ[splitTorusOver k M, semigroupChartOver k S]).left =
      (pullbackSpecIso (CommRingCat.of k)
        (CommRingCat.of (AddMonoidAlgebra k M))
        (CommRingCat.of (AddMonoidAlgebra k S))).hom ≫
      Spec.map (CommRingCat.ofHom (semigroupChartCoaction k S).toRingHom) := by
  let F := algSpec (CommRingCat.of k)
  letI : F.LaxMonoidal :=
    (AlgebraicGeometry.braidedAlgSpec (R := CommRingCat.of k)).toMonoidal.toLaxMonoidal
  let T : (CommAlgCat k)ᵒᵖ := op (CommAlgCat.of k (AddMonoidAlgebra k M))
  let C : (CommAlgCat k)ᵒᵖ := op (CommAlgCat.of k (AddMonoidAlgebra k S))
  let i : T ⟶ C := (CommAlgCat.ofHom
    (AddMonoidAlgebra.mapDomainBialgHom k S.subtype).toAlgHom).op
  have hnatural := Functor.LaxMonoidal.μ_natural_left F i C
  have haction : γ[splitTorusOver k M, semigroupChartOver k S] =
      Functor.LaxMonoidal.μ F T C ≫ F.map ((i ▷ C) ≫ μ[C]) := by
    change (F.map i ▷ F.obj C) ≫
      (Functor.LaxMonoidal.μ F C C ≫ F.map μ[C]) = _
    rw [← Category.assoc, hnatural, Category.assoc, ← F.map_comp]
  rw [haction]
  rfl

/-- The chart inclusion is equivariant at the genuine coaction level. -/
theorem semigroupChartCoaction_inclusion (f : AddMonoidAlgebra k S) :
    Algebra.TensorProduct.map (AlgHom.id k (AddMonoidAlgebra k M))
      (AddMonoidAlgebra.mapDomainBialgHom k S.subtype).toAlgHom
      (semigroupChartCoaction k S f) =
    Coalgebra.comul (R := k)
      (AddMonoidAlgebra.mapDomainBialgHom k S.subtype f) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single s c =>
      simp only [semigroupChartCoaction_single, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, BialgHom.coe_toAlgHom, AddMonoidAlgebra.mapDomainBialgHom_single,
        AddMonoidAlgebra.comul_single, CommSemiring.comul_apply,
        TensorProduct.map_tmul, AddMonoidAlgebra.lsingle_apply]
      rfl

end PaperVerification.ToricSchemes

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite MonoidalCategory MonObj
open WithConv

section GroupHom

variable (k : Type (max u v w)) [CommRing k] (M : Type v) [AddCommGroup M]

/-- The fully faithful affine Hopf correspondence identifies actual
group-scheme morphisms of split tori with their actual bialgebra
comorphisms. In particular, this is not a test on rational points. -/
def torusBialgHomGroupHomEquiv (N : Type w) [AddCommGroup N] :
    (AddMonoidAlgebra k N →ₐc[k] AddMonoidAlgebra k M) ≃
      (splitTorusGroup.{max u v w, v} k M ⟶
        splitTorusGroup.{max u v w, w} k N) := by
  let e : (AddMonoidAlgebra k N →ₐc[k] AddMonoidAlgebra k M) ≃
      (op (CommHopfAlgCat.of k (AddMonoidAlgebra k M)) ⟶
        op (CommHopfAlgCat.of k (AddMonoidAlgebra k N))) :=
    { toFun := fun f => (CommHopfAlgCat.ofHom f).op
      invFun := fun f => f.unop.hom
      left_inv := fun _ => rfl
      right_inv := fun f => Quiver.Hom.unop_inj (CommHopfAlgCat.ofHom_hom f.unop) }
  exact e.trans (hopfSpec.fullyFaithful (R := CommRingCat.of k)).homEquiv

@[simp] theorem torusBialgHomGroupHomEquiv_hom (N : Type w) [AddCommGroup N]
    (f : AddMonoidAlgebra k N →ₐc[k] AddMonoidAlgebra k M) :
    (torusBialgHomGroupHomEquiv.{u, v, w} k M N f).hom.hom =
      (Spec.map (CommRingCat.ofHom f.toAlgHom.toRingHom)).asOver
        (Spec (CommRingCat.of k)) := rfl

end GroupHom

section Characters

variable (k : Type (max u v)) [CommRing k] (M : Type v) [AddCommGroup M]

/-- The target `Spec k[ℤ]` is the ordinary multiplicative group scheme:
its actual scheme-valued points over every test algebra are the units
of that algebra. Nonreduced test algebras are included. -/
def multiplicativeGroupSchemePointsEquiv (A : Type (max u v))
    [CommRing A] [Algebra k A] :
    ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of k)) ⟶
      splitTorusOver k ℤ) ≃ Aˣ :=
  Spec.mapMulEquiv.toEquiv.symm.trans <|
    (WithConv.equiv _).trans <|
      (torusCharacterPointsEquiv k ℤ A).trans (zpowersHom Aˣ).symm

variable [IsDomain k]

/-- The lattice is exactly the group of genuine scheme characters
`T_M → G_m`. Mathlib's group-like-element classification and fully
faithful `hopfSpec` prove exhaustion, over every domain. -/
def torusCharacterEquiv :
    M ≃ (splitTorusGroup.{max u v, v} k M ⟶ splitTorusGroup.{max u v, 0} k ℤ) :=
  (zmultiplesHom M).trans <|
    (AddMonoidAlgebra.mapDomainBialgHomEquiv (R := k)).trans
      (torusBialgHomGroupHomEquiv.{u, v, 0} k M ℤ)

@[simp] theorem torusCharacterEquiv_hom (m : M) :
    (torusCharacterEquiv k M m).hom.hom =
      (Spec.map (CommRingCat.ofHom
        (AddMonoidAlgebra.mapDomainBialgHom k (zmultiplesHom M m)).toAlgHom.toRingHom)).asOver
          (Spec (CommRingCat.of k)) := rfl

/-- The comorphism of the character indexed by `m` literally sends
the Laurent monomial `t^z` to the lattice monomial `χ^(z • m)`. -/
@[simp] theorem torusCharacter_comorphism_single (m : M) (z : ℤ) (c : k) :
    (AddMonoidAlgebra.mapDomainBialgHom k (zmultiplesHom M m))
      (AddMonoidAlgebra.single z c) = AddMonoidAlgebra.single (z • m) c := by
  simp only [AddMonoidAlgebra.mapDomainBialgHom_single, zmultiplesHom_apply]

set_option synthInstance.maxHeartbeats 200000 in
/-- Addition in the lattice is the ordinary product of actual
group-scheme characters. -/
theorem torusCharacterEquiv_add (m m' : M) :
    torusCharacterEquiv k M (m + m') =
      torusCharacterEquiv k M m * torusCharacterEquiv k M m' := by
  let f := AddMonoidAlgebra.mapDomainBialgHom k (zmultiplesHom M m)
  let g := AddMonoidAlgebra.mapDomainBialgHom k (zmultiplesHom M m')
  have hsum : AddMonoidAlgebra.mapDomainBialgHom k (zmultiplesHom M (m + m')) =
      (toConv f * toConv g).ofConv := by
    rw [show zmultiplesHom M (m + m') =
      zmultiplesHom M m + zmultiplesHom M m' from (zmultiplesAddHom M).map_add m m']
    exact AddMonoidAlgebra.mapDomainBialgHom_add _ _
  have hconv := congrArg (fun φ : AddMonoidAlgebra k ℤ →ₐc[k] AddMonoidAlgebra k M =>
    toConv φ.toAlgHom) hsum
  rw [BialgHom.toAlgHom_convMul] at hconv
  apply Grp.hom_ext
  simp only [Grp.Hom.hom_mul, Mon.Hom.hom_mul, torusCharacterEquiv_hom]
  change Spec.mapMulEquiv
      (toConv (AddMonoidAlgebra.mapDomainBialgHom k
        (zmultiplesHom M (m + m'))).toAlgHom) =
    Spec.mapMulEquiv (toConv f.toAlgHom) * Spec.mapMulEquiv (toConv g.toAlgHom)
  rw [hconv, map_mul]

def additiveEquivOfMultiplicativeLaw
    {A B : Type*} [Add A] [Mul B] (e : A ≃ B)
    (h : ∀ x y, e (x + y) = e x * e y) : A ≃+ Additive B where
  toEquiv := e.trans Additive.ofMul
  map_add' x y := congrArg Additive.ofMul (h x y)

set_option synthInstance.maxHeartbeats 200000 in
/-- The character lattice equivalence also preserves the full abelian
group structure, rather than only enumerating its underlying set. -/
def torusCharacterAddEquiv :
    M ≃+ Additive
      (splitTorusGroup.{max u v, v} k M ⟶ splitTorusGroup.{max u v, 0} k ℤ) :=
  additiveEquivOfMultiplicativeLaw (torusCharacterEquiv.{u, v} k M)
    (torusCharacterEquiv_add.{u, v} k M)

theorem torusCharacter_existsUnique
    (f : splitTorusGroup.{max u v, v} k M ⟶ splitTorusGroup.{max u v, 0} k ℤ) :
    ∃! m : M, torusCharacterEquiv k M m = f := by
  let e := torusCharacterEquiv k M
  refine ⟨e.symm f, e.apply_symm_apply f, ?_⟩
  intro m hm
  exact e.injective (hm.trans (e.apply_symm_apply f).symm)

end Characters

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.torusCharacterAddEquiv
#print axioms PaperVerification.ToricSchemes.torusCharacter_existsUnique
end
-- END PaperVerification.ToricTorusAction
end

section
-- BEGIN PaperVerification.ToricDenseTorusFunctionField



/-!
# The function field of a scheme containing the actual split torus

The coordinate ring is the ordinary group algebra of the integral
character lattice. Its domain property is proved from the iterated
Laurent presentation, so no additional domain hypothesis is attached to
the torus statement.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters

variable (k : Type u) [Field k] (n : ℕ) (X : Scheme.{u}) [IsIntegral X]
    (j : splitTorus k (Fin n → ℤ) ⟶ X) [hj : IsOpenImmersion j]

/-- Restriction along the actual open torus identifies rational
functions with the fraction field of its character algebra. -/
def torusOpenFunctionFieldEquiv :
    X.functionField ≃+* FractionRing (torusCoordinateRing k n) := by
  letI := torusCoordinateRing_isDomain k n
  letI : IsOpenImmersion
      (show Spec (CommRingCat.of (torusCoordinateRing k n)) ⟶ X from j) := hj
  exact affineOpenFunctionFieldEquiv
    (CommRingCat.of (torusCoordinateRing k n)) j

/-- On global regular functions this is the literal restriction to the
torus, followed by the canonical fraction-field embedding. -/
@[simp] theorem torusOpenFunctionFieldEquiv_germ_top (a : Γ(X,⊤)) :
    torusOpenFunctionFieldEquiv k n X j (X.germToFunctionField ⊤ a) =
      algebraMap (torusCoordinateRing k n) (FractionRing (torusCoordinateRing k n))
        ((Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).hom
          (j.appTop a)) := by
  letI := torusCoordinateRing_isDomain k n
  letI : IsOpenImmersion
      (show Spec (CommRingCat.of (torusCoordinateRing k n)) ⟶ X from j) := hj
  exact affineOpenFunctionFieldEquiv_germ_top
    (CommRingCat.of (torusCoordinateRing k n)) j a

/-- Equality of rational functions can be checked on the actual open
torus. This is injectivity of a constructed equivalence, not a hypothesis. -/
theorem rationalFunction_eq_iff_on_torus (f g : X.functionField) :
    f=g ↔ torusOpenFunctionFieldEquiv k n X j f =
      torusOpenFunctionFieldEquiv k n X j g :=
  (torusOpenFunctionFieldEquiv k n X j).injective.eq_iff.symm

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.torusOpenFunctionFieldEquiv
end
-- END PaperVerification.ToricDenseTorusFunctionField
end

section
-- BEGIN PaperVerification.ToricTorusCartierRepresentative



/-!
# A linearly equivalent Cartier representative trivial on the dense torus

The actual torus Picard trivialization supplies a nonzero rational generator.
Multiplying the fractional embedding by its inverse gives a linearly
equivalent Cartier divisor. On every open of the torus, the new actual
fractional module is precisely the actual regular-function module. The
explicit rational factor is retained; equality of divisors is not confused
with linear equivalence.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace PaperVerification.ToricSchemes

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (j : Y ⟶ X) [IsOpenImmersion j]

namespace CartierData

variable (D : CartierData X)

/-- The actual rational value of a section on a nonempty open chart. -/
def alongSectionValue (V : Y.Opens) [Nonempty V] :
    Γ(D.sheaf.restrict j,V) →+ X.functionField := by
  letI : Nonempty (j ''ᵁ V) := openImmersion_image_nonempty j V
  exact (D.sectionValue (j ''ᵁ V)).toAddMonoidHom.comp
    (D.sheaf.restrictAppIso j V).addCommGroupIsoToAddEquiv.toAddMonoidHom

theorem alongSectionValue_injective (V : Y.Opens) [Nonempty V] :
    Function.Injective (D.alongSectionValue j V) := by
  letI : Nonempty (j ''ᵁ V) := openImmersion_image_nonempty j V
  exact (D.sectionValue_injective (j ''ᵁ V)).comp
    (D.sheaf.restrictAppIso j V).addCommGroupIsoToAddEquiv.injective

theorem alongSectionValue_smul (V : Y.Opens) [Nonempty V]
    (a : Γ(Y,V)) (s : Γ(D.sheaf.restrict j,V)) :
    D.alongSectionValue j V (a • s) =
      openImmersionRegularToFunctionField j V a * D.alongSectionValue j V s := by
  letI : Nonempty (j ''ᵁ V) := openImmersion_image_nonempty j V
  change D.sectionValue (j ''ᵁ V)
      ((j.appIso V).inv a • (D.sheaf.restrictAppIso j V).hom s) = _
  rw [D.sectionValue_smul,openImmersionRegularToFunctionField_eq_germ_image]
  rfl

theorem alongSectionValue_restrict {U V : Y.Opens} [Nonempty U] [Nonempty V]
    (i : V ⟶ U) (s : Γ(D.sheaf.restrict j,U)) :
    D.alongSectionValue j V ((D.sheaf.restrict j).presheaf.map i.op s) =
      D.alongSectionValue j U s := by
  letI : Nonempty (j ''ᵁ U) := openImmersion_image_nonempty j U
  letI : Nonempty (j ''ᵁ V) := openImmersion_image_nonempty j V
  exact D.sectionValue_restrict (homOfLE (j.image_mono i.le)) s

/-- Evaluation of an actual global trivialization on any open of the chart. -/
def chartFrameCoordinates
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf) (V : Y.Opens) :
    Γ(D.sheaf.restrict j,V) ≃ₗ[Γ(Y,V)] Γ(Y,V) :=
  ((PresheafOfModules.evaluation Y.ringCatSheaf.obj (op V)).mapIso
    ((SheafOfModules.forget _).mapIso e)).toLinearEquiv

/-- The nonzero rational generator supplied by an actual chart trivialization. -/
def chartFrameRationalGenerator
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf) : X.functionField :=
  D.alongSectionValue j ⊤ (e.inv.app ⊤ (1 : Γ(Y,⊤)))

theorem chartFrameRationalGenerator_ne_zero
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf) :
    D.chartFrameRationalGenerator j e ≠ 0 := by
  intro hzero
  have hz : e.inv.app ⊤ (1 : Γ(Y,⊤))=0 :=
    D.alongSectionValue_injective j ⊤ (hzero.trans (map_zero _).symm)
  have h1 : (1 : Γ(Y,⊤))=0 := by
    let L := D.chartFrameCoordinates j e ⊤
    calc
      (1 : Γ(Y,⊤)) = L (e.inv.app ⊤ (1 : Γ(Y,⊤))) :=
        (L.apply_symm_apply (1 : Γ(Y,⊤))).symm
      _ = L 0 := congrArg L hz
      _ = 0 := map_zero L
  apply (one_ne_zero : (1 : Y.functionField) ≠ 0)
  calc
    (1 : Y.functionField) = Y.germToFunctionField ⊤ (1 : Γ(Y,⊤)) :=
      (map_one (Y.germToFunctionField ⊤).hom).symm
    _ = Y.germToFunctionField ⊤ (0 : Γ(Y,⊤)) := congrArg (Y.germToFunctionField ⊤) h1
    _ = 0 := map_zero (Y.germToFunctionField ⊤).hom

theorem alongSectionValue_frameGenerator
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (V : Y.Opens) [Nonempty V] :
    D.alongSectionValue j V (e.inv.app V (1 : Γ(Y,V)))=D.chartFrameRationalGenerator j e := by
  have hg : e.inv.app V (1 : Γ(Y,V)) =
      (D.sheaf.restrict j).presheaf.map (homOfLE le_top).op (e.inv.app ⊤ (1 : Γ(Y,⊤))) := by
    have hn := PresheafOfModules.naturality_apply e.inv.val
      (homOfLE (show V≤(⊤ : Y.Opens) from le_top)).op
      (1 : Γ(Y,⊤))
    change e.inv.app V
        ((Y.presheaf.map (homOfLE (show V≤(⊤ : Y.Opens) from le_top)).op).hom
          (1 : Γ(Y,⊤))) =
      (D.sheaf.restrict j).presheaf.map (homOfLE le_top).op
        (e.inv.app ⊤ (1 : Γ(Y,⊤))) at hn
    simpa only [map_one] using hn
  calc
    _ = D.alongSectionValue j V
        ((D.sheaf.restrict j).presheaf.map (homOfLE le_top).op
          (e.inv.app ⊤ (1 : Γ(Y,⊤)))) := congrArg (D.alongSectionValue j V) hg
    _ = D.alongSectionValue j ⊤ (e.inv.app ⊤ (1 : Γ(Y,⊤))) :=
      D.alongSectionValue_restrict j (homOfLE (show V≤(⊤ : Y.Opens) from le_top)) _
    _ = _ := rfl

/-- The actual chart coordinate describes the rational value of every
section, not only the distinguished generator. -/
theorem alongSectionValue_frame
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (V : Y.Opens) [Nonempty V] (s : Γ(D.sheaf.restrict j,V)) :
    D.alongSectionValue j V s =
      openImmersionRegularToFunctionField j V (e.hom.app V s) *
        D.chartFrameRationalGenerator j e := by
  let a : Γ(Y,V) := e.hom.app V s
  let t : Γ(D.sheaf.restrict j,V) := e.inv.app V (1 : Γ(Y,V))
  have hs : s=a • t := by
    apply (D.chartFrameCoordinates j e V).injective
    change D.chartFrameCoordinates j e V s =
      D.chartFrameCoordinates j e V
        (D.chartFrameCoordinates j e V s • (D.chartFrameCoordinates j e V).symm 1)
    simp
  calc
    _ = D.alongSectionValue j V (a • t) := congrArg (D.alongSectionValue j V) hs
    _ = openImmersionRegularToFunctionField j V a * D.alongSectionValue j V t :=
      D.alongSectionValue_smul j V a t
    _ = _ := congrArg (fun z : X.functionField => openImmersionRegularToFunctionField j V a * z)
      (D.alongSectionValue_frameGenerator j e V)

theorem scale_alongSectionValue (q : X.functionFieldˣ)
    (V : Y.Opens) [Nonempty V] (s : Γ(D.sheaf.restrict j,V)) :
    (D.scale q).alongSectionValue j V s =
      (q : X.functionField)*D.alongSectionValue j V s := by
  letI : Nonempty (j ''ᵁ V) := openImmersion_image_nonempty j V
  exact D.scale_sectionValue q (j ''ᵁ V) s

end CartierData

section Torus

open PaperVerification.ToricCharacters

variable (k : Type u) [Field k] (n : ℕ) (X : Scheme.{u}) [IsIntegral X]
    (j : splitTorus k (Fin n→ℤ) ⟶ X) [hj : IsOpenImmersion j]
    (D : CartierData X)

local instance torusScheme_integral : IsIntegral (splitTorus k (Fin n→ℤ)) := by
  letI := torusCoordinateRing_isDomain k n
  change IsIntegral (Spec (CommRingCat.of (torusCoordinateRing k n)))
  infer_instance

/-- The actual Picard trivialization of the restriction to the split torus. -/
def torusCartierFrame :
    D.sheaf.restrict j ≅ SheafOfModules.unit (splitTorus k (Fin n→ℤ)).ringCatSheaf := by
  letI : IsOpenImmersion
      (show Spec (CommRingCat.of (torusCoordinateRing k n)) ⟶ X from j) := hj
  exact torusInvertibleSheafIso k n (D.sheaf.restrict j)
    (isInvertibleModule_restrict j D.locallyFree)

/-- The explicit ambient rational generator supplied by this trivialization. -/
def torusCartierGenerator : X.functionFieldˣ := by
  letI := torusCoordinateRing_isDomain k n
  exact Units.mk0 (D.chartFrameRationalGenerator j (torusCartierFrame k n X j D))
    (D.chartFrameRationalGenerator_ne_zero j (torusCartierFrame k n X j D))

/-- A linearly equivalent representative, normalized to O_T on the actual
dense open torus. The rational translation factor remains explicit. -/
def torusNormalizedCartier : CartierData X :=
  D.scale (torusCartierGenerator k n X j D)⁻¹

theorem torusNormalizedCartier_linearlyEquivalent :
    (torusNormalizedCartier k n X j D).LinearlyEquivalent D :=
  D.scale_linearlyEquivalent _

theorem torusNormalizedCartier_isAmple_iff :
    (torusNormalizedCartier k n X j D).IsAmple ↔ D.IsAmple :=
  D.isAmple_scale_iff _

def torusNormalizedCartierSheafIso :
    (torusNormalizedCartier k n X j D).sheaf.restrict j ≅
      SheafOfModules.unit (splitTorus k (Fin n→ℤ)).ringCatSheaf :=
  torusCartierFrame k n X j D

/-- On every nonempty torus open, the normalized actual fractional embedding
agrees with the ordinary embedding of regular functions into K(X). -/
theorem torusNormalizedCartier_value
    (V : (splitTorus k (Fin n→ℤ)).Opens) [Nonempty V]
    (s : Γ((torusNormalizedCartier k n X j D).sheaf.restrict j,V)) :
    (torusNormalizedCartier k n X j D).alongSectionValue j V s =
      openImmersionRegularToFunctionField j V
        ((torusNormalizedCartierSheafIso k n X j D).hom.app V s) := by
  letI := torusCoordinateRing_isDomain k n
  calc
    _ = (↑((torusCartierGenerator k n X j D)⁻¹) : X.functionField) *
        D.alongSectionValue j V s := D.scale_alongSectionValue j _ V s
    _ = (↑((torusCartierGenerator k n X j D)⁻¹) : X.functionField) *
        (openImmersionRegularToFunctionField j V
          ((torusCartierFrame k n X j D).hom.app V s) *
            D.chartFrameRationalGenerator j (torusCartierFrame k n X j D)) :=
      congrArg (fun z : X.functionField =>
        (↑((torusCartierGenerator k n X j D)⁻¹) : X.functionField) * z)
        (D.alongSectionValue_frame j (torusCartierFrame k n X j D) V s)
    _ = _ := by
      change (D.chartFrameRationalGenerator j (torusCartierFrame k n X j D))⁻¹ *
          (openImmersionRegularToFunctionField j V
            ((torusCartierFrame k n X j D).hom.app V s) *
              D.chartFrameRationalGenerator j (torusCartierFrame k n X j D)) = _
      field_simp [D.chartFrameRationalGenerator_ne_zero j (torusCartierFrame k n X j D)]
      rfl

/-- Equality of the actual fractional module with the regular-function
module on each torus open. No boundary or invariant-divisor dictionary is
included as an assumption. -/
theorem torusNormalizedCartier_range
    (V : (splitTorus k (Fin n→ℤ)).Opens) [Nonempty V] :
    Set.range ((torusNormalizedCartier k n X j D).alongSectionValue j V) =
      Set.range (openImmersionRegularToFunctionField j V) := by
  letI := torusCoordinateRing_isDomain k n
  ext r
  constructor
  · rintro ⟨s,rfl⟩
    exact ⟨(torusNormalizedCartierSheafIso k n X j D).hom.app V s,
      (torusNormalizedCartier_value k n X j D V s).symm⟩
  · rintro ⟨a,rfl⟩
    let E := torusNormalizedCartierSheafIso k n X j D
    let C := torusNormalizedCartier k n X j D
    let s := E.inv.app V a
    refine ⟨s,?_⟩
    calc
      _ = openImmersionRegularToFunctionField j V (E.hom.app V s) :=
        torusNormalizedCartier_value k n X j D V s
      _ = _ := congrArg (openImmersionRegularToFunctionField j V)
        ((C.chartFrameCoordinates j E V).apply_symm_apply a)

end Torus

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.torusNormalizedCartier_linearlyEquivalent
#print axioms PaperVerification.ToricSchemes.torusNormalizedCartier_value
#print axioms PaperVerification.ToricSchemes.torusNormalizedCartier_range
end
-- END PaperVerification.ToricTorusCartierRepresentative
end

section
-- BEGIN PaperVerification.ToricCartierChartValues



/-!
# Fractional values on genuine open charts

A global frame on an open chart gives a principal fractional module on
every smaller ambient open. This statement is derived from restriction of
the actual sheaf. It also proves the regularity of the ratio of two chart
generators on the actual scheme overlap.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace PaperVerification.ToricSchemes.CartierData

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (D : CartierData X) (j : Y ⟶ X) [IsOpenImmersion j]

theorem alongSectionValue_range (V : Y.Opens) [Nonempty V] :
    Set.range (D.alongSectionValue j V) =
      Set.range (@sectionValue X inferInstance D (j ''ᵁ V)
        (openImmersion_image_nonempty j V)) := by
  letI : Nonempty (j ''ᵁ V) := openImmersion_image_nonempty j V
  ext r
  constructor
  · rintro ⟨s,rfl⟩
    exact ⟨(D.sheaf.restrictAppIso j V).hom s,rfl⟩
  · rintro ⟨s,rfl⟩
    refine ⟨(D.sheaf.restrictAppIso j V).inv s,?_⟩
    change D.sectionValue (j ''ᵁ V)
      ((D.sheaf.restrictAppIso j V).hom ((D.sheaf.restrictAppIso j V).inv s)) = _
    simp

/-- The exact fractional-principal description on the image of a chart
open, with the ordinary ambient regular-function embedding. -/
theorem mem_sectionValueRange_image_iff
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (V : Y.Opens) [Nonempty V] [Nonempty (j ''ᵁ V)] (r : X.functionField) :
    r ∈ D.sectionValueRange (j ''ᵁ V) ↔
      ∃ a : Γ(X,j ''ᵁ V), X.germToFunctionField (j ''ᵁ V) a *
        D.chartFrameRationalGenerator j e = r := by
  change r ∈ Set.range (D.sectionValue (j ''ᵁ V)) ↔ _
  rw [← D.alongSectionValue_range j V]
  constructor
  · rintro ⟨s,rfl⟩
    let a : Γ(Y,V) := e.hom.app V s
    refine ⟨(j.appIso V).inv a,?_⟩
    calc
      _ = openImmersionRegularToFunctionField j V a * D.chartFrameRationalGenerator j e :=
        congrArg (fun z : X.functionField => z * D.chartFrameRationalGenerator j e)
          (openImmersionRegularToFunctionField_eq_germ_image j V a).symm
      _ = _ := (D.alongSectionValue_frame j e V s).symm
  · rintro ⟨a,ha⟩
    let t : Γ(D.sheaf.restrict j,V) := e.inv.app V ((j.appIso V).hom a)
    refine ⟨t,?_⟩
    have he : (show Γ(Y,V) from e.hom.app V t) = (j.appIso V).hom a :=
      (D.chartFrameCoordinates j e V).apply_symm_apply ((j.appIso V).hom a)
    calc
      _ = openImmersionRegularToFunctionField j V (e.hom.app V t) *
          D.chartFrameRationalGenerator j e := D.alongSectionValue_frame j e V t
      _ = openImmersionRegularToFunctionField j V ((j.appIso V).hom a) *
          D.chartFrameRationalGenerator j e :=
        congrArg (fun r : Γ(Y,V) => openImmersionRegularToFunctionField j V r *
          D.chartFrameRationalGenerator j e) he
      _ = X.germToFunctionField (j ''ᵁ V) ((j.appIso V).inv ((j.appIso V).hom a)) *
          D.chartFrameRationalGenerator j e :=
        congrArg (fun z : X.functionField => z * D.chartFrameRationalGenerator j e)
          (openImmersionRegularToFunctionField_eq_germ_image j V ((j.appIso V).hom a))
      _ = X.germToFunctionField (j ''ᵁ V) a * D.chartFrameRationalGenerator j e :=
        congrArg (fun r : Γ(X,j ''ᵁ V) => X.germToFunctionField (j ''ᵁ V) r *
          D.chartFrameRationalGenerator j e) (CommRingCat.inv_hom_apply (j.appIso V) a)
      _ = r := ha

/-- The chart-frame formula holds on every smaller ambient open, not only
on opens presented as images in the statement. -/
theorem mem_sectionValueRange_iff_chartFrame
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (W : X.Opens) [Nonempty W] (hW : W≤j.opensRange) (r : X.functionField) :
    r ∈ D.sectionValueRange W ↔
      ∃ a : Γ(X,W), X.germToFunctionField W a *
        D.chartFrameRationalGenerator j e = r := by
  let V := j ⁻¹ᵁ W
  letI : Nonempty V := openImmersion_preimage_nonempty j W
  letI : Nonempty (j ''ᵁ V) := openImmersion_image_nonempty j V
  have himage : j ''ᵁ V=W := by
    rw [show V=j ⁻¹ᵁ W from rfl,j.image_preimage_eq_opensRange_inf,inf_eq_right.mpr hW]
  let P (U : X.Opens) : Prop := ∀ (hU : Nonempty U),
    letI : Nonempty U := hU
    r ∈ D.sectionValueRange U ↔
      ∃ a : Γ(X,U), X.germToFunctionField U a *
        D.chartFrameRationalGenerator j e = r
  have hP : P (j ''ᵁ V) := by
    intro hU
    letI := hU
    exact D.mem_sectionValueRange_image_iff j e V r
  have hQ : P W := Eq.mp (congrArg P himage) hP
  exact hQ inferInstance

theorem chartFrameRationalGenerator_mem_sectionValueRange
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (W : X.Opens) [Nonempty W] (hW : W≤j.opensRange) :
    D.chartFrameRationalGenerator j e ∈ D.sectionValueRange W := by
  apply (D.mem_sectionValueRange_iff_chartFrame j e W hW _).mpr
  exact ⟨1,by simp⟩

/-- A chart generator divided by another is an actual regular unit on
every nonempty open in their overlap. -/
theorem exists_chartFrameTransitionUnit (g : Z ⟶ X) [IsOpenImmersion g]
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (f : D.sheaf.restrict g ≅ SheafOfModules.unit Z.ringCatSheaf)
    (W : X.Opens) [Nonempty W] (hWj : W≤j.opensRange) (hWg : W≤g.opensRange) :
    ∃ a : Γ(X,W)ˣ, X.germToFunctionField W (a : Γ(X,W)) =
      D.chartFrameRationalGenerator j e / D.chartFrameRationalGenerator g f := by
  obtain ⟨a,ha⟩ := (D.mem_sectionValueRange_iff_chartFrame g f W hWg _).mp
    (D.chartFrameRationalGenerator_mem_sectionValueRange j e W hWj)
  obtain ⟨b,hb⟩ := (D.mem_sectionValueRange_iff_chartFrame j e W hWj _).mp
    (D.chartFrameRationalGenerator_mem_sectionValueRange g f W hWg)
  have hab : a*b=1 := by
    apply X.germToFunctionField_injective W
    rw [map_mul,map_one]
    apply mul_right_cancel₀ (D.chartFrameRationalGenerator_ne_zero j e)
    rw [mul_assoc,hb,ha,one_mul]
  exact ⟨⟨a,b,hab,by simpa only [mul_comm] using hab⟩,
    (eq_div_iff (D.chartFrameRationalGenerator_ne_zero g f)).mpr ha⟩

theorem chartFrameRatio_regularAt (g : Z ⟶ X) [IsOpenImmersion g]
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (f : D.sheaf.restrict g ≅ SheafOfModules.unit Z.ringCatSheaf)
    (x : X) (hxj : x∈j.opensRange) (hxg : x∈g.opensRange) :
    D.chartFrameRationalGenerator j e / D.chartFrameRationalGenerator g f ∈
      regularAtSubring X x := by
  let W := j.opensRange⊓g.opensRange
  letI : Nonempty W := ⟨⟨x,hxj,hxg⟩⟩
  obtain ⟨a,ha⟩ := D.exists_chartFrameTransitionUnit j g e f W inf_le_left inf_le_right
  rw [← ha]
  exact regular_germ_mem_regularAt X W a x ⟨hxj,hxg⟩

/-- A chosen generator of a chart frame is a unit on an open where the
actual fractional module equals the regular-function module. -/
theorem chartFrameGenerator_isUnit_of_range
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (W : X.Opens) [Nonempty W] (hW : W≤j.opensRange)
    (hregular : (D.sectionValueRange W : Set X.functionField)=
      Set.range (X.germToFunctionField W)) :
    ∃ a : Γ(X,W)ˣ, X.germToFunctionField W (a : Γ(X,W)) =
      D.chartFrameRationalGenerator j e := by
  have hq := D.chartFrameRationalGenerator_mem_sectionValueRange j e W hW
  change D.chartFrameRationalGenerator j e ∈ (D.sectionValueRange W : Set X.functionField) at hq
  rw [hregular] at hq
  obtain ⟨a,ha⟩ := hq
  have h1 : (1 : X.functionField)∈D.sectionValueRange W := by
    change (1 : X.functionField)∈(D.sectionValueRange W : Set X.functionField)
    rw [hregular]
    exact ⟨1,map_one _⟩
  obtain ⟨b,hb⟩ := (D.mem_sectionValueRange_iff_chartFrame j e W hW 1).mp h1
  have hab : a*b=1 := by
    apply X.germToFunctionField_injective W
    rw [map_mul,map_one,ha,mul_comm]
    exact hb
  exact ⟨⟨a,b,hab,by simpa only [mul_comm] using hab⟩,ha⟩

end PaperVerification.ToricSchemes.CartierData

#print axioms PaperVerification.ToricSchemes.CartierData.mem_sectionValueRange_iff_chartFrame
#print axioms PaperVerification.ToricSchemes.CartierData.exists_chartFrameTransitionUnit
#print axioms PaperVerification.ToricSchemes.CartierData.chartFrameGenerator_isUnit_of_range
end
-- END PaperVerification.ToricCartierChartValues
end

section
-- BEGIN PaperVerification.ToricCharacterRegularity



/-!
# Semigroup chart rings and character shifts inside the actual group algebra

The chart ring is the image of its genuine semigroup-algebra homomorphism
into k[M]. Its underlying module is proved to consist exactly of the
Laurent polynomials with support in the semigroup. Multiplication by a
Cartier character is an actual linear automorphism and translates the
exponent set. Arbitrary intersections preserve this exact support meaning.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open Set AddMonoidAlgebra
open scoped Pointwise

variable (k : Type*) [CommSemiring k]
variable {M : Type*} [AddCommMonoid M]

def monoidChartMap (S : AddSubmonoid M) :
    AddMonoidAlgebra k S →ₐ[k] AddMonoidAlgebra k M :=
  AddMonoidAlgebra.mapDomainAlgHom k k S.subtype

@[simp] theorem monoidChartMap_single (S : AddSubmonoid M) (m : S) (r : k) :
    monoidChartMap k S (single m r) = single (m : M) r := by
  simp [monoidChartMap]

theorem monoidChartMap_injective (S : AddSubmonoid M) :
    Function.Injective (monoidChartMap k S) :=
  AddMonoidAlgebra.mapDomain_injective Subtype.val_injective

/-- This is a genuine subalgebra of the group algebra, obtained as an
algebra-homomorphism image, rather than an assumed affine-chart model. -/
def monoidChartAlgebra (S : AddSubmonoid M) : Subalgebra k (AddMonoidAlgebra k M) :=
  (monoidChartMap k S).range

def monoidChartAlgebraEquiv (S : AddSubmonoid M) :
    AddMonoidAlgebra k S ≃ₐ[k] monoidChartAlgebra k S :=
  AlgEquiv.ofInjective (monoidChartMap k S) (monoidChartMap_injective k S)

theorem range_monoidChartMap (S : AddSubmonoid M) :
    LinearMap.range (monoidChartMap k S).toLinearMap = characterModule k (S : Set M) := by
  rw [← Submodule.map_top, ← (AddMonoidAlgebra.basis S k).span_eq,
    Submodule.map_span, characterModule_eq_span]
  congr 1
  ext f
  constructor
  · rintro ⟨g, ⟨m, rfl⟩, rfl⟩
    exact ⟨(m : M), m.property, by simp⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨AddMonoidAlgebra.basis S k ⟨m, hm⟩,
      Set.mem_range_self _, by simp⟩

theorem monoidChartAlgebra_toSubmodule (S : AddSubmonoid M) :
    (monoidChartAlgebra k S).toSubmodule = characterModule k (S : Set M) :=
  range_monoidChartMap k S

theorem mem_monoidChartAlgebra (S : AddSubmonoid M) (f : AddMonoidAlgebra k M) :
    f ∈ monoidChartAlgebra k S ↔ (f.coeff.support : Set M) ⊆ S := by
  change f ∈ (monoidChartAlgebra k S).toSubmodule ↔ _
  rw [monoidChartAlgebra_toSubmodule, mem_characterModule_iff]

theorem characterModule_iInter {ι : Sort*} (S : ι → Set M) :
    characterModule k (⋂ i, S i) = ⨅ i, characterModule k (S i) := by
  ext f
  simp only [Submodule.mem_iInf, mem_characterModule_iff, Set.subset_iInter_iff]

section Translation

variable {G : Type*} [AddCommGroup G]

/-- Multiplication by χ^v, with the genuine inverse multiplication by
χ^(-v). It acts on the full Laurent-character algebra. -/
def characterTranslation (v : G) : AddMonoidAlgebra k G ≃ₗ[k] AddMonoidAlgebra k G where
  toFun f := single v (1 : k) * f
  invFun f := single (-v) (1 : k) * f
  left_inv f := by simp [← mul_assoc, ← AddMonoidAlgebra.one_def]
  right_inv f := by simp [← mul_assoc, ← AddMonoidAlgebra.one_def]
  map_add' f g := mul_add _ _ _
  map_smul' r f := mul_smul_comm _ _ _

@[simp] theorem characterTranslation_apply (v : G) (f : AddMonoidAlgebra k G) :
    characterTranslation k v f = single v (1 : k) * f := rfl

@[simp] theorem characterTranslation_single (v m : G) (r : k) :
    characterTranslation k v (single m r) = single (v + m) r := by
  simp [characterTranslation]

@[simp] theorem characterTranslation_neg (v : G) :
    (characterTranslation k v).symm = characterTranslation k (-v) := by
  ext f
  rfl

/-- An actual principal character shift translates exactly the support
set, without a convexity, lattice-basis, or finite-generation assumption. -/
theorem map_characterTranslation (v : G) (S : Set G) :
    (characterModule k S).map (characterTranslation k v).toLinearMap =
      characterModule k ((fun m => v + m) '' S) := by
  rw [characterModule_eq_span, Submodule.map_span, characterModule_eq_span]
  congr 1
  simp only [Set.image_image, LinearEquiv.coe_coe, Function.comp_def,
    characterTranslation_single]

theorem mem_characterTranslation_image (v : G) (S : Set G) (f : AddMonoidAlgebra k G) :
    (∃ g ∈ characterModule k S, single v (1 : k) * g = f) ↔
      (f.coeff.support : Set G) ⊆ (fun m => v + m) '' S := by
  change f ∈ (characterModule k S).map (characterTranslation k v).toLinearMap ↔ _
  rw [map_characterTranslation, mem_characterModule_iff]

/-- The intersection of the actual principal chart modules has precisely
the intersection of their allowed exponent sets as its support condition. -/
theorem intersection_principal_character_modules {ι : Sort*}
    (S : ι → AddSubmonoid G) (v : ι → G) :
    (⨅ i, ((monoidChartAlgebra k (S i)).toSubmodule).map
      (characterTranslation k (v i)).toLinearMap) =
      characterModule k (⋂ i, (fun m => v i + m) '' (S i : Set G)) := by
  simp only [monoidChartAlgebra_toSubmodule, map_characterTranslation,
    characterModule_iInter]

end Translation

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.monoidChartAlgebra_toSubmodule
#print axioms PaperVerification.ToricCharacters.intersection_principal_character_modules
end
-- END PaperVerification.ToricCharacterRegularity
end

section
-- BEGIN PaperVerification.ToricSmoothChartAlgebra



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
end
-- END PaperVerification.ToricSmoothChartAlgebra
end

section
-- BEGIN PaperVerification.ToricExchange
/-!
# Quadratic exchange on decomposition fibers

The vertices are actual multisets of points of a set in an additive commutative group.
An edge replaces precisely two entries by two entries with the same sum.
No connectivity assumption is hidden in the definition of an edge or a fiber.
-/

namespace PaperVerification.ToricExchange

variable {M : Type*} [AddCommGroup M] (A : Set M)

/-- Sum of the ambient lattice vectors in a multiset of points of `A`. -/
def total (s : Multiset A) : M := (s.map Subtype.val).sum

@[simp] theorem total_zero : total A 0 = 0 := by simp [total]
@[simp] theorem total_cons (a : A) (s : Multiset A) :
    total A (a ::ₘ s) = (a : M) + total A s := by simp [total]
@[simp] theorem total_singleton (a : A) : total A {a} = (a : M) := by
  simp [total]
@[simp] theorem total_add (s t : Multiset A) :
    total A (s + t) = total A s + total A t := by simp [total]

/-- A single quadratic exchange, preserving all entries outside the selected pair. -/
def QuadraticMove (s t : Multiset A) : Prop :=
  ∃ (r : Multiset A) (a b c d : A),
    s = a ::ₘ b ::ₘ r ∧ t = c ::ₘ d ::ₘ r ∧
    (a : M) + b = (c : M) + d

/-- Connectivity by finitely many genuine quadratic exchanges. -/
def Connected (s t : Multiset A) : Prop :=
  Relation.ReflTransGen (QuadraticMove A) s t

namespace QuadraticMove

variable {A}

theorem symm {s t : Multiset A} (h : QuadraticMove A s t) : QuadraticMove A t s := by
  rcases h with ⟨r, a, b, c, d, hs, ht, he⟩
  exact ⟨r, c, d, a, b, ht, hs, he.symm⟩

theorem card_eq {s t : Multiset A} (h : QuadraticMove A s t) : s.card = t.card := by
  rcases h with ⟨r, a, b, c, d, rfl, rfl, he⟩
  simp

theorem total_eq {s t : Multiset A} (h : QuadraticMove A s t) : total A s = total A t := by
  rcases h with ⟨r, a, b, c, d, rfl, rfl, he⟩
  simpa only [total_cons, ← add_assoc] using congrArg (· + total A r) he

theorem add_right {s t : Multiset A} (h : QuadraticMove A s t) (u : Multiset A) :
    QuadraticMove A (s + u) (t + u) := by
  rcases h with ⟨r, a, b, c, d, rfl, rfl, he⟩
  exact ⟨r + u, a, b, c, d, by simp, by simp, he⟩

end QuadraticMove

namespace Connected

variable {A}

@[refl] theorem refl (s : Multiset A) : Connected A s s := Relation.ReflTransGen.refl

theorem single {s t : Multiset A} (h : QuadraticMove A s t) : Connected A s t :=
  Relation.ReflTransGen.single h

@[trans] theorem trans {r s t : Multiset A} (h : Connected A r s) (k : Connected A s t) :
    Connected A r t := Relation.ReflTransGen.trans h k

@[symm] theorem symm {s t : Multiset A} (h : Connected A s t) : Connected A t s := by
  induction h with
  | refl => exact refl _
  | @tail b c hbc hcd ih =>
    exact trans (single hcd.symm) ih

theorem card_eq {s t : Multiset A} (h : Connected A s t) : s.card = t.card := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact ih.trans h.card_eq

theorem total_eq {s t : Multiset A} (h : Connected A s t) : total A s = total A t := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact ih.trans h.total_eq

theorem add_right {s t : Multiset A} (h : Connected A s t) (u : Multiset A) :
    Connected A (s + u) (t + u) := by
  induction h with
  | refl => exact refl _
  | tail _ h ih => exact trans ih (single (h.add_right u))

theorem cons {s t : Multiset A} (h : Connected A s t) (a : A) :
    Connected A (a ::ₘ s) (a ::ₘ t) := by
  have h' := h.add_right {a}
  rw [add_comm s {a}, add_comm t {a}, Multiset.singleton_add, Multiset.singleton_add] at h'
  exact h' 

end Connected

/-- The midpoint decomposition property needed in the all-degree exchange induction.
For lattice points of a convex polytope this follows from convexity and IDP. -/
def MidpointDecomposition : Prop :=
  ∀ (u v : Multiset A), 0 < u.card → u.card = v.card → ∀ z : M,
    z + z = total A u + total A v →
    ∃ w : Multiset A, w.card = u.card ∧ total A w = z

/-- The local triple-reduction conclusion supplied by the parity and adjoint arguments. -/
def TripleReduction : Prop :=
  ∀ a b c : A, ∃ p q : A,
    Connected A (a ::ₘ b ::ₘ c ::ₘ 0) (p ::ₘ q ::ₘ q ::ₘ 0)

/-- A prescribed parity for the first summand creates a repeated entry in two exchanges. -/
theorem triple_reduction_of_parity {a b c p q e : A}
    (hab : (a : M) + b = (p : M) + q)
    (hpc : (p : M) + c = (e : M) + e) :
    Connected A (a ::ₘ b ::ₘ c ::ₘ 0) (q ::ₘ e ::ₘ e ::ₘ 0) := by
  have h₁ : Connected A (a ::ₘ b ::ₘ c ::ₘ 0) (p ::ₘ q ::ₘ c ::ₘ 0) :=
    Connected.single ⟨c ::ₘ 0, a, b, p, q, rfl, rfl, hab⟩
  have h₂ : Connected A (p ::ₘ q ::ₘ c ::ₘ 0) (q ::ₘ e ::ₘ e ::ₘ 0) :=
    Connected.single ⟨q ::ₘ 0, p, c, e, e,
      by simp only [Multiset.cons_swap q c],
      by simp only [Multiset.cons_swap q e], hpc⟩
  exact h₁.trans h₂

/-- The geometric portion of Proposition 2.1, expressed by the minimal-face map.
`parity` is prescribed parity plus midpoint convexity on each face; `adjoint` moves
one entry into the relative interior of a proper face. Both hypotheses are equations
and face relations, not assumptions of exchange connectivity. -/
theorem tripleReduction_of_face_data {F : Type*} [SemilatticeSup F] [OrderTop F]
    (face : A → F)
    (parity : ∀ a b c : A, face c ≤ face a ⊔ face b →
      ∃ p q e : A, (a : M) + b = (p : M) + q ∧ (p : M) + c = (e : M) + e)
    (adjoint : ∀ a b : A, face a ⊔ face b ≠ ⊤ →
      ∃ u v : A, (a : M) + b = (u : M) + v ∧
        face u = face a ⊔ face b ∧ face v ≤ face a ⊔ face b) :
    TripleReduction A := by
  intro a b c
  by_cases hc : face c ≤ face a ⊔ face b
  · obtain ⟨p, q, e, hab, hpc⟩ := parity a b c hc
    exact ⟨q, e, triple_reduction_of_parity A hab hpc⟩
  · have hproper : face a ⊔ face b ≠ ⊤ := by
      intro htop
      apply hc
      rw [htop]
      exact le_top
    obtain ⟨u, v, huv, huf, hvf⟩ := adjoint a b hproper
    have hvc : face v ≤ face u ⊔ face c := le_sup_of_le_left (by simpa only [huf] using hvf)
    obtain ⟨p, q, e, hup, hpv⟩ := parity u c v hvc
    have h₁ : Connected A (a ::ₘ b ::ₘ c ::ₘ 0) (u ::ₘ v ::ₘ c ::ₘ 0) :=
      Connected.single ⟨c ::ₘ 0, a, b, u, v, rfl, rfl, huv⟩
    have h₂ : Connected A (u ::ₘ v ::ₘ c ::ₘ 0) (q ::ₘ e ::ₘ e ::ₘ 0) := by
      simpa only [Multiset.cons_swap c v] using triple_reduction_of_parity A hup hpv
    exact ⟨q, e, h₁.trans h₂⟩

theorem exists_repeated (htriple : TripleReduction A) (s : Multiset A)
    (hs : 3 ≤ s.card) :
    ∃ (b : A) (u : Multiset A), Connected A s (b ::ₘ b ::ₘ u) := by
  obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp (show 0 < s.card by omega)
  obtain ⟨r, rfl⟩ := Multiset.exists_cons_of_mem ha
  obtain ⟨b, hb⟩ := Multiset.card_pos_iff_exists_mem.mp (show 0 < r.card by simp at hs; omega)
  obtain ⟨r', rfl⟩ := Multiset.exists_cons_of_mem hb
  obtain ⟨c, hc⟩ := Multiset.card_pos_iff_exists_mem.mp (show 0 < r'.card by simp at hs; omega)
  obtain ⟨r'', rfl⟩ := Multiset.exists_cons_of_mem hc
  obtain ⟨p, q, h⟩ := htriple a b c
  refine ⟨q, p ::ₘ r'', ?_⟩
  have h' := h.add_right r''
  simpa only [Multiset.cons_add, Multiset.zero_add, Multiset.cons_swap p q] using h'

theorem connected_of_card_le_two (s t : Multiset A) (hn : s.card ≤ 2)
    (hc : s.card = t.card) (hz : total A s = total A t) : Connected A s t := by
  interval_cases hs : s.card
  · have hs0 : s = 0 := Multiset.card_eq_zero.mp hs
    have ht0 : t = 0 := Multiset.card_eq_zero.mp (show t.card = 0 by omega)
    subst s; subst t
    exact Connected.refl _
  · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp hs
    obtain ⟨b, rfl⟩ := Multiset.card_eq_one.mp (by simpa using hc.symm)
    have hab : a = b := Subtype.ext (by simpa [total] using hz)
    subst b
    exact Connected.refl _
  · obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp hs
    obtain ⟨c, d, rfl⟩ := Multiset.card_eq_two.mp (by simpa using hc.symm)
    exact Connected.single ⟨0, a, b, c, d, rfl, rfl, by simpa [total] using hz⟩

/-- Every decomposition fiber is connected once midpoint decomposition and the
local triple-reduction property are available. The induction is over all natural degrees. -/
theorem all_fibers_connected (hmid : MidpointDecomposition A) (htriple : TripleReduction A)
    (s t : Multiset A) (hc : s.card = t.card) (hz : total A s = total A t) :
    Connected A s t := by
  have main : ∀ n (s t : Multiset A), s.card = n → t.card = n →
      total A s = total A t → Connected A s t := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro s t hs ht hz
      by_cases hn : n ≤ 2
      · exact connected_of_card_le_two A s t (by simpa only [hs] using hn) (hs.trans ht.symm) hz
      have hn3 : 3 ≤ n := by omega
      obtain ⟨b, u, hsu⟩ := exists_repeated A htriple s (by simpa only [hs] using hn3)
      obtain ⟨d, v, htv⟩ := exists_repeated A htriple t (by simpa only [ht] using hn3)
      have hu : u.card + 2 = n := by simpa [hs, Nat.add_assoc] using hsu.card_eq.symm
      have hv : v.card + 2 = n := by simpa [ht, Nat.add_assoc] using htv.card_eq.symm
      have hsu' : total A s = (b : M) + b + total A u := by
        simpa only [total_cons, ← add_assoc] using hsu.total_eq
      have htv' : total A t = (d : M) + d + total A v := by
        simpa only [total_cons, ← add_assoc] using htv.total_eq
      let q : M := total A s - b - d
      have hq : q + q = total A u + total A v := by
        dsimp [q]
        calc
          total A s - b - d + (total A s - b - d) =
              (total A s - b - b) + (total A t - d - d) := by rw [← hz]; abel
          _ = total A u + total A v := by rw [hsu', htv']; abel
      obtain ⟨g, hg, hgz⟩ := hmid u v (by omega) (by omega) q hq
      have hl : Connected A (b ::ₘ u) (d ::ₘ g) := by
        apply ih (n - 1) (by omega)
        · simp; omega
        · simp; omega
        · simp only [total_cons, hgz]
          dsimp [q]
          rw [hsu']
          abel
      have hr : Connected A (b ::ₘ g) (d ::ₘ v) := by
        apply ih (n - 1) (by omega)
        · simp; omega
        · simp; omega
        · simp only [total_cons, hgz]
          dsimp [q]
          rw [hz, htv']
          abel
      have hmiddle : Connected A (b ::ₘ b ::ₘ u) (d ::ₘ d ::ₘ v) :=
        (hl.cons b).trans (by simpa only [Multiset.cons_swap b d] using hr.cons d)
      exact hsu.trans (hmiddle.trans htv.symm)
  exact main s.card s t rfl hc.symm hz

end PaperVerification.ToricExchange
-- END PaperVerification.ToricExchange
end

section
-- BEGIN PaperVerification.ToricIdeal
/-!
# Toric ideals and quadratic exchange

This file uses genuine semigroup algebras and ideal kernels. The monomials of the
polynomial algebra are first indexed by multisets, then identified with Mathlib's
`MvPolynomial` by the multiplicity equivalence.
-/

noncomputable section

namespace PaperVerification.ToricExchange

open AddMonoidAlgebra

section GeneralKernel

variable {R S T : Type*} [CommRing R] [AddCommMonoid S] [AddCommMonoid T]

/-- The ideal of all binomials whose exponents have the same image. -/
def fiberIdeal (f : S →+ T) : Ideal (AddMonoidAlgebra R S) :=
  Ideal.span {p | ∃ s t : S, f s = f t ∧ p = single s 1 - single t 1}

/-- The kernel of a semigroup-algebra map is generated by its fiber binomials.
This holds over every commutative coefficient ring. -/
theorem kernel_mapDomain_eq_fiberIdeal (f : S →+ T) :
    RingHom.ker (AddMonoidAlgebra.mapDomainRingHom R f) = fiberIdeal (R := R) f := by
  classical
  apply le_antisymm
  · intro p hp
    let I : Ideal (AddMonoidAlgebra R S) := fiberIdeal f
    let q := Ideal.Quotient.mk I
    let rep : T → S := Function.invFun f
    have hrep (s : S) : f (rep (f s)) = f s := Function.apply_invFun_apply (f := f) (a := s)
    have hsingle (s : S) (r : R) : q (single s r) = q (single (rep (f s)) r) := by
      apply Ideal.Quotient.eq.mpr
      have hgen : single s (1 : R) - single (rep (f s)) 1 ∈ I :=
        Ideal.subset_span ⟨s, rep (f s), (hrep s).symm, rfl⟩
      have hmul := I.mul_mem_left (single (0 : S) r) hgen
      simpa only [mul_sub, single_mul_single, zero_add, mul_one] using hmul
    let g : T → R → AddMonoidAlgebra R S ⧸ I := fun t r => q (single (rep t) r)
    have hg0 (t : T) : g t 0 = 0 := by simp [g]
    have hgadd (t : T) (r₁ r₂ : R) : g t (r₁ + r₂) = g t r₁ + g t r₂ := by
      simp [g, single_add]
    have hfactor : q p = (Finsupp.mapDomain f p.coeff).sum g := by
      calc
        q p = q (p.coeff.sum single) := congrArg q p.sum_coeff_single.symm
        _ = p.coeff.sum (fun s r => q (single s r)) := map_finsuppSum q _ _
        _ = p.coeff.sum (fun s r => g (f s) r) := by
          apply Finsupp.sum_congr
          intro s hs
          exact hsingle s _
        _ = (Finsupp.mapDomain f p.coeff).sum g :=
          (Finsupp.sum_mapDomain_index hg0 hgadd).symm
    have hcoeff : Finsupp.mapDomain f p.coeff = 0 := by
      have hp' : AddMonoidAlgebra.mapDomain f p = 0 := hp
      simpa [AddMonoidAlgebra.mapDomain] using congrArg AddMonoidAlgebra.coeff hp'
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q p = 0
    rw [hfactor, hcoeff]
    simp
  · apply Ideal.span_le.mpr
    rintro p ⟨s, t, hst, rfl⟩
    change (AddMonoidAlgebra.mapDomainRingHom R f) (single s 1 - single t 1) = 0
    rw [map_sub]
    simp [AddMonoidAlgebra.mapDomainRingHom, hst]

end GeneralKernel

section QuadraticKernel

variable {M : Type*} [AddCommGroup M] (A : Set M)
variable (R : Type*) [CommRing R]

/-- The degree and lattice sum of a multiset monomial. -/
def grade : Multiset A →+ M × ℕ where
  toFun s := (total A s, s.card)
  map_zero' := by simp
  map_add' s t := by simp

/-- The homogeneous toric map before the multiset/multiplicity identification. -/
noncomputable def multisetToricMap : AddMonoidAlgebra R (Multiset A) →+* AddMonoidAlgebra R (M × ℕ) :=
  AddMonoidAlgebra.mapDomainRingHom R (grade A)

/-- The actual ideal generated by equal-sum quadratic binomials. -/
def quadraticIdeal : Ideal (AddMonoidAlgebra R (Multiset A)) :=
  Ideal.span {p | ∃ a b c d : A, (a : M) + b = (c : M) + d ∧
    p = single (a ::ₘ b ::ₘ 0) 1 - single (c ::ₘ d ::ₘ 0) 1}

theorem move_binomial_mem {s t : Multiset A} (h : QuadraticMove A s t) :
    single s (1 : R) - single t 1 ∈ quadraticIdeal A R := by
  rcases h with ⟨r, a, b, c, d, rfl, rfl, he⟩
  have hgen : single (a ::ₘ b ::ₘ 0) (1 : R) - single (c ::ₘ d ::ₘ 0) 1 ∈
      quadraticIdeal A R := Ideal.subset_span ⟨a, b, c, d, he, rfl⟩
  have hmul := (quadraticIdeal A R).mul_mem_right (single r 1) hgen
  simpa only [sub_mul, single_mul_single, one_mul, Multiset.cons_add,
    Multiset.zero_add] using hmul

theorem connected_binomial_mem {s t : Multiset A} (h : Connected A s t) :
    single s (1 : R) - single t 1 ∈ quadraticIdeal A R := by
  induction h with
  | refl => simp
  | @tail b c hbc hcd ih =>
    have hsum := (quadraticIdeal A R).add_mem ih (move_binomial_mem A R hcd)
    simpa only [sub_add_sub_cancel] using hsum

/-- Connectivity of all fibers gives quadratic generation of the genuine toric kernel. -/
theorem kernel_eq_quadraticIdeal
    (hconn : ∀ s t : Multiset A, s.card = t.card → total A s = total A t → Connected A s t) :
    RingHom.ker (multisetToricMap A R) = quadraticIdeal A R := by
  rw [multisetToricMap, kernel_mapDomain_eq_fiberIdeal]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro p ⟨s, t, he, rfl⟩
    exact connected_binomial_mem A R (hconn s t (congrArg Prod.snd he) (congrArg Prod.fst he))
  · apply Ideal.span_le.mpr
    rintro p ⟨a, b, c, d, he, rfl⟩
    apply Ideal.subset_span
    refine ⟨a ::ₘ b ::ₘ 0, c ::ₘ d ::ₘ 0, ?_, rfl⟩
    apply Prod.ext
    · simpa [grade] using he
    · simp [grade]

/-- The complete algebraic exchange criterion, in every degree and over every
commutative coefficient ring. -/
theorem quadratic_generation_of_midpoint_and_triples
    (hmid : MidpointDecomposition A) (htriple : TripleReduction A) :
    RingHom.ker (multisetToricMap A R) = quadraticIdeal A R :=
  kernel_eq_quadraticIdeal A R (all_fibers_connected A hmid htriple)

/-- The multiplicity equivalence identifies multiset monomials with Mathlib polynomials. -/
noncomputable def polynomialEquiv : AddMonoidAlgebra R (Multiset A) ≃+* MvPolynomial A R := by
  classical
  exact AddMonoidAlgebra.mapDomainRingEquiv R Multiset.toFinsupp

/-- The faithful homogeneous toric map, `X a ↦ χ^a t`, with target exponent `(a,1)`. -/
noncomputable def toricMap : MvPolynomial A R →+* AddMonoidAlgebra R (M × ℕ) :=
  (multisetToricMap A R).comp (polynomialEquiv A R).symm.toRingHom

@[simp] theorem polynomialEquiv_singleton (a : A) :
    polynomialEquiv A R (single ({a} : Multiset A) 1) = MvPolynomial.X a := by
  classical
  simp [polynomialEquiv, MvPolynomial.X, MvPolynomial.monomial,
    AddMonoidAlgebra.lsingle]

@[simp] theorem polynomialEquiv_constant (r : R) :
    polynomialEquiv A R (single (0 : Multiset A) r) = MvPolynomial.C r := by
  classical
  simp [polynomialEquiv, MvPolynomial.C, MvPolynomial.monomial,
    AddMonoidAlgebra.lsingle]

@[simp] theorem polynomialEquiv_symm_C (r : R) :
    (polynomialEquiv A R).symm (MvPolynomial.C r) = single (0 : Multiset A) r := by
  apply (polynomialEquiv A R).injective
  simp

@[simp] theorem polynomialEquiv_pair (a b : A) :
    polynomialEquiv A R (single (a ::ₘ b ::ₘ 0) 1) =
      MvPolynomial.X a * MvPolynomial.X b := by
  have he : (single (a ::ₘ b ::ₘ 0) 1 : AddMonoidAlgebra R (Multiset A)) =
      single ({a} : Multiset A) 1 * single ({b} : Multiset A) 1 := by
    simp [single_mul_single]
  rw [he, map_mul, polynomialEquiv_singleton, polynomialEquiv_singleton]

@[simp] theorem polynomialEquiv_symm_X (a : A) :
    (polynomialEquiv A R).symm (MvPolynomial.X a) = single ({a} : Multiset A) 1 := by
  apply (polynomialEquiv A R).injective
  simp

@[simp] theorem toricMap_X (a : A) :
    toricMap A R (MvPolynomial.X a) = single ((a : M), 1) 1 := by
  simp [toricMap, multisetToricMap, AddMonoidAlgebra.mapDomainRingHom, grade]

@[simp] theorem toricMap_C (r : R) :
    toricMap A R (MvPolynomial.C r) = single ((0 : M), (0 : ℕ)) r := by
  simp [toricMap, multisetToricMap, AddMonoidAlgebra.mapDomainRingHom, grade]

/-- The conventional quadratic ideal in Mathlib's polynomial ring. -/
def polynomialQuadraticIdeal : Ideal (MvPolynomial A R) :=
  Ideal.span {p | ∃ a b c d : A, (a : M) + b = (c : M) + d ∧
    p = MvPolynomial.X a * MvPolynomial.X b - MvPolynomial.X c * MvPolynomial.X d}

theorem quadraticIdeal_map_polynomialEquiv :
    (quadraticIdeal A R).map (polynomialEquiv A R).toRingHom = polynomialQuadraticIdeal A R := by
  have hmap (a b c d : A) :
      (polynomialEquiv A R).toRingHom
        (single (a ::ₘ b ::ₘ 0) 1 - single (c ::ₘ d ::ₘ 0) 1) =
        MvPolynomial.X a * MvPolynomial.X b - MvPolynomial.X c * MvPolynomial.X d := by
    change polynomialEquiv A R (_ - _) = _
    rw [map_sub, polynomialEquiv_pair, polynomialEquiv_pair]
  rw [quadraticIdeal, Ideal.map_span, polynomialQuadraticIdeal]
  congr 1
  ext p
  constructor
  · rintro ⟨q, ⟨a, b, c, d, he, rfl⟩, rfl⟩
    exact ⟨a, b, c, d, he, hmap a b c d⟩
  · rintro ⟨a, b, c, d, he, rfl⟩
    exact ⟨single (a ::ₘ b ::ₘ 0) 1 - single (c ::ₘ d ::ₘ 0) 1,
      ⟨a, b, c, d, he, rfl⟩, hmap a b c d⟩

/-- Quadratic generation stated in Mathlib's `MvPolynomial`, with no loss of degree
or coefficient-field generality. -/
theorem polynomial_kernel_eq_quadrics (hmid : MidpointDecomposition A)
    (htriple : TripleReduction A) :
    RingHom.ker (toricMap A R) = polynomialQuadraticIdeal A R := by
  rw [← quadraticIdeal_map_polynomialEquiv]
  have hk := quadratic_generation_of_midpoint_and_triples A R hmid htriple
  ext p
  constructor
  · intro hp
    have hp' : (polynomialEquiv A R).symm p ∈ quadraticIdeal A R := by
      rw [← hk]
      exact hp
    have hm := Ideal.mem_map_of_mem (polynomialEquiv A R).toRingHom hp'
    simpa using hm
  · intro hp
    obtain ⟨q, hq, rfl⟩ := (Ideal.mem_map_iff_of_surjective
      (polynomialEquiv A R).toRingHom (polynomialEquiv A R).surjective).mp hp
    change multisetToricMap A R ((polynomialEquiv A R).symm ((polynomialEquiv A R) q)) = 0
    simp only [RingEquiv.symm_apply_apply]
    change q ∈ RingHom.ker (multisetToricMap A R)
    rw [hk]
    exact hq

/-- The canonical equivalence between exponent pairs `(a,k)` and `χ^a t^k`. -/
noncomputable def characterPolynomialEquiv :
    AddMonoidAlgebra R (M × ℕ) ≃+* Polynomial (AddMonoidAlgebra R M) :=
  (AddMonoidAlgebra.mapDomainRingEquiv R (AddEquiv.prodComm : M × ℕ ≃+ ℕ × M)).trans
    (AddMonoidAlgebra.curryRingEquiv.trans (Polynomial.toFinsuppIso _).symm)

@[simp] theorem characterPolynomialEquiv_single (m : M) (k : ℕ) (r : R) :
    characterPolynomialEquiv (M := M) R (single (m, k) r) =
      Polynomial.monomial k (single m r) := by
  simpa [characterPolynomialEquiv, Polynomial.toFinsuppIso] using
    (Polynomial.single_eq_monomial k (single m r))

/-- The toric homomorphism with exactly the paper's target `R[M][t]`. -/
noncomputable def paperToricMap :
    MvPolynomial A R →+* Polynomial (AddMonoidAlgebra R M) :=
  (characterPolynomialEquiv (M := M) R).toRingHom.comp (toricMap A R)

/-- Each generator is sent to the character times the homogenizing variable. -/
@[simp] theorem paperToricMap_X (a : A) :
    paperToricMap A R (MvPolynomial.X a) =
      Polynomial.C (single (a : M) 1) * Polynomial.X := by
  simp [paperToricMap, Polynomial.C_mul_X_eq_monomial]

/-- The coefficient ring is included as constant characters and constant polynomials. -/
@[simp] theorem paperToricMap_C (r : R) :
    paperToricMap A R (MvPolynomial.C r) = Polynomial.C (single (0 : M) r) := by
  simp [paperToricMap, Polynomial.monomial_zero_left]

/-- The exchange criterion yields the paper's ideal equality in the conventional target. -/
theorem paper_kernel_eq_quadrics (hmid : MidpointDecomposition A)
    (htriple : TripleReduction A) :
    RingHom.ker (paperToricMap A R) = polynomialQuadraticIdeal A R := by
  rw [paperToricMap, RingHom.ker_comp_of_injective _
    (characterPolynomialEquiv (M := M) R).injective]
  exact polynomial_kernel_eq_quadrics A R hmid htriple

end QuadraticKernel

end PaperVerification.ToricExchange
end
-- END PaperVerification.ToricIdeal
end

section
-- BEGIN PaperVerification.ToricConvexity
/-!
# The convexity and integer-decomposition bridge

This file makes the geometric hypothesis in the exchange induction explicit.
The degree-`k` polytope is the ordinary scalar dilate `k • P`, represented by
an existential witness in `P`. The integer-decomposition property is required at
all positive natural degrees, with no bounded-degree restriction.
-/

noncomputable section

namespace PaperVerification.ToricExchange

variable {M V : Type*} [AddCommGroup M] [AddCommGroup V] [Module ℝ V]
variable (embedding : M →+ V) (P : Set V)

/-- The actual set of lattice points in a real convex set. -/
def latticePoints : Set M := embedding ⁻¹' P

/-- Integer decomposition in every positive degree, for the specified lattice embedding. -/
def IntegerDecompositionProperty : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ z : M,
    (∃ x ∈ P, embedding z = (k : ℝ) • x) →
    ∃ s : Multiset (latticePoints embedding P), s.card = k ∧
      total (latticePoints embedding P) s = z

/-- The arithmetic mean of a nonempty multiset of lattice points lies in the
convex set containing those points. -/
theorem average_total_mem (hP : Convex ℝ P)
    (s : Multiset (latticePoints embedding P)) (hs : 0 < s.card) :
    (s.card : ℝ)⁻¹ • embedding (total (latticePoints embedding P) s) ∈ P := by
  classical
  let l := s.toList
  have hn : (s.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
  have hweights : (∑ _i : Fin l.length, (s.card : ℝ)⁻¹) = 1 := by
    simp [l, Multiset.length_toList, nsmul_eq_mul, mul_inv_cancel₀ hn]
  have hsum : (∑ i : Fin l.length, embedding ((l[i.1] : latticePoints embedding P) : M)) =
      embedding (total (latticePoints embedding P) s) := by
    rw [Fin.sum_univ_fun_getElem l
      (fun a : latticePoints embedding P => embedding (a : M))]
    change (s.toList.map (fun a : latticePoints embedding P => embedding (a : M))).sum = _
    rw [Multiset.sum_map_toList s
      (fun a : latticePoints embedding P => embedding (a : M))]
    simp only [total, map_multiset_sum, Multiset.map_map]
    rfl
  have hmean := hP.sum_mem (t := Finset.univ)
    (w := fun _i : Fin l.length => (s.card : ℝ)⁻¹)
    (z := fun i : Fin l.length => embedding ((l[i.1] : latticePoints embedding P) : M))
    (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)) hweights
    (fun i _ => (l[i.1]).property)
  simpa only [← Finset.smul_sum, hsum] using hmean

/-- Convexity and the actual integer-decomposition property imply precisely the
midpoint decomposition used by the all-degree exchange proof. -/
theorem midpointDecomposition_of_convex_idp (hP : Convex ℝ P)
    (hidp : IntegerDecompositionProperty embedding P) :
    MidpointDecomposition (latticePoints embedding P) := by
  intro u v hu huv z hz
  have hv : 0 < v.card := by omega
  have huP := average_total_mem embedding P hP u hu
  have hvP := average_total_mem embedding P hP v hv
  rw [← huv] at hvP
  have hz' : embedding z + embedding z =
      embedding (total (latticePoints embedding P) u) +
      embedding (total (latticePoints embedding P) v) := by
    simpa using congrArg embedding hz
  have hhalf : (1 / 2 : ℝ) •
      (embedding (total (latticePoints embedding P) u) +
        embedding (total (latticePoints embedding P) v)) = embedding z := by
    rw [← hz',← two_smul ℝ (embedding z),smul_smul]
    norm_num
  have hw := hP huP hvP (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show 0 ≤ (1 / 2 : ℝ) by norm_num) (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hw' : (u.card : ℝ)⁻¹ • embedding z ∈ P := by
    convert hw using 1
    rw [← hhalf]
    simp only [smul_add,smul_comm (u.card : ℝ)⁻¹ (1 / 2 : ℝ)]
  apply hidp u.card (by omega) z
  refine ⟨(u.card : ℝ)⁻¹ • embedding z, hw', ?_⟩
  have hn : (u.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hu)
  simp [smul_smul, mul_inv_cancel₀ hn]

/-- Congruence modulo twice the ambient lattice, stated without quotient notation. -/
def SameParity (a b : M) : Prop := ∃ w : M, a - b = w + w

/-- For points in an affine face, ambient parity is exactly parity in the saturated
face lattice: the halving witness automatically lies in the real face direction. -/
theorem sameParity_iff_saturated_direction (W : Submodule ℝ V) (p c : M)
    (hdirection : embedding (p - c) ∈ W) :
    SameParity p c ↔ ∃ w : M, embedding w ∈ W ∧ p - c = w + w := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_, hw⟩
    have htwice : embedding w + embedding w ∈ W := by
      simpa only [hw, map_add] using hdirection
    have hhalf := W.smul_mem (1 / 2 : ℝ) htwice
    convert hhalf using 1
    rw [← two_smul ℝ (embedding w),smul_smul]
    norm_num
  · rintro ⟨w, _, hw⟩
    exact ⟨w, hw⟩

/-- Convexity turns an integral parity midpoint into an actual lattice point of the polytope. -/
theorem midpoint_of_sameParity (hP : Convex ℝ P)
    (p c : latticePoints embedding P) (hpc : SameParity (p : M) c) :
    ∃ e : latticePoints embedding P, (p : M) + c = (e : M) + e := by
  obtain ⟨w, hw⟩ := hpc
  have he : (p : M) + c = (c + w) + (c + w) := by
    calc
      (p : M) + c = (p - c) + (c + c) := by abel
      _ = (w + w) + (c + c) := by rw [hw]
      _ = (c + w) + (c + w) := by abel
  have hmid := hP p.property c.property (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show 0 ≤ (1 / 2 : ℝ) by norm_num) (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have he' : embedding p + embedding c = embedding (c + w) + embedding (c + w) := by
    simpa using congrArg embedding he
  have hm : embedding (c + w) ∈ P := by
    convert hmid using 1
    rw [← smul_add, he',← two_smul ℝ (embedding (c + w)),smul_smul]
    norm_num
  exact ⟨⟨c + w, hm⟩, he⟩

/-- The parity and proper-face adjoint data imply triple reduction using actual convexity,
so no midpoint-closure axiom is needed. -/
theorem tripleReduction_of_convex_face_data (hP : Convex ℝ P)
    {F : Type*} [SemilatticeSup F] [OrderTop F]
    (face : latticePoints embedding P → F)
    (parity : ∀ a b c : latticePoints embedding P, face c ≤ face a ⊔ face b →
      ∃ p q : latticePoints embedding P,
        (a : M) + b = (p : M) + q ∧ SameParity (p : M) c)
    (adjoint : ∀ a b : latticePoints embedding P, face a ⊔ face b ≠ ⊤ →
      ∃ u v : latticePoints embedding P, (a : M) + b = (u : M) + v ∧
        face u = face a ⊔ face b ∧ face v ≤ face a ⊔ face b) :
    TripleReduction (latticePoints embedding P) := by
  apply tripleReduction_of_face_data (latticePoints embedding P) face ?_ adjoint
  intro a b c hc
  obtain ⟨p, q, he, hp⟩ := parity a b c hc
  obtain ⟨e, hmid⟩ := midpoint_of_sameParity embedding P hP p c hp
  exact ⟨p, q, e, he, hmid⟩

end PaperVerification.ToricExchange
end
-- END PaperVerification.ToricConvexity
end

section
-- BEGIN PaperVerification.ToricCriterion
/-!
# The complete exchange criterion with explicit geometric inputs

This is the algebraic reduction underlying Proposition 2.1. The face map
and its parity/adjoint properties are explicit inputs: they are not constructed from
smoothness or an edge-length bound in this file.
-/

namespace PaperVerification.ToricExchange

variable {M V : Type*} [AddCommGroup M] [AddCommGroup V] [Module ℝ V]
variable (embedding : M →+ V) (P : Set V)
variable (R : Type*) [CommRing R]

/-- Convexity, full IDP, face parity, and proper-face adjoint decomposition yield
quadratic generation in the conventional ring `R[X_a] → R[M][t]`.
All natural degrees and every commutative coefficient ring are included. -/
theorem quadratic_generation_of_convex_face_data (hP : Convex ℝ P)
    (hidp : IntegerDecompositionProperty embedding P)
    {F : Type*} [SemilatticeSup F] [OrderTop F]
    (face : latticePoints embedding P → F)
    (parity : ∀ a b c : latticePoints embedding P, face c ≤ face a ⊔ face b →
      ∃ p q : latticePoints embedding P,
        (a : M) + b = (p : M) + q ∧ SameParity (p : M) c)
    (adjoint : ∀ a b : latticePoints embedding P, face a ⊔ face b ≠ ⊤ →
      ∃ u v : latticePoints embedding P, (a : M) + b = (u : M) + v ∧
        face u = face a ⊔ face b ∧ face v ≤ face a ⊔ face b) :
    RingHom.ker (paperToricMap (latticePoints embedding P) R) =
      polynomialQuadraticIdeal (latticePoints embedding P) R :=
  paper_kernel_eq_quadrics (latticePoints embedding P) R
    (midpointDecomposition_of_convex_idp embedding P hP hidp)
    (tripleReduction_of_convex_face_data embedding P hP face parity adjoint)

end PaperVerification.ToricExchange
-- END PaperVerification.ToricCriterion
end

#eval "TORIC_DICTIONARY_PART_03_EOF"
