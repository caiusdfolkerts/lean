module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Data.Int.Cast.Lemmas
public import PaperVerification.ToricCharacterSubrepresentations

@[expose] public section

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
  rw [← Category.assoc, ← tensorHom_def']
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
