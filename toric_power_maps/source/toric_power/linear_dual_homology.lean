module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.CategoryTheory.Abelian.Injective.Basic
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Exact scalar duality for chain complexes

Linear Hom into an injective coefficient object preserves homology as a
module-valued functor. Its compatibility with forgetting scalars is used
only to prove exactness; the resulting comparison remains scalar-linear.
For vector spaces, injectivity is proved from an actual linear left inverse
of every injective linear map. No finite-dimensionality assumption enters.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace ToricPower

universe w v u

section LinearCategory

variable (k : Type u) [CommRing k]
  {C : Type w} [Category.{v} C] [Abelian C] [Linear k C]

/-- Exactness of linear Hom into an injective object retains its scalar
structure, by reflection of limits and colimits through the forgetful functor. -/
instance linearYonedaObj_preservesHomology_of_injective (J : C) [Injective J] :
    ((linearYoneda k C).obj J).PreservesHomology := by
  let F := (linearYoneda k C).obj J
  let G := forget₂ (ModuleCat.{v} k) AddCommGrpCat.{v}
  have hFG : F ⋙ G = preadditiveYonedaObj J ⋙
      forget₂ (ModuleCat.{v} (End J)) AddCommGrpCat.{v} := rfl
  letI : PreservesFiniteLimits (F ⋙ G) := by rw [hFG]; infer_instance
  letI : PreservesFiniteColimits (F ⋙ G) := by rw [hFG]; infer_instance
  letI : ReflectsFiniteColimits G :=
    { reflects J _ _ := ModuleCat.reflectsColimitsOfShape.{v, u, 0, 0} (R := k) (J := J) }
  letI : PreservesFiniteLimits F := preservesFiniteLimits_of_reflects_of_preserves F G
  letI : PreservesFiniteColimits F := preservesFiniteColimits_of_reflects_of_preserves F G
  exact Functor.preservesHomologyOfExact F

end LinearCategory

section VectorSpaces

variable (k : Type u) [Field k]

/-- Every vector space is an injective object, without a dimension bound. -/
theorem vectorSpace_injective (M : ModuleCat.{v} k) : Injective M where
  factors g f _ := by
    obtain ⟨leftInverse, inverse_eq⟩ := f.hom.exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr ((ModuleCat.mono_iff_injective f).mp inferInstance))
    refine ⟨ModuleCat.ofHom (g.hom.comp leftInverse), ?_⟩
    apply ModuleCat.hom_ext
    change (g.hom.comp leftInverse).comp f.hom = g.hom
    rw [LinearMap.comp_assoc, inverse_eq, LinearMap.comp_id]

/-- Scalar-linear duality, with the coefficient field itself as target. -/
abbrev scalarDual : (ModuleCat.{u} k)ᵒᵖ ⥤ ModuleCat.{u} k :=
  (linearYoneda k (ModuleCat.{u} k)).obj (ModuleCat.of k k)

instance scalarDual_preservesHomology : (scalarDual k).PreservesHomology := by
  letI : Injective (ModuleCat.of k k) := vectorSpace_injective k _
  infer_instance

/-- Evaluation at one identifies the scalar dual of the coefficient
field with the coefficient field, by an actual linear equivalence. -/
def scalarDualUnitIso :
    (scalarDual k).obj (op (ModuleCat.of k k)) ≅ ModuleCat.of k k :=
  (ModuleCat.homLinearEquiv.trans (LinearMap.ringLmapEquivSelf k k k)).toModuleIso

/-- The literal scalar dual of a chain complex, with transposed differential. -/
def scalarDualComplex (K : ChainComplex (ModuleCat.{u} k) ℕ) :
    CochainComplex (ModuleCat.{u} k) ℕ :=
  ((scalarDual k).mapHomologicalComplex _).obj K.op

/-- The contravariant map of scalar dual complexes. -/
def scalarDualMap {K L : ChainComplex (ModuleCat.{u} k) ℕ} (f : K ⟶ L) :
    scalarDualComplex k L ⟶ scalarDualComplex k K :=
  ((scalarDual k).mapHomologicalComplex _).map ((HomologicalComplex.opFunctor _ _).map f.op)

/-- Cohomology of the scalar dual is the scalar dual of homology, as
actual modules rather than merely underlying additive groups. -/
def scalarDualHomologyIso (K : ChainComplex (ModuleCat.{u} k) ℕ) (q : ℕ) :
    (scalarDualComplex k K).homology q ≅ (scalarDual k).obj (op (K.homology q)) :=
  (K.op.sc q).mapHomologyIso (scalarDual k) ≪≫
    (scalarDual k).mapIso (K.homologyOp q)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The homology comparison intertwines every actual chain map. -/
theorem scalarDualHomologyIso_natural {K L : ChainComplex (ModuleCat.{u} k) ℕ}
    (f : K ⟶ L) (q : ℕ) :
    HomologicalComplex.homologyMap (scalarDualMap k f) q ≫
        (scalarDualHomologyIso k K q).hom =
      (scalarDualHomologyIso k L q).hom ≫
        (scalarDual k).map (HomologicalComplex.homologyMap f q).op := by
  have h := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ q).map
      ((HomologicalComplex.opFunctor _ _).map f.op)) (scalarDual k)
  change HomologicalComplex.homologyMap (scalarDualMap k f) q ≫
      ((K.op.sc q).mapHomologyIso (scalarDual k)).hom =
    ((L.op.sc q).mapHomologyIso (scalarDual k)).hom ≫
      (scalarDual k).map
        (HomologicalComplex.homologyMap ((HomologicalComplex.opFunctor _ _).map f.op) q) at h
  simp only [scalarDualHomologyIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, h, Category.assoc, ← Functor.map_comp,
    HomologicalComplex.homologyOp_hom_naturality, Functor.map_comp, Category.assoc]

/-- Vanishing is transported without any finite-dimensional duality hypothesis. -/
theorem scalarDualComplex_isZero_homology (K : ChainComplex (ModuleCat.{u} k) ℕ)
    (q : ℕ) (h : IsZero (K.homology q)) :
    IsZero ((scalarDualComplex k K).homology q) :=
  ((scalarDual k).map_isZero h.op).of_iso (scalarDualHomologyIso k K q)

end VectorSpaces

end ToricPower
