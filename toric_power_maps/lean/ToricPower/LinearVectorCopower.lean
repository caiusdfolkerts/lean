module

public import ToricPower.CellularHomDiagram
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Actual vector copowers in a cocomplete linear category

A vector space has a basis, so its copower of an object is an actual
coproduct indexed by that basis. The universal property is linear in the
vector argument and independent of that auxiliary basis choice up to its
canonical isomorphism. The functor and its adjunction are constructed from
this genuine universal property, rather than supplied as hypotheses.

-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical

namespace ToricPower.Cellular

universe u v

variable (k : Type u) [Field k]
  {A : Type v} [Category.{u} A] [Preadditive A] [Linear k A]
  [HasCoproducts.{u} A]

/-- An actual coproduct indexed by an actual vector-space basis. -/
def vectorCopower (P : A) (M : ModuleCat.{u} k) : A :=
  ∐ (fun _ : Module.Free.ChooseBasisIndex k M => P)

/-- Every vector defines its actual linear combination of coproduct
inclusions. No finiteness assumption on the vector space is imposed. -/
def vectorCopowerInclusion (P : A) (M : ModuleCat.{u} k) :
    M →ₗ[k] (P ⟶ vectorCopower k P M) :=
  (Module.Free.chooseBasis k M).constr k
    (fun i => Sigma.ι (fun _ : Module.Free.ChooseBasisIndex k M => P) i)

@[simp]
theorem vectorCopowerInclusion_basis (P : A) (M : ModuleCat.{u} k)
    (i : Module.Free.ChooseBasisIndex k M) :
    vectorCopowerInclusion k P M (Module.Free.chooseBasis k M i) =
      Sigma.ι (fun _ : Module.Free.ChooseBasisIndex k M => P) i :=
  Module.Basis.constr_basis _ _ _ _

/-- The literal linear Hom universal property of the coproduct. -/
def vectorCopowerHomEquiv (P : A) (M : ModuleCat.{u} k) (E : A) :
    (vectorCopower k P M ⟶ E) ≃
      (M ⟶ ModuleCat.of k (P ⟶ E)) where
  toFun h := ModuleCat.ofHom
    ((Linear.rightComp k P h).comp (vectorCopowerInclusion k P M))
  invFun f := Sigma.desc
    (fun i : Module.Free.ChooseBasisIndex k M => f (Module.Free.chooseBasis k M i))
  left_inv h := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_comp_desc]
    change vectorCopowerInclusion k P M (Module.Free.chooseBasis k M i) ≫ h = _
    rw [vectorCopowerInclusion_basis]
  right_inv f := by
    apply ModuleCat.hom_ext
    apply (Module.Free.chooseBasis k M).ext
    intro i
    change vectorCopowerInclusion k P M (Module.Free.chooseBasis k M i) ≫
      Sigma.desc (fun j => f (Module.Free.chooseBasis k M j)) = f (Module.Free.chooseBasis k M i)
    rw [vectorCopowerInclusion_basis, Sigma.ι_comp_desc]

@[simp]
theorem vectorCopowerHomEquiv_apply (P : A) (M : ModuleCat.{u} k) (E : A)
    (h : vectorCopower k P M ⟶ E) (x : M) :
    vectorCopowerHomEquiv k P M E h x = vectorCopowerInclusion k P M x ≫ h := rfl

@[simp]
theorem vectorCopowerInclusion_desc (P : A) (M : ModuleCat.{u} k) (E : A)
    (f : M ⟶ ModuleCat.of k (P ⟶ E)) (x : M) :
    vectorCopowerInclusion k P M x ≫ (vectorCopowerHomEquiv k P M E).symm f = f x := by
  exact ConcreteCategory.congr_hom ((vectorCopowerHomEquiv k P M E).apply_symm_apply f) x

/-- Postcomposition is exactly the action of the genuine linear Hom
functor on the universal property. -/
theorem vectorCopowerHomEquiv_natural (P : A) (M : ModuleCat.{u} k)
    (E E' : A) (g : E ⟶ E') (h : vectorCopower k P M ⟶ E) :
    vectorCopowerHomEquiv k P M E' (h ≫ g) =
      vectorCopowerHomEquiv k P M E h ≫
        ((linearCoyoneda k A).obj (op P)).map g := by
  ext x
  exact (Category.assoc _ _ _).symm

/-- Functoriality in the vector space is derived from the universal
property and actual postcomposition naturality. -/
def vectorCopowerFunctor (P : A) : ModuleCat.{u} k ⥤ A :=
  Adjunction.leftAdjointOfEquiv (G := (linearCoyoneda k A).obj (op P))
    (vectorCopowerHomEquiv k P)
    (vectorCopowerHomEquiv_natural k P)

/-- Actual vector copower is left adjoint to the actual linear Hom
functor, with no adjoint-existence hypothesis. -/
def vectorCopowerAdjunction (P : A) :
    vectorCopowerFunctor k P ⊣ (linearCoyoneda k A).obj (op P) :=
  Adjunction.adjunctionOfEquivLeft (G := (linearCoyoneda k A).obj (op P))
    (vectorCopowerHomEquiv k P)
    (vectorCopowerHomEquiv_natural k P)

instance vectorCopower_isLeftAdjoint (P : A) : (vectorCopowerFunctor k P).IsLeftAdjoint :=
  (vectorCopowerAdjunction k P).isLeftAdjoint

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts

instance vectorCopower_additive (P : A) : (vectorCopowerFunctor k P).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

@[reassoc]
theorem vectorCopowerInclusion_map (P : A) {M N : ModuleCat.{u} k}
    (f : M ⟶ N) (x : M) :
    vectorCopowerInclusion k P M x ≫ (vectorCopowerFunctor k P).map f =
      vectorCopowerInclusion k P N (f x) := by
  change vectorCopowerHomEquiv k P M _
      ((vectorCopowerHomEquiv k P M _).symm
        (f ≫ vectorCopowerHomEquiv k P N _ (𝟙 _))) x = _
  rw [Equiv.apply_symm_apply]
  change vectorCopowerInclusion k P N (f x) ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- Covariance in the object being copied is literal postcomposition
on each coproduct inclusion. -/
def vectorCopowerMapObject {P Q : A} (a : P ⟶ Q) (M : ModuleCat.{u} k) :
    vectorCopower k P M ⟶ vectorCopower k Q M :=
  Sigma.desc (fun i : Module.Free.ChooseBasisIndex k M =>
    a ≫ Sigma.ι (fun _ : Module.Free.ChooseBasisIndex k M => Q) i)

@[reassoc]
theorem vectorCopowerInclusion_mapObject {P Q : A} (a : P ⟶ Q)
    (M : ModuleCat.{u} k) (x : M) :
    vectorCopowerInclusion k P M x ≫ vectorCopowerMapObject k a M =
      a ≫ vectorCopowerInclusion k Q M x := by
  have h :
      (Linear.rightComp k P (vectorCopowerMapObject k a M)).comp
          (vectorCopowerInclusion k P M) =
        (Linear.leftComp k (vectorCopower k Q M) a).comp
          (vectorCopowerInclusion k Q M) := by
    apply (Module.Free.chooseBasis k M).ext
    intro i
    simp only [LinearMap.comp_apply, vectorCopowerInclusion_basis,
      Linear.leftComp_apply, Linear.rightComp_apply, vectorCopowerMapObject,
      Sigma.ι_comp_desc]
  exact LinearMap.congr_fun h x

/-- Checking maps on all vector inclusions suffices; the proof uses the
actual coproduct generators. -/
theorem vectorCopower_hom_ext (P : A) (M : ModuleCat.{u} k) {E : A}
    {f g : vectorCopower k P M ⟶ E}
    (h : ∀ x : M, vectorCopowerInclusion k P M x ≫ f =
      vectorCopowerInclusion k P M x ≫ g) : f = g := by
  apply (vectorCopowerHomEquiv k P M E).injective
  ext x
  exact h x

/-- Over a field every short exact sequence of vector spaces splits.
The actual vector-copower functor therefore preserves finite limits,
in addition to the colimits supplied by its actual adjunction. -/
instance vectorCopower_preservesFiniteLimits
    {B : Type v} [Category.{u} B] [Abelian B] [Linear k B] [HasCoproducts.{u} B]
    (P : B) :
    PreservesFiniteLimits (vectorCopowerFunctor k P) := by
  apply (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).mpr
  intro S hS
  letI : Projective S.X₃ := ModuleCat.projective_of_free (Module.Basis.ofVectorSpace k S.X₃)
  let splitting := hS.splittingOfProjective.map (vectorCopowerFunctor k P)
  exact ⟨splitting.exact, splitting.mono_f⟩

end ToricPower.Cellular

end
