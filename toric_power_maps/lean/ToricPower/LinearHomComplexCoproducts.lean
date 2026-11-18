module

public import ToricPower.CompactLinearHomCoproducts
public import ToricPower.FiniteGradedCoproductCompact
public import ToricPower.CochainFiniteSupport
public import ToricPower.LinearHomComplexFunctor
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Linear.FunctorCategory

/-! # Arbitrary coproducts in the actual signed Hom complex

A source complex with finitely many nonzero, coproduct-compact terms
has a Hom-complex functor preserving arbitrary coproducts. The second
complex can be unbounded in both directions. The proof identifies each
actual Hom degree with Hom from its finite graded source; it therefore
uses the original signed differential and original chain maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex HomComplex

namespace ToricPower

universe u v
variable (R : Type v) [CommRing R]
  {A : Type u} [Category.{v} A] [Abelian A] [Linear R A] [HasCoproducts.{v} A]

def gradedSourceDiagram (P : CochainComplex A ℤ) : Discrete ℤ ⥤ A :=
  Discrete.functor P.X

def gradedTargetFunctor (n : ℤ) : CochainComplex A ℤ ⥤ (Discrete ℤ ⥤ A) where
  obj K := Discrete.functor (fun q => K.X (q+n))
  map f := Discrete.natTrans (fun q => f.f (q.as+n))
  map_id K := by rfl
  map_comp f g := by rfl

def discreteHomLinearEquiv {I : Type} (F G : Discrete I ⥤ A) :
    (F ⟶ G) ≃ₗ[R] ∀ i : I, F.obj ⟨i⟩ ⟶ G.obj ⟨i⟩ where
  toFun f i := f.app ⟨i⟩
  invFun f := Discrete.natTrans (fun i => f i.as)
  left_inv f := by apply NatTrans.ext; funext i; rfl
  right_inv f := rfl
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def homCochainGradedEquiv (P K : CochainComplex A ℤ) (n : ℤ) :
    Cochain P K n ≃ₗ[R]
      (gradedSourceDiagram P ⟶ (gradedTargetFunctor n).obj K) :=
  (SerrePairing.cochainSourceValues R P K n).trans
    (discreteHomLinearEquiv R (gradedSourceDiagram P) ((gradedTargetFunctor n).obj K)).symm

/-- This is natural in actual chain maps, before passing to homology. -/
def linearHomDegreeGradedIso (P : CochainComplex A ℤ) (n : ℤ) :
    linearHomComplexFunctor R P ⋙ HomologicalComplex.eval (ModuleCat R) (.up ℤ) n ≅
      gradedTargetFunctor n ⋙
        (linearCoyoneda R (Discrete ℤ ⥤ A)).obj (op (gradedSourceDiagram P)) :=
  NatIso.ofComponents (fun K => (homCochainGradedEquiv R P K n).toModuleIso) (by
    intro K L f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply NatTrans.ext
    funext q
    exact homCochainPostcomp_v R P f n z q.as (q.as+n) rfl)

instance gradedTargetFunctor_preservesCoproducts (n : ℤ) (I : Type v) :
    PreservesColimitsOfShape (Discrete I) (gradedTargetFunctor (A := A) n) := by
  apply preservesColimitsOfShape_of_evaluation
  intro q
  change PreservesColimitsOfShape (Discrete I) (HomologicalComplex.eval A (.up ℤ) (q.as+n))
  infer_instance

variable (P : CochainComplex A ℤ) (grades : Finset ℤ)
  (outside : ∀ q, q ∉ grades → IsZero (P.X q))
  (compact : ∀ q ∈ grades, CompactExtraction.CoproductCompact.{u,v,v} (P.X q))

include outside compact in
/-- The actual Hom-complex functor preserves every coproduct, including
families of completely unbounded coefficient complexes. -/
theorem linearHomComplexFunctor_preservesCoproducts (I : Type v) :
    PreservesColimitsOfShape (Discrete I) (linearHomComplexFunctor R P) := by
  have sourceCompact : CompactExtraction.CoproductCompact (gradedSourceDiagram P) :=
    CompactExtraction.finiteGraded_coproductCompact (gradedSourceDiagram P) grades outside compact
  letI (family : I → (Discrete ℤ ⥤ A)) :
      PreservesColimit (Discrete.functor family)
        ((linearCoyoneda R (Discrete ℤ ⥤ A)).obj (op (gradedSourceDiagram P))) :=
    CompactExtraction.linearHom_preservesCoproduct R (gradedSourceDiagram P) sourceCompact family
  letI : PreservesColimitsOfShape (Discrete I)
      ((linearCoyoneda R (Discrete ℤ ⥤ A)).obj (op (gradedSourceDiagram P))) :=
    preservesColimitsOfShape_of_discrete _
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  exact preservesColimitsOfShape_of_natIso (linearHomDegreeGradedIso R P n).symm

end ToricPower

end
