module

public import ToricPower.CartierTensorEquivalence
public import ToricPower.SchemeRestrictionTensor
public import ToricPower.CechOpenPushforwardAcyclic
public import ToricPower.CartierMeetDerivedCech

/-!
# Cartier tensoring and actual open direct image

Restriction carries the two inverse Cartier tensor pairings to inverse
pairings on the open. The commuting square of inverse tensor and
restriction functors therefore gives a commuting square of their actual
right adjoints. This proves the projection isomorphism for arbitrary
coefficients on the open and supplies the twisted local Čech rows.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory Functor.LaxMonoidal Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace ToricPower

universe u

section Restriction

variable {U X : Scheme.{u}} [IsIntegral X]
  (j : U ⟶ X) [IsOpenImmersion j] (D : CartierDivisor X)

/-- Restriction of the two actual inverse pairings gives the tensor
equivalence on the open, without choosing a divisor representative there. -/
def cartierRestrictedTensorEquivalence : U.Modules ≌ U.Modules :=
  tensorEquivalenceOfInverse (D.sheaf.restrict j) ((-D).sheaf.restrict j)
    ((Scheme.Modules.restrictTensorIso j (-D).sheaf D.sheaf).symm ≪≫
      (Scheme.Modules.restrictFunctor j).mapIso (cartierNegTensorIsoUnit D) ≪≫
        Scheme.Modules.restrictUnitIso j)
    ((Scheme.Modules.restrictTensorIso j D.sheaf (-D).sheaf).symm ≪≫
      (Scheme.Modules.restrictFunctor j).mapIso (cartierTensorNegIsoUnit D) ≪≫
        Scheme.Modules.restrictUnitIso j)

/-- The actual tensor comparison supplies the left-adjoint square. -/
def cartierInverseTensorRestrictionIso :
    Scheme.Modules.restrictFunctor j ⋙ (cartierRestrictedTensorEquivalence j D).inverse ≅
      (cartierTensorEquivalence D).inverse ⋙ Scheme.Modules.restrictFunctor j :=
  NatIso.ofComponents
    (fun M => (Scheme.Modules.restrictTensorIso j (-D).sheaf M).symm)
    (fun g => μ_natural_right (Scheme.Modules.restrictFunctor j) (-D).sheaf g)

/-- The resulting genuine projection isomorphism is natural in every
module coefficient on the open. -/
def cartierOpenPushforwardIso :
    Scheme.Modules.pushforward j ⋙ tensorLeft D.sheaf ≅
      tensorLeft (D.sheaf.restrict j) ⋙ Scheme.Modules.pushforward j :=
  conjugateIsoEquiv
    ((cartierTensorEquivalence D).symm.toAdjunction.comp (Scheme.Modules.restrictAdjunction j))
    ((Scheme.Modules.restrictAdjunction j).comp
      (cartierRestrictedTensorEquivalence j D).symm.toAdjunction)
    (cartierInverseTensorRestrictionIso j D)

end Restriction

section Rows

variable (k : Type) [Field k] (X : Scheme) [X.Over (Spec (.of k))] [IsIntegral X]
  {B : Type} [SemilatticeInf B] [Finite B] (opens : B ⥤ X.Opens)
  (meetEq : ∀ (q : ℕ) (t : Fin (q+1) → B),
    BondalThomsen.FiniteAffineCechHigherComparison.cechIntersection opens.obj q t =
      opens.obj (FiniteCech.tupleMeet t))

/-- Actual coefficient isomorphisms preserve exactness of every
ordinary projective coefficient row. -/
theorem projectiveCoefficient_exactAt_of_targetIso
    {C : Type*} [Category.{0} C] [Abelian C] [Linear k C]
    {Z : C} (P : ProjectiveResolution Z) {M N : C} (e : M ≅ N) (n : ℕ)
    (h : (projectiveCoefficientComplex k P N).ExactAt n) :
    (projectiveCoefficientComplex k P M).ExactAt n := by
  let E := (NatIso.mapHomologicalComplex ((linearYoneda k C).mapIso e) (.up ℕ)).app P.complex.op
  exact h.of_iso E.symm

include meetEq in
/-- Inverse Cartier twisting an actual open direct image gives exact
positive rows of the finite Čech projective resolution. -/
theorem cartierMeetFinite_openPushforward_rows
    {L : Type} [Category.{0} L] (P : Lᵒᵖ ⥤ CartierSources X)
    (a : B) [IsAffineHom (opens.obj a).ι]
    (M : QCoh (opens.obj a).toScheme) (c : L) (n : ℕ) :
    (projectiveCoefficientComplex k (FiniteCech.finiteTupleResolution k)
      (((cartierMeetSectionsDiagram k X P opens).obj
        ((quasicoherentAffinePushforward (opens.obj a).ι).obj M)).obj c)).ExactAt (n+1) := by
  let D := -(cartierSourceDivisor X ((P.rightOp.obj c).unop))
  let e := (cartierOpenPushforwardIso (opens.obj a).ι D).app M.obj
  let F := FiniteCech.meetChartSectionsFunctor k X opens
  apply projectiveCoefficient_exactAt_of_targetIso k
    (FiniteCech.finiteTupleResolution k) (F.mapIso e) (n+1)
  exact FiniteCech.meetFinite_openPushforward_exactAt_positive k X opens meetEq a
    (D.sheaf.restrict (opens.obj a).ι ⊗ M.obj) n

end Rows

end ToricPower

end
