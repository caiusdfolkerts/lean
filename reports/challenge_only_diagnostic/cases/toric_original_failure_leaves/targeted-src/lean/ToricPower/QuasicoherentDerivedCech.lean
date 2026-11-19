module

public import ToricPower.CartierMeetDerivedCech
public import ToricPower.QuasicoherentDerivedSectionsCohomology

/-!
# Actual bounded-below global sections from the full affine Čech diagram

The full tuple resolution is a genuine projective resolution of the
constant chart diagram. Exact affine sections and the proved flasqueness
of quasicoherent injectives identify its signed Hom complex with actual
right-derived global sections. Consequently a quasi-isomorphism between
the original scalar chart-section complexes computes the same actual
cohomology, even when it is not induced by a module-sheaf morphism.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex HomComplex

namespace ToricPower

variable (k : Type) [Field k] (X : Scheme.{0}) [X.Over (Spec (.of k))]
  [IsLocallyNoetherian X] [CompactSpace X] [X.IsSeparated]
  {B : Type} [SemilatticeInf B] [Finite B] (opens : B ⥤ X.Opens)
  (chartsInf : ∀ b c, opens.obj (b ⊓ c) = opens.obj b ⊓ opens.obj c)
  (cover : iSup opens.obj = ⊤)
  (meetEq : ∀ (q : ℕ) (t : Fin (q+1) → B),
    BondalThomsen.FiniteAffineCechHigherComparison.cechIntersection opens.obj q t =
      opens.obj (FiniteCech.tupleMeet t))
  (affine : ∀ b, IsAffineOpen (opens.obj b))

local notation "S" => FiniteCech.quasicoherentMeetSections k X opens
local notation "Γ" => quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X ⊤
local notation "P" => FiniteCech.tupleProjectiveResolution (B := B) k

include meetEq in
/-- Actual injective quasicoherent coefficients have exact positive
rows in the original full tuple complex. -/
theorem quasicoherentMeetSections_injective_rows
    (J : QCoh X) (injective : Injective J) (q : ℕ) :
    (projectiveCoefficientComplex k P ((S).obj J)).ExactAt (q+1) := by
  letI := injective
  exact FiniteCech.meetTupleCoefficient_exactAt_positive k X opens meetEq J.obj q

variable [HasDerivedCategory.{1} (QCoh X)]
  [HasDerivedCategory.{1} (Bᵒᵖ ⥤ ModuleCat.{0} k)]
  [HasDerivedCategory.{1} (ModuleCat.{0} k)]

/-- The original projective Čech model, localized on all complexes. -/
def quasicoherentMeetDerived :
    DerivedCategory (QCoh X) ⥤ DerivedCategory (ModuleCat.{0} k) := by
  letI := (FiniteCech.quasicoherentMeetSections_exact k X opens affine).1
  letI := (FiniteCech.quasicoherentMeetSections_exact k X opens affine).2
  exact projectiveCoefficientDerived k (S) P

/-- The genuine derived Čech comparison on the entire bounded-below
category, retaining all original coefficient and restriction maps. -/
def quasicoherentMeetDerivedPlusIso :
    DerivedCategory.Plus.ι ⋙ quasicoherentMeetDerived k X opens affine ≅
      (Γ).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι := by
  letI := (FiniteCech.quasicoherentMeetSections_exact k X opens affine).1
  letI := (FiniteCech.quasicoherentMeetSections_exact k X opens affine).2
  exact projectiveCoefficientPlusNatIso k (S) P
      (quasicoherentMeetSections_injective_rows k X opens meetEq) ≪≫
    Functor.isoWhiskerRight
      (rightDerivedPlusNatIso
        (quasicoherentGlobalTupleSectionsIso k X opens chartsInf cover).symm)
      DerivedCategory.Plus.ι

/-- Explicit full Hom complex for the actual right-derived global
sections of an arbitrary bounded-below quasicoherent complex. -/
def quasicoherentDerivedSectionsCechComplexIso (K : CochainComplex.Plus (QCoh X)) :
    DerivedCategory.Plus.ι.obj
      ((Γ).rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) ≅
    DerivedCategory.Q.obj
      (linearHomComplex k (projectiveCochain P)
        (((S).mapHomologicalComplex (.up ℤ)).obj K.obj)) := by
  letI := (FiniteCech.quasicoherentMeetSections_exact k X opens affine).1
  letI := (FiniteCech.quasicoherentMeetSections_exact k X opens affine).2
  exact (quasicoherentMeetDerivedPlusIso k X opens chartsInf cover meetEq affine).symm.app
      (DerivedCategory.Plus.Q.obj K) ≪≫
    (projectiveCoefficientDerivedFactors k (S) P).app K.obj

/-- Actual derived cohomology agrees with the homology of the entire
signed projective Čech complex in every integer degree. -/
def quasicoherentDerivedSectionsCechHomologyIso
    (K : CochainComplex.Plus (QCoh X)) (q : ℤ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{0} k) q).obj
      ((Γ).rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) ≅
    (linearHomComplex k (projectiveCochain P)
      (((S).mapHomologicalComplex (.up ℤ)).obj K.obj)).homology q :=
  (DerivedCategory.homologyFunctor (ModuleCat.{0} k) q).mapIso
      (quasicoherentDerivedSectionsCechComplexIso k X opens chartsInf cover meetEq affine K) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{0} k) q).app _

/-- A genuine quasi-isomorphism of complete scalar chart-section
complexes induces the corresponding isomorphism of derived global
cohomology. No lift of that map to module sheaves is required. -/
def quasicoherentDerivedSectionsCohomologyIsoOfChartQuasiIso
    (K L : CochainComplex.Plus (QCoh X))
    (f : ((S).mapHomologicalComplex (.up ℤ)).obj K.obj ⟶
      ((S).mapHomologicalComplex (.up ℤ)).obj L.obj)
    [QuasiIso f] (q : ℤ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{0} k) q).obj
      ((Γ).rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) ≅
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{0} k) q).obj
      ((Γ).rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj L)) := by
  let g := linearHomComplexMap k (projectiveCochain P) f
  letI : QuasiIso g := linearHomComplexMap_quasiIso k (projectiveCochain P) f
  exact quasicoherentDerivedSectionsCechHomologyIso k X opens chartsInf cover meetEq affine K q ≪≫
    asIso (HomologicalComplex.homologyMap g q) ≪≫
      (quasicoherentDerivedSectionsCechHomologyIso k X opens chartsInf cover meetEq affine L q).symm

/-- A chart-diagram quasi-isomorphism to a single actual quasicoherent
sheaf computes that sheaf's ordinary cohomology, in every degree. -/
def quasicoherentDerivedSectionsSingleCohomologyOfChartQuasiIso
    (K : CochainComplex.Plus (QCoh X)) (T : QCoh X)
    (f : ((S).mapHomologicalComplex (.up ℤ)).obj K.obj ⟶
      ((S).mapHomologicalComplex (.up ℤ)).obj (singlePlusComplex T).obj)
    [QuasiIso f] (degree : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{0} k) (degree : ℤ)).obj
      ((Γ).rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) ≃+
    TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology T.obj degree :=
  (quasicoherentDerivedSectionsCohomologyIsoOfChartQuasiIso k X opens chartsInf cover meetEq affine
      K (singlePlusComplex T) f degree).toLinearEquiv.toAddEquiv.trans
    (quasicoherentDerivedSectionsSingleCohomology k X T degree)

end ToricPower
end
