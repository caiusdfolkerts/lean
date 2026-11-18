module

public import ToricPower.AffineCoresolutionClosure
public import ToricPower.HomologicalComparisonClosure
public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor

/-! # Ordinary section comparisons on the actual affine coresolution

A natural map of additive coefficient functors which is invertible on
every affine direct-image sheaf is a quasi-isomorphism on the genuine
finite affine coresolution of every unbounded complex. The finite cone
filtration and the actual five lemma supply this implication.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex

namespace ToricPower

universe u v w z

section Generic

variable {A : Type u} {B : Type w} [Category.{v} A] [Category.{z} B]
  [Abelian A] [Abelian B] {F G : A ⥤ B} [F.Additive] [G.Additive]
  (a : F ⟶ G) (K : CochainComplex A ℤ)

/-- The componentwise isomorphisms are the components of the original
mapped natural transformation. -/
theorem mappedNaturalTransformation_isIso_of_terms
    (terms : ∀ q, IsIso (a.app (K.X q))) :
    IsIso ((NatTrans.mapHomologicalComplex a (.up ℤ)).app K) := by
  haveI (q : ℤ) : IsIso (((NatTrans.mapHomologicalComplex a (.up ℤ)).app K).f q) :=
    terms q
  exact HomologicalComplex.Hom.isIso_of_components _

theorem homotopyNaturalTransformation_isIso_of_terms
    (terms : ∀ q, IsIso (a.app (K.X q))) :
    IsIso ((NatTrans.mapHomotopyCategory a (.up ℤ)).app
      ((HomotopyCategory.quotient A (.up ℤ)).obj K)) := by
  haveI := mappedNaturalTransformation_isIso_of_terms a K terms
  change IsIso ((HomotopyCategory.quotient B (.up ℤ)).map
    ((NatTrans.mapHomologicalComplex a (.up ℤ)).app K))
  infer_instance

end Generic

variable {X : Scheme.{u}} {I : Type v}
  (V : I → X.Opens) [∀ i, IsAffineHom (V i).ι]
  {B : Type w} [Category.{z} B] [Abelian B]
  {F G : QCoh X ⥤ B} [F.Additive] [G.Additive] (a : F ⟶ G)

/-- The literal coefficient comparison on the full affine coresolution,
without a boundedness assumption on its original input. -/
theorem affineCoresolution_mappedSection_quasiIso
    (localIso : ∀ (i : I) (M : QCoh (V i).toScheme),
      IsIso (a.app ((quasicoherentAffinePushforward (V i).ι).obj M)))
    (l : List I) (K : CochainComplex (QCoh X) ℤ) :
    QuasiIso ((NatTrans.mapHomologicalComplex a (.up ℤ)).app
      ((affineConeCoresolution V l).obj K)) := by
  rw [quasiIso_iff]
  intro q
  let QA := HomotopyCategory.quotient (QCoh X) (.up ℤ)
  let QB := HomotopyCategory.quotient B (.up ℤ)
  let Hq := HomotopyCategory.homologyFunctor B (.up ℤ) q
  let α := Functor.whiskerRight (NatTrans.mapHomotopyCategory a (.up ℤ)) Hq
  let P := homologicalComparisonLocus
    (F.mapHomotopyCategory (.up ℤ) ⋙ Hq)
    (G.mapHomotopyCategory (.up ℤ) ⋙ Hq) α
  have hlocal (i : I) (J : CochainComplex (QCoh (V i).toScheme) ℤ) :
      P (QA.obj (((quasicoherentAffinePushforward (V i).ι).mapHomologicalComplex
        (.up ℤ)).obj J)) := by
    let L := ((quasicoherentAffinePushforward (V i).ι).mapHomologicalComplex (.up ℤ)).obj J
    intro n
    apply (NatTrans.isIso_app_iff_of_iso α ((QA.commShiftIso n).app L)).mp
    haveI : IsIso ((NatTrans.mapHomotopyCategory a (.up ℤ)).app (QA.obj (L⟦n⟧))) := by
      apply homotopyNaturalTransformation_isIso_of_terms
      intro p
      apply (NatTrans.isIso_app_iff_of_iso a
        (CochainComplex.shiftFunctorObjXIso L n p (p+n) rfl)).mpr
      exact localIso i (J.X (p+n))
    change IsIso (Hq.map ((NatTrans.mapHomotopyCategory a (.up ℤ)).app (QA.obj (L⟦n⟧))))
    infer_instance
  have hR := affineConeCoresolution_mem V P hlocal l K
  let L := (affineConeCoresolution V l).obj K
  haveI : IsIso (α.app (QA.obj L)) :=
    (NatTrans.isIso_app_iff_of_iso α
      ((shiftFunctorZero (HomotopyCategory (QCoh X) (.up ℤ)) ℤ).app (QA.obj L))).mp (hR 0)
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply (NatIso.isIso_map_iff (HomotopyCategory.homologyFunctorFactors B (.up ℤ) q)
    ((NatTrans.mapHomologicalComplex a (.up ℤ)).app L)).mp
  change IsIso (α.app (QA.obj L))
  infer_instance

end ToricPower

end
