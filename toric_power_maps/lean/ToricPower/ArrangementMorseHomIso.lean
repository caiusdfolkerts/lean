module

public import ToricPower.ArrangementLocalMorse
public import ToricPower.CellularHomDiagram
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-! # Actual Hom-diagram isomorphisms transport the entire Morse complex

The source labels, target labels, projection and coefficient complex
remain abstract. This seals the comparison before a geometric affine
replacement is evaluated.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (c : UniversalIncidenceObject A) (region : Set (Fin n → ℝ))
  {C : Type*} [Category.{0} C] [Preadditive C] [Linear ℂ C]
  {J : Type} [Category.{0} J]
  (P : (UniversalIncidenceObject A)ᵒᵖ ⥤ C) (Q : Jᵒᵖ ⥤ C)
  (projection : UniversalIncidenceObject A ⥤ J)

theorem universalLocalMorse_homPrecomposition_acyclic_of_iso
    (comparison : Cellular.homDiagram ℂ P ≅ Cellular.homDiagram ℂ Q ⋙
      (Functor.whiskeringLeft (UniversalIncidenceObject A) J (ModuleCat ℂ)).obj projection)
    (K : CochainComplex C ℤ)
    (vanishes : ((universalLocalMorse A ℂ c region).obj
      (((Cellular.homDiagram ℂ P).mapHomologicalComplex (.up ℤ)).obj K)).Acyclic) :
    ((universalLocalMorse A ℂ c region).obj
      (((Cellular.homDiagram ℂ Q ⋙
        (Functor.whiskeringLeft (UniversalIncidenceObject A) J (ModuleCat ℂ)).obj projection
        ).mapHomologicalComplex (.up ℤ)).obj K)).Acyclic := by
  let e := (universalLocalMorse A ℂ c region).mapIso
    ((NatIso.mapHomologicalComplex comparison (.up ℤ)).app K)
  intro q
  exact Iff.mp (exactAt_iff_of_quasiIsoAt e.hom q) (vanishes q)

end ToricPower.IntegralArrangement
end
