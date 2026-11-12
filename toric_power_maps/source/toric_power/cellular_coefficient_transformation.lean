module

public import ToricPower.ArrangementCellularCoefficientFunctor

/-!
# Naturality in the actual cellular coefficient functor

An additive natural transformation commutes with the canonical finite
cellular comparison. This keeps the original finite biproduct maps and
is independent of exactness or a homology calculation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.IntegralArrangement

universe u v w z

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [CommRing k]
  {B : Type u} [Category.{v} B] [Preadditive B] [Linear k B]
  {D : Type w} [Category.{z} D] [Preadditive D] [Linear k D]
  [HasFiniteBiproducts B] [HasFiniteBiproducts D]
  (F G : B ⥤ D) [F.Additive] [F.Linear k] [G.Additive] [G.Linear k]
  (γ : F ⟶ G) (P : IncidenceObject A ⥤ B)

local instance coefficientTransformationCellsFintype (q : ℕ) : Fintype (NormalizedCell A q) := Fintype.ofFinite _

/-- The original cellular comparison commutes with an actual natural
transformation of coefficient functors, in every degree and differential. -/
@[reassoc]
theorem cellularCoefficientComplexIso_transformation :
    (γ.mapHomologicalComplex (.up ℕ)).app
        (arrangementCellularCochainComplex A k P) ≫
      (cellularCoefficientComplexIso A k G P).hom =
    (cellularCoefficientComplexIso A k F P).hom ≫
      (arrangementCellularCochainFunctor A k).map (Functor.whiskerLeft P γ) := by
  apply HomologicalComplex.Hom.ext
  funext q
  change γ.app ((arrangementCellularCochainComplex A k P).X q) ≫
      (cellularCoefficientTermIso A k G P q).hom =
    (cellularCoefficientTermIso A k F P q).hom ≫
      ((arrangementCellularCochainFunctor A k).map (Functor.whiskerLeft P γ)).f q
  apply (cancel_mono (arrangementCellularCochainTermIso A k (P ⋙ G) q).hom).mp
  apply biproduct.hom_ext
  intro j
  simp only [Category.assoc, arrangementCellularCochainTermIso_projection]
  rw [cellularCoefficientTermIso_projection, cellularCochainMap_projection,
    ← Category.assoc, cellularCoefficientTermIso_projection]
  exact (γ.naturality (arrangementCellularCochainProjection A k P q j)).symm

end ToricPower.IntegralArrangement

end
