module
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
/-! # The exact map formula for homotopy localization -/
@[expose] public noncomputable section
open CategoryTheory
namespace ToricPower
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
theorem derivedQh_map_quotient_formula {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    DerivedCategory.Qh.map ((HomotopyCategory.quotient A (.up ℤ)).map f) =
      ((DerivedCategory.quotientCompQhIso A).app K).hom ≫
        DerivedCategory.Q.map f ≫ ((DerivedCategory.quotientCompQhIso A).app L).inv := by
  apply (cancel_mono ((DerivedCategory.quotientCompQhIso A).app L).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact DerivedCategory.quotientCompQhIso_hom_naturality f
end ToricPower
end
