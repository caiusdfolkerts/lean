module

public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # Quasi-isomorphisms and the actual mapping cone -/

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CochainComplex HomologicalComplex

namespace ToricPower

universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- This is the cone of the original chain map, before localization. -/
theorem quasiIso_iff_mappingCone_acyclic {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    QuasiIso f ↔ (mappingCone f).Acyclic := by
  change HomologicalComplex.quasiIso A (.up ℤ) f ↔ _
  rw [← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact ((HomotopyCategory.subcategoryAcyclic A).trW_iff_of_distinguished
    (mappingCone.triangleh f) (HomotopyCategory.mappingCone_triangleh_distinguished f)).trans
      (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic (mappingCone f))

end ToricPower

end
