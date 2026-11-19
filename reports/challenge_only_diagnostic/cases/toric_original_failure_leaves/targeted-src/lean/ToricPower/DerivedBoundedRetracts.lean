module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.ObjectProperty.Retract

/-!
# Retracts retain actual derived cohomological bounds

Homology sends a retract to a retract. A retract of a zero object is
zero, so both cohomological bounds pass to retracts without any
assumption that the retract was already represented by a bounded
complex.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

theorem derived_isGE_of_retract {X Y : DerivedCategory A}
    (r : Retract X Y) (a : ℤ) [Y.IsGE a] : X.IsGE a := by
  rw [DerivedCategory.isGE_iff]
  intro q hq
  let rh := r.map (DerivedCategory.homologyFunctor A q)
  exact IsZero.of_mono rh.i (DerivedCategory.isZero_of_isGE Y a q hq)

theorem derived_isLE_of_retract {X Y : DerivedCategory A}
    (r : Retract X Y) (b : ℤ) [Y.IsLE b] : X.IsLE b := by
  rw [DerivedCategory.isLE_iff]
  intro q hq
  let rh := r.map (DerivedCategory.homologyFunctor A q)
  exact IsZero.of_mono rh.i (DerivedCategory.isZero_of_isLE Y b q hq)

theorem derived_bounded_of_retract {X Y : DerivedCategory A}
    (r : Retract X Y) (bounded : DerivedCategory.TStructure.t.bounded Y) :
    DerivedCategory.TStructure.t.bounded X := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := bounded
  letI := ha
  letI := hb
  exact ⟨⟨a, derived_isGE_of_retract r a⟩, ⟨b, derived_isLE_of_retract r b⟩⟩

instance derived_bounded_isStableUnderRetracts :
    (DerivedCategory.TStructure.t (C := A)).bounded.IsStableUnderRetracts where
  of_retract := derived_bounded_of_retract

end ToricPower

end
