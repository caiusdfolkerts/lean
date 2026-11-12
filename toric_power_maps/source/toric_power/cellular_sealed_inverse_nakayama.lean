module

public import ToricPower.CellularAbelianNakayama
public import ToricPower.AdditiveHomotopyDerivedFunctor

/-!
# A proof-transparent, computationally sealed inverse-Nakayama presentation

The coefficient functor below is proved equal to ordinary inverse
Nakayama. The existential choice is used only to keep the implementation
opaque during kernel conversion of mapped-complex and homotopy-category
types. Its mathematical identity, additivity, and scalar linearity are
all proved. The whole homotopy functor is compared before its objects
are evaluated.
-/

@[expose] public noncomputable section

open CategoryTheory
namespace ToricPower

universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

theorem additiveHomotopyDerived_eq_of_eq
    (F G : A ⥤ A) [F.Additive] [G.Additive] (same : F = G) :
    additiveHomotopyDerived F = additiveHomotopyDerived G := by
  subst G
  rfl

namespace Cellular

universe a
variable (k : Type a) [Field k] {C : Type a} [Category.{a} C]

theorem inverseNakayamaPresentation_exists :
    ∃ F : (C ⥤ ModuleCat.{a} k) ⥤ C ⥤ ModuleCat.{a} k,
      F = inverseNakayama k := ⟨inverseNakayama k, rfl⟩

/-- This is the ordinary coefficient functor, with a checked equality
and an opaque computational presentation. -/
def sealedInverseNakayama : (C ⥤ ModuleCat.{a} k) ⥤ C ⥤ ModuleCat.{a} k :=
  Classical.choose (inverseNakayamaPresentation_exists k (C := C))

theorem sealedInverseNakayama_eq :
    sealedInverseNakayama k (C := C) = inverseNakayama k :=
  Classical.choose_spec (inverseNakayamaPresentation_exists k (C := C))

attribute [local instance 2000] Abelian.toPreadditive

instance sealedInverseNakayama_additive :
    (sealedInverseNakayama k (C := C)).Additive := by
  rw [sealedInverseNakayama_eq]
  exact inverseNakayamaAbelian_additive k

instance sealedInverseNakayama_linear :
    (sealedInverseNakayama k (C := C)).Linear k := by
  rw [sealedInverseNakayama_eq]
  infer_instance

end Cellular
end ToricPower
end
