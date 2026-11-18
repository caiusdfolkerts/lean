module

public import ToricPower.WeightedIncidenceGeometry

/-! # Lifting a specified incidence functor with its actual weights -/

@[expose] public noncomputable section

open CategoryTheory

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  {C : Type*} [Category* C] (F : C ⥤ IncidenceObject A)
  (weight : C → Fin n → ℤ)
  (compatible : ∀ {c d : C} (f : c ⟶ d), weight d = weight c + (F.map f).val)

/-- The proof of incidence containment is retained from `F`; the weight
equation is the only extra datum required for its universal lift. -/
def weightedIncidenceFunctorLift : C ⥤ WeightedIncidenceObject A where
  obj c := (F.obj c,weight c)
  map f := ⟨F.map f,compatible f⟩
  map_id c := by
    apply Subtype.ext
    exact F.map_id c
  map_comp f g := by
    apply Subtype.ext
    exact F.map_comp f g

end ToricPower.IntegralArrangement

end
