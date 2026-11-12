module

public import ToricPower.ArrangementCochainFreeCoordinates

/-!
# Cellular cochains with literal translating character bases

This interface starts with a family of permitted integral characters
and a proof that every genuine incidence translates that family into
the next one. It constructs the corresponding coefficient diagram and
its actual cellular cochains. The free coordinates retain the complete
integral lattice and the original cell incidences.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (allowed : IncidenceObject A → (Fin n → ℤ) → Prop)
  (stable : ∀ {c d : IncidenceObject A} (f : c ⟶ d) {a : Fin n → ℤ},
    allowed c a → allowed d (a + f.val))

abbrev TranslatedWeightIndex (c : IncidenceObject A) := {a // allowed c a}

def translatedWeightMap {c d : IncidenceObject A} (f : c ⟶ d) :
    TranslatedWeightIndex A allowed c → TranslatedWeightIndex A allowed d :=
  fun a => ⟨a.val + f.val, stable f a.property⟩

@[simp]
theorem translatedWeightMap_id (c : IncidenceObject A) :
    translatedWeightMap A allowed stable (𝟙 c) = id := by
  funext a
  apply Subtype.ext
  simp only [translatedWeightMap, incidence_id_val, add_zero]
  rfl

@[simp]
theorem translatedWeightMap_comp {c d e : IncidenceObject A}
    (f : c ⟶ d) (g : d ⟶ e) :
    translatedWeightMap A allowed stable (f ≫ g) =
      translatedWeightMap A allowed stable g ∘ translatedWeightMap A allowed stable f := by
  funext a
  apply Subtype.ext
  simp only [translatedWeightMap, incidence_comp_val, Function.comp_apply, add_assoc]

variable (k : Type) [CommRing k]

/-- The actual unrestricted character coefficient diagram. -/
def translatedWeightDiagram : IncidenceObject A ⥤ ModuleCat.{0} k where
  obj c := ModuleCat.of k (TranslatedWeightIndex A allowed c →₀ k)
  map f := ModuleCat.ofHom (Finsupp.lmapDomain k k (translatedWeightMap A allowed stable f))
  map_id c := by
    rw [translatedWeightMap_id, Finsupp.lmapDomain_id]
    rfl
  map_comp f g := by
    rw [translatedWeightMap_comp, Finsupp.lmapDomain_comp]
    rfl

@[simp]
theorem translatedWeightDiagram_map_single {c d : IncidenceObject A}
    (f : c ⟶ d) (a : TranslatedWeightIndex A allowed c) (r : k) :
    (translatedWeightDiagram A allowed stable k).map f (Finsupp.single a r) =
      Finsupp.single (translatedWeightMap A allowed stable f a) r :=
  Finsupp.mapDomain_single

abbrev TranslatedCellIndex (q : ℕ) :=
  Σ c : NormalizedCell A q, TranslatedWeightIndex A allowed ⟨q, c⟩

/-- The cellular complex is obtained from the independently defined
coefficient functor and the genuine cellular differential. -/
def translatedWeightCellularComplex : CochainComplex (ModuleCat.{0} k) ℕ :=
  arrangementCellularCochainComplex A k (translatedWeightDiagram A allowed stable k)

def translatedWeightCellularCoordinates (q : ℕ) :
    (translatedWeightCellularComplex A allowed stable k).X q ≃ₗ[k]
      (TranslatedCellIndex A allowed q →₀ k) :=
  cellularCochainFreeCoordinates A k (translatedWeightDiagram A allowed stable k)
    (TranslatedWeightIndex A allowed) (fun _ => LinearEquiv.refl k _) q

theorem translatedWeightCellularCoordinates_symm_single (q : ℕ)
    (i : TranslatedCellIndex A allowed q) (r : k) :
    (translatedWeightCellularCoordinates A allowed stable k q).symm (Finsupp.single i r) =
      arrangementCellularCochainInclusion A k (translatedWeightDiagram A allowed stable k)
        q i.1 (Finsupp.single i.2 r) :=
  cellularCochainFreeCoordinates_symm_single A k
    (translatedWeightDiagram A allowed stable k) (TranslatedWeightIndex A allowed)
    (fun _ => LinearEquiv.refl k _) q i.1 i.2 r

end ToricPower.IntegralArrangement
