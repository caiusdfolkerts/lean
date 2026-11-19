module

public import ToricPower.CellularTranslatedWeights
public import ToricPower.ArrangementCochainColimits

/-!
# Actual coefficient maps between translating character diagrams

A constant translation of all characters is natural for the original
incidence maps. Applying the genuine cellular cochain functor gives a
chain map, and the full cell-and-character basis records its literal
translation with unchanged scalar coefficient.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (allowed target : IncidenceObject A → (Fin n → ℤ) → Prop)
  (stable : ∀ {c d : IncidenceObject A} (f : c ⟶ d) {a : Fin n → ℤ},
    allowed c a → allowed d (a + f.val))
  (targetStable : ∀ {c d : IncidenceObject A} (f : c ⟶ d) {a : Fin n → ℤ},
    target c a → target d (a + f.val))
  (z : Fin n → ℤ) (permitted : ∀ c a, allowed c a → target c (a + z))

/-- Literal translation of each permitted character. -/
def translatedCoefficientIndex (c : IncidenceObject A) :
    TranslatedWeightIndex A allowed c → TranslatedWeightIndex A target c :=
  fun a => ⟨a.val + z, permitted c a.val a.property⟩

variable (k : Type) [CommRing k]

/-- The natural transformation uses the actual free character maps. -/
def translatedCoefficientMap :
    translatedWeightDiagram A allowed stable k ⟶
      translatedWeightDiagram A target targetStable k where
  app c := ModuleCat.ofHom (Finsupp.lmapDomain k k
    (translatedCoefficientIndex A allowed target z permitted c))
  naturality {c d} f := by
    apply ModuleCat.hom_ext
    change (Finsupp.lmapDomain k k (translatedCoefficientIndex A allowed target z permitted d)).comp
        (Finsupp.lmapDomain k k (translatedWeightMap A allowed stable f)) =
      (Finsupp.lmapDomain k k (translatedWeightMap A target targetStable f)).comp
        (Finsupp.lmapDomain k k (translatedCoefficientIndex A allowed target z permitted c))
    rw [← Finsupp.lmapDomain_comp, ← Finsupp.lmapDomain_comp]
    congr 1
    funext a
    apply Subtype.ext
    change (a.val + f.val) + z = (a.val + z) + f.val
    abel

/-- The actual full cellular cochain map. -/
def translatedCoefficientComplexMap :
    translatedWeightCellularComplex A allowed stable k ⟶
      translatedWeightCellularComplex A target targetStable k :=
  (arrangementCellularCochainFunctor A k).map
    (translatedCoefficientMap A allowed target stable targetStable z permitted k)

def translatedCellIndex (q : ℕ) :
    TranslatedCellIndex A allowed q → TranslatedCellIndex A target q :=
  fun i => ⟨i.1, translatedCoefficientIndex A allowed target z permitted ⟨q, i.1⟩ i.2⟩

/-- Every actual generator is sent to its translated generator with
exactly its original scalar coefficient. -/
theorem translatedCoefficientComplexMap_generator (q : ℕ)
    (i : TranslatedCellIndex A allowed q) (r : k) :
    translatedWeightCellularCoordinates A target targetStable k q
        ((translatedCoefficientComplexMap A allowed target stable targetStable z permitted k).f q
          ((translatedWeightCellularCoordinates A allowed stable k q).symm
            (Finsupp.single i r))) =
      Finsupp.single (translatedCellIndex A allowed target z permitted q i) r := by
  rw [translatedWeightCellularCoordinates_symm_single]
  have component := ConcreteCategory.congr_hom
    (arrangementCellularCochainMap_inclusion A k
      (translatedCoefficientMap A allowed target stable targetStable z permitted k) q i.1)
    (Finsupp.single i.2 r)
  change (translatedCoefficientComplexMap A allowed target stable targetStable z permitted k).f q
      (arrangementCellularCochainInclusion A k (translatedWeightDiagram A allowed stable k)
        q i.1 (Finsupp.single i.2 r)) =
    arrangementCellularCochainInclusion A k (translatedWeightDiagram A target targetStable k)
      q i.1 (Finsupp.mapDomain (translatedCoefficientIndex A allowed target z permitted ⟨q, i.1⟩)
        (Finsupp.single i.2 r)) at component
  rw [component, Finsupp.mapDomain_single]
  exact cellularCochainFreeCoordinates_generator A k
    (translatedWeightDiagram A target targetStable k) (TranslatedWeightIndex A target)
    (fun _ => LinearEquiv.refl k _) q i.1 _ r

end ToricPower.IntegralArrangement
