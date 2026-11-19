module

public import ToricPower.ArrangementRepresentableCellMaps

/-!
# The actual representable coefficient diagram in Laurent coordinates

The coordinate identifications are natural before forming a complex.
Consequently the original cellular cochain functor gives a genuine
isomorphism of complexes with this explicit full-character diagram. Each
index records the actual source incidence, not merely its endpoints.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (S : Set (Fin s))
  (c : IncidenceObject A)

/-- A genuine incidence copy and a permitted monomial of its label. -/
def RepresentedLaurentIndex (d : IncidenceObject A) :=
  Σ f : c ⟶ d, ReflectedLaurentWeight A S d

/-- Both actual actions are retained in the coefficient-index map. -/
def representedLaurentIndexMap {d e : IncidenceObject A} (h : d ⟶ e) :
    RepresentedLaurentIndex A S c d → RepresentedLaurentIndex A S c e :=
  fun p => ⟨p.1 ≫ h, reflectedLaurentWeightMap A S h p.2⟩

@[simp]
theorem representedLaurentIndexMap_id (d : IncidenceObject A) :
    representedLaurentIndexMap A S c (𝟙 d) = id := by
  funext p
  rcases p with ⟨f, m⟩
  change (⟨f ≫ 𝟙 d, reflectedLaurentWeightMap A S (𝟙 d) m⟩ :
    RepresentedLaurentIndex A S c d) = ⟨f, m⟩
  rw [Category.comp_id, reflectedLaurentWeightMap_id]
  rfl

@[simp]
theorem representedLaurentIndexMap_comp {d e f : IncidenceObject A}
    (h : d ⟶ e) (g : e ⟶ f) :
    representedLaurentIndexMap A S c (h ≫ g) =
      representedLaurentIndexMap A S c g ∘ representedLaurentIndexMap A S c h := by
  funext p
  rcases p with ⟨a, m⟩
  change (⟨a ≫ h ≫ g, reflectedLaurentWeightMap A S (h ≫ g) m⟩ :
    RepresentedLaurentIndex A S c f) =
      ⟨(a ≫ h) ≫ g, reflectedLaurentWeightMap A S g (reflectedLaurentWeightMap A S h m)⟩
  rw [Category.assoc, reflectedLaurentWeightMap_comp]
  rfl

variable (k : Type) [Field k]

/-- The explicit full-character coefficient functor. -/
def representedLaurentDiagram : IncidenceObject A ⥤ ModuleCat.{0} k where
  obj d := ModuleCat.of k (RepresentedLaurentIndex A S c d →₀ k)
  map h := ModuleCat.ofHom (Finsupp.lmapDomain k k (representedLaurentIndexMap A S c h))
  map_id d := by
    rw [representedLaurentIndexMap_id, Finsupp.lmapDomain_id]
    rfl
  map_comp h g := by
    rw [representedLaurentIndexMap_comp, Finsupp.lmapDomain_comp]
    rfl

/-- The actual copower coefficient functor is naturally isomorphic to
its explicit genuine-incidence and full-character coordinate functor. -/
def representedLaurentDiagramIso :
    Cellular.covariantCopowerDiagram k (reflectedLaurentDiagram A S k)
        (Cellular.representable k c) ≅ representedLaurentDiagram A S c k :=
  NatIso.ofComponents
    (fun d => (representableLaurentCellCoordinates A S k c d.1 d.2).toModuleIso)
    (by
      rintro ⟨q, e⟩ ⟨r, d⟩ h
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact representableLaurentCellMap_coordinates A S k c e d h x)

/-- Applying the original, independently constructed cellular functor
gives an actual isomorphism of complexes, including every differential. -/
def representedLaurentCellularComplexIso :
    representableLaurentCellularComplex A S k c ≅
      arrangementCellularCochainComplex A k (representedLaurentDiagram A S c k) :=
  (arrangementCellularCochainFunctor A k).mapIso (representedLaurentDiagramIso A S c k)

/-- The full total character is invariant under every actual incidence
map: the two recorded displacements cancel exactly. -/
theorem representedLaurentIndexMap_totalWeight {d e : IncidenceObject A}
    (h : d ⟶ e) (p : RepresentedLaurentIndex A S c d) :
    (representedLaurentIndexMap A S c h p).2.val -
        (representedLaurentIndexMap A S c h p).1.val = p.2.val - p.1.val := by
  change p.2.val + h.val - (p.1 ≫ h).val = _
  rw [incidence_comp_val]
  abel

end ToricPower.IntegralArrangement
