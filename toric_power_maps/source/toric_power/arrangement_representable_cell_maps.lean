module

public import ToricPower.ArrangementRepresentableTerms

/-!
# Actual incidence maps in representable Laurent coordinates

The source representable acts by genuine incidence composition, while
the covariant Cartier coefficient acts by its genuine character shift.
This file checks both actions on the actual copower maps and then on all
finite Laurent sums. It supplies the coefficient-map comparison needed
to identify the actual cellular differential with the costalk matrix.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (S : Set (Fin s))
  (k : Type) [Field k] (c : IncidenceObject A)

local instance representableCellMapHomFintype (d : IncidenceObject A) :
    Fintype (c ⟶ d) := Fintype.ofFinite _

local notation "Q" => reflectedLaurentDiagram A S k
local notation "Rep" => Cellular.representable k c
local notation "Coefficients" => Cellular.covariantCopowerDiagram k Q Rep

/-- The canonical free-copower coordinates read the literal incidence
projection in the actual finite biproduct. -/
theorem representableLaurentCellCoordinates_apply (q : ℕ) (e : NormalizedCell A q)
    (x : (Coefficients).obj ⟨q, e⟩) (f : c ⟶ (⟨q, e⟩ : IncidenceObject A))
    (m : ReflectedLaurentWeight A S ⟨q, e⟩) :
    representableLaurentCellCoordinates A S k c q e x ⟨f, m⟩ =
      Finsupp.lapply (R := k) (M := k) m
        (biproduct.π (fun _ : c ⟶ (⟨q, e⟩ : IncidenceObject A) => (Q).obj ⟨q, e⟩) f
        ((Cellular.vectorCopowerFreeBiproductIso k ((Q).obj ⟨q, e⟩)
          (c ⟶ (⟨q, e⟩ : IncidenceObject A))).hom x)) := by
  change Finsupp.lapply (R := k) (M := k) m (((ModuleCat.biproductIsoPi
      (fun _ : c ⟶ (⟨q, e⟩ : IncidenceObject A) => (Q).obj ⟨q, e⟩)).hom
      ((Cellular.vectorCopowerFreeBiproductIso k ((Q).obj ⟨q, e⟩)
        (c ⟶ (⟨q, e⟩ : IncidenceObject A))).hom x)) f) = _
  rw [moduleBiproductIsoPi_hom_apply]

/-- Each actual copower inclusion is the corresponding literal free
generator in the full Laurent coordinate module. -/
theorem representableLaurentCellCoordinates_generator (q : ℕ)
    (e : NormalizedCell A q) (f : c ⟶ (⟨q, e⟩ : IncidenceObject A))
    (m : ReflectedLaurentWeight A S ⟨q, e⟩) (a : k) :
    representableLaurentCellCoordinates A S k c q e
      (Cellular.vectorCopowerInclusion k ((Q).obj ⟨q, e⟩)
        ((Rep).obj ⟨q, e⟩) (ModuleCat.freeMk f) (Finsupp.single m a)) =
      Finsupp.single ⟨f, m⟩ a := by
  ext p
  rcases p with ⟨g, l⟩
  rw [representableLaurentCellCoordinates_apply]
  have generator := ConcreteCategory.congr_hom
    (Cellular.vectorCopowerFreeBiproductIso_generator k ((Q).obj ⟨q, e⟩)
      (c ⟶ (⟨q, e⟩ : IncidenceObject A)) f) (Finsupp.single m a)
  change (Cellular.vectorCopowerFreeBiproductIso k ((Q).obj ⟨q, e⟩)
      (c ⟶ (⟨q, e⟩ : IncidenceObject A))).hom
      (Cellular.vectorCopowerInclusion k ((Q).obj ⟨q, e⟩)
        ((Rep).obj ⟨q, e⟩) (ModuleCat.freeMk f) (Finsupp.single m a)) =
    biproduct.ι (fun _ : c ⟶ (⟨q, e⟩ : IncidenceObject A) => (Q).obj ⟨q, e⟩) f
      (Finsupp.single m a) at generator
  rw [generator, ← ModuleCat.comp_apply]
  by_cases equal : f = g
  · subst g
    rw [biproduct.ι_π_self, ModuleCat.id_apply]
    simp only [Finsupp.single_apply, Sigma.mk.inj_iff, heq_eq_eq, true_and]
    change (Finsupp.single m a) l = if m = l then a else 0
    exact Finsupp.single_apply
  · rw [biproduct.ι_π_ne _ equal]
    change (0 : k) = (Finsupp.single
      (⟨f, m⟩ : Σ f : c ⟶ (⟨q, e⟩ : IncidenceObject A),
        ReflectedLaurentWeight A S ⟨q, e⟩) a) ⟨g, l⟩
    symm
    exact Finsupp.single_eq_of_ne (fun h => equal (congrArg Sigma.fst h).symm)

/-- The inverse coordinate map sends a basis vector to its actual
copower inclusion. -/
theorem representableLaurentCellCoordinates_symm_single (q : ℕ)
    (e : NormalizedCell A q) (f : c ⟶ (⟨q, e⟩ : IncidenceObject A))
    (m : ReflectedLaurentWeight A S ⟨q, e⟩) (a : k) :
    (representableLaurentCellCoordinates A S k c q e).symm (Finsupp.single ⟨f, m⟩ a) =
      Cellular.vectorCopowerInclusion k ((Q).obj ⟨q, e⟩)
        ((Rep).obj ⟨q, e⟩) (ModuleCat.freeMk f) (Finsupp.single m a) := by
  apply (representableLaurentCellCoordinates A S k c q e).injective
  rw [LinearEquiv.apply_symm_apply, representableLaurentCellCoordinates_generator]

/-- The two actual coefficient actions are incidence composition and
the matching character shift, with coefficient unchanged. -/
theorem representableLaurentCellMap_generator {q r : ℕ}
    (e : NormalizedCell A q) (d : NormalizedCell A r)
    (h : (⟨q, e⟩ : IncidenceObject A) ⟶ ⟨r, d⟩)
    (f : c ⟶ (⟨q, e⟩ : IncidenceObject A))
    (m : ReflectedLaurentWeight A S ⟨q, e⟩) (a : k) :
    representableLaurentCellCoordinates A S k c r d
      ((Coefficients).map h
        (Cellular.vectorCopowerInclusion k ((Q).obj ⟨q, e⟩)
          ((Rep).obj ⟨q, e⟩) (ModuleCat.freeMk f) (Finsupp.single m a))) =
      Finsupp.single ⟨f ≫ h, reflectedLaurentWeightMap A S h m⟩ a := by
  have action := ConcreteCategory.congr_hom
    (Cellular.covariantCopowerDiagram_map_inclusion k Q Rep h (ModuleCat.freeMk f))
    (Finsupp.single m a)
  simp only [ModuleCat.comp_apply, Cellular.representable_map_freeMk,
    reflectedLaurentDiagram_map_single] at action
  exact (congrArg (representableLaurentCellCoordinates A S k c r d) action).trans
    (representableLaurentCellCoordinates_generator A S k c r d
      (f ≫ h) (reflectedLaurentWeightMap A S h m) a)

/-- The same formula holds for every actual Laurent sum. -/
theorem representableLaurentCellMap_coordinates {q r : ℕ}
    (e : NormalizedCell A q) (d : NormalizedCell A r)
    (h : (⟨q, e⟩ : IncidenceObject A) ⟶ ⟨r, d⟩)
    (x : (Coefficients).obj ⟨q, e⟩) :
    representableLaurentCellCoordinates A S k c r d ((Coefficients).map h x) =
      Finsupp.mapDomain
        (fun p : Σ f : c ⟶ (⟨q, e⟩ : IncidenceObject A),
          ReflectedLaurentWeight A S ⟨q, e⟩ =>
          ⟨p.1 ≫ h, reflectedLaurentWeightMap A S h p.2⟩)
        (representableLaurentCellCoordinates A S k c q e x) := by
  obtain ⟨p, rfl⟩ := (representableLaurentCellCoordinates A S k c q e).symm.surjective x
  rw [LinearEquiv.apply_symm_apply]
  induction p using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.mapDomain_zero]
  | add p p' hp hp' => simp only [map_add, Finsupp.mapDomain_add, hp, hp']
  | single p a =>
    rcases p with ⟨f, m⟩
    rw [representableLaurentCellCoordinates_symm_single,
      representableLaurentCellMap_generator, Finsupp.mapDomain_single]

end ToricPower.IntegralArrangement
