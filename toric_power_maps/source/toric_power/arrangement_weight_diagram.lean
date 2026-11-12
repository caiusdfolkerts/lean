module

public import ToricPower.ArrangementCochainFreeCoordinates
public import ToricPower.ArrangementRepresentableLaurentDiagram

/-!
# The genuine character fibers of a representable coefficient diagram

The total character is the Laurent character minus the recorded incidence
translation. Every incidence preserves this total character. Its fiber is
therefore an actual coefficient functor, and its cellular cochains are an
actual summand of the original full Laurent construction. The indexing
equivalence below retains the literal coface, incidence, and monomial
inequalities used by the independently constructed geometric costalk.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (S : Set (Fin s))
  (c : IncidenceObject A) (m : Fin n → ℤ)

/-- All genuine incidences in one total-character fiber. -/
def RepresentedWeightIndex (d : IncidenceObject A) :=
  {f : c ⟶ d // ∀ i ∈ S,
    0 ≤ rayPairing A (m + f.val) i + reflectedCeiling A d.2.val i}

instance representedWeightIndex_finite (d : IncidenceObject A) :
    Finite (RepresentedWeightIndex A S c m d) := by
  unfold RepresentedWeightIndex
  infer_instance

/-- Actual postcomposition preserves the full character condition. -/
def representedWeightIndexMap {d e : IncidenceObject A} (h : d ⟶ e) :
    RepresentedWeightIndex A S c m d → RepresentedWeightIndex A S c m e :=
  fun f => ⟨f.val ≫ h, by
    have allowed := (reflectedLaurentWeightMap A S h
      (⟨m + f.val.val, f.property⟩ : ReflectedLaurentWeight A S d)).property
    simpa only [reflectedLaurentWeightMap, incidence_comp_val, add_assoc] using allowed⟩

@[simp]
theorem representedWeightIndexMap_id (d : IncidenceObject A) :
    representedWeightIndexMap A S c m (𝟙 d) = id := by
  funext f
  apply Subtype.ext
  exact Category.comp_id f.val

@[simp]
theorem representedWeightIndexMap_comp {d e f : IncidenceObject A}
    (h : d ⟶ e) (g : e ⟶ f) :
    representedWeightIndexMap A S c m (h ≫ g) =
      representedWeightIndexMap A S c m g ∘ representedWeightIndexMap A S c m h := by
  funext p
  apply Subtype.ext
  exact (Category.assoc p.val h g).symm

/-- The fixed-character basis is exactly the geometric costalk basis. -/
def representedWeightCostalkIndexEquiv (q : ℕ) :
    (Σ d : NormalizedCell A q, RepresentedWeightIndex A S c m ⟨q, d⟩) ≃
      RepresentableCostalkIndex A c S m q where
  toFun p := ⟨⟨p.1, p.2.val⟩, p.2.property⟩
  invFun p := ⟨p.val.1, ⟨p.val.2, p.property⟩⟩
  left_inv p := by rcases p with ⟨d, f, hf⟩; rfl
  right_inv p := by rcases p with ⟨⟨d, f⟩, hf⟩; rfl

variable (k : Type) [Field k]

/-- The actual coefficient functor in one unrestricted integral weight. -/
def representedWeightDiagram : IncidenceObject A ⥤ ModuleCat.{0} k where
  obj d := ModuleCat.of k (RepresentedWeightIndex A S c m d →₀ k)
  map h := ModuleCat.ofHom (Finsupp.lmapDomain k k (representedWeightIndexMap A S c m h))
  map_id d := by
    rw [representedWeightIndexMap_id, Finsupp.lmapDomain_id]
    rfl
  map_comp h g := by
    rw [representedWeightIndexMap_comp, Finsupp.lmapDomain_comp]
    rfl

@[simp]
theorem representedWeightDiagram_map_single {d e : IncidenceObject A}
    (h : d ⟶ e) (f : RepresentedWeightIndex A S c m d) (r : k) :
    (representedWeightDiagram A S c m k).map h (Finsupp.single f r) =
      Finsupp.single (representedWeightIndexMap A S c m h f) r :=
  Finsupp.mapDomain_single

/-- The same original cellular construction, evaluated on its genuine
character-fiber functor. -/
def representedWeightCellularComplex : CochainComplex (ModuleCat.{0} k) ℕ :=
  arrangementCellularCochainComplex A k (representedWeightDiagram A S c m k)

/-- Coordinates in the literal costalk index, before any homology
calculation or assertion of exactness. -/
def representedWeightCellularCoordinates (q : ℕ) :
    (representedWeightCellularComplex A S c m k).X q ≃ₗ[k]
      (RepresentableCostalkIndex A c S m q →₀ k) :=
  (cellularCochainFreeCoordinates A k (representedWeightDiagram A S c m k)
    (RepresentedWeightIndex A S c m) (fun _ => LinearEquiv.refl k _) q).trans
      (Finsupp.mapDomain.linearEquiv k k (representedWeightCostalkIndexEquiv A S c m q))

theorem representedWeightCellularCoordinates_apply (q : ℕ)
    (v : (representedWeightCellularComplex A S c m k).X q)
    (i : RepresentableCostalkIndex A c S m q) :
    representedWeightCellularCoordinates A S c m k q v i =
      Finsupp.lapply (R := k) (M := k) (⟨i.val.2, i.property⟩ :
        RepresentedWeightIndex A S c m ⟨q, i.val.1⟩)
        (arrangementCellularCochainProjection A k (representedWeightDiagram A S c m k)
          q i.val.1 v) := by
  change Finsupp.mapDomain (representedWeightCostalkIndexEquiv A S c m q)
      (cellularCochainFreeCoordinates A k (representedWeightDiagram A S c m k)
        (RepresentedWeightIndex A S c m) (fun _ => LinearEquiv.refl k _) q v) i = _
  have value := Finsupp.mapDomain_apply_of_injective
    (representedWeightCostalkIndexEquiv A S c m q).injective
    (cellularCochainFreeCoordinates A k (representedWeightDiagram A S c m k)
      (RepresentedWeightIndex A S c m) (fun _ => LinearEquiv.refl k _) q v)
    ((representedWeightCostalkIndexEquiv A S c m q).symm i)
  rw [Equiv.apply_symm_apply] at value
  exact value.trans (cellularCochainFreeCoordinates_apply A k
    (representedWeightDiagram A S c m k) (RepresentedWeightIndex A S c m)
    (fun _ => LinearEquiv.refl k _) q v i.val.1 ⟨i.val.2, i.property⟩)

/-- Each coordinate basis vector is the actual cellwise inclusion of
the corresponding incidence coefficient. -/
theorem representedWeightCellularCoordinates_generator (q : ℕ)
    (i : RepresentableCostalkIndex A c S m q) (r : k) :
    representedWeightCellularCoordinates A S c m k q
      (arrangementCellularCochainInclusion A k (representedWeightDiagram A S c m k)
        q i.val.1 (Finsupp.single ⟨i.val.2, i.property⟩ r)) = Finsupp.single i r := by
  change Finsupp.mapDomain (representedWeightCostalkIndexEquiv A S c m q)
      (cellularCochainFreeCoordinates A k (representedWeightDiagram A S c m k)
        (RepresentedWeightIndex A S c m) (fun _ => LinearEquiv.refl k _) q
        (arrangementCellularCochainInclusion A k (representedWeightDiagram A S c m k)
          q i.val.1 (Finsupp.single ⟨i.val.2, i.property⟩ r))) = _
  have generator := cellularCochainFreeCoordinates_generator A k
    (representedWeightDiagram A S c m k) (RepresentedWeightIndex A S c m)
    (fun _ => LinearEquiv.refl k _) q i.val.1 ⟨i.val.2, i.property⟩ r
  exact (congrArg
    (Finsupp.mapDomain (representedWeightCostalkIndexEquiv A S c m q)) generator).trans
      Finsupp.mapDomain_single

theorem representedWeightCellularCoordinates_symm_single (q : ℕ)
    (i : RepresentableCostalkIndex A c S m q) (r : k) :
    (representedWeightCellularCoordinates A S c m k q).symm (Finsupp.single i r) =
      arrangementCellularCochainInclusion A k (representedWeightDiagram A S c m k)
        q i.val.1 (Finsupp.single ⟨i.val.2, i.property⟩ r) := by
  apply (representedWeightCellularCoordinates A S c m k q).injective
  rw [LinearEquiv.apply_symm_apply, representedWeightCellularCoordinates_generator]

end ToricPower.IntegralArrangement
