module

public import ToricPower.ArrangementIncidenceCeilings
public import ToricPower.ArrangementCostalkCells
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Full Laurent coefficients of the covariant Cartier labels

The label at a cell consists of all allowed integral characters, with
finite support for each individual section. Incidences translate these
characters by their actual lattice displacement. On a representable,
subtracting that displacement gives the exact costalk weight. This is a
reindexing of the full lattice, with no bounded-character hypothesis.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (S : Set (Fin s))

/-- Every integral monomial section of the reflected dual label. -/
def ReflectedLaurentWeight (c : IncidenceObject A) :=
  {m : Fin n → ℤ // ∀ i ∈ S,
    0 ≤ rayPairing A m i + reflectedCeiling A c.2.val i}

/-- The actual incidence character sends a permitted monomial to a
permitted monomial of the target label. -/
def reflectedLaurentWeightMap {c d : IncidenceObject A} (f : c ⟶ d) :
    ReflectedLaurentWeight A S c → ReflectedLaurentWeight A S d :=
  fun m => ⟨m.val + f.val, by
    intro i hi
    have original := m.property i hi
    have multiplier := (incidence_ceiling_bounds A f i).1
    have pairingAdd : rayPairing A (m.val + f.val) i =
        rayPairing A m.val i + rayPairing A f.val i := by
      simp [rayPairing, mul_add, Finset.sum_add_distrib]
    rw [pairingAdd]
    omega⟩

@[simp]
theorem reflectedLaurentWeightMap_id (c : IncidenceObject A) :
    reflectedLaurentWeightMap A S (𝟙 c) = id := by
  funext m
  apply Subtype.ext
  simp only [reflectedLaurentWeightMap, incidence_id_val, add_zero]
  rfl

@[simp]
theorem reflectedLaurentWeightMap_comp {c d e : IncidenceObject A}
    (f : c ⟶ d) (g : d ⟶ e) :
    reflectedLaurentWeightMap A S (f ≫ g) =
      reflectedLaurentWeightMap A S g ∘ reflectedLaurentWeightMap A S f := by
  funext m
  apply Subtype.ext
  simp only [reflectedLaurentWeightMap, incidence_comp_val, Function.comp_apply, add_assoc]

variable (k : Type) [CommRing k]

/-- The full Laurent coefficient diagram, with the genuine monomial
map on every incidence and no discarded weights. -/
def reflectedLaurentDiagram : IncidenceObject A ⥤ ModuleCat.{0} k where
  obj c := ModuleCat.of k (ReflectedLaurentWeight A S c →₀ k)
  map f := ModuleCat.ofHom (Finsupp.lmapDomain k k (reflectedLaurentWeightMap A S f))
  map_id c := by
    rw [reflectedLaurentWeightMap_id, Finsupp.lmapDomain_id]
    rfl
  map_comp f g := by
    rw [reflectedLaurentWeightMap_comp, Finsupp.lmapDomain_comp]
    rfl

@[simp]
theorem reflectedLaurentDiagram_map_single {c d : IncidenceObject A} (f : c ⟶ d)
    (m : ReflectedLaurentWeight A S c) (a : k) :
    (reflectedLaurentDiagram A S k).map f (Finsupp.single m a) =
      Finsupp.single (reflectedLaurentWeightMap A S f m) a :=
  Finsupp.mapDomain_single

/-- The genuine incidence basis and every Laurent monomial in the
corresponding cell coefficient. -/
def RepresentableLaurentIndex (c : IncidenceObject A) (q : ℕ) :=
  Σ e : NormalizedCell A q, Σ f : c ⟶ (⟨q, e⟩ : IncidenceObject A),
    ReflectedLaurentWeight A S ⟨q, e⟩

/-- The total character is the label character minus the literal
incidence displacement. Its fiber is exactly the proved costalk index. -/
def representableLaurentWeightEquiv (c : IncidenceObject A) (q : ℕ) :
    RepresentableLaurentIndex A S c q ≃
      Σ m : Fin n → ℤ, RepresentableCostalkIndex A c S m q where
  toFun p := ⟨p.2.2.val - p.2.1.val,
    ⟨⟨p.1, p.2.1⟩, by
      simpa only [sub_add_cancel] using p.2.2.property⟩⟩
  invFun p := ⟨p.2.val.1, p.2.val.2, ⟨p.1 + p.2.val.2.val, p.2.property⟩⟩
  left_inv p := by
    rcases p with ⟨e, f, m, hm⟩
    change (⟨e, f, ⟨m - f.val + f.val, _⟩⟩ : RepresentableLaurentIndex A S c q) =
      ⟨e, f, ⟨m, hm⟩⟩
    simp only [sub_add_cancel]
  right_inv p := by
    rcases p with ⟨m, ⟨⟨e, f⟩, hm⟩⟩
    change (⟨m + f.val - f.val, ⟨⟨e, f⟩, _⟩⟩ :
      Σ m : Fin n → ℤ, RepresentableCostalkIndex A c S m q) =
      ⟨m, ⟨⟨e, f⟩, hm⟩⟩
    apply Sigma.ext (add_sub_cancel_right m f.val)
    apply (Subtype.heq_iff_coe_eq (fun p => by
      simp only [add_sub_cancel_right])).mpr
    rfl

/-- The same exhaustive reindexing on actual finite Laurent sums. -/
def representableLaurentCoefficientsEquiv (c : IncidenceObject A) (q : ℕ) :
    (RepresentableLaurentIndex A S c q →₀ k) ≃ₗ[k]
      ((Σ m : Fin n → ℤ, RepresentableCostalkIndex A c S m q) →₀ k) :=
  Finsupp.mapDomain.linearEquiv k k (representableLaurentWeightEquiv A S c q)

end ToricPower.IntegralArrangement
