module

public import ToricPower.ArrangementIncidenceCostalk

/-!
# Costalk functor on every integral lift of the incidence category

Objects retain both a normalized arrangement cell and an arbitrary
integral character. An incidence changes the character by its recorded
lattice translation. This is an infinite category: no bound on lifts or
on characters enters the construction.

The relative cellular chain maps form an actual functor, before taking
homology. Scalar duality gives the contravariant cochain functor. Thus
identity and composition are consequences of the literal topological
translations and cellular functoriality, rather than extra assumptions
on the coefficient identifications.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (matrix : Fin s → Fin n → ℤ)

local instance weightedIncidencePeriodicCW : CWComplex (arrangementCarrier matrix) :=
  periodicArrangementCWComplex matrix

/-- A normalized cell together with every possible full integral weight. -/
def WeightedIncidenceObject := IncidenceObject matrix × (Fin n → ℤ)

/-- The incidence translation records the exact change of weight. -/
abbrev WeightedIncidenceHom (c d : WeightedIncidenceObject matrix) :=
  {f : c.1 ⟶ d.1 // d.2 = c.2 + f.val}

@[reducible]
instance weightedIncidenceCategory : Category (WeightedIncidenceObject matrix) where
  Hom := WeightedIncidenceHom matrix
  id c := ⟨𝟙 c.1, by simp only [incidence_id_val, add_zero]⟩
  comp f g := ⟨f.val ≫ g.val, by
    rw [incidence_comp_val, ← add_assoc, ← f.property, ← g.property]⟩
  id_comp f := by apply Subtype.ext; exact Category.id_comp f.val
  comp_id f := by apply Subtype.ext; exact Category.comp_id f.val
  assoc f g h := by apply Subtype.ext; exact Category.assoc f.val g.val h.val

@[simp]
theorem weightedIncidence_id_val (c : WeightedIncidenceObject matrix) :
    (𝟙 c : c ⟶ c).val = 𝟙 c.1 := rfl

@[simp]
theorem weightedIncidence_comp_val {c d e : WeightedIncidenceObject matrix}
    (f : c ⟶ d) (g : d ⟶ e) : (f ≫ g).val = f.val ≫ g.val := rfl

/-- Zero translation is the identity on the actual ambient space. -/
@[simp]
theorem arrangementTranslation_zero :
    arrangementTranslation matrix (0 : Fin n → ℤ) = 𝟙 (TopCat.of (arrangementCarrier matrix)) := by
  ext x j
  simp [arrangementTranslation, latticeLift]

/-- Addition of lattice vectors is actual composition of ambient maps. -/
theorem arrangementTranslation_add (a b : Fin n → ℤ) :
    arrangementTranslation matrix (a + b) =
      arrangementTranslation matrix a ≫ arrangementTranslation matrix b := by
  ext x j
  simp [arrangementTranslation, latticeLift, add_assoc]

variable (selected : Set (Fin s ⊕ Fin n))

/-- The literal complementary subcomplex for the chosen cell and full
integral character. -/
def weightedCostalkComplement (c : WeightedIncidenceObject matrix) :
    CWComplex.Subcomplex (arrangementCarrier matrix) :=
  periodicCostalkComplementSubcomplex matrix selected
    (augmentedLatticePairing matrix c.2) (incidenceCellCenter matrix c.1)

/-- The actual translation preserves the two relative bases. -/
theorem weightedCostalk_base {c d : WeightedIncidenceObject matrix} (f : c ⟶ d)
    (p : arrangementCarrier matrix) (outside : p.val ∈ weightedCostalkComplement matrix selected c) :
    (arrangementTranslation matrix f.val.val p).val ∈ weightedCostalkComplement matrix selected d := by
  change p.val ∉ costalkRegion (augmentedForms matrix) selected
    (augmentedLatticePairing matrix c.2) (incidenceCellCenter matrix c.1) at outside
  change p.val + latticeLift f.val.val ∉ costalkRegion (augmentedForms matrix) selected
    (augmentedLatticePairing matrix d.2) (incidenceCellCenter matrix d.1)
  intro inside
  have middle := incidence_costalkRegion_subset matrix f.val selected
    (augmentedLatticePairing matrix d.2) inside
  have shiftEquality : augmentedLatticePairing matrix d.2 =
      augmentedLatticePairing matrix c.2 + augmentedLatticePairing matrix f.val.val :=
    (congrArg (augmentedLatticePairing matrix) f.property).trans
      (augmentedLatticePairing_add matrix c.2 f.val.val)
  rw [shiftEquality] at middle
  exact outside ((add_mem_costalkRegion_iff (augmentedForms matrix) selected
    (augmentedLatticePairing matrix c.2) (augmentedLatticePairing matrix f.val.val)
    (latticeLift f.val.val) (augmentedForms_latticeLift matrix f.val.val)
    (incidenceCellCenter matrix c.1) p.val).mp middle)

variable {k : Type} [Ring k] (M : ModuleCat.{0} k)

/-- The literal chain complex at a cell and an arbitrary weight. -/
def weightedCostalkComplex (c : WeightedIncidenceObject matrix) :
    ChainComplex (ModuleCat.{0} k) ℕ :=
  relativeCellularComplex M (weightedCostalkComplement matrix selected c)

/-- Every weighted incidence acts by its actual ambient lattice map. -/
def weightedCostalkChainMap {c d : WeightedIncidenceObject matrix} (f : c ⟶ d) :
    weightedCostalkComplex matrix selected M c ⟶ weightedCostalkComplex matrix selected M d :=
  relativeCWChainMap (weightedCostalkComplement matrix selected c)
    (weightedCostalkComplement matrix selected d) (arrangementTranslation matrix f.val.val)
    M (arrangementTranslation_cellular matrix f.val.val)
    (weightedCostalk_base matrix selected f)

@[simp]
theorem weightedCostalkChainMap_id (c : WeightedIncidenceObject matrix) :
    weightedCostalkChainMap matrix selected M (𝟙 c) =
      𝟙 (weightedCostalkComplex matrix selected M c) := by
  refine Eq.trans (relativeCWChainMap_congr
    (weightedCostalkComplement matrix selected c) (weightedCostalkComplement matrix selected c)
    _ M _ _ (TauCeti.isCellular_id (arrangementCarrier matrix))
    (weightedCostalk_base matrix selected (𝟙 c)) (fun _ h => h)
    (arrangementTranslation_zero matrix)) ?_
  exact relativeCWChainMap_id M _

@[reassoc]
theorem weightedCostalkChainMap_comp {c d e : WeightedIncidenceObject matrix}
    (f : c ⟶ d) (g : d ⟶ e) :
    weightedCostalkChainMap matrix selected M (f ≫ g) =
      weightedCostalkChainMap matrix selected M f ≫ weightedCostalkChainMap matrix selected M g := by
  refine Eq.trans (relativeCWChainMap_congr
    (weightedCostalkComplement matrix selected c) (weightedCostalkComplement matrix selected e)
    _ M _ _
    (TauCeti.IsCellular.comp (arrangementCarrier matrix) (arrangementCarrier matrix)
      (arrangementTranslation_cellular matrix f.val.val)
      (arrangementTranslation_cellular matrix g.val.val))
    (weightedCostalk_base matrix selected (f ≫ g))
    (fun p h => weightedCostalk_base matrix selected g _
      (weightedCostalk_base matrix selected f p h))
    (arrangementTranslation_add matrix f.val.val g.val.val)) ?_
  exact relativeCWChainMap_comp
    (weightedCostalkComplement matrix selected c) (weightedCostalkComplement matrix selected d)
    _ M (weightedCostalkComplement matrix selected e) _
    (arrangementTranslation_cellular matrix f.val.val)
    (arrangementTranslation_cellular matrix g.val.val)
    (weightedCostalk_base matrix selected f) (weightedCostalk_base matrix selected g)

/-- A genuine chain-level functor on all integral lifts. -/
def weightedCostalkChainFunctor : WeightedIncidenceObject matrix ⥤ ChainComplex (ModuleCat.{0} k) ℕ where
  obj := weightedCostalkComplex matrix selected M
  map := weightedCostalkChainMap matrix selected M
  map_id := weightedCostalkChainMap_id matrix selected M
  map_comp := weightedCostalkChainMap_comp matrix selected M

variable (𝕜 : Type) [Field 𝕜]

/-- Scalar duality gives the actual contravariant cochain diagram, with
every integral weight retained. -/
def weightedCostalkCochainFunctor :
    (WeightedIncidenceObject matrix)ᵒᵖ ⥤ CochainComplex (ModuleCat.{0} 𝕜) ℕ :=
  (weightedCostalkChainFunctor matrix selected (ModuleCat.of 𝕜 𝕜)).op ⋙
    HomologicalComplex.opFunctor _ _ ⋙ (scalarDual 𝕜).mapHomologicalComplex _

end ToricPower.IntegralArrangement
