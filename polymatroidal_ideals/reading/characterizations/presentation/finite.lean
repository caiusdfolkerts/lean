import Characterizations.Presentation.Connectivity
import Characterizations.WitnessPaths
import Characterizations.VariableOrders

/-! # Conventional finite free presentations and the local exchange criterion -/
noncomputable section
@[reducible] local instance (priority := 2000) presentationDecEq (α : Type*) [Fintype α] : DecidableEq α := Classical.decEq α
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.Presentation
open Classical Finset MvPolynomial CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [DecidableEq V] [CommRing k]

/-- An actual finite free presentation of the original monomial ideal, with all
first differential entries linear. The canonical free generators have the common
degree of the monomial generating family. -/
structure FiniteLinearPresentation (B : Family V) where
  rank : ℕ
  differential : (Fin rank → MvPolynomial V k) →ₗ[MvPolynomial V k] Free (k := k) B
  exact : LinearMap.range differential = LinearMap.ker (augmentation B)
  linear : Resolution.IsHomogeneousMap differential 1

lemma augmentation_range (B : Family V) :
    LinearMap.range (augmentation (k := k) B) = monomialIdeal k B := by
  rw [augmentation, Fintype.range_linearCombination, monomialIdeal]
  apply congrArg (Submodule.span (MvPolynomial V k))
  ext x
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b.val, b.property, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, hb⟩, rfl⟩

lemma FiniteLinearPresentation.hasLinearPresentation {B : Family V}
    (P : FiniteLinearPresentation (k := k) B) : HasLinearPresentation (k := k) B := by
  intro x hx
  rw [← P.exact] at hx
  obtain ⟨y, rfl⟩ := hx
  have hy : y = ∑ j, y j • Pi.single j (1 : MvPolynomial V k) := by
    ext j
    simp [Pi.single_apply]
  rw [hy, map_sum]
  apply Submodule.sum_mem
  intro j hj
  rw [map_smul]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  constructor
  · rw [← P.exact]
    exact LinearMap.mem_range_self _ _
  · exact fun b => P.linear b j

abbrev Edges (B : Family V) :=
  {ab : Generators B × Generators B // UnitStep ab.1.val ab.2.val}

def edgeColumn (B : Family V) (j : Fin (Fintype.card (Edges B))) : Free (k := k) B :=
  let ab := (Fintype.equivFin (Edges B)).symm j
  pairSyzygy B ab.val.1 ab.val.2

lemma edgeColumn_range (B : Family V) :
    Set.range (edgeColumn (k := k) B) =
      {x | ∃ a b : Generators B, UnitStep a.val b.val ∧ x = pairSyzygy B a b} := by
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    let ab := (Fintype.equivFin (Edges B)).symm j
    exact ⟨ab.val.1, ab.val.2, ab.property, rfl⟩
  · rintro ⟨a, b, hab, rfl⟩
    refine ⟨(Fintype.equivFin (Edges B)) ⟨(a, b), hab⟩, ?_⟩
    simp [edgeColumn]

/-- The first free module has one basis vector for each ordered unit-exchange
edge. Exactness follows from the proved algebraic syzygy criterion. -/
def finiteLinearPresentationOfCondition {B : Family V} {d : ℕ}
    (hB : Equigenerated B d) (h : HasLinearPresentation (k := k) B) :
    FiniteLinearPresentation (k := k) B where
  rank := Fintype.card (Edges B)
  differential := Fintype.linearCombination _ (edgeColumn B)
  exact := by
    rw [Fintype.range_linearCombination, edgeColumn_range]
    change edgeSpan B = LinearMap.ker (augmentation B)
    apply le_antisymm (edgeSpan_le_ker B)
    simpa only [HasLinearPresentation, linearSpan_eq_edgeSpan hB] using h
  linear := by
    intro b j
    have he : Fintype.linearCombination (MvPolynomial V k) (edgeColumn (k := k) B) (Pi.single j 1) = edgeColumn (k := k) B j := by
      simp [Fintype.linearCombination_apply, Pi.single_apply]
    rw [he]
    let ab := (Fintype.equivFin (Edges B)).symm j
    exact pairSyzygy_linear B ab.val.1 ab.val.2 ab.property b

/-- The syzygy-generation definition is equivalent to a literal finite free
presentation with linear entries. -/
theorem nonempty_finiteLinearPresentation_iff {B : Family V} {d : ℕ}
    (hB : Equigenerated B d) :
    Nonempty (FiniteLinearPresentation (k := k) B) ↔ HasLinearPresentation (k := k) B :=
  ⟨fun ⟨P⟩ => P.hasLinearPresentation, fun h => ⟨finiteLinearPresentationOfCondition hB h⟩⟩

/-- Lemma 3.1, stated directly with the actual finite free presentation. -/
theorem finiteLinearPresentation_iff_boxConnected [Nontrivial k] {B : Family V} {d : ℕ}
    (hB : Equigenerated B d) :
    Nonempty (FiniteLinearPresentation (k := k) B) ↔ BoxConnected B :=
  (nonempty_finiteLinearPresentation_iff hB).trans (linearPresentation_iff_boxConnected hB)

/-- Exchange restricted exactly to pairs at the paper's distance four. -/
def DistanceFourExchange (B : Family V) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, l1Distance a b = 4 → ∀ i, b i < a i →
    ∃ j, a j < b j ∧ exchange a i j ∈ B

/-- Theorem 3.3, with a genuine finite linear presentation and the full prescribed
donor exchange condition. -/
theorem polymatroidal_iff_linearPresentation_distanceFour [Nontrivial k]
    {B : Family V} {d : ℕ} (hB : Equigenerated B d) :
    IsPolymatroidal B ↔ Nonempty (FiniteLinearPresentation (k := k) B) ∧ DistanceFourExchange B := by
  constructor
  · intro h
    constructor
    · apply (finiteLinearPresentation_iff_boxConnected hB).mpr
      let o : VariableOrder V := Fintype.equivFin V
      exact boxConnected_of_linearQuotients hB (variableRevlex_irrefl o)
        (variableRevlex_trans o) (variableRevlex_total o)
        (polymatroidal_variable_linearQuotients (k := k) h.2 o)
    · intro a ha b hb _ i hi
      exact h.2 a ha b hb i hi
  · rintro ⟨hp, he⟩
    refine ⟨⟨d, hB⟩, ?_⟩
    by_contra hn
    obtain ⟨a, b, ha, hb, hd, i, hi, hbad⟩ :=
      failed_exchange_distance_four ((finiteLinearPresentation_iff_boxConnected hB).mp hp) hn
    obtain ⟨j, hj, hjB⟩ := he a ha b hb hd i hi
    exact hbad j hj hjB

end Characterizations.Presentation
