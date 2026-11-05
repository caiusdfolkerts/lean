module

public import Papers.GraphicalZonotopes.UnitFamilyStructure
public import Papers.GraphicalZonotopes.UnitTranslatedGeometry
public import Papers.GraphicalZonotopes.FourPartGraphRecognition
public import Papers.GraphicalZonotopes.PrincipalTargets

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace GraphicalZonotopes
open Finset RefinedTriangleComponents

namespace UnitLatticeGeometry

/-- The actual coefficient model has a Cartesian tetrahedral family. Its
coverage forces the entire ambient graph to be the corresponding four-partite
graph; no extra ambient edges or unused vertices remain. -/
theorem CoefficientModel.classification {n : ℕ} {G : SimpleGraph (Fin n)}
    {Q : Set (Fin n → ℝ)} (M : CoefficientModel G Q) (hG : G.CliqueFree 5) :
    actualDirectionGraph Q=G ∧ n≤8 ∧
      ∃ a : Fin 4 → ℕ,(∀ i,a i=1 ∨ a i=2) ∧ Nonempty (G ≃g fourPartite a) := by
  let F := family (mobius M.function)
  have hmem : ∀ D,D∈F ↔ D.card=4 ∧ mobius M.function D≠0 := mem_family _
  obtain ⟨hthin,hsquare⟩ := UnitFamilyStructure.structure_of_boolean
    hG M.supported M.boolean hmem
  obtain ⟨A,hsize,hdis,hprod⟩ := FourPartCompletion.cartesian_completion F
    (fun D hD => ((hmem D).mp hD).1) M.nonempty M.connected hthin hsquare
  have hneA : ∀ i,(A i).Nonempty := by
    intro i
    apply card_pos.mp
    rcases hsize i with he | he <;> omega
  obtain ⟨P,hP⟩ := FourPartGraphRecognition.parts_of_cover F A hneA hdis hprod M.covers
  have hproduct : FourPartGraphRecognition.ProductFamily F P.parts := by
    rw [hP]
    exact hprod
  have hsizeP : ∀ i,(P.parts i).card=1 ∨ (P.parts i).card=2 := by
    rw [hP]
    exact hsize
  have hcl : ∀ D∈F,G.IsClique D := by
    intro D hD
    exact M.supported.clique_of_nonzero ((hmem D).mp hD).2
  obtain ⟨he,hcard,hiso⟩ := FourPartGraphRecognition.recognize P F hproduct hsizeP hcl
    (BooleanFourPartStructure.clique_card_le_four hG)
  have hedge : edgeGraph (mobius M.function)=FourPartGraphRecognition.unionGraph F := rfl
  exact ⟨M.directions.trans (hedge.trans he),by simpa using hcard,hiso⟩

end UnitLatticeGeometry

/-- Theorem 9.5, in its complete unit-summand range: all n≥4, the given
K5-free ambient graph, full dimension, and actual lattice polytopes. -/
theorem unit_lattice_classification : Targets.UnitLatticeClassification := by
  intro n hn G hG Q hQ hi hd hsum
  obtain ⟨M⟩ := UnitLatticeGeometry.coefficient_model hn hG hQ hi hd hsum
  exact M.classification hG

/-- The same theorem with the traditional polytope-only definition of
Minkowski indecomposability, whose equivalence is derived from the actual sum. -/
theorem unit_lattice_classification_polytopal {n : ℕ} (hn : 4≤n)
    {G : SimpleGraph (Fin n)} (hG : G.CliqueFree 5)
    {Q : Set (Fin n → ℝ)} (hQ : LatticePolytope Q)
    (hi : PolytopalMinkowskiIndecomposable Q) (hd : FullDimension Q)
    (hsum : IsMinkowskiSummand Q (graphicalZonotope G)) :
    actualDirectionGraph Q=G ∧ n≤8 ∧
      ∃ a : Fin 4 → ℕ,(∀ i,a i=1 ∨ a i=2) ∧ Nonempty (G ≃g fourPartite a) := by
  obtain ⟨M⟩ := UnitLatticeGeometry.coefficient_model_polytopal hn hG hQ hi hd hsum
  exact M.classification hG

/-- Arbitrary real translations of lattice polytopes obey the same exact
classification, with every conclusion stated on the original translated body. -/
theorem unit_translated_lattice_classification {n : ℕ} (hn : 4≤n)
    {G : SimpleGraph (Fin n)} (hG : G.CliqueFree 5)
    {Q : Set (Fin n → ℝ)} (hQ : TranslatedLatticePolytope Q)
    (hi : MinkowskiIndecomposable Q) (hd : FullDimension Q)
    (hsum : IsMinkowskiSummand Q (graphicalZonotope G)) :
    actualDirectionGraph Q=G ∧ n≤8 ∧
      ∃ a : Fin 4 → ℕ,(∀ i,a i=1 ∨ a i=2) ∧ Nonempty (G ≃g fourPartite a) := by
  obtain ⟨M⟩ := UnitLatticeGeometry.coefficient_model_translated hn hG hQ hi hd hsum
  exact M.classification hG

theorem unit_translated_lattice_classification_polytopal {n : ℕ} (hn : 4≤n)
    {G : SimpleGraph (Fin n)} (hG : G.CliqueFree 5)
    {Q : Set (Fin n → ℝ)} (hQ : TranslatedLatticePolytope Q)
    (hi : PolytopalMinkowskiIndecomposable Q) (hd : FullDimension Q)
    (hsum : IsMinkowskiSummand Q (graphicalZonotope G)) :
    actualDirectionGraph Q=G ∧ n≤8 ∧
      ∃ a : Fin 4 → ℕ,(∀ i,a i=1 ∨ a i=2) ∧ Nonempty (G ≃g fourPartite a) := by
  obtain ⟨M⟩ := UnitLatticeGeometry.coefficient_model_translated_polytopal hn hG hQ hi hd hsum
  exact M.classification hG

end GraphicalZonotopes
