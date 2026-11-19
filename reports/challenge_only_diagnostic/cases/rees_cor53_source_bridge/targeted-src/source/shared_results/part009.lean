module
public import graph_foundation.part010
public import shared_results.part008

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphCoefficientIntegral -/
section

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {k : Type u} [CommRing k]

lemma closedGraph_contains_union {V : Type*} [DecidableEq V]
    (B C : Family V) (α : Exponent V) :
    Contains (B ∪ C) α ↔ Contains B α ∨ Contains C α := by
  constructor
  · rintro ⟨b, hb, hbα⟩
    rcases Finset.mem_union.mp hb with hb | hb
    · exact Or.inl ⟨b, hb, hbα⟩
    · exact Or.inr ⟨b, hb, hbα⟩
  · rintro (⟨b, hb, hbα⟩ | ⟨b, hb, hbα⟩)
    · exact ⟨b, Finset.mem_union_left _ hb, hbα⟩
    · exact ⟨b, Finset.mem_union_right _ hb, hbα⟩

variable {N m : ℕ} {G : SimpleGraph (Fin N)}

lemma closedGraphPredecessor_contains_iff (hG : IntervalLabeling G)
    {a : FiniteTuple (GraphRows N)} (ha : a ∈ graphEdgeLattice G)
    (α : Exponent (FiniteVariable.{u} (GraphRows N))) :
    Contains (finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) a) α ↔
      Contains (graphColonFamily G a) α := by
  rw [← finiteCoordinatePredecessor_contains_iff (graphEdgeLattice_closed hG) ha]
  exact graphCoordinateColon_contains_iff hG ha α

def closedGraphChainLinearVariables
    (w : FiniteMultichain (GraphRows N) (graphEdgeLattice G) m) :
    Finset (FiniteVariable.{u} (GraphRows N)) :=
  Finset.univ.biUnion (fun s => graphLinearVariables G (w.val s).val)

/-- Along a nonempty multichain the residual ideals are nested. Hence the
coefficient ideal is exactly the sum of all its linear variables and the
residual at the maximal edge. This is the literal version of equation (6.1). -/
theorem closedGraphChainCoefficient_contains_iff (hG : IntervalLabeling G)
    (w : FiniteMultichain (GraphRows N) (graphEdgeLattice G) (m + 1))
    (α : Exponent (FiniteVariable.{u} (GraphRows N))) :
    Contains (finiteChainCoefficientFamily (GraphRows N) w) α ↔
      Contains (variableMonomialFamily (closedGraphChainLinearVariables w) ∪
        finiteRowFamily (GraphRows N) (graphResidualEdges G (w.val (Fin.last m)).val)) α := by
  rw [closedGraph_contains_union]
  constructor
  · rintro ⟨b, hb, hbα⟩
    obtain ⟨s, hs, hbs⟩ := Finset.mem_biUnion.mp hb
    have hcol := (closedGraphPredecessor_contains_iff hG (w.val s).property α).mp
      ⟨b, hbs, hbα⟩
    rw [graphColonFamily, closedGraph_contains_union] at hcol
    rcases hcol with hlin | ⟨b, hb, hbα⟩
    · rcases hlin with ⟨b, hb, hbα⟩
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
      have hαv : 0 < α v := by
        simpa only [Finsupp.single_eq_same, Nat.succ_le_iff] using hbα v
      exact Or.inl ((contains_variableMonomialFamily (closedGraphChainLinearVariables w) α).mpr
        ⟨v, Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, hv⟩, hαv⟩)
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      exact Or.inr ⟨_, Finset.mem_image.mpr
        ⟨a, graphResidualEdges_mono hG (w.val s).property (w.val (Fin.last m)).property
          (w.property (Fin.le_last s)) ha, rfl⟩, hbα⟩
  · intro h
    have hstep : ∀ s : Fin (m + 1), Contains (graphColonFamily G (w.val s).val) α →
        Contains (finiteChainCoefficientFamily (GraphRows N) w) α := by
      intro s hs
      obtain ⟨b, hb, hbα⟩ :=
        (closedGraphPredecessor_contains_iff hG (w.val s).property α).mpr hs
      exact ⟨b, Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, hb⟩, hbα⟩
    rcases h with hlin | ⟨b, hb, hbα⟩
    · obtain ⟨v, hv, hαv⟩ :=
        (contains_variableMonomialFamily (closedGraphChainLinearVariables w) α).mp hlin
      obtain ⟨s, hs, hvs⟩ := Finset.mem_biUnion.mp hv
      apply hstep s
      rw [graphColonFamily, closedGraph_contains_union]
      exact Or.inl ⟨_, Finset.mem_image.mpr ⟨v, hvs, rfl⟩,
        Finsupp.single_le_iff.mpr hαv⟩
    · apply hstep (Fin.last m)
      exact ⟨b, Finset.mem_union_right _ hb, hbα⟩

section RemoveLinearVariables
variable {d : ℕ} {n : Fin d → ℕ}

def closedGraphRowsOutside (L : Finset (FiniteVariable.{u} n))
    (A : ∀ r, Finset (Fin (n r))) : ∀ r, Finset (Fin (n r)) :=
  fun r => (A r).filter (fun j => (⟨r, ULift.up j⟩ : FiniteVariable.{u} n) ∉ L)

lemma closedGraphRowsOutside_avoids (L : Finset (FiniteVariable.{u} n))
    (A : ∀ r, Finset (Fin (n r))) (r : Fin d) (j : Fin (n r))
    (hj : j ∈ closedGraphRowsOutside L A r) :
    (⟨r, ULift.up j⟩ : FiniteVariable.{u} n) ∉ L :=
  (Finset.mem_filter.mp hj).2

/-- Once the linear variables belong to an ideal, each remaining monomial
generator containing one of those variables is redundant. Removing exactly
those generators is an equality of divisibility predicates. -/
lemma closedGraph_rowFamily_variables_reduce
    (E : Finset (FiniteTuple n)) (L : Finset (FiniteVariable.{u} n))
    (A : ∀ r, Finset (Fin (n r))) (α : Exponent (FiniteVariable.{u} n)) :
    Contains (variableMonomialFamily L ∪ finiteRowFamily n (finiteRowRestriction E A)) α ↔
      Contains (variableMonomialFamily L ∪
        finiteRowFamily n (finiteRowRestriction E (closedGraphRowsOutside L A))) α := by
  rw [closedGraph_contains_union, closedGraph_contains_union]
  constructor
  · rintro (hL | ⟨b, hb, hbα⟩)
    · exact Or.inl hL
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      rcases (mem_finiteRowRestriction E A a).mp ha with ⟨haE, haA⟩
      by_cases hs : ∀ r, (⟨r, ULift.up (a r)⟩ : FiniteVariable.{u} n) ∉ L
      · exact Or.inr ⟨_, Finset.mem_image.mpr
          ⟨a, (mem_finiteRowRestriction E (closedGraphRowsOutside L A) a).mpr
            ⟨haE, fun r => Finset.mem_filter.mpr ⟨haA r, hs r⟩⟩, rfl⟩, hbα⟩
      · push_neg at hs
        obtain ⟨r, hr⟩ := hs
        apply Or.inl
        apply (contains_variableMonomialFamily L α).mpr
        refine ⟨⟨r, ULift.up (a r)⟩, hr, ?_⟩
        have hh := hbα ⟨r, ULift.up (a r)⟩
        simpa only [finiteRowExponent_apply, ite_true, Nat.succ_le_iff] using hh
  · rintro (hL | ⟨b, hb, hbα⟩)
    · exact Or.inl hL
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      rcases (mem_finiteRowRestriction E (closedGraphRowsOutside L A) a).mp ha with ⟨haE, haA⟩
      exact Or.inr ⟨_, Finset.mem_image.mpr
        ⟨a, (mem_finiteRowRestriction E A a).mpr
          ⟨haE, fun r => (Finset.mem_filter.mp (haA r)).1⟩, rfl⟩, hbα⟩

end RemoveLinearVariables

def closedGraphChainResidualRows
    (w : FiniteMultichain (GraphRows N) (graphEdgeLattice G) (m + 1)) :
    ∀ r, Finset (Fin (GraphRows N r)) :=
  closedGraphRowsOutside.{u} (closedGraphChainLinearVariables.{u} w)
    (graphResidualRows G (w.val (Fin.last m)).val (fun _ => Finset.univ))

theorem closedGraphChainCoefficient_faces (hG : IntervalLabeling G)
    (w : FiniteMultichain (GraphRows N) (graphEdgeLattice G) (m + 1))
    (α : Exponent (FiniteVariable.{u} (GraphRows N))) :
    quotientKoszulFaces (finiteChainCoefficientFamily (GraphRows N) w) α =
      quotientKoszulFaces (variableMonomialFamily (closedGraphChainLinearVariables w) ∪
        finiteRowFamily (GraphRows N)
          (finiteRowRestriction (graphEdgeLattice G) (closedGraphChainResidualRows.{u} w))) α := by
  apply quotientKoszulFaces_eq_of_contains
  intro β
  rw [closedGraphChainCoefficient_contains_iff hG w]
  have he := graphResidualRows_lattice_eq G (w.val (Fin.last m)).val (fun _ => Finset.univ)
  simp only [finiteRowRestriction_univ] at he
  rw [← he]
  exact closedGraph_rowFamily_variables_reduce (graphEdgeLattice G)
    (closedGraphChainLinearVariables w)
    (graphResidualRows G (w.val (Fin.last m)).val (fun _ => Finset.univ)) β

/-- Every nonempty-chain coefficient quotient has integral fine homology zero
or free of rank one. Linear variables and residual graph variables are split
by actual exterior multiplication, with all signs retained. -/
theorem closedGraph_chain_coefficient_homology_small_succ (hG : IntervalLabeling G)
    (w : FiniteMultichain (GraphRows N) (graphEdgeLattice G) (m + 1))
    (α : Exponent (FiniteVariable.{u} (GraphRows N))) :
    ClosedGraphSmallFreeModel k (ClosedGraphFaceHomology (k := k)
      (finiteChainCoefficientFamily (GraphRows N) w) α) :=
  ClosedGraphSmallFreeModel.of_equiv
    (quotientFaceHomologyEquivOfFaces _ _ α α (closedGraphChainCoefficient_faces hG w α))
    (closedGraph_linear_restriction_homology_small (k := k) hG
      (closedGraphChainLinearVariables w) (closedGraphChainResidualRows.{u} w)
      (closedGraphRowsOutside_avoids _ _) α)

theorem closedGraph_chain_coefficient_homology_small (hG : IntervalLabeling G)
    (w : FiniteMultichain (GraphRows N) (graphEdgeLattice G) m)
    (α : Exponent (FiniteVariable.{u} (GraphRows N))) :
    ClosedGraphSmallFreeModel k (ClosedGraphFaceHomology (k := k)
      (finiteChainCoefficientFamily (GraphRows N) w) α) := by
  cases m with
  | succ m => exact closedGraph_chain_coefficient_homology_small_succ hG w α
  | zero =>
    have hw : finiteChainCoefficientFamily.{u} (GraphRows N) w = ∅ := by
      simp [finiteChainCoefficientFamily]
    by_cases hα : α = 0
    · subst α
      apply Or.inr
      refine ⟨closedGraphZeroStrandHomologyEquiv _ ?_⟩
      rw [hw]
      rintro ⟨b, hb, _⟩
      exact Finset.notMem_empty b hb
    · obtain ⟨v, hv⟩ : ∃ v, 0 < α v := by
        by_contra h
        push_neg at h
        apply hα
        ext v
        exact Nat.eq_zero_of_le_zero (h v)
      apply Or.inl
      apply closedGraphHomology_subsingleton_of_boundaries
      intro z hz
      apply quotient_cycle_boundary_free_variable (e := v) _ hv z hz
      intro b hb
      rw [hw] at hb
      exact (Finset.notMem_empty b hb).elim

theorem closedGraph_chain_coefficient_homology_free (hG : IntervalLabeling G)
    (w : FiniteMultichain (GraphRows N) (graphEdgeLattice G) m)
    (α : Exponent (FiniteVariable.{u} (GraphRows N))) :
    Module.Free k (ClosedGraphFaceHomology (k := k)
      (finiteChainCoefficientFamily (GraphRows N) w) α) :=
  (closedGraph_chain_coefficient_homology_small (k := k) hG w α).free

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.UnitIntervalCoefficient -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {k : Type u} [CommRing k]

lemma variableMonomialFamily_squarefree {V : Type u} [Fintype V] [LinearOrder V]
    (L : Finset V) : ∀ b ∈ variableMonomialFamily L, ∀ v, b v ≤ 1 := by
  intro b hb v
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hb
  simp only [Finsupp.single_apply]
  split_ifs <;> omega

variable {d N m : ℕ} {E : Finset ((Fin (d+1) → Fin N))}

lemma unitIntervalPredecessor_contains_iff (hE : UnitIntervalFacetFamily E)
    {a : (Fin (d+1) → Fin N)} (ha : a ∈ E)
    (α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))) :
    Contains (finitePredecessorFamily (UnitIntervalRows d N) E a) α ↔
      Contains (facetColonFamily E a) α := by
  rw [← finiteCoordinatePredecessor_contains_iff hE.latticeClosed ha]
  exact facetCoordinateColon_contains_iff hE ha α

def unitIntervalChainLinearVariables (w : FiniteMultichain (UnitIntervalRows d N) E m) :
    Finset (FiniteVariable.{u} (UnitIntervalRows d N)) :=
  Finset.univ.biUnion (fun s => facetLinearVariables E (w.val s).val)

/-- Equation (6.1), as exact equality of monomial membership, in arbitrary
row count. The largest residual facet ideal contains all earlier residuals. -/
theorem unitIntervalChainCoefficient_contains_iff (hE : UnitIntervalFacetFamily E)
    (w : FiniteMultichain (UnitIntervalRows d N) E (m+1))
    (α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))) :
    Contains (finiteChainCoefficientFamily (UnitIntervalRows d N) w) α ↔
      Contains (variableMonomialFamily (unitIntervalChainLinearVariables w) ∪
        finiteRowFamily (UnitIntervalRows d N) (facetResidualFacets E (w.val (Fin.last m)).val)) α := by
  rw [closedGraph_contains_union]
  constructor
  · rintro ⟨b, hb, hbα⟩
    obtain ⟨s, hs, hbs⟩ := Finset.mem_biUnion.mp hb
    have hcol := (unitIntervalPredecessor_contains_iff hE (w.val s).property α).mp ⟨b, hbs, hbα⟩
    rw [facetColonFamily, closedGraph_contains_union] at hcol
    rcases hcol with ⟨b, hb, hbα⟩ | ⟨b, hb, hbα⟩
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
      apply Or.inl
      apply (contains_variableMonomialFamily (unitIntervalChainLinearVariables w) α).mpr
      exact ⟨v, Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, hv⟩,
        by simpa only [Finsupp.single_eq_same, Nat.succ_le_iff] using hbα v⟩
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      exact Or.inr ⟨_, Finset.mem_image.mpr
        ⟨a, facetResidualFacets_mono (w.property (Fin.le_last s)) ha, rfl⟩, hbα⟩
  · intro h
    have hstep : ∀ s : Fin (m+1), Contains (facetColonFamily E (w.val s).val) α →
        Contains (finiteChainCoefficientFamily (UnitIntervalRows d N) w) α := by
      intro s hs
      obtain ⟨b, hb, hbα⟩ := (unitIntervalPredecessor_contains_iff hE (w.val s).property α).mpr hs
      exact ⟨b, Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, hb⟩, hbα⟩
    rcases h with hlin | ⟨b, hb, hbα⟩
    · obtain ⟨v, hv, hαv⟩ :=
        (contains_variableMonomialFamily (unitIntervalChainLinearVariables w) α).mp hlin
      obtain ⟨s, hs, hvs⟩ := Finset.mem_biUnion.mp hv
      exact hstep s ⟨_, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, hvs, rfl⟩),
        Finsupp.single_le_iff.mpr hαv⟩
    · exact hstep (Fin.last m) ⟨b, Finset.mem_union_right _ hb, hbα⟩

def unitIntervalChainResidualRows (w : FiniteMultichain (UnitIntervalRows d N) E (m+1)) :
    ∀ r, Finset (Fin (UnitIntervalRows d N r)) :=
  closedGraphRowsOutside.{u} (unitIntervalChainLinearVariables.{u} w)
    (facetResidualRows E (w.val (Fin.last m)).val)

theorem unitIntervalChainCoefficient_faces (hE : UnitIntervalFacetFamily E)
    (w : FiniteMultichain (UnitIntervalRows d N) E (m+1))
    (α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))) :
    quotientKoszulFaces (finiteChainCoefficientFamily (UnitIntervalRows d N) w) α =
      quotientKoszulFaces (variableMonomialFamily (unitIntervalChainLinearVariables w) ∪
        finiteRowFamily (UnitIntervalRows d N) (finiteRowRestriction E (unitIntervalChainResidualRows.{u} w))) α := by
  apply quotientKoszulFaces_eq_of_contains
  intro β
  rw [unitIntervalChainCoefficient_contains_iff hE w,
    ← facetResidualRows_lattice_eq]
  exact closedGraph_rowFamily_variables_reduce E (unitIntervalChainLinearVariables w)
    (facetResidualRows E (w.val (Fin.last m)).val) β

theorem unitInterval_restricted_residue_cycle_boundary (hE : UnitIntervalFacetFamily E)
    (A : ∀ r, Finset (Fin (UnitIntervalRows d N r)))
    (α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))) (r : ZMod d)
    (z : TotalFaceModule (k := k)
      (quotientKoszulFaces (finiteRowFamily (UnitIntervalRows d N) (finiteRowRestriction E A)) α))
    (hzr : z.val ∈ faceResidueSpace d r)
    (hz : quotientTotalDifferential (finiteRowFamily (UnitIntervalRows d N) (finiteRowRestriction E A)) α z = 0)
    (hr : r ≠ (α.degree : ZMod d)) :
    ∃ y, quotientTotalDifferential (finiteRowFamily (UnitIntervalRows d N) (finiteRowRestriction E A)) α y = z := by
  by_cases hs : SupportedRows A α
  · let B := finiteRowFamily (UnitIntervalRows d N) (finiteRowRestriction E A)
    let C := finiteRowFamily (UnitIntervalRows d N) E
    have hf := quotientFaces_finiteRowRestriction E A α hs
    let z' := quotientFaceCast B C α α hf z
    have hz' : quotientTotalDifferential C α z' = 0 := by
      rw [show z' = quotientFaceCast B C α α hf z from rfl,
        quotientFaceCast_differential, hz, map_zero]
    have hzr' : z'.val ∈ faceResidueSpace d r := by simpa only [z', quotientFaceCast_val] using hzr
    exact (quotientFaceCast_boundary_iff B C α α hf z).mp
      (unitInterval_residue_cycle_boundary hE α r z' hzr' hz' hr)
  · change ¬∀ r j, 0 < α ⟨r, ULift.up j⟩ → j ∈ A r at hs
    push_neg at hs
    obtain ⟨s, j, hj, hjA⟩ := hs
    apply quotient_cycle_boundary_free_variable (e := ⟨s, ULift.up j⟩) _ hj z hz
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    have haA := ((mem_finiteRowRestriction _ A a).mp ha).2 s
    have hne : a s ≠ j := fun h => hjA (h ▸ haA)
    simp only [finiteRowExponent_apply, if_neg hne]

lemma squarefree_filter_degree_add {V : Type u} [Fintype V] [LinearOrder V]
    (L : Finset V) (α : Exponent V) (hsq : ∀ v, α v ≤ 1) :
    α.degree = (α.filter (fun v => v ∉ L)).degree + (α.filter (fun v => v ∈ L)).support.card := by
  have hLsq : ∀ v, (α.filter (fun v => v ∈ L)) v ≤ 1 := by
    intro v
    by_cases hv : v ∈ L <;> simp [Finsupp.filter_apply, hv, hsq v]
  have hL := congrArg Finsupp.degree
    (squarefreeExponent_eq_faceExponent_support (α.filter (fun v => v ∈ L)) hLsq)
  rw [degree_faceExponent] at hL
  have hsum := congrArg Finsupp.degree (Finsupp.filter_add_filter_not α (fun v => v ∈ L))
  simp only [map_add] at hsum
  omega

theorem unitInterval_linear_restriction_residue_boundary (hE : UnitIntervalFacetFamily E)
    (L : Finset (FiniteVariable.{u} (UnitIntervalRows d N)))
    (A : ∀ r, Finset (Fin (UnitIntervalRows d N r)))
    (hA : ∀ r j, j ∈ A r → (⟨r, ULift.up j⟩ : FiniteVariable.{u} (UnitIntervalRows d N)) ∉ L)
    (α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))) (r : ZMod d)
    (z : TotalFaceModule (k := k) (quotientKoszulFaces
      (variableMonomialFamily L ∪ finiteRowFamily (UnitIntervalRows d N) (finiteRowRestriction E A)) α))
    (hzr : z.val ∈ faceResidueSpace d r)
    (hz : quotientTotalDifferential
      (variableMonomialFamily L ∪ finiteRowFamily (UnitIntervalRows d N) (finiteRowRestriction E A)) α z = 0)
    (hr : r ≠ (α.degree : ZMod d)) :
    ∃ y, quotientTotalDifferential
      (variableMonomialFamily L ∪ finiteRowFamily (UnitIntervalRows d N) (finiteRowRestriction E A)) α y = z := by
  let B := finiteRowFamily (UnitIntervalRows d N) (finiteRowRestriction E A)
  by_cases hsq : ∀ v, α v ≤ 1
  · have hB : ∀ b ∈ B, ∀ v, b v ≠ 0 → v ∉ L := by
      intro b hb v hv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      rcases v with ⟨s, ⟨j⟩⟩
      have haA := ((mem_finiteRowRestriction _ A a).mp ha).2 s
      by_cases he : a s = j
      · exact hA s j (he ▸ haA)
      · simp [finiteRowExponent_apply, he] at hv
    let C := variableMonomialFamily L ∪ B
    change ∃ y, quotientTotalDifferential C α y = z
    letI : DecidableEq (FiniteVariable.{u} (UnitIntervalRows d N)) :=
      LinearOrder.toDecidableEq
    let C' := variableMonomialFamily L ∪ B
    have hC : C = C' := by
      ext b
      simp only [C, C', Finset.mem_union]
    have hf := congrArg (fun D => quotientKoszulFaces D α) hC
    let z' := quotientFaceCast C C' α α hf z
    have hz' : quotientTotalDifferential C' α z' = 0 := by
      rw [show z' = quotientFaceCast C C' α α hf z from rfl,
        quotientFaceCast_differential, hz, map_zero]
    have hzr' : z'.val ∈ faceResidueSpace d r := by
      simpa only [z', quotientFaceCast_val] using hzr
    apply (quotientFaceCast_boundary_iff C C' α α hf z).mp
    let f := linearVariableQuotientFactor (k := k) L B hB α hsq
    let y := f.symm z'
    have hy := linearVariableQuotientFactor_symm_cycle L B hB α hsq z' hz'
    have hyr := linearVariableQuotientFactor_symm_residue L B hB α hsq d r z' hzr'
    have hne : r - (α.filter (fun v => v ∈ L)).support.card ≠
        ((α.filter (fun v => v ∉ L)).degree : ZMod d) := by
      intro hh
      apply hr
      have hdeg := congrArg (fun q : ℕ => (q : ZMod d)) (squarefree_filter_degree_add L α hsq)
      simp only [Nat.cast_add] at hdeg
      rw [hdeg]
      exact (sub_eq_iff_eq_add).mp hh
    exact linearVariableQuotientFactor_boundary_of_symm L B hB α hsq z'
      (unitInterval_restricted_residue_cycle_boundary hE A _ _ y hyr hy hne)
  · push_neg at hsq
    obtain ⟨v, hv⟩ := hsq
    apply quotient_cycle_boundary_of_two_le (e := v) _ (by omega) z hz
    intro b hb
    rcases Finset.mem_union.mp hb with hb | hb
    · exact variableMonomialFamily_squarefree L b hb v
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      rcases v with ⟨s, ⟨j⟩⟩
      simp only [finiteRowExponent_apply]
      split_ifs <;> omega

/-- Every coefficient quotient in the all-powers decomposition has precisely
the same allowed degree residues as the original unit-interval quotient. -/
theorem unitInterval_chain_coefficient_residue_boundary (hE : UnitIntervalFacetFamily E)
    (w : FiniteMultichain (UnitIntervalRows d N) E (m+1))
    (α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))) (r : ZMod d)
    (z : TotalFaceModule (k := k) (quotientKoszulFaces (finiteChainCoefficientFamily (UnitIntervalRows d N) w) α))
    (hzr : z.val ∈ faceResidueSpace d r)
    (hz : quotientTotalDifferential (finiteChainCoefficientFamily (UnitIntervalRows d N) w) α z = 0)
    (hr : r ≠ (α.degree : ZMod d)) :
    ∃ y, quotientTotalDifferential (finiteChainCoefficientFamily (UnitIntervalRows d N) w) α y = z := by
  let B := finiteChainCoefficientFamily (UnitIntervalRows d N) w
  let C := variableMonomialFamily (unitIntervalChainLinearVariables w) ∪
    finiteRowFamily (UnitIntervalRows d N) (finiteRowRestriction E (unitIntervalChainResidualRows.{u} w))
  have hf := unitIntervalChainCoefficient_faces hE w α
  let z' := quotientFaceCast B C α α hf z
  have hz' : quotientTotalDifferential C α z' = 0 := by
    rw [show z' = quotientFaceCast B C α α hf z from rfl,
      quotientFaceCast_differential, hz, map_zero]
  have hzr' : z'.val ∈ faceResidueSpace d r := by simpa only [z', quotientFaceCast_val] using hzr
  exact (quotientFaceCast_boundary_iff B C α α hf z).mp
    (unitInterval_linear_restriction_residue_boundary hE (unitIntervalChainLinearVariables w)
      (unitIntervalChainResidualRows.{u} w) (closedGraphRowsOutside_avoids _ _) α r z' hzr' hz' hr)

end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.unitInterval_chain_coefficient_residue_boundary

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphDegreeHomology -/
section

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.FilteredHomology
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

section Integral
variable {W : Type} [Fintype W] [LinearOrder W]

theorem closedGraph_degree_homology_free {N : ℕ} {G : SimpleGraph (Fin N)}
    (hG : IntervalLabeling G) (α : Exponent (FiniteVariable (GraphRows N))) (p : ℕ) :
    Module.Free ℤ (ClosedGraphDegreeHomology (k := ℤ)
      (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) α p) :=
  closedGraphDegreeHomology_free_of_total _ α p (closedGraph_fine_homology_free (k := ℤ) hG α)

theorem closedGraph_chain_coefficient_degree_homology_free {N m : ℕ} {G : SimpleGraph (Fin N)}
    (hG : IntervalLabeling G) (w : FiniteMultichain (GraphRows N) (graphEdgeLattice G) m)
    (α : Exponent (FiniteVariable (GraphRows N))) (p : ℕ) :
    Module.Free ℤ (ClosedGraphDegreeHomology (k := ℤ)
      (finiteChainCoefficientFamily (GraphRows N) w) α p) :=
  closedGraphDegreeHomology_free_of_total _ α p
    (closedGraph_chain_coefficient_homology_free (k := ℤ) hG w α)

end Integral
end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphDegreeRetract -/
section

/-! # The genuine degree homology is a retract of total fine homology

Projection to exterior degree `p` preserves cycles and carries boundaries to
boundaries with an explicit degree-`p+1` filling. It therefore descends to the
actual quotient homology and retracts its inclusion in total homology.
Over a domain, a retract of a module which is zero or one copy of the ring
is itself zero or one copy of the ring. This works directly over `ℤ[z]`.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.FilteredHomology
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

def closedGraphCycleDegreeProjection (B : Family V) (α : Exponent V) (p : ℕ) :
    LinearMap.ker (quotientTotalDifferential (k := k) B α) →ₗ[k]
      ClosedGraphDegreeCycles (k := k) B α p :=
  ((Grading.projection (totalFaceBasis (quotientKoszulFaces B α))
    (fun F => F.val.card) p).comp (LinearMap.ker (quotientTotalDifferential B α)).subtype).codRestrict
    _ (by
      intro z
      have hp : Grading.projection (totalFaceBasis (quotientKoszulFaces B α))
          (fun F => F.val.card) p z.val ∈ totalFacePiece (quotientKoszulFaces B α) p := by
        rw [totalFacePiece_eq_basis_span]
        exact Grading.projection_mem _ _ _ _
      refine ⟨?_, hp⟩
      change quotientTotalDifferential B α
        (Grading.projection (totalFaceBasis (quotientKoszulFaces B α))
          (fun F => F.val.card) p z.val) = 0
      have hz : quotientTotalDifferential B α z.val = 0 := z.property
      cases p with
      | zero => exact quotientTotalDifferential_zero_degree B α _ hp
      | succ p =>
          have hh := LinearMap.congr_fun (quotientTotalDifferential_degree_projection B α p) z.val
          change quotientTotalDifferential B α
              (Grading.projection (totalFaceBasis (quotientKoszulFaces B α))
                (fun F => F.val.card) (p+1) z.val) = _ at hh
          simpa only [LinearMap.comp_apply, hz, map_zero] using hh)

@[simp] lemma closedGraphCycleDegreeProjection_val (B : Family V) (α : Exponent V) (p : ℕ)
    (z : LinearMap.ker (quotientTotalDifferential (k := k) B α)) :
    (closedGraphCycleDegreeProjection B α p z).val =
      Grading.projection (totalFaceBasis (quotientKoszulFaces B α))
        (fun F => F.val.card) p z.val := rfl

set_option maxHeartbeats 100000 in
theorem closedGraphCycleDegreeProjection_boundary_mem_range
    (B : Family V) (α : Exponent V) (p : ℕ)
    (y : TotalFaceModule (k := k) (quotientKoszulFaces B α)) :
    closedGraphCycleDegreeProjection (k := k) B α p
      (boundaryMap (quotientTotalDifferential (k := k) B α)
        (quotientTotalDifferential B α) (quotientTotalDifferential_comp B α) y) ∈
      LinearMap.range (closedGraphDegreeBoundary (k := k) B α p) := by
  let z := Grading.projection (totalFaceBasis (k := k) (quotientKoszulFaces B α))
    (fun F => F.val.card) (p + 1) y
  have hz : z ∈ totalFacePiece (k := k) (quotientKoszulFaces B α) (p + 1) := by
    rw [totalFacePiece_eq_basis_span]
    exact Grading.projection_mem _ _ _ _
  refine ⟨⟨z, hz⟩, ?_⟩
  apply Subtype.ext
  change quotientTotalDifferential (k := k) B α z =
    Grading.projection (totalFaceBasis (k := k) (quotientKoszulFaces B α))
      (fun F => F.val.card) p (quotientTotalDifferential B α y)
  exact LinearMap.congr_fun (quotientTotalDifferential_degree_projection (k := k) B α p) y

section
attribute [local irreducible] ClosedGraphDegreeHomology ClosedGraphFaceHomology

set_option maxHeartbeats 100000 in
set_option backward.isDefEq.respectTransparency true in
def closedGraphDegreeHomologyProjection (B : Family V) (α : Exponent V) (p : ℕ) :
    @LinearMap k k inferInstance inferInstance (RingHom.id k)
      (ClosedGraphFaceHomology (k := k) B α) (ClosedGraphDegreeHomology (k := k) B α p)
      (closedGraphFaceHomologyAddCommGroup (k := k) B α).toAddCommMonoid
      (closedGraphDegreeHomologyAddCommGroup (k := k) B α p).toAddCommMonoid
      (closedGraphFaceHomologyModule (k := k) B α)
      (closedGraphDegreeHomologyModule (k := k) B α p) := by
  unfold ClosedGraphFaceHomology ClosedGraphDegreeHomology
  exact submoduleHomologyProjection (K := k) (M := Simplicial.Ambient V k)
    (TotalFaceModule (k := k) (quotientKoszulFaces B α))
    (quotientTotalDifferential (k := k) B α) (quotientTotalDifferential_comp B α)
    (totalFacePiece (k := k) (quotientKoszulFaces B α) (p + 1))
    (ClosedGraphDegreeCycles (k := k) B α p)
    (closedGraphDegreeBoundary (k := k) B α p)
    (closedGraphCycleDegreeProjection (k := k) B α p)
    (closedGraphCycleDegreeProjection_boundary_mem_range (k := k) B α p)

end

/-- This is an actual retraction on the homology quotients. In particular,
it is stronger than an injection of the underlying modules. -/
theorem closedGraphDegreeHomologyProjection_inclusion (B : Family V) (α : Exponent V) (p : ℕ) :
    (closedGraphDegreeHomologyProjection (k := k) B α p).comp
      (closedGraphDegreeHomologyInclusion B α p) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := (LinearMap.range (closedGraphDegreeBoundary B α p)).mkQ_surjective x
  change Submodule.Quotient.mk
      (closedGraphCycleDegreeProjection B α p ⟨z.val, z.property.1⟩) =
    (Submodule.Quotient.mk z : ClosedGraphDegreeHomology (k := k) B α p)
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  rw [closedGraphCycleDegreeProjection_val]
  apply Grading.projection_eq_self
  unfold Grading.Piece
  rw [← totalFacePiece_eq_basis_span]
  exact z.property.2

section Domain
variable [IsDomain k]

theorem closedGraphDegreeHomology_small_of_total (B : Family V) (α : Exponent V) (p : ℕ)
    (hsmall : ClosedGraphSmallFreeModel k (ClosedGraphFaceHomology (k := k) B α)) :
    ClosedGraphSmallFreeModel k (ClosedGraphDegreeHomology (k := k) B α p) := by
  cases hsmall with
  | inl hzero =>
    exact Or.inl ⟨fun x y => closedGraphDegreeHomologyInclusion_injective B α p
      (hzero.allEq _ _)⟩
  | inr he =>
    let e := Classical.choice he
    let i := e.toLinearMap.comp (closedGraphDegreeHomologyInclusion B α p)
    let r := (closedGraphDegreeHomologyProjection B α p).comp e.symm.toLinearMap
    apply FourPapers.split_rank_one_zero_or_equiv i r
    apply LinearMap.ext
    intro x
    change closedGraphDegreeHomologyProjection B α p
      (e.symm (e (closedGraphDegreeHomologyInclusion B α p x))) = x
    rw [LinearEquiv.symm_apply_apply]
    exact LinearMap.congr_fun (closedGraphDegreeHomologyProjection_inclusion B α p) x

theorem closedGraph_degree_homology_small_domain {N : ℕ} {G : SimpleGraph (Fin N)}
    (hG : IntervalLabeling G)
    (α : Exponent (FiniteVariable.{u} (GraphRows N))) (p : ℕ) :
    ClosedGraphSmallFreeModel k (ClosedGraphDegreeHomology (k := k)
      (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) α p) :=
  closedGraphDegreeHomology_small_of_total _ α p (closedGraph_fine_homology_small hG α)

theorem closedGraph_chain_coefficient_degree_homology_small_domain
    {N m : ℕ} {G : SimpleGraph (Fin N)} (hG : IntervalLabeling G)
    (w : FiniteMultichain (GraphRows N) (graphEdgeLattice G) m)
    (α : Exponent (FiniteVariable.{u} (GraphRows N))) (p : ℕ) :
    ClosedGraphSmallFreeModel k (ClosedGraphDegreeHomology (k := k)
      (finiteChainCoefficientFamily (GraphRows N) w) α p) :=
  closedGraphDegreeHomology_small_of_total _ α p
    (closedGraph_chain_coefficient_homology_small hG w α)

theorem closedGraph_degree_homology_free_domain {N : ℕ} {G : SimpleGraph (Fin N)}
    (hG : IntervalLabeling G)
    (α : Exponent (FiniteVariable.{u} (GraphRows N))) (p : ℕ) :
    Module.Free k (ClosedGraphDegreeHomology (k := k)
      (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) α p) :=
  (closedGraph_degree_homology_small_domain (k := k) hG α p).free

theorem closedGraph_chain_coefficient_degree_homology_free_domain
    {N m : ℕ} {G : SimpleGraph (Fin N)} (hG : IntervalLabeling G)
    (w : FiniteMultichain (GraphRows N) (graphEdgeLattice G) m)
    (α : Exponent (FiniteVariable.{u} (GraphRows N))) (p : ℕ) :
    Module.Free k (ClosedGraphDegreeHomology (k := k)
      (finiteChainCoefficientFamily (GraphRows N) w) α p) :=
  (closedGraph_chain_coefficient_degree_homology_small_domain (k := k) hG w α p).free

theorem closedGraphDegreeHomology_finite_of_small (B : Family V) (α : Exponent V) (p : ℕ)
    (hsmall : ClosedGraphSmallFreeModel k (ClosedGraphDegreeHomology (k := k) B α p)) :
    Module.Finite k (ClosedGraphDegreeHomology (k := k) B α p) := by
  cases hsmall with
  | inl hzero =>
    letI := hzero
    exact Module.Finite.of_surjective (0 : k →ₗ[k] ClosedGraphDegreeHomology (k := k) B α p)
      (fun x => ⟨0, Subsingleton.elim _ _⟩)
  | inr he => exact Module.Finite.equiv (Classical.choice he).symm

theorem closedGraph_chain_coefficient_degree_homology_finite_domain
    {N m : ℕ} {G : SimpleGraph (Fin N)} (hG : IntervalLabeling G)
    (w : FiniteMultichain (GraphRows N) (graphEdgeLattice G) m)
    (α : Exponent (FiniteVariable.{u} (GraphRows N))) (p : ℕ) :
    Module.Finite k (ClosedGraphDegreeHomology (k := k)
      (finiteChainCoefficientFamily (GraphRows N) w) α p) :=
  closedGraphDegreeHomology_finite_of_small _ α p
    (closedGraph_chain_coefficient_degree_homology_small_domain (k := k) hG w α p)

end Domain
end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphIntegralTensor -/
section

/-! # Integral tensor cycle spanning for the graph coefficient quotients

The one-factor homotopy comes from projectivity of the actual degree-wise
homology quotients. It raises exterior degree by one, and is consequently
odd for the exterior involution over every coefficient ring. The resulting
tensor argument uses no field complement and never divides by two.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open scoped TensorProduct
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

theorem quotientTotalPiece_projective (B : Family V) (α : Exponent V) (p : ℕ) :
    Module.Projective k ((quotientTotalData (k := k) B α).piece p) := by
  change Module.Projective k (totalFacePiece (k := k) (quotientKoszulFaces B α) p)
  letI : Module.Free k (totalFacePiece (k := k) (quotientKoszulFaces B α) p) :=
    Module.Free.of_basis (quotientTotalPieceBasis (k := k) B α p)
  infer_instance

theorem quotientPieceHomology_projective (B : Family V) (α : Exponent V)
    (hfree : ∀ p, Module.Free k (ClosedGraphDegreeHomology (k := k) B α p)) (p : ℕ) :
    Module.Projective k (FourPapers.ProjectiveComplexSplitting.Homology
      (fun p => ↥((quotientTotalData (k := k) B α).piece p))
      (quotientTotalData B α).differential
      (quotientTotalData B α).differential_comp p) := by
  letI := hfree p
  letI := Module.Free.of_equiv (quotientPieceHomologyEquiv (k := k) B α p).symm
  infer_instance

def quotientPieceBoundaryHomotopy (B : Family V) (α : Exponent V)
    (hfree : ∀ p, Module.Free k (ClosedGraphDegreeHomology (k := k) B α p)) (p : ℕ) :
    totalFacePiece (k := k) (quotientKoszulFaces B α) p →ₗ[k]
      totalFacePiece (k := k) (quotientKoszulFaces B α) (p+1) :=
  FourPapers.ProjectiveComplexSplitting.homotopy
    (fun p => ↥((quotientTotalData (k := k) B α).piece p))
    (quotientTotalData B α).differential
    (quotientTotalData B α).differential_comp
    (quotientTotalPiece_projective B α) (quotientPieceHomology_projective B α hfree) p

/-- Extend the actual degree-wise homotopy by linearity on the exterior
basis. Its degree is exactly +1. -/
def quotientTotalBoundaryHomotopy (B : Family V) (α : Exponent V)
    (hfree : ∀ p, Module.Free k (ClosedGraphDegreeHomology (k := k) B α p)) :
    Module.End k (TotalFaceModule (k := k) (quotientKoszulFaces B α)) :=
  (totalFaceBasis (quotientKoszulFaces B α)).constr k (fun F =>
    (quotientPieceBoundaryHomotopy B α hfree F.val.card
      ⟨totalFaceBasis (quotientKoszulFaces B α) F, totalFaceBasis_mem_degree _ F⟩).val)

@[simp] lemma quotientTotalBoundaryHomotopy_basis (B : Family V) (α : Exponent V)
    (hfree : ∀ p, Module.Free k (ClosedGraphDegreeHomology (k := k) B α p))
    (F : {F // quotientKoszulFaces B α F}) :
    quotientTotalBoundaryHomotopy B α hfree (totalFaceBasis (quotientKoszulFaces B α) F) =
      (quotientPieceBoundaryHomotopy B α hfree F.val.card
        ⟨totalFaceBasis (quotientKoszulFaces B α) F, totalFaceBasis_mem_degree _ F⟩).val :=
  Module.Basis.constr_basis _ _ _ _

lemma quotientTotalBoundaryHomotopy_on_piece (B : Family V) (α : Exponent V)
    (hfree : ∀ p, Module.Free k (ClosedGraphDegreeHomology (k := k) B α p))
    (p : ℕ) (x : totalFacePiece (k := k) (quotientKoszulFaces B α) p) :
    quotientTotalBoundaryHomotopy B α hfree x.val =
      (quotientPieceBoundaryHomotopy B α hfree p x).val := by
  have he : (quotientTotalBoundaryHomotopy B α hfree).domRestrict
      (totalFacePiece (quotientKoszulFaces B α) p) =
      (totalFacePiece (quotientKoszulFaces B α) (p+1)).subtype.comp
        (quotientPieceBoundaryHomotopy B α hfree p) := by
    apply (quotientTotalPieceBasis (k := k) B α p).ext
    intro F
    rcases F with ⟨F, hF, hcard⟩
    subst p
    change quotientTotalBoundaryHomotopy B α hfree
        (quotientTotalPieceBasis B α F.card ⟨F, hF, rfl⟩).val =
      (quotientPieceBoundaryHomotopy B α hfree F.card
        (quotientTotalPieceBasis B α F.card ⟨F, hF, rfl⟩)).val
    rw [quotientTotalPieceBasis_val, quotientTotalBoundaryHomotopy_basis]
    apply congrArg (fun x => (quotientPieceBoundaryHomotopy B α hfree F.card x).val)
    apply Subtype.ext
    exact (quotientTotalPieceBasis_val B α F.card ⟨F, hF, rfl⟩).symm
  exact LinearMap.congr_fun he x

lemma quotientTotalBoundaryHomotopy_raises (B : Family V) (α : Exponent V)
    (hfree : ∀ p, Module.Free k (ClosedGraphDegreeHomology (k := k) B α p))
    (p : ℕ) (x : TotalFaceModule (k := k) (quotientKoszulFaces B α))
    (hx : x ∈ totalFacePiece (quotientKoszulFaces B α) p) :
    quotientTotalBoundaryHomotopy B α hfree x ∈
      totalFacePiece (quotientKoszulFaces B α) (p+1) := by
  rw [quotientTotalBoundaryHomotopy_on_piece B α hfree p ⟨x, hx⟩]
  exact (quotientPieceBoundaryHomotopy B α hfree p ⟨x, hx⟩).property

lemma quotientTotalBoundaryHomotopy_generalized_inverse (B : Family V) (α : Exponent V)
    (hfree : ∀ p, Module.Free k (ClosedGraphDegreeHomology (k := k) B α p)) :
    quotientTotalDifferential B α * quotientTotalBoundaryHomotopy B α hfree *
      quotientTotalDifferential B α = quotientTotalDifferential B α := by
  let C := quotientTotalData (k := k) B α
  let hC := quotientTotalPiece_projective (k := k) B α
  let hH := quotientPieceHomology_projective (k := k) B α hfree
  apply (totalFaceBasis (k := k) (quotientKoszulFaces B α)).ext
  intro F
  change quotientTotalDifferential B α
      (quotientTotalBoundaryHomotopy B α hfree
        (quotientTotalDifferential B α (totalFaceBasis _ F))) =
    quotientTotalDifferential B α (totalFaceBasis _ F)
  cases hn : F.val.card with
  | zero =>
      have hz := quotientTotalDifferential_zero_degree (k := k) B α (totalFaceBasis _ F)
        (hn ▸ totalFaceBasis_mem_degree _ F)
      rw [hz, map_zero, map_zero]
  | succ p =>
      let x : C.piece (p+1) := ⟨totalFaceBasis _ F, hn ▸ totalFaceBasis_mem_degree _ F⟩
      change quotientTotalDifferential B α
          (quotientTotalBoundaryHomotopy B α hfree (C.differential p x).val) =
        (C.differential p x).val
      rw [quotientTotalBoundaryHomotopy_on_piece B α hfree p (C.differential p x)]
      have hh := congrArg (fun y : C.piece (p+1) => y.val)
        (FourPapers.ProjectiveComplexSplitting.homotopy_differential
          (fun p => ↥(C.piece p)) C.differential C.differential_comp hC hH p x)
      change (quotientPieceBoundaryHomotopy B α hfree p (C.differential p x)).val =
        x.val - (FourPapers.ProjectiveComplexSplitting.cycleProjection
          (fun p => ↥(C.piece p)) C.differential C.differential_comp hC hH (p+1) x).val.val at hh
      rw [hh, map_sub]
      have hz : quotientTotalDifferential B α
          (FourPapers.ProjectiveComplexSplitting.cycleProjection
            (fun p => ↥(C.piece p)) C.differential C.differential_comp hC hH (p+1) x).val.val = 0 :=
        congrArg Subtype.val (FourPapers.ProjectiveComplexSplitting.cycleProjection
          (fun p => ↥(C.piece p)) C.differential C.differential_comp hC hH (p+1) x).property
      rw [hz, sub_zero]
      rfl

lemma totalFaceInvolute_on_piece (P : Finset V → Prop) (p : ℕ)
    (x : TotalFaceModule (k := k) P) (hx : x ∈ totalFacePiece P p) :
    totalFaceInvolute P x = (-1 : k)^p • x := by
  apply Subtype.ext
  change CliffordAlgebra.involute x.val = (-1 : k)^p • x.val
  change x.val ∈ Simplicial.Chains (k := k) P p at hx
  generalize x.val = z at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨F, ⟨_, hcard⟩, rfl⟩ := hy
      simpa only [Simplicial.basis, hcard] using
        TauCeti.ExteriorAlgebra.involute_basis (Pi.basisFun k V) F
  | zero => simp
  | add x y hx hy ihx ihy => rw [map_add, ihx, ihy, smul_add]
  | smul r x hx ih => rw [map_smul, ih, smul_comm]

lemma quotientTotalBoundaryHomotopy_odd (B : Family V) (α : Exponent V)
    (hfree : ∀ p, Module.Free k (ClosedGraphDegreeHomology (k := k) B α p)) :
    totalFaceInvolute (quotientKoszulFaces B α) * quotientTotalBoundaryHomotopy B α hfree +
      quotientTotalBoundaryHomotopy B α hfree * totalFaceInvolute (quotientKoszulFaces B α) = 0 := by
  apply (totalFaceBasis (k := k) (quotientKoszulFaces B α)).ext
  intro F
  change totalFaceInvolute (quotientKoszulFaces B α)
      (quotientTotalBoundaryHomotopy B α hfree (totalFaceBasis _ F)) +
    quotientTotalBoundaryHomotopy B α hfree (totalFaceInvolute _ (totalFaceBasis _ F)) = 0
  rw [totalFaceInvolute_on_piece _ (F.val.card+1) _
      (quotientTotalBoundaryHomotopy_raises B α hfree F.val.card _ (totalFaceBasis_mem_degree _ F)),
    totalFaceInvolute_on_piece _ F.val.card _ (totalFaceBasis_mem_degree _ F), map_smul]
  rw [pow_succ, mul_smul, neg_one_smul, smul_neg, neg_add_cancel]

/-- Integral tensor cycle generation for actual quotient strands with free
degree-wise homology. Those hypotheses will be discharged below for every
graph predecessor factor. -/
theorem quotientFaceTensorCycles_of_free_homology {m : ℕ}
    (B : Fin m → Family V) (α : Fin m → Exponent V)
    (hfree : ∀ j p, Module.Free k (ClosedGraphDegreeHomology (k := k) (B j) (α j) p)) :
    LinearMap.ker (finiteFaceTensorDifferential (k := k)
      (fun j => quotientKoszulFaces (B j) (α j))) =
      Submodule.span k {z | ∃ x : ∀ j, TotalFaceModule (k := k)
          (quotientKoszulFaces (B j) (α j)),
        (∀ j, projectedTotalDifferential (quotientKoszulFaces (B j) (α j)) (x j) = 0) ∧
          PiTensorProduct.tprod k x = z} ⊔
      LinearMap.range (finiteFaceTensorDifferential
        (fun j => quotientKoszulFaces (B j) (α j))) := by
  apply FourPapers.TensorCycleSpanning.ker_differential_eq_span_cycles_sup_range_of_homotopies
    (fun j => projectedTotalDifferential (quotientKoszulFaces (B j) (α j)))
    (fun j => totalFaceInvolute (quotientKoszulFaces (B j) (α j)))
    (fun j => quotientTotalBoundaryHomotopy (B j) (α j) (hfree j))
  · intro j
    rw [← quotientTotalDifferential_eq_projected]
    exact quotientTotalDifferential_comp (B j) (α j)
  · intro j
    exact totalFaceInvolute_square _
  · intro j
    exact projectedTotalDifferential_anticommute _
  · intro j
    rw [← quotientTotalDifferential_eq_projected]
    exact quotientTotalBoundaryHomotopy_generalized_inverse (B j) (α j) (hfree j)
  · intro j
    exact quotientTotalBoundaryHomotopy_odd (B j) (α j) (hfree j)

section Graph
variable [IsDomain k] {N : ℕ} {G : SimpleGraph (Fin N)}

def graphSingletonMultichain (a : graphEdgeLattice G) :
    FiniteMultichain (GraphRows N) (graphEdgeLattice G) 1 :=
  ⟨fun _ => a, fun _ _ _ => le_rfl⟩

lemma graphSingletonMultichain_coefficient (a : graphEdgeLattice G) :
    finiteChainCoefficientFamily.{u} (GraphRows N) (graphSingletonMultichain a) =
      finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) a.val := by
  simp [finiteChainCoefficientFamily, graphSingletonMultichain]

theorem closedGraph_predecessor_degree_homology_free (hG : IntervalLabeling G)
    (a : graphEdgeLattice G) (α : Exponent (FiniteVariable.{u} (GraphRows N))) (p : ℕ) :
    Module.Free k (ClosedGraphDegreeHomology (k := k)
      (finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) a.val) α p) := by
  rw [← graphSingletonMultichain_coefficient.{u} a]
  exact closedGraph_chain_coefficient_degree_homology_free_domain (k := k) hG
    (graphSingletonMultichain a) α p

theorem closedGraph_predecessor_tensor_cycles (hG : IntervalLabeling G) {m : ℕ}
    (a : Fin m → graphEdgeLattice G)
    (α : Fin m → Exponent (FiniteVariable.{u} (GraphRows N))) :
    LinearMap.ker (finiteFaceTensorDifferential (k := k)
      (fun j => quotientKoszulFaces
        (finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) (a j).val) (α j))) =
      Submodule.span k {z | ∃ x : ∀ j, TotalFaceModule (k := k)
          (quotientKoszulFaces
            (finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) (a j).val) (α j)),
        (∀ j, projectedTotalDifferential (quotientKoszulFaces
          (finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) (a j).val) (α j)) (x j) = 0) ∧
          PiTensorProduct.tprod k x = z} ⊔
      LinearMap.range (finiteFaceTensorDifferential
        (fun j => quotientKoszulFaces
          (finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) (a j).val) (α j))) :=
  quotientFaceTensorCycles_of_free_homology _ _
    (fun j p => closedGraph_predecessor_degree_homology_free hG (a j) (α j) p)

end Graph
end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphChainHomology -/
section

/-! # Integral homology of every monomial graph power

The categorical homology is identified with the literal cycle/boundary
quotient in every homological degree, including degree zero. Applying the
actual all-power chain isomorphism then transfers the proved rank-zero-or-one
description of the coefficient quotients to finite free homology of each
fine strand of the monomial power.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u v

variable {k V : Type u} [CommRing k] [Fintype V] [LinearOrder V]

section Domain
variable [IsDomain k] {N : ℕ} {G : SimpleGraph (Fin N)}

theorem closedGraph_chain_coefficient_categorical_homology_free
    (hG : IntervalLabeling G) {m : ℕ}
    (w : FiniteMultichain (GraphRows N) (graphEdgeLattice G) m)
    (α : Exponent (FiniteVariable.{u} (GraphRows N))) (p : ℕ) :
    Module.Free k ((quotientHomogeneousComplex (k := k)
      (finiteChainCoefficientFamily (GraphRows N) w) α).homology p) := by
  letI := closedGraph_chain_coefficient_degree_homology_free_domain (k := k) hG w α p
  exact Module.Free.of_equiv (quotientCategoricalDegreeHomologyEquiv _ α p).symm

theorem closedGraph_chain_coefficient_categorical_homology_finite
    (hG : IntervalLabeling G) {m : ℕ}
    (w : FiniteMultichain (GraphRows N) (graphEdgeLattice G) m)
    (α : Exponent (FiniteVariable.{u} (GraphRows N))) (p : ℕ) :
    Module.Finite k ((quotientHomogeneousComplex (k := k)
      (finiteChainCoefficientFamily (GraphRows N) w) α).homology p) := by
  letI := closedGraph_chain_coefficient_degree_homology_finite_domain (k := k) hG w α p
  exact Module.Finite.equiv (quotientCategoricalDegreeHomologyEquiv _ α p).symm

/-- Every actual fine Koszul homology group of every positive monomial
graph power is free over the coefficient domain, in all homological degrees. -/
theorem closedGraph_monomial_power_homology_free (hG : IntervalLabeling G)
    (m : ℕ) (hm : 0 < m) (α : Exponent (FiniteVariable.{u} (GraphRows N))) (p : ℕ) :
    Module.Free k ((homogeneousComplex (k := k)
      (exponentPowerFamily (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) m)
        α).homology p) := by
  letI : ∀ w : AdmissibleChain (GraphRows N) (graphEdgeLattice G) m α,
      Module.Free k ((quotientHomogeneousComplex (k := k)
        (finiteChainCoefficientFamily (GraphRows N) w.val)
          (α-finiteChainShift (GraphRows N) w.val)).homology p) :=
    fun w => closedGraph_chain_coefficient_categorical_homology_free
      hG w.val _ p
  exact Module.Free.of_equiv
    (allPowerHomogeneousHomologyIso (k := k) (graphEdgeLattice_closed hG) m hm α p).toLinearEquiv.symm

theorem closedGraph_monomial_power_homology_finite (hG : IntervalLabeling G)
    (m : ℕ) (hm : 0 < m) (α : Exponent (FiniteVariable.{u} (GraphRows N))) (p : ℕ) :
    Module.Finite k ((homogeneousComplex (k := k)
      (exponentPowerFamily (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) m)
        α).homology p) := by
  letI : ∀ w : AdmissibleChain (GraphRows N) (graphEdgeLattice G) m α,
      Module.Finite k ((quotientHomogeneousComplex (k := k)
        (finiteChainCoefficientFamily (GraphRows N) w.val)
          (α-finiteChainShift (GraphRows N) w.val)).homology p) :=
    fun w => closedGraph_chain_coefficient_categorical_homology_finite
      hG w.val _ p
  exact Module.Finite.equiv
    (allPowerHomogeneousHomologyIso (k := k) (graphEdgeLattice_closed hG) m hm α p).toLinearEquiv.symm

end Domain
end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.QuotientFaceBaseChange -/
section

/-!
# Arbitrary coefficient change for the literal quotient face complexes

The standard exterior-face bases have identical indices over both rings.
Their differential coefficients are the same integer signs. This gives an
actual chain equivalence from the tensor extension of the original complex
to the new polynomial-quotient Koszul strand. When the original homology is
free, the explicit split-complex argument proves invariance of every rank.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open scoped TensorProduct
universe u
variable {V R S : Type u} [Fintype V] [LinearOrder V]
  [CommRing R] [CommRing S] [Algebra R S]

attribute [local irreducible] quotientFaceDifferential

lemma quotientTotalPieceEquiv_differential (B : Family V) (α : Exponent V) (p : ℕ)
    (x : (quotientTotalData (k := R) B α).piece (p+1)) :
    totalFacePieceEquiv (quotientKoszulFaces B α) p
        ((quotientTotalData B α).differential p x) =
      quotientFaceDifferential B α p
        (totalFacePieceEquiv (quotientKoszulFaces B α) (p+1) x) := by
  apply Subtype.ext
  change quotientFaceProjection (k := R) B α (Simplicial.boundary x.val.val) =
    (quotientFaceDifferential (k := R) B α p ⟨x.val.val, x.property⟩).val
  exact (quotientFaceDifferential_val (k := R) B α p ⟨x.val.val, x.property⟩).symm

lemma quotientTotalPieceBasis_differential (B : Family V) (α : Exponent V) (p : ℕ)
    (F : QuotientFaceIndex B α (p+1)) :
    (quotientTotalData (k := R) B α).differential p (quotientTotalPieceBasis B α (p+1) F) =
      ∑ j : {j // j ∈ F.val},
        if h : QuotientAllowed B (α - faceExponent F.val + Finsupp.single j.val 1) then
          TauCeti.ExteriorAlgebra.basisEraseSign j.val F.val •
            quotientTotalPieceBasis B α p (eraseQuotientFace F j h)
        else 0 := by
  apply (totalFacePieceEquiv (quotientKoszulFaces B α) p).injective
  rw [quotientTotalPieceEquiv_differential, map_sum]
  simp only [quotientTotalPieceBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply,
    quotientFaceDifferential_basis]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hj
  · let e := totalFacePieceEquiv (k := R) (quotientKoszulFaces B α) p
    let x := e.symm (quotientFaceBasis (k := R) B α p (eraseQuotientFace F j hj))
    have hz := e.toLinearMap.toAddMonoidHom.map_zsmul
      (TauCeti.ExteriorAlgebra.basisEraseSign j.val F.val : ℤ) x
    simpa only [e, x, Units.smul_def, int_smul_eq_zsmul,
      LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] using hz.symm
  · exact (map_zero _).symm

/-- The new face module is identified with the genuine scalar extension of
the old one, by the actual exterior-face basis. -/
def quotientPieceBaseChangeEquiv (B : Family V) (α : Exponent V) (p : ℕ) :
    S ⊗[R] totalFacePiece (k := R) (quotientKoszulFaces B α) p ≃ₗ[S]
      totalFacePiece (k := S) (quotientKoszulFaces B α) p :=
  ((quotientTotalPieceBasis (k := R) B α p).baseChange S).equiv
    (quotientTotalPieceBasis (k := S) B α p) (Equiv.refl _)

@[simp] lemma quotientPieceBaseChangeEquiv_basis (B : Family V) (α : Exponent V) (p : ℕ)
    (F : QuotientFaceIndex B α p) :
    quotientPieceBaseChangeEquiv (R := R) (S := S) B α p
      (1 ⊗ₜ[R] quotientTotalPieceBasis (k := R) B α p F) =
        quotientTotalPieceBasis (k := S) B α p F := by
  change (((quotientTotalPieceBasis (k := R) B α p).baseChange S).equiv
    (quotientTotalPieceBasis (k := S) B α p) (Equiv.refl _))
      (1 ⊗ₜ[R] quotientTotalPieceBasis (k := R) B α p F) = _
  simpa only [Module.Basis.baseChange_apply, Equiv.refl_apply] using
    Module.Basis.equiv_apply ((quotientTotalPieceBasis (k := R) B α p).baseChange S) F
      (quotientTotalPieceBasis (k := S) B α p) (Equiv.refl _)

def quotientPieceScalarMap (B : Family V) (α : Exponent V) (p : ℕ) :
    totalFacePiece (k := R) (quotientKoszulFaces B α) p →ₗ[R]
      totalFacePiece (k := S) (quotientKoszulFaces B α) p :=
  ((quotientPieceBaseChangeEquiv (R := R) (S := S) B α p).toLinearMap.restrictScalars R).comp
    (TensorProduct.mk R S (totalFacePiece (k := R) (quotientKoszulFaces B α) p) 1)

@[simp] lemma quotientPieceScalarMap_basis (B : Family V) (α : Exponent V) (p : ℕ)
    (F : QuotientFaceIndex B α p) :
    quotientPieceScalarMap (R := R) (S := S) B α p
      (quotientTotalPieceBasis (k := R) B α p F) =
        quotientTotalPieceBasis (k := S) B α p F :=
  quotientPieceBaseChangeEquiv_basis B α p F

theorem quotientPieceBaseChangeEquiv_differential (B : Family V) (α : Exponent V) (p : ℕ)
    (x : S ⊗[R] (quotientTotalData (k := R) B α).piece (p+1)) :
    quotientPieceBaseChangeEquiv (R := R) (S := S) B α p
        (((quotientTotalData (k := R) B α).differential p).baseChange S x) =
      (quotientTotalData (k := S) B α).differential p
        (quotientPieceBaseChangeEquiv (R := R) (S := S) B α (p+1) x) := by
  have he : (quotientPieceBaseChangeEquiv (R := R) (S := S) B α p).toLinearMap.comp
        (((quotientTotalData (k := R) B α).differential p).baseChange S) =
      ((quotientTotalData (k := S) B α).differential p).comp
        (quotientPieceBaseChangeEquiv (R := R) (S := S) B α (p+1)).toLinearMap := by
    apply ((quotientTotalPieceBasis (k := R) B α (p+1)).baseChange S).ext
    intro F
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.baseChange_apply,
      LinearMap.baseChange_tmul, quotientPieceBaseChangeEquiv_basis]
    change quotientPieceScalarMap (R := R) (S := S) B α p
        ((quotientTotalData (k := R) B α).differential p
          (quotientTotalPieceBasis (k := R) B α (p+1) F)) =
      (quotientTotalData (k := S) B α).differential p
        (quotientPieceBaseChangeEquiv (R := R) (S := S) B α (p+1)
          (1 ⊗ₜ[R] quotientTotalPieceBasis (k := R) B α (p+1) F))
    rw [quotientPieceBaseChangeEquiv_basis (R := R) (S := S) B α (p+1) F,
      quotientTotalPieceBasis_differential (R := R) B α p F,
      quotientTotalPieceBasis_differential (R := S) B α p F, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hj
    · let y : totalFacePiece (k := R) (quotientKoszulFaces B α) p :=
        quotientTotalPieceBasis (k := R) B α p (eraseQuotientFace F j hj)
      have hy : quotientPieceScalarMap (R := R) (S := S) B α p y =
          quotientTotalPieceBasis (k := S) B α p (eraseQuotientFace F j hj) :=
        quotientPieceScalarMap_basis (R := R) (S := S) B α p (eraseQuotientFace F j hj)
      have hz := AddMonoidHom.map_zsmul
        (α := ↥(totalFacePiece (k := R) (quotientKoszulFaces B α) p))
        (β := ↥(totalFacePiece (k := S) (quotientKoszulFaces B α) p))
        (quotientPieceScalarMap (R := R) (S := S) B α p).toAddMonoidHom
        (TauCeti.ExteriorAlgebra.basisEraseSign j.val F.val : ℤ) y
      simp only [LinearMap.toAddMonoidHom_coe] at hz
      rw [hy] at hz
      simpa only [y, Units.smul_def, int_smul_eq_zsmul] using hz
    · exact map_zero _
  exact LinearMap.congr_fun he x

/-- Identification of the actual homology quotient after coefficient change. -/
def quotientPieceBaseChangeHomologyEquiv (B : Family V) (α : Exponent V) (p : ℕ) :
    FourPapers.ProjectiveComplexSplitting.ScalarHomology
      (fun j => ↥((quotientTotalData (k := R) B α).piece j)) (quotientTotalData B α).differential
      (quotientTotalData B α).differential_comp S p ≃ₗ[S]
    FourPapers.ProjectiveComplexSplitting.Homology
      (fun j => ↥((quotientTotalData (k := S) B α).piece j)) (quotientTotalData B α).differential
      (quotientTotalData B α).differential_comp p :=
  FourPapers.ProjectiveComplexSplitting.chainHomologyEquiv
    (FourPapers.ProjectiveComplexSplitting.scalarPiece (R := R) (fun j => ↥((quotientTotalData (k := R) B α).piece j)) S)
    (fun j => ↥((quotientTotalData (k := S) B α).piece j))
    (FourPapers.ProjectiveComplexSplitting.scalarDifferential
      (fun j => ↥((quotientTotalData (k := R) B α).piece j)) (quotientTotalData B α).differential S)
    (quotientTotalData (k := S) B α).differential
    (FourPapers.ProjectiveComplexSplitting.scalarDifferential_comp
      (fun j => ↥((quotientTotalData (k := R) B α).piece j)) (quotientTotalData B α).differential
      (quotientTotalData B α).differential_comp S)
    (quotientTotalData (k := S) B α).differential_comp
    (quotientPieceBaseChangeEquiv B α) (quotientPieceBaseChangeEquiv_differential B α) p

theorem quotientDegreeHomology_finrank_baseChange
    [StrongRankCondition R] [StrongRankCondition S]
    (B : Family V) (α : Exponent V)
    (hfree : ∀ p, Module.Free R (ClosedGraphDegreeHomology (k := R) B α p)) (p : ℕ) :
    Module.finrank S (ClosedGraphDegreeHomology (k := S) B α p) =
      Module.finrank R (ClosedGraphDegreeHomology (k := R) B α p) := by
  letI := hfree p
  letI : Module.Free R (FourPapers.ProjectiveComplexSplitting.Homology
      (fun j => ↥((quotientTotalData (k := R) B α).piece j)) (quotientTotalData B α).differential
      (quotientTotalData B α).differential_comp p) :=
    Module.Free.of_equiv (quotientPieceHomologyEquiv (k := R) B α p).symm
  rw [← (quotientPieceHomologyEquiv (k := S) B α p).finrank_eq,
    ← (quotientPieceBaseChangeHomologyEquiv (R := R) (S := S) B α p).finrank_eq]
  rw [FourPapers.ProjectiveComplexSplitting.scalarHomology_finrank
    (fun j => ↥((quotientTotalData (k := R) B α).piece j)) (quotientTotalData B α).differential
    (quotientTotalData B α).differential_comp S (quotientTotalPiece_projective B α)
    (quotientPieceHomology_projective B α hfree) p]
  exact (quotientPieceHomologyEquiv (k := R) B α p).finrank_eq

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.quotientDegreeHomology_finrank_baseChange

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.UnitIntervalCoefficientIntegral -/
section

/-!
# Integral coefficient homology in arbitrary row count

The restriction and linear-variable splitting are the actual face-complex
maps. They reduce every chain coefficient quotient to the proved zero-or-one
model of the original unit-interval ideal. Degree projections are genuine
retracts, so over a domain the homology in each exterior degree is also zero
or one free copy. Applying arbitrary base change to the integral complex
then proves equality of the ordinary derived-Tor dimensions over all fields.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {k : Type u} [CommRing k]
  {d N m : ℕ} {E : Finset ((Fin (d+1) → Fin N))}

theorem unitInterval_restricted_homology_small (hE : UnitIntervalFacetFamily E)
    (A : ∀ r, Finset (Fin (UnitIntervalRows d N r)))
    (α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))) :
    ClosedGraphSmallFreeModel k (ClosedGraphFaceHomology (k := k)
      (finiteRowFamily (UnitIntervalRows d N) (finiteRowRestriction E A)) α) := by
  by_cases hs : SupportedRows A α
  · exact ClosedGraphSmallFreeModel.of_equiv
      (quotientFaceHomologyEquivOfFaces _ _ α α (quotientFaces_finiteRowRestriction E A α hs))
      (unitInterval_fine_homology_small (k := k) hE α)
  · change ¬∀ r j, 0 < α ⟨r, ULift.up j⟩ → j ∈ A r at hs
    push_neg at hs
    obtain ⟨r, j, hj, hjA⟩ := hs
    apply Or.inl
    apply closedGraphHomology_subsingleton_of_boundaries
    intro z hz
    apply quotient_cycle_boundary_free_variable (e := ⟨r, ULift.up j⟩) _ hj z hz
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    have haA := ((mem_finiteRowRestriction _ A a).mp ha).2 r
    have hne : a r ≠ j := fun he => hjA (he ▸ haA)
    simp only [finiteRowExponent_apply, if_neg hne]

theorem unitInterval_linear_restriction_homology_small (hE : UnitIntervalFacetFamily E)
    (L : Finset (FiniteVariable.{u} (UnitIntervalRows d N)))
    (A : ∀ r, Finset (Fin (UnitIntervalRows d N r)))
    (hA : ∀ r j, j ∈ A r → (⟨r, ULift.up j⟩ : FiniteVariable.{u} (UnitIntervalRows d N)) ∉ L)
    (α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))) :
    ClosedGraphSmallFreeModel k (ClosedGraphFaceHomology (k := k)
      (variableMonomialFamily L ∪ finiteRowFamily (UnitIntervalRows d N) (finiteRowRestriction E A)) α) := by
  by_cases hsq : ∀ v, α v ≤ 1
  · let B := finiteRowFamily (UnitIntervalRows d N) (finiteRowRestriction E A)
    have hB : ∀ b ∈ B, ∀ v, b v ≠ 0 → v ∉ L := by
      intro b hb v hv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      rcases v with ⟨r, ⟨j⟩⟩
      have haA := ((mem_finiteRowRestriction _ A a).mp ha).2 r
      by_cases he : a r = j
      · exact hA r j (he ▸ haA)
      · simp [finiteRowExponent_apply, he] at hv
    let C := variableMonomialFamily L ∪ B
    change ClosedGraphSmallFreeModel k (ClosedGraphFaceHomology (k := k) C α)
    letI : DecidableEq (FiniteVariable.{u} (UnitIntervalRows d N)) := LinearOrder.toDecidableEq
    let C' := variableMonomialFamily L ∪ B
    have hC : C = C' := by
      ext b
      simp only [C, C', Finset.mem_union]
    let e₀ : ClosedGraphFaceHomology (k := k) C α ≃ₗ[k]
        ClosedGraphFaceHomology (k := k) C' α :=
      quotientFaceHomologyEquivOfFaces C C' α α
        (congrArg (fun D => quotientKoszulFaces D α) hC)
    let δ := α.filter (fun v => v ∉ L)
    let e : ClosedGraphFaceHomology (k := k) C' α ≃ₗ[k]
        ClosedGraphFaceHomology (k := k) B δ :=
      linearVariableQuotientHomologyEquiv (k := k) L B hB α hsq
    have hsmall : ClosedGraphSmallFreeModel k (ClosedGraphFaceHomology (k := k) B δ) :=
      unitInterval_restricted_homology_small (k := k) hE A δ
    exact ClosedGraphSmallFreeModel.of_equiv (R := k)
      (M := ClosedGraphFaceHomology (k := k) C α)
      (P := ClosedGraphFaceHomology (k := k) B δ) (e₀.trans e) hsmall
  · push_neg at hsq
    obtain ⟨v, hv⟩ := hsq
    apply Or.inl
    apply closedGraphHomology_subsingleton_of_boundaries
    intro z hz
    apply quotient_cycle_boundary_of_two_le (e := v) _ (by omega) z hz
    intro b hb
    rcases Finset.mem_union.mp hb with hb | hb
    · exact variableMonomialFamily_squarefree L b hb v
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      rcases v with ⟨r, ⟨j⟩⟩
      simp only [finiteRowExponent_apply]
      split_ifs <;> omega

theorem unitInterval_chain_coefficient_homology_small (hE : UnitIntervalFacetFamily E)
    (w : FiniteMultichain (UnitIntervalRows d N) E m)
    (α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))) :
    ClosedGraphSmallFreeModel k (ClosedGraphFaceHomology (k := k)
      (finiteChainCoefficientFamily (UnitIntervalRows d N) w) α) := by
  cases m with
  | succ m =>
      exact ClosedGraphSmallFreeModel.of_equiv
        (quotientFaceHomologyEquivOfFaces _ _ α α (unitIntervalChainCoefficient_faces hE w α))
        (unitInterval_linear_restriction_homology_small (k := k) hE
          (unitIntervalChainLinearVariables w) (unitIntervalChainResidualRows.{u} w)
          (closedGraphRowsOutside_avoids _ _) α)
  | zero =>
      have hw : finiteChainCoefficientFamily.{u} (UnitIntervalRows d N) w = ∅ := by
        simp [finiteChainCoefficientFamily]
      by_cases hα : α = 0
      · subst α
        apply Or.inr
        refine ⟨closedGraphZeroStrandHomologyEquiv _ ?_⟩
        rw [hw]
        rintro ⟨b, hb, _⟩
        exact Finset.notMem_empty b hb
      · obtain ⟨v, hv⟩ : ∃ v, 0 < α v := by
          by_contra h
          push_neg at h
          apply hα
          ext v
          exact Nat.eq_zero_of_le_zero (h v)
        apply Or.inl
        apply closedGraphHomology_subsingleton_of_boundaries
        intro z hz
        apply quotient_cycle_boundary_free_variable (e := v) _ hv z hz
        intro b hb
        rw [hw] at hb
        exact (Finset.notMem_empty b hb).elim

section Domain
variable [IsDomain k]

theorem unitInterval_chain_coefficient_degree_homology_small (hE : UnitIntervalFacetFamily E)
    (w : FiniteMultichain (UnitIntervalRows d N) E m)
    (α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))) (p : ℕ) :
    ClosedGraphSmallFreeModel k (ClosedGraphDegreeHomology (k := k)
      (finiteChainCoefficientFamily (UnitIntervalRows d N) w) α p) :=
  closedGraphDegreeHomology_small_of_total _ α p
    (unitInterval_chain_coefficient_homology_small (k := k) hE w α)

theorem unitInterval_chain_coefficient_degree_homology_free (hE : UnitIntervalFacetFamily E)
    (w : FiniteMultichain (UnitIntervalRows d N) E m)
    (α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))) (p : ℕ) :
    Module.Free k (ClosedGraphDegreeHomology (k := k)
      (finiteChainCoefficientFamily (UnitIntervalRows d N) w) α p) :=
  (unitInterval_chain_coefficient_degree_homology_small (k := k) hE w α p).free

end Domain

section Fields
variable (K L : Type u) [Field K] [Field L]

/-- The same literal coefficient quotient has the same derived-Tor dimensions
over every pair of fields. The common reference complex is defined over the
integers, lifted only to match the universe of the variable indexing type. -/
theorem unitInterval_coefficient_betti_field_independent (hE : UnitIntervalFacetFamily E)
    (w : FiniteMultichain (UnitIntervalRows d N) E m)
    (α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))) (p : ℕ) :
    quotientBettiNumber (k := K) (finiteChainCoefficientFamily (UnitIntervalRows d N) w) α p =
      quotientBettiNumber (k := L) (finiteChainCoefficientFamily (UnitIntervalRows d N) w) α p := by
  let R := ULift.{u} ℤ
  letI : IsDomain R := MulEquiv.isDomain ℤ (ULift.ringEquiv : R ≃+* ℤ).toMulEquiv
  letI : Algebra R K := ULift.algebra' ℤ K
  letI : Algebra R L := ULift.algebra' ℤ L
  let B := finiteChainCoefficientFamily (UnitIntervalRows d N) w
  have hfree (i : ℕ) : Module.Free R (ClosedGraphDegreeHomology (k := R) B α i) :=
    unitInterval_chain_coefficient_degree_homology_free (k := R) hE w α i
  have hK := quotientDegreeHomology_finrank_baseChange (R := R) (S := K) B α hfree p
  have hL := quotientDegreeHomology_finrank_baseChange (R := R) (S := L) B α hfree p
  rw [quotientBettiNumber_eq_homology, quotientBettiNumber_eq_homology,
    (quotientCategoricalDegreeHomologyEquiv (k := K) B α p).finrank_eq,
    (quotientCategoricalDegreeHomologyEquiv (k := L) B α p).finrank_eq]
  exact hK.trans hL.symm

/-- Characteristic independence in every fine degree and every positive
power. The all-power formula is applied only to actual Tor groups. -/
theorem unitInterval_power_betti_field_independent (hE : UnitIntervalFacetFamily E)
    (m : ℕ) (hm : 0 < m) (α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))) (p : ℕ) :
    bettiNumber (k := K)
      (exponentPowerFamily (finiteRowFamily (UnitIntervalRows d N) E) m) α p =
    bettiNumber (k := L)
      (exponentPowerFamily (finiteRowFamily (UnitIntervalRows d N) E) m) α p := by
  rw [allPowerBetti_admissible hE.latticeClosed m hm p α,
    allPowerBetti_admissible hE.latticeClosed m hm p α]
  apply Finset.sum_congr rfl
  intro w _
  exact unitInterval_coefficient_betti_field_independent K L hE w.val _ p

end Fields
end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.unitInterval_power_betti_field_independent

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.GraphUnitIntervalFamily -/
section

/-! # Interval-graph edge families as two-row unit-interval families -/

section
set_option autoImplicit false
noncomputable section
namespace FourPapers.Sublattice
open Classical
variable {N : ℕ}

/-- The edge family of an interval-labeled graph is precisely a two-row
unit-interval facet family; this is a theorem about its actual edges. -/
theorem graphEdgeLattice_unitInterval (G : SimpleGraph (Fin N)) (hG : IntervalLabeling G) :
    UnitIntervalFacetFamily (d := 1) (graphEdgeLattice G) := by
  constructor
  · intro a ha i j hij
    have ha01 := ((mem_graphEdgeLattice G a).mp ha).1
    fin_cases i <;> fin_cases j <;> simp_all
  · intro a ha b hb hab hba
    have hb01 : b 0 < b 1 := hb (by decide : (0 : Fin 2) < 1)
    have haG := ((mem_graphEdgeLattice G a).mp ha).2
    change b 1 ≤ a 1 at hba
    exact (mem_graphEdgeLattice G b).mpr ⟨hb01,
      interval_adj_right hG (interval_adj_left hG haG hab (hb01.trans_le hba)) hb01 hba⟩


end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.CliqueCycleLifting -/
section

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 300000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open FourPapers.Universal
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
variable {N : ℕ} {k : Type u} [CommRing k]

/-- The complete-interval initial ideal has no homology in the error degree
of a linear-strand cycle. Consequently every such leading cycle lifts in its
unchanged auxiliary degree through an actual monic Gröbner degeneration. -/
theorem groebnerIntervalClique_linear_cycle_lift
    (l r : Fin N) (m : MonomialOrder (FiniteVariable.{u} (GraphRows N)))
    (J : Ideal (MvPolynomial (FiniteVariable.{u} (GraphRows N)) k))
    (G : Set (MvPolynomial (FiniteVariable.{u} (GraphRows N)) k))
    (hG : m.IsGroebnerBasis G J)
    (hu : ∀g∈G,g≠0→IsUnit (m.leadingCoeff g))
    (hstd : ∀a,a∈m.standardMonomials J ↔
      QuotientAllowed (finiteRowFamily (GraphRows N)
        (graphEdgeLattice (intervalCliqueGraph l r))) a)
    (w : FiniteVariable.{u} (GraphRows N) → ℕ)
    (htail : ∀g∈G,g≠0→∀b∈(monomial (m.degree g) 1-g).support,
      Finsupp.weight w b<Finsupp.weight w (m.degree g))
    {A : Type*} [AddCommMonoid A] (deg : FiniteVariable.{u} (GraphRows N) → A)
    (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule k deg)) (a : A) (p : ℕ)
    (hdegree : ∀α,Finsupp.weight deg α=a→α.degree=p+2)
    (n : ℕ)
    (z : Set.powersetCard (FiniteVariable.{u} (GraphRows N)) (p+1) →₀
      CoefficientQuotient (k := k)
        (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))))
    (hza : z∈Grading.Piece (quotientCoefficientBasis
      (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) (p+1))
      (fun t => Finsupp.weight deg (quotientDegree t)) a)
    (hzw : z∈Grading.Piece (quotientCoefficientBasis
      (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) (p+1))
      (fun t => Finsupp.weight w (quotientDegree t)) n)
    (hdz : quotientDifferential
      (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) p z=0) :
    ∃y,y∈Grading.Piece (quotientCoefficientBasis
      (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) (p+1))
      (fun t => Finsupp.weight deg (quotientDegree t)) a ∧
      groebnerQuotientDifferential m J G hG hu
        (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) hstd p y=0 ∧
      z-y∈(basisFiltration (quotientCoefficientBasis
        (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) (p+1))
        (fun t => Finsupp.weight w (quotientDegree t))).level n := by
  apply groebnerQuotient_lift_cycle_of_fine_fillings m J G hG hu _ hstd w htail deg hJ a p _
    n z hza hzw hdz
  intro α hα y hy hdy
  exact intervalClique_quotientCoordinateCycle_boundary l r α p
    (by rw [hdegree α hα]; omega) (by rw [hdegree α hα]; omega) y hy hdy

/-- The same lift with an explicit natural-number scalar structure on the
auxiliary degree monoid and an explicit equality decision procedure. These
choices are unique; transporting their equality prevents expensive normalization
of product/Finsupp scalar actions and grading dictionaries. -/
theorem groebnerIntervalClique_linear_cycle_lift_withNatModule
    (l r : Fin N) (m : MonomialOrder (FiniteVariable.{u} (GraphRows N)))
    (J : Ideal (MvPolynomial (FiniteVariable.{u} (GraphRows N)) k))
    (G : Set (MvPolynomial (FiniteVariable.{u} (GraphRows N)) k))
    (hG : m.IsGroebnerBasis G J)
    (hu : ∀g∈G,g≠0→IsUnit (m.leadingCoeff g))
    (hstd : ∀a,a∈m.standardMonomials J ↔
      QuotientAllowed (finiteRowFamily (GraphRows N)
        (graphEdgeLattice (intervalCliqueGraph l r))) a)
    (w : FiniteVariable.{u} (GraphRows N) → ℕ)
    (htail : ∀g∈G,g≠0→∀b∈(monomial (m.degree g) 1-g).support,
      Finsupp.weight w b<Finsupp.weight w (m.degree g))
    {A : Type*} [AddCommMonoid A] [hNat : Module ℕ A] [hDec : DecidableEq A] (deg : FiniteVariable.{u} (GraphRows N) → A)
    (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule k deg)) (a : A) (p : ℕ)
    (hdegree : ∀α,Finsupp.weight deg α=a→α.degree=p+2)
    (n : ℕ)
    (z : Set.powersetCard (FiniteVariable.{u} (GraphRows N)) (p+1) →₀
      CoefficientQuotient (k := k)
        (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))))
    (hza : z∈Grading.Piece (quotientCoefficientBasis
      (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) (p+1))
      (fun t => Finsupp.weight deg (quotientDegree t)) a)
    (hzw : z∈Grading.Piece (quotientCoefficientBasis
      (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) (p+1))
      (fun t => Finsupp.weight w (quotientDegree t)) n)
    (hdz : quotientDifferential
      (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) p z=0) :
    ∃y,y∈Grading.Piece (quotientCoefficientBasis
      (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) (p+1))
      (fun t => Finsupp.weight deg (quotientDegree t)) a ∧
      groebnerQuotientDifferential m J G hG hu
        (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) hstd p y=0 ∧
      z-y∈(basisFiltration (quotientCoefficientBasis
        (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) (p+1))
        (fun t => Finsupp.weight w (quotientDegree t))).level n := by
  have hd : hDec = Classical.decEq A := Subsingleton.elim _ _
  subst hDec
  have he : hNat = (AddCommMonoid.toNatModule : Module ℕ A) := Subsingleton.elim _ _
  subst hNat
  exact groebnerIntervalClique_linear_cycle_lift l r m J G hG hu hstd w htail
    deg hJ a p hdegree n z hza hzw hdz

end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.RectangleCoordinates -/
section

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 250000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

lemma rectangleFaceVector_card (X Y : Finset V) :
    rectangleFaceVector (k := k) X Y∈basisSpan Simplicial.basis
      (fun F => F.card=X.card+Y.card-1) := by
  apply faceSpan_mul_mem (fun F => ∃x∈X,F=X.erase x) (fun F => F=Y)
    (fun F => F.card=X.card+Y.card-1) _ (boundary_mem_eraseSpan X)
    (Submodule.subset_span ⟨Y,rfl,rfl⟩)
  intro F hF G hG hFG
  obtain ⟨x,hx,rfl⟩ := hF
  subst G
  rw [Finset.card_union_of_disjoint hFG,Finset.card_erase_of_mem hx]
  have hpos := Finset.card_pos.mpr ⟨x,hx⟩
  omega

lemma rectangleFaceVector_chains (B : Family V) (X Y : Finset V)
    (hXY : Disjoint X Y) (hlinear : ∀x∈X,¬Contains B (Finsupp.single x 1)) :
    rectangleFaceVector (k := k) X Y∈
      Simplicial.Chains (quotientKoszulFaces B (rectangleFaceDegree X Y)) (X.card+Y.card-1) := by
  have hQ := rectangleFaceVector_mem (k := k) B X Y hXY hlinear
  have hD := rectangleFaceVector_card (k := k) X Y
  rw [Simplicial.Chains,Simplicial.basis.mem_span_image]
  intro F hF
  exact ⟨(Simplicial.basis.mem_span_image.mp hQ) hF,
    (Simplicial.basis.mem_span_image.mp hD) hF⟩

def rectangleCoordinate (B : Family V) (X Y : Finset V) (p : ℕ)
    (hXY : Disjoint X Y) (hcard : X.card+Y.card=p+2)
    (hlinear : ∀x∈X,¬Contains B (Finsupp.single x 1)) :
    Set.powersetCard V (p+1) →₀ CoefficientQuotient (k := k) B :=
  (quotientFaceHomogeneousEquiv B (rectangleFaceDegree X Y) (p+1)
    ⟨rectangleFaceVector X Y,by
      have hh := rectangleFaceVector_chains (k := k) B X Y hXY hlinear
      have hc : X.card+Y.card-1=p+1 := by omega
      simpa only [hc] using hh⟩).val

lemma rectangleCoordinate_fine (B : Family V) (X Y : Finset V) (p : ℕ)
    (hXY : Disjoint X Y) (hcard : X.card+Y.card=p+2)
    (hlinear : ∀x∈X,¬Contains B (Finsupp.single x 1)) :
    rectangleCoordinate (k := k) B X Y p hXY hcard hlinear∈
      quotientPiece (k := k) B (rectangleFaceDegree X Y) (p+1) :=
  (quotientFaceHomogeneousEquiv B (rectangleFaceDegree X Y) (p+1) _).property

lemma rectangleCoordinate_closed (B : Family V) (X Y : Finset V) (p : ℕ)
    (hXY : Disjoint X Y) (hcard : X.card+Y.card=p+2)
    (hlinear : ∀x∈X,¬Contains B (Finsupp.single x 1))
    (hedges : ∀x∈X,∀y∈Y,Contains B (Finsupp.single x 1+Finsupp.single y 1)) :
    quotientDifferential (k := k) B p (rectangleCoordinate (k := k) B X Y p hXY hcard hlinear)=0 := by
  let z : Simplicial.Chains (k := k) (quotientKoszulFaces B (rectangleFaceDegree X Y)) (p+1) :=
    ⟨rectangleFaceVector X Y,by
      have hh := rectangleFaceVector_chains (k := k) B X Y hXY hlinear
      have hc : X.card+Y.card-1=p+1 := by omega
      simpa only [hc] using hh⟩
  have hz : quotientFaceDifferential (k := k) B (rectangleFaceDegree X Y) p z=0 := by
    apply Subtype.ext
    rw [quotientFaceDifferential_val]
    exact relativeProjection_zero_on_discarded (Simplicial.basis (k := k))
      (fullKoszulFaces (rectangleFaceDegree X Y))
      (forbiddenKoszulFaces B (rectangleFaceDegree X Y))
      (rectangleFaceVector_boundary_mem (k := k) B X Y hXY hedges)
  have hh := quotientFaceHomogeneousEquiv_differential (k := k) B (rectangleFaceDegree X Y) p z
  rw [hz,(quotientFaceHomogeneousEquiv (k := k) B (rectangleFaceDegree X Y) p).map_zero] at hh
  exact congrArg Subtype.val hh

lemma rectangleCoordinate_regraded {A : Type*} (deg : Exponent V → A)
    (B : Family V) (X Y : Finset V) (p : ℕ)
    (hXY : Disjoint X Y) (hcard : X.card+Y.card=p+2)
    (hlinear : ∀x∈X,¬Contains B (Finsupp.single x 1)) :
    rectangleCoordinate (k := k) B X Y p hXY hcard hlinear∈
      Grading.Piece (quotientCoefficientBasis B (p+1)) (fun t => deg (quotientDegree t))
        (deg (rectangleFaceDegree X Y)) :=
  piece_regrade _ quotientDegree _ deg (rectangleCoordinate_fine B X Y p hXY hcard hlinear)

lemma rectangleFaceDegree_degree (X Y : Finset V) (hXY : Disjoint X Y) :
    (rectangleFaceDegree X Y).degree=X.card+Y.card := by
  rw [rectangleFaceDegree,degree_faceExponent,Finset.card_union_of_disjoint hXY]

end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.GraphCliqueCycleLifting -/
section

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open FourPapers.Universal
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
variable {N : ℕ} {k : Type u} [CommRing k] [IsDomain k]

lemma intervalCliqueGraph_closed (l r : Fin N) : ClosedLabeling (intervalCliqueGraph l r) := by
  constructor
  · intro a b c hab hac hbc habG hacG
    exact ⟨hbc,habG.2.2.2.1,habG.2.2.2.2,hacG.2.2.2.1,hacG.2.2.2.2⟩
  · intro a b c hac hbc hab hacG hbcG
    exact ⟨hab,hacG.2.1,hacG.2.2.1,hbcG.2.1,hbcG.2.2.1⟩

lemma graphVertexRowDegree_total (α : Exponent (FiniteVariable.{u} (GraphRows N))) :
    (Finsupp.weight graphVertexRowDegree α).1.degree=α.degree := by
  induction α using Finsupp.induction_linear with
  | zero => simp
  | add α β ihα ihβ => simpa only [map_add,Prod.fst_add,ihα,ihβ]
  | single v n => simp [Finsupp.weight_single,graphVertexRowDegree]

lemma graphVertexRowDegree_eq_total
    (α β : Exponent (FiniteVariable.{u} (GraphRows N)))
    (h : Finsupp.weight graphVertexRowDegree α=Finsupp.weight graphVertexRowDegree β) :
    α.degree=β.degree := by
  have hh := congrArg (fun a : (Fin N →₀ ℕ) × (Fin 2 →₀ ℕ) => a.1.degree) h
  simpa only [graphVertexRowDegree_total] using hh

lemma graphBinomialGenerators_unit_leading (G : SimpleGraph (Fin N)) :
    ∀g∈graphBinomialGenerators (k := k) G,g≠0→IsUnit (graphLexOrder.leadingCoeff g) := by
  rintro _ ⟨i,j,hij,_,rfl⟩ _
  rw [graphBinomial_leadingCoeff (k := k) hij]
  exact isUnit_one

/-- The literal ordinary quotient differential in the actual binomial graph
quotient, written in its proved standard monomial coordinates. -/
def graphOrdinaryQuotientDifferential (G : SimpleGraph (Fin N)) (hG : ClosedLabeling G)
    (p : ℕ) :
    (Set.powersetCard (FiniteVariable.{u} (GraphRows N)) (p+1) →₀
      CoefficientQuotient (k := k) (finiteRowFamily (GraphRows N) (graphEdgeLattice G))) →ₗ[k]
    (Set.powersetCard (FiniteVariable.{u} (GraphRows N)) p →₀
      CoefficientQuotient (k := k) (finiteRowFamily (GraphRows N) (graphEdgeLattice G))) :=
  groebnerQuotientDifferential graphLexOrder (graphBinomialIdeal (k := k) G) (graphBinomialGenerators (k := k) G)
    (closedGraph_binomial_groebner (k := k) hG) (graphBinomialGenerators_unit_leading (k := k) G)
    (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
    (closedGraph_standardMonomials (k := k) hG) p

attribute [local irreducible] groebnerQuotientDifferential

/-- Every initial linear-strand cycle of a complete interval lifts through its
actual binomial edge ideal. Vertex and row degrees are unchanged, and the
correction has strictly smaller diagonal weight. No homology-surjectivity or
flatness assumption occurs in this statement. -/
theorem intervalClique_linear_cycle_lift (l r : Fin N)
    (α : Exponent (FiniteVariable.{u} (GraphRows N))) (p : ℕ)
    (hα : α.degree=p+2) (n : ℕ)
    (z : Set.powersetCard (FiniteVariable.{u} (GraphRows N)) (p+1) →₀
      CoefficientQuotient (k := k)
        (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))))
    (hza : z∈Grading.Piece (quotientCoefficientBasis (k := k)
      (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) (p+1))
      (fun t => Finsupp.weight graphVertexRowDegree (quotientDegree t))
      (Finsupp.weight graphVertexRowDegree α))
    (hzw : z∈Grading.Piece (quotientCoefficientBasis (k := k)
      (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) (p+1))
      (fun t => Finsupp.weight graphDiagonalWeight (quotientDegree t)) n)
    (hdz : quotientDifferential (k := k)
      (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) p z=0) :
    ∃y,y∈Grading.Piece (quotientCoefficientBasis (k := k)
      (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) (p+1))
      (fun t => Finsupp.weight graphVertexRowDegree (quotientDegree t))
      (Finsupp.weight graphVertexRowDegree α) ∧
      graphOrdinaryQuotientDifferential (k := k) (intervalCliqueGraph l r)
        (intervalCliqueGraph_closed l r) p y=0 ∧
      z-y∈(basisFiltration (K := k) (quotientCoefficientBasis (k := k)
        (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) (p+1))
        (fun t => Finsupp.weight graphDiagonalWeight (quotientDegree t))).level n := by
  have hhom : (graphBinomialIdeal (k := k) (intervalCliqueGraph l r)).IsHomogeneous
      (weightedHomogeneousSubmodule k
        (graphVertexRowDegree : FiniteVariable.{u} (GraphRows N) →
          (Fin N →₀ ℕ) × (Fin 2 →₀ ℕ))) :=
    graphBinomialIdeal_vertexRow_homogeneous (k := k) (intervalCliqueGraph l r)
  unfold graphOrdinaryQuotientDifferential
  have hdegree : ∀ β : Exponent (FiniteVariable.{u} (GraphRows N)),
      Finsupp.weight graphVertexRowDegree β = Finsupp.weight graphVertexRowDegree α →
        β.degree = p + 2 := by
    intro β hβ
    exact (graphVertexRowDegree_eq_total β α hβ).trans hα
  have hlift := groebnerIntervalClique_linear_cycle_lift_withNatModule
    (N := N) (k := k) (l := l) (r := r) (m := graphLexOrder)
    (J := graphBinomialIdeal (k := k) (intervalCliqueGraph l r))
    (G := graphBinomialGenerators (k := k) (intervalCliqueGraph l r))
    (hG := closedGraph_binomial_groebner (k := k) (G := intervalCliqueGraph l r)
      (intervalCliqueGraph_closed l r))
    (hu := graphBinomialGenerators_unit_leading (k := k) (intervalCliqueGraph l r))
    (hstd := closedGraph_standardMonomials (k := k) (G := intervalCliqueGraph l r)
      (intervalCliqueGraph_closed l r))
    (w := graphDiagonalWeight)
    (htail := graphBinomialGenerators_weight_tails (k := k) (intervalCliqueGraph l r))
    (A := (Fin N →₀ ℕ) × (Fin 2 →₀ ℕ))
    (hNat := (inferInstance : Module ℕ ((Fin N →₀ ℕ) × (Fin 2 →₀ ℕ))))
    (hDec := (inferInstance : DecidableEq ((Fin N →₀ ℕ) × (Fin 2 →₀ ℕ))))
    (deg := graphVertexRowDegree)
    (hJ := hhom) (a := Finsupp.weight graphVertexRowDegree α) (p := p)
    (hdegree := hdegree) (n := n) (z := z) (hza := hza) (hzw := hzw) (hdz := hdz)
  exact hlift

end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.GraphRectangleInterval -/
section

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 250000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.Universal
universe u
variable {N : ℕ} {G : SimpleGraph (Fin N)}
  {A : ∀r,Finset (Fin (GraphRows N r))}

def GraphRectangle.lowerVertex (R : GraphRectangle.{u} G A) : Fin N :=
  (R.X.image (fun v => v.2.down)).min' (R.nonemptyX.image _)

def GraphRectangle.upperVertex (R : GraphRectangle.{u} G A) : Fin N :=
  (R.Y.image (fun v => v.2.down)).max' (R.nonemptyY.image _)

lemma GraphRectangle.lowerVertex_mem (R : GraphRectangle.{u} G A) :
    ∃ x ∈ R.X, x.2.down = R.lowerVertex := by
  have hm : R.lowerVertex ∈ R.X.image
      (fun v : FiniteVariable.{u} (GraphRows N) => (v.2.down : Fin N)) :=
    Finset.min'_mem _ (R.nonemptyX.image _)
  obtain ⟨x, hx, hval⟩ := Finset.mem_image.mp hm
  exact ⟨x, hx, hval⟩

lemma GraphRectangle.upperVertex_mem (R : GraphRectangle.{u} G A) :
    ∃ x ∈ R.Y, x.2.down = R.upperVertex := by
  have hm : R.upperVertex ∈ R.Y.image
      (fun v : FiniteVariable.{u} (GraphRows N) => (v.2.down : Fin N)) :=
    Finset.max'_mem _ (R.nonemptyY.image _)
  obtain ⟨x, hx, hval⟩ := Finset.mem_image.mp hm
  exact ⟨x, hx, hval⟩

lemma GraphRectangle.lower_le_X (R : GraphRectangle.{u} G A)
    (x : FiniteVariable.{u} (GraphRows N)) (hx : x∈R.X) : R.lowerVertex≤x.2.down :=
  Finset.min'_le _ _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩)

lemma GraphRectangle.Y_le_upper (R : GraphRectangle.{u} G A)
    (y : FiniteVariable.{u} (GraphRows N)) (hy : y∈R.Y) : y.2.down≤R.upperVertex := by
  unfold GraphRectangle.upperVertex
  exact Finset.le_max' (R.Y.image
    (fun v : FiniteVariable.{u} (GraphRows N) => (v.2.down : Fin N))) y.2.down
    (Finset.mem_image.mpr ⟨y,hy,rfl⟩)

lemma GraphRectangle.X_lt_upper (R : GraphRectangle.{u} G A)
    (x : FiniteVariable.{u} (GraphRows N)) (hx : x∈R.X) : x.2.down<R.upperVertex := by
  obtain ⟨y,hy,hey⟩ := R.upperVertex_mem
  simpa only [hey] using (R.edges x hx y hy).1

lemma GraphRectangle.lower_lt_Y (R : GraphRectangle.{u} G A)
    (y : FiniteVariable.{u} (GraphRows N)) (hy : y∈R.Y) : R.lowerVertex<y.2.down := by
  obtain ⟨x,hx,hex⟩ := R.lowerVertex_mem
  simpa only [hex] using (R.edges x hx y hy).1

lemma GraphRectangle.extreme_edge (R : GraphRectangle.{u} G A) :
    R.lowerVertex<R.upperVertex ∧ G.Adj R.lowerVertex R.upperVertex := by
  obtain ⟨x,hx,hex⟩ := R.lowerVertex_mem
  obtain ⟨y,hy,hey⟩ := R.upperVertex_mem
  simpa only [hex,hey] using R.edges x hx y hy

/-- The complete interval containing a rectangle uses the same vertices and
literal variables as the original graph. -/
def GraphRectangle.inInterval (R : GraphRectangle.{u} G A) :
    GraphRectangle.{u} (intervalCliqueGraph R.lowerVertex R.upperVertex) A where
  X := R.X
  Y := R.Y
  nonemptyX := R.nonemptyX
  nonemptyY := R.nonemptyY
  rowX := R.rowX
  rowY := R.rowY
  retainedX := R.retainedX
  retainedY := R.retainedY
  edges x hx y hy := ⟨(R.edges x hx y hy).1,
    (R.edges x hx y hy).1.ne,R.lower_le_X x hx,(R.X_lt_upper x hx).le,
      (R.lower_lt_Y y hy).le,R.Y_le_upper y hy⟩

lemma GraphRectangle.interval_le (R : GraphRectangle.{u} G A) (hG : IntervalLabeling G) :
    intervalCliqueGraph R.lowerVertex R.upperVertex≤G := by
  intro x y hxy
  exact interval_edge_spans_clique hG R.extreme_edge.2
    hxy.2.1 hxy.2.2.2.1 hxy.2.2.1 hxy.2.2.2.2 hxy.1

lemma graphEdgeFamily_no_linear (H : SimpleGraph (Fin N))
    (v : FiniteVariable.{u} (GraphRows N)) :
    ¬Contains (finiteRowFamily (GraphRows N) (graphEdgeLattice H)) (Finsupp.single v 1) := by
  rintro ⟨b,hb,hbv⟩
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
  have hh := degree_mono hbv
  simp only [finiteRowExponent_degree,Finsupp.degree_single] at hh
  omega

lemma GraphRectangle.edge_contains_unrestricted (R : GraphRectangle.{u} G A)
    (x : FiniteVariable.{u} (GraphRows N)) (hx : x∈R.X)
    (y : FiniteVariable.{u} (GraphRows N)) (hy : y∈R.Y) :
    Contains (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
      (Finsupp.single x 1+Finsupp.single y 1) := by
  refine ⟨finiteRowExponent (GraphRows N) (graphTuple x.2.down y.2.down),?_,?_⟩
  · exact Finset.mem_image.mpr ⟨graphTuple x.2.down y.2.down,
      (mem_graphEdgeLattice G _).mpr (R.edges x hx y hy),rfl⟩
  · exact (graphRowExponent_pair x y (R.rowX x hx) (R.rowY y hy)).le

variable {k : Type u} [CommRing k] [IsDomain k]

lemma GraphRectangle.cliqueIdeal_le (R : GraphRectangle.{u} G A) (hG : IntervalLabeling G) :
    graphBinomialIdeal (k := k) (intervalCliqueGraph R.lowerVertex R.upperVertex)≤
      graphBinomialIdeal G := by
  apply Ideal.span_le.mpr
  rintro f ⟨i,j,hij,hadj,rfl⟩
  exact Ideal.subset_span (graphBinomial_mem hij (R.interval_le hG hadj))

/-- The particular canonical rectangle vector has an actual lift in the
binomial clique quotient. Its same auxiliary degree and strict correction
bound are explicit and will be preserved by the quotient map to the graph. -/
theorem GraphRectangle.clique_cycle_lift (R : GraphRectangle.{u} G A) (p : ℕ)
    (hcard : R.X.card+R.Y.card=p+2) :
    let H := intervalCliqueGraph R.lowerVertex R.upperVertex
    let B := finiteRowFamily (GraphRows N) (graphEdgeLattice H)
    let z := rectangleCoordinate (k := k) B R.X R.Y p R.disjoint hcard
      (fun x _ => graphEdgeFamily_no_linear H x)
    ∃y,y∈Grading.Piece (quotientCoefficientBasis (k := k) B (p+1))
      (fun t => Finsupp.weight graphVertexRowDegree (quotientDegree t))
      (Finsupp.weight graphVertexRowDegree R.fineDegree) ∧
      graphOrdinaryQuotientDifferential (k := k) H (intervalCliqueGraph_closed _ _) p y=0 ∧
      z-y∈(basisFiltration (K := k) (quotientCoefficientBasis (k := k) B (p+1))
        (fun t => Finsupp.weight graphDiagonalWeight (quotientDegree t))).level
          (Finsupp.weight graphDiagonalWeight R.fineDegree) := by
  dsimp only
  apply intervalClique_linear_cycle_lift R.lowerVertex R.upperVertex R.fineDegree p
    (by exact (rectangleFaceDegree_degree R.X R.Y R.disjoint).trans hcard)
  · exact rectangleCoordinate_regraded (Finsupp.weight graphVertexRowDegree) _ R.X R.Y p
      R.disjoint hcard _
  · exact rectangleCoordinate_regraded (Finsupp.weight graphDiagonalWeight) _ R.X R.Y p
      R.disjoint hcard _
  · exact rectangleCoordinate_closed _ R.X R.Y p R.disjoint hcard _
      R.inInterval.edge_contains_unrestricted

end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.QuotientFaceMaps -/
section

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 300000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

def quotientFaceProjectionBetween (B C : Family V) (α : Exponent V) (i : ℕ) :
    Simplicial.Chains (k := k) (quotientKoszulFaces B α) i →ₗ[k]
      Simplicial.Chains (k := k) (quotientKoszulFaces C α) i :=
  ((quotientFaceProjection (k := k) C α).comp
    (Submodule.subtype (Simplicial.Chains (k := k) (quotientKoszulFaces B α) i))).codRestrict _
      (fun x => quotientFaceProjection_degree C α i
        (Simplicial.chains_mono (fun _ h => h.1) i x.property))

lemma quotientFaceProjectionBetween_val (B C : Family V) (α : Exponent V) (i : ℕ)
    (x : Simplicial.Chains (k := k) (quotientKoszulFaces B α) i) :
    (quotientFaceProjectionBetween (k := k) B C α i x).val=quotientFaceProjection (k := k) C α x.val := rfl

lemma initialKoszulFactor_face (P Q : QuotientGroebnerData V k)
    (α : Exponent V) (i : ℕ)
    (x : Simplicial.Chains (k := k) (quotientKoszulFaces P.family α) i) :
    P.initialKoszulFactor Q i (quotientFaceHomogeneousEquiv (k := k) P.family α i x).val=
      (quotientFaceHomogeneousEquiv (k := k) Q.family α i
        (quotientFaceProjectionBetween (k := k) P.family Q.family α i x)).val := by
  let f := (P.initialKoszulFactor Q i).comp
    ((Submodule.subtype (quotientPiece (k := k) P.family α i)).comp
      (quotientFaceHomogeneousEquiv (k := k) P.family α i).toLinearMap)
  let g := (Submodule.subtype (quotientPiece (k := k) Q.family α i)).comp
    ((quotientFaceHomogeneousEquiv (k := k) Q.family α i).toLinearMap.comp
      (quotientFaceProjectionBetween (k := k) P.family Q.family α i))
  have he : f=g := by
    apply (quotientFaceBasis (k := k) P.family α i).ext
    intro F
    change P.initialKoszulFactor Q i
      (quotientFaceHomogeneousEquiv (k := k) P.family α i (quotientFaceBasis (k := k) P.family α i F)).val=_
    rw [quotientFaceHomogeneousEquiv_basis,QuotientGroebnerData.initialKoszulFactor_basis]
    by_cases ha : QuotientAllowed Q.family (α-faceExponent F.val)
    · let T : QuotientFaceIndex Q.family α i := ⟨F.val,⟨⟨F.property.1.1,ha⟩,F.property.2⟩⟩
      have hp : quotientFaceProjectionBetween (k := k) P.family Q.family α i
          (quotientFaceBasis (k := k) P.family α i F)=quotientFaceBasis (k := k) Q.family α i T := by
        apply Subtype.ext
        rw [quotientFaceProjectionBetween_val,quotientFaceBasis_val,quotientFaceBasis_val]
        rw [quotientFaceProjection,relativeProjection_basis,if_pos ⟨F.property.1.1,ha⟩]
      change Finsupp.single _ (quotientMonomial (k := k) Q.family (α-faceExponent F.val))=
        (quotientFaceHomogeneousEquiv (k := k) Q.family α i
          (quotientFaceProjectionBetween (k := k) P.family Q.family α i (quotientFaceBasis (k := k) P.family α i F))).val
      rw [hp,quotientFaceHomogeneousEquiv_basis,quotientCoefficientBasis_apply]
      rfl
    · have hp : quotientFaceProjectionBetween (k := k) P.family Q.family α i
          (quotientFaceBasis (k := k) P.family α i F)=0 := by
        apply Subtype.ext
        rw [quotientFaceProjectionBetween_val,quotientFaceBasis_val]
        change quotientFaceProjection (k := k) Q.family α (Simplicial.basis F.val)=0
        rw [quotientFaceProjection,relativeProjection_basis,
          if_neg (fun h => ha h.2)]
      change Finsupp.single _ (quotientMonomial (k := k) Q.family (α-faceExponent F.val))=
        (quotientFaceHomogeneousEquiv (k := k) Q.family α i
          (quotientFaceProjectionBetween (k := k) P.family Q.family α i (quotientFaceBasis (k := k) P.family α i F))).val
      rw [hp,map_zero]
      rw [quotientMonomial_zero Q.family (α-faceExponent F.val) ha,Finsupp.single_zero]
      rfl
  exact LinearMap.congr_fun he x

/-- The leading quotient map carries the canonical rectangle cycle to the
same canonical rectangle cycle. Its coefficient degree is one, so no
quadratic graph ideal can discard those coefficients. -/
theorem initialKoszulFactor_rectangle (P Q : QuotientGroebnerData V k)
    (X Y : Finset V) (p : ℕ) (hXY : Disjoint X Y) (hcard : X.card+Y.card=p+2)
    (hP : ∀x∈X,¬Contains P.family (Finsupp.single x 1))
    (hQ : ∀x∈X,¬Contains Q.family (Finsupp.single x 1)) :
    P.initialKoszulFactor Q (p+1) (rectangleCoordinate (k := k) P.family X Y p hXY hcard hP)=
      rectangleCoordinate (k := k) Q.family X Y p hXY hcard hQ := by
  let z : Simplicial.Chains (k := k) (quotientKoszulFaces P.family (rectangleFaceDegree X Y))
      (p+1) := ⟨rectangleFaceVector (k := k) X Y,by
        have hh := rectangleFaceVector_chains (k := k) P.family X Y hXY hP
        have hc : X.card+Y.card-1=p+1 := by omega
        simpa only [hc] using hh⟩
  have he := initialKoszulFactor_face P Q (rectangleFaceDegree X Y) (p+1) z
  have hp : quotientFaceProjectionBetween (k := k) P.family Q.family (rectangleFaceDegree X Y) (p+1) z=
      ⟨rectangleFaceVector (k := k) X Y,by
        have hh := rectangleFaceVector_chains (k := k) Q.family X Y hXY hQ
        have hc : X.card+Y.card-1=p+1 := by omega
        simpa only [hc] using hh⟩ := by
    apply Subtype.ext
    change quotientFaceProjection (k := k) Q.family (rectangleFaceDegree X Y) (rectangleFaceVector (k := k) X Y)=_
    exact relativeProjection_eq_self (rectangleFaceVector_mem (k := k) Q.family X Y hXY hQ)
  rw [hp] at he
  exact he

end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.GraphRectangleLifts -/
section

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.Universal
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
variable {N : ℕ} {k : Type u} [CommRing k] [IsDomain k]

lemma intervalLabeling_closed {G : SimpleGraph (Fin N)} (hG : IntervalLabeling G) :
    ClosedLabeling G := by
  constructor
  · intro a b c hab hac hbc habG hacG
    rcases lt_or_gt_of_ne hbc with hbc | hcb
    · exact (hG a b c hab hbc hacG).2
    · exact ((hG a c b hac hcb habG).2).symm
  · intro a b c hac hbc hab hacG hbcG
    rcases lt_or_gt_of_ne hab with hab | hba
    · exact (hG a b c hab hbc hacG).1
    · exact ((hG b a c hba hac hbcG).1).symm

def graphQuotientData (G : SimpleGraph (Fin N)) (hG : ClosedLabeling G) :
    QuotientGroebnerData (FiniteVariable.{u} (GraphRows N)) k where
  order := graphLexOrder
  ideal := graphBinomialIdeal G
  generators := graphBinomialGenerators G
  groebner := closedGraph_binomial_groebner hG
  unitLeading := graphBinomialGenerators_unit_leading G
  family := finiteRowFamily (GraphRows N) (graphEdgeLattice G)
  standard := closedGraph_standardMonomials hG

/-- Every canonical rectangle class of an interval-labeled graph has an
actual binomial Koszul cycle with that precise leading cycle. The proof uses
the actual quotient map from its containing clique, so no componentwise
tensor-product assertion about ideals is involved. -/
theorem GraphRectangle.graph_cycle_lift {G : SimpleGraph (Fin N)}
    {A : ∀r,Finset (Fin (GraphRows N r))} (R : GraphRectangle.{u} G A)
    (hG : IntervalLabeling G) (p : ℕ) (hcard : R.X.card+R.Y.card=p+2) :
    let B := finiteRowFamily (GraphRows N) (graphEdgeLattice G)
    let z := rectangleCoordinate (k := k) B R.X R.Y p R.disjoint hcard
      (fun x _ => graphEdgeFamily_no_linear G x)
    ∃y,y∈Grading.Piece (quotientCoefficientBasis (k := k) B (p+1))
      (fun t => Finsupp.weight graphVertexRowDegree (quotientDegree t))
      (Finsupp.weight graphVertexRowDegree R.fineDegree) ∧
      graphOrdinaryQuotientDifferential (k := k) G (intervalLabeling_closed hG) p y=0 ∧
      z-y∈(basisFiltration (quotientCoefficientBasis (k := k) B (p+1))
        (fun t => Finsupp.weight graphDiagonalWeight (quotientDegree t))).level
          (Finsupp.weight graphDiagonalWeight R.fineDegree) := by
  let H := intervalCliqueGraph R.lowerVertex R.upperVertex
  let P : QuotientGroebnerData (FiniteVariable.{u} (GraphRows N)) k :=
    graphQuotientData (k := k) H (intervalCliqueGraph_closed _ _)
  let Q : QuotientGroebnerData (FiniteVariable.{u} (GraphRows N)) k :=
    graphQuotientData (k := k) G (intervalLabeling_closed hG)
  let hPQ : P.ideal≤Q.ideal := R.cliqueIdeal_le hG
  let zP := rectangleCoordinate (k := k) P.family R.X R.Y p R.disjoint hcard
    (fun x _ => graphEdgeFamily_no_linear H x)
  obtain ⟨y,hya,hdy,herr⟩ := R.clique_cycle_lift (k := k) p hcard
  have hzw : zP∈Grading.Piece (quotientCoefficientBasis (k := k) P.family (p+1))
      (fun t => Finsupp.weight graphDiagonalWeight (quotientDegree t))
      (Finsupp.weight graphDiagonalWeight R.fineDegree) :=
    rectangleCoordinate_regraded (Finsupp.weight graphDiagonalWeight) P.family R.X R.Y p
      R.disjoint hcard _
  have hhom : Q.ideal.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule k
        (graphVertexRowDegree : FiniteVariable.{u} (GraphRows N) →
          (Fin N →₀ ℕ) × (Fin 2 →₀ ℕ))) :=
    graphBinomialIdeal_vertexRow_homogeneous (k := k) G
  have hdy' : P.differential p y = 0 := hdy
  have hh := QuotientGroebnerData.koszulFactor_transfers_lift_withNatModule (k := k)
    (V := FiniteVariable.{u} (GraphRows N)) (A := (Fin N →₀ ℕ) × (Fin 2 →₀ ℕ))
    (hNat := (inferInstance : Module ℕ ((Fin N →₀ ℕ) × (Fin 2 →₀ ℕ))))
    (hDec := (inferInstance : DecidableEq ((Fin N →₀ ℕ) × (Fin 2 →₀ ℕ))))
    P Q hPQ graphVertexRowDegree hhom graphDiagonalWeight
    (graphBinomialGenerators_weight_tails (k := k) G) p
    (Finsupp.weight graphDiagonalWeight R.fineDegree)
    (Finsupp.weight graphVertexRowDegree R.fineDegree) zP y hzw hya hdy' herr
  refine ⟨P.koszulFactor Q hPQ (p+1) y,hh.1,hh.2.1,?_⟩
  have he := initialKoszulFactor_rectangle P Q R.X R.Y p R.disjoint hcard
    (fun x _ => graphEdgeFamily_no_linear H x)
    (fun x _ => graphEdgeFamily_no_linear G x)
  have herr' := hh.2.2
  dsimp only [zP] at herr'
  rw [he] at herr'
  exact herr'

end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FilteredBilinear -/
section

section
set_option autoImplicit false
set_option maxHeartbeats 250000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg FourPapers.Universal
variable {R X Y Z I J L : Type*} [CommRing R]
  [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
  [AddCommGroup Z] [Module R Z]

lemma bilinear_mem_of_basis (b : Module.Basis I R X) (c : Module.Basis J R Y)
    (P : I → Prop) (Q : J → Prop) (T : Submodule R Z) (f : X →ₗ[R] Y →ₗ[R] Z)
    (hf : ∀i,P i→∀j,Q j→f (b i) (c j)∈T)
    (x : X) (hx : x∈Submodule.span R (b '' {i | P i}))
    (y : Y) (hy : y∈Submodule.span R (c '' {j | Q j})) : f x y∈T := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,hi,rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j,hj,rfl⟩ := hy
      exact hf i hi j hj
    | zero => simpa only [map_zero] using T.zero_mem
    | add y z hy hz ihy ihz => simpa only [map_add] using T.add_mem ihy ihz
    | smul a y hy ih => simpa only [map_smul] using T.smul_mem a ih
  | zero => simpa only [map_zero,LinearMap.zero_apply] using T.zero_mem
  | add x z hx hz ihx ihz =>
    simpa only [map_add,LinearMap.add_apply] using T.add_mem ihx ihz
  | smul a x hx ih =>
    simpa only [map_smul,LinearMap.smul_apply] using T.smul_mem a ih

lemma bilinear_filtered_mem (b : Module.Basis I R X) (c : Module.Basis J R Y)
    (e : Module.Basis L R Z) (w : I → ℕ) (v : J → ℕ) (u : L → ℕ)
    (f : X →ₗ[R] Y →ₗ[R] Z)
    (hf : ∀i j l,w i+v j<u l→e.repr (f (b i) (c j)) l=0)
    (n m r : ℕ) (hbound : ∀i j,w i<n→v j< m→w i+v j<r)
    (x : X) (hx : x∈(basisFiltration b w).level n)
    (y : Y) (hy : y∈(basisFiltration c v).level m) :
    f x y∈(basisFiltration e u).level r := by
  apply bilinear_mem_of_basis b c (fun i => w i<n) (fun j => v j< m)
    ((basisFiltration e u).level r) f _ x hx y hy
  intro i hi j hj
  rw [basisFiltration_mem]
  intro l hl
  exact hf i j l ((hbound i j hi hj).trans_le hl)

lemma bilinear_strict_filtered_mem (b : Module.Basis I R X) (c : Module.Basis J R Y)
    (e : Module.Basis L R Z) (w : I → ℕ) (v : J → ℕ) (u : L → ℕ)
    (f : X →ₗ[R] Y →ₗ[R] Z)
    (hf : ∀i j l,w i+v j≤u l→e.repr (f (b i) (c j)) l=0)
    (n m r : ℕ) (hbound : ∀i j,w i<n→v j< m→w i+v j≤r)
    (x : X) (hx : x∈(basisFiltration b w).level n)
    (y : Y) (hy : y∈(basisFiltration c v).level m) :
    f x y∈(basisFiltration e u).level r := by
  apply bilinear_mem_of_basis b c (fun i => w i<n) (fun j => v j< m)
    ((basisFiltration e u).level r) f _ x hx y hy
  intro i hi j hj
  rw [basisFiltration_mem]
  intro l hl
  exact hf i j l ((hbound i j hi hj).trans hl)

lemma bilinear_leading_bound (b : Module.Basis I R X) (c : Module.Basis J R Y)
    (e : Module.Basis L R Z) (w : I → ℕ) (v : J → ℕ) (u : L → ℕ)
    (f g : X →ₗ[R] Y →ₗ[R] Z)
    (hg : ∀i j,g (b i) (c j)∈Grading.Piece e u (w i+v j))
    (hc : ∀i j l,w i+v j≤u l→e.repr ((f-g) (b i) (c j)) l=0) :
    ∀i j l,w i+v j<u l→e.repr (f (b i) (c j)) l=0 := by
  intro i j l hlt
  have hz : e.repr (g (b i) (c j)) l=0 := by
    by_contra hn
    have hh := (Grading.mem_piece e u _ _).mp (hg i j) l hn
    omega
  have hh := hc i j l hlt.le
  simpa only [LinearMap.sub_apply,map_sub,Finsupp.sub_apply,hz,sub_zero] using hh

/-- Multiplication of two actual lifts preserves the specified leading
product, including weight-zero edge cases. This finite support argument
does not assume a flat family or a spectral-sequence collapse. -/
theorem bilinear_product_lift (b : Module.Basis I R X) (c : Module.Basis J R Y)
    (e : Module.Basis L R Z) (w : I → ℕ) (v : J → ℕ) (u : L → ℕ)
    (f g : X →ₗ[R] Y →ₗ[R] Z)
    (hg : ∀i j,g (b i) (c j)∈Grading.Piece e u (w i+v j))
    (hc : ∀i j l,w i+v j≤u l→e.repr ((f-g) (b i) (c j)) l=0)
    (a q : ℕ) (x x' : X) (y y' : Y)
    (hx : x∈(basisFiltration b w).level (a+1))
    (hy : y∈(basisFiltration c v).level (q+1))
    (hxx : x-x'∈(basisFiltration b w).level a)
    (hyy : y-y'∈(basisFiltration c v).level q) :
    g x y-f x' y'∈(basisFiltration e u).level (a+q) := by
  have hf := bilinear_leading_bound b c e w v u f g hg hc
  have hx' : x'∈(basisFiltration b w).level (a+1) := by
    have hh := ((basisFiltration b w).level (a+1)).sub_mem hx
      ((basisFiltration b w).mono (Nat.le_succ a) hxx)
    simpa only [sub_sub_cancel] using hh
  have h0 := bilinear_strict_filtered_mem b c e w v u (f-g) hc
    (a+1) (q+1) (a+q) (by intro i j hi hj; omega) x hx y hy
  have h1 := bilinear_filtered_mem b c e w v u f hf
    a (q+1) (a+q) (by intro i j hi hj; omega) (x-x') hxx y hy
  have h2 := bilinear_filtered_mem b c e w v u f hf
    (a+1) q (a+q) (by intro i j hi hj; omega) x' hx' (y-y') hyy
  have he : g x y-f x' y'=f (x-x') y+f x' (y-y')-(f-g) x y := by
    simp only [map_sub,LinearMap.sub_apply]
    abel
  rw [he]
  exact Submodule.sub_mem _ (Submodule.add_mem _ h1 h2) h0

end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.QuotientTensorProduct -/
section

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 300000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open FourPapers.Universal
open scoped TensorProduct
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]
namespace QuotientGroebnerData

abbrev TensorModel (P : QuotientGroebnerData V k) :=
  CoefficientQuotient (k := k) P.family ⊗[k] Simplicial.Ambient V k

abbrev TensorIndex (P : QuotientGroebnerData V k) :=
  {a : Exponent V // QuotientAllowed P.family a} × Finset V

def tensorBasis (P : QuotientGroebnerData V k) : Module.Basis P.TensorIndex k P.TensorModel :=
  (quotientMonomialBasis P.family).tensorProduct Simplicial.basis

def tensorDegree (P : QuotientGroebnerData V k) (t : P.TensorIndex) : Exponent V :=
  t.1.val+faceExponent t.2

def tensorEquiv (P : QuotientGroebnerData V k) :
    P.TensorModel ≃ₗ[k] ((MvPolynomial V k ⧸ P.ideal) ⊗[k] Simplicial.Ambient V k) :=
  TensorProduct.congr P.coefficientEquiv (LinearEquiv.refl k _)

def tensorMul (P : QuotientGroebnerData V k) : P.TensorModel →ₗ[k] P.TensorModel →ₗ[k] P.TensorModel :=
  ((LinearMap.mul k ((MvPolynomial V k ⧸ P.ideal) ⊗[k] Simplicial.Ambient V k)).compl₁₂
    P.tensorEquiv.toLinearMap P.tensorEquiv.toLinearMap).compr₂ P.tensorEquiv.symm.toLinearMap

lemma tensorMul_apply (P : QuotientGroebnerData V k) (x y : P.TensorModel) :
    P.tensorMul x y=P.tensorEquiv.symm (P.tensorEquiv x*P.tensorEquiv y) := rfl

lemma tensorEquiv_basis (P : QuotientGroebnerData V k) (t : P.TensorIndex) :
    P.tensorEquiv (P.tensorBasis t)=
      Ideal.Quotient.mk P.ideal (monomial t.1.val 1) ⊗ₜ[k] Simplicial.basis t.2 := by
  rw [tensorBasis,Module.Basis.tensorProduct_apply']
  simp only [tensorEquiv,TensorProduct.congr_tmul,LinearEquiv.refl_apply,coefficientEquiv,
    groebnerCoefficientEquiv_basis]

lemma tensorMul_basis (P : QuotientGroebnerData V k) (s t : P.TensorIndex) :
    P.tensorMul (P.tensorBasis s) (P.tensorBasis t)=
      P.coefficientEquiv.symm (Ideal.Quotient.mk P.ideal (monomial (s.1.val+t.1.val) 1))
        ⊗ₜ[k] (Simplicial.basis s.2*Simplicial.basis t.2) := by
  rw [tensorMul_apply,tensorEquiv_basis,tensorEquiv_basis,
    Algebra.TensorProduct.tmul_mul_tmul,←map_mul,monomial_mul_monomial,one_mul]
  simp only [tensorEquiv,TensorProduct.congr_symm,TensorProduct.congr_tmul,
    LinearEquiv.refl_symm,LinearEquiv.refl_apply]

lemma tensorInitialMul_basis (P : QuotientGroebnerData V k) (s t : P.TensorIndex) :
    P.tensorBasis s*P.tensorBasis t=
      quotientMonomial P.family (s.1.val+t.1.val) ⊗ₜ[k]
        (Simplicial.basis s.2*Simplicial.basis t.2) := by
  rw [tensorBasis,Module.Basis.tensorProduct_apply',Module.Basis.tensorProduct_apply',
    quotientMonomialBasis_apply,quotientMonomialBasis_apply,Algebra.TensorProduct.tmul_mul_tmul]
  congr 1
  change Ideal.Quotient.mk _ (monomial s.1.val (1:k))*
    Ideal.Quotient.mk _ (monomial t.1.val (1:k))=Ideal.Quotient.mk _ (monomial _ 1)
  rw [←map_mul,monomial_mul_monomial,one_mul]

lemma coefficient_normalForm_correction (P : QuotientGroebnerData V k) (w : V → ℕ)
    (htail : ∀g∈P.generators,g≠0→∀b∈(monomial (P.order.degree g) 1-g).support,
      Finsupp.weight w b<Finsupp.weight w (P.order.degree g))
    (α : Exponent V) (β : {a : Exponent V // QuotientAllowed P.family a})
    (hβα : Finsupp.weight w α≤Finsupp.weight w β.val) :
    (quotientMonomialBasis (k := k) P.family).repr
      (P.coefficientEquiv.symm (Ideal.Quotient.mk P.ideal (monomial α 1))-
        quotientMonomial P.family α) β=0 := by
  by_cases hα : QuotientAllowed P.family α
  · rw [show P.coefficientEquiv.symm (Ideal.Quotient.mk P.ideal (monomial α 1))=
        quotientMonomial P.family α from groebnerCoefficientEquiv_symm_monomial
        P.order P.ideal P.generators P.groebner P.unitLeading P.family P.standard hα,
      sub_self]
    exact congrArg (fun x : {a : Exponent V // QuotientAllowed P.family a} →₀ k => x β)
      (quotientMonomialBasis (k := k) P.family).repr.map_zero
  · rw [quotientMonomial_zero P.family α hα,sub_zero]
    change (quotientMonomialBasis P.family).repr
      ((groebnerCoefficientEquiv P.order P.ideal P.generators P.groebner P.unitLeading
        P.family P.standard).symm (Ideal.Quotient.mk P.ideal (monomial α 1))) β=0
    rw [groebnerCoefficientEquiv_symm_repr]
    by_contra hc
    have hh := groebner_normalForm_strictly_lowers_of_tails P.order P.ideal P.generators
      P.groebner P.unitLeading w htail α (fun h => hα ((P.standard _).mp h))
    exact (not_lt_of_ge hβα) ((mem_restrictSupport_iff k).mp hh (mem_support_iff.mpr hc))

theorem tensorLinearEquiv_unit_smul {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (c : ℤˣ) (x : M) : e (c • x)=c • e x :=
  map_zsmul_unit e.toAddEquiv c x

theorem tensorLinearEquiv_sum {R M N I : Type*} [CommRing R] [Fintype I]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (f : I → M) : e (∑ i, f i)=∑ i, e (f i) :=
  map_sum e.toAddEquiv f Finset.univ

theorem tensorLinearEquiv_zero {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) : e 0=0 := e.map_zero

/-- The actual binomial multiplication differs from monomial quotient
multiplication only by strictly lower total coefficient/exterior weight. -/
theorem tensorMul_basis_strict_correction (P : QuotientGroebnerData V k) (w : V → ℕ)
    (htail : ∀g∈P.generators,g≠0→∀b∈(monomial (P.order.degree g) 1-g).support,
      Finsupp.weight w b<Finsupp.weight w (P.order.degree g))
    (s t u : P.TensorIndex)
    (hweight : Finsupp.weight w (P.tensorDegree s)+Finsupp.weight w (P.tensorDegree t)≤
      Finsupp.weight w (P.tensorDegree u)) :
    P.tensorBasis.repr (P.tensorMul (P.tensorBasis s) (P.tensorBasis t)-
      P.tensorBasis s*P.tensorBasis t) u=0 := by
  rw [tensorMul_basis,tensorInitialMul_basis,←TensorProduct.sub_tmul]
  by_cases hst : Disjoint s.2 t.2
  · rw [faceBasis_mul_of_disjoint _ _ hst,TensorProduct.tmul_smul,
      tensorLinearEquiv_unit_smul (R := k) P.tensorBasis.repr,Finsupp.smul_apply]
    change faceWedgeSign s.2 t.2 hst •
      ((quotientMonomialBasis P.family).tensorProduct (Simplicial.basis (k := k))).repr
        ((_ : CoefficientQuotient (k := k) P.family) ⊗ₜ[k] Simplicial.basis (s.2∪t.2)) u=0
    rw [Module.Basis.tensorProduct_repr_tmul_apply,Module.Basis.repr_self,Finsupp.single_apply]
    by_cases hu : s.2∪t.2=u.2
    · rw [if_pos hu,one_smul]
      have hw : Finsupp.weight w (s.1.val+t.1.val)≤Finsupp.weight w u.1.val := by
        simp only [tensorDegree,map_add,←hu,faceExponent_union_of_disjoint s.2 t.2 hst,
          map_add] at hweight
        rw [map_add]
        omega
      rw [P.coefficient_normalForm_correction w htail _ _ hw,smul_zero]
    · rw [if_neg hu,zero_smul,smul_zero]
  · rw [faceBasis_mul_of_not_disjoint _ _ hst,TensorProduct.tmul_zero]
    exact congrArg (fun x : P.TensorIndex →₀ k => x u) P.tensorBasis.repr.map_zero

lemma tensorInitialMul_basis_homogeneous (P : QuotientGroebnerData V k)
    {A : Type*} [AddCommMonoid A] (deg : V → A) (s t : P.TensorIndex) :
    P.tensorBasis s*P.tensorBasis t∈Grading.Piece P.tensorBasis
      (fun u => Finsupp.weight deg (P.tensorDegree u))
      (Finsupp.weight deg (P.tensorDegree s)+Finsupp.weight deg (P.tensorDegree t)) := by
  rw [tensorInitialMul_basis]
  by_cases hst : Disjoint s.2 t.2
  · rw [faceBasis_mul_of_disjoint _ _ hst,TensorProduct.tmul_smul]
    apply (Submodule.smul_mem_iff' _ (faceWedgeSign s.2 t.2 hst)).mpr
    by_cases ha : QuotientAllowed P.family (s.1.val+t.1.val)
    · let u : P.TensorIndex := (⟨s.1.val+t.1.val,ha⟩,s.2∪t.2)
      have hu := Grading.basis_mem_piece P.tensorBasis
        (fun u => Finsupp.weight deg (P.tensorDegree u)) u
      have hd : Finsupp.weight deg (P.tensorDegree u)=
          Finsupp.weight deg (P.tensorDegree s)+Finsupp.weight deg (P.tensorDegree t) := by
        simp only [tensorDegree,u,faceExponent_union_of_disjoint s.2 t.2 hst,map_add]
        abel
      simpa only [hd,tensorBasis,Module.Basis.tensorProduct_apply',quotientMonomialBasis_apply] using hu
    · rw [quotientMonomial_zero P.family _ ha,TensorProduct.zero_tmul]
      exact Submodule.zero_mem _
  · rw [faceBasis_mul_of_not_disjoint _ _ hst,TensorProduct.tmul_zero]
    exact Submodule.zero_mem _

theorem tensorMul_preserves_leading_product (P : QuotientGroebnerData V k) (w : V → ℕ)
    (htail : ∀g∈P.generators,g≠0→∀b∈(monomial (P.order.degree g) 1-g).support,
      Finsupp.weight w b<Finsupp.weight w (P.order.degree g))
    (a q : ℕ) (x x' y y' : P.TensorModel)
    (hx : x∈(basisFiltration P.tensorBasis (fun t => Finsupp.weight w (P.tensorDegree t))).level (a+1))
    (hy : y∈(basisFiltration P.tensorBasis (fun t => Finsupp.weight w (P.tensorDegree t))).level (q+1))
    (hxx : x-x'∈(basisFiltration P.tensorBasis (fun t => Finsupp.weight w (P.tensorDegree t))).level a)
    (hyy : y-y'∈(basisFiltration P.tensorBasis (fun t => Finsupp.weight w (P.tensorDegree t))).level q) :
    x*y-P.tensorMul x' y'∈
      (basisFiltration P.tensorBasis (fun t => Finsupp.weight w (P.tensorDegree t))).level (a+q) := by
  apply bilinear_product_lift P.tensorBasis P.tensorBasis P.tensorBasis
    (fun t => Finsupp.weight w (P.tensorDegree t))
    (fun t => Finsupp.weight w (P.tensorDegree t))
    (fun t => Finsupp.weight w (P.tensorDegree t)) P.tensorMul (LinearMap.mul k P.TensorModel)
    (P.tensorInitialMul_basis_homogeneous w) _ a q x x' y y' hx hy hxx hyy
  intro s t u hweight
  exact P.tensorMul_basis_strict_correction w htail s t u hweight

end QuotientGroebnerData
end FourPapers.Sublattice
end

end
end


end
