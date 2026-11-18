module

public import Papers.GraphicalZonotopes.ThreeTreeFactorization
public import Papers.GraphicalZonotopes.ThreeTreeMaximal
public import Papers.GraphicalZonotopes.SummandEdges
public import Papers.GraphicalZonotopes.GraphDefinitions

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace ThreeTreeStates
open Finset
open RootedResponse
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

def contextBits (A : Finset V) (w : V) : Bool := decide (w∈A)

theorem booleanSupport_contextBits (A : Finset V) :
    booleanSupport (fun w => realBit (contextBits A w))=A := by
  ext w
  by_cases hw : w∈A <;> simp [booleanSupport,contextBits,realBit,hw]

theorem elemental_factorization_context {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v)
    (A : Finset V) (hu : u∉A) (hv : v∉A) :
    delta (setFunction h s) u v A=
      ∑ C : IncidentPairClique G {u,v},pairFactor G s {u,v} (by simp [huv.ne]) C
        (fun w => realBit (contextBits A w)) := by
  simpa only [booleanSupport_contextBits,erase_eq_of_notMem hu,erase_eq_of_notMem hv]
    using elemental_factorization h s huv (contextBits A)

theorem elemental_bounds_incident {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v)
    (A : Finset V) (hu : u∉A) (hv : v∉A) :
    0≤delta (setFunction h s) u v A ∧
      delta (setFunction h s) u v A≤(Fintype.card (IncidentPairClique G {u,v}) : ℝ) := by
  rw [elemental_factorization_context h s huv A hu hv]
  constructor
  · apply sum_nonneg
    intro C hC
    rcases pairFactor_zero_or_one G s {u,v} (by simp [huv.ne]) C (contextBits A)
      with he | he <;> simp only [he] <;> norm_num
  · calc
      _≤∑ _ : IncidentPairClique G {u,v},(1 : ℝ) := by
        apply sum_le_sum
        intro C hC
        rcases pairFactor_zero_or_one G s {u,v} (by simp [huv.ne]) C (contextBits A)
          with he | he <;> simp only [he] <;> norm_num
      _=_ := by simp

theorem incidentPairClique_card_le {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (E : Finset V) :
    Fintype.card (IncidentPairClique G E)≤S.card-3 := by
  calc
    _≤Fintype.card ↥(tetrahedra G) :=
      Fintype.card_le_of_injective (fun C => C.1) (fun C D he => Subtype.ext he)
    _=S.card-3 := by rw [Fintype.card_coe,h.tetrahedra_card]

/-- The original unbounded graph, with all of its conditioning sets,
satisfies the full supermodular inequalities. No subset of rows is used. -/
theorem setFunction_supermodular {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) : Supermodular (setFunction h s) := by
  apply ElementallyNonnegative.supermodular
  intro u v huv A hu hv
  by_cases hedge : G.Adj u v
  · exact (elemental_bounds_incident h s hedge A hu hv).1
  · rw [(setFunction_normalized_graphical h s).2 u v huv hedge A hu hv]

theorem elemental_bound {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v)
    (A : Finset V) (hu : u∉A) (hv : v∉A) :
    delta (setFunction h s) u v A≤((S.card-3 : ℕ) : ℝ) := by
  apply (elemental_bounds_incident h s huv A hu hv).2.trans
  exact_mod_cast incidentPairClique_card_le h ({u,v} : Finset V)

theorem setFunction_lattice {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) : LatticePolytope (basePolytope (setFunction h s)) :=
  (setFunction_integerValued h s).basePolytope (setFunction_normalized_graphical h s).1.1
    (setFunction_supermodular h s)

/-- The construction is an actual summand of the stated dilation of the
ordinary graphical zonotope, including its compact convex complement. -/
theorem setFunction_actual_summand {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) :
    IsMinkowskiSummand (basePolytope (setFunction h s))
      (((S.card-3 : ℕ) : ℝ) • graphicalZonotope G) := by
  apply (isMinkowskiSummand_graphical_iff (setFunction_normalized_graphical h s).1.1
    (setFunction_supermodular h s) (Nat.cast_nonneg _)).mpr
  exact ⟨(setFunction_normalized_graphical h s).2,
    fun u v huv hedge A hu hv => elemental_bound h s hedge A hu hv⟩

/-- A coefficient-one tetrahedron forces a nonzero elemental row at each
of its edges. Nonnegativity then makes that row strictly positive. -/
theorem exists_positive_edge_slack {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v) :
    ∃ A : Finset V,u∉A ∧ v∉A ∧ 0<delta (setFunction h s) u v A := by
  classical
  by_contra hn
  push_neg at hn
  have hz : ∀ A : Finset V,u∉A → v∉A → delta (setFunction h s) u v A=0 := by
    intro A hu hv
    exact le_antisymm (hn A hu hv) ((setFunction_supermodular h s).elemental u v huv.ne A hu hv)
  have hy := (nonedge_coefficients_zero_iff (coefficients h s) huv.ne).mp hz
  obtain ⟨C,hC,hEC⟩ := h.clique_extends
    (C:=({u,v} : Finset V)) (by
      simpa only [insert_subset_iff,singleton_subset_iff] using h.edges_supported huv)
    (((mem_edgeFamily G {u,v}).mp ((pair_mem_edgeFamily G huv.ne).mpr huv)).2)
  have hc:=hy C (hEC (by simp)) (hEC (by simp))
  rw [coefficients_tetrahedron h s hC] at hc
  norm_num at hc

theorem setFunction_direction_graph {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) :
    actualDirectionGraph (basePolytope (setFunction h s))=G := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  constructor
  · intro he
    obtain ⟨R,hR,hRc,hnR,hadd⟩:=setFunction_actual_summand h s
    exact basePolytope_summand_actualRootEdge (setFunction_normalized_graphical h s).1.1
      (setFunction_supermodular h s) G (Nat.cast_nonneg _) R hadd he
  · intro huv
    obtain ⟨A,hu,hv,hpos⟩:=exists_positive_edge_slack h s huv
    exact exposedSegment_of_positive_delta (setFunction_normalized_graphical h s).1.1
      (setFunction_supermodular h s) huv.ne hu hv hpos

end ThreeTreeStates
end GraphicalZonotopes
