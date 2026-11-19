module

public import Papers.GraphicalZonotopes.BooleanAllDimensions
public import Papers.GraphicalZonotopes.ThreeTreeLatticeDilation

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise

/-- Four actual color classes exclude a five-clique, independently of the
sizes of those classes. -/
theorem cliqueFree_five_of_four_coloring {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} (c : V → Fin 4)
    (hc : ∀ u v,G.Adj u v → c u≠c v) : G.CliqueFree 5 := by
  intro C hC
  have hinj : Set.InjOn c (C : Set V) := by
    intro u hu v hv he
    by_contra hne
    exact hc u v (hC.isClique hu hv hne) he
  have hcard : C.card≤4 := by
    calc
      C.card=(C.image c).card := (card_image_of_injOn hinj).symm
      _≤(univ : Finset (Fin 4)).card := card_le_card (subset_univ _)
      _=4 := by simp
  rw [hC.card_eq] at hcard
  omega

/-- Every vertex cardinality from four through eight has an actual
full-dimensional unit lattice summand of a K5-free graphical zonotope. The
five cases are exactly the bounded branch of the optimal-dilation theorem. -/
theorem unit_lattice_witness_four_to_eight {n : ℕ} (hn : 4≤n) (hn8 : n≤8) :
    ∃ G : SimpleGraph (Fin n),G.CliqueFree 5 ∧ FullLatticeSummandAt G 1 := by
  let a : Fin 4 → ℕ := fun i => if i.val<n-4 then 2 else 1
  have ha : ∀ i,a i=1 ∨ a i=2 := by intro i;dsimp [a];split_ifs <;> simp
  have hc : Fintype.card (Σ i : Fin 4,Fin (a i))=n := by
    change Fintype.card (Σ i : Fin 4, Fin (if i.val < n - 4 then 2 else 1)) = n
    interval_cases n <;> decide
  let e : Fin n ≃ (Σ i : Fin 4,Fin (a i)) := Fintype.equivOfCardEq (by simpa using hc.symm)
  let H := (fourPartite a).comap e
  let D : BooleanPairData (fourPartite a) := by
    simpa only [FourSmallParts.graph_partSizeEquiv] using
      (FourSmallParts.pairData (FourSmallParts.doubledParts a)).relabel
        (FourSmallParts.partSizeEquiv a ha)
  let E : H ≃g fourPartite a := {toEquiv := e,map_rel_iff' := by intros;rfl}
  have hconn : H.Connected := E.connected_iff.mpr
    (FourSmallParts.fourPartite_connected a (fun i => by rcases ha i with h | h <;> omega))
  let D' : BooleanPairData H := D.relabel e
  have hpair := D'.geometric_pair hconn
  refine ⟨H,cliqueFree_five_of_four_coloring (fun v => (e v).1) (by intros;assumption),
    basePolytope D'.left,hpair.1,hpair.2.2.1,hpair.2.2.2.2.1,?_⟩
  refine ⟨basePolytope D'.right,
    basePolytope_compact D'.right_extreme.1.1 D'.right_extreme.2.1,
    basePolytope_convex _,basePolytope_nonempty D'.right_extreme.1.1 D'.right_extreme.2.1,?_⟩
  simpa only [one_smul] using hpair.2.2.2.2.2.2.1

/-- The attainment half of Corollary 9.12, with no restriction on the vertex
count beyond the paper's n≥4 hypothesis. -/
theorem optimal_k5_free_dilation_attained {n : ℕ} (hn : 4≤n) :
    ∃ G : SimpleGraph (Fin n),G.CliqueFree 5 ∧
      FullLatticeSummandAt G (if n≤8 then 1 else 2) := by
  by_cases hn8 : n≤8
  · simpa only [if_pos hn8] using unit_lattice_witness_four_to_eight hn hn8
  · have h := threeTree_lattice_dilation_sharp.2 n (by omega)
    exact ⟨Path.graph n,h.1.cliqueFree_five,by simpa only [if_neg hn8] using h.2⟩

end GraphicalZonotopes
