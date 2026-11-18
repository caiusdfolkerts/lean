module

public import Papers.GraphicalZonotopes.ThreeTreeLink
public import Papers.GraphicalZonotopes.QuadraticSetFunctions
public import Papers.GraphicalZonotopes.GraphicalCone

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem CliqueSupported.clique_of_nonzero {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y) {C : Finset V} (hC : y C≠0) : G.IsClique C := by
  intro u hu v hv huv
  by_contra hnot
  exact hC (hy.2.2 C u v hu hv huv hnot)

/-- Möbius coefficients of an elemental row, with its two endpoint variables
removed. The discarded coordinates are explicitly zero, not quotiented out. -/
def edgeCoefficients (y : SetFunction V) (u v : V) : SetFunction V := fun C =>
  if u∉C ∧ v∉C then y (insert u (insert v C)) else 0

theorem edgeCoefficients_degree_two {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y)
    (hfour : ∀ C : Finset V,G.IsClique C → C.card≤4)
    {u v : V} (huv : u≠v) (C : Finset V) (hC : 2<C.card) :
    edgeCoefficients y u v C=0 := by
  classical
  by_cases he : u∉C ∧ v∉C
  · rw [edgeCoefficients,if_pos he]
    by_contra hnonzero
    have hbound := hfour _ (hy.clique_of_nonzero hnonzero)
    rw [card_insert_of_notMem (by simp [huv,he.1]),card_insert_of_notMem he.2] at hbound
    omega
  · simp [edgeCoefficients,he]

theorem edgeCoefficients_graph {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y) {u v : V} (huv : u≠v)
    (C : Finset V) (hC : C.card=2) (hnot : C∉edgeFamily (edgeLink G u v)) :
    edgeCoefficients y u v C=0 := by
  classical
  by_cases he : u∉C ∧ v∉C
  · rw [edgeCoefficients,if_pos he]
    by_contra hn
    have hcl := hy.clique_of_nonzero hn
    obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hC
    have hua : u≠a := fun h => he.1 (by simp [h])
    have hub : u≠b := fun h => he.1 (by simp [h])
    have hva : v≠a := fun h => he.2 (by simp [h])
    have hvb : v≠b := fun h => he.2 (by simp [h])
    apply hnot
    apply (pair_mem_edgeFamily (edgeLink G u v) hab).mpr
    exact ⟨hcl (by simp) (by simp) hab,
      hcl (by simp) (by simp) hua,hcl (by simp) (by simp) hva,
      hcl (by simp) (by simp) hub,hcl (by simp) (by simp) hvb⟩
  · simp [edgeCoefficients,he]

theorem zeta_erase_of_containing_zero (g : SetFunction V) (u : V)
    (hz : ∀ C : Finset V,u∈C → g C=0) (S : Finset V) :
    zeta g S=zeta g (S.erase u) := by
  classical
  symm
  apply sum_subset (powerset_mono.mpr (erase_subset _ _))
  intro C hC hnot
  apply hz C
  by_contra hu
  apply hnot
  apply mem_powerset.mpr
  intro v hv
  exact mem_erase.mpr ⟨fun he => hu (he ▸ hv),(mem_powerset.mp hC) hv⟩

theorem edgeCoefficients_zeta {y : SetFunction V} {u v : V} (huv : u≠v)
    {S : Finset V} (hu : u∉S) (hv : v∉S) :
    zeta (edgeCoefficients y u v) S=delta (zeta y) u v S := by
  classical
  rw [delta_zeta huv hu hv]
  apply sum_bij (fun C _ => insert u (insert v C))
  · intro C hC
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr (insert_subset_insert _
      (insert_subset_insert _ (mem_powerset.mp hC))),by simp⟩
  · intro C hC D hD he
    have huC : u∉C := notMem_mono (mem_powerset.mp hC) hu
    have hvC : v∉C := notMem_mono (mem_powerset.mp hC) hv
    have huD : u∉D := notMem_mono (mem_powerset.mp hD) hu
    have hvD : v∉D := notMem_mono (mem_powerset.mp hD) hv
    have hh:=congrArg (fun A : Finset V => (A.erase u).erase v) he
    simpa [huv,huC,hvC,huD,hvD] using hh
  · intro D hD
    obtain ⟨hsub,huD,hvD⟩ := mem_filter.mp hD
    refine ⟨(D.erase u).erase v,?_,?_⟩
    · apply mem_powerset.mpr
      intro w hw
      have hwD := mem_of_mem_erase (mem_of_mem_erase hw)
      have hwu := ne_of_mem_erase (mem_of_mem_erase hw)
      have hwv := ne_of_mem_erase hw
      have hm := (mem_powerset.mp hsub) hwD
      simpa only [mem_insert,hwu,hwv,false_or] using hm
    · ext w
      by_cases hwu : w=u <;> by_cases hwv : w=v <;> simp [hwu,hwv,huD,hvD]
  · intro C hC
    have huC : u∉C := notMem_mono (mem_powerset.mp hC) hu
    have hvC : v∉C := notMem_mono (mem_powerset.mp hC) hv
    simp [edgeCoefficients,huC,hvC]

/-- Every elemental row of four-clique-supported data is the literal
quadratic Boolean polynomial on the common-neighbor graph. -/
theorem edgeCoefficients_boolean_quadratic {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y)
    (hfour : ∀ C : Finset V,G.IsClique C → C.card≤4)
    {u v : V} (huv : u≠v) (x : V → ℝ) (hx : ∀ w,x w=0 ∨ x w=1) :
    ForestSigns.quadratic (edgeLink G u v) (edgeCoefficients y u v ∅)
      (fun w => edgeCoefficients y u v {w})
      (fun e => edgeCoefficients y u v e.toFinset) x=
      delta (zeta y) u v (((booleanSupport x).erase u).erase v) := by
  rw [← zeta_eq_boolean_quadratic (edgeLink G u v) (edgeCoefficients y u v)
    (edgeCoefficients_degree_two hy hfour huv) (edgeCoefficients_graph hy huv) x hx]
  rw [zeta_erase_of_containing_zero _ u (by
    intro C hC; simp [edgeCoefficients,hC])]
  rw [zeta_erase_of_containing_zero _ v (by
    intro C hC; simp [edgeCoefficients,hC])]
  exact edgeCoefficients_zeta huv (by simp) (by simp)

end GraphicalZonotopes
