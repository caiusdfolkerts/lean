module

public import Papers.GraphicalZonotopes.EdgeCoordinates
public import Papers.GraphicalZonotopes.ForestOscillation
public import Papers.GraphicalZonotopes.Mobius
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The complete degree-two expansion, retaining arbitrary constant and
linear coefficients. This is a finite identity, valid on every ground set. -/
theorem zeta_degree_two (g : SetFunction V)
    (hdegree : ∀ C : Finset V,2<C.card → g C=0) (S : Finset V) :
    zeta g S=g ∅+(∑ v∈S,g {v})+∑ C∈S.powersetCard 2,g C := by
  let N:=max (S.card+1) 3
  let F : ℕ → ℝ := fun j => ∑ C∈S.powersetCard j,g C
  have hlarge : ∑ j∈range (S.card+1),F j=∑ j∈range N,F j := by
    apply sum_subset (range_mono (le_max_left _ _))
    intro j hj hsmall
    have hcard : S.card<j := by
      have hn : ¬j<S.card+1 := by simpa only [mem_range] using hsmall
      omega
    simp only [F,(powersetCard_eq_empty.mpr hcard),sum_empty]
  have hshort : ∑ j∈range 3,F j=∑ j∈range N,F j := by
    apply sum_subset (range_mono (le_max_right _ _))
    intro j hj hsmall
    have hthree : 3≤j := by simpa only [mem_range,not_lt] using hsmall
    apply sum_eq_zero
    intro C hC
    exact hdegree C (by have hc:=(mem_powersetCard.mp hC).2; omega)
  unfold zeta
  rw [sum_powerset,hlarge,← hshort]
  simp only [F,sum_range_succ,sum_range_zero,zero_add,powersetCard_zero,
    sum_singleton,powersetCard_one,sum_map] <;> rfl

/-- The actual interaction graph can omit every pair whose coefficient is
zero; no additional equality is imposed on the linear or constant terms. -/
theorem zeta_degree_two_on_graph (G : SimpleGraph V) (g : SetFunction V)
    (hdegree : ∀ C : Finset V,2<C.card → g C=0)
    (hgraph : ∀ C : Finset V,C.card=2 → C∉edgeFamily G → g C=0)
    (S : Finset V) :
    zeta g S=g ∅+(∑ v∈S,g {v})+
      ∑ e∈G.edgeFinset,if e.toFinset⊆S then g e.toFinset else 0 := by
  rw [zeta_degree_two g hdegree S]
  congr 1
  have hp : (edgeFamily G).filter (fun C => C⊆S)⊆S.powersetCard 2 := by
    intro C hC
    obtain ⟨hC,hCS⟩ := mem_filter.mp hC
    exact mem_powersetCard.mpr ⟨hCS,((mem_edgeFamily G C).mp hC).1⟩
  have he : (∑ C∈(edgeFamily G).filter (fun C => C⊆S),g C)=
      ∑ C∈S.powersetCard 2,g C := by
    apply sum_subset hp
    intro C hC hnot
    have hCS := (mem_powersetCard.mp hC).1
    apply hgraph C (mem_powersetCard.mp hC).2
    intro hedge
    exact hnot (mem_filter.mpr ⟨hedge,hCS⟩)
  rw [← he,sum_filter,sum_edgeFamily_eq]

def booleanSupport (x : V → ℝ) : Finset V := by
  classical
  exact univ.filter (fun v => x v=1)

@[simp] theorem mem_booleanSupport (x : V → ℝ) (v : V) :
    v∈booleanSupport x ↔ x v=1 := by
  classical
  simp [booleanSupport]

theorem zeta_eq_boolean_quadratic (G : SimpleGraph V) (g : SetFunction V)
    (hdegree : ∀ C : Finset V,2<C.card → g C=0)
    (hgraph : ∀ C : Finset V,C.card=2 → C∉edgeFamily G → g C=0)
    (x : V → ℝ) (hx : ∀ v,x v=0 ∨ x v=1) :
    zeta g (booleanSupport x)=ForestSigns.quadratic G (g ∅)
      (fun v => g {v}) (fun e => g e.toFinset) x := by
  classical
  rw [zeta_degree_two_on_graph G g hdegree hgraph]
  unfold ForestSigns.quadratic
  have hlinear : (∑ v∈booleanSupport x,g {v})=∑ v,g {v}*x v := by
    rw [booleanSupport,sum_filter]
    apply sum_congr rfl
    intro v hv
    rcases hx v with he | he <;> simp [he]
  have hquad : (∑ e∈G.edgeFinset,if e.toFinset⊆booleanSupport x then g e.toFinset else 0)=
      ∑ e∈G.edgeFinset,g e.toFinset*ForestSigns.edgeProduct x e := by
    apply sum_congr rfl
    intro e he
    obtain ⟨a,b⟩ := e
    rw [Sym2.toFinset_mk_eq,ForestSigns.edgeProduct_pair]
    rcases hx a with ha | ha <;> rcases hx b with hb | hb <;>
      simp [Finset.insert_subset_iff,Finset.singleton_subset_iff,ha,hb]
  rw [hlinear,hquad]

end GraphicalZonotopes
