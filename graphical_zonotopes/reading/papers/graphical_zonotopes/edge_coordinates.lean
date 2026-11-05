module

public import Papers.GraphicalZonotopes.GraphModels
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Unordered graph edges and two-element clique sets are exactly equivalent
coordinate systems, including their finite sums. -/
theorem sym2_toFinset_injective : Function.Injective (Sym2.toFinset : Sym2 V → Finset V) := by
  intro e f he
  apply Sym2.ext
  intro v
  apply Iff.of_eq
  simpa only [Sym2.mem_toFinset] using congrArg (fun C : Finset V => v∈C) he

theorem edgeFamily_eq_image_edgeFinset (G : SimpleGraph V) :
    edgeFamily G=G.edgeFinset.image Sym2.toFinset := by
  classical
  ext C
  constructor
  · intro hC
    obtain ⟨hc,hcl⟩ := (mem_edgeFamily G C).mp hC
    obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hc
    have hadj := (pair_mem_edgeFamily G hab).mp hC
    exact mem_image.mpr ⟨s(a,b),G.mem_edgeFinset.mpr hadj,Sym2.toFinset_mk_eq⟩
  · rintro hC
    obtain ⟨e,he,rfl⟩ := mem_image.mp hC
    obtain ⟨a,b⟩ := e
    rw [Sym2.toFinset_mk_eq]
    have hadj := G.mem_edgeFinset.mp he
    exact (pair_mem_edgeFamily G (G.ne_of_adj hadj)).mpr hadj

theorem sum_edgeFamily_eq (G : SimpleGraph V) (f : Finset V → ℝ) :
    (∑ C∈edgeFamily G,f C)=∑ e∈G.edgeFinset,f e.toFinset := by
  rw [edgeFamily_eq_image_edgeFinset,sum_image]
  exact fun e he d hd h => sym2_toFinset_injective h

end GraphicalZonotopes
