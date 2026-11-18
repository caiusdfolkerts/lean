module

public import Papers.GraphicalZonotopes.SimplexRay
public import Papers.GraphicalZonotopes.AffineDimension

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem ThreeTreeOn.roots_mem {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (W : Submodule ℝ (V → ℝ))
    (hW : ∀ u v,G.Adj u v → basisVector u-basisVector v∈W) :
    ∀ u∈S,∀ v∈S,basisVector u-basisVector v∈W := by
  revert hW
  induction h with
  | tetrahedron C hC =>
    intro hW u hu v hv
    by_cases huv : u=v
    · simp [huv]
    · exact hW u v ⟨huv,hu,hv⟩
  | @attach S G h w hw T hT hTS hcl ih =>
    intro hW u hu v hv
    have hi:=ih (fun u v huv => hW u v (Or.inl huv))
    obtain ⟨a,ha⟩:=card_pos.mp (show 0<T.card by omega)
    have hwa:=hW w a ((attached_vertex_adj_iff h hw hTS a).mpr ha)
    rcases mem_insert.mp hu with huw | huS
    · subst u
      rcases mem_insert.mp hv with hvw | hvS
      · subst v
        simp
      · have hp:=W.add_mem hwa (hi a (hTS ha) v hvS)
        convert hp using 1 <;> module
    · rcases mem_insert.mp hv with hvw | hvS
      · subst v
        have hp:=W.sub_mem (hi u huS a (hTS ha)) hwa
        convert hp using 1 <;> module
      · exact hi u huS v hvS

theorem ThreeTreeOn.eq_cliqueGraph_of_card_four {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (hS : S.card=4) : G=cliqueGraph S := by
  induction h with
  | tetrahedron C hC => rfl
  | @attach S G h w hw T hT hTS hcl ih =>
    have hlo:=h.active_card_ge_four
    rw [card_insert_of_notMem hw] at hS
    omega

namespace ThreeTreeStates

theorem setFunction_fullDimension {n : ℕ} {G : SimpleGraph (Fin n)}
    (h : IsThreeTree G) (s : CompatibleRows G) :
    FullDimension (basePolytope (setFunction h s)) := by
  have hn4 : 4≤n:=by simpa only [card_univ,Fintype.card_fin] using h.active_card_ge_four
  have hn:=(setFunction_normalized_graphical h s).1.1
  have hs:=setFunction_supermodular h s
  unfold FullDimension
  simp only [Fintype.card_fin]
  apply finrank_vectorSpan_eq_of_consecutive_roots (by omega) (basePolytope_nonempty hn hs)
  intro i
  apply h.roots_mem (vectorSpan ℝ (basePolytope (setFunction h s))) _ _ (mem_univ _) _ (mem_univ _)
  intro u v huv
  obtain ⟨A,hu,hv,hpos⟩:=exists_positive_edge_slack h s huv
  exact root_mem_vectorSpan_of_delta_ne_zero hn hs huv.ne hu hv hpos.ne'

end ThreeTreeStates

theorem complete_simplex_fullDimension {n : ℕ} (hn : 2≤n) :
    FullDimension (basePolytope (setMonomial (univ : Finset (Fin n)))) := by
  have hzn:=(setMonomial_translationNormalized (C:=(univ : Finset (Fin n)))
    (by simpa using hn)).1
  have hzs:=setMonomial_supermodular (univ : Finset (Fin n))
  unfold FullDimension
  simp only [Fintype.card_fin]
  apply finrank_vectorSpan_eq_of_consecutive_roots (by omega) (basePolytope_nonempty hzn hzs)
  intro i
  let u : Fin n:=⟨i.val,by omega⟩
  let v : Fin n:=⟨i.val+1,by omega⟩
  have huv : u≠v:=by intro he; have he':=congrArg Fin.val he; dsimp [u,v] at he'; omega
  let A:=(univ.erase u).erase v
  have hu : u∉A:=by simp [A]
  have hv : v∉A:=by simp [A]
  have he : insert u (insert v A)=univ := by
    ext w
    by_cases hwu : w=u <;> by_cases hwv : w=v <;> simp [A,hwu,hwv]
  apply root_mem_vectorSpan_of_delta_ne_zero hzn hzs huv hu hv
  rw [delta_setMonomial huv hu hv,he]
  norm_num

theorem complete_simplex_direction_graph {n : ℕ} (hn : 2≤n) :
    actualDirectionGraph (basePolytope (setMonomial (univ : Finset (Fin n)) ))=
      cliqueGraph (univ : Finset (Fin n)) := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  constructor
  · intro he
    exact ⟨he.1,mem_univ _,mem_univ _⟩
  · intro huv
    let A:=(univ.erase u).erase v
    have hu : u∉A:=by simp [A]
    have hv : v∉A:=by simp [A]
    have he : insert u (insert v A)=univ := by
      ext w
      by_cases hwu : w=u <;> by_cases hwv : w=v <;> simp [A,hwu,hwv]
    apply exposedSegment_of_positive_delta
      (setMonomial_translationNormalized (C:=(univ : Finset (Fin n))) (by simpa using hn)).1
      (setMonomial_supermodular _) huv.1 hu hv
    rw [delta_setMonomial huv.1 hu hv,he]
    norm_num

/-- The complete quantitative existence assertion of Theorem6.1. This is
the actual integral Möbius vector, all graph directions, full affine
dimension, and the literal (n−3)-zonotope summand, for every n≥4. -/
theorem admissible_threeTree_construction {n : ℕ} (hn : 4≤n)
    {G : SimpleGraph (Fin n)} (hG : IsThreeTree G) (hA : Admissible G) :
    ∃ z : SetFunction (Fin n),ExtremeSupermodular z ∧ IntegerValued (mobius z) ∧
      (∀ C∈tetrahedra G,mobius z C=1) ∧
      (∀ T : Finset (Fin n),T.card=3 → G.IsClique T →
        mobius z T=0 ∨ mobius z T= -1 ∨ mobius z T= -2) ∧
      FullDimension (basePolytope z) ∧ actualDirectionGraph (basePolytope z)=G ∧
      IsMinkowskiSummand (basePolytope z) (((n-3 : ℕ) : ℝ) • graphicalZonotope G) := by
  classical
  by_cases hn4 : n=4
  · have hGraph : G=cliqueGraph (univ : Finset (Fin n)):=
      hG.eq_cliqueGraph_of_card_four (by simpa using hn4)
    let z:=setMonomial (univ : Finset (Fin n))
    refine ⟨z,setMonomial_extreme (by simpa using (show 2≤n by omega)),?_,?_,?_,
      complete_simplex_fullDimension (by omega),?_,?_⟩
    · rw [mobius_setMonomial]
      intro C
      by_cases hC : C=univ
      · exact ⟨1,by simp [hC]⟩
      · exact ⟨0,by simp [hC]⟩
    · intro C hC
      rw [hGraph,tetrahedra_cliqueGraph (by simpa using hn4),mem_singleton] at hC
      rw [mobius_setMonomial]
      simp [hC]
    · intro T ht hcl
      left
      rw [mobius_setMonomial]
      have hne : T≠univ := by
        intro he
        have hc:=congrArg Finset.card he
        simp only [ht,card_univ,Fintype.card_fin] at hc
        omega
      simp [hne]
    · rw [hGraph]
      exact complete_simplex_direction_graph (by omega)
    · apply (isMinkowskiSummand_graphical_iff
        (setMonomial_translationNormalized (C:=(univ : Finset (Fin n)))
          (by simpa using (show 2≤n by omega))).1
        (setMonomial_supermodular _) (Nat.cast_nonneg _)).mpr
      refine ⟨by rw [hGraph]; exact setMonomial_graphical _,?_⟩
      intro u v huv hedge A hu hv
      rw [delta_setMonomial huv hu hv]
      have he : (n-3 : ℕ)=1 := by omega
      rw [he]
      split <;> norm_num
  · obtain ⟨s⟩:=ThreeTreeStates.compatibleRows_exists hG hA
    have hm : 2≤(tetrahedra G).card := by
      rw [hG.tetrahedra_card,card_univ,Fintype.card_fin]
      omega
    refine ⟨ThreeTreeStates.setFunction hG s,
      ThreeTreeStates.setFunction_extreme hG s hm,?_,?_,?_,
      ThreeTreeStates.setFunction_fullDimension hG s,
      ThreeTreeStates.setFunction_direction_graph hG s,?_⟩
    · rw [ThreeTreeStates.setFunction_mobius]
      exact ThreeTreeStates.coefficients_integerValued hG s
    · intro C hC
      rw [ThreeTreeStates.setFunction_mobius]
      exact ThreeTreeStates.coefficients_tetrahedron hG s hC
    · intro T ht hcl
      rw [ThreeTreeStates.setFunction_mobius]
      exact ThreeTreeStates.coefficients_triangle_values hG s (mem_triangles.mpr ⟨ht,hcl⟩)
    · simpa only [card_univ,Fintype.card_fin] using ThreeTreeStates.setFunction_actual_summand hG s

end GraphicalZonotopes
