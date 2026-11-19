module

public import Papers.GraphicalZonotopes.PathJoinLatticeDilation
public import Papers.GraphicalZonotopes.BooleanPair
public import Papers.GraphicalZonotopes.ThreeTreeLatticeDilation
public import Papers.GraphicalZonotopes.UnitLatticeDilation

/-! # Corollary 9.4, including both small path cubes and every larger one -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.PathJoin
open Finset SetFunctionEmbedding
open scoped Pointwise

/-- Canonical coordinate relabelling of the actual Appendix B summand. -/
theorem relabelled_summand (n : ℕ) {W : Type*} [Fintype W] [DecidableEq W]
    (e : W ≃ Vertex n) :
    FullLatticeSummandAt ((graph n).comap e) (((n+2)/2 : ℕ) : ℝ) := by
  let f := restrict e.toEmbedding (setFunction n)
  have hext : ExtremeSupermodular f := extreme_restrict_equiv e (extreme n)
  have hi : IntegerValued f := integerValued_restrict e.toEmbedding (integerValued n)
  have hg : Graphical ((graph n).comap e) f := restrict_graphical e.toEmbedding (graphical n)
  let E : ((graph n).comap e) ≃g graph n := {toEquiv := e,map_rel_iff' := by intros;rfl}
  have hconn : ((graph n).comap e).Connected := E.connected_iff.mpr (graph_connected n)
  have hpositive : ∀ u v,((graph n).comap e).Adj u v →
      ∃ S : Finset W,u∉S ∧ v∉S ∧ delta f u v S≠0 := by
    intro u v huv
    obtain ⟨S,hu,hv,hd⟩ := positive_slack (e u) (e v) huv
    refine ⟨S.map e.symm.toEmbedding,by simpa using hu,by simpa using hv,?_⟩
    rw [delta_restrict]
    have hS : (S.map e.symm.toEmbedding).map e.toEmbedding=S := by ext x; simp
    rw [hS]
    exact ne_of_gt hd
  have hb : ∀ u v,u≠v → ((graph n).comap e).Adj u v → ∀ S : Finset W,
      u∉S → v∉S → delta f u v S≤(((n+2)/2 : ℕ) : ℝ) := by
    intro u v huv hadj S hu hv
    rw [delta_restrict]
    exact (slack_bounds (e u) (e v) (fun h => huv (e.injective h)) _
      (by simpa using hu) (by simpa using hv)).2
  refine ⟨basePolytope f,hi.basePolytope hext.1.1 hext.2.1,
    hext.minkowskiIndecomposable,?_,?_⟩
  · exact finrank_vectorSpan_eq_of_connected_slacks hext.1.1 hext.2.1 hconn hpositive
  · exact (isMinkowskiSummand_graphical_iff hext.1.1 hext.2.1 (Nat.cast_nonneg _)).mpr ⟨hg,hb⟩

theorem pathCube_four_unit : FullLatticeSummandAt (Path.graph 4) 1 := by
  have h := relabelled_summand 0 (Equiv.refl (Fin 4))
  have he : (graph 0).comap (Equiv.refl (Fin 4))=Path.graph 4 := by
    ext u v
    fin_cases u <;> fin_cases v <;> decide
  simpa only [he,show ((0+2)/2 : ℕ)=1 by decide,Nat.cast_one] using h

theorem pathCube_five_unit : FullLatticeSummandAt (Path.graph 5) 1 := by
  have h := relabelled_summand 1 (Equiv.swap (0 : Fin 5) 2)
  have he : (graph 1).comap (Equiv.swap (0 : Fin 5) 2)=Path.graph 5 := by
    ext u v
    fin_cases u <;> fin_cases v <;> decide
  simpa only [he,show ((1+2)/2 : ℕ)=1 by decide,Nat.cast_one] using h

/-- The path-cube clause of Corollary 9.4, with its entire stated range. -/
theorem pathCube_least_dilation (n : ℕ) (hn : 4≤n) :
    LeastFullLatticeDilation (Path.graph n) (if n≤5 then 1 else 2) := by
  by_cases hsmall : n≤5
  · have hunit : FullLatticeSummandAt (Path.graph n) 1 := by
      have hc : n=4 ∨ n=5 := by omega
      rcases hc with rfl | rfl
      · exact pathCube_four_unit
      · exact pathCube_five_unit
    rw [if_pos hsmall]
    refine ⟨by norm_num,hunit,?_⟩
    intro a ha hQ
    obtain ⟨Q,hQ,hi,hd,hs⟩ := hQ
    exact UnitLatticeDilation.dilation_at_least_one (by omega) hQ hi.1 hd ha hs
  · rw [if_neg hsmall]
    refine ⟨by norm_num,(threeTree_lattice_dilation_sharp.2 n (by omega)).2,?_⟩
    intro a ha hQ
    obtain ⟨Q,hQ,hi,hd,hs⟩ := hQ
    exact (threeTree_lattice_lower_bound (by omega) (Path.graph_isThreeTree hn) hQ hi hd ha hs).1

/-- Every clause of the paper's Corollary 9.4. -/
theorem corollary_nine_four :
    (∀ m : ℕ,2≤m → LeastFullLatticeDilation (graph (m-2)) ((m/2 : ℕ) : ℝ)) ∧
    (∀ n : ℕ,4≤n → LeastFullLatticeDilation (Path.graph n) (if n≤5 then 1 else 2)) :=
  ⟨paper_path_join,pathCube_least_dilation⟩

end GraphicalZonotopes.PathJoin
