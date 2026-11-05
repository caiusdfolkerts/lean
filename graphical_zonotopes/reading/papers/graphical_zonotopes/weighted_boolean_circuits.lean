module

public import Papers.GraphicalZonotopes.AnchoredBooleanCircuits

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise

/-- Transport of a finite positive integral response circuit to the literal
book vertex type, retaining its integral dilation bound. -/
theorem lattice_book_of_finite_weighted_circuit
    {J : Type*} [Fintype J] [DecidableEq J] {s k : ℕ} (hs : 0<s)
    (F : J → SetFunction (Fin s)) (hF : ∀ j,IsMonotoneBoolean (F j))
    (j₀ : J) (hanchor : ∀ a,Essential (F j₀) a)
    (hbranch : ∀ j,∃ a,Essential (F j) a)
    (w : J → ℤ) (hw : ∀ j,0<w j)
    (hrel : (fun j => (w j : ℝ))∈LinearMap.ker (quotientRelation F))
    (huniq : UniqueIntegrableRelation F (fun j => (w j : ℝ)))
    (hcard : Fintype.card J=k) (M : ℤ) (hM : ∑ j,w j≤M) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(M : ℝ) • graphicalZonotope (cliqueBook s k) := by
  classical
  letI : Nonempty (Fin s) := ⟨⟨0,hs⟩⟩
  letI : Nonempty J := ⟨j₀⟩
  have hk : 0<k := by rw [← hcard]; exact Fintype.card_pos
  let e : Fin k ≃ J := (finCongr hcard.symm).trans (Fintype.equivFin J).symm
  let F' : Fin k → SetFunction (Fin s) := fun i => F (e i)
  let w' : Fin k → ℤ := fun i => w (e i)
  have hc : (essentialSpokeGraph F').Connected := by
    apply essentialSpokeGraph_connected_of_anchor F' (e.symm j₀)
    · intro a
      simpa only [F',e.apply_symm_apply] using hanchor a
    · intro i
      exact hbranch (e i)
  obtain ⟨z,hzn,hzc⟩ := (mem_quotientRelation_ker_iff F _).mp hrel
  have hrel' : (fun i => (w' i : ℝ))∈LinearMap.ker (quotientRelation F') := by
    apply (mem_quotientRelation_ker_iff F' _).mpr
    have hh : Compatible z F (fun j => (w' (e.symm j) : ℝ)) := by
      simpa only [w',e.apply_symm_apply] using hzc
    exact ⟨z,hzn,(compatible_reindex e z F (fun i => (w' i : ℝ))).mpr hh⟩
  have huniq' : UniqueIntegrableRelation F' (fun i => (w' i : ℝ)) := by
    intro t ht
    obtain ⟨u,hun,huc⟩ := ht
    have hold : Compatible u F (fun j => t (e.symm j)) :=
      (compatible_reindex e u F t).mp huc
    obtain ⟨c,hc'⟩ := huniq (fun j => t (e.symm j)) ⟨u,hun,hold⟩
    refine ⟨c,?_⟩
    funext i
    simpa only [e.symm_apply_apply,Pi.smul_apply,w'] using congrFun hc' (e i)
  apply lattice_book_of_weighted_modules hk F' (fun i => hF (e i)) w'
    (fun i => hw (e i)) hc hrel' huniq' M
  change (∑ i : Fin k,w (e i))≤M
  rw [e.sum_comp]
  exact hM

end BooleanModule
end GraphicalZonotopes
