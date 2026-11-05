module

public import Papers.GraphicalZonotopes.WeightedBooleanCircuits
public import Papers.GraphicalZonotopes.ActualDirectionsFromSlacks
public import Mathlib.Order.Sum.Order

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.BooleanModule
open Finset
open scoped BigOperators

variable {H J : Type*} [Fintype H] [LinearOrder H] [Fintype J] [LinearOrder J]

local instance sumOrder : LinearOrder (H⊕J) := inferInstanceAs (LinearOrder (H⊕ₗJ))
local instance sumDecidableEq : DecidableEq (H⊕J) := (sumOrder (H:=H) (J:=J)).toDecidableEq

theorem assembled_actual_spoke_iff {z : SetFunction H} (hz : TranslationNormalized z)
    {F : J → SetFunction H} (hF : ∀ j,IsMonotoneBoolean (F j))
    {w : J → ℝ} (hw : ∀ j,0<w j) (hc : Compatible z F w)
    (scope : J → Finset H) (hessential : ∀ j a,a∈scope j → Essential (F j) a)
    (hignore : ∀ j a,a∉scope j → ∀ X,F j (insert a X)=F j X) (a : H) (j : J) :
    ActualRootEdge (basePolytope (assembled z F w)) (Sum.inl a) (Sum.inr j) ↔ a∈scope j := by
  have hn := assembled_normalized hz F hF w
  have hs := assembled_supermodular z F hF w (fun j => (hw j).le) hc
  rw [actualRootEdge_iff_nonzero_elemental hn.1 hs]
  constructor
  · rintro ⟨hne,X,ha,hj,hd⟩
    by_contra hn
    rw [delta_assembled_spoke _ _ _ _ _ _ hj,hignore j a hn,sub_self,mul_zero] at hd
    exact hd rfl
  · intro ha
    obtain ⟨X,hu,hj,hd⟩ := essential_spoke_slack (z:=z) (F:=F)
      (a:=Sum.inl a) (b:=Sum.inr j) hw (hessential j a ha)
    exact ⟨Sum.inl_ne_inr,X,hu,hj,hd⟩

/-- A finite integral circuit with explicit essential-variable sets gives a
literal clique-book polytope with exactly the specified active spokes. -/
theorem scoped_book_of_finite_circuit
    {J : Type*} [Fintype J] [DecidableEq J] {s k : ℕ} (hs : 0<s)
    (F : J → SetFunction (Fin s)) (hF : ∀ j,IsMonotoneBoolean (F j))
    (scope : J → Finset (Fin s))
    (hessential : ∀ j a,a∈scope j → Essential (F j) a)
    (hignore : ∀ j a,a∉scope j → ∀ X,F j (insert a X)=F j X)
    (j₀ : J) (hanchor : scope j₀=univ) (hbranch : ∀ j,(scope j).Nonempty)
    (w : J → ℤ) (hw : ∀ j,0<w j)
    (hrel : (fun j => (w j : ℝ))∈LinearMap.ker (quotientRelation F))
    (huniq : UniqueIntegrableRelation F (fun j => (w j : ℝ)))
    (hcard : Fintype.card J=k) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      LatticePolytope (basePolytope f) ∧
      ∀ a : Fin s,(univ.filter (fun j : Fin k =>
        ActualRootEdge (basePolytope f) (Sum.inl a) (Sum.inr j))).card=
        (univ.filter (fun j : J => a∈scope j)).card := by
  classical
  letI : Nonempty (Fin s) := ⟨⟨0,hs⟩⟩
  letI : Nonempty J := ⟨j₀⟩
  have hk : 0<k := by rw [←hcard]; exact Fintype.card_pos
  let e : Fin k ≃ J := (finCongr hcard.symm).trans (Fintype.equivFin J).symm
  let F' : Fin k → SetFunction (Fin s) := fun i => F (e i)
  let w' : Fin k → ℤ := fun i => w (e i)
  let C' : Fin k → Finset (Fin s) := fun i => scope (e i)
  have hc : (essentialSpokeGraph F').Connected := by
    apply essentialSpokeGraph_connected_of_anchor F' (e.symm j₀)
    · intro a
      apply hessential
      simp only [e.apply_symm_apply,hanchor,mem_univ]
    · intro i
      obtain ⟨a,ha⟩ := hbranch (e i)
      exact ⟨a,hessential (e i) a ha⟩
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
  obtain ⟨u,hun,hui,huc⟩ := integral_compatible_lift F' (fun i => hF (e i)) w' hrel'
  have hw' : ∀ i,0<(w' i : ℝ) := fun i => by exact_mod_cast hw (e i)
  let f := assembled u F' (fun i => (w' i : ℝ))
  have hfn := assembled_normalized hun F' (fun i => hF (e i)) (fun i => (w' i : ℝ))
  have hfi := assembled_integerValued hui F' (fun i => hF (e i)) w'
  have hfe := positive_circuit_extreme hun (fun i => hF (e i))
    (fun i => (hw' i).le) ⟨⟨0,hk⟩,ne_of_gt (hw' ⟨0,hk⟩)⟩ huc huniq'
  refine ⟨f,hfn,hfi,hfe,assembled_graphical u F' _,
    assembled_fullDimension hun (fun i => hF (e i)) hw' huc hc,
    hfi.basePolytope hfn.1 hfe.2.1,?_⟩
  intro a
  have hedge : ∀ i : Fin k,ActualRootEdge (basePolytope f) (Sum.inl a) (Sum.inr i) ↔ a∈scope (e i) := by
    intro i
    exact assembled_actual_spoke_iff hun (fun i => hF (e i)) hw' huc C'
      (fun j a ha => hessential (e j) a ha) (fun j a ha => hignore (e j) a ha) a i
  apply card_bij (fun i _ => e i)
  · intro i hi
    simp only [mem_filter,mem_univ,true_and] at hi ⊢
    exact (hedge i).mp hi
  · intro i hi j hj he
    exact e.injective he
  · intro j hj
    refine ⟨e.symm j,?_,e.apply_symm_apply j⟩
    simp only [mem_filter,mem_univ,true_and] at hj ⊢
    apply (hedge _).mpr
    simpa only [e.apply_symm_apply] using hj

end GraphicalZonotopes.BooleanModule
