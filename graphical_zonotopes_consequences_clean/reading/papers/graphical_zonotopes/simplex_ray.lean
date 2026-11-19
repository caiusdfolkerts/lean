module

public import Papers.GraphicalZonotopes.ThreeTreeTightKernel

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem setMonomial_translationNormalized {C : Finset V} (hC : 2≤C.card) :
    TranslationNormalized (setMonomial C) := by
  refine ⟨setMonomial_normalized (card_pos.mp (by omega)),?_⟩
  intro v
  have hnot : ¬C⊆{v} := by
    intro hs
    have hc:=card_le_card hs
    simp only [card_singleton] at hc
    omega
  simp only [setMonomial,if_neg hnot]

theorem setMonomial_graphical (C : Finset V) : Graphical (cliqueGraph C) (setMonomial C) := by
  intro u v huv hnon A hu hv
  rw [delta_setMonomial huv hu hv]
  apply if_neg
  rintro ⟨huC,hvC,hsub⟩
  exact hnon ⟨huv,huC,hvC⟩

theorem zeta_single_coefficient (C : Finset V) (a : ℝ) :
    zeta (fun D : Finset V => if D=C then a else 0)=a • setMonomial C := by
  funext A
  by_cases hCA : C⊆A <;> simp [zeta,setMonomial,hCA]

theorem mobius_setMonomial (C : Finset V) :
    mobius (setMonomial C)=(fun D => if D=C then 1 else 0) := by
  have he:=zeta_single_coefficient C 1
  simp only [one_smul] at he
  rw [← he,mobius_zeta]

/-- The simplex ray has its complete normalized tight kernel in every
ambient dimension. The proof retains every proper-subset equation, including
coordinates outside the simplex's support. -/
theorem setMonomial_tight_kernel {C : Finset V} (hC : 2≤C.card)
    (f : SetFunction V) (hn : TranslationNormalized f)
    (hf : ThreeTreeStates.TightVariation (setMonomial C) f) :
    ∃ a : ℝ,f=a • setMonomial C := by
  classical
  have hgraph : Graphical (cliqueGraph C) f := by
    intro u v huv hnon A hu hv
    exact hf u v huv A hu hv (setMonomial_graphical C u v huv hnon A hu hv)
  have hy : CliqueSupported (cliqueGraph C) (mobius f):=
    (mobius_cliqueSupported_iff _ f).mpr ⟨hn,hgraph⟩
  have hzero : ∀ D : Finset V,D≠C → mobius f D=0 := by
    intro D
    refine Finset.strongInductionOn D ?_
    intro D ih
    intro hDC
    by_cases hd0 : D.card=0
    · rw [card_eq_zero.mp hd0]
      exact hy.1
    by_cases hd1 : D.card=1
    · obtain ⟨v,rfl⟩:=card_eq_one.mp hd1
      exact hy.2.1 v
    by_contra hnonzero
    have hd2 : 2≤D.card:=by omega
    have hcl:=hy.clique_of_nonzero hnonzero
    have hDCsub : D⊆C := by
      intro u hu
      obtain ⟨v,hv,hvu⟩:=exists_mem_ne (show 1<D.card by omega) u
      exact (hcl hu hv hvu.symm).2.1
    have hnot : ¬C⊆D:=fun hCD => hDC (subset_antisymm hDCsub hCD)
    obtain ⟨u,huD,v,hvD,huv⟩:=one_lt_card.mp (show 1<D.card by omega)
    let A:=(D.erase u).erase v
    have huA : u∉A:=by simp [A]
    have hvA : v∉A:=by simp [A]
    have he : insert u (insert v A)=D := by
      ext w
      by_cases hwu : w=u <;> by_cases hwv : w=v <;> simp [A,hwu,hwv,huD,hvD]
    have hrow : delta (setMonomial C) u v A=0 := by
      rw [delta_setMonomial huv huA hvA,he]
      simp only [hnot,and_false,ite_false]
    have hvar:=hf u v huv A huA hvA hrow
    rw [← zeta_mobius f,delta_zeta huv huA hvA,he] at hvar
    rw [sum_eq_single D] at hvar
    · exact hnonzero hvar
    · intro B hB hBD
      have hBDsub:=(mem_powerset.mp (mem_filter.mp hB).1)
      apply ih B (Finset.ssubset_iff_subset_ne.mpr ⟨hBDsub,hBD⟩)
      intro hBC
      exact hnot (hBC ▸ hBDsub)
    · intro hDnot
      exact False.elim (hDnot (by simp [huD,hvD]))
  let a:=mobius f C
  have hyEq : mobius f=(fun D => if D=C then a else 0) := by
    funext D
    by_cases hDC : D=C
    · simp only [hDC,ite_true,a]
    · simp only [if_neg hDC,hzero D hDC]
  refine ⟨a,?_⟩
  rw [← zeta_mobius f,hyEq]
  exact zeta_single_coefficient C a

theorem setMonomial_extreme {C : Finset V} (hC : 2≤C.card) :
    ExtremeSupermodular (setMonomial C) := by
  apply extremeSupermodular_of_tightEquations (setMonomial_translationNormalized hC)
    (setMonomial_supermodular C)
  · intro he
    have hx:=congrFun he C
    norm_num [setMonomial] at hx
  · exact setMonomial_tight_kernel hC

end GraphicalZonotopes
