module

public import Papers.GraphicalZonotopes.TreewidthDefinition

/-! # A degree consequence of an ordinary tree decomposition

The proof prunes redundant leaf bags. A vertex exclusive to a leaf bag has
all its neighbors in that bag. This is the standard degeneracy consequence
of bounded treewidth, with the full connected-occurrence condition used.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem tree_bags_have_low_degree [Nonempty V] (G : SimpleGraph V) (w : ℕ)
    {I : Type} [Fintype I] [DecidableEq I] (T : SimpleGraph I) (bag : I → Finset V)
    (hT : T.IsTree) (hsize : ∀ i, (bag i).card ≤ w+1)
    (hcover : ∀ v, ∃ i, v ∈ bag i)
    (hedge : ∀ u v, G.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i)
    (hconn : ∀ v, (T.induce {i | v ∈ bag i}).Connected) :
    ∃ v : V, G.degree v ≤ w := by
  classical
  have single (I : Type) [Fintype I] [DecidableEq I] (bag : I → Finset V)
      (hs : ∀ i, (bag i).card ≤ w+1)
      (he : ∀ u v, G.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i)
      (r : I) (v : V) (hv : v ∈ bag r)
      (honly : ∀ i, v ∈ bag i → i = r) : ∃ v : V, G.degree v ≤ w := by
    refine ⟨v,?_⟩
    have hsub : G.neighborFinset v ⊆ (bag r).erase v := by
      intro u hu
      have hAdj := (G.mem_neighborFinset v u).mp hu
      obtain ⟨i,hvi,hui⟩ := he v u hAdj
      have hir := honly i hvi
      subst i
      exact mem_erase.mpr ⟨hAdj.ne.symm,hui⟩
    have hc := card_le_card hsub
    rw [SimpleGraph.card_neighborFinset_eq_degree,card_erase_of_mem hv] at hc
    have hb := hs r
    omega
  suffices aux : ∀ n : ℕ, ∀ (J : Type) [Fintype J] [DecidableEq J],
      Fintype.card J = n → ∀ (H : SimpleGraph J) (b : J → Finset V),
      H.IsTree → (∀ i, (b i).card ≤ w+1) →
      (∀ v, ∃ i, v ∈ b i) →
      (∀ u v, G.Adj u v → ∃ i, u ∈ b i ∧ v ∈ b i) →
      (∀ v, (H.induce {i | v ∈ b i}).Connected) → ∃ v : V, G.degree v ≤ w from
    aux _ I rfl T bag hT hsize hcover hedge hconn
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro J _ _ hcard H b htree hs hc he hcon
    by_cases hsub : Subsingleton J
    · letI : Subsingleton J := hsub
      obtain ⟨r⟩ := htree.connected.nonempty
      let v : V := Classical.choice inferInstance
      have hv : v ∈ b r := by
        obtain ⟨i,hi⟩ := hc v
        simpa only [Subsingleton.elim i r] using hi
      exact single J b hs he r v hv (fun i _ => Subsingleton.elim _ _)
    · letI : Nontrivial J := not_subsingleton_iff_nontrivial.mp hsub
      obtain ⟨r,hrdeg⟩ := htree.exists_vert_degree_one_of_nontrivial
      obtain ⟨q,hrq,hqonly⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hrdeg
      have hqr : q ≠ r := hrq.ne.symm
      by_cases hleaf : b r ⊆ b q
      · let J' := {i : J // i ≠ r}
        let H' : SimpleGraph J' := H.induce {r}ᶜ
        let b' : J' → Finset V := fun i => b i.1
        have htree' : H'.IsTree :=
          ⟨htree.connected.induce_compl_singleton_of_degree_eq_one hrdeg,
            htree.isAcyclic.induce _⟩
        have hc' : ∀ v, ∃ i : J', v ∈ b' i := by
          intro v
          obtain ⟨i,hi⟩ := hc v
          by_cases hir : i = r
          · subst i
            exact ⟨⟨q,hqr⟩,hleaf hi⟩
          · exact ⟨⟨i,hir⟩,hi⟩
        have he' : ∀ u v, G.Adj u v → ∃ i : J', u ∈ b' i ∧ v ∈ b' i := by
          intro u v huv
          obtain ⟨i,hu,hv⟩ := he u v huv
          by_cases hir : i = r
          · subst i
            exact ⟨⟨q,hqr⟩,hleaf hu,hleaf hv⟩
          · exact ⟨⟨i,hir⟩,hu,hv⟩
        have hcon' : ∀ v, (H'.induce {i | v ∈ b' i}).Connected := by
          intro v
          let K := H.induce {i | v ∈ b i}
          let S : Set {i : J // v ∈ b i} := {i | i.1 ≠ r}
          have hpre : (K.induce S).Preconnected := by
            apply (hcon v).preconnected.induce_of_degree_eq_one
            intro i hi
            have hir : i.1 = r := by
              by_contra hne
              exact hi hne
            intro j hj k hk
            apply Subtype.ext
            have hj' : H.Adj i.1 j.1 := hj
            have hk' : H.Adj i.1 k.1 := hk
            have hjq : j.1 = q := hqonly j.1 (by simpa only [hir] using hj')
            have hkq : k.1 = q := hqonly k.1 (by simpa only [hir] using hk')
            exact hjq.trans hkq.symm
          let e : (H'.induce {i | v ∈ b' i}) ≃g (K.induce S) :=
            { toFun := fun i => ⟨⟨i.1.1,i.2⟩,i.1.2⟩
              invFun := fun i => ⟨⟨i.1.1,i.2⟩,i.1.2⟩
              left_inv := by intro i; rfl
              right_inv := by intro i; rfl
              map_rel_iff' := by intro i j; rfl }
          have hpre' := e.preconnected_iff.mpr hpre
          obtain ⟨i,hi⟩ := hc' v
          letI : Nonempty ({i : J' | v ∈ b' i} : Set J') := ⟨⟨i,hi⟩⟩
          exact ⟨hpre'⟩
        have hlt : Fintype.card J' < n := by
          rw [← hcard]
          exact Fintype.card_subtype_lt (x := r) (by simp)
        exact ih _ hlt J' rfl H' b' htree' (fun i => hs i.1) hc' he' hcon'
      · obtain ⟨v,hvr,hvq⟩ := not_subset.mp hleaf
        apply single J b hs he r v hvr
        intro i hvi
        by_contra hir
        let r' : {i : J // v ∈ b i} := ⟨r,hvr⟩
        let i' : {i : J // v ∈ b i} := ⟨i,hvi⟩
        have hri : r' ≠ i' := fun hh => hir (congrArg Subtype.val hh).symm
        obtain ⟨j,hj⟩ := ((hcon v) r' i').nonempty_neighborSet_left hri
        have hjq : j.1 = q := hqonly j.1 hj
        exact hvq (hjq ▸ j.2)

theorem HasTreewidthAtMost.exists_degree_le {G : SimpleGraph V} [Nonempty V] {w : ℕ}
    (h : HasTreewidthAtMost G w) : ∃ v : V, G.degree v ≤ w := by
  obtain ⟨m,T,bag,hT,hs,hc,he,hcon⟩ := h
  exact tree_bags_have_low_degree G w T bag hT hs hc he hcon

end GraphicalZonotopes
