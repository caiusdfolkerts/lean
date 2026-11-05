module

public import Papers.GraphicalZonotopes.SmallCountGeometry
public import Papers.GraphicalZonotopes.MultipartiteRealization

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise

theorem conjunction_boolean {H : Type*} [Fintype H] [DecidableEq H] [Nonempty H] :
    IsMonotoneBoolean (setMonomial (univ : Finset H)) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro A B hAB
    by_cases hA : (univ : Finset H)⊆A
    · simp only [setMonomial,if_pos hA,if_pos (hA.trans hAB),le_refl]
    · simp only [setMonomial,if_neg hA]
      split_ifs <;> norm_num
  · intro A
    by_cases hA : (univ : Finset H)⊆A <;> simp [setMonomial,hA]
  · have hn : ¬(univ : Finset H)⊆∅ := by
      obtain ⟨a⟩:=‹Nonempty H›
      intro h
      exact notMem_empty a (h (mem_univ a))
    simp only [setMonomial,if_neg hn]
  · simp only [setMonomial,subset_refl,ite_true]

theorem conjunction_essential {H : Type*} [Fintype H] [DecidableEq H] (a : H) :
    Essential (setMonomial (univ : Finset H)) a := by
  refine ⟨univ.erase a,notMem_erase a univ,?_⟩
  have hins : insert a (univ.erase a)=(univ : Finset H):=insert_erase (mem_univ a)
  have hn : ¬(univ : Finset H)⊆univ.erase a:=
    fun h => notMem_erase a univ (h (mem_univ a))
  rw [hins]
  simp only [setMonomial,subset_refl,ite_true,if_neg hn,sub_zero]

theorem one_outer_lattice_book (s : ℕ) (hs : 0<s) :
    ∃ f : SetFunction (Fin s⊕Fin 1),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s 1) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin 1) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(1 : ℝ) • graphicalZonotope (cliqueBook s 1) := by
  letI : Nonempty (Fin s):=⟨⟨0,hs⟩⟩
  let F : Fin 1 → SetFunction (Fin s):=fun _ => setMonomial univ
  have hrel : ∃ z : SetFunction (Fin s),TranslationNormalized z ∧
      Compatible z F (fun _ => 1) := by
    refine ⟨0,⟨rfl,fun _ => rfl⟩,?_⟩
    intro u v huv S hu hv
    have hn : negativeResponse (setMonomial (univ : Finset (Fin s))) u v S=0 := by
      exact max_eq_left (neg_nonpos.mpr ((setMonomial_supermodular univ).elemental u v huv S hu hv))
    simpa only [F,hn,mul_zero,sum_const_zero] using
      (show delta (0 : SetFunction (Fin s)) u v S=0 by simp [delta])
  have huniq : UniqueIntegrableRelation F (fun _ => 1) := by
    intro t ht
    refine ⟨t 0,?_⟩
    funext i
    have hi : i=0:=Subsingleton.elim _ _
    subst i
    simp only [Pi.smul_apply,smul_eq_mul,mul_one]
  simpa only [Nat.cast_one] using lattice_book_of_unit_modules hs (by decide) F
    (fun _ => conjunction_boolean) (fun _ a => conjunction_essential a) hrel huniq

/-- The complete parameter range in Theorem7.5, with actual lattice
complements in `k` times the graphical zonotope. The proof includes the
one-column simplex case and constructs the multipartite pair pattern for
every remaining integer count. -/
theorem small_count_lattice_books (s k : ℕ) (hs : 2≤s) (hk : 1≤k)
    (hmax : k≤s.choose 2) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(k : ℝ) • graphicalZonotope (cliqueBook s k) := by
  by_cases hk1 : k=1
  · subst k
    simpa only [Nat.cast_one] using one_outer_lattice_book s (by omega)
  · have hs3 : 3≤s := by
      by_contra hn
      have hs2 : s=2:=by omega
      subst s
      norm_num at hmax
      omega
    have hm : 0<k-1:=by omega
    have hlt : k-1<s.choose 2:=by omega
    obtain ⟨blocks,hb,hcard,hproper⟩:=SmallCount.exists_complement_family_count s (k-1) hm hlt
    exact SmallCount.lattice_book_of_complement_family hs3 blocks hb hproper (by omega)


/-- Literal geometric formulation of Theorem 7.5, obtained from the complete
integral construction above. The actual complement already exists when k=1. -/
theorem small_count_lattice_books_literal (s k : ℕ) (hs : 2≤s) (hk : 1≤k)
    (hmax : k≤s.choose 2) :
    ∃ Q : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope Q ∧
      MinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s k)) ∧
      (2≤k → IsMinkowskiSummand Q ((k : ℝ) • graphicalZonotope (cliqueBook s k))) := by
  obtain ⟨f,hn,hi,he,hg,hd,hm,hl,R,hR,hnR,hsum⟩ :=
    small_count_lattice_books s k hs hk hmax
  have hactual : IsMinkowskiSummand (basePolytope f)
      ((k : ℝ) • graphicalZonotope (cliqueBook s k)) :=
    ⟨R,hR.compact,hR.convex,hnR,hsum⟩
  refine ⟨basePolytope f,hl,hm,hd,⟨(k : ℝ),?_,hactual⟩,fun _ => hactual⟩
  exact_mod_cast (show 0<k by omega)

end BooleanModule
end GraphicalZonotopes
