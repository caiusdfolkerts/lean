module

public import Papers.GraphicalZonotopes.PureDecompositions

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H : Type*} [Fintype H] [LinearOrder H]

/-- Independent clique blocks remain independent in the actual quotient by
all central coefficients. This proves the direct-sum assertion, rather than
assuming an identification with a synthetic coordinate space. -/
theorem block_sum_zero_component {B : Type*} [Fintype B] [DecidableEq B]
    (C : B → Finset H) (hC : Function.Injective C)
    (e₀ : ∀ b,PairIn (C b)) (x : ∀ b,PairIn (C b) → ℝ)
    (hz : (∑ b,blockClass (C b) (x b))=0) (b : B) :
    blockClass (C b) (x b)=0 := by
  have hraw : coefficientClass (∑ c,blockCoordinates (C c) (x c))=0 := by
    simpa only [map_sum,blockClass,LinearMap.comp_apply] using hz
  have heval : ∀ e : PairIn (C b),
      (∑ c,blockCoordinates (C c) (x c)) (pairRow (C b) e)=x b e := by
    intro e
    rw [Finset.sum_apply]
    rw [sum_eq_single b]
    · exact blockCoordinates_pairRow (C b) (x b) e
    · intro c hc hcb
      have hne : rowClique (pairRow (C b) e)≠C c := by
        rw [rowClique_pairRow]
        exact fun h => hcb (hC h.symm)
      change (if h : rowClique (pairRow (C b) e)=C c then
        x c (pairAtRow (C c) (pairRow (C b) e) h) else 0)=0
      exact dite_eq_right hne
    · simp
  apply (blockClass_eq_zero_iff (C b) (e₀ b) (x b)).mpr
  refine ⟨x b (e₀ b),?_⟩
  intro e
  have hrows : rowCliqueIndex (pairRow (C b) e)=rowCliqueIndex (pairRow (C b) (e₀ b)) := by
    apply Subtype.ext
    exact (rowClique_pairRow (C b) e).trans (rowClique_pairRow (C b) (e₀ b)).symm
  have hh := (coefficientClass_eq_zero_iff _).mp hraw _ _ hrows
  simpa only [heval] using hh

theorem block_families_independent {B : Type*} [Fintype B] [DecidableEq B]
    (C : B → Finset H) (hC : Function.Injective C) (e₀ : ∀ b,PairIn (C b))
    {J : B → Type*} [∀ b,Fintype (J b)]
    (x : ∀ b,J b → PairIn (C b) → ℝ)
    (hx : ∀ b,LinearIndependent ℝ (fun j => blockClass (C b) (x b j))) :
    LinearIndependent ℝ (fun j : Sigma J => blockClass (C j.1) (x j.1 j.2)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  let y := fun b => ∑ i : J b,c ⟨b,i⟩ • x b i
  have hy : (∑ b,blockClass (C b) (y b))=0 := by
    rw [Fintype.sum_sigma] at hc
    simpa only [y,map_sum,map_smul] using hc
  have hj := block_sum_zero_component C hC e₀ y hy j.1
  have hji : (∑ i : J j.1,c ⟨j.1,i⟩ • blockClass (C j.1) (x j.1 i))=0 := by
    simpa only [y,map_sum,map_smul] using hj
  exact (Fintype.linearIndependent_iff.mp (hx j.1)) _ hji j.2

theorem pureDecompositions_independent {B : Type*} [Fintype B] [DecidableEq B]
    (C : B → Finset H) (hC : Function.Injective C) (hsize : ∀ b,2≤(C b).card)
    (v : B → ResponseQuotient H) (k : B → ℕ)
    (P : ∀ b,PureDecomposition (C b) (v b) (k b)) :
    LinearIndependent ℝ (fun j : Σ b,Fin (k b) => responseClass ((P j.1).functions j.2)) := by
  classical
  choose x hx using fun b j => (P b).block_supported j
  have hex : ∀ b,∃ e : PairIn (C b),True := by
    intro b
    obtain ⟨e,he⟩ := cliquePairs_nonempty (C b) (C b) (Subset.refl _) (hsize b)
    exact ⟨e,trivial⟩
  choose e₀ he₀ using hex
  have hi : ∀ b,LinearIndependent ℝ (fun j => blockClass (C b) (x b j)) := by
    intro b
    simpa only [← hx] using (P b).independent
  simpa only [hx] using block_families_independent C hC e₀ x hi

end BooleanModule
end GraphicalZonotopes
