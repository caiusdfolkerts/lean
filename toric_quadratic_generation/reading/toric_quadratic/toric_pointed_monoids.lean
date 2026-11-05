module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Push

@[expose] public section

/-!
# Minimal generators of a pointed affine semigroup

For a pointed submonoid of an abelian group, every member of a minimal
finite generating set is indecomposable. The proof uses only cancellation
and pointedness, without assuming saturation or normality. This is the
semigroup ingredient of the direct smoothness/cotangent argument.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open scoped Classical

variable {M : Type*} [AddCommGroup M]

def IsPointedMonoid (S : AddSubmonoid M) : Prop :=
  ∀ x∈S, ∀ y∈S, x+y=0 → x=0 ∧ y=0

def IsMonoidAtom (S : AddSubmonoid M) (m : M) : Prop :=
  m∈S ∧ m≠0 ∧ ∀ x∈S, ∀ y∈S, x+y=m → x=0 ∨ y=0

theorem minimalGenerator_not_mem_eraseClosure (S : AddSubmonoid M)
    {G : Finset M} (hG : Minimal (fun T : Finset M => AddSubmonoid.closure (T : Set M)=S) G)
    {g : M} (hg : g∈G) : g∉AddSubmonoid.closure (G.erase g : Set M) := by
  intro hbad
  have heq : AddSubmonoid.closure (G.erase g : Set M)=S := by
    apply le_antisymm
    · rw [← hG.prop]
      exact AddSubmonoid.closure_mono (Finset.erase_subset g G)
    · rw [← hG.prop]
      apply AddSubmonoid.closure_le.mpr
      intro x hx
      by_cases h : x=g
      · simpa [h] using hbad
      · exact AddSubmonoid.subset_closure (Finset.mem_erase.mpr ⟨h,hx⟩)
  exact hG.not_prop_of_lt (Finset.erase_ssubset hg) heq

theorem minimalGenerator_ne_zero (S : AddSubmonoid M)
    {G : Finset M} (hG : Minimal (fun T : Finset M => AddSubmonoid.closure (T : Set M)=S) G)
    {g : M} (hg : g∈G) : g≠0 := by
  intro hz
  apply minimalGenerator_not_mem_eraseClosure S hG hg
  rw [hz]
  exact AddSubmonoid.zero_mem _

/-- Every generated element either avoids one selected generator, or
contains that generator plus another semigroup element. -/
theorem mem_closure_erase_or_add (S : AddSubmonoid M)
    (G : Finset M) (hG : AddSubmonoid.closure (G : Set M)=S)
    (g : M) {x : M} (hx : x∈S) :
    x∈AddSubmonoid.closure (G.erase g : Set M) ∨ ∃ z∈S,x=g+z := by
  rw [← hG] at hx
  induction hx using AddSubmonoid.closure_induction with
  | mem x hx =>
      by_cases h : x=g
      · exact Or.inr ⟨0,S.zero_mem,by simpa [h]⟩
      · exact Or.inl (AddSubmonoid.subset_closure (Finset.mem_erase.mpr ⟨h,hx⟩))
  | zero => exact Or.inl (AddSubmonoid.zero_mem _)
  | add x y hx hy ihx ihy =>
      have hxS : x∈S := hG ▸ hx
      have hyS : y∈S := hG ▸ hy
      rcases ihx with hx'|⟨z,hz,rfl⟩
      · rcases ihy with hy'|⟨z,hz,rfl⟩
        · exact Or.inl (AddSubmonoid.add_mem _ hx' hy')
        · exact Or.inr ⟨x+z,S.add_mem hxS hz,by abel⟩
      · exact Or.inr ⟨z+y,S.add_mem hz hyS,by abel⟩

theorem minimalGenerator_isAtom (S : AddSubmonoid M) (hS : IsPointedMonoid S)
    {G : Finset M} (hG : Minimal (fun T : Finset M => AddSubmonoid.closure (T : Set M)=S) G)
    {g : M} (hg : g∈G) : IsMonoidAtom S g := by
  refine ⟨hG.prop ▸ AddSubmonoid.subset_closure hg,
    minimalGenerator_ne_zero S hG hg, ?_⟩
  intro x hx y hy hxy
  by_contra h
  push_neg at h
  have hx' : x∈AddSubmonoid.closure (G.erase g : Set M) := by
    rcases mem_closure_erase_or_add S G hG.prop g hx with hx'|⟨z,hz,hxg⟩
    · exact hx'
    · have hzy : z+y=0 := by
        apply add_left_cancel (a := g)
        calc
          g+(z+y) = x+y := by rw [hxg]; abel
          _ = g+0 := by simpa using hxy
      exact (h.2 (hS z hz y hy hzy).2).elim
  have hy' : y∈AddSubmonoid.closure (G.erase g : Set M) := by
    rcases mem_closure_erase_or_add S G hG.prop g hy with hy'|⟨z,hz,hyg⟩
    · exact hy'
    · have hzx : z+x=0 := by
        apply add_left_cancel (a := g)
        calc
          g+(z+x) = x+y := by rw [hyg]; abel
          _ = g+0 := by simpa using hxy
      exact (h.1 (hS z hz x hx hzx).2).elim
  apply minimalGenerator_not_mem_eraseClosure S hG hg
  have hsum : x+y∈AddSubmonoid.closure (G.erase g : Set M) :=
    AddSubmonoid.add_mem _ hx' hy'
  simpa only [hxy] using hsum

theorem exists_finite_atom_generators (S : AddSubmonoid M)
    (hS : IsPointedMonoid S) (hfg : S.FG) :
    ∃ G : Finset M, AddSubmonoid.closure (G : Set M)=S ∧
      ∀ g∈G,IsMonoidAtom S g := by
  obtain ⟨G,hG⟩ := hfg.exists_minimal_closure_eq
  exact ⟨G,hG.prop,fun g hg => minimalGenerator_isAtom S hS hG hg⟩

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.exists_finite_atom_generators
