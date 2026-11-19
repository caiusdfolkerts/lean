module
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Fin
public import Mathlib.GroupTheory.Perm.Basic
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Finite basis exchange and deletion for catalogue induction

The family consists of genuine subsets of its ground set, all of the
specified rank. The exchange axiom and absence of loops are explicit.
Deleting a non-coloop preserves rank; deleting a coloop removes that
element from every basis and lowers rank by one. These are the complete
two branches used by the finite extension certificates.
-/

namespace Papers.RationalityTen.BasisFamilies

open Finset
variable {α : Type*} [DecidableEq α]

structure BasisFamily (ground : Finset α) (rank : ℕ) where
  bases : Finset (Finset α)
  nonempty : bases.Nonempty
  subset_ground : ∀ A ∈ bases, A ⊆ ground
  basis_card : ∀ A ∈ bases, A.card = rank
  exchange : ∀ A ∈ bases, ∀ B ∈ bases, ∀ x ∈ A, x ∉ B →
    ∃ y ∈ B, y ∉ A ∧ insert y (A.erase x) ∈ bases
  loopless : ∀ x ∈ ground, ∃ A ∈ bases, x ∈ A

variable {ground : Finset α} {rank : ℕ}

theorem rank_le_ground_card (M : BasisFamily ground rank) : rank ≤ ground.card := by
  obtain ⟨A,hA⟩ := M.nonempty
  rw [← M.basis_card A hA]
  exact card_le_card (M.subset_ground A hA)

theorem rank_pos_of_ground_nonempty (M : BasisFamily ground rank)
    (hg : ground.Nonempty) : 0 < rank := by
  obtain ⟨x,hx⟩ := hg
  obtain ⟨A,hA,hxA⟩ := M.loopless x hx
  rw [← M.basis_card A hA]
  exact card_pos.mpr ⟨x,hxA⟩

def deleteNonColoop (M : BasisFamily ground rank) (e : α)
    (havoid : ∃ A ∈ M.bases, e ∉ A) : BasisFamily (ground.erase e) rank where
  bases := M.bases.filter (e ∉ ·)
  nonempty := by
    obtain ⟨A,hA,heA⟩ := havoid
    exact ⟨A,mem_filter.mpr ⟨hA,heA⟩⟩
  subset_ground := by
    intro A hA x hx
    obtain ⟨hA,heA⟩ := mem_filter.mp hA
    exact mem_erase.mpr ⟨fun h => heA (h ▸ hx),M.subset_ground A hA hx⟩
  basis_card := fun A hA => M.basis_card A (mem_filter.mp hA).1
  exchange := by
    intro A hA B hB x hx hxB
    obtain ⟨hA,heA⟩ := mem_filter.mp hA
    obtain ⟨hB,heB⟩ := mem_filter.mp hB
    obtain ⟨y,hyB,hyA,hnew⟩ := M.exchange A hA B hB x hx hxB
    refine ⟨y,hyB,hyA,mem_filter.mpr ⟨hnew,?_⟩⟩
    intro he
    rcases mem_insert.mp he with hey | he
    · exact heB (hey ▸ hyB)
    · exact heA (mem_erase.mp he).2
  loopless := by
    intro x hx
    obtain ⟨hxe,hxg⟩ := mem_erase.mp hx
    obtain ⟨A,hA,hxA⟩ := M.loopless x hxg
    by_cases heA : e ∈ A
    · obtain ⟨B,hB,heB⟩ := havoid
      obtain ⟨y,hyB,hyA,hnew⟩ := M.exchange A hA B hB e heA heB
      refine ⟨insert y (A.erase e),mem_filter.mpr ⟨hnew,?_⟩,?_⟩
      · intro he
        rcases mem_insert.mp he with hey | he
        · exact heB (hey ▸ hyB)
        · exact (mem_erase.mp he).1 rfl
      · exact mem_insert_of_mem (mem_erase.mpr ⟨hxe,hxA⟩)
    · exact ⟨A,mem_filter.mpr ⟨hA,heA⟩,hxA⟩

def deleteColoop (M : BasisFamily ground rank) (e : α)
    (hevery : ∀ A ∈ M.bases, e ∈ A) : BasisFamily (ground.erase e) (rank-1) where
  bases := M.bases.image (fun A => A.erase e)
  nonempty := M.nonempty.image _
  subset_ground := by
    intro A hA
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hA
    exact erase_subset_erase e (M.subset_ground B hB)
  basis_card := by
    intro A hA
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hA
    rw [card_erase_of_mem (hevery B hB),M.basis_card B hB]
  exchange := by
    intro A hA B hB x hx hxB
    obtain ⟨C,hC,rfl⟩ := mem_image.mp hA
    obtain ⟨D,hD,rfl⟩ := mem_image.mp hB
    obtain ⟨hxe,hxC⟩ := mem_erase.mp hx
    have hxD : x ∉ D := fun h => hxB (mem_erase.mpr ⟨hxe,h⟩)
    obtain ⟨y,hyD,hyC,hnew⟩ := M.exchange C hC D hD x hxC hxD
    have hye : y ≠ e := fun h => hyC (h ▸ hevery C hC)
    refine ⟨y,mem_erase.mpr ⟨hye,hyD⟩,
      fun h => hyC (mem_erase.mp h).2,mem_image.mpr ?_⟩
    refine ⟨insert y (C.erase x),hnew,?_⟩
    rw [erase_insert_of_ne hye]
    congr 1
    ext z
    simp only [mem_erase]
    exact and_left_comm
  loopless := by
    intro x hx
    obtain ⟨hxe,hxg⟩ := mem_erase.mp hx
    obtain ⟨A,hA,hxA⟩ := M.loopless x hxg
    exact ⟨A.erase e,mem_image.mpr ⟨A,hA,rfl⟩,mem_erase.mpr ⟨hxe,hxA⟩⟩

theorem deleteColoop_recovers (M : BasisFamily ground rank) (e : α)
    (hevery : ∀ A ∈ M.bases, e ∈ A) :
    (deleteColoop M e hevery).bases.image (insert e) = M.bases := by
  change (M.bases.image (fun A => A.erase e)).image (insert e) = M.bases
  rw [image_image]
  apply Finset.ext
  intro A
  constructor
  · intro h
    obtain ⟨B,hB,hBA⟩ := mem_image.mp h
    have h := insert_erase (hevery B hB)
    exact (h.symm.trans hBA) ▸ hB
  · intro hA
    exact mem_image.mpr ⟨A,hA,insert_erase (hevery A hA)⟩

def relabel (M : BasisFamily ground rank) (p : Equiv.Perm α) :
    BasisFamily (ground.image p) rank where
  bases := M.bases.image (fun A => A.image p)
  nonempty := M.nonempty.image _
  subset_ground := by
    intro A hA
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hA
    exact image_subset_image (M.subset_ground B hB)
  basis_card := by
    intro A hA
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hA
    rw [card_image_of_injective _ p.injective]
    exact M.basis_card B hB
  exchange := by
    intro A hA B hB x hx hxB
    obtain ⟨C,hC,rfl⟩ := mem_image.mp hA
    obtain ⟨D,hD,rfl⟩ := mem_image.mp hB
    obtain ⟨u,huC,rfl⟩ := mem_image.mp hx
    have huD : u ∉ D := fun h => hxB (mem_image.mpr ⟨u,h,rfl⟩)
    obtain ⟨y,hyD,hyC,hnew⟩ := M.exchange C hC D hD u huC huD
    refine ⟨p y,mem_image.mpr ⟨y,hyD,rfl⟩,?_,?_⟩
    · intro h
      obtain ⟨z,hzC,hzy⟩ := mem_image.mp h
      exact hyC (p.injective hzy ▸ hzC)
    · apply mem_image.mpr
      refine ⟨insert y (C.erase u),hnew,?_⟩
      rw [image_insert,image_erase p.injective]
  loopless := by
    intro x hx
    obtain ⟨u,hug,rfl⟩ := mem_image.mp hx
    obtain ⟨A,hA,huA⟩ := M.loopless u hug
    exact ⟨A.image p,mem_image.mpr ⟨A,hA,rfl⟩,mem_image.mpr ⟨u,huA,rfl⟩⟩

theorem relabel_bases_trans (M : BasisFamily ground rank) (p q : Equiv.Perm α) :
    (relabel (relabel M p) q).bases = (relabel M (p.trans q)).bases := by
  simp only [relabel,image_image,Function.comp_def,Equiv.trans_apply]
  rfl

end Papers.RationalityTen.BasisFamilies
