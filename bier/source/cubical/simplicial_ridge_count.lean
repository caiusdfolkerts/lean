module

public import cubical.simplicial_faces
public import cubical.pseudomanifold_circuit

/-! # Facet-ridge incidence for finite simplicial pseudomanifolds -/

@[expose] public section

namespace Cubical.Simplicial

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

theorem mem_simplexBoundary_iff {s t : Finset V} :
    t ∈ simplexBoundary s ↔ t ⊆ s ∧ t.card + 1 = s.card := by
  constructor
  · intro h
    exact ⟨simplexBoundary_subset h, simplexBoundary_card h⟩
  · rintro ⟨hsub, hcard⟩
    obtain ⟨v, hv, hvn⟩ := Finset.exists_mem_notMem_of_card_lt_card (by omega : t.card < s.card)
    have hsub' : t ⊆ s.erase v := by
      intro x hx
      exact Finset.mem_erase.mpr ⟨fun h => hvn (h ▸ hx), hsub hx⟩
    have hc := Finset.card_erase_add_one hv
    have heq : t = s.erase v := Finset.eq_of_subset_of_card_le hsub' (by omega)
    exact Finset.mem_image.mpr ⟨v, hv, heq.symm⟩

@[simp]
theorem simplexBoundary_card_eq (s : Finset V) : (simplexBoundary s).card = s.card := by
  exact Finset.card_image_iff.mpr s.erase_injOn

theorem simplexBoundary_subset_faces {n : ℕ} {s : Finset (Finset V)}
    (hpure : Pure n id s) {t : Finset V} (ht : t ∈ s) :
    simplexBoundary t ⊆ faces s (n - 1) := by
  intro r hr
  have hc := simplexBoundary_card hr
  have hct : t.card = n := hpure t ht
  exact (mem_faces s (n - 1) r).mpr
    ⟨by omega, t, ht, simplexBoundary_subset hr⟩

theorem RidgeDegreeTwo.ridge_incidence {n : ℕ} (hn : 0 < n)
    {s : Finset (Finset V)} (hpure : Pure n id s) (hdeg : RidgeDegreeTwo s) :
    n * s.card = 2 * (faces s (n - 1)).card := by
  have hleft : (∑ t ∈ s, ((faces s (n - 1)).filter
      (fun r => r ∈ simplexBoundary t)).card) = n * s.card := by
    have hterm : ∀ t ∈ s, ((faces s (n - 1)).filter
        (fun r => r ∈ simplexBoundary t)).card = n := by
      intro t ht
      have heq : (faces s (n - 1)).filter (fun r => r ∈ simplexBoundary t) =
          simplexBoundary t := by
        ext r
        simp only [Finset.mem_filter]
        exact ⟨And.right, fun hr => ⟨simplexBoundary_subset_faces hpure ht hr, hr⟩⟩
      rw [heq, simplexBoundary_card_eq]
      exact hpure t ht
    rw [Finset.sum_congr rfl hterm]
    simp [Nat.mul_comm]
  have hright : (∑ r ∈ faces s (n - 1), (s.filter
      (fun t => r ∈ simplexBoundary t)).card) = 2 * (faces s (n - 1)).card := by
    have hterm : ∀ r ∈ faces s (n - 1), (s.filter
        (fun t => r ∈ simplexBoundary t)).card = 2 := by
      intro r hr
      obtain ⟨hcr, t, ht, hsub⟩ := (mem_faces s (n - 1) r).mp hr
      have hct : t.card = n := hpure t ht
      have hrb : r ∈ simplexBoundary t := mem_simplexBoundary_iff.mpr ⟨hsub, by omega⟩
      have hpos : 0 < (s.filter (fun t => r ∈ simplexBoundary t)).card :=
        Finset.card_pos.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, hrb⟩⟩
      rcases hdeg r with hz | ht
      · omega
      · exact ht
    rw [Finset.sum_congr rfl hterm]
    simp [Nat.mul_comm]
  have hswap : (∑ t ∈ s, ((faces s (n - 1)).filter
      (fun r => r ∈ simplexBoundary t)).card) =
      ∑ r ∈ faces s (n - 1), (s.filter (fun t => r ∈ simplexBoundary t)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  exact hleft.symm.trans (hswap.trans hright)

end Cubical.Simplicial
