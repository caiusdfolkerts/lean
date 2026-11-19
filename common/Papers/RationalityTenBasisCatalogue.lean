module
public import Papers.RationalityTenBasisReconstruction

@[expose] public section

namespace Papers.RationalityTen.BasisCatalogue

open Finset BasisFamilies BasisReconstruction

abbrev Point := Fin 8
abbrev Catalogue := ℕ → ℕ → Finset (Finset (Finset Point))

def Covered (C : Catalogue) (n r : ℕ) : Prop :=
  ∀ M : BasisFamily (groundPrefix n) r,
    ∃ B ∈ C n r, IsomorphicWithin n M.bases B

def ExtensionCovered (C : Catalogue) (n r : ℕ) (hn : n < 8) : Prop :=
  ∀ B ∈ C n r, ∀ M : BasisFamily (groundPrefix (n+1)) r,
    M.bases.filter (fun A => (⟨n,hn⟩ : Point) ∉ A) = B →
    ∃ D ∈ C (n+1) r, IsomorphicWithin (n+1) M.bases D

def ColoopCovered (C : Catalogue) (n r : ℕ) (hn : n < 8) : Prop :=
  0 < r → ∀ B ∈ C n (r-1), ∃ D ∈ C (n+1) r,
    IsomorphicWithin (n+1) (B.image (insert (⟨n,hn⟩ : Point))) D

theorem relabel_filter (p : Equiv.Perm Point) (e : Point)
    (he : p e = e) (B : Finset (Finset Point)) :
    relabelFamily p (B.filter (e ∉ ·)) =
      (relabelFamily p B).filter (e ∉ ·) := by
  have hmem (A : Finset Point) : e ∈ A.image p ↔ e ∈ A := by
    constructor
    · intro h
      obtain ⟨x,hx,hxe⟩ := mem_image.mp h
      have hx_eq : x=e := p.injective (hxe.trans he.symm)
      exact hx_eq ▸ hx
    · intro h
      exact mem_image.mpr ⟨e,h,he⟩
  ext A
  constructor
  · rintro h
    obtain ⟨D,hD,rfl⟩ := mem_image.mp h
    obtain ⟨hD,heD⟩ := mem_filter.mp hD
    exact mem_filter.mpr ⟨mem_image.mpr ⟨D,hD,rfl⟩,fun h=>heD ((hmem D).mp h)⟩
  · rintro h
    obtain ⟨hA,heA⟩ := mem_filter.mp h
    obtain ⟨D,hD,rfl⟩ := mem_image.mp hA
    exact mem_image.mpr ⟨D,mem_filter.mpr ⟨hD,fun h=>heA ((hmem D).mpr h)⟩,rfl⟩

theorem relabel_insert (p : Equiv.Perm Point) (e : Point)
    (he : p e = e) (B : Finset (Finset Point)) :
    relabelFamily p (B.image (insert e)) = (relabelFamily p B).image (insert e) := by
  simp only [relabelFamily,image_image,Function.comp_def,image_insert,he]

theorem covered_zero (C : Catalogue) (hC : ({∅} : Finset (Finset Point)) ∈ C 0 0)
    (r : ℕ) : Covered C 0 r := by
  intro M
  have hr := rank_le_ground_card M
  simp only [groundPrefix_zero,card_empty,Nat.le_zero] at hr
  subst r
  have hb : M.bases = {∅} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    constructor
    · obtain ⟨A,hA⟩ := M.nonempty
      have ha := M.subset_ground A hA
      have he : A=∅ := by simpa using ha
      exact he ▸ hA
    · intro A hA
      have ha := M.subset_ground A hA
      simpa using ha
  exact ⟨{∅},hC,hb ▸ isomorphicWithin_refl 0 M.bases⟩

/-- The complete deletion induction. The two input coverage statements are
finite extension and coloop certificate families, not mathematical
classification assumptions about an arbitrary input. -/
theorem covered_step (C : Catalogue) (n r : ℕ) (hn : n < 8)
    (hold : Covered C n r) (hcolold : Covered C n (r-1))
    (hext : ExtensionCovered C n r hn) (hcol : ColoopCovered C n r hn) :
    Covered C (n+1) r := by
  intro M
  let e : Point := ⟨n,hn⟩
  by_cases havoid : ∃ A ∈ M.bases, e ∉ A
  · let D : BasisFamily (groundPrefix n) r :=
      castGround (deleteNonColoop M e havoid) (groundPrefix_erase_last n hn)
    obtain ⟨B,hB,p,hp,hpB⟩ := hold D
    have he : p e = e := hp e (by rfl)
    let N := relabelWithin M p (fixesOutside_mono hp (Nat.le_succ n))
    have hNB : N.bases.filter (e ∉ ·) = B := by
      dsimp only [N]
      rw [relabelWithin_bases]
      rw [← relabel_filter p e he]
      simpa only [D,castGround_bases,deleteNonColoop] using hpB
    obtain ⟨F,hF,q,hq,hqF⟩ := hext B hB N hNB
    refine ⟨F,hF,p.trans q,
      fixesOutside_trans (fixesOutside_mono hp (Nat.le_succ n)) hq,?_⟩
    rw [← relabelFamily_trans]
    simpa only [N,relabelWithin_bases] using hqF
  · have hevery : ∀ A ∈ M.bases, e ∈ A := by
      intro A hA
      by_contra heA
      exact havoid ⟨A,hA,heA⟩
    let D : BasisFamily (groundPrefix n) (r-1) :=
      castGround (deleteColoop M e hevery) (groundPrefix_erase_last n hn)
    obtain ⟨B,hB,p,hp,hpB⟩ := hcolold D
    have he : p e = e := hp e (by rfl)
    have hrpos : 0 < r := rank_pos_of_ground_nonempty M
      ⟨e,by simp only [mem_groundPrefix]; exact Nat.lt_succ_self n⟩
    obtain ⟨F,hF,q,hq,hqF⟩ := hcol hrpos B hB
    refine ⟨F,hF,p.trans q,
      fixesOutside_trans (fixesOutside_mono hp (Nat.le_succ n)) hq,?_⟩
    rw [← relabelFamily_trans]
    have hrec : D.bases.image (insert e) = M.bases := by
      simpa only [D,castGround_bases] using deleteColoop_recovers M e hevery
    rw [← hrec,relabel_insert p e he,hpB]
    exact hqF

theorem covered_through_seven (C : Catalogue)
    (hzero : ({∅} : Finset (Finset Point)) ∈ C 0 0)
    (hext : ∀ n, n < 7 → ∀ r, r ≤ 4 → ∀ hn : n < 8,
      ExtensionCovered C n r hn)
    (hcol : ∀ n, n < 7 → ∀ r, r ≤ 4 → ∀ hn : n < 8,
      ColoopCovered C n r hn) :
    ∀ n, n ≤ 7 → ∀ r, r ≤ 4 → Covered C n r := by
  intro n hn
  induction n with
  | zero => exact fun r hr => covered_zero C hzero r
  | succ n ih =>
    intro r hr
    have hn7 : n < 7 := by omega
    have hn8 : n < 8 := by omega
    exact covered_step C n r hn8 (ih (by omega) r hr)
      (ih (by omega) (r-1) (by omega))
      (hext n hn7 r hr hn8) (hcol n hn7 r hr hn8)

theorem covered_eight_rank_four (C : Catalogue)
    (hseven : ∀ r, r ≤ 4 → Covered C 7 r)
    (hext : ExtensionCovered C 7 4 (by decide))
    (hcol : ColoopCovered C 7 4 (by decide)) :
    Covered C 8 4 :=
  covered_step C 7 4 (by decide) (hseven 4 (by decide))
    (hseven 3 (by decide)) hext hcol

end Papers.RationalityTen.BasisCatalogue
