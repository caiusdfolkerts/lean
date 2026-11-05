module

public import PaperVerification.ToricOneExceptionalPositive
public import PaperVerification.ToricContractibleWalls

@[expose] public section

/-!
# Actual opposite walls in the exceptional fiber directions

At every full cone over a selected contraction locus, the fiber directions
have neighboring cones with a strictly positive exceptional coordinate.
These are constructed by the original contraction replacement or by changing
the pivot of the genuine star subdivision.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

theorem starRaySet_replace_commutes {n : ℕ}
    (U T : Finset (Lattice n)) (p x z : Lattice n)
    (hzp : z ≠ p) (hxe : x ≠ ∑ v ∈ T, v) :
    starRaySet (insert z (U.erase x)) T p =
      insert z ((starRaySet U T p).erase x) := by
  ext v
  by_cases hvp : v = p <;> by_cases hvx : v = x <;>
    by_cases hvz : v = z <;> by_cases hve : v = ∑ w ∈ T, w <;>
    simp_all [starRaySet]

theorem starRaySet_change_pivot {n : ℕ}
    (U T : Finset (Lattice n)) (p x : Lattice n)
    (hpU : p ∈ U) (hpx : p ≠ x) (hxe : x ≠ ∑ v ∈ T, v) :
    starRaySet U T x = insert p ((starRaySet U T p).erase x) := by
  ext v
  by_cases hvp : v = p <;> by_cases hvx : v = x <;>
    by_cases hve : v = ∑ w ∈ T, w <;> simp_all [starRaySet]

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- A full cone containing the exceptional ray is one whole star chart of
a full old cone. No completeness or purity consequence is postulated. -/
theorem full_star_cone_parent
    (T : Finset (Lattice n)) (hT : T ∈ «Σ».cones) (hne : T.Nonempty)
    (hcard : 2 ≤ T.card) {s : Finset (Lattice n)}
    (hs : s ∈ («Σ».starSubdivision T hT hne).cones) (hscard : s.card = n)
    (he : (∑ v ∈ T, v) ∈ s) :
    ∃ U ∈ «Σ».cones, U.card = n ∧ T ⊆ U ∧
      ∃ p ∈ T, s = starRaySet U T p := by
  obtain ⟨C, hC, hsC⟩ := (mem_finiteConeFamilyClosure («Σ».starCandidates T) s).mp hs
  obtain ⟨b, hb⟩ := «Σ».starCandidates_smooth T C hC
  have hCle : C.card ≤ n := by
    have hh := Finset.card_le_card hb
    simpa only [Finset.card_image_of_injective _ b.injective, Finset.card_fin] using hh
  have hsCeq : s = C := Finset.eq_of_subset_of_card_le hsC (by omega)
  rcases («Σ».mem_starCandidates T C).mp hC with ⟨hCold, hnot⟩ |
    ⟨U, hU, p, hp, hTU, hCeq⟩
  · exact («Σ».sum_rays_not_mem_rays hT hcard
      («Σ».ray_mem_of_mem_cone hCold (hsCeq ▸ he))).elim
  · have hseq := hsCeq.trans hCeq
    refine ⟨U, hU, ?_, hTU, p, hp, hseq⟩
    rw [hseq, «Σ».starRaySet_card hU hTU hp] at hscard
    exact hscard

end SmoothCompleteFan

namespace SmoothCompleteFan.PrimitiveRelation

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} (R : «Σ».PrimitiveRelation)

/-- At a full star cone the `r+q-1` fiber walls have actual opposite rays
with negative wall coordinate and positive exceptional coordinate. The
basis, ray sets and adjacent cones are all constructed from the fan. -/
theorem exceptional_fiber_wall_data
    (hR : R.IsCombinatoriallyContractible)
    (hne : R.negative.Nonempty) (hcard : 2 ≤ R.negative.card)
    {s : Finset (Lattice n)}
    (hs : s ∈ («Σ».starSubdivision R.negative R.negative_cone hne).cones)
    (hscard : s.card = n) (he : (∑ v ∈ R.negative, v) ∈ s) :
    ∃ (b : Module.Basis (Fin n) ℤ (Lattice n)) (j : Fin n) (F : Finset (Fin n)),
      s = Finset.univ.image b ∧ b j = ∑ v ∈ R.negative, v ∧ j ∉ F ∧
      F.card = R.fiberDimension + R.negative.card - 1 ∧
      ∀ k ∈ F, ∃ z : Lattice n,
        insert z ((Finset.univ.erase k).image b) ∈
          («Σ».starSubdivision R.negative R.negative_cone hne).cones ∧
        b.repr z k = -1 ∧ 0 < b.repr z j := by
  let T := R.negative
  let e := ∑ v ∈ T, v
  obtain ⟨U, hU, hUcard, hTU, p, hp, hseq⟩ :=
    «Σ».full_star_cone_parent T R.negative_cone hne hcard hs hscard he
  obtain ⟨d, hUd⟩ := «Σ».full_cone_basis hU hUcard
  let J := basisRayIndices d T
  have hJ : J.image d = T := image_basisRayIndices d T (hUd ▸ hTU)
  obtain ⟨j, hj, hdj⟩ := Finset.mem_image.mp (hJ.symm ▸ hp)
  have hpU : p ∈ U := hTU hp
  let b := starRayBasis d J j
  have hsb : s = Finset.univ.image b := by
    rw [hseq, hUd, ← hJ, ← hdj,
      lattice_starRaySet_basis d Finset.univ J (Finset.subset_univ J) j hj]
  have hbj : b j = e := by
    change b j = ∑ v ∈ T, v
    rw [starRayBasis_pivot d J j hj, ← hJ, Finset.sum_image]
    exact fun i _ k _ hik => d.injective hik
  let A := basisRayIndices d (R.positive ∩ U)
  have hAimage : A.image d = R.positive ∩ U :=
    image_basisRayIndices d _ (hUd ▸ Finset.inter_subset_right)
  have hAcard : A.card = R.fiberDimension := by
    have hh := R.positive_count_in_full_cone hR hU hUcard hTU
    rw [← hAimage, Finset.card_image_of_injective _ d.injective] at hh
    exact hh
  have hJcard : J.card = T.card := by
    rw [← hJ, Finset.card_image_of_injective _ d.injective]
  have hAdisjJ : Disjoint A J := by
    apply Finset.disjoint_left.mpr
    intro k hkA hkJ
    have hkP := (Finset.mem_inter.mp (Finset.mem_filter.mp hkA).2).1
    have hkT := (Finset.mem_filter.mp hkJ).2
    exact Finset.disjoint_left.mp R.disjoint hkP hkT
  let F := A ∪ J.erase j
  have hjF : j ∉ F := by
    intro hh
    rcases Finset.mem_union.mp hh with hh | hh
    · exact Finset.disjoint_left.mp hAdisjJ hh hj
    · exact (Finset.mem_erase.mp hh).1 rfl
  have hFcard : F.card = R.fiberDimension + T.card - 1 := by
    rw [Finset.card_union_of_disjoint (hAdisjJ.mono_right (Finset.erase_subset j J)),
      hAcard, Finset.card_erase_of_mem hj, hJcard]
    have hq : 1 ≤ T.card := Finset.card_pos.mpr hne
    exact (Nat.add_sub_assoc hq R.fiberDimension).symm
  refine ⟨b, j, F, hsb, hbj, hjF, hFcard, ?_⟩
  intro k hkF
  have hkj : k ≠ j := fun hh => hjF (hh ▸ hkF)
  have hbk : b k = d k := starRayBasis_other d J j k hkj
  have hdkU : d k ∈ U := hUd.symm ▸ Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩
  have heold : e ∉ «Σ».rays := «Σ».sum_rays_not_mem_rays R.negative_cone hcard
  have hdke : d k ≠ e := fun hh => heold (hh ▸ «Σ».ray_mem_of_mem_cone hU hdkU)
  have hwall : (Finset.univ.erase k).image b = s.erase (d k) := by
    rw [Finset.image_erase b.injective, ← hsb, hbk]
  rcases Finset.mem_union.mp hkF with hkA | hkJ
  · have hkP : d k ∈ R.positive := (Finset.mem_inter.mp (Finset.mem_filter.mp hkA).2).1
    have hknotJ : k ∉ J := fun hh => Finset.disjoint_left.mp hAdisjJ hkA hh
    obtain ⟨z, hzP, hzU, hPdiff, hzcone, hzcoord⟩ :=
      R.replacement_across_full_wall hR U hU d hUd hTU k hkP
    have hzj : d.repr z j = R.coefficient p := by
      have hh := R.omitted_positive_coordinates d U hUd hTU z hzP hzU hPdiff j
      have hpP : p ∉ R.positive := fun hh => Finset.disjoint_left.mp R.disjoint hh hp
      have hpN : p ∈ R.negative := hp
      change d.repr z j + _ = _ at hh
      simpa only [hdj, if_neg hpP, if_pos hpN, add_zero] using hh
    have hTU' : T ⊆ insert z (U.erase (d k)) := by
      intro u hu
      have huk : u ≠ d k := by
        intro hh
        exact Finset.disjoint_left.mp R.disjoint hkP (hh ▸ hu)
      exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨huk, hTU hu⟩)
    have hnew := «Σ».starRaySet_mem_starSubdivision T R.negative_cone hne hzcone hTU' hp
    have hzp : z ≠ p := fun hh => hzU (hh.symm ▸ hpU)
    rw [starRaySet_replace_commutes U T p (d k) z hzp hdke, ← hseq, ← hwall] at hnew
    refine ⟨z, hnew, ?_, ?_⟩
    · change (starRayBasis d J j).coord k z = -1
      rw [starRayBasis_coord, if_neg (fun hh => hknotJ (Finset.mem_of_mem_erase hh))]
      exact (hzcoord k).mp hkP
    · change 0 < (starRayBasis d J j).coord j z
      rw [starRayBasis_coord_pivot]
      change 0 < d.repr z j
      rw [hzj]
      exact_mod_cast R.coefficient_pos p hp
  · have hkT : d k ∈ T := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hkJ)).2
    have hpdk : p ≠ d k := by
      intro hh
      exact hkj (d.injective (hh.symm.trans hdj.symm))
    have hnew := «Σ».starRaySet_mem_starSubdivision T R.negative_cone hne hU hTU hkT
    rw [starRaySet_change_pivot U T p (d k) hpU hpdk hdke, ← hseq, ← hwall] at hnew
    refine ⟨p, hnew, ?_, ?_⟩
    · change (starRayBasis d J j).coord k p = -1
      rw [starRayBasis_coord, if_pos hkJ, ← hdj]
      simp only [Module.Basis.coord_apply, Module.Basis.repr_self_apply,
        if_neg (Ne.symm hkj), if_pos rfl]
      norm_num
    · change 0 < (starRayBasis d J j).coord j p
      rw [starRayBasis_coord_pivot, ← hdj]
      simp

/-- In codimension one the same fiber wall data lives on the original fan.
There are exactly `r` such walls, all from the positive collection. -/
theorem divisor_fiber_wall_data
    (hR : R.IsCombinatoriallyContractible) (e : Lattice n)
    (hfocus : R.negative = {e}) {s : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (hscard : s.card = n) (he : e ∈ s) :
    ∃ (b : Module.Basis (Fin n) ℤ (Lattice n)) (j : Fin n) (F : Finset (Fin n)),
      s = Finset.univ.image b ∧ b j = e ∧ j ∉ F ∧ F.card = R.fiberDimension ∧
      ∀ k ∈ F, ∃ z : Lattice n,
        insert z ((Finset.univ.erase k).image b) ∈ «Σ».cones ∧
        b.repr z k = -1 ∧ 0 < b.repr z j := by
  obtain ⟨b, hsb⟩ := «Σ».full_cone_basis hs hscard
  obtain ⟨j, hj, hbj⟩ := Finset.mem_image.mp (hsb ▸ he)
  let F := basisRayIndices b (R.positive ∩ s)
  have hFimage : F.image b = R.positive ∩ s :=
    image_basisRayIndices b _ (hsb ▸ Finset.inter_subset_right)
  have hNs : R.negative ⊆ s := by simpa only [hfocus, Finset.singleton_subset_iff] using he
  have hFcard : F.card = R.fiberDimension := by
    have hh := R.positive_count_in_full_cone hR hs hscard hNs
    rw [← hFimage, Finset.card_image_of_injective _ b.injective] at hh
    exact hh
  have heN : e ∈ R.negative := hfocus.symm ▸ Finset.mem_singleton_self e
  have heP : e ∉ R.positive := fun hh => Finset.disjoint_left.mp R.disjoint hh heN
  have hjF : j ∉ F := by
    intro hh
    have hP := (Finset.mem_inter.mp (Finset.mem_filter.mp hh).2).1
    exact heP (hbj ▸ hP)
  refine ⟨b, j, F, hsb, hbj, hjF, hFcard, ?_⟩
  intro k hk
  have hkP := (Finset.mem_inter.mp (Finset.mem_filter.mp hk).2).1
  obtain ⟨z, hzP, hzs, hPdiff, hzcone, hzcoord⟩ :=
    R.replacement_across_full_wall hR s hs b hsb hNs k hkP
  have hwall : s.erase (b k) = (Finset.univ.erase k).image b := by
    rw [hsb, ← Finset.image_erase b.injective]
  refine ⟨z, hwall ▸ hzcone, (hzcoord k).mp hkP, ?_⟩
  have hh := R.omitted_positive_coordinates b s hsb hNs z hzP hzs hPdiff j
  change b.repr z j + _ = _ at hh
  have heq : b.repr z j = R.coefficient e := by
    simpa only [hbj, if_neg heP, if_pos heN, add_zero] using hh
  rw [heq]
  exact_mod_cast R.coefficient_pos e heN

end SmoothCompleteFan.PrimitiveRelation

end PaperVerification.ToricGeometry
