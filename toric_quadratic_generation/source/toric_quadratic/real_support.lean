module

public import paper_verification.toric009
public import toric_quadratic.fan_basics

@[expose] public section

/-!
# Side-two corner boxes for real ample support

This module proves the full real-support form of Proposition 5.2. The old
integral proof uses a ceiling correction; for a real deficit the correction
is its quotient by the smallest positive normal coefficient. The fan and
all of its primitive relations are the existing geometric objects.

The only positivity assumption is the stated lower bound on the ordinary
normalized degrees across adjacent full cones. The first two lemmas identify
these degrees with the displacement of the actual Cartier points and with
the existing integral wall-degree predicate when the support is integral.
-/

noncomputable section

namespace ToricQuadratic.RealSupport

open Set
open PaperVerification.ToricGeometry
open PaperVerification.ToricGeometry.SmoothCompleteFan
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- The ordinary real invariant-degree bound: every adjacent full-cone
wall has normalized primitive slack at least `bound`. -/
def WallDegreesAtLeast (a : Lattice n → ℝ) (bound : ℝ) : Prop :=
  ∀ s t : «Σ».fullCones, (s.val ∩ t.val).card = n - 1 →
    ∀ u ∈ t.val, u ∉ s.val → bound ≤ «Σ».wallSlack a s u

/-- The number used in `WallDegreesAtLeast` is precisely the coefficient
of the primitive dual lattice direction in the displacement of the two
actual Cartier points. No auxiliary curve-degree variable is assumed. -/
theorem wall_degree_displacement (a : Lattice n → ℝ)
    (s t : «Σ».fullCones) (hst : (s.val ∩ t.val).card = n - 1)
    (u : Lattice n) (hut : u ∈ t.val) (hus : u ∉ s.val) :
    ∃ j : Fin n,
      «Σ».cartierPoint a t = «Σ».cartierPoint a s +
        «Σ».wallSlack a s u • integralBasisReal
          (integralDualBasis («Σ».fullConeBasis s)) j := by
  obtain ⟨j, _, ht⟩ := «Σ».adjacentWall_basisIndex s t hst u hut hus
  refine ⟨j, ?_⟩
  exact «Σ».cartierPoint_across_wall a s t j u ht
    («Σ».adjacentWall_transverse s t j u ht hus)

/-- The real predicate specializes exactly to the existing integral
wall-degree predicate, rather than imposing an additional positivity test. -/
theorem wallDegreesAtLeast_integral_iff (a : Lattice n → ℤ) (bound : ℕ) :
    WallDegreesAtLeast «Σ» (fun u => (a u : ℝ)) bound ↔
      «Σ».HasWallSlacksAtLeast a bound := by
  constructor
  · intro h s t hst u hut hus
    have hh := h s t hst u hut hus
    rw [← «Σ».integerWallSlack_cast a s u] at hh
    exact_mod_cast hh
  · intro h s t hst u hut hus
    rw [← «Σ».integerWallSlack_cast a s u]
    exact_mod_cast h s t hst u hut hus

/-- A wall may be presented in any integral cone basis. Its supporting
linear-form slack equals the canonical Cartier-point slack. -/
theorem bound_at_basis_wall (a : Lattice n → ℝ) (bound : ℝ)
    (hbound : WallDegreesAtLeast «Σ» a bound)
    (d : Module.Basis (Fin n) ℤ (Lattice n))
    (hd : Finset.univ.image d ∈ «Σ».cones) (j : Fin n) (q : Lattice n)
    (hqcone : insert q ((Finset.univ.erase j).image d) ∈ «Σ».cones)
    (hqcoord : d.repr q j = -1)
    (ℓ : Ambient n →ₗ[ℝ] ℝ)
    (hℓ : ∀ i, ℓ (embed n (d i)) = a (d i)) :
    bound ≤ a q - ℓ (embed n q) := by
  let U := Finset.univ.image d
  let W := (Finset.univ.erase j).image d
  have hWU : W ⊆ U := Finset.image_subset_image (Finset.erase_subset j Finset.univ)
  have hUcard : U.card = n := by
    rw [Finset.card_image_of_injective _ d.injective]
    simp
  have hWcard : W.card = n - 1 := by
    rw [Finset.card_image_of_injective _ d.injective, Finset.card_erase_of_mem
      (Finset.mem_univ j)]
    simp
  have hqU : q ∉ U := by
    intro hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    rw [d.repr_self_apply] at hqcoord
    split_ifs at hqcoord
  have hqW : q ∉ W := fun hq => hqU (hWU hq)
  have htcard : (insert q W).card = n := by
    rw [Finset.card_insert_of_notMem hqW, hWcard]
    have := j.isLt
    omega
  let s : «Σ».fullCones := ⟨U, Finset.mem_filter.mpr ⟨hd, hUcard⟩⟩
  let t : «Σ».fullCones := ⟨insert q W, Finset.mem_filter.mpr ⟨hqcone, htcard⟩⟩
  have hmeet : U ∩ insert q W = W := by
    ext u
    constructor
    · rintro hu
      obtain ⟨huU, huT⟩ := Finset.mem_inter.mp hu
      rcases Finset.mem_insert.mp huT with rfl | huW
      · exact (hqU huU).elim
      · exact huW
    · intro huW
      exact Finset.mem_inter.mpr ⟨hWU huW, Finset.mem_insert_of_mem huW⟩
  have hst : (s.val ∩ t.val).card = n - 1 := by
    change (U ∩ insert q W).card = n - 1
    rw [hmeet, hWcard]
  have hform : ℓ = -(dotProductEquiv ℝ (Fin n) («Σ».cartierPoint a s)) := by
    apply (integralBasisReal d).ext
    intro i
    rw [integralBasisReal_apply, hℓ i]
    change a (d i) = -dotProduct («Σ».cartierPoint a s) (embed n (d i))
    rw [dotProduct_comm]
    have hi : d i ∈ s.val := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have hh := «Σ».cartierPoint_support_eq_of_mem a s hi
    change dotProduct (embed n (d i)) («Σ».cartierPoint a s) = -a (d i) at hh
    linarith only [hh]
  have hslack : «Σ».wallSlack a s q = a q - ℓ (embed n q) := by
    rw [hform]
    simp only [wallSlack, LinearMap.neg_apply, sub_neg_eq_add]
    change a q + dotProduct (embed n q) («Σ».cartierPoint a s) =
      a q + dotProduct («Σ».cartierPoint a s) (embed n q)
    rw [dotProduct_comm]
  rw [← hslack]
  exact hbound s t hst q (Finset.mem_insert_self _ _) hqU

/-- Every contractible primitive relation is represented by a genuine
wall, so the original real invariant-degree bound applies to it. -/
theorem contractible_degree_lower_bound
    (hpure : «Σ».IsPure) (a : Lattice n → ℝ) (ha : «Σ».IsStrictSupport a)
    (bound : ℝ) (hbound : WallDegreesAtLeast «Σ» a bound)
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible) :
    bound ≤ R.degree a := by
  obtain ⟨U, hUcone, hNU, hUcard⟩ := hpure R.negative R.negative_cone
  obtain ⟨d, hU⟩ := «Σ».full_cone_basis hUcone hUcard
  have hcount := R.positive_count_in_full_cone hR hUcone hUcard hNU
  have hpos : 0 < (R.positive ∩ U).card := by
    rw [hcount]
    exact R.fiberDimension_pos
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
  obtain ⟨j, _, hdj⟩ := Finset.mem_image.mp (hU ▸ (Finset.mem_inter.mp hz).2)
  have hjP : d j ∈ R.positive := by
    simpa only [hdj] using (Finset.mem_inter.mp hz).1
  obtain ⟨q, hqP, hqU, hPdiff, hqcone, hqcoord⟩ :=
    R.replacement_across_full_wall hR U hUcone d hU hNU j hjP
  obtain ⟨ℓ, hℓ, _⟩ := ha U hUcone
  have hrest (u : Lattice n) (hu : u ∈ R.positive) (huq : u ≠ q) :
      a u - ℓ (embed n u) = 0 := by
    have huU : u ∈ U := by
      by_contra hh
      have hm : u ∈ R.positive \ U := Finset.mem_sdiff.mpr ⟨hu, hh⟩
      rw [hPdiff] at hm
      exact huq (Finset.mem_singleton.mp hm)
    exact sub_eq_zero.mpr (hℓ u huU).symm
  have hdegree : R.degree a = a q - ℓ (embed n q) := by
    rw [R.degree_eq_sum_slack a ℓ (fun u hu => hℓ u (hNU hu))]
    rw [Finset.sum_eq_single q (fun u hu huq => hrest u hu huq)
      (fun hh => (hh hqP).elim)]
  have herase : U.erase (d j) = (Finset.univ.erase j).image d := by
    rw [hU, ← Finset.image_erase d.injective]
  rw [hdegree]
  apply bound_at_basis_wall «Σ» a bound hbound d (hU ▸ hUcone) j q
    (herase ▸ hqcone) ((hqcoord j).mp hjP) ℓ
  intro i
  exact hℓ _ (hU.symm ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

section Simultaneous

variable {ι : Type*} [Fintype ι] (T : ι → Finset (Lattice n))
variable (hT : ∀ i, T i ∈ «Σ».cones) (hne : ∀ i, (T i).Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci T) (hcard : ∀ i, 2 ≤ (T i).card)

include hcard in
/-- A positive exceptional endpoint pulls back the degree of an actual
old wall. The argument works for arbitrary real support values. -/
theorem simultaneous_positive_pullback_degree_lower_bound
    (hpure : «Σ».IsPure) (a : Lattice n → ℝ) (ha : «Σ».IsStrictSupport a)
    (bound : ℝ) (hbound : WallDegreesAtLeast «Σ» a bound)
    (S : («Σ».simultaneousSubdivision T hT hne hdisj).PrimitiveRelation)
    (hS : S.IsCombinatoriallyContractible) (i : ι)
    (hi : (∑ v ∈ T i, v) ∈ S.positive) :
    bound ≤ S.degree (simultaneousSupport T a 0) := by
  let Γ := «Σ».simultaneousSubdivision T hT hne hdisj
  let e := ∑ v ∈ T i, v
  let B := simultaneousSupport T a 0
  have hΓpure := «Σ».isPure_simultaneousSubdivision T hpure hT hne hdisj
  have hex : ∃ x ∈ S.positive, x ≠ e := by
    by_contra hn
    push Not at hn
    have hsub : S.positive ⊆ {e} := by
      intro x hx
      exact Finset.mem_singleton.mpr (hn x hx)
    exact S.primitive.2.1 (Γ.downward {e}
      (Γ.singleton_mem_of_mem_rays (S.primitive.1 hi)) S.positive hsub)
  obtain ⟨z, hzP, hze⟩ := hex
  have hcore := S.contractible_core_cone hS hzP
  obtain ⟨U, hU, hcoreU, hUcard⟩ := hΓpure _ hcore
  have heU : e ∈ U := hcoreU
    (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hze.symm, hi⟩))
  have hNU : S.negative ⊆ U := fun u hu => hcoreU (Finset.mem_union_right _ hu)
  obtain ⟨b, hb⟩ := Γ.full_cone_basis hU hUcard
  obtain ⟨j, hj, hbj⟩ := Finset.mem_image.mp (hb ▸ heU)
  obtain ⟨x, hxP, hxU, hPdiff, hxcone, hxcoords⟩ :=
    S.replacement_across_full_wall hS U hU b hb hNU j (hbj.symm ▸ hi)
  let W := U.erase e
  have heW : e ∉ W := by simp [W]
  have hUinsert : insert e W = U := Finset.insert_erase heU
  have hN : S.negative ⊆ W := by
    intro u hu
    refine Finset.mem_erase.mpr ⟨?_, hNU hu⟩
    intro hue
    have heN : e ∈ S.negative := hue ▸ hu
    exact Finset.disjoint_left.mp S.disjoint hi heN
  have hxcone' : insert x W ∈ Γ.cones := by simpa only [hbj] using hxcone
  have hxW : x ∉ W := fun hh => hxU (Finset.mem_of_mem_erase hh)
  have hWcard : W.card + 1 = n := by
    dsimp only [W]
    rw [Finset.card_erase_of_mem heU]
    have hUpos := Finset.card_pos.mpr ⟨e, heU⟩
    omega
  have hxcard : (insert x W).card = n := by
    rw [Finset.card_insert_of_notMem hxW]
    exact hWcard
  obtain ⟨hWold, hWrays, hWnone⟩ :=
    «Σ».simultaneous_wall_below_sum_old T hT hne hdisj hcard i W
      (hUinsert.symm ▸ hU) heW
  obtain ⟨p, hpT, hpW, hpcone, hpcard, hTp, hC, he⟩ :=
    «Σ».full_simultaneous_sum_endpoint_parent T hT hne hdisj hcard i W
      (hUinsert.symm ▸ hU) (hUinsert.symm ▸ hUcard) heW
  obtain ⟨q, D, hqcone, hqcard, hD, hx, hqkind⟩ :=
    «Σ».full_simultaneous_endpoint_parent T hT hne hdisj hcard W x hWnone hxcone' hxcard
  obtain ⟨d, hd⟩ := «Σ».full_cone_basis hpcone hpcard
  obtain ⟨k, hk, hdk⟩ := Finset.mem_image.mp (hd ▸ Finset.mem_insert_self p W)
  have hWbasis : W = (Finset.univ.erase k).image d := by
    rw [Finset.image_erase d.injective, ← hd, hdk,
      Finset.erase_insert_eq_erase, Finset.erase_eq_of_notMem hpW]
  have hBwall (u : Lattice n) (hu : u ∈ W) : B u = a u :=
    «Σ».simultaneousSupport_old T hT hcard a 0 u (hWrays hu)
  have hinj := «Σ».simultaneous_sum_rays_injective T hT hdisj
  have hBe : B e = a p + ∑ u ∈ (T i).erase p, a u := by
    change simultaneousSupport T a 0 (∑ v ∈ T i, v) = _
    rw [simultaneousSupport_at_sum T hinj, Pi.zero_apply, sub_zero,
      ← Finset.add_sum_erase (T i) a hpT]
  have hBx : B x = a q + ∑ u ∈ D, a u := by
    rcases hqkind with ⟨hxold, hqx, hDempty⟩ | ⟨l, hxsum, hql, rfl⟩
    · change simultaneousSupport T a 0 x = _
      rw [«Σ».simultaneousSupport_old T hT hcard a 0 x hxold,
        hqx, hDempty, Finset.sum_empty, add_zero]
    · change simultaneousSupport T a 0 x = _
      rw [hxsum, simultaneousSupport_at_sum T hinj, Pi.zero_apply, sub_zero,
        ← Finset.add_sum_erase (T l) a hql]
  obtain ⟨ℓ, hℓ, _⟩ := ha _ hpcone
  have hℓW (u : Lattice n) (hu : u ∈ (Finset.univ.erase k).image d) :
      ℓ (embed n u) = a u :=
    hℓ u (hd.symm ▸ Finset.image_subset_image (Finset.erase_subset k Finset.univ) hu)
  have hℓk : ℓ (embed n (d k)) = a (d k) :=
    hℓ _ (hd.symm ▸ Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩)
  have hcoord := S.opposite_old_coordinate_of_two_sum_rays d k ((T i).erase p) D q e x
    (hWbasis ▸ hC) (hWbasis ▸ hD)
    (by simpa only [hdk] using he) hx hi
    (hWbasis ▸ hN) (by simpa only [← hWbasis, hUinsert] using hPdiff)
  have hdegree := S.degree_pullback_two_sum_rays a B W ((T i).erase p) D p q e x
    hC hD he hx hN (by simpa only [hUinsert] using hPdiff)
    hBwall hBe hBx ℓ (fun u hu => hℓW u (hWbasis ▸ hu))
    (by simpa only [hdk] using hℓk)
  rw [hdegree]
  apply bound_at_basis_wall «Σ» a bound hbound d (hd ▸ hpcone) k q
    (hWbasis ▸ hqcone) hcoord ℓ
  intro l
  exact hℓ _ (hd.symm ▸ Finset.mem_image.mpr ⟨l, Finset.mem_univ l, rfl⟩)

end Simultaneous

section Selected

variable {ι : Type*} [Fintype ι] (R : ι → «Σ».PrimitiveRelation)
variable (hne : ∀ i, (R i).negative.Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci (fun i => (R i).negative))

/-- The original degree threshold survives a positive selected divisor,
including selected divisors that were already of codimension one. -/
theorem selected_positive_pullback_degree_lower_bound
    (hpure : «Σ».IsPure) (a : Lattice n → ℝ) (ha : «Σ».IsStrictSupport a)
    (bound : ℝ) (hbound : WallDegreesAtLeast «Σ» a bound)
    (S : («Σ».selectedFan R hne hdisj).PrimitiveRelation)
    (hS : S.IsCombinatoriallyContractible)
    (hpositive : ∃ i : ι, «Σ».selectedRay R i ∈ S.positive) :
    (bound : ℝ) ≤ S.degree («Σ».selectedPullback R a) := by
  let T := «Σ».selectedStarFocus R
  have hT (i : «Σ».BlowupIndices R) : T i ∈ «Σ».cones := (R i).negative_cone
  have hTne (i : «Σ».BlowupIndices R) : (T i).Nonempty := hne i
  have hTd := «Σ».selectedStarFocus_disjoint R hdisj
  have hTc (i : «Σ».BlowupIndices R) : 2 ≤ (T i).card := i.property
  by_cases hex : ∃ i : «Σ».BlowupIndices R, «Σ».selectedRay R i ∈ S.positive
  · obtain ⟨i, hi⟩ := hex
    exact simultaneous_positive_pullback_degree_lower_bound «Σ» T hT hTne hTd hTc
      hpure a ha bound hbound S hS i hi
  · have hnone (i : «Σ».BlowupIndices R) : (∑ v ∈ T i, v) ∉ S.positive := by
      intro hh
      exact hex ⟨i, hh⟩
    have hnotfocus (i : «Σ».BlowupIndices R) : S.positive ≠ T i := by
      intro hfocus
      obtain ⟨j, hj⟩ := hpositive
      have hjN : «Σ».selectedRay R j ∈ (R i).negative := by
        change «Σ».selectedRay R j ∈ T i
        exact hfocus ▸ hj
      by_cases hji : j = (i : ι)
      · subst j
        have hOld := «Σ».ray_mem_of_mem_cone (R i).negative_cone hjN
        exact «Σ».sum_rays_not_mem_rays (R i).negative_cone i.property hOld
      · exact «Σ».selected_ray_not_negative_of_ne R hdisj j i hji hjN
    obtain ⟨Q, hQP, hQ, hdeg⟩ :=
      «Σ».simultaneous_contractible_pushdown T hT hTne hTd hTc S hS hnone hnotfocus
    have hdegree : S.degree («Σ».selectedPullback R a) =
        Q.degree a := by
      change S.degree (simultaneousSupport T a 0) = _
      rcases hdeg with h | ⟨i, hi, h⟩
      · exact h _ 0
      · have hh := h a
          (0 : «Σ».BlowupIndices R → ℝ)
        rw [Pi.zero_apply, mul_zero, add_zero] at hh
        exact hh
    rw [hdegree]
    exact contractible_degree_lower_bound «Σ» hpure a ha bound hbound Q hQ

end Selected

section CorrectedNef

variable {ι : Type*} [Fintype ι] (R : ι → «Σ».PrimitiveRelation)
variable (hR : ∀ i, (R i).IsCombinatoriallyContractible)
variable (hne : ∀ i, (R i).negative.Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci (fun i => (R i).negative))

include hR in
/-- Proposition 5.2's corrected support is genuinely nef. The family is
the finite family of activated old contractible relations; the exact
real quotient construction supplies the displayed scalar repair and budgets. -/
theorem outside_side_two_corrected_isNef
    (hpure : «Σ».IsPure) (A : Lattice n → ℤ)
    (hA : «Σ».IsStrictSupport (fun u => (A u : ℝ)))
    (a : Lattice n → ℝ) (ha : «Σ».IsStrictSupport a)
    (hbound : WallDegreesAtLeast «Σ» a n)
    (σ D : Finset (Lattice n)) (hσ : σ ∈ «Σ».cones) (hDσ : D ⊆ σ)
    (houtside : ∀ i, ¬ (R i).negative ⊆ σ)
    (τ : ι → ℝ) (hτ0 : ∀ i, 0 ≤ τ i)
    (hτfiber : ∀ i, τ i ≤ 2 * ((R i).fiberDimension : ℝ) - n)
    (hτbudget : ∀ i, τ i ≤ 2 * ((D ∩ (R i).positive).card : ℝ) -
      2 * (((R i).negative ∩ D).card : ℝ) - n)
    (hrepair : ∀ i, 0 ≤
      (R i).degree (fun v => a v -
        2 * (if v ∈ D then 1 else 0)) +
      ((R i).minimumCoefficient (hne i) : ℝ) * τ i)
    (hinactive : ∀ Q : «Σ».PrimitiveRelation, Q.IsCombinatoriallyContractible →
      (∀ i, Q.positive ≠ (R i).positive) →
      0 ≤ Q.degree (fun v => a v -
        2 * (if v ∈ D then 1 else 0))) :
    («Σ».selectedFan R hne hdisj).IsNef
      (simultaneousSupport (fun i => (R i).negative)
        (fun v => a v - 2 * (if v ∈ D then 1 else 0)) τ) := by
  let Γ := «Σ».selectedFan R hne hdisj
  let F := simultaneousSupport (fun i => (R i).negative)
    (fun v => a v - 2 * (if v ∈ D then 1 else 0)) τ
  let u := «Σ».selectedCorrectionWeight R 0 2 D τ
  have hD := «Σ».outside_cone_avoids_selected_rays R hσ hDσ houtside
  have hformula : F = fun v => «Σ».selectedPullback R a v -
      2 * (if v ∈ D then 1 else 0) -
      ∑ i, if v = «Σ».selectedRay R i then u i else 0 := by
    simpa only [F, sub_zero] using
      «Σ».selected_support_coefficient_formula R hne hdisj a 0 2 D hD τ
  have hu (i : ι) : u i = 2 * (((R i).negative ∩ D).card : ℝ) + τ i := by
    simp only [u, selectedCorrectionWeight, zero_mul, zero_add]
  have hk (i : ι) : (((R i).negative ∩ D).card : ℝ) + 1 ≤ (R i).negative.card := by
    exact_mod_cast «Σ».outside_focus_selection_card_bound R hDσ houtside i
  have hdim (i : ι) : (n : ℝ) = (R i).fiberDimension + (R i).negative.card +
      «Σ».selectedBaseDimension R i := by exact_mod_cast «Σ».selected_dimension_eq R hR i
  have hΓpure : Γ.IsPure := «Σ».isPure_simultaneousSubdivision
    («Σ».selectedStarFocus R) hpure (fun i => (R i).negative_cone)
    (fun i => hne i) («Σ».selectedStarFocus_disjoint R hdisj)
  obtain ⟨H, hH⟩ := «Σ».exists_integral_strictSupport_simultaneousSubdivision
    («Σ».selectedStarFocus R) (fun i => (R i).negative_cone)
    (fun i => hne i) («Σ».selectedStarFocus_disjoint R hdisj)
    (fun i => i.property) A hA
  apply (Γ.isNef_iff_extremal_primitive_nonneg hΓpure H hH F).mpr
  intro S hSext
  have hS := S.combinatoriallyContractible_of_extremal hSext
  by_cases hex : ∃ i, «Σ».selectedRay R i ∈ S.positive
  · obtain ⟨i, hi⟩ := hex
    have hB := selected_positive_pullback_degree_lower_bound «Σ» R hne hdisj
      hpure a ha n hbound S hS ⟨i, hi⟩
    by_cases hexj : ∃ j, j ≠ i ∧ «Σ».selectedRay R j ∈ S.positive
    · obtain ⟨j, hji, hj⟩ := hexj
      have hij := hji.symm
      have hdeg := «Σ».selected_two_positive_degree_bound R hne hdisj S hS i j hij hi hj
        («Σ».selectedPullback R a) (n : ℝ) 0 2 le_rfl hB D hD u
      have hdeg' : (n : ℝ) + 2 * S.negativeWeightOn D - u i - u j ≤ S.degree F := by
        simpa only [hformula, sub_zero, mul_zero, zero_mul, add_zero] using hdeg
      rw [hu i, hu j] at hdeg'
      have hfirst : 2 * ((«Σ».selectedBaseDimension R i : ℝ) +
          «Σ».selectedBaseDimension R j) + 4 - n ≤ S.degree F := by
        have hns := S.negativeWeightOn_nonneg D
        have hki := hk i
        have hkj := hk j
        have hti := hτfiber i
        have htj := hτfiber j
        have hdi := hdim i
        have hdj := hdim j
        linarith
      have hweight := «Σ».selected_pair_negative_weight_bound R hR hne hdisj
        hpure S hS i j hij hi hj D ((Finset.card_le_card hDσ).trans («Σ».card_cone_le hσ))
      have hsecond : (n : ℝ) - 2 * ((«Σ».selectedBaseDimension R i : ℝ) +
          «Σ».selectedBaseDimension R j) - 2 ≤ S.degree F := by
        have hti := hτbudget i
        have htj := hτbudget j
        linarith
      exact zero_le_one.trans (outside_box_two_positive_bound n
        ((«Σ».selectedBaseDimension R i : ℝ) + «Σ».selectedBaseDimension R j)
        (S.degree F) hfirst hsecond)
    · have hother : ∀ j, j ≠ i → «Σ».selectedRay R j ∉ S.positive := by
        intro j hji hj
        exact hexj ⟨j, hji, hj⟩
      have hdeg := «Σ».selected_one_positive_degree_bound R hR hne hdisj S hS i hi hother
        («Σ».selectedPullback R a) (n : ℝ) 0 2 le_rfl (by norm_num) hB D hD u
      have hdeg' : (n : ℝ) - 2 * ((«Σ».selectedBaseDimension R i : ℝ) + 1) - u i ≤
          S.degree F := by
        simpa only [hformula, sub_zero, mul_zero, zero_mul] using hdeg
      rw [hu i] at hdeg'
      have hki := hk i
      have hti := hτfiber i
      have hdi := hdim i
      linarith
  · have hnone : ∀ i, «Σ».selectedRay R i ∉ S.positive := by
      simpa only [not_exists] using hex
    exact «Σ».selected_no_positive_degree_nonneg R hR hne hdisj
      (fun v => a v - 2 * (if v ∈ D then 1 else 0)) τ hτ0 hrepair
      (fun Q hQ hpos hother => hinactive Q hQ hother) S hS hnone

end CorrectedNef

/-- The activated family is chosen from all contractible primitive relations.
The real correction is the exact quotient of the deficit by the least
normal coefficient; its construction requires no integrality of `a`. -/
theorem exists_outside_side_two_correction
    (hpure : «Σ».IsPure) (A : Lattice n → ℤ)
    (hA : «Σ».IsStrictSupport (fun u => (A u : ℝ)))
    (a : Lattice n → ℝ) (ha : «Σ».IsStrictSupport a)
    (hbound : WallDegreesAtLeast «Σ» a n)
    (σ D : Finset (Lattice n)) (hσ : σ ∈ «Σ».cones) (hDσ : D ⊆ σ)
    (houtside : ∀ Q : «Σ».PrimitiveRelation, Q.IsCombinatoriallyContractible →
      Q.degree a < 2 * (Q.fiberDimension : ℝ) → ¬ Q.negative ⊆ σ) :
    ∃ (Γ : SmoothCompleteFan n) (F : Lattice n → ℝ),
      Γ.IsNef F ∧ «Σ».rays ⊆ Γ.rays ∧ σ ∈ Γ.cones ∧
      (∀ v ∈ σ, F v = a v - 2 * (if v ∈ D then 1 else 0)) ∧
      (∀ v ∈ «Σ».rays, F v ≤ a v - 2 * (if v ∈ D then 1 else 0)) := by
  let b : Lattice n → ℝ := fun v => a v - 2 * (if v ∈ D then 1 else 0)
  let test : «Σ».PrimitiveRelation → Prop := fun Q => Q.degree b < 0
  let R := «Σ».selectionRelation test
  have hR (i : «Σ».selectedPrimitiveCollections test) :
      (R i).IsCombinatoriallyContractible := «Σ».selectionRelation_contractible test i
  have hneg (i : «Σ».selectedPrimitiveCollections test) : (R i).degree b < 0 :=
    «Σ».selectionRelation_test test i
  have hdegree (Q : «Σ».PrimitiveRelation) : Q.degree b = Q.degree a -
      2 * (((D ∩ Q.positive).card : ℝ) - Q.negativeWeightOn D) := by
    have he : b = a - (2 : ℝ) • (fun v => if v ∈ D then 1 else 0) := by
      funext v
      simp only [b, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [he, Q.degree_sub, Q.degree_smul, Q.degree_indicator,
      Finset.inter_comm Q.positive D]
  have hobs (i : «Σ».selectedPrimitiveCollections test) :
      (R i).degree a < 2 * ((R i).fiberDimension : ℝ) := by
    have hn := hneg i
    rw [hdegree] at hn
    have hc : ((D ∩ (R i).positive).card : ℝ) ≤ (R i).fiberDimension := by
      exact_mod_cast «Σ».selection_positive_card_le_fiberDimension hσ hDσ (R i)
    have hw := (R i).negativeWeightOn_nonneg D
    linarith
  have hlarge (i : «Σ».selectedPrimitiveCollections test) : n < 2 * (R i).fiberDimension := by
    have hd := contractible_degree_lower_bound «Σ» hpure a ha n hbound (R i) (hR i)
    exact_mod_cast hd.trans_lt (hobs i)
  have hdisj : «Σ».PairwiseDisjointFoci (fun i => (R i).negative) :=
    «Σ».selectionRelation_disjoint_of_large hpure test hlarge
  have hout (i : «Σ».selectedPrimitiveCollections test) : ¬ (R i).negative ⊆ σ :=
    houtside (R i) (hR i) (hobs i)
  have hne (i : «Σ».selectedPrimitiveCollections test) : (R i).negative.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hh
    apply hout i
    rw [hh]
    exact Finset.empty_subset _
  let τ : «Σ».selectedPrimitiveCollections test → ℝ :=
    fun i => -(R i).degree b / ((R i).minimumCoefficient (hne i) : ℝ)
  have hmin (i : «Σ».selectedPrimitiveCollections test) :
      (1 : ℝ) ≤ (R i).minimumCoefficient (hne i) := by
    exact_mod_cast ((R i).minimumCoefficient_spec (hne i)).1
  have hτ0 (i : «Σ».selectedPrimitiveCollections test) : 0 ≤ τ i :=
    div_nonneg (neg_nonneg.mpr (hneg i).le) (zero_le_one.trans (hmin i))
  have hτle (i : «Σ».selectedPrimitiveCollections test) : τ i ≤ -(R i).degree b := by
    have hm : (0 : ℝ) < (R i).minimumCoefficient (hne i) := zero_lt_one.trans_le (hmin i)
    apply (div_le_iff₀ hm).mpr
    have hd := neg_nonneg.mpr (hneg i).le
    nlinarith [hmin i]
  have hbudget (i : «Σ».selectedPrimitiveCollections test) : τ i ≤
      2 * ((D ∩ (R i).positive).card : ℝ) -
        2 * (((R i).negative ∩ D).card : ℝ) - n := by
    apply (hτle i).trans
    rw [hdegree]
    have hd := contractible_degree_lower_bound «Σ» hpure a ha n hbound (R i) (hR i)
    have hw := (R i).card_negative_inter_le_weight D
    linarith
  have hfiber (i : «Σ».selectedPrimitiveCollections test) :
      τ i ≤ 2 * ((R i).fiberDimension : ℝ) - n := by
    have hh := hbudget i
    have hc : ((D ∩ (R i).positive).card : ℝ) ≤ (R i).fiberDimension := by
      exact_mod_cast «Σ».selection_positive_card_le_fiberDimension hσ hDσ (R i)
    have hk : (0 : ℝ) ≤ ((R i).negative ∩ D).card := Nat.cast_nonneg _
    linarith
  have hrepair (i : «Σ».selectedPrimitiveCollections test) :
      0 ≤ (R i).degree b + ((R i).minimumCoefficient (hne i) : ℝ) * τ i := by
    have hm : ((R i).minimumCoefficient (hne i) : ℝ) ≠ 0 :=
      ne_of_gt (zero_lt_one.trans_le (hmin i))
    simp only [τ, mul_div_cancel₀ _ hm, add_neg_cancel, le_refl]
  have hinactive (Q : «Σ».PrimitiveRelation) (hQ : Q.IsCombinatoriallyContractible)
      (hother : ∀ i : «Σ».selectedPrimitiveCollections test, Q.positive ≠ (R i).positive) :
      0 ≤ Q.degree b := by
    by_contra hh
    have ht : test Q := lt_of_not_ge hh
    have hcongr : ∀ Q S : «Σ».PrimitiveRelation,
        Q.positive = S.positive → (test Q ↔ test S) := by
      intro Q S hpos
      change Q.degree b < 0 ↔ S.degree b < 0
      rw [Q.degree_unique S hpos b]
    obtain ⟨i, hi⟩ := («Σ».selectionRelation_exhaustive test hcongr Q).mpr ⟨hQ, ht⟩
    exact hother i hi
  let Γ := «Σ».selectedFan R hne hdisj
  let F := simultaneousSupport (fun i => (R i).negative) b τ
  have hF : Γ.IsNef F := outside_side_two_corrected_isNef «Σ» R hR hne hdisj
    hpure A hA a ha hbound σ D hσ hDσ hout τ hτ0 hfiber hbudget hrepair hinactive
  refine ⟨Γ, F, hF, «Σ».old_rays_subset_selected R hne hdisj,
    «Σ».outside_cone_mem_selected R hne hdisj hσ hout, ?_, ?_⟩
  · intro v hv
    exact «Σ».selected_support_eq_old_on_outside_cone R b τ hσ hout hv
  · intro v hv
    exact «Σ».selected_support_le_old_on_rays R hne hdisj b τ hτ0 hv

/-- **Proposition 5.2 for arbitrary real ample support.** A real strict
support with all invariant degrees at least the dimension contains the
full side-two primitive corner box at every Cartier vertex outside the
obstructing loci. Purity and an integral projectivity witness are derived
internally. Both the vertex and the box directions are the actual Cartier
point and dual integral cone basis. -/
theorem proposition_5_2
    (a : Lattice n → ℝ) (ha : «Σ».IsStrictSupport a)
    (hbound : WallDegreesAtLeast «Σ» a n)
    (s : «Σ».fullCones)
    (houtside : ∀ Q : «Σ».PrimitiveRelation, Q.IsCombinatoriallyContractible →
      Q.degree a < 2 * (Q.fiberDimension : ℝ) → ¬ Q.negative ⊆ s.val)
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 2) :
    «Σ».cartierPoint a s + ∑ i, t i • «Σ».cartierBasis s i ∈ «Σ».fanPolytope a := by
  have hpure : «Σ».IsPure := «Σ».isPure_of_complete
  obtain ⟨A, hA⟩ := «Σ».exists_integral_strictSupport_of_real a ha
  let d := «Σ».fullConeBasis s
  have hd : Finset.univ.image d = s.val := («Σ».fullConeBasis_ray_set s).symm
  apply «Σ».box_mem_fanPolytope_of_vertices a («Σ».cartierPoint a s)
    («Σ».cartierBasis s) 2 (by norm_num) ?_ t ht
  intro I
  let D := I.image d
  have hD : D ⊆ s.val := by
    rw [← hd]
    exact Finset.image_subset_image (Finset.subset_univ I)
  obtain ⟨Γ, F, hF, hrays, hΓs, hcoeff, hle⟩ :=
    exists_outside_side_two_correction «Σ» hpure A hA a ha hbound s.val D
      (Finset.mem_filter.mp s.property).1 hD houtside
  apply «Σ».box_corner_mem_of_refinement_nef Γ hrays a F hF d
    (hd.symm ▸ hΓs) («Σ».cartierPoint a s) («Σ».cartierPoint_active a s) I 2
  · intro i
    have hi : d i ∈ s.val := by
      rw [← hd]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have hh := hcoeff (d i) hi
    have hiD : d i ∈ D ↔ i ∈ I := by
      simp only [D, Finset.mem_image, d.injective.eq_iff]
      simp
    simpa only [hiD] using hh
  · intro u hu
    have hh := hle u hu
    have hnonneg : 0 ≤ 2 * (if u ∈ D then (1 : ℝ) else 0) := by
      split_ifs <;> norm_num
    linarith

end ToricQuadratic.RealSupport

end
