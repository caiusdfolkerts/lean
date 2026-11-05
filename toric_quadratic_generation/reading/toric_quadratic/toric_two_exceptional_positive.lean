module

public import PaperVerification.ToricFiberWalls
public import Mathlib.Tactic.Tauto

@[expose] public section

/-!
# Two positive exceptional rays: the actual wall argument

The proof uses only actual full cones, their integral bases, and neighboring
cones. A shared fiber direction would give two opposite rays at one wall.
Uniqueness forces those rays to agree, while the pair relation makes their
exceptional coordinates have opposite signs. Counting the remaining common
wall rays gives the base-dimension bound.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan.PrimitiveRelation

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} (R : «Σ».PrimitiveRelation)

/-- Replace one of the two positive rays in a neighboring wall cone.
The added ray is required to avoid the primitive relation's support; this
is later verified from its negative transverse coordinate. -/
theorem pair_transport_neighbor (hR : R.IsCombinatoriallyContractible)
    (e f : Lattice n) (hef : e ≠ f) (hpositive : R.positive = {e, f})
    (W : Finset (Lattice n)) (hW : Disjoint W R.positive)
    (hN : R.negative ⊆ W) (k z : Lattice n)
    (hk : k ∈ W) (hkN : k ∉ R.negative)
    (hzP : z ∉ R.positive) (hzN : z ∉ R.negative)
    (hzcone : insert z ((insert e W).erase k) ∈ «Σ».cones) :
    insert z ((insert f W).erase k) ∈ «Σ».cones := by
  let V := (W.erase k) \ R.negative
  let ν := insert z V
  have hNe : e ∉ R.negative := by
    intro he
    exact Finset.disjoint_left.mp R.disjoint
      (hpositive.symm ▸ Finset.mem_insert_self _ _) he
  have heW : e ∉ W := fun he => Finset.disjoint_left.mp hW he
    (hpositive.symm ▸ Finset.mem_insert_self _ _)
  have hfW : f ∉ W := fun hf => Finset.disjoint_left.mp hW hf
    (hpositive.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hke : k ≠ e := fun h => heW (h ▸ hk)
  have hkf : k ≠ f := fun h => hfW (h ▸ hk)
  have hNerase : R.negative ⊆ W.erase k := by
    intro u hu
    exact Finset.mem_erase.mpr ⟨fun h => hkN (h ▸ hu), hN hu⟩
  have hνsub : ν ⊆ insert z ((insert e W).erase k) := by
    intro u hu
    rcases Finset.mem_insert.mp hu with huz | huV
    · exact Finset.mem_insert.mpr (Or.inl huz)
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr
        ⟨(Finset.mem_erase.mp (Finset.mem_sdiff.mp huV).1).1,
          Finset.mem_insert_of_mem (Finset.mem_of_mem_erase (Finset.mem_sdiff.mp huV).1)⟩)
  have hν : ν ∈ «Σ».cones := «Σ».downward _ hzcone ν hνsub
  have hdisj : Disjoint ν (R.positive ∪ R.negative) := by
    apply Finset.disjoint_left.mpr
    intro u hu hPN
    rcases Finset.mem_insert.mp hu with huz | huV
    · subst u
      exact (Finset.mem_union.mp hPN).elim hzP hzN
    · obtain ⟨huW, huN⟩ := Finset.mem_sdiff.mp huV
      rcases Finset.mem_union.mp hPN with huP | huN'
      · exact Finset.disjoint_left.mp hW (Finset.mem_of_mem_erase huW) huP
      · exact huN huN'
  have hNν : R.negative ∪ ν ∈ «Σ».cones := by
    apply «Σ».downward _ hzcone
    apply Finset.union_subset
    · intro u hu
      exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr
        ⟨(Finset.mem_erase.mp (hNerase hu)).1, Finset.mem_insert_of_mem (hN hu)⟩)
    · exact hνsub
  have heP : e ∈ R.positive := hpositive.symm ▸ Finset.mem_insert_self _ _
  have hnew := hR ν hν hdisj hNν e heP
  have heq : R.positive.erase e ∪ R.negative ∪ ν =
      insert z ((insert f W).erase k) := by
    have hpos : R.positive.erase e = {f} := by
      rw [hpositive, Finset.erase_insert
        (by simpa only [Finset.mem_singleton] using hef)]
    rw [hpos]
    ext u
    have huN : u ∈ R.negative → u ≠ k ∧ u ∈ W := fun h =>
      Finset.mem_erase.mp (hNerase h)
    have huf : u = f → u ≠ k := by
      rintro rfl
      exact hkf.symm
    simp only [Finset.mem_union, Finset.mem_singleton,
      ν, V, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_erase]
    tauto
  exact heq ▸ hnew

/-- Two actual neighboring full bases identify the special coordinate by
a sign change. Coordinates at wall rays outside the focus are unchanged. -/
theorem pair_wall_coordinate_identities
    (e f : Lattice n) (hef : e ≠ f) (hpositive : R.positive = {e, f})
    (W : Finset (Lattice n)) (hN : R.negative ⊆ W)
    (b c : Module.Basis (Fin n) ℤ (Lattice n)) (j l : Fin n)
    (hb : insert e W = Finset.univ.image b) (hc : insert f W = Finset.univ.image c)
    (hbj : b j = e) (hcl : c l = f) (heW : e ∉ W) (hfW : f ∉ W)
    (i k : Fin n) (hik : b i = c k) (hiW : b i ∈ W) (hiN : b i ∉ R.negative) :
    c.coord l = -b.coord j ∧ c.coord k = b.coord i := by
  have hij : i ≠ j := fun h => heW (hbj ▸ (h ▸ hiW))
  have hkl : k ≠ l := by
    intro h
    exact hfW (hcl ▸ (h ▸ (hik ▸ hiW)))
  have hwall_b (u : Lattice n) (hu : u ∈ W) : b.coord j u = 0 := by
    rw [basis_coord_of_mem_ray_set b j (hb ▸ Finset.mem_insert_of_mem hu)]
    exact if_neg (show u ≠ b j from fun h => heW (hbj ▸ (h ▸ hu)))
  have hwall_c (u : Lattice n) (hu : u ∈ W) : c.coord l u = 0 := by
    rw [basis_coord_of_mem_ray_set c l (hc ▸ Finset.mem_insert_of_mem hu)]
    exact if_neg (show u ≠ c l from fun h => hfW (hcl ▸ (h ▸ hu)))
  have heq : e + f = ∑ u ∈ R.negative, (R.coefficient u : ℤ) • u := by
    simpa only [hpositive, Finset.sum_pair hef] using R.equation
  have hbf : b.coord j f = -1 := by
    have hn : (∑ u ∈ R.negative, (R.coefficient u : ℤ) * b.coord j u) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      rw [hwall_b u (hN hu), mul_zero]
    have h := congrArg (b.coord j) heq
    simp only [map_add, map_sum, map_smul, smul_eq_mul] at h
    rw [hn, ← hbj, Module.Basis.coord_apply, Module.Basis.repr_self_apply, if_pos rfl] at h
    omega
  have hce : c.coord l e = -1 := by
    have h := congrArg (c.coord l) heq
    have hn : (∑ u ∈ R.negative, (R.coefficient u : ℤ) * c.coord l u) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      rw [hwall_c u (hN hu), mul_zero]
    simp only [map_add, map_sum, map_smul, smul_eq_mul] at h
    have hcf : c.coord l f = 1 := by
      rw [← hcl, Module.Basis.coord_apply, Module.Basis.repr_self_apply, if_pos rfl]
    rw [hn, hcf] at h
    omega
  have hif : b.coord i f = 0 := by
    have hn : (∑ u ∈ R.negative, (R.coefficient u : ℤ) * b.coord i u) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      rw [basis_coord_of_mem_ray_set b i (hb ▸ Finset.mem_insert_of_mem (hN hu)),
        if_neg (show u ≠ b i from fun h => hiN (h ▸ hu)), mul_zero]
    have h := congrArg (b.coord i) heq
    simp only [map_add, map_sum, map_smul, smul_eq_mul] at h
    rw [hn, ← hbj, Module.Basis.coord_apply, Module.Basis.repr_self_apply,
      if_neg hij.symm, zero_add] at h
    exact h
  constructor
  · apply b.ext
    intro a
    by_cases haj : a = j
    · subst a
      simp only [hbj, hce, LinearMap.neg_apply]
      rw [← hbj, Module.Basis.coord_apply, Module.Basis.repr_self_apply, if_pos rfl]
    · have haw : b a ∈ W := by
        have hm : b a ∈ insert e W := hb.symm ▸ Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
        rcases Finset.mem_insert.mp hm with he | hw
        · exact (haj (b.injective (he.trans hbj.symm))).elim
        · exact hw
      simp only [hwall_c _ haw, LinearMap.neg_apply, Module.Basis.coord_apply,
        Module.Basis.repr_self_apply, if_neg haj, neg_zero]
  · apply c.ext
    intro a
    by_cases hal : a = l
    · subst a
      rw [hcl, hif, ← hcl, Module.Basis.coord_apply,
        Module.Basis.repr_self_apply, if_neg hkl.symm]
    · have haw : c a ∈ W := by
        have hm : c a ∈ insert f W := hc.symm ▸ Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
        rcases Finset.mem_insert.mp hm with he | hw
        · exact (hal (c.injective (he.trans hcl.symm))).elim
        · exact hw
      rw [basis_coord_of_mem_ray_set b i (hb ▸ Finset.mem_insert_of_mem haw), hik,
        basis_coord_of_mem_ray_set c k (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)]

/-- A common wall direction outside the pair focus cannot be a fiber
direction for both positive exceptional rays. -/
theorem pair_no_shared_fiber_direction (hR : R.IsCombinatoriallyContractible)
    (e f : Lattice n) (hef : e ≠ f) (hpositive : R.positive = {e, f})
    (W : Finset (Lattice n)) (hW : Disjoint W R.positive)
    (hN : R.negative ⊆ W)
    (b c : Module.Basis (Fin n) ℤ (Lattice n)) (j l i k : Fin n)
    (hb : insert e W = Finset.univ.image b) (hc : insert f W = Finset.univ.image c)
    (hbj : b j = e) (hcl : c l = f) (hik : b i = c k)
    (hiW : b i ∈ W) (hiN : b i ∉ R.negative)
    (z z' : Lattice n)
    (hz : insert z ((Finset.univ.erase i).image b) ∈ «Σ».cones)
    (hz' : insert z' ((Finset.univ.erase k).image c) ∈ «Σ».cones)
    (hzi : b.repr z i = -1) (hzj : 0 < b.repr z j)
    (hz'k : c.repr z' k = -1) (hz'l : 0 < c.repr z' l) : False := by
  have heW : e ∉ W := fun he => Finset.disjoint_left.mp hW he
    (hpositive.symm ▸ Finset.mem_insert_self _ _)
  have hfW : f ∉ W := fun hf => Finset.disjoint_left.mp hW hf
    (hpositive.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  obtain ⟨hl, hk⟩ := R.pair_wall_coordinate_identities e f hef hpositive W hN
    b c j l hb hc hbj hcl heW hfW i k hik hiW hiN
  have hij : i ≠ j := fun h => heW (hbj ▸ (h ▸ hiW))
  have hif : b.coord i f = 0 := by
    rw [← hk, ← hcl, Module.Basis.coord_apply, Module.Basis.repr_self_apply]
    apply if_neg
    intro h
    exact hfW (hcl ▸ (h ▸ (hik ▸ hiW)))
  have hzP : z ∉ R.positive := by
    intro h
    rcases (by simpa only [hpositive, Finset.mem_insert, Finset.mem_singleton] using h : z = e ∨ z = f) with h | h
    · rw [h, ← hbj, Module.Basis.repr_self_apply, if_neg hij.symm] at hzi
      omega
    · have hz0 : b.repr z i = 0 := by simpa only [h, Module.Basis.coord_apply] using hif
      omega
  have hzN : z ∉ R.negative := by
    intro h
    have hzU : z ∈ Finset.univ.image b := hb ▸ Finset.mem_insert_of_mem (hN h)
    have hzcoord := basis_coord_of_mem_ray_set b i hzU
    have hzne : z ≠ b i := fun he => hiN (he ▸ h)
    rw [if_neg hzne] at hzcoord
    change b.repr z i = 0 at hzcoord
    omega
  have hzactual : insert z ((insert e W).erase (b i)) ∈ «Σ».cones := by
    simpa only [Finset.image_erase b.injective, ← hb] using hz
  have htransport := R.pair_transport_neighbor hR e f hef hpositive W hW hN
    (b i) z hiW hiN hzP hzN hzactual
  have htransport' : insert z ((Finset.univ.erase k).image c) ∈ «Σ».cones := by
    simpa only [Finset.image_erase c.injective, ← hc, ← hik] using htransport
  have hzk : c.repr z k = -1 := by
    change c.coord k z = -1
    rw [hk]
    exact hzi
  have hzz' := «Σ».opposite_wall_ray_unique c k z z' htransport' hz' hzk hz'k
  have hsign : c.repr z l = -b.repr z j := by
    change c.coord l z = -b.coord j z
    rw [hl]
    rfl
  rw [← hzz'] at hz'l
  omega

/-- The common-wall counting form of Lemma 5.1(ii). The integers `d₁,d₂`
are the actual numbers of complementary wall directions in the two local
fiber configurations. -/
theorem pair_negative_card_bound_of_wall_data
    (hR : R.IsCombinatoriallyContractible)
    (e f : Lattice n) (hef : e ≠ f) (hpositive : R.positive = {e, f})
    (W : Finset (Lattice n)) (hW : Disjoint W R.positive)
    (hN : R.negative ⊆ W)
    (b c : Module.Basis (Fin n) ℤ (Lattice n)) (j l : Fin n)
    (hb : insert e W = Finset.univ.image b) (hc : insert f W = Finset.univ.image c)
    (hbj : b j = e) (hcl : c l = f)
    (F G : Finset (Fin n)) (hjF : j ∉ F) (hlG : l ∉ G)
    (d₁ d₂ : ℕ) (hFd : F.card + d₁ + 1 = n) (hGd : G.card + d₂ + 1 = n)
    (hF : ∀ i ∈ F, ∃ z : Lattice n,
      insert z ((Finset.univ.erase i).image b) ∈ «Σ».cones ∧
      b.repr z i = -1 ∧ 0 < b.repr z j)
    (hG : ∀ k ∈ G, ∃ z : Lattice n,
      insert z ((Finset.univ.erase k).image c) ∈ «Σ».cones ∧
      c.repr z k = -1 ∧ 0 < c.repr z l) :
    n ≤ R.negative.card + d₁ + d₂ + 1 := by
  let A := F.image b
  let B := G.image c
  have heW : e ∉ W := fun he => Finset.disjoint_left.mp hW he
    (hpositive.symm ▸ Finset.mem_insert_self _ _)
  have hfW : f ∉ W := fun hf => Finset.disjoint_left.mp hW hf
    (hpositive.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hAW : A ⊆ W := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hmem : b i ∈ insert e W :=
      hb.symm ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    rcases Finset.mem_insert.mp hmem with he | hw
    · exact (hjF ((b.injective (he.trans hbj.symm)) ▸ hi)).elim
    · exact hw
  have hBW : B ⊆ W := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    have hmem : c k ∈ insert f W :=
      hc.symm ▸ Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩
    rcases Finset.mem_insert.mp hmem with he | hw
    · exact (hlG ((c.injective (he.trans hcl.symm)) ▸ hk)).elim
    · exact hw
  have hcover : W \ R.negative ⊆ (W \ A) ∪ (W \ B) := by
    intro x hx
    obtain ⟨hxW, hxN⟩ := Finset.mem_sdiff.mp hx
    by_cases hxA : x ∈ A
    · by_cases hxB : x ∈ B
      · obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hxA
        obtain ⟨k, hk, hkx⟩ := Finset.mem_image.mp hxB
        obtain ⟨z, hz, hzi, hzj⟩ := hF i hi
        obtain ⟨z', hz', hz'k, hz'l⟩ := hG k hk
        have hiW : b i ∈ W := by simpa only [hix] using hxW
        have hiN : b i ∉ R.negative := by simpa only [hix] using hxN
        exact (R.pair_no_shared_fiber_direction hR e f hef hpositive W hW hN
          b c j l i k hb hc hbj hcl (hix.trans hkx.symm) hiW hiN
          z z' hz hz' hzi hzj hz'k hz'l).elim
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxW, hxB⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxW, hxA⟩)
  have hcount := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have hNcard := Finset.card_sdiff_add_card_eq_card hN
  have hAcard := Finset.card_sdiff_add_card_eq_card hAW
  have hBcard := Finset.card_sdiff_add_card_eq_card hBW
  have hAF : A.card = F.card := Finset.card_image_of_injective _ b.injective
  have hBG : B.card = G.card := Finset.card_image_of_injective _ c.injective
  have hWcard : W.card + 1 = n := by
    have h := congrArg Finset.card hb
    simpa only [Finset.card_insert_of_notMem heW,
      Finset.card_image_of_injective _ b.injective, Finset.card_fin] using h
  omega

end SmoothCompleteFan.PrimitiveRelation

end PaperVerification.ToricGeometry
