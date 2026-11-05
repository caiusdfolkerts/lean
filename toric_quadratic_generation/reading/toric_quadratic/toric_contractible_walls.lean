module

public import PaperVerification.ToricWallUniqueness

@[expose] public section

/-!
# Contractible relations at an actual full cone

The omitted positive ray is recovered from the primitive equation in the
full cone's integral basis. Its coordinates equal `-1` exactly on the
positive rays of the relation. Replacement across any such wall is an
actual cone of the fan.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

theorem basis_coord_of_mem_ray_set {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n)
    {v : Lattice n} (hv : v ∈ Finset.univ.image b) :
    b.coord i v = if v = b i then 1 else 0 := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self_apply]
  by_cases hji : j = i
  · simp [hji]
  · simp [hji, b.injective.ne hji]

namespace SmoothCompleteFan.PrimitiveRelation

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} (R : «Σ».PrimitiveRelation)

theorem omitted_positive_coordinates
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (U : Finset (Lattice n))
    (hU : U = Finset.univ.image b) (hNU : R.negative ⊆ U)
    (w : Lattice n) (hw : w ∈ R.positive) (hwU : w ∉ U)
    (hPdiff : R.positive \ U = {w}) (i : Fin n) :
    b.coord i w + (if b i ∈ R.positive then 1 else 0) =
      if b i ∈ R.negative then (R.coefficient (b i) : ℤ) else 0 := by
  have hbiU : b i ∈ U := hU.symm ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hbiw : b i ≠ w := fun h => hwU (h ▸ hbiU)
  have hrestU : R.positive.erase w ⊆ U := by
    intro v hv
    by_contra hvU
    have hvdiff : v ∈ R.positive \ U :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase hv, hvU⟩
    rw [hPdiff] at hvdiff
    exact (Finset.mem_erase.mp hv).1 (Finset.mem_singleton.mp hvdiff)
  have hcoord (v : Lattice n) (hv : v ∈ U) :
      b.coord i v = if v = b i then 1 else 0 :=
    basis_coord_of_mem_ray_set b i (hU ▸ hv)
  have hrest : (∑ v ∈ R.positive.erase w, b.coord i v) =
      if b i ∈ R.positive then 1 else 0 := by
    calc
      (∑ v ∈ R.positive.erase w, b.coord i v) =
          ∑ v ∈ R.positive.erase w, if v = b i then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro v hv
        exact hcoord v (hrestU hv)
      _ = if b i ∈ R.positive then 1 else 0 := by simp [hbiw]
  have hneg : (∑ v ∈ R.negative, (R.coefficient v : ℤ) * b.coord i v) =
      if b i ∈ R.negative then (R.coefficient (b i) : ℤ) else 0 := by
    calc
      (∑ v ∈ R.negative, (R.coefficient v : ℤ) * b.coord i v) =
          ∑ v ∈ R.negative, if v = b i then (R.coefficient (b i) : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [hcoord v (hNU hv)]
        split_ifs with h
        · simp [h]
        · simp
      _ = if b i ∈ R.negative then (R.coefficient (b i) : ℤ) else 0 := by simp
  have he := congrArg (b.coord i) R.equation
  simp only [map_sum, map_smul, smul_eq_mul] at he
  rw [← Finset.add_sum_erase R.positive (fun v => b.coord i v) hw, hrest, hneg] at he
  exact he

theorem positive_iff_omitted_coordinate_neg_one
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (U : Finset (Lattice n))
    (hU : U = Finset.univ.image b) (hNU : R.negative ⊆ U)
    (w : Lattice n) (hw : w ∈ R.positive) (hwU : w ∉ U)
    (hPdiff : R.positive \ U = {w}) (i : Fin n) :
    b i ∈ R.positive ↔ b.repr w i = -1 := by
  have hc := R.omitted_positive_coordinates b U hU hNU w hw hwU hPdiff i
  change b.repr w i + _ = _ at hc
  constructor
  · intro hi
    have hiN : b i ∉ R.negative := fun h => Finset.disjoint_left.mp R.disjoint hi h
    rw [if_pos hi, if_neg hiN] at hc
    omega
  · intro hcoord
    by_contra hi
    rw [if_neg hi, hcoord, add_zero] at hc
    have hnonneg : (0 : ℤ) ≤
        if b i ∈ R.negative then (R.coefficient (b i) : ℤ) else 0 := by
      split_ifs
      · exact Int.natCast_nonneg _
      · exact le_rfl
    omega

/-- The full contraction replacement produces the actual opposite cone at
each positive wall. The omitted ray is characterized simultaneously by all
its basis coordinates. -/
theorem replacement_across_full_wall (hR : R.IsCombinatoriallyContractible)
    (U : Finset (Lattice n)) (hUcone : U ∈ «Σ».cones)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (hU : U = Finset.univ.image b)
    (hNU : R.negative ⊆ U) (j : Fin n) (hjP : b j ∈ R.positive) :
    ∃ w ∈ R.positive, w ∉ U ∧
      R.positive \ U = {w} ∧
      insert w (U.erase (b j)) ∈ «Σ».cones ∧
      ∀ i : Fin n, b i ∈ R.positive ↔ b.repr w i = -1 := by
  have hcard : U.card = n := by
    rw [hU, Finset.card_image_of_injective _ b.injective, Finset.card_fin]
  obtain ⟨w, hw, hPdiff⟩ := R.exists_unique_omitted_positive hR hUcone hcard hNU
  have hwU : w ∉ U := by
    have h := hPdiff.symm ▸ Finset.mem_singleton_self w
    exact (Finset.mem_sdiff.mp h).2
  have hjU : b j ∈ U := hU.symm ▸ Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
  have hwj : w ≠ b j := fun h => hwU (h.symm ▸ hjU)
  let ν := U \ (R.positive ∪ R.negative)
  have hνU : ν ⊆ U := Finset.sdiff_subset
  have hν : ν ∈ «Σ».cones := «Σ».downward U hUcone ν hνU
  have hdisj : Disjoint ν (R.positive ∪ R.negative) := by
    apply Finset.disjoint_left.mpr
    intro v hv hvPN
    exact (Finset.mem_sdiff.mp hv).2 hvPN
  have hNν : R.negative ∪ ν ∈ «Σ».cones :=
    «Σ».downward U hUcone _ (Finset.union_subset hNU hνU)
  have hreplace := hR ν hν hdisj hNν (b j) hjP
  have hjN : b j ∉ R.negative := fun h => Finset.disjoint_left.mp R.disjoint hjP h
  have hsets : R.positive.erase (b j) ∪ R.negative ∪ ν = insert w (U.erase (b j)) := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with hv | hv
      · rcases Finset.mem_union.mp hv with hvP | hvN
        · by_cases hvU : v ∈ U
          · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hvP).1, hvU⟩)
          · have hdiff : v ∈ R.positive \ U :=
              Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase hvP, hvU⟩
            rw [hPdiff] at hdiff
            exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hdiff))
        · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr
            ⟨fun hvj => hjN (hvj ▸ hvN), hNU hvN⟩)
      · have hvj : v ≠ b j := by
          intro hvj
          exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_union_left _ (hvj.symm ▸ hjP))
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hvj, hνU hv⟩)
    · intro hv
      rcases Finset.mem_insert.mp hv with hvw | hvU
      · subst v
        exact Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwj, hw⟩))
      · obtain ⟨hvj, hvU⟩ := Finset.mem_erase.mp hvU
        by_cases hvP : v ∈ R.positive
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hvj, hvP⟩))
        · by_cases hvN : v ∈ R.negative
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ hvN)
          · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
              ⟨hvU, by simpa only [Finset.mem_union, not_or] using And.intro hvP hvN⟩)
  refine ⟨w, hw, hwU, hPdiff, hsets ▸ hreplace, ?_⟩
  exact R.positive_iff_omitted_coordinate_neg_one b U hU hNU w hw hwU hPdiff

end SmoothCompleteFan.PrimitiveRelation

end PaperVerification.ToricGeometry
