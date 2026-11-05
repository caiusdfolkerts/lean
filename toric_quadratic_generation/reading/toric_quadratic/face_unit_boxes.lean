module

public import ToricQuadratic.UnitCornerBoxes

@[expose] public section

/-!
# Unit corner boxes pass to saturated face charts

The proof compares genuine edge endpoints. Saturation preserves lattice
length, so each primitive direction in the face maps to one of the
ambient primitive edge directions, with no change of scale. Zero extension
of the corresponding box coordinates gives the desired containment.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical Pointwise

namespace LatticePolytope

/-- Literal unit corner boxes are inherited by a smooth saturated affine
chart of an actual face. The cut premise says that intersecting the ambient
polytope with the affine chart range recovers the face. -/
theorem UnitCornerBoxes.face_chart {d n : ℕ} {P : LatticePolytope n}
    (hP : P.UnitCornerBoxes) (F : Set (Ambient n))
    (hF : IsExtreme ℝ P.carrier F) (Q : LatticePolytope d)
    (hQ : Q.Smooth) (e : IntegralAffineEmbedding d n)
    (heF : e.realMap '' Q.carrier = F)
    (hcut : ∀ x ∈ P.carrier, x ∈ Set.range e.realMap → x ∈ F) :
    Q.UnitCornerBoxes := by
  intro v hv
  obtain ⟨vZ, c, l, hvZ, hl, hallQ⟩ := hQ v hv
  have hvF : e.realMap v ∈ F.extremePoints ℝ := by
    rw [← heF]
    exact PaperVerification.ToricExchange.affine_mem_extremePoints_image
      e.realMap e.realMap_injective hv
  have hvP : e.realMap v ∈ P.carrier.extremePoints ℝ :=
    hF.extremePoints_subset_extremePoints hvF
  obtain ⟨wZ, b, L, hwZ, hL, hallP, hbox⟩ := hP (e.realMap v) hvP
  have horigin : e.latticeMap vZ = wZ := by
    apply embed_injective n
    rw [e.embed_latticeMap, hvZ, hwZ]
  have hmapedge (i : Fin d) :
      P.IsEdge (e.realMap v) (e.realMap (embed d (vZ + (l i : ℤ) • c i))) := by
    refine ⟨fun hh => (hl i).2.1 (e.realMap_injective hh), ?_⟩
    have hh := affine_isExtreme_image e.realMap e.realMap_injective (hl i).2.2
    rw [heF, image_segment] at hh
    exact hF.trans hh
  choose j hj using fun i : Fin d => hallP _ (hmapedge i)
  have hendpoint (i : Fin d) :
      e.latticeMap (vZ + (l i : ℤ) • c i) = wZ + (L (j i) : ℤ) • b (j i) := by
    apply embed_injective n
    rw [e.embed_latticeMap]
    exact hj i
  have hlength (i : Fin d) : l i = L (j i) := by
    calc
      l i = latticeLength vZ (vZ + (l i : ℤ) • c i) :=
        (latticeLength_basis_direction vZ c i (l i)).symm
      _ = latticeLength (e.latticeMap vZ) (e.latticeMap (vZ + (l i : ℤ) • c i)) :=
        (e.latticeLength_latticeMap _ _).symm
      _ = latticeLength wZ (wZ + (L (j i) : ℤ) • b (j i)) := by
        rw [horigin, hendpoint i]
      _ = L (j i) := latticeLength_basis_direction wZ b (j i) (L (j i))
  have hdir (i : Fin d) : e.linear (c i) = b (j i) := by
    have hh := hendpoint i
    have hbase : e.origin + e.linear vZ = wZ := horigin
    simp only [IntegralAffineEmbedding.latticeMap, map_add, map_zsmul] at hh
    rw [← add_assoc, hbase, ← hlength i] at hh
    have hs : (l i : ℤ) • e.linear (c i) = (l i : ℤ) • b (j i) :=
      add_left_cancel hh
    ext k
    have hc := congrFun hs k
    simp only [Pi.smul_apply, smul_eq_mul] at hc
    exact mul_left_cancel₀ (by exact_mod_cast (hl i).1.ne') hc
  have hjinj : Function.Injective j := by
    intro i k hik
    apply c.injective
    apply e.linear_injective
    rw [hdir i, hdir k, hik]
  have hdirR (i : Fin d) :
      e.realLinear (integralBasisReal c i) = integralBasisReal b (j i) := by
    rw [integralBasisReal_apply, ← e.compatible, hdir i, integralBasisReal_apply]
  refine ⟨vZ, c, l, hvZ, hl, hallQ, ?_⟩
  intro t ht
  let u : Fin n → ℝ := fun k => ∑ i : Fin d, if j i = k then t i else 0
  have hu_selected (i : Fin d) : u (j i) = t i := by
    simp only [u, hjinj.eq_iff]
    simp
  have hu (k : Fin n) : 0 ≤ u k ∧ u k ≤ 1 := by
    by_cases hk : ∃ i, j i = k
    · obtain ⟨i, rfl⟩ := hk
      rw [hu_selected]
      exact ht i
    · have hzero : u k = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        exact if_neg (fun hh => hk ⟨i, hh⟩)
      rw [hzero]
      norm_num
  have hsum : (∑ k, u k • integralBasisReal b k) =
      ∑ i, t i • integralBasisReal b (j i) := by
    simp only [u, Finset.sum_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    simp [ite_smul]
  have hmap : e.realMap (v + ∑ i, t i • integralBasisReal c i) =
      e.realMap v + ∑ k, u k • integralBasisReal b k := by
    simp only [IntegralAffineEmbedding.realMap_apply, map_add, map_sum, map_smul, hdirR]
    rw [hsum]
    abel
  have hmemP : e.realMap (v + ∑ i, t i • integralBasisReal c i) ∈ P.carrier := by
    rw [hmap]
    exact hbox u hu
  have hmemF := hcut _ hmemP ⟨v + ∑ i, t i • integralBasisReal c i, rfl⟩
  rw [← heF] at hmemF
  obtain ⟨z, hz, hez⟩ := hmemF
  have hzv := e.realMap_injective hez
  simpa only [hzv] using hz

end LatticePolytope

end PaperVerification.ToricGeometry
