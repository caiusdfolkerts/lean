module

public import PaperVerification.ToricEdgeWallSupport

@[expose] public section

/-!
# Contractible degrees are actual lattice edge lengths

The equality is proved from the primitive lattice equation, the genuine
normal fan and the supporting values of the polytope. In particular the
degree lower bound applies to every combinatorially contractible primitive
relation, including those which need not be extremal on the original fan.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

theorem contractible_degree_at_full_cone
    (hP : P.Smooth) («Σ» : SmoothCompleteFan n)
    (hfan : «Σ».realCones = P.normalFan)
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible)
    (U : Finset (Lattice n)) (hUcone : U ∈ «Σ».cones)
    (d : Module.Basis (Fin n) ℤ (Lattice n)) (hU : U = Finset.univ.image d)
    (hNU : R.negative ⊆ U)
    (v : Lattice n) (lengths : Fin n → ℕ)
    (hedges : ∀ i, 0 < lengths i ∧ P.IsEdge (embed n v)
      (embed n (v + (lengths i : ℤ) • integralDualBasis d i)))
    (hcone : P.normalCone (embed n v) =
      (latticeRayCone (Finset.univ.image d) : Set (Ambient n)))
    (j : Fin n) (hjP : d j ∈ R.positive) :
    R.degree (fun u => (P.integralSupport u : ℝ)) = lengths j := by
  obtain ⟨e, heP, heU, hPdiff, hecone, hecoord⟩ :=
    R.replacement_across_full_wall hR U hUcone d hU hNU j hjP
  have hecoordj : d.repr e j = -1 := (hecoord j).mp hjP
  have herase : U.erase (d j) = (Finset.univ.erase j).image d := by
    rw [hU, ← Finset.image_erase d.injective]
  have heactive := P.opposite_wall_normal_at_edge_endpoint hP «Σ» hfan v d
    (hU ▸ hUcone) hcone j (lengths j) (hedges j).1 (hedges j).2 e
    (herase ▸ hecone) (by omega)
  let a : Lattice n → ℝ := fun u => (P.integralSupport u : ℝ)
  let ℓ : Ambient n →ₗ[ℝ] ℝ := -(dotProductEquiv ℝ (Fin n) (embed n v))
  have hv := (P.edge_endpoints_extreme (hedges j).2).1.1
  have hpair (u : Lattice n) :
      ℓ (embed n u) = -(dotProductEquiv ℝ (Fin n) (embed n u)) (embed n v) := by
    simp only [ℓ, LinearMap.neg_apply]
    congr 1
    change (∑ i, embed n v i * embed n u i) = ∑ i, embed n u i * embed n v i
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hsupport (u : Lattice n) (hu : u ∈ U) : ℓ (embed n u) = a u := by
    rw [hpair]
    apply (P.integralSupport_spec u (embed n v) hv).2.mpr
    rw [hcone]
    exact latticeRayCone_generator _ (hU ▸ hu)
  rw [R.degree_eq_sum_slack a ℓ (fun u hu => hsupport u (hNU hu))]
  have hrest (u : Lattice n) (hu : u ∈ R.positive) (hue : u ≠ e) :
      a u - ℓ (embed n u) = 0 := by
    have huU : u ∈ U := by
      by_contra hnot
      have hd : u ∈ R.positive \ U := Finset.mem_sdiff.mpr ⟨hu, hnot⟩
      rw [hPdiff] at hd
      exact hue (Finset.mem_singleton.mp hd)
    exact sub_eq_zero.mpr (hsupport u huU).symm
  rw [Finset.sum_eq_single e (fun u hu hue => hrest u hu hue)
    (fun h => False.elim (h heP))]
  let y := embed n (v + (lengths j : ℤ) • integralDualBasis d j)
  let f : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) (embed n e)
  have hy := (P.edge_endpoints_extreme (hedges j).2).2.1
  have hay : a e = -f y := ((P.integralSupport_spec e y hy).2.mpr heactive).symm
  rw [hay, hpair]
  change -f y - -f (embed n v) = _
  rw [show -f y - -f (embed n v) = -f (y - embed n v) by rw [map_sub]; ring]
  rw [show y - embed n v = (lengths j : ℝ) •
    integralBasisReal (integralDualBasis d) j by
      simp only [y, map_add, embed_int_smul, Int.cast_natCast,
        integralBasisReal_apply, add_sub_cancel_left]]
  rw [map_smul, smul_eq_mul, pairing_integral_dual_basis, hecoordj]
  simp

/-- Every contractible primitive degree is exactly the length of a genuine
edge. All geometric objects and all support values are the literal ones. -/
theorem contractible_degree_eq_edge_length
    (hP : P.Smooth) («Σ» : SmoothCompleteFan n) (hpure : «Σ».IsPure)
    (hfan : «Σ».realCones = P.normalFan)
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible) :
    ∃ v w : Lattice n, P.IsEdge (embed n v) (embed n w) ∧
      R.degree (fun u => (P.integralSupport u : ℝ)) = (latticeLength v w : ℝ) := by
  obtain ⟨U, hUcone, hNU, hUcard⟩ := hpure R.negative R.negative_cone
  obtain ⟨d, hU⟩ := «Σ».full_cone_basis hUcone hUcard
  have hnormal : (latticeRayCone U : Set (Ambient n)) ∈ P.normalFan := by
    rw [← hfan]
    exact ⟨U, hUcone, rfl⟩
  obtain ⟨x, hx, hxcone⟩ := hnormal
  have hxcone' : P.normalCone x =
      (latticeRayCone (Finset.univ.image d) : Set (Ambient n)) := by
    rw [← hxcone, hU]
  obtain ⟨v, lengths, hv, hedges⟩ := P.full_normal_basis_edges hP x hx d hxcone'
  have hcount := R.positive_count_in_full_cone hR hUcone hUcard hNU
  have hpos : 0 < (R.positive ∩ U).card := by
    rw [hcount]
    exact R.fiberDimension_pos
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
  obtain ⟨j, hj, hdj⟩ := Finset.mem_image.mp (hU ▸ (Finset.mem_inter.mp hz).2)
  have hjP : d j ∈ R.positive := by
    simpa only [hdj] using (Finset.mem_inter.mp hz).1
  have hc : P.normalCone (embed n v) =
      (latticeRayCone (Finset.univ.image d) : Set (Ambient n)) := by simpa only [hv] using hxcone'
  refine ⟨v, v + (lengths j : ℤ) • integralDualBasis d j, (hedges j).2, ?_⟩
  rw [latticeLength_basis_direction]
  exact P.contractible_degree_at_full_cone hP «Σ» hfan R hR U hUcone d hU hNU
    v lengths hedges hc j hjP

/-- The paper's edge lower bound holds for every contractible primitive
class, with no additional extremality or curve-representability hypothesis. -/
theorem contractible_degree_lower_bound
    (hP : P.Smooth) («Σ» : SmoothCompleteFan n) (hpure : «Σ».IsPure)
    (hfan : «Σ».realCones = P.normalFan) {bound : ℕ} (hbound : P.EdgesAtLeast bound)
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible) :
    (bound : ℝ) ≤ R.degree (fun u => (P.integralSupport u : ℝ)) := by
  obtain ⟨v, w, hedge, he⟩ := P.contractible_degree_eq_edge_length hP «Σ» hpure hfan R hR
  rw [he]
  exact_mod_cast (P.edgesAtLeast_iff bound).mp hbound v w hedge

end LatticePolytope

end PaperVerification.ToricGeometry
