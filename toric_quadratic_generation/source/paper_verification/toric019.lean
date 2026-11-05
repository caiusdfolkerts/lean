module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Elab.Tactic.Omega
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Tauto
public import paper_verification.toric002
public import paper_verification.toric005
public import paper_verification.toric017
public import paper_verification.toric018

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.ToricContractibleEdgeDegrees
section Source_ToricContractibleEdgeDegrees

-- original header: module

-- original header: public import PaperVerification.ToricEdgeWallSupport

-- original header: @[expose] public section

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
end
end Source_ToricContractibleEdgeDegrees
-- END ORIGINAL PaperVerification.ToricContractibleEdgeDegrees


-- BEGIN ORIGINAL PaperVerification.ToricBundleFanInduction
section Source_ToricBundleFanInduction

-- original header: module

-- original header: public import PaperVerification.ToricBundleFanEdgeBounds
-- original header: public import PaperVerification.ToricBundleFanReconstruction
-- original header: public import PaperVerification.ToricContractibleEdgeDegrees


-- original header: @[expose] public section
/-!
# The complete fiber-type branch of both mixed theorems

The hypotheses are the actual smooth lattice polytopes, their actual common
normal fan, the original geometric edge bounds, and the corresponding theorem
only in strictly smaller dimensions.  No split-bundle description, base edge
bound, coordinate saturation, or degree bound is an additional assumption.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

open Set
open scoped BigOperators Classical Pointwise
open PaperVerification.ToricExchange

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} {R : «Σ».PrimitiveRelation}
  (c : R.BundleCoordinates)

theorem fiberDegree_nat_of_edge_bound (c : R.BundleCoordinates) (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (hpure : «Σ».IsPure)
    (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) {bound : ℕ} (hbound : P.EdgesAtLeast bound) :
    ∃ k : ℕ, (∑ v ∈ R.positive, P.integralSupport v) = k ∧ bound ≤ k := by
  have h := P.contractible_degree_lower_bound hP «Σ» hpure hfan hbound R hR
  simp only [SmoothCompleteFan.PrimitiveRelation.degree, hN, Finset.sum_empty,
    sub_zero] at h
  have hZ : (bound : ℤ) ≤ ∑ v ∈ R.positive, P.integralSupport v := by
    exact_mod_cast h
  let k := (∑ v ∈ R.positive, P.integralSupport v).toNat
  have hk : (k : ℤ) = ∑ v ∈ R.positive, P.integralSupport v :=
    Int.toNat_of_nonneg (le_trans (Int.natCast_nonneg bound) hZ)
  refine ⟨k, hk.symm, ?_⟩
  exact_mod_cast (hZ.trans_eq hk.symm)

theorem interior_minkowski_support (c : R.BundleCoordinates) (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (m : Lattice n) (hm : embed n m ∈ interior (P.minkowskiSum Q)) :
    embed n m ∈ interior («Σ».fanPolytope
      (fun v => ((P.integralSupport + Q.integralSupport) v : ℝ))) := by
  have ha := P.integralSupport_isStrictSupport «Σ» hfanP
  have hb := Q.integralSupport_isStrictSupport «Σ» hfanQ
  have he : (fun v => ((P.integralSupport + Q.integralSupport) v : ℝ)) =
      (fun v => (P.integralSupport v : ℝ)) +
        (fun v => (Q.integralSupport v : ℝ)) := by
    funext v
    simp
  rw [he, «Σ».fanPolytope_add hpure _ _
    (SmoothCompleteFan.IsStrictSupport.isNef «Σ» ha)
    (SmoothCompleteFan.IsStrictSupport.isNef «Σ» hb),
    P.fanPolytope_integralSupport_eq «Σ» hfanP,
    Q.fanPolytope_integralSupport_eq «Σ» hfanQ]
  exact hm

include c in
/-- The full prescribed-parity conclusion for an actual empty-focus
contractible relation.  The sole recursive input concerns smaller dimension. -/
theorem bundle_parity_decomposition (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hlenP : P.EdgesAtLeast n) (hlenQ : Q.EdgesAtLeast n)
    (IH : ∀ d : ℕ, d < n → ∀ A B : LatticePolytope d,
      A.Smooth → B.Smooth → A.SameNormalFan B → A.EdgesAtLeast d → B.EdgesAtLeast d →
      ∀ m : Lattice d, embed d m ∈ interior (A.minkowskiSum B) →
      ∀ p : Lattice d, ∃ u v : Lattice d,
        embed d u ∈ A.carrier ∧ embed d v ∈ B.carrier ∧
          u + v = m ∧ SameParity u p)
    (m : Lattice n) (hm : embed n m ∈ interior (P.minkowskiSum Q))
    (p : Lattice n) :
    ∃ u v : Lattice n,
      embed n u ∈ P.carrier ∧ embed n v ∈ Q.carrier ∧
        u + v = m ∧ SameParity u p := by
  let a := P.integralSupport
  let b := Q.integralSupport
  have ha : «Σ».IsStrictSupport (fun v => (a v : ℝ)) :=
    P.integralSupport_isStrictSupport «Σ» hfanP
  have hb : «Σ».IsStrictSupport (fun v => (b v : ℝ)) :=
    Q.integralSupport_isStrictSupport «Σ» hfanQ
  have hcarrierP : P.carrier = «Σ».fanPolytope (fun v => (a v : ℝ)) :=
    (P.fanPolytope_integralSupport_eq «Σ» hfanP).symm
  have hcarrierQ : Q.carrier = «Σ».fanPolytope (fun v => (b v : ℝ)) :=
    (Q.fanPolytope_integralSupport_eq «Σ» hfanQ).symm
  obtain ⟨k, hk, hkn⟩ := c.fiberDegree_nat_of_edge_bound hR hN hpure P hP hfanP hlenP
  obtain ⟨l, hl, hln⟩ := c.fiberDegree_nat_of_edge_bound hR hN hpure Q hQ hfanQ hlenQ
  let γ := c.integerHomogeneousWeight (a + b) m
  have hγ : (∑ v ∈ R.positive, γ v) = (k + l : ℕ) := by
    rw [c.integerHomogeneousWeight_total hN]
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    rw [hk, hl]
    simp
  have hmfan : embed n m ∈ interior («Σ».fanPolytope (fun v => ((a + b) v : ℝ))) :=
    c.interior_minkowski_support hpure P Q hfanP hfanQ m hm
  have hγpos (v : Lattice n) (hv : v ∈ R.positive) : 0 < γ v :=
    c.integerHomogeneousWeight_pos_of_interior (a + b) m hmfan (R.primitive.1 hv)
  obtain ⟨α, β, hα, hβ, hα0, hβ0, hweights, hpar⟩ :=
    c.homogeneous_parity_allocation (c.fiberIndices_card_le.trans hkn)
      (c.fiberIndices_card_le.trans hln) γ (c.integerHomogeneousWeight a p) hγ hγpos
  have hαa : (∑ v ∈ R.positive, α v) = ∑ v ∈ R.positive, a v := hα.trans hk.symm
  have hβb : (∑ v ∈ R.positive, β v) = ∑ v ∈ R.positive, b v := hβ.trans hl.symm
  obtain ⟨A, hA, hAsm, hAfan, hAlen⟩ :=
    c.exists_basePolytope hR hN hpure a α ha hαa hα0 P hcarrierP hlenP
  obtain ⟨B, hB, hBsm, hBfan, hBlen⟩ :=
    c.exists_basePolytope hR hN hpure b β hb hβb hβ0 Q hcarrierQ hlenQ
  have hbaseA := c.integerBaseWeight_isStrictSupport hR hN a α ha hαa hα0
  have hbaseB := c.integerBaseWeight_isStrictSupport hR hN b β hb hβb hβ0
  have hmBase : embed (n - c.fiberIndices.card) (c.integerBasePoint m) ∈
      interior (A.minkowskiSum B) := by
    have h := c.integerBasePoint_mem_interior_sum_support hR hN a b α β m hmfan hweights
    rw [c.baseFan.fanPolytope_add (c.baseFan_isPure hpure) _ _
      (SmoothCompleteFan.IsStrictSupport.isNef c.baseFan hbaseA)
      (SmoothCompleteFan.IsStrictSupport.isNef c.baseFan hbaseB)] at h
    simpa only [LatticePolytope.minkowskiSum, hA, hB] using h
  have hABfan : A.SameNormalFan B := hAfan.trans hBfan.symm
  obtain ⟨u, v, hu, hv, huv, hup⟩ := IH (n - c.fiberIndices.card) c.baseDimension_lt
    A B hAsm hBsm hABfan
    (A.edgesAtLeast_of_le hAlen (Nat.sub_le _ _))
    (B.edgesAtLeast_of_le hBlen (Nat.sub_le _ _))
    (c.integerBasePoint m) hmBase (c.integerBasePoint p)
  refine ⟨c.integerPoint a α u, c.integerPoint b β v, ?_, ?_,
    c.integerPoint_sum_eq a b α β m u v hweights huv,
    c.integerPoint_sameParity a α p u hpar hup⟩
  · rw [hcarrierP, c.integerPoint_mem_fanPolytope_iff hR hN a α hαa]
    exact ⟨hα0, hA ▸ hu⟩
  · rw [hcarrierQ, c.integerPoint_mem_fanPolytope_iff hR hN b β hβb]
    exact ⟨hβ0, hB ▸ hv⟩

include c in
/-- The full interior-second-summand conclusion for the same actual
empty-focus relation.  Strict second homogeneous weights supply all fiber
facets, while the lower-dimensional theorem supplies the base interior. -/
theorem bundle_adjoint_decomposition (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hlenP : P.EdgesAtLeast (n + 1)) (hlenQ : Q.EdgesAtLeast (n + 1))
    (IH : ∀ d : ℕ, d < n → ∀ A B : LatticePolytope d,
      A.Smooth → B.Smooth → A.SameNormalFan B →
      A.EdgesAtLeast (d + 1) → B.EdgesAtLeast (d + 1) →
      ∀ m : Lattice d, embed d m ∈ interior (A.minkowskiSum B) →
      ∃ u v : Lattice d, embed d u ∈ A.carrier ∧ embed d v ∈ interior B.carrier ∧ u + v = m)
    (m : Lattice n) (hm : embed n m ∈ interior (P.minkowskiSum Q)) :
    ∃ u v : Lattice n,
      embed n u ∈ P.carrier ∧ embed n v ∈ interior Q.carrier ∧ u + v = m := by
  let a := P.integralSupport
  let b := Q.integralSupport
  have ha : «Σ».IsStrictSupport (fun v => (a v : ℝ)) :=
    P.integralSupport_isStrictSupport «Σ» hfanP
  have hb : «Σ».IsStrictSupport (fun v => (b v : ℝ)) :=
    Q.integralSupport_isStrictSupport «Σ» hfanQ
  have hcarrierP : P.carrier = «Σ».fanPolytope (fun v => (a v : ℝ)) :=
    (P.fanPolytope_integralSupport_eq «Σ» hfanP).symm
  have hcarrierQ : Q.carrier = «Σ».fanPolytope (fun v => (b v : ℝ)) :=
    (Q.fanPolytope_integralSupport_eq «Σ» hfanQ).symm
  obtain ⟨k, hk, hkn⟩ := c.fiberDegree_nat_of_edge_bound hR hN hpure P hP hfanP hlenP
  obtain ⟨l, hl, hln⟩ := c.fiberDegree_nat_of_edge_bound hR hN hpure Q hQ hfanQ hlenQ
  let γ := c.integerHomogeneousWeight (a + b) m
  have hγ : (∑ v ∈ R.positive, γ v) = (k + l : ℕ) := by
    rw [c.integerHomogeneousWeight_total hN]
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    rw [hk, hl]
    simp
  have hmfan : embed n m ∈ interior («Σ».fanPolytope (fun v => ((a + b) v : ℝ))) :=
    c.interior_minkowski_support hpure P Q hfanP hfanQ m hm
  have hγpos (v : Lattice n) (hv : v ∈ R.positive) : 0 < γ v :=
    c.integerHomogeneousWeight_pos_of_interior (a + b) m hmfan (R.primitive.1 hv)
  obtain ⟨α, β, hα, hβ, hα0, hβpos, hweights⟩ :=
    c.homogeneous_adjoint_allocation
      ((Nat.add_le_add_right c.fiberIndices_card_le 1).trans hln) γ hγ hγpos
  have hβ0 (v : Lattice n) (hv : v ∈ R.positive) : 0 ≤ β v := (hβpos v hv).le
  have hαa : (∑ v ∈ R.positive, α v) = ∑ v ∈ R.positive, a v := hα.trans hk.symm
  have hβb : (∑ v ∈ R.positive, β v) = ∑ v ∈ R.positive, b v := hβ.trans hl.symm
  obtain ⟨A, hA, hAsm, hAfan, hAlen⟩ :=
    c.exists_basePolytope hR hN hpure a α ha hαa hα0 P hcarrierP hlenP
  obtain ⟨B, hB, hBsm, hBfan, hBlen⟩ :=
    c.exists_basePolytope hR hN hpure b β hb hβb hβ0 Q hcarrierQ hlenQ
  have hbaseA := c.integerBaseWeight_isStrictSupport hR hN a α ha hαa hα0
  have hbaseB := c.integerBaseWeight_isStrictSupport hR hN b β hb hβb hβ0
  have hmBase : embed (n - c.fiberIndices.card) (c.integerBasePoint m) ∈
      interior (A.minkowskiSum B) := by
    have h := c.integerBasePoint_mem_interior_sum_support hR hN a b α β m hmfan hweights
    rw [c.baseFan.fanPolytope_add (c.baseFan_isPure hpure) _ _
      (SmoothCompleteFan.IsStrictSupport.isNef c.baseFan hbaseA)
      (SmoothCompleteFan.IsStrictSupport.isNef c.baseFan hbaseB)] at h
    simpa only [LatticePolytope.minkowskiSum, hA, hB] using h
  have hABfan : A.SameNormalFan B := hAfan.trans hBfan.symm
  obtain ⟨u, v, hu, hv, huv⟩ := IH (n - c.fiberIndices.card) c.baseDimension_lt
    A B hAsm hBsm hABfan
    (A.edgesAtLeast_of_le hAlen (Nat.add_le_add_right (Nat.sub_le _ _) 1))
    (B.edgesAtLeast_of_le hBlen (Nat.add_le_add_right (Nat.sub_le _ _) 1))
    (c.integerBasePoint m) hmBase
  refine ⟨c.integerPoint a α u, c.integerPoint b β v, ?_, ?_,
    c.integerPoint_sum_eq a b α β m u v hweights huv⟩
  · rw [hcarrierP, c.integerPoint_mem_fanPolytope_iff hR hN a α hαa]
    exact ⟨hα0, hA ▸ hu⟩
  · rw [hcarrierQ, c.integerPoint_mem_interior_fanPolytope_iff hR hN b β hβb]
    exact ⟨hβpos, hB ▸ hv⟩

end PaperVerification.ToricGeometry.SmoothCompleteFan.PrimitiveRelation.BundleCoordinates
end
end Source_ToricBundleFanInduction
-- END ORIGINAL PaperVerification.ToricBundleFanInduction


-- BEGIN ORIGINAL PaperVerification.ToricFanFaceHulls
section Source_ToricFanFaceHulls

-- original header: module

-- original header: public import PaperVerification.ToricFanPolytopes
-- original header: public import PaperVerification.ToricQuotientStarCovering

-- original header: @[expose] public section

/-!
# Exact nef face hulls over an actual fan cone

Even when nef support collapses some edges, the face cut out by a cone is
the convex hull of Cartier points of full cones containing it. Small
perturbations of the cone's interior normal prove the minimizing property,
so no assumption that the nef polytope retains the original normal fan is
needed.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

def supportFace (a : Lattice n → ℝ) (F : Finset (Lattice n)) : Set (Ambient n) :=
  {x ∈ «Σ».fanPolytope a | ∀ u ∈ F,
    (dotProductEquiv ℝ (Fin n) (embed n u)) x = -a u}

def fullConesOver (F : Finset (Lattice n)) : Finset «Σ».fullCones :=
  Finset.univ.filter (fun s => F ⊆ (s : Finset (Lattice n)))

theorem cartierPoint_support_eq (a : Lattice n → ℝ) (s : «Σ».fullCones)
    {u : Lattice n} (hu : u ∈ (s : Finset (Lattice n))) :
    (dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint a s) = -a u := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ((«Σ».fullConeBasis_ray_set s) ▸ hu)
  exact «Σ».cartierPoint_active a s i

theorem convex_supportFace (a : Lattice n → ℝ) (F : Finset (Lattice n)) :
    Convex ℝ («Σ».supportFace a F) := by
  intro x hx y hy r t hr ht hrt
  refine ⟨«Σ».convex_fanPolytope a hx.1 hy.1 hr ht hrt, ?_⟩
  intro u hu
  rw [map_add, map_smul, map_smul, hx.2 u hu, hy.2 u hu]
  change r * -a u + t * -a u = -a u
  rw [← add_mul, hrt, one_mul]

/-- Equality in genuine supporting primitive halfspaces cuts out an
actual extreme face of the original halfspace polytope. -/
theorem supportFace_isExtreme (a : Lattice n → ℝ)
    (F : Finset (Lattice n)) (hF : F ⊆ «Σ».rays) :
    IsExtreme ℝ («Σ».fanPolytope a) («Σ».supportFace a F) := by
  refine ⟨fun _ hx => hx.1, ?_⟩
  intro x hx y hy z hz hseg
  obtain ⟨r, t, hr, ht, hrt, he⟩ := hseg
  refine ⟨hx, ?_⟩
  intro u hu
  have hxu := hx u (hF hu)
  have hyu := hy u (hF hu)
  have hzu := hz.2 u hu
  have hlin := congrArg (dotProductEquiv ℝ (Fin n) (embed n u) : Ambient n → ℝ) he
  simp only [map_add, map_smul, smul_eq_mul] at hlin
  have hxnon := mul_nonneg hr.le (sub_nonneg.mpr hxu)
  have hynon := mul_nonneg ht.le (sub_nonneg.mpr hyu)
  have htotal :
      r * ((dotProductEquiv ℝ (Fin n) (embed n u)) x + a u) +
        t * ((dotProductEquiv ℝ (Fin n) (embed n u)) y + a u) = 0 := by
    calc
      _ = (r * ((dotProductEquiv ℝ (Fin n) (embed n u)) x) +
        t * ((dotProductEquiv ℝ (Fin n) (embed n u)) y)) + (r + t) * a u := by ring
      _ = 0 := by rw [hlin, hzu, hrt]; ring
  have hzero : r * ((dotProductEquiv ℝ (Fin n) (embed n u)) x + a u) = 0 := by
    nlinarith only [hxnon, hynon, htotal]
  have hz := (mul_eq_zero.mp hzero).resolve_left hr.ne'
  linarith

theorem cartierPoint_mem_supportFace {a : Lattice n → ℝ} (ha : «Σ».IsNef a)
    (F : Finset (Lattice n)) (s : «Σ».fullConesOver F) :
    «Σ».cartierPoint a s ∈ «Σ».supportFace a F := by
  refine ⟨«Σ».cartierPoint_mem_of_nef ha s, ?_⟩
  intro u hu
  exact «Σ».cartierPoint_support_eq a s ((Finset.mem_filter.mp s.property).2 hu)

/-- A normal in a full fan cone is minimized at that cone's actual
Cartier point on the whole nef polytope. -/
theorem cartierPoint_minimizes_normal (a : Lattice n → ℝ) (s : «Σ».fullCones)
    (u : Ambient n) (hu : u ∈ latticeRayCone (s : Finset (Lattice n)))
    (x : Ambient n) (hx : x ∈ «Σ».fanPolytope a) :
    (dotProductEquiv ℝ (Fin n) u) («Σ».cartierPoint a s) ≤
      (dotProductEquiv ℝ (Fin n) u) x := by
  let d := «Σ».fullConeBasis s
  let B := «Σ».cartierBasis s
  rw [«Σ».fullConeBasis_ray_set s] at hu
  have hcoords := ((mem_latticeRayCone_basis_iff d Finset.univ u).mp hu).1
  apply linear_le_of_basis_coordinates B (dotProductEquiv ℝ (Fin n) u)
    («Σ».cartierPoint a s) x
  · intro i
    have hp := integralDualBasis_real_repr (integralDualBasis d) u i
    rw [integralDualBasis_involutive] at hp
    have hi := hcoords i
    rw [hp] at hi
    exact hi
  · intro i
    rw [← «Σ».activeRay_dual s i, map_sub, «Σ».cartierPoint_active]
    exact sub_nonneg.mpr (hx («Σ».activeRay s i) («Σ».activeRay s i).property)

/-- Equation (1) restricted to the face indexed by any actual cone. This
also applies at nef endpoints and to lower-dimensional restriction polytopes. -/
theorem supportFace_eq_convexHull_cartier (hpure : «Σ».IsPure)
    (a : Lattice n → ℝ) (ha : «Σ».IsNef a)
    (F : Finset (Lattice n)) (hF : F ∈ «Σ».cones) :
    «Σ».supportFace a F = convexHull ℝ
      (Set.range (fun s : «Σ».fullConesOver F => «Σ».cartierPoint a s)) := by
  apply Set.Subset.antisymm
  · intro x hx
    apply mem_finite_convexHull_of_lower_support
    intro f
    obtain ⟨ε, hε, t, ht, hFt, hut⟩ :=
      «Σ».exists_small_perturbation_in_containing_cone hF (dualVector f)
    obtain ⟨s, hs, hts, hscard⟩ := hpure t ht
    let s' : «Σ».fullCones := ⟨s, Finset.mem_filter.mpr ⟨hs, hscard⟩⟩
    let s'' : «Σ».fullConesOver F :=
      ⟨s', Finset.mem_filter.mpr ⟨Finset.mem_univ s', hFt.trans hts⟩⟩
    let w : Ambient n := ∑ u ∈ F, embed n u
    have hnormal : w + ε • dualVector f ∈ latticeRayCone s :=
      latticeRayCone_mono hts hut
    have hmin := «Σ».cartierPoint_minimizes_normal a s' (w + ε • dualVector f)
      hnormal x hx.1
    have hcface := «Σ».cartierPoint_mem_supportFace ha F s''
    let q : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) w
    have hwvalue (y : Ambient n) (hy : y ∈ «Σ».supportFace a F) :
        q y = -∑ u ∈ F, a u := by
      change (dotProductEquiv ℝ (Fin n) (∑ u ∈ F, embed n u)) y = _
      calc
        _ = ∑ u ∈ F, (dotProductEquiv ℝ (Fin n) (embed n u)) y := by
          rw [map_sum, LinearMap.sum_apply]
        _ = ∑ u ∈ F, -a u := Finset.sum_congr rfl (fun u hu => hy.2 u hu)
        _ = _ := Finset.sum_neg_distrib a
    have hpair (y : Ambient n) :
        (dotProductEquiv ℝ (Fin n) (w + ε • dualVector f)) y = q y + ε * f y := by
      rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
      have hf : (dotProductEquiv ℝ (Fin n) (dualVector f)) y = f y := by
        change (∑ i, dualVector f i * y i) = f y
        simpa only [Pi.zero_apply, sub_zero] using
          dualVector_pairing f (0 : Ambient n) y
      rw [hf]
      rfl
    rw [hpair, hpair, hwvalue x hx, hwvalue _ hcface] at hmin
    refine ⟨s'', ?_⟩
    nlinarith
  · exact convexHull_min
      (by rintro _ ⟨s, rfl⟩; exact «Σ».cartierPoint_mem_supportFace ha F s)
      («Σ».convex_supportFace a F)

end PaperVerification.ToricGeometry.SmoothCompleteFan
end
end Source_ToricFanFaceHulls
-- END ORIGINAL PaperVerification.ToricFanFaceHulls


-- BEGIN ORIGINAL PaperVerification.ToricDisplacedSupport
section Source_ToricDisplacedSupport

-- original header: module

-- original header: public import PaperVerification.ToricFanFaceHulls
-- original header: public import PaperVerification.ToricContractibleEdgeDegrees

-- original header: @[expose] public section

/-!
# Exact displaced slices and their convex support

Subtracting nonnegative primitive-facet coefficients imposes the prescribed
normal heights. The equality with the actual slice is a direct equality of
subsets. The primitive degree estimate proves nefness and strict support
through the already established extremal criterion.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical

def facetWeight {n : ℕ} (T : Finset (Lattice n)) (h : Lattice n → ℝ) :
    Lattice n → ℝ := fun u => if u ∈ T then h u else 0

def displacedSupport {n : ℕ} (a : Lattice n → ℝ)
    (T : Finset (Lattice n)) (h : Lattice n → ℝ) : Lattice n → ℝ :=
  a - facetWeight T h

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- Equality of the actual displaced support face and the actual normal
height slice of the original polytope. -/
theorem displaced_supportFace_eq_slice (a : Lattice n → ℝ)
    (T : Finset (Lattice n)) (h : Lattice n → ℝ)
    (hh : ∀ u ∈ T, 0 ≤ h u) :
    «Σ».supportFace (displacedSupport a T h) T =
      {x ∈ «Σ».fanPolytope a | ∀ u ∈ T,
        (dotProductEquiv ℝ (Fin n) (embed n u)) x + a u = h u} := by
  ext x
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · intro u hu
      have hxu := hx.1 u hu
      by_cases huT : u ∈ T
      · simp only [displacedSupport, Pi.sub_apply, facetWeight, if_pos huT] at hxu
        have hhu := hh u huT
        linarith
      · simpa only [displacedSupport, Pi.sub_apply, facetWeight, if_neg huT, sub_zero] using hxu
    · intro u hu
      have hxu := hx.2 u hu
      simp only [displacedSupport, Pi.sub_apply, facetWeight, if_pos hu] at hxu
      linarith
  · intro hx
    refine ⟨?_, ?_⟩
    · intro u hu
      by_cases huT : u ∈ T
      · have he := hx.2 u huT
        simp only [displacedSupport, Pi.sub_apply, facetWeight, if_pos huT]
        linarith
      · simpa only [displacedSupport, Pi.sub_apply, facetWeight, if_neg huT, sub_zero]
          using hx.1 u hu
    · intro u hu
      have he := hx.2 u hu
      simp only [displacedSupport, Pi.sub_apply, facetWeight, if_pos hu]
      linarith

namespace PrimitiveRelation

variable {«Σ»} (R : «Σ».PrimitiveRelation)

/-- A nonnegative collection of facet shifts has degree at most its total
height on any primitive relation, since every positive coefficient is one. -/
theorem degree_facetWeight_le (T : Finset (Lattice n)) (h : Lattice n → ℝ)
    (hh : ∀ u ∈ T, 0 ≤ h u) : R.degree (facetWeight T h) ≤ ∑ u ∈ T, h u := by
  have hnonneg (u : Lattice n) : 0 ≤ facetWeight T h u := by
    by_cases hu : u ∈ T
    · simpa only [facetWeight, if_pos hu] using hh u hu
    · simp [facetWeight, hu]
  have hnegative : 0 ≤ ∑ u ∈ R.negative,
      (R.coefficient u : ℝ) * facetWeight T h u :=
    Finset.sum_nonneg (fun u hu => mul_nonneg (Nat.cast_nonneg _) (hnonneg u))
  have hpositive : (∑ u ∈ R.positive, facetWeight T h u) ≤ ∑ u ∈ T, h u := by
    let S := R.positive.filter (fun u => u ∈ T)
    have hsub : S ⊆ T := fun u hu => (Finset.mem_filter.mp hu).2
    have he : (∑ u ∈ R.positive, facetWeight T h u) = ∑ u ∈ S, h u := by
      rw [show S = R.positive.filter (fun u => u ∈ T) from rfl, Finset.sum_filter]
      rfl
    rw [he]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun u hu huS => hh u hu)
  unfold degree
  linarith

theorem degree_displacedSupport_lower (a : Lattice n → ℝ)
    (T : Finset (Lattice n)) (h : Lattice n → ℝ)
    (hh : ∀ u ∈ T, 0 ≤ h u) :
    R.degree a - (∑ u ∈ T, h u) ≤ R.degree (displacedSupport a T h) := by
  rw [displacedSupport, R.degree_sub]
  exact sub_le_sub_left (R.degree_facetWeight_le T h hh) _

end PrimitiveRelation

/-- The nef assertion of the displaced-slice lemma, derived from genuine
extremal degrees and the proved convex-support criterion. -/
theorem displacedSupport_isNef (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun u => (H u : ℝ)))
    (a : Lattice n → ℝ) (e : ℝ)
    (hdegree : ∀ R : «Σ».PrimitiveRelation, R.IsExtremal → e ≤ R.degree a)
    (T : Finset (Lattice n)) (h : Lattice n → ℝ)
    (hh : ∀ u ∈ T, 0 ≤ h u) (hbudget : (∑ u ∈ T, h u) ≤ e) :
    «Σ».IsNef (displacedSupport a T h) := by
  apply («Σ».isNef_iff_extremal_primitive_nonneg hpure H hH _).mpr
  intro R hR
  exact (sub_nonneg.mpr (hbudget.trans (hdegree R hR))).trans
    (R.degree_displacedSupport_lower a T h hh)

/-- Strictly smaller displacement gives actual strict support, rather than
only a positive inequality assumed to imply ampleness. -/
theorem displacedSupport_isStrictSupport (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun u => (H u : ℝ)))
    (a : Lattice n → ℝ) (e : ℝ)
    (hdegree : ∀ R : «Σ».PrimitiveRelation, R.IsExtremal → e ≤ R.degree a)
    (T : Finset (Lattice n)) (h : Lattice n → ℝ)
    (hh : ∀ u ∈ T, 0 ≤ h u) (hbudget : (∑ u ∈ T, h u) < e) :
    «Σ».IsStrictSupport (displacedSupport a T h) := by
  apply «Σ».isStrictSupport_of_extremal_primitive_pos hpure H hH
  intro R hR
  exact (sub_pos.mpr (hbudget.trans_le (hdegree R hR))).trans_le
    (R.degree_displacedSupport_lower a T h hh)

/-- All nef support functions are closed under actual finite sums. -/
theorem isNef_finset_sum {ι : Type*} (I : Finset ι)
    (a : ι → Lattice n → ℝ) (ha : ∀ i ∈ I, «Σ».IsNef (a i)) :
    «Σ».IsNef (∑ i ∈ I, a i) := by
  induction I using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using «Σ».isNef_zero
  | @insert i I hi ih =>
      rw [Finset.sum_insert hi]
      exact IsNef.add «Σ» (ha i (Finset.mem_insert_self _ _))
        (ih (fun j hj => ha j (Finset.mem_insert_of_mem hj)))

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricDisplacedSupport
-- END ORIGINAL PaperVerification.ToricDisplacedSupport


-- BEGIN ORIGINAL PaperVerification.ToricDisplacedEdgeBounds
section Source_ToricDisplacedEdgeBounds

-- original header: module

-- original header: public import PaperVerification.ToricSupportAveragedEdges
-- original header: public import PaperVerification.ToricDisplacedSupport

-- original header: @[expose] public section

/-!
# Literal edge bounds after moving primitive facets

A nef difference of support functions gives feasible translated, scaled
axis segments in the new polytope. The classification of all actual edges
then transfers the original edge lower bound. This does not identify an
arbitrary wall relation with a primitive or extremal relation.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical

theorem convex_axis_point_of_le {n : ℕ} (A : Set (Ambient n)) (hA : Convex ℝ A)
    (v e : Ambient n) (L t : ℝ) (hv : v ∈ A) (hL : v + L • e ∈ A)
    (ht : 0 ≤ t) (htL : t ≤ L) : v + t • e ∈ A := by
  by_cases hzero : L = 0
  · have htzero : t = 0 := by linarith
    simpa only [htzero, zero_smul, add_zero] using hv
  · have hLpos : 0 < L := lt_of_le_of_ne (ht.trans htL) (Ne.symm hzero)
    have hratio : t / L ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg ht hLpos.le, (div_le_one hLpos).mpr htL⟩
    have hh := hA.lineMap_mem hv hL hratio
    have heq : AffineMap.lineMap v (v + L • e) (t / L) = v + t • e := by
      rw [AffineMap.lineMap_apply_module', add_sub_cancel_left,
        smul_smul, div_mul_cancel₀ _ hzero, add_comm]
    simpa only [heq] using hh

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem cartierPoint_sub (a b : Lattice n → ℝ) (s : «Σ».fullCones) :
    «Σ».cartierPoint (a - b) s = «Σ».cartierPoint a s - «Σ».cartierPoint b s := by
  simp only [cartierPoint, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, neg_sub]
  abel

theorem cartierPoint_smul (t : ℝ) (a : Lattice n → ℝ) (s : «Σ».fullCones) :
    «Σ».cartierPoint (t • a) s = t • «Σ».cartierPoint a s := by
  simp only [cartierPoint, Pi.smul_apply, smul_eq_mul, mul_smul,
    ← Finset.smul_sum, smul_neg]

/-- The constructed polytope has exactly the prescribed support value
on each genuine primitive fan ray. -/
theorem supportLatticePolytope_integralSupport_on_ray (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    (u : Lattice n) (hu : u ∈ «Σ».rays) :
    ((«Σ».supportLatticePolytope hpure a ha).integralSupport u : ℝ) = a u := by
  let P := «Σ».supportLatticePolytope hpure a ha
  obtain ⟨s, hs, hus⟩ := («Σ».mem_rays_iff u).mp hu
  obtain ⟨U, hU, hsU, hUcard⟩ := hpure s hs
  let U' : «Σ».fullCones := ⟨U, Finset.mem_filter.mpr ⟨hU, hUcard⟩⟩
  let v := «Σ».cartierPoint (fun w => (a w : ℝ)) U'
  have hv : v ∈ P.carrier := by
    rw [«Σ».supportLatticePolytope_carrier]
    exact «Σ».cartierPoint_mem_of_nef (IsStrictSupport.isNef «Σ» ha) U'
  have hnormal : embed n u ∈ P.normalCone v := by
    rw [«Σ».supportLatticePolytope_cartier_normalCone]
    exact latticeRayCone_generator U (hsU hus)
  have hp := (P.integralSupport_spec u v hv).2.mpr hnormal
  have hvu := «Σ».cartierPoint_support_eq_of_mem (fun w => (a w : ℝ)) U' (hsU hus)
  linarith

theorem support_contractible_degree_lower_bound_of_edges (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {e : ℕ} (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible) :
    (e : ℝ) ≤ R.degree (fun u => (a u : ℝ)) := by
  let P := «Σ».supportLatticePolytope hpure a ha
  have hP := «Σ».supportLatticePolytope_smooth hpure a ha
  have hfan := («Σ».supportLatticePolytope_normalFan hpure a ha).symm
  have hl := P.contractible_degree_lower_bound hP «Σ» hpure hfan hedges R hR
  have heq : R.degree (fun u => (P.integralSupport u : ℝ)) =
      R.degree (fun u => (a u : ℝ)) := by
    unfold PrimitiveRelation.degree
    congr 1
    · exact Finset.sum_congr rfl (fun u hu =>
        «Σ».supportLatticePolytope_integralSupport_on_ray hpure a ha u (R.primitive.1 hu))
    · exact Finset.sum_congr rfl (fun u hu =>
        congrArg (fun t : ℝ => (R.coefficient u : ℝ) * t)
          («Σ».supportLatticePolytope_integralSupport_on_ray hpure a ha u
            («Σ».ray_mem_of_mem_cone R.negative_cone hu)))
  rwa [heq] at hl

theorem support_extremal_degree_lower_bound_of_edges (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {e : ℕ} (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (R : «Σ».PrimitiveRelation) (hR : R.IsExtremal) :
    (e : ℝ) ≤ R.degree (fun u => (a u : ℝ)) :=
  «Σ».support_contractible_degree_lower_bound_of_edges hpure a ha hedges R
    (R.combinatoriallyContractible_of_extremal hR)

/-- Nef displaced support from the literal all-edge hypothesis, including
the exact endpoint where the total displacement equals the edge bound. -/
theorem displacedSupport_isNef_of_edges (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {e : ℕ} (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (T : Finset (Lattice n)) (h : Lattice n → ℝ)
    (hh : ∀ u ∈ T, 0 ≤ h u) (hbudget : (∑ u ∈ T, h u) ≤ e) :
    «Σ».IsNef (displacedSupport (fun u => (a u : ℝ)) T h) :=
  «Σ».displacedSupport_isNef hpure a ha _ e
    («Σ».support_extremal_degree_lower_bound_of_edges hpure a ha hedges) T h hh hbudget

theorem displacedSupport_isStrictSupport_of_edges (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {e : ℕ} (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (T : Finset (Lattice n)) (h : Lattice n → ℝ)
    (hh : ∀ u ∈ T, 0 ≤ h u) (hbudget : (∑ u ∈ T, h u) < e) :
    «Σ».IsStrictSupport (displacedSupport (fun u => (a u : ℝ)) T h) :=
  «Σ».displacedSupport_isStrictSupport hpure a ha _ e
    («Σ».support_extremal_degree_lower_bound_of_edges hpure a ha hedges) T h hh hbudget

/-- A genuine nef support difference transfers all actual edge bounds
through the common primitive coordinate directions. -/
theorem support_edgesAtLeast_of_nef_difference (hpure : «Σ».IsPure)
    (a d : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    (hd : «Σ».IsStrictSupport (fun u => (d u : ℝ)))
    {e bound : ℕ} (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (c : ℝ) (hc : 0 ≤ c)
    (hnef : «Σ».IsNef ((fun u => (d u : ℝ)) - c • (fun u => (a u : ℝ))))
    (hbound : (bound : ℝ) ≤ c * e) :
    («Σ».supportLatticePolytope hpure d hd).EdgesAtLeast bound := by
  let A : Lattice n → ℝ := fun u => (a u : ℝ)
  let D : Lattice n → ℝ := fun u => (d u : ℝ)
  let N := D - c • A
  apply «Σ».support_edgesAtLeast_of_axis_points hpure d hd bound
  intro s i
  have hAxisA := «Σ».support_axis_point_of_edgesAtLeast hpure a ha hedges s i
  have hN := «Σ».cartierPoint_mem_of_nef hnef s
  have hlarge : «Σ».cartierPoint D s + (c * e) • «Σ».cartierBasis s i ∈ «Σ».fanPolytope D := by
    have heq : «Σ».cartierPoint D s + (c * e) • «Σ».cartierBasis s i =
        c • («Σ».cartierPoint A s + (e : ℝ) • «Σ».cartierBasis s i) + «Σ».cartierPoint N s := by
      dsimp [N]
      rw [«Σ».cartierPoint_sub, «Σ».cartierPoint_smul, smul_add, smul_smul]
      abel
    rw [heq]
    intro u hu
    have hAu := hAxisA u hu
    have hNu := hN u hu
    have hmult := mul_le_mul_of_nonneg_left hAu hc
    change -(D u - c * A u) ≤
      (dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint N s) at hNu
    rw [map_add, map_smul]
    change -D u ≤ c *
      (dotProductEquiv ℝ (Fin n) (embed n u))
        («Σ».cartierPoint A s + (e : ℝ) • «Σ».cartierBasis s i) +
      (dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint N s)
    nlinarith
  exact convex_axis_point_of_le («Σ».fanPolytope D) («Σ».convex_fanPolytope D)
    («Σ».cartierPoint D s) («Σ».cartierBasis s i) (c * e) bound
    («Σ».cartierPoint_mem_of_nef (IsStrictSupport.isNef «Σ» hd) s)
    hlarge (Nat.cast_nonneg _) hbound

/-- The proportional remainder of a displaced support function is nef.
Only the already proved extremal criterion and the exact facet-degree
estimate are used. -/
theorem displacedSupport_nef_difference (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    (e : ℝ) (he : 0 < e)
    (hdegree : ∀ R : «Σ».PrimitiveRelation, R.IsExtremal →
      e ≤ R.degree (fun u => (a u : ℝ)))
    (T : Finset (Lattice n)) (h : Lattice n → ℝ) (hh : ∀ u ∈ T, 0 ≤ h u) :
    «Σ».IsNef (displacedSupport (fun u => (a u : ℝ)) T h -
      (1 - (∑ u ∈ T, h u) / e) • (fun u => (a u : ℝ))) := by
  let A : Lattice n → ℝ := fun u => (a u : ℝ)
  let H := ∑ u ∈ T, h u
  have hH : 0 ≤ H := Finset.sum_nonneg hh
  have hHe : 0 ≤ H / e := div_nonneg hH he.le
  apply («Σ».isNef_iff_extremal_primitive_nonneg hpure a ha _).mpr
  intro R hR
  have hd := hdegree R hR
  have hf := R.degree_facetWeight_le T h hh
  have hmul := mul_le_mul_of_nonneg_left hd hHe
  have hcancel : (H / e) * e = H := div_mul_cancel₀ H he.ne'
  rw [hcancel] at hmul
  rw [R.degree_sub, R.degree_smul, displacedSupport, R.degree_sub]
  change 0 ≤ R.degree A - R.degree (facetWeight T h) -
    (1 - H / e) * R.degree A
  change R.degree (facetWeight T h) ≤ H at hf
  nlinarith

/-- Every actual edge loses at most the total normal displacement.
The resulting support is required to be strict only because the target
is an ordinary full-dimensional lattice polytope. -/
theorem displacedSupport_edgesAtLeast (hpure : «Σ».IsPure)
    (a d : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    (hd : «Σ».IsStrictSupport (fun u => (d u : ℝ)))
    {e bound : ℕ} (he : 0 < e)
    (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (T : Finset (Lattice n)) (h : Lattice n → ℝ)
    (hh : ∀ u ∈ T, 0 ≤ h u)
    (hdcoeff : (fun u => (d u : ℝ)) = displacedSupport (fun u => (a u : ℝ)) T h)
    (hbudget : (∑ u ∈ T, h u) ≤ e)
    (hbound : (bound : ℝ) ≤ (e : ℝ) - ∑ u ∈ T, h u) :
    («Σ».supportLatticePolytope hpure d hd).EdgesAtLeast bound := by
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hdegree := «Σ».support_extremal_degree_lower_bound_of_edges hpure a ha hedges
  let c := 1 - (∑ u ∈ T, h u) / (e : ℝ)
  have hc : 0 ≤ c := by
    dsimp [c]
    exact sub_nonneg.mpr ((div_le_one heR).mpr hbudget)
  have hnef := «Σ».displacedSupport_nef_difference hpure a ha e heR hdegree T h hh
  rw [← hdcoeff] at hnef
  apply «Σ».support_edgesAtLeast_of_nef_difference hpure a d ha hd hedges c hc hnef
  have hcancel : c * (e : ℝ) = (e : ℝ) - ∑ u ∈ T, h u := by
    dsimp [c]
    rw [sub_mul, one_mul, div_mul_cancel₀ _ heR.ne']
  rwa [hcancel]

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricDisplacedEdgeBounds
-- END ORIGINAL PaperVerification.ToricDisplacedEdgeBounds


-- BEGIN ORIGINAL PaperVerification.ToricQuotientFaceCoordinates
section Source_ToricQuotientFaceCoordinates

-- original header: module

-- original header: public import PaperVerification.ToricQuotientStarCovering
-- original header: public import PaperVerification.ToricFanFaceHulls
-- original header: public import PaperVerification.ToricFaceCoordinates

-- original header: @[expose] public section

/-!
# Actual saturated affine coordinates on a support face

The normal quotient and the tangent embedding are dual under the ordinary
coordinate pairing. The origin solves precisely the active support
equalities. At integral support values this is an actual saturated integral
affine chart, so all lattice and parity coordinates retain their meaning.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical

variable {n : ℕ}

def complementaryEmbedding (I : Finset (Fin n)) : Fin (n - I.card) ↪ Fin n where
  toFun j := ((quotientIndexEquivFin I).symm j : Fin n)
  inj' := Subtype.val_injective.comp (quotientIndexEquivFin I).symm.injective

theorem mem_range_complementaryEmbedding_iff (I : Finset (Fin n)) (i : Fin n) :
    i ∈ Set.range (complementaryEmbedding I) ↔ i ∉ I := by
  constructor
  · rintro ⟨j, rfl⟩
    exact ((quotientIndexEquivFin I).symm j).property
  · intro hi
    refine ⟨quotientIndexEquivFin I ⟨i, hi⟩, ?_⟩
    simp only [complementaryEmbedding, Function.Embedding.coeFn_mk,
      Equiv.symm_apply_apply]

def faceTangentReal (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) : Ambient (n - I.card) →ₗ[ℝ] Ambient n :=
  selectedBasisMap (integralBasisReal (integralDualBasis b)) (complementaryEmbedding I)

def faceTangentLattice (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) : Lattice (n - I.card) →ₗ[ℤ] Lattice n :=
  selectedBasisMap (integralDualBasis b) (complementaryEmbedding I)

/-- The tangent embedding is literally dual to the saturated normal
quotient, not merely isomorphic after tensoring with the reals. -/
theorem faceTangentReal_pairing (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) (u : Ambient n) (x : Ambient (n - I.card)) :
    (dotProductEquiv ℝ (Fin n) u) (faceTangentReal b I x) =
      (dotProductEquiv ℝ (Fin (n - I.card)) (coneQuotientReal b I u)) x := by
  have hp (j : Fin (n - I.card)) :
      (dotProductEquiv ℝ (Fin n) u)
        (integralBasisReal (integralDualBasis b) (complementaryEmbedding I j)) =
      (integralBasisReal b).repr u (complementaryEmbedding I j) := by
    rw [integralBasisReal_apply]
    change (∑ k, u k * embed n (integralDualBasis b (complementaryEmbedding I j)) k) = _
    simpa only [mul_comm] using
      integralDualBasis_real_pairing b (complementaryEmbedding I j) u
  simp only [faceTangentReal, selectedBasisMap_apply, map_sum, map_smul, hp, smul_eq_mul]
  change (∑ j, x j * (integralBasisReal b).repr u (complementaryEmbedding I j)) =
    ∑ j, (coneQuotientReal b I u) j * x j
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

def quotientFaceOrigin (a : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) : Ambient n :=
  -∑ i ∈ I, a (b i) • integralBasisReal (integralDualBasis b) i

def quotientFaceOriginLattice (a : Lattice n → ℤ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) : Lattice n :=
  -∑ i ∈ I, a (b i) • integralDualBasis b i

theorem embed_quotientFaceOrigin (a : Lattice n → ℤ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    embed n (quotientFaceOriginLattice a b I) =
      quotientFaceOrigin (fun u => (a u : ℝ)) b I := by
  simp only [quotientFaceOriginLattice, quotientFaceOrigin, map_neg, map_sum,
    embed_int_smul, integralBasisReal_apply]

theorem quotientFaceOrigin_coordinate (a : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) (i : Fin n) :
    (integralBasisReal (integralDualBasis b)).repr (quotientFaceOrigin a b I) i =
      if i ∈ I then -a (b i) else 0 := by
  by_cases hi : i ∈ I <;>
    simp [quotientFaceOrigin, map_sum, map_smul, Finsupp.finsetSum_apply,
      Finsupp.smul_apply, Module.Basis.repr_self_apply, Finsupp.single_apply, smul_eq_mul, hi]

def quotientFaceMap (a : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    Ambient (n - I.card) →ᵃ[ℝ] Ambient n :=
  AffineMap.const ℝ _ (quotientFaceOrigin a b I) + (faceTangentReal b I).toAffineMap

@[simp] theorem quotientFaceMap_apply (a : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (x : Ambient (n - I.card)) :
    quotientFaceMap a b I x = quotientFaceOrigin a b I + faceTangentReal b I x := rfl

theorem quotientFaceMap_injective (a : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    Function.Injective (quotientFaceMap a b I) := by
  intro x y h
  apply selectedBasisMap_injective (integralBasisReal (integralDualBasis b))
    (complementaryEmbedding I)
  exact add_left_cancel h

theorem normal_pairing_eq_dual_coordinate
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) (x : Ambient n) :
    (dotProductEquiv ℝ (Fin n) (embed n (b i))) x =
      (integralBasisReal (integralDualBasis b)).repr x i := by
  change (∑ j, embed n (b i) j * x j) = _
  simpa only [integralDualBasis_involutive] using
    integralDualBasis_real_pairing (integralDualBasis b) i x

theorem quotientFaceMap_active (a : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (x : Ambient (n - I.card)) (i : Fin n) (hi : i ∈ I) :
    (dotProductEquiv ℝ (Fin n) (embed n (b i))) (quotientFaceMap a b I x) = -a (b i) := by
  rw [normal_pairing_eq_dual_coordinate, quotientFaceMap_apply,
    map_add, Finsupp.add_apply, quotientFaceOrigin_coordinate, if_pos hi]
  have hnot : i ∉ Set.range (complementaryEmbedding I) := by
    rw [mem_range_complementaryEmbedding_iff]
    exact not_not.mpr hi
  rw [show faceTangentReal b I x = selectedBasisMap
      (integralBasisReal (integralDualBasis b)) (complementaryEmbedding I) x from rfl,
    selectedBasisMap_coordinate_eq_zero _ _ _ _ hnot, add_zero]

/-- The affine chart covers exactly the genuine active hyperplanes, with
no unproved saturation or affine-span premise. -/
theorem mem_range_quotientFaceMap_iff (a : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) (x : Ambient n) :
    x ∈ Set.range (quotientFaceMap a b I) ↔ ∀ i ∈ I,
      (dotProductEquiv ℝ (Fin n) (embed n (b i))) x = -a (b i) := by
  constructor
  · rintro ⟨y, rfl⟩ i hi
    exact quotientFaceMap_active a b I y i hi
  · intro hx
    have hzero : ∀ i ∉ Set.range (complementaryEmbedding I),
        (integralBasisReal (integralDualBasis b)).repr
          (x - quotientFaceOrigin a b I) i = 0 := by
      intro i hi
      have hiI : i ∈ I := by
        simpa only [mem_range_complementaryEmbedding_iff, not_not] using hi
      rw [map_sub, Finsupp.sub_apply, quotientFaceOrigin_coordinate, if_pos hiI,
        ← normal_pairing_eq_dual_coordinate, hx i hiI, sub_self]
    obtain ⟨y, hy⟩ := (mem_range_selectedBasisMap_iff
      (integralBasisReal (integralDualBasis b)) (complementaryEmbedding I)
      (x - quotientFaceOrigin a b I)).mpr hzero
    refine ⟨y, ?_⟩
    change quotientFaceOrigin a b I +
      selectedBasisMap (integralBasisReal (integralDualBasis b)) (complementaryEmbedding I) y = x
    rw [hy]
    abel

/-- Integral support gives the actual saturated affine lattice chart. -/
def quotientFaceIntegralChart (a : Lattice n → ℤ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    IntegralAffineEmbedding (n - I.card) n :=
  selectedBasisChart (quotientFaceOriginLattice a b I)
    (integralDualBasis b) (complementaryEmbedding I)

theorem quotientFaceIntegralChart_realMap (a : Lattice n → ℤ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    (quotientFaceIntegralChart a b I).realMap =
      quotientFaceMap (fun u => (a u : ℝ)) b I := by
  ext x
  simp only [quotientFaceIntegralChart, IntegralAffineEmbedding.realMap_apply,
    selectedBasisChart, embed_quotientFaceOrigin, quotientFaceMap_apply,
    faceTangentReal]

/-- A linear form vanishing on the deleted normals factors through the
explicit saturated quotient, with the actual chosen section. -/
theorem linear_face_factorization
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (ℓ : Ambient n →ₗ[ℝ] ℝ)
    (hℓ : ∀ i ∈ I, ℓ (integralBasisReal b i) = 0) (u : Ambient n) :
    ℓ (coneQuotientSectionReal b I (coneQuotientReal b I u)) = ℓ u := by
  change ℓ (basisSection (integralBasisReal b) I
    ((quotientCoordinateFinEquiv ℝ I).symm
      (quotientCoordinateFinEquiv ℝ I (basisProjection (integralBasisReal b) I u)))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact map_basisSection_projection (integralBasisReal b) I ℓ hℓ u

end PaperVerification.ToricGeometry
end
end Source_ToricQuotientFaceCoordinates
-- END ORIGINAL PaperVerification.ToricQuotientFaceCoordinates


-- BEGIN ORIGINAL PaperVerification.ToricQuotientFaceSupport
section Source_ToricQuotientFaceSupport

-- original header: module

-- original header: public import PaperVerification.ToricQuotientFaceCoordinates
-- original header: public import PaperVerification.ToricAdjointSupport

-- original header: @[expose] public section

/-!
# Support functions on the actual saturated quotient star

Every projected star ray has one actual primitive lift. Restriction support
is the original coefficient plus the value of the chosen affine origin on
that lift. The linear support functions factor through the saturated
quotient, proving both nefness and strict support on the actual quotient
fan. The affine image of its polytope is proved to be the original face.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b ∈ «Σ».cones)

theorem exists_starRayLift
    (u : («Σ».completeQuotientStarFan b I hF).rays) :
    ∃ v : Lattice n, ∃ s ∈ «Σ».cones, I.image b ⊆ s ∧
      v ∈ s \ I.image b ∧ coneQuotientLattice b I v = u := by
  obtain ⟨t, ht, hut⟩ := ((«Σ».completeQuotientStarFan b I hF).mem_rays_iff u).mp u.property
  obtain ⟨s, hs, hFs, hts⟩ := («Σ».mem_quotientStarCones b I t).mp ht
  rw [hts] at hut
  obtain ⟨v, hv, hvu⟩ := Finset.mem_image.mp hut
  exact ⟨v, s, hs, hFs, hv, hvu⟩

def starRayLift (u : («Σ».completeQuotientStarFan b I hF).rays) : Lattice n :=
  Classical.choose («Σ».exists_starRayLift b I hF u)

theorem starRayLift_spec (u : («Σ».completeQuotientStarFan b I hF).rays) :
    ∃ s ∈ «Σ».cones, I.image b ⊆ s ∧
      «Σ».starRayLift b I hF u ∈ s \ I.image b ∧
      coneQuotientLattice b I («Σ».starRayLift b I hF u) = u :=
  Classical.choose_spec («Σ».exists_starRayLift b I hF u)

theorem projected_starRay_mem {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones)
    (hFs : I.image b ⊆ s) {v : Lattice n} (hv : v ∈ s \ I.image b) :
    coneQuotientLattice b I v ∈ («Σ».completeQuotientStarFan b I hF).rays := by
  apply ((«Σ».completeQuotientStarFan b I hF).mem_rays_iff _).mpr
  refine ⟨(s \ I.image b).image (coneQuotientLattice b I), ?_,
    Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩
  exact («Σ».mem_quotientStarCones b I _).mpr ⟨s, hs, hFs, rfl⟩

theorem starRayLift_projected {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones)
    (hFs : I.image b ⊆ s) {v : Lattice n} (hv : v ∈ s \ I.image b) :
    «Σ».starRayLift b I hF ⟨coneQuotientLattice b I v,
      «Σ».projected_starRay_mem b I hF hs hFs hv⟩ = v := by
  obtain ⟨t, ht, hFt, hwt, hwp⟩ := «Σ».starRayLift_spec b I hF
    ⟨coneQuotientLattice b I v, «Σ».projected_starRay_mem b I hF hs hFs hv⟩
  exact «Σ».coneQuotient_injective_star_rays b I ht hs hFt hFs hwt hv hwp

/-- The actual restriction coefficient on each quotient primitive ray.
Values outside the ray set are irrelevant and are fixed to zero. -/
def faceSupport (a : Lattice n → ℝ) : Lattice (n - I.card) → ℝ := fun u =>
  if hu : u ∈ («Σ».completeQuotientStarFan b I hF).rays then
    a («Σ».starRayLift b I hF ⟨u, hu⟩) +
      (dotProductEquiv ℝ (Fin n) (embed n («Σ».starRayLift b I hF ⟨u, hu⟩)))
        (quotientFaceOrigin a b I)
  else 0

theorem faceSupport_lift (a : Lattice n → ℝ)
    (u : («Σ».completeQuotientStarFan b I hF).rays) :
    «Σ».faceSupport b I hF a u = a («Σ».starRayLift b I hF u) +
      (dotProductEquiv ℝ (Fin n) (embed n («Σ».starRayLift b I hF u)))
        (quotientFaceOrigin a b I) := by
  simp only [faceSupport, dif_pos u.property]

theorem faceSupport_projected (a : Lattice n → ℝ)
    {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones) (hFs : I.image b ⊆ s)
    {v : Lattice n} (hv : v ∈ s \ I.image b) :
    «Σ».faceSupport b I hF a (coneQuotientLattice b I v) =
      a v + (dotProductEquiv ℝ (Fin n) (embed n v)) (quotientFaceOrigin a b I) := by
  have h := «Σ».faceSupport_lift b I hF a
    ⟨coneQuotientLattice b I v, «Σ».projected_starRay_mem b I hF hs hFs hv⟩
  rw [«Σ».starRayLift_projected b I hF hs hFs hv] at h
  exact h

theorem quotientFaceMap_pairing (a : Lattice n → ℝ)
    (u : Lattice n) (x : Ambient (n - I.card)) :
    (dotProductEquiv ℝ (Fin n) (embed n u)) (quotientFaceMap a b I x) =
      (dotProductEquiv ℝ (Fin n) (embed n u)) (quotientFaceOrigin a b I) +
      (dotProductEquiv ℝ (Fin (n - I.card)) (embed (n - I.card)
        (coneQuotientLattice b I u))) x := by
  rw [quotientFaceMap_apply, map_add, faceTangentReal_pairing, coneQuotient_compatible]

/-- Original linear support, shifted by the affine origin, factors through
the normal quotient. -/
theorem face_linear_support_factors (a : Lattice n → ℝ)
    (ℓ : Ambient n →ₗ[ℝ] ℝ)
    (he : ∀ i ∈ I, ℓ (embed n (b i)) = a (b i)) :
    ∀ u : Ambient n,
      ((ℓ + dotProductEquiv ℝ (Fin n) (quotientFaceOrigin a b I)).comp
        (coneQuotientSectionReal b I)) (coneQuotientReal b I u) =
      ℓ u + (dotProductEquiv ℝ (Fin n) (quotientFaceOrigin a b I)) u := by
  intro u
  apply linear_face_factorization b I
    (ℓ + dotProductEquiv ℝ (Fin n) (quotientFaceOrigin a b I)) ?_ u
  intro i hi
  simp only [LinearMap.add_apply, integralBasisReal_apply, he i hi]
  have hp : (dotProductEquiv ℝ (Fin n) (quotientFaceOrigin a b I)) (embed n (b i)) =
      -a (b i) := by
    have hcomm : (dotProductEquiv ℝ (Fin n) (quotientFaceOrigin a b I)) (embed n (b i)) =
        (dotProductEquiv ℝ (Fin n) (embed n (b i))) (quotientFaceOrigin a b I) := by
      change quotientFaceOrigin a b I ⬝ᵥ embed n (b i) =
        embed n (b i) ⬝ᵥ quotientFaceOrigin a b I
      exact dotProduct_comm _ _
    rw [hcomm, normal_pairing_eq_dual_coordinate,
      quotientFaceOrigin_coordinate, if_pos hi]
  rw [hp, add_neg_cancel]

/-- Nefness restricts to the genuine saturated quotient-star fan. -/
theorem faceSupport_isNef (a : Lattice n → ℝ) (ha : «Σ».IsNef a) :
    («Σ».completeQuotientStarFan b I hF).IsNef («Σ».faceSupport b I hF a) := by
  intro t ht
  obtain ⟨s, hs, hFs, hts⟩ := («Σ».mem_quotientStarCones b I t).mp ht
  obtain ⟨ℓ, he, hle⟩ := ha s hs
  let L := ℓ + dotProductEquiv ℝ (Fin n) (quotientFaceOrigin a b I)
  let q := L.comp (coneQuotientSectionReal b I)
  have hfactor (v : Lattice n) : q (embed (n - I.card) (coneQuotientLattice b I v)) =
      ℓ (embed n v) + (dotProductEquiv ℝ (Fin n) (embed n v)) (quotientFaceOrigin a b I) := by
    rw [← coneQuotient_compatible]
    have h := face_linear_support_factors b I a ℓ
      (fun i hi => he _ (hFs (Finset.mem_image.mpr ⟨i, hi, rfl⟩))) (embed n v)
    change q (coneQuotientReal b I (embed n v)) =
      ℓ (embed n v) + quotientFaceOrigin a b I ⬝ᵥ embed n v at h
    change q (coneQuotientReal b I (embed n v)) =
      ℓ (embed n v) + embed n v ⬝ᵥ quotientFaceOrigin a b I
    rw [dotProduct_comm (embed n v) (quotientFaceOrigin a b I)]
    exact h
  refine ⟨q, ?_, ?_⟩
  · intro u hu
    rw [hts] at hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    rw [hfactor, he v (Finset.mem_sdiff.mp hv).1,
      «Σ».faceSupport_projected b I hF a hs hFs hv]
  · intro u hu
    let u' : («Σ».completeQuotientStarFan b I hF).rays := ⟨u, hu⟩
    obtain ⟨s', hs', hFs', hv, hproj⟩ := «Σ».starRayLift_spec b I hF u'
    have hvray := «Σ».ray_mem_of_mem_cone hs' (Finset.mem_sdiff.mp hv).1
    have hbound := hle («Σ».starRayLift b I hF u') hvray
    have hsupp := «Σ».faceSupport_lift b I hF a u'
    have hfactor' := hfactor («Σ».starRayLift b I hF u')
    rw [hproj] at hfactor'
    exact hfactor'.trans_le ((add_le_add hbound le_rfl).trans_eq hsupp.symm)

/-- Strict support restricts as well: no extra quotient-ray coincidence is
assumed, since uniqueness of actual primitive lifts was proved above. -/
theorem faceSupport_isStrictSupport (a : Lattice n → ℝ)
    (ha : «Σ».IsStrictSupport a) :
    («Σ».completeQuotientStarFan b I hF).IsStrictSupport («Σ».faceSupport b I hF a) := by
  intro t ht
  obtain ⟨s, hs, hFs, hts⟩ := («Σ».mem_quotientStarCones b I t).mp ht
  obtain ⟨ℓ, he, hlt⟩ := ha s hs
  let L := ℓ + dotProductEquiv ℝ (Fin n) (quotientFaceOrigin a b I)
  let q := L.comp (coneQuotientSectionReal b I)
  have hfactor (v : Lattice n) : q (embed (n - I.card) (coneQuotientLattice b I v)) =
      ℓ (embed n v) + (dotProductEquiv ℝ (Fin n) (embed n v)) (quotientFaceOrigin a b I) := by
    rw [← coneQuotient_compatible]
    have h := face_linear_support_factors b I a ℓ
      (fun i hi => he _ (hFs (Finset.mem_image.mpr ⟨i, hi, rfl⟩))) (embed n v)
    change q (coneQuotientReal b I (embed n v)) =
      ℓ (embed n v) + quotientFaceOrigin a b I ⬝ᵥ embed n v at h
    change q (coneQuotientReal b I (embed n v)) =
      ℓ (embed n v) + embed n v ⬝ᵥ quotientFaceOrigin a b I
    rw [dotProduct_comm (embed n v) (quotientFaceOrigin a b I)]
    exact h
  refine ⟨q, ?_, ?_⟩
  · intro u hu
    rw [hts] at hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    rw [hfactor, he v (Finset.mem_sdiff.mp hv).1,
      «Σ».faceSupport_projected b I hF a hs hFs hv]
  · intro u hu hut
    let u' : («Σ».completeQuotientStarFan b I hF).rays := ⟨u, hu⟩
    obtain ⟨s', hs', hFs', hv, hproj⟩ := «Σ».starRayLift_spec b I hF u'
    have hvray := «Σ».ray_mem_of_mem_cone hs' (Finset.mem_sdiff.mp hv).1
    have hvnot : «Σ».starRayLift b I hF u' ∉ s := by
      intro hvs
      apply hut
      rw [hts]
      exact Finset.mem_image.mpr ⟨«Σ».starRayLift b I hF u',
        Finset.mem_sdiff.mpr ⟨hvs, (Finset.mem_sdiff.mp hv).2⟩, hproj⟩
    have hbound := hlt («Σ».starRayLift b I hF u') hvray hvnot
    have hsupp := «Σ».faceSupport_lift b I hF a u'
    have hfactor' := hfactor («Σ».starRayLift b I hF u')
    rw [hproj] at hfactor'
    exact hfactor'.trans_lt ((add_lt_add_of_lt_of_le hbound le_rfl).trans_eq hsupp.symm)

/-- A full cone of the quotient star is the projection of a full original
cone containing the deleted cone. The dimension assertion is a consequence
of the already proved injectivity of primitive ray projection. -/
theorem exists_fullCone_lift
    (t : («Σ».completeQuotientStarFan b I hF).fullCones) :
    ∃ s : «Σ».fullCones, I.image b ⊆ (s : Finset (Lattice n)) ∧
      (t : Finset (Lattice (n - I.card))) =
        ((s : Finset (Lattice n)) \ I.image b).image (coneQuotientLattice b I) := by
  obtain ⟨s, hs, hFs, hts⟩ := («Σ».mem_quotientStarCones b I t).mp
    ((«Σ».completeQuotientStarFan b I hF).fullCones_mem t)
  have hcard := («Σ».completeQuotientStarFan b I hF).fullCones_card t
  have himage : ((s \ I.image b).image (coneQuotientLattice b I)).card =
      (s \ I.image b).card := by
    apply Finset.card_image_of_injOn
    intro v hv w hw he
    exact «Σ».coneQuotient_injective_star_rays b I hs hs hFs hFs hv hw he
  have hIcard : (I.image b).card = I.card := Finset.card_image_of_injective I b.injective
  have hIs : I.card ≤ s.card := by
    rw [← hIcard]
    exact Finset.card_le_card hFs
  have hIn : I.card ≤ n := hIs.trans («Σ».card_cone_le hs)
  rw [hts, himage, Finset.card_sdiff_of_subset hFs, hIcard] at hcard
  have hsn : s.card = n := by omega
  exact ⟨⟨s, Finset.mem_filter.mpr ⟨hs, hsn⟩⟩, hFs, hts⟩

/-- The quotient Cartier point maps to the original Cartier point in every
full lifted chart. This is an equality of actual vectors. -/
theorem quotientFaceMap_cartierPoint (a : Lattice n → ℝ)
    (t : («Σ».completeQuotientStarFan b I hF).fullCones)
    (s : «Σ».fullCones) (hFs : I.image b ⊆ (s : Finset (Lattice n)))
    (hts : (t : Finset (Lattice (n - I.card))) =
      ((s : Finset (Lattice n)) \ I.image b).image (coneQuotientLattice b I)) :
    quotientFaceMap a b I
        ((«Σ».completeQuotientStarFan b I hF).cartierPoint («Σ».faceSupport b I hF a) t) =
      «Σ».cartierPoint a s := by
  let x := («Σ».completeQuotientStarFan b I hF).cartierPoint («Σ».faceSupport b I hF a) t
  have hactive (u : Lattice n) (hu : u ∈ (s : Finset (Lattice n))) :
      (dotProductEquiv ℝ (Fin n) (embed n u)) (quotientFaceMap a b I x) = -a u := by
    by_cases huF : u ∈ I.image b
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp huF
      exact quotientFaceMap_active a b I x i hi
    · have hut : coneQuotientLattice b I u ∈ (t : Finset (Lattice (n - I.card))) := by
        rw [hts]
        exact Finset.mem_image.mpr ⟨u, Finset.mem_sdiff.mpr ⟨hu, huF⟩, rfl⟩
      have hq := («Σ».completeQuotientStarFan b I hF).cartierPoint_support_eq
        («Σ».faceSupport b I hF a) t hut
      rw [«Σ».faceSupport_projected b I hF a («Σ».fullCones_mem s) hFs
        (Finset.mem_sdiff.mpr ⟨hu, huF⟩)] at hq
      rw [quotientFaceMap_pairing]
      change _ + (dotProductEquiv ℝ (Fin (n - I.card))
        (embed (n - I.card) (coneQuotientLattice b I u))) x = _
      rw [hq]
      ring
  apply (integralBasisReal (integralDualBasis («Σ».fullConeBasis s))).ext_elem
  intro i
  rw [← normal_pairing_eq_dual_coordinate, ← normal_pairing_eq_dual_coordinate]
  have hi : «Σ».fullConeBasis s i ∈ (s : Finset (Lattice n)) := by
    rw [«Σ».fullConeBasis_ray_set]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  rw [hactive _ hi, «Σ».cartierPoint_support_eq a s hi]

/-- The exact saturated face dictionary, including nef degenerate faces.
No extra inequality is discarded: containment in the original polytope is
proved first on all quotient Cartier points and then on their convex hull. -/
theorem quotientFaceMap_image_fanPolytope (hpure : «Σ».IsPure)
    (a : Lattice n → ℝ) (ha : «Σ».IsNef a) :
    quotientFaceMap a b I ''
      («Σ».completeQuotientStarFan b I hF).fanPolytope («Σ».faceSupport b I hF a) =
      «Σ».supportFace a (I.image b) := by
  let Ψ := «Σ».completeQuotientStarFan b I hF
  have hΨpure : Ψ.IsPure := «Σ».completeQuotientStarFan_isPure hpure b I hF
  have hΨnef : Ψ.IsNef («Σ».faceSupport b I hF a) :=
    «Σ».faceSupport_isNef b I hF a ha
  apply Set.Subset.antisymm
  · rintro x ⟨y, hy, rfl⟩
    have hcontain : Ψ.fanPolytope («Σ».faceSupport b I hF a) ⊆
        quotientFaceMap a b I ⁻¹' «Σ».supportFace a (I.image b) := by
      rw [Ψ.fanPolytope_eq_convexHull_cartier hΨpure _ hΨnef]
      apply convexHull_min
      · rintro z ⟨t, rfl⟩
        obtain ⟨s, hFs, hts⟩ := «Σ».exists_fullCone_lift b I hF t
        change quotientFaceMap a b I
          (Ψ.cartierPoint («Σ».faceSupport b I hF a) t) ∈ «Σ».supportFace a (I.image b)
        rw [«Σ».quotientFaceMap_cartierPoint b I hF a t s hFs hts]
        exact ⟨«Σ».cartierPoint_mem_of_nef ha s,
          fun u hu => «Σ».cartierPoint_support_eq a s (hFs hu)⟩
      · exact Convex.affine_preimage _ («Σ».convex_supportFace a (I.image b))
    exact hcontain hy
  · intro x hx
    have hactive : ∀ i ∈ I,
        (dotProductEquiv ℝ (Fin n) (embed n (b i))) x = -a (b i) :=
      fun i hi => hx.2 _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    obtain ⟨y, rfl⟩ := (mem_range_quotientFaceMap_iff a b I x).mpr hactive
    refine ⟨y, ?_, rfl⟩
    intro u hu
    let u' : Ψ.rays := ⟨u, hu⟩
    obtain ⟨s, hs, hFs, hv, hproj⟩ := «Σ».starRayLift_spec b I hF u'
    have hvray := «Σ».ray_mem_of_mem_cone hs (Finset.mem_sdiff.mp hv).1
    have hbound := hx.1 («Σ».starRayLift b I hF u') hvray
    rw [quotientFaceMap_pairing, hproj] at hbound
    have hsupp := «Σ».faceSupport_lift b I hF a u'
    change -«Σ».faceSupport b I hF a u ≤ _
    rw [hsupp]
    linarith

/-- Integral restriction coefficients use the actual integral affine
origin and the actual primitive lifts. -/
def faceSupportLattice (a : Lattice n → ℤ) : Lattice (n - I.card) → ℤ := fun u =>
  if hu : u ∈ («Σ».completeQuotientStarFan b I hF).rays then
    a («Σ».starRayLift b I hF ⟨u, hu⟩) +
      ∑ i, («Σ».starRayLift b I hF ⟨u, hu⟩) i * quotientFaceOriginLattice a b I i
  else 0

theorem faceSupportLattice_cast (a : Lattice n → ℤ) :
    (fun u => («Σ».faceSupportLattice b I hF a u : ℝ)) =
      «Σ».faceSupport b I hF (fun u => (a u : ℝ)) := by
  funext u
  by_cases hu : u ∈ («Σ».completeQuotientStarFan b I hF).rays
  · simp only [faceSupportLattice, faceSupport, dif_pos hu, Int.cast_add]
    rw [← embed_quotientFaceOrigin, normalRay_pairing_lattice]
  · simp only [faceSupportLattice, faceSupport, dif_neg hu, Int.cast_zero]

theorem quotientFaceIntegralChart_image_fanPolytope (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsNef (fun u => (a u : ℝ))) :
    (quotientFaceIntegralChart a b I).realMap ''
      («Σ».completeQuotientStarFan b I hF).fanPolytope
        (fun u => («Σ».faceSupportLattice b I hF a u : ℝ)) =
      «Σ».supportFace (fun u => (a u : ℝ)) (I.image b) := by
  rw [quotientFaceIntegralChart_realMap, «Σ».faceSupportLattice_cast]
  exact «Σ».quotientFaceMap_image_fanPolytope b I hF hpure _ ha

end PaperVerification.ToricGeometry.SmoothCompleteFan
end
end Source_ToricQuotientFaceSupport
-- END ORIGINAL PaperVerification.ToricQuotientFaceSupport


-- BEGIN ORIGINAL PaperVerification.ToricSliceReserve
section Source_ToricSliceReserve

-- original header: module
-- original header: public import PaperVerification.ToricFaceInheritance
-- original header: public import Mathlib.Data.Finset.Max
-- original header: public import Mathlib.Tactic.Push
-- original header: @[expose] public section
/-!
# A quantitative reserve for nonincident integral supporting facets

This is the local slack estimate used in Lemma 3.2. It follows directly from
the genuine tangent cone and long incident edges: one descending edge supplies
a negative integral coefficient, and a coefficient of greatest magnitude
controls every nonnegative coordinate displacement. No Mori statement is an
assumption of this estimate.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

/-- An affine functional evaluated on an arbitrary basis-coordinate displacement. -/
theorem affine_apply_add_basis_sum (f : E →ᵃ[ℝ] ℝ) (v : E)
    (b : Module.Basis ι ℝ E) (h : ι → ℝ) :
    f (v + ∑ i, h i • b i) = f v + ∑ i, h i * f.linear (b i) := by
  rw [add_comm]
  change f ((∑ i, h i • b i) +ᵥ v) = _
  rw [AffineMap.map_vadd]
  simp [map_sum, map_smul, vadd_eq_add, smul_eq_mul, add_comm]

/-- If an actual supporting affine functional is positive at a vertex, its
linear part is strictly negative on at least one incident basis direction. -/
theorem supporting_facet_has_descending_direction
    (P : Set E) (v : E) (b : Module.Basis ι ℝ E)
    (hcone : ∀ x ∈ P, ∀ i, 0 ≤ b.repr (x - v) i)
    (f : E →ᵃ[ℝ] ℝ) (hfv : 0 < f v)
    (htouch : ∃ y ∈ P, f y = 0) :
    ∃ i, f.linear (b i) < 0 := by
  by_contra hnone
  push_neg at hnone
  obtain ⟨y, hy, hfy⟩ := htouch
  have hsum : 0 ≤ ∑ i, b.repr (y - v) i * f.linear (b i) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hcone y hy i) (hnone i))
  have h := affine_apply_basis_coordinates f b v y
  rw [hfy] at h
  linarith

/-- The exact reserve `L - sum h` for every real nonnegative normal displacement.
The supporting facet must actually meet the polytope and be nonincident to the
chosen vertex. Its integrality is required on the primitive basis directions. -/
theorem nonincident_facet_displacement_reserve
    (P : Set E) (v : E) (b : Module.Basis ι ℝ E)
    (hcone : ∀ x ∈ P, ∀ i, 0 ≤ b.repr (x - v) i)
    (lengths : ι → ℝ) (L : ℝ) (hlength : ∀ i, L ≤ lengths i)
    (hedges : ∀ i, v + lengths i • b i ∈ P)
    (f : E →ᵃ[ℝ] ℝ) (hfeasible : ∀ x ∈ P, 0 ≤ f x)
    (hfv : 0 < f v) (htouch : ∃ y ∈ P, f y = 0)
    (hintegral : ∀ i, ∃ z : ℤ, (z : ℝ) = f.linear (b i))
    (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i) (hbudget : (∑ i, h i) ≤ L) :
    L - ∑ i, h i ≤ f (v + ∑ i, h i • b i) := by
  classical
  obtain ⟨i₀, hi₀⟩ := supporting_facet_has_descending_direction P v b hcone f hfv htouch
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset ι)
    (fun i => f.linear (b i)) ⟨i₀, Finset.mem_univ i₀⟩
  have hjneg : f.linear (b j) < 0 :=
    (hmin i₀ (Finset.mem_univ i₀)).trans_lt hi₀
  let c := -f.linear (b j)
  have hcpos : 0 < c := neg_pos.mpr hjneg
  have hc1 : 1 ≤ c := by
    obtain ⟨z, hz⟩ := hintegral j
    have hzneg : z < 0 := by exact_mod_cast (hz.symm ▸ hjneg)
    have hzbound : (1 : ℤ) ≤ -z := by omega
    dsimp only [c]
    rw [← hz]
    exact_mod_cast hzbound
  have hcoef (i : ι) : -c ≤ f.linear (b i) := by
    simpa only [c, neg_neg] using hmin i (Finset.mem_univ i)
  have hslack : L * c ≤ f v := by
    have hedge := hfeasible _ (hedges j)
    rw [affine_apply_add_smul] at hedge
    have hprod : L * c ≤ lengths j * c :=
      mul_le_mul_of_nonneg_right (hlength j) hcpos.le
    dsimp only [c] at hprod
    nlinarith
  have hsum : -(c * ∑ i, h i) ≤ ∑ i, h i * f.linear (b i) := by
    calc
      -(c * ∑ i, h i) = ∑ i, h i * (-c) := by
        simp [Finset.sum_mul, Finset.mul_sum, mul_comm]
      _ ≤ ∑ i, h i * f.linear (b i) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hcoef i) (hh i))
  have hscale : L - ∑ i, h i ≤ c * (L - ∑ i, h i) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hbudget) (sub_nonneg.mpr hc1)]
  rw [affine_apply_add_basis_sum]
  nlinarith

/-- Strict reserve prevents any nonincident facet from appearing before the
total displacement reaches the original edge bound. -/
theorem nonincident_facet_displacement_positive
    (P : Set E) (v : E) (b : Module.Basis ι ℝ E)
    (hcone : ∀ x ∈ P, ∀ i, 0 ≤ b.repr (x - v) i)
    (lengths : ι → ℝ) (L : ℝ) (hlength : ∀ i, L ≤ lengths i)
    (hedges : ∀ i, v + lengths i • b i ∈ P)
    (f : E →ᵃ[ℝ] ℝ) (hfeasible : ∀ x ∈ P, 0 ≤ f x)
    (hfv : 0 < f v) (htouch : ∃ y ∈ P, f y = 0)
    (hintegral : ∀ i, ∃ z : ℤ, (z : ℝ) = f.linear (b i))
    (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i) (hbudget : (∑ i, h i) < L) :
    0 < f (v + ∑ i, h i • b i) := by
  exact (sub_pos.mpr hbudget).trans_le
    (nonincident_facet_displacement_reserve P v b hcone lengths L hlength hedges f
      hfeasible hfv htouch hintegral h hh hbudget.le)

end PaperVerification.ToricGeometry
end
end Source_ToricSliceReserve
-- END ORIGINAL PaperVerification.ToricSliceReserve


-- BEGIN ORIGINAL PaperVerification.ToricDisplacedFaceReserve
section Source_ToricDisplacedFaceReserve

-- original header: module

-- original header: public import PaperVerification.ToricDisplacedEdgeBounds
-- original header: public import PaperVerification.ToricQuotientFaceSupport
-- original header: public import PaperVerification.ToricSliceReserve

-- original header: @[expose] public section

/-!
# Nonincident facets do not cut short displaced faces

The local integral slack estimate is applied to the actual primitive dual
coordinates of every Cartier vertex. Convexity then gives the same reserve
on the entire displaced face, including its real points and nef endpoints.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem sum_fullConeBasis_subset (s : «Σ».fullCones)
    (T : Finset (Lattice n)) (hTs : T ⊆ (s : Finset (Lattice n)))
    (h : Lattice n → ℝ) :
    (∑ i, facetWeight T h («Σ».fullConeBasis s i)) = ∑ u ∈ T, h u := by
  calc
    (∑ i, facetWeight T h («Σ».fullConeBasis s i)) =
        ∑ u ∈ (s : Finset (Lattice n)), facetWeight T h u := by
      rw [«Σ».fullConeBasis_ray_set, Finset.sum_image]
      exact fun i _ j _ he => («Σ».fullConeBasis s).injective he
    _ = ∑ u ∈ T, facetWeight T h u := by
      symm
      apply Finset.sum_subset hTs
      intro u hu huT
      simp only [facetWeight, if_neg huT]
    _ = ∑ u ∈ T, h u :=
      Finset.sum_congr rfl (fun u hu => by simp only [facetWeight, if_pos hu])

theorem cartierPoint_displacedSupport (a : Lattice n → ℝ)
    (T : Finset (Lattice n)) (h : Lattice n → ℝ) (s : «Σ».fullCones) :
    «Σ».cartierPoint (displacedSupport a T h) s = «Σ».cartierPoint a s +
      ∑ i, facetWeight T h («Σ».fullConeBasis s i) • «Σ».cartierBasis s i := by
  simp only [cartierPoint, displacedSupport, Pi.sub_apply, sub_smul,
    Finset.sum_sub_distrib, neg_sub, cartierBasis]
  abel

/-- The exact `e - sum h` reserve on every displaced Cartier point, derived
from actual contained axis segments and primitive integral normal vectors. -/
theorem displaced_cartier_nonincident_reserve (hpure : «Σ».IsPure)
    (a : Lattice n → ℝ) (ha : «Σ».IsStrictSupport a)
    (e : ℝ)
    (haxis : ∀ s : «Σ».fullCones, ∀ i,
      «Σ».cartierPoint a s + e • «Σ».cartierBasis s i ∈ «Σ».fanPolytope a)
    (T : Finset (Lattice n)) (h : Lattice n → ℝ)
    (hh : ∀ u ∈ T, 0 ≤ h u) (hbudget : (∑ u ∈ T, h u) ≤ e)
    (s : «Σ».fullCones) (hTs : T ⊆ (s : Finset (Lattice n)))
    (u : Lattice n) (hu : u ∈ «Σ».rays) (hus : u ∉ (s : Finset (Lattice n))) :
    e - ∑ v ∈ T, h v ≤
      a u + (dotProductEquiv ℝ (Fin n) (embed n u))
        («Σ».cartierPoint (displacedSupport a T h) s) := by
  let v := «Σ».cartierPoint a s
  let B := «Σ».cartierBasis s
  let f : Ambient n →ᵃ[ℝ] ℝ :=
    AffineMap.const ℝ _ (a u) + (dotProductEquiv ℝ (Fin n) (embed n u)).toAffineMap
  let α : Fin n → ℝ := fun i => facetWeight T h («Σ».fullConeBasis s i)
  have hα (i : Fin n) : 0 ≤ α i := by
    dsimp only [α, facetWeight]
    split_ifs with hi
    · exact hh _ hi
    · exact le_rfl
  have hsum : (∑ i, α i) = ∑ w ∈ T, h w := «Σ».sum_fullConeBasis_subset s T hTs h
  have hfeasible : ∀ x ∈ «Σ».fanPolytope a, 0 ≤ f x := by
    intro x hx
    have hxu := hx u hu
    change 0 ≤ a u + (dotProductEquiv ℝ (Fin n) (embed n u)) x
    linarith
  have hfv : 0 < f v := by
    have h := «Σ».cartierPoint_support_lt_of_not_mem ha s hu hus
    change 0 < a u + (dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint a s)
    linarith
  have htouch : ∃ y ∈ «Σ».fanPolytope a, f y = 0 := by
    obtain ⟨C, hC, huC⟩ := («Σ».mem_rays_iff u).mp hu
    obtain ⟨U, hU, hCU, hcard⟩ := hpure C hC
    let U' : «Σ».fullCones := ⟨U, Finset.mem_filter.mpr ⟨hU, hcard⟩⟩
    refine ⟨«Σ».cartierPoint a U', «Σ».cartierPoint_mem_of_nef (IsStrictSupport.isNef «Σ» ha) U', ?_⟩
    change a u + (dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint a U') = 0
    rw [«Σ».cartierPoint_support_eq a U' (hCU huC), add_neg_cancel]
  have hintegral (i : Fin n) : ∃ z : ℤ, (z : ℝ) = f.linear (B i) := by
    refine ⟨∑ j, u j * integralDualBasis («Σ».fullConeBasis s) i j, ?_⟩
    have hf : f.linear = dotProductEquiv ℝ (Fin n) (embed n u) := by
      simp only [f, AffineMap.add_linear, AffineMap.const_linear,
        LinearMap.toAffineMap_linear, zero_add]
    rw [hf]
    change _ = (dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierBasis s i)
    rw [cartierBasis, integralBasisReal_apply]
    exact (normalRay_pairing_lattice u (integralDualBasis («Σ».fullConeBasis s) i)).symm
  have hreserve := nonincident_facet_displacement_reserve
    («Σ».fanPolytope a) v B
    (fun x hx i => «Σ».cartierPoint_orthant s hx i)
    (fun _ => e) e (fun _ => le_rfl) (haxis s) f hfeasible hfv htouch hintegral
    α hα (by rw [hsum]; exact hbudget)
  rw [hsum] at hreserve
  rw [«Σ».cartierPoint_displacedSupport]
  exact hreserve

/-- A primitive facet not incident to the original face retains the same
reserve on every point of the displaced face. -/
theorem displaced_supportFace_nonincident_reserve (hpure : «Σ».IsPure)
    (a : Lattice n → ℝ) (ha : «Σ».IsStrictSupport a)
    (e : ℝ)
    (haxis : ∀ s : «Σ».fullCones, ∀ i,
      «Σ».cartierPoint a s + e • «Σ».cartierBasis s i ∈ «Σ».fanPolytope a)
    (T : Finset (Lattice n)) (hT : T ∈ «Σ».cones)
    (h : Lattice n → ℝ) (hh : ∀ u ∈ T, 0 ≤ h u)
    (hbudget : (∑ u ∈ T, h u) ≤ e)
    (hD : «Σ».IsNef (displacedSupport a T h))
    (u : Lattice n) (hu : u ∈ «Σ».rays) (huT : insert u T ∉ «Σ».cones)
    (x : Ambient n) (hx : x ∈ «Σ».supportFace (displacedSupport a T h) T) :
    e - ∑ v ∈ T, h v ≤ a u + (dotProductEquiv ℝ (Fin n) (embed n u)) x := by
  let f : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) (embed n u)
  have hall : «Σ».supportFace (displacedSupport a T h) T ⊆
      f ⁻¹' Ici (e - (∑ v ∈ T, h v) - a u) := by
    rw [«Σ».supportFace_eq_convexHull_cartier hpure _ hD T hT]
    apply convexHull_min
    · rintro z ⟨s, rfl⟩
      have hTs := (Finset.mem_filter.mp s.property).2
      have hus : u ∉ ((s : «Σ».fullCones) : Finset (Lattice n)) := by
        intro hus
        exact huT («Σ».downward _ («Σ».fullCones_mem s) _ (Finset.insert_subset hus hTs))
      have hreserveVertex := «Σ».displaced_cartier_nonincident_reserve hpure a ha e haxis
        T h hh hbudget s hTs u hu hus
      change e - (∑ v ∈ T, h v) - a u ≤ _
      linarith
    · exact (convex_Ici _).linear_preimage f
  have hl := hall hx
  change e - (∑ v ∈ T, h v) - a u ≤ f x at hl
  change _ ≤ a u + f x
  linarith

/-- The preceding real-height reserve follows from the literal original
edge bound of the integral support polytope. -/
theorem displaced_supportFace_reserve_of_edges (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {e : ℕ} (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (T : Finset (Lattice n)) (hT : T ∈ «Σ».cones)
    (h : Lattice n → ℝ) (hh : ∀ u ∈ T, 0 ≤ h u)
    (hbudget : (∑ u ∈ T, h u) ≤ e)
    (hD : «Σ».IsNef (displacedSupport (fun u => (a u : ℝ)) T h))
    (u : Lattice n) (hu : u ∈ «Σ».rays) (huT : insert u T ∉ «Σ».cones)
    (x : Ambient n) (hx : x ∈ «Σ».supportFace
      (displacedSupport (fun u => (a u : ℝ)) T h) T) :
    (e : ℝ) - ∑ v ∈ T, h v ≤ (a u : ℝ) +
      (dotProductEquiv ℝ (Fin n) (embed n u)) x :=
  «Σ».displaced_supportFace_nonincident_reserve hpure _ ha e
    («Σ».support_axis_point_of_edgesAtLeast hpure a ha hedges)
    T hT h hh hbudget hD u hu huT x hx

end PaperVerification.ToricGeometry.SmoothCompleteFan
end
end Source_ToricDisplacedFaceReserve
-- END ORIGINAL PaperVerification.ToricDisplacedFaceReserve


-- BEGIN ORIGINAL PaperVerification.ToricNefBoxes
section Source_ToricNefBoxes

-- original header: module

-- original header: public import PaperVerification.ToricFanPolytopes

-- original header: @[expose] public section

/-!
# Corner boxes of genuine nef support polytopes

This form of the corner criterion includes degenerate nef endpoints. The
polytope remains its actual primitive halfspace intersection, and every
corner is obtained from a separately proved nef support subtraction.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem fanPolytope_mono {a c : Lattice n → ℝ}
    (h : ∀ u ∈ «Σ».rays, a u ≤ c u) : «Σ».fanPolytope a ⊆ «Σ».fanPolytope c := by
  intro x hx u hu
  exact (neg_le_neg (h u hu)).trans (hx u hu)

theorem cartierPoint_sub_cone_selection (a : Lattice n → ℝ)
    (s : «Σ».fullCones) (I : Finset (Fin n)) (side : ℝ) :
    «Σ».cartierPoint (a - side • (fun u =>
      if u ∈ I.image («Σ».fullConeBasis s) then 1 else 0)) s =
      «Σ».cartierPoint a s + side • (∑ i ∈ I, «Σ».cartierBasis s i) := by
  have hmem (i : Fin n) : «Σ».fullConeBasis s i ∈ I.image («Σ».fullConeBasis s) ↔ i ∈ I := by
    simp only [Finset.mem_image, («Σ».fullConeBasis s).injective.eq_iff]
    simp
  simp only [cartierPoint, cartierBasis, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    hmem, sub_smul, Finset.sum_sub_distrib, neg_sub]
  have he : (∑ i, (side * if i ∈ I then (1 : ℝ) else 0) •
      integralBasisReal (integralDualBasis («Σ».fullConeBasis s)) i) =
      side • ∑ i ∈ I, integralBasisReal (integralDualBasis («Σ».fullConeBasis s)) i := by
    simp only [mul_ite, mul_one, mul_zero, ite_smul, zero_smul]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.smul_sum]
  rw [he]
  abel

theorem corner_vertex_mem_fanPolytope {a : Lattice n → ℝ}
    (s : «Σ».fullCones) (I : Finset (Fin n)) (side : ℝ) (hside : 0 ≤ side)
    (hnef : «Σ».IsNef (a - side • (fun u =>
      if u ∈ I.image («Σ».fullConeBasis s) then 1 else 0))) :
    «Σ».cartierPoint a s + side • (∑ i ∈ I, «Σ».cartierBasis s i) ∈ «Σ».fanPolytope a := by
  rw [← «Σ».cartierPoint_sub_cone_selection]
  apply «Σ».fanPolytope_mono (a := a - side • _) ?_ («Σ».cartierPoint_mem_of_nef hnef s)
  intro u hu
  change a u - side * (if u ∈ I.image («Σ».fullConeBasis s) then 1 else 0) ≤ a u
  split_ifs <;> nlinarith

theorem corner_box_mem_fanPolytope_of_vertices (a : Lattice n → ℝ)
    (v : Ambient n) (B : Fin n → Ambient n) (side : ℝ)
    (hvertices : ∀ I : Finset (Fin n), v + side • (∑ i ∈ I, B i) ∈ «Σ».fanPolytope a)
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ side) :
    v + ∑ i, t i • B i ∈ «Σ».fanPolytope a := by
  intro u hu
  let f : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) (embed n u)
  let I := Finset.univ.filter (fun i => f (B i) < 0)
  have hv := hvertices I u hu
  have hmin : f (v + side • (∑ i ∈ I, B i)) ≤ f (v + ∑ i, t i • B i) := by
    simp only [map_add, map_sum, map_smul, smul_eq_mul]
    apply add_le_add le_rfl
    rw [Finset.mul_sum]
    calc
      (∑ i ∈ I, side * f (B i)) =
          ∑ i, if i ∈ I then side * f (B i) else 0 := by simp
      _ ≤ ∑ i, t i * f (B i) := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hiI : i ∈ I
        · rw [if_pos hiI]
          exact mul_le_mul_of_nonpos_right (ht i).2 (Finset.mem_filter.mp hiI).2.le
        · rw [if_neg hiI]
          have hf : 0 ≤ f (B i) := by
            simpa only [I, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hiI
          exact mul_nonneg (ht i).1 hf
  exact hv.trans hmin

/-- Full corner boxes, including every real point and every nef endpoint,
follow from actual contractible primitive degree inequalities. -/
theorem corner_box_mem_fanPolytope (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun u => (H u : ℝ)))
    (a : Lattice n → ℝ) (side : ℝ) (hside : 0 ≤ side)
    (hdegree : ∀ R : «Σ».PrimitiveRelation, R.IsCombinatoriallyContractible →
      side * R.fiberDimension ≤ R.degree a)
    (s : «Σ».fullCones) (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ side) :
    «Σ».cartierPoint a s + ∑ i, t i • «Σ».cartierBasis s i ∈ «Σ».fanPolytope a := by
  apply «Σ».corner_box_mem_fanPolytope_of_vertices a _ _ side ?_ t ht
  intro I
  apply «Σ».corner_vertex_mem_fanPolytope s I side hside
  apply «Σ».nef_sub_cone_selection_of_contractible_degrees hpure H hH a side hside hdegree
    («Σ».fullCones_mem s)
  rw [«Σ».fullConeBasis_ray_set]
  exact Finset.image_subset_image (Finset.subset_univ I)

end PaperVerification.ToricGeometry.SmoothCompleteFan
end
end Source_ToricNefBoxes
-- END ORIGINAL PaperVerification.ToricNefBoxes


-- BEGIN ORIGINAL PaperVerification.ToricCanonicalSlices
section Source_ToricCanonicalSlices

-- original header: module

-- original header: public import PaperVerification.ToricDisplacedFaceReserve
-- original header: public import PaperVerification.ToricNefBoxes

-- original header: @[expose] public section

/-!
# Exact canonical slices on the saturated face lattice

The canonical shift is literally subtraction of one at every primitive
normal. Active normal heights at least one satisfy the deleted inequalities.
Adjacent rays give exactly the quotient canonical shift; the proved reserve
shows that nonincident original facets make no further cut.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b ∈ «Σ».cones)

/-- Exact adjunction on the actual affine slice. The reserve premise is
discharged from original edge lengths in the next theorem. -/
theorem canonical_slice_eq_of_reserve (hpure : «Σ».IsPure)
    (a : Lattice n → ℝ) (h : Lattice n → ℝ)
    (hh : ∀ u ∈ I.image b, 1 ≤ h u)
    (hD : «Σ».IsNef (displacedSupport a (I.image b) h))
    (hreserve : ∀ u ∈ «Σ».rays, insert u (I.image b) ∉ «Σ».cones →
      ∀ x ∈ «Σ».supportFace (displacedSupport a (I.image b) h) (I.image b),
        1 ≤ a u + (dotProductEquiv ℝ (Fin n) (embed n u)) x) :
    quotientFaceMap (displacedSupport a (I.image b) h) b I ''
      («Σ».completeQuotientStarFan b I hF).fanPolytope
        (fun u => «Σ».faceSupport b I hF (displacedSupport a (I.image b) h) u - 1) =
      {x ∈ «Σ».fanPolytope (fun u => a u - 1) | ∀ u ∈ I.image b,
        (dotProductEquiv ℝ (Fin n) (embed n u)) x + a u = h u} := by
  let D := displacedSupport a (I.image b) h
  let Ψ := «Σ».completeQuotientStarFan b I hF
  have hh0 : ∀ u ∈ I.image b, 0 ≤ h u := fun u hu => (by norm_num : (0 : ℝ) ≤ 1).trans (hh u hu)
  have himage := «Σ».quotientFaceMap_image_fanPolytope b I hF hpure D hD
  apply Set.Subset.antisymm
  · rintro x ⟨z, hz, rfl⟩
    have hzparent : z ∈ Ψ.fanPolytope («Σ».faceSupport b I hF D) := by
      apply Ψ.fanPolytope_mono (a := fun u => «Σ».faceSupport b I hF D u - 1)
        (fun u hu => by linarith) hz
    have hface : quotientFaceMap D b I z ∈ «Σ».supportFace D (I.image b) := by
      rw [← himage]
      exact ⟨z, hzparent, rfl⟩
    have hslice : quotientFaceMap D b I z ∈
        {x ∈ «Σ».fanPolytope a | ∀ u ∈ I.image b,
          (dotProductEquiv ℝ (Fin n) (embed n u)) x + a u = h u} := by
      rw [← «Σ».displaced_supportFace_eq_slice a (I.image b) h hh0]
      exact hface
    refine ⟨?_, hslice.2⟩
    intro u hu
    by_cases huF : u ∈ I.image b
    · have hheight := hslice.2 u huF
      have hhu := hh u huF
      change -(a u - 1) ≤ _
      linarith
    · by_cases hadj : insert u (I.image b) ∈ «Σ».cones
      · have hv : u ∈ insert u (I.image b) \ I.image b :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self _ _, huF⟩
        have hqray := «Σ».projected_starRay_mem b I hF hadj (Finset.subset_insert _ _) hv
        have hq := hz (coneQuotientLattice b I u) hqray
        have hcoeff := «Σ».faceSupport_projected b I hF D hadj (Finset.subset_insert _ _) hv
        have hDu : D u = a u := by
          simp only [D, displacedSupport, Pi.sub_apply, facetWeight, if_neg huF, sub_zero]
        rw [hDu] at hcoeff
        change -(«Σ».faceSupport b I hF D (coneQuotientLattice b I u) - 1) ≤ _ at hq
        rw [hcoeff] at hq
        rw [quotientFaceMap_pairing]
        change -(a u - 1) ≤ _
        linarith
      · have hr := hreserve u hu hadj (quotientFaceMap D b I z) hface
        change -(a u - 1) ≤ _
        linarith
  · intro x hx
    have hxparent : x ∈ «Σ».fanPolytope a :=
      «Σ».fanPolytope_mono (a := fun u => a u - 1) (fun u hu => by linarith) hx.1
    have hface : x ∈ «Σ».supportFace D (I.image b) := by
      rw [«Σ».displaced_supportFace_eq_slice a (I.image b) h hh0]
      exact ⟨hxparent, hx.2⟩
    have hactive : ∀ i ∈ I,
        (dotProductEquiv ℝ (Fin n) (embed n (b i))) x = -D (b i) :=
      fun i hi => hface.2 _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    obtain ⟨z, rfl⟩ := (mem_range_quotientFaceMap_iff D b I x).mpr hactive
    refine ⟨z, ?_, rfl⟩
    intro u hu
    let u' : Ψ.rays := ⟨u, hu⟩
    obtain ⟨s, hs, hFs, hv, hproj⟩ := «Σ».starRayLift_spec b I hF u'
    let v := «Σ».starRayLift b I hF u'
    have hvray := «Σ».ray_mem_of_mem_cone hs (Finset.mem_sdiff.mp hv).1
    have hvF : v ∉ I.image b := (Finset.mem_sdiff.mp hv).2
    have hbound := hx.1 v hvray
    rw [quotientFaceMap_pairing, hproj] at hbound
    have hcoeff := «Σ».faceSupport_lift b I hF D u'
    have hDv : D v = a v := by
      simp only [D, displacedSupport, Pi.sub_apply, facetWeight, if_neg hvF, sub_zero]
    rw [hDv] at hcoeff
    change -(«Σ».faceSupport b I hF D u - 1) ≤ _
    rw [hcoeff]
    change -(a v - 1) ≤ _ at hbound
    linarith

/-- Equation (13) with the nonincident-facet reserve proved from the
literal original edge bound. The heights are arbitrary real numbers. -/
theorem canonical_slice_eq_of_edges (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {e : ℕ} (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (h : Lattice n → ℝ) (hh : ∀ u ∈ I.image b, 1 ≤ h u)
    (hbudget : (∑ u ∈ I.image b, h u) + 1 ≤ (e : ℝ)) :
    quotientFaceMap (displacedSupport (fun u => (a u : ℝ)) (I.image b) h) b I ''
      («Σ».completeQuotientStarFan b I hF).fanPolytope
        (fun u => «Σ».faceSupport b I hF
          (displacedSupport (fun u => (a u : ℝ)) (I.image b) h) u - 1) =
      {x ∈ «Σ».fanPolytope (fun u => (a u : ℝ) - 1) | ∀ u ∈ I.image b,
        (dotProductEquiv ℝ (Fin n) (embed n u)) x + (a u : ℝ) = h u} := by
  have hh0 : ∀ v ∈ I.image b, 0 ≤ h v :=
    fun v hv => (by norm_num : (0 : ℝ) ≤ 1).trans (hh v hv)
  have hD := «Σ».displacedSupport_isNef_of_edges hpure a ha hedges (I.image b) h hh0
    (by linarith)
  apply «Σ».canonical_slice_eq_of_reserve b I hF hpure _ h hh hD
  intro u hu huF x hx
  have hr := «Σ».displaced_supportFace_reserve_of_edges hpure a ha hedges
    (I.image b) hF h hh0 (by linarith) hD u hu huF x hx
  linarith

end PaperVerification.ToricGeometry.SmoothCompleteFan
end
end Source_ToricCanonicalSlices
-- END ORIGINAL PaperVerification.ToricCanonicalSlices


-- BEGIN ORIGINAL PaperVerification.ToricCorrectionBounds
section Source_ToricCorrectionBounds

-- original header: module
-- original header: public import Mathlib.Algebra.Order.Floor.Ring
-- original header: public import Mathlib.Data.Real.Basic
-- original header: public import Mathlib.Tactic.Linarith
-- original header: public import Mathlib.Tactic.NormNum
-- original header: public import Mathlib.Tactic.Positivity
-- original header: public import Lean.Elab.Tactic.Omega
-- original header: @[expose] public section
/-!
# Exact numerical bounds for the corrected boxes

These are the integer ceiling and degree calculations in Sections 5--7.
Every geometric premise is kept explicit. No contraction, positivity, or
box-containment conclusion is built into these purely numerical statements.
-/

namespace PaperVerification.ToricGeometry

/-- An integer ceiling correction with positive integral slope is bounded by
the nonnegative part of the deficit. -/
theorem ceil_div_le_positivePart (δ a : ℤ) (ha : 1 ≤ a) :
    Int.ceil ((δ : ℝ) / (a : ℝ)) ≤ max δ 0 := by
  apply Int.ceil_le.mpr
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hmax0 : (0 : ℝ) ≤ (max δ 0 : ℤ) := by exact_mod_cast le_max_right δ 0
  have hmaxδ : (δ : ℝ) ≤ (max δ 0 : ℤ) := by exact_mod_cast le_max_left δ 0
  apply (div_le_iff₀ (show (0 : ℝ) < a by linarith)).mpr
  nlinarith [mul_nonneg hmax0 (sub_nonneg.mpr haR)]

/-- The ceiling supplies enough correction to repair the actual deficit. -/
theorem deficit_le_mul_ceil_div (δ a : ℤ) (ha : 1 ≤ a) :
    δ ≤ a * Int.ceil ((δ : ℝ) / (a : ℝ)) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast (show (0 : ℤ) < a by omega)
  have h := (div_le_iff₀ haR).mp (Int.le_ceil ((δ : ℝ) / (a : ℝ)))
  have h' : (δ : ℝ) ≤ (a : ℝ) * (Int.ceil ((δ : ℝ) / (a : ℝ)) : ℝ) := by
    nlinarith
  exact_mod_cast h'

/-- For a strictly positive deficit the correction is a positive integer,
at most the deficit itself. -/
theorem positive_ceil_correction (δ a : ℤ) (hδ : 0 < δ) (ha : 1 ≤ a) :
    1 ≤ Int.ceil ((δ : ℝ) / (a : ℝ)) ∧
      Int.ceil ((δ : ℝ) / (a : ℝ)) ≤ δ ∧
      δ ≤ a * Int.ceil ((δ : ℝ) / (a : ℝ)) := by
  have hrepair := deficit_le_mul_ceil_div δ a ha
  have hupper := ceil_div_le_positivePart δ a ha
  rw [max_eq_left hδ.le] at hupper
  have hpos : 0 < Int.ceil ((δ : ℝ) / (a : ℝ)) := by
    by_contra h
    have hnonpos : Int.ceil ((δ : ℝ) / (a : ℝ)) ≤ 0 := le_of_not_gt h
    have hprod : a * Int.ceil ((δ : ℝ) / (a : ℝ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by omega) hnonpos
    omega
  exact ⟨by omega, hupper, hrepair⟩

/-- The exact common-blowup displacement chosen for the parity boxes. -/
noncomputable def parityCorrection (r q d a : ℤ) : ℤ :=
  max (2 * (q - 1)) (max (Int.ceil (((2 * r - d : ℤ) : ℝ) / (a : ℝ))) 0)

/-- All bounds in Section 6.2, including the fiber-degree repair, for the
exact integer correction used by the paper. -/
theorem parityCorrection_bounds (n r q b d a : ℤ)
    (hqdim : 1 ≤ q) (hb : 0 ≤ b) (ha : 1 ≤ a)
    (hdim : n = r + q + b) (hlarge : n < 2 * r) (hd : n ≤ d) :
    0 ≤ parityCorrection r q d a ∧
      2 * (q - 1) ≤ parityCorrection r q d a ∧
      parityCorrection r q d a ≤ n - 2 * b - 2 ∧
      parityCorrection r q d a ≤ r + q - 2 ∧
      2 * r ≤ d + a * parityCorrection r q d a := by
  let c := Int.ceil (((2 * r - d : ℤ) : ℝ) / (a : ℝ))
  have hc : c ≤ 2 * r - n := by
    apply (ceil_div_le_positivePart (2 * r - d) a ha).trans
    exact max_le (by omega) (by omega)
  have hbase : 2 * (q - 1) ≤ parityCorrection r q d a :=
    le_max_left _ _
  have hct : c ≤ parityCorrection r q d a :=
    (le_max_left _ _).trans (le_max_right _ _)
  have ht0 : 0 ≤ parityCorrection r q d a :=
    (le_max_right _ _).trans (le_max_right _ _)
  have htupper : parityCorrection r q d a ≤ n - 2 * b - 2 := by
    unfold parityCorrection
    apply max_le
    · omega
    · apply max_le
      · dsimp [c] at hc
        omega
      · omega
  have hrepair := deficit_le_mul_ceil_div (2 * r - d) a ha
  have hproduct : a * c ≤ a * parityCorrection r q d a :=
    mul_le_mul_of_nonneg_left hct (by omega)
  exact ⟨ht0, hbase, htupper, by omega, by dsimp [c] at hproduct; omega⟩

/-- The exact displacement of the inner unit boxes in Section 7.3. -/
noncomputable def adjointCorrection (r q d coefficientSum a : ℤ) : ℤ :=
  max (2 * (q - 1))
    (q - 1 + Int.ceil (((2 * r + 1 - d - coefficientSum : ℤ) : ℝ) / (a : ℝ)))

/-- Bounds for an actually selected adjoint obstruction. The coefficient sum
is at least the number of negative rays because each coefficient is positive. -/
theorem adjointCorrection_bounds (n r q b d coefficientSum a : ℤ)
    (hq : 1 ≤ q) (hb : 0 ≤ b) (ha : 1 ≤ a)
    (hdim : n = r + q + b) (hd : n + 1 ≤ d)
    (hcoeff : q ≤ coefficientSum) (hselected : 0 < 2 * r + 1 - d - coefficientSum) :
    n < 2 * r ∧
      2 * (q - 1) ≤ adjointCorrection r q d coefficientSum a ∧
      adjointCorrection r q d coefficientSum a ≤ n - 2 * b - 2 ∧
      2 * r + 1 ≤ d + coefficientSum +
        a * (adjointCorrection r q d coefficientSum a + 1 - q) := by
  let δ := 2 * r + 1 - d - coefficientSum
  let c := Int.ceil ((δ : ℝ) / (a : ℝ))
  have hδ : 0 < δ := hselected
  have hc : c ≤ δ := (positive_ceil_correction δ a hδ ha).2.1
  have hrepair : δ ≤ a * c := deficit_le_mul_ceil_div δ a ha
  have hlarge : n < 2 * r := by omega
  have hbase : 2 * (q - 1) ≤ adjointCorrection r q d coefficientSum a :=
    le_max_left _ _
  have hct : q - 1 + c ≤ adjointCorrection r q d coefficientSum a :=
    le_max_right _ _
  have htupper : adjointCorrection r q d coefficientSum a ≤ n - 2 * b - 2 := by
    unfold adjointCorrection
    apply max_le
    · omega
    · change q - 1 + c ≤ _
      dsimp [δ] at hc
      omega
  have hproduct : a * c ≤
      a * (adjointCorrection r q d coefficientSum a + 1 - q) :=
    mul_le_mul_of_nonneg_left (by omega) (by omega)
  exact ⟨hlarge, hbase, htupper, by dsimp [δ] at hrepair; omega⟩

/-- Equation (8): an activated correction is positive and obeys the precise
normal-coordinate budget. -/
theorem activatedCorrection_bounds (n r q A k δ a : ℤ)
    (hA : A ≤ r) (hk : 0 ≤ k) (hδ : 0 < δ) (ha : 1 ≤ a)
    (hbudget : δ ≤ 2 * A - 2 * k - n) :
    1 ≤ Int.ceil ((δ : ℝ) / (a : ℝ)) ∧
      Int.ceil ((δ : ℝ) / (a : ℝ)) ≤ 2 * A - 2 * k - n ∧
      Int.ceil ((δ : ℝ) / (a : ℝ)) ≤ 2 * r - n := by
  obtain ⟨hpos, hup, _⟩ := positive_ceil_correction δ a hδ ha
  exact ⟨hpos, by omega, by omega⟩

/-- Proposition 5.2's one-positive-exceptional-divisor estimate. -/
theorem outside_box_one_positive_bound (n r q b s k τ : ℤ)
    (hdim : n = r + q + b) (hs : s ≤ b + 2)
    (hk : k ≤ q - 1) (hτ : τ ≤ 2 * r - n) :
    0 ≤ n - 2 * (s - 1) - 2 * k - τ := by omega

/-- The complementary two-positive-divisor estimates force a positive
degree; no sign is lost by choosing one of the two estimates. -/
theorem outside_box_two_positive_bound (n b : ℝ) (degree : ℝ)
    (hfirst : 2 * b + 4 - n ≤ degree)
    (hsecond : n - 2 * b - 2 ≤ degree) : 1 ≤ degree := by linarith

/-- A parity center remains nef in the one-positive-divisor case. -/
theorem parity_center_one_positive_bound (n r q b s t : ℤ)
    (hdim : n = r + q + b) (hs : s ≤ b + 2) (ht : t ≤ r + q - 2) :
    0 ≤ n - s - t := by omega

/-- The parity center has positive degree in the two-positive-divisor case. -/
theorem parity_center_two_positive_bound (n ri qi bi rj qj bj q' ti tj : ℤ)
    (hdi : n = ri + qi + bi) (hdj : n = rj + qj + bj)
    (hnegative : n - 1 - bi - bj ≤ q')
    (hti : ti ≤ ri + qi - 2) (htj : tj ≤ rj + qj - 2) :
    1 ≤ n - 2 + q' - ti - tj := by omega

/-- Twice the Section 7.4 one-positive-divisor lower bound, avoiding any
rounding of the half-canonical coefficient. -/
theorem adjoint_center_one_positive_bound (n b t : ℤ)
    (ht : t ≤ n - 2 * b - 2) :
    b ≤ 2 * (n + 1) - 3 * (b + 2) - 2 * t := by omega

/-- Twice the corresponding two-positive-divisor bound. -/
theorem adjoint_center_two_positive_bound (n bi bj q' ti tj : ℤ)
    (hnegative : n - 1 - bi - bj ≤ q')
    (hti : ti ≤ n - 2 * bi - 2) (htj : tj ≤ n - 2 * bj - 2) :
    n + bi + bj + 1 ≤ 2 * (n - 2) + 3 * q' - 2 * ti - 2 * tj := by omega

/-- The first center's one-positive-divisor degree estimate in Section 7.4. -/
theorem first_adjoint_center_one_positive_bound (n r q b s : ℤ)
    (hdim : n = r + q + b) (hs : s ≤ b + 2) :
    2 * r + b + 2 ≤ 2 * (n + 1) - s - 2 * (q - 1) := by omega

/-- Large disjoint contraction parameters force the strict codimension sum
used by both center estimates. -/
theorem large_loci_codimension_sum_lt (n ri qi bi rj qj bj : ℤ)
    (hdi : n = ri + qi + bi) (hdj : n = rj + qj + bj)
    (hbi : 0 ≤ bi) (hbj : 0 ≤ bj) (hri : n < 2 * ri) (hrj : n < 2 * rj) :
    qi + qj < n := by omega

end PaperVerification.ToricGeometry

end Source_ToricCorrectionBounds
-- END ORIGINAL PaperVerification.ToricCorrectionBounds


-- BEGIN ORIGINAL PaperVerification.ToricMinimumCoefficient
section Source_ToricMinimumCoefficient

-- original header: module

-- original header: public import PaperVerification.ToricPrimitiveRelations
-- original header: public import Mathlib.Data.Finset.Max

-- original header: @[expose] public section

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan.PrimitiveRelation

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} (R : «Σ».PrimitiveRelation)

/-- The actual least positive coefficient on a nonempty focus. -/
def minimumCoefficient (hne : R.negative.Nonempty) : ℕ :=
  R.coefficient (Classical.choose (R.negative.exists_min_image R.coefficient hne))

theorem minimumCoefficient_spec (hne : R.negative.Nonempty) :
    0 < R.minimumCoefficient hne ∧
      (∃ p ∈ R.negative, R.coefficient p = R.minimumCoefficient hne) ∧
      ∀ v ∈ R.negative, R.minimumCoefficient hne ≤ R.coefficient v := by
  let p := Classical.choose (R.negative.exists_min_image R.coefficient hne)
  have hp := Classical.choose_spec (R.negative.exists_min_image R.coefficient hne)
  exact ⟨R.coefficient_pos p hp.1, ⟨p, hp.1, rfl⟩, hp.2⟩

end PaperVerification.ToricGeometry.SmoothCompleteFan.PrimitiveRelation
end
end Source_ToricMinimumCoefficient
-- END ORIGINAL PaperVerification.ToricMinimumCoefficient


-- BEGIN ORIGINAL PaperVerification.ToricStrictSupportFaces
section Source_ToricStrictSupportFaces

-- original header: module
-- original header: public import PaperVerification.ToricFiniteSupportPerturbation
-- original header: public import PaperVerification.ToricFiniteConeFamily
-- original header: public import Mathlib.Tactic.NormNum
-- original header: @[expose] public section

/-!
# Strict supporting functions on coordinate faces

Strict support on a cone can be refined to strict support on any of its
coordinate faces. The proof perturbs by the sum of the omitted dual
coordinates and preserves every other strict inequality by an explicit
finite perturbation lemma.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

/-- Sum of the real dual coordinates selected by a finite set of integral
basis rays. -/
def raySelectorFunctional {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n))
    (s : Finset (Lattice n)) : Ambient n →ₗ[ℝ] ℝ :=
  ∑ i ∈ basisRayIndices b s, (integralBasisReal b).coord i

theorem raySelectorFunctional_basis {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (s : Finset (Lattice n)) (j : Fin n) :
    raySelectorFunctional b s (embed n (b j)) = if b j ∈ s then 1 else 0 := by
  rw [← integralBasisReal_apply b j]
  simp [raySelectorFunctional, basisRayIndices, Module.Basis.coord_apply,
    Module.Basis.repr_self_apply, Finsupp.single_apply]

/-- Strict support on a smooth cone extends to every actual ray-subset
face, with the same prescribed coefficients on the whole finite ray set. -/
theorem exists_strict_support_subset {n : ℕ}
    (R s t : Finset (Lattice n)) (a : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (hs : s ⊆ Finset.univ.image b)
    (hts : t ⊆ s) (ℓ : Ambient n →ₗ[ℝ] ℝ)
    (heq : ∀ v ∈ s, ℓ (embed n v) = a v)
    (hlt : ∀ v ∈ R, v ∉ s → ℓ (embed n v) < a v) :
    ∃ k : Ambient n →ₗ[ℝ] ℝ,
      (∀ v ∈ t, k (embed n v) = a v) ∧
      (∀ v ∈ R, v ∉ t → k (embed n v) < a v) := by
  let g : Ambient n →ₗ[ℝ] ℝ := -raySelectorFunctional b (s \ t)
  have hg (v : Lattice n) (hv : v ∈ s) :
      g (embed n v) = if v ∈ t then 0 else -1 := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hs hv)
    simp only [g, LinearMap.neg_apply, raySelectorFunctional_basis]
    by_cases hit : b i ∈ t
    · simp [Finset.mem_sdiff, hv, hit]
    · simp [Finset.mem_sdiff, hv, hit]
  have hactive : ∀ u ∈ ({t} : Finset (Finset (Lattice n))), ∀ v ∈ u,
      ℓ (embed n v) = a v ∧ g (embed n v) = (0 : Lattice n → ℝ) v := by
    intro u hu v hv
    have hut := Finset.mem_singleton.mp hu
    subst u
    refine ⟨heq v (hts hv), ?_⟩
    simp only [hg v (hts hv), if_pos hv, Pi.zero_apply]
  have hinactive : ∀ u ∈ ({t} : Finset (Finset (Lattice n))), ∀ v ∈ R, v ∉ u →
      ℓ (embed n v) < a v ∨
      (ℓ (embed n v) = a v ∧ g (embed n v) < (0 : Lattice n → ℝ) v) := by
    intro u hu v hv hvu
    have hut := Finset.mem_singleton.mp hu
    subst u
    by_cases hvs : v ∈ s
    · right
      refine ⟨heq v hvs, ?_⟩
      simp only [hg v hvs, if_neg hvu, Pi.zero_apply]
      norm_num
    · exact Or.inl (hlt v hv hvs)
  obtain ⟨ε, hε, hsupport⟩ := finite_lexicographic_support_perturbation
    {t} R a 0 (fun _ => ℓ) (fun _ => g) hactive hinactive
  refine ⟨ℓ + ε • g, ?_⟩
  simpa only [Pi.zero_apply, mul_zero, add_zero] using
    hsupport t (Finset.mem_singleton_self t)

/-- Strict support supplied on a finite smooth cone family descends to the
entire fan obtained by taking all its coordinate faces. -/
theorem strictSupport_fanOfFiniteSmoothCones {n : ℕ}
    (C : Finset (Finset (Lattice n)))
    (hsmooth : ∀ s ∈ C, ∃ b : Module.Basis (Fin n) ℤ (Lattice n),
      s ⊆ Finset.univ.image b)
    (hinter : ∀ s ∈ C, ∀ t ∈ C,
      latticeRayCone s ⊓ latticeRayCone t = latticeRayCone (s ∩ t))
    (hcover : ∀ x : Ambient n, ∃ s ∈ C, x ∈ latticeRayCone s)
    (R : Finset (Lattice n)) (hR : ∀ s ∈ C, s ⊆ R)
    (a : Lattice n → ℝ)
    (hsupport : ∀ s ∈ C, ∃ ℓ : Ambient n →ₗ[ℝ] ℝ,
      (∀ v ∈ s, ℓ (embed n v) = a v) ∧
      (∀ v ∈ R, v ∉ s → ℓ (embed n v) < a v)) :
    (fanOfFiniteSmoothCones C hsmooth hinter hcover).IsStrictSupport a := by
  let «Σ» := fanOfFiniteSmoothCones C hsmooth hinter hcover
  intro t ht
  obtain ⟨s, hs, hts⟩ := (mem_finiteConeFamilyClosure C t).mp ht
  obtain ⟨b, hb⟩ := hsmooth s hs
  obtain ⟨ℓ, heq, hlt⟩ := hsupport s hs
  obtain ⟨k, hkeq, hklt⟩ := exists_strict_support_subset R s t a b hb hts ℓ heq hlt
  refine ⟨k, hkeq, ?_⟩
  intro v hv hvt
  obtain ⟨u, hu, hvu⟩ := («Σ».mem_rays_iff v).mp hv
  obtain ⟨z, hz, huz⟩ := (mem_finiteConeFamilyClosure C u).mp hu
  exact hklt v (hR z hz (huz hvu)) hvt

end PaperVerification.ToricGeometry
end
end Source_ToricStrictSupportFaces
-- END ORIGINAL PaperVerification.ToricStrictSupportFaces


-- BEGIN ORIGINAL PaperVerification.ToricStarStrictSupport
section Source_ToricStarStrictSupport

-- original header: module
-- original header: public import PaperVerification.ToricStarSubdivision
-- original header: public import PaperVerification.ToricStrictSupportFaces
-- original header: public import Mathlib.Tactic.NormNum
-- original header: @[expose] public section

/-!
# Strict convex support survives smooth star subdivision

The new coefficient on the exceptional ray is the sum of the old focus
coefficients minus one common sufficiently small positive real parameter.
All supporting linear forms and every strict inequality are constructed.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

def starCoefficientBase {n : ℕ} (a : Lattice n → ℝ) (t : Finset (Lattice n)) :
    Lattice n → ℝ := fun v => if v = ∑ w ∈ t, w then ∑ w ∈ t, a w else a v

def starCoefficientSlope {n : ℕ} (t : Finset (Lattice n)) : Lattice n → ℝ :=
  fun v => if v = ∑ w ∈ t, w then -1 else 0

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem starCandidates_subset_rays (t : Finset (Lattice n)) :
    ∀ s ∈ «Σ».starCandidates t, s ⊆ insert (∑ v ∈ t, v) «Σ».rays := by
  intro s hs
  rcases («Σ».mem_starCandidates t s).mp hs with ⟨hs, hts⟩ |
    ⟨u, hu, v, hv, htu, rfl⟩
  · intro v hv
    exact Finset.mem_insert_of_mem («Σ».ray_mem_of_mem_cone hs hv)
  · intro w hw
    rcases (mem_starRaySet u t v w).mp hw with rfl | ⟨_, hwu⟩
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem («Σ».ray_mem_of_mem_cone hu hwu)

/-- On a cone not containing the focus, the sum ray has strictly positive
old supporting slack. -/
theorem supporting_sum_strict_of_not_subset (a : Lattice n → ℝ)
    {s t : Finset (Lattice n)} (ht : t ∈ «Σ».cones) (hts : ¬ t ⊆ s)
    (ℓ : Ambient n →ₗ[ℝ] ℝ)
    (heq : ∀ v ∈ s, ℓ (embed n v) = a v)
    (hlt : ∀ v ∈ «Σ».rays, v ∉ s → ℓ (embed n v) < a v) :
    ℓ (embed n (∑ v ∈ t, v)) < ∑ v ∈ t, a v := by
  rw [map_sum, map_sum]
  apply Finset.sum_lt_sum
  · intro v hv
    by_cases hvs : v ∈ s
    · exact (heq v hvs).le
    · exact (hlt v («Σ».ray_mem_of_mem_cone ht hv) hvs).le
  · obtain ⟨v, hv, hvs⟩ := Finset.not_subset.mp hts
    exact ⟨v, hv, hlt v («Σ».ray_mem_of_mem_cone ht hv) hvs⟩

/-- Each candidate new cone admits two explicit linear forms whose
supporting slacks are lexicographically positive outside that cone. -/
theorem starCandidate_lexicographic_support
    (a : Lattice n → ℝ) (ha : «Σ».IsStrictSupport a)
    (t : Finset (Lattice n)) (ht : t ∈ «Σ».cones) (hcard : 2 ≤ t.card) :
    ∀ c ∈ «Σ».starCandidates t, ∃ L₀ L₁ : Ambient n →ₗ[ℝ] ℝ,
      (∀ v ∈ c, L₀ (embed n v) = starCoefficientBase a t v ∧
        L₁ (embed n v) = starCoefficientSlope t v) ∧
      (∀ v ∈ insert (∑ w ∈ t, w) «Σ».rays, v ∉ c →
        L₀ (embed n v) < starCoefficientBase a t v ∨
        (L₀ (embed n v) = starCoefficientBase a t v ∧
          L₁ (embed n v) < starCoefficientSlope t v)) := by
  let e := ∑ w ∈ t, w
  have he : e ∉ «Σ».rays := «Σ».sum_rays_not_mem_rays ht hcard
  have hcoeff (v : Lattice n) (hv : v ∈ «Σ».rays) :
      starCoefficientBase a t v = a v ∧ starCoefficientSlope t v = 0 := by
    have hve : v ≠ e := fun h => he (h ▸ hv)
    change v ≠ (∑ w ∈ t, w) at hve
    simp only [starCoefficientBase, starCoefficientSlope, if_neg hve, true_and]
  intro c hc
  rcases («Σ».mem_starCandidates t c).mp hc with ⟨hc, htc⟩ |
    ⟨s, hs, p, hp, hts, rfl⟩
  · obtain ⟨ℓ, heq, hlt⟩ := ha c hc
    refine ⟨ℓ, 0, ?_, ?_⟩
    · intro v hv
      obtain ⟨h₀, h₁⟩ := hcoeff v («Σ».ray_mem_of_mem_cone hc hv)
      exact ⟨(heq v hv).trans h₀.symm, by simp only [LinearMap.zero_apply, h₁]⟩
    · intro v hv hvc
      rcases Finset.mem_insert.mp hv with rfl | hv
      · left
        simpa only [starCoefficientBase, if_pos rfl, ite_true] using
          «Σ».supporting_sum_strict_of_not_subset a ht htc ℓ heq hlt
      · left
        rw [(hcoeff v hv).1]
        exact hlt v hv hvc
  · obtain ⟨ℓ, heq, hlt⟩ := ha s hs
    obtain ⟨b, I, J, hsI, htJ, hJI⟩ := «Σ».adapted_basis_for_subcone hs hts
    have hpJ : p ∈ J.image b := htJ ▸ hp
    obtain ⟨j, hj, hpj⟩ := Finset.mem_image.mp hpJ
    let g : Ambient n →ₗ[ℝ] ℝ := -(integralBasisReal b).coord j
    have hgold (v : Lattice n) (hv : v ∈ s) :
        g (embed n v) = if v = p then -1 else 0 := by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hsI ▸ hv)
      rw [← hpj, ← integralBasisReal_apply b i]
      simp only [g, LinearMap.neg_apply, Module.Basis.coord_apply,
        Module.Basis.repr_self_apply]
      by_cases hij : i = j
      · simp [hij]
      · simp [hij, b.injective.ne hij]
    have heqsum : e = ∑ i ∈ J, b i := by
      change (∑ w ∈ t, w) = _
      rw [htJ, Finset.sum_image]
      exact fun i _ k _ hik => b.injective hik
    have hge : g (embed n e) = -1 := by
      rw [heqsum, map_sum]
      simp only [g, LinearMap.neg_apply, map_sum]
      simp [← integralBasisReal_apply, Module.Basis.coord_apply,
        Module.Basis.repr_self_apply, Finsupp.single_apply, hj]
    have hℓe : ℓ (embed n e) = ∑ v ∈ t, a v := by
      change ℓ (embed n (∑ v ∈ t, v)) = _
      rw [map_sum, map_sum]
      exact Finset.sum_congr rfl (fun v hv => heq v (hts hv))
    refine ⟨ℓ, g, ?_, ?_⟩
    · intro v hv
      rcases (mem_starRaySet s t p v).mp hv with hve | ⟨hvp, hvs⟩
      · subst v
        simpa only [e, starCoefficientBase, starCoefficientSlope, if_pos rfl,
          ite_true] using And.intro hℓe hge
      · obtain ⟨h₀, h₁⟩ := hcoeff v («Σ».ray_mem_of_mem_cone hs hvs)
        refine ⟨(heq v hvs).trans h₀.symm, ?_⟩
        rw [hgold v hvs, if_neg hvp, h₁]
    · intro v hv hvc
      have hve : v ≠ e := by
        intro h
        exact hvc ((mem_starRaySet s t p v).mpr (Or.inl h))
      have hvrays : v ∈ «Σ».rays := (Finset.mem_insert.mp hv).resolve_left hve
      obtain ⟨h₀, h₁⟩ := hcoeff v hvrays
      rw [h₀, h₁]
      by_cases hvs : v ∈ s
      · right
        have hvp : v = p := by
          by_contra hne
          exact hvc ((mem_starRaySet s t p v).mpr (Or.inr ⟨hne, hvs⟩))
        refine ⟨heq v hvs, ?_⟩
        rw [hgold v hvs, if_pos hvp]
        norm_num
      · exact Or.inl (hlt v hvrays hvs)

/-- Strict support survives a genuine smooth star subdivision. The new
exceptional coefficient is exactly `Σ a_v - ε`; every old ray coefficient
is unchanged because the sum ray is proved to be new. -/
theorem strictSupport_starSubdivision_all_small
    (a : Lattice n → ℝ) (ha : «Σ».IsStrictSupport a)
    (t : Finset (Lattice n)) (ht : t ∈ «Σ».cones) (hne : t.Nonempty)
    (hcard : 2 ≤ t.card) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      («Σ».starSubdivision t ht hne).IsStrictSupport
      (fun v => starCoefficientBase a t v + ε * starCoefficientSlope t v) := by
  let C := «Σ».starCandidates t
  let R := insert (∑ v ∈ t, v) «Σ».rays
  have hcharts := «Σ».starCandidate_lexicographic_support a ha t ht hcard
  choose L₀ L₁ hactive hinactive using hcharts
  let K₀ : Finset (Lattice n) → Ambient n →ₗ[ℝ] ℝ :=
    fun s => if hs : s ∈ C then L₀ s hs else 0
  let K₁ : Finset (Lattice n) → Ambient n →ₗ[ℝ] ℝ :=
    fun s => if hs : s ∈ C then L₁ s hs else 0
  have heq : ∀ s ∈ C, ∀ v ∈ s,
      K₀ s (embed n v) = starCoefficientBase a t v ∧
      K₁ s (embed n v) = starCoefficientSlope t v := by
    intro s hs v hv
    simpa only [K₀, K₁, dif_pos hs] using hactive s hs v hv
  have hlex : ∀ s ∈ C, ∀ v ∈ R, v ∉ s →
      K₀ s (embed n v) < starCoefficientBase a t v ∨
      (K₀ s (embed n v) = starCoefficientBase a t v ∧
        K₁ s (embed n v) < starCoefficientSlope t v) := by
    intro s hs v hv hvs
    simpa only [K₀, K₁, dif_pos hs] using hinactive s hs v hv hvs
  obtain ⟨δ, hδ, hsupp⟩ := finite_lexicographic_support_perturbation_all_small
    C R (starCoefficientBase a t) (starCoefficientSlope t) K₀ K₁ heq hlex
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  apply strictSupport_fanOfFiniteSmoothCones C
    («Σ».starCandidates_smooth t) («Σ».starCandidates_intersection t ht)
    («Σ».starCandidates_cover t hne) R («Σ».starCandidates_subset_rays t)
  intro s hs
  exact ⟨K₀ s + ε • K₁ s, hsupp ε hε hεδ s hs⟩

theorem exists_strictSupport_starSubdivision
    (a : Lattice n → ℝ) (ha : «Σ».IsStrictSupport a)
    (t : Finset (Lattice n)) (ht : t ∈ «Σ».cones) (hne : t.Nonempty)
    (hcard : 2 ≤ t.card) :
    ∃ ε : ℝ, 0 < ε ∧ («Σ».starSubdivision t ht hne).IsStrictSupport
      (fun v => starCoefficientBase a t v + ε * starCoefficientSlope t v) := by
  obtain ⟨δ, hδ, hsmall⟩ := «Σ».strictSupport_starSubdivision_all_small a ha t ht hne hcard
  exact ⟨δ, hδ, hsmall δ hδ le_rfl⟩

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricStarStrictSupport
-- END ORIGINAL PaperVerification.ToricStarStrictSupport


-- BEGIN ORIGINAL PaperVerification.ToricStarCombinatorics
section Source_ToricStarCombinatorics

-- original header: module
-- original header: public import PaperVerification.ToricStarSubdivision
-- original header: public import PaperVerification.ToricStarStrictSupport
-- original header: public import Mathlib.Tactic.Tauto
-- original header: @[expose] public section

/-!
# Exact cone combinatorics of the smooth star subdivision

The membership descriptions are derived from the constructed fan. They are
the finite combinatorial basis for the later primitive-relation pushdown.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable (t : Finset (Lattice n)) (ht : t ∈ «Σ».cones) (hne : t.Nonempty)

theorem starSubdivision_rays_subset :
    («Σ».starSubdivision t ht hne).rays ⊆ insert (∑ v ∈ t, v) «Σ».rays := by
  intro v hv
  obtain ⟨s, hs, hvs⟩ := ((«Σ».starSubdivision t ht hne).mem_rays_iff v).mp hv
  obtain ⟨u, hu, hsu⟩ := (mem_finiteConeFamilyClosure («Σ».starCandidates t) s).mp hs
  exact «Σ».starCandidates_subset_rays t u hu (hsu hvs)

/-- An old-ray set avoiding the new sum ray is a new cone exactly when it
was an old cone and did not contain the focus. -/
theorem mem_starSubdivision_without_sum_iff {s : Finset (Lattice n)}
    (he : (∑ v ∈ t, v) ∉ s) :
    s ∈ («Σ».starSubdivision t ht hne).cones ↔ s ∈ «Σ».cones ∧ ¬ t ⊆ s := by
  constructor
  · intro hs
    obtain ⟨u, hu, hsu⟩ := (mem_finiteConeFamilyClosure («Σ».starCandidates t) s).mp hs
    rcases («Σ».mem_starCandidates t u).mp hu with ⟨hu, htu⟩ |
      ⟨u', hu', p, hp, htu', rfl⟩
    · exact ⟨«Σ».downward u hu s hsu, fun hts => htu (hts.trans hsu)⟩
    · have hsub : s ⊆ u'.erase p := by
        intro v hv
        rcases (mem_starRaySet _ _ _ _).mp (hsu hv) with hve | ⟨hvp, hvu⟩
        · exact (he (hve ▸ hv)).elim
        · exact Finset.mem_erase.mpr ⟨hvp, hvu⟩
      refine ⟨«Σ».downward u' hu' s (hsub.trans (Finset.erase_subset p u')), ?_⟩
      intro hts
      exact (Finset.mem_erase.mp (hsub (hts hp))).1 rfl
  · rintro ⟨hs, hts⟩
    exact «Σ».mem_starSubdivision_of_unchanged t ht hne hs hts

/-- A cone containing the exceptional ray is characterized by replacing it
with the full old focus and omitting at least one focus ray. -/
theorem mem_starSubdivision_with_sum_iff (hcard : 2 ≤ t.card)
    {s : Finset (Lattice n)} (he : (∑ v ∈ t, v) ∈ s) :
    s ∈ («Σ».starSubdivision t ht hne).cones ↔
      ∃ p ∈ t, p ∉ s ∧ (s.erase (∑ v ∈ t, v) ∪ t) ∈ «Σ».cones := by
  let e := ∑ v ∈ t, v
  have heold : e ∉ «Σ».rays := «Σ».sum_rays_not_mem_rays ht hcard
  constructor
  · intro hs
    obtain ⟨u, hu, hsu⟩ := (mem_finiteConeFamilyClosure («Σ».starCandidates t) s).mp hs
    rcases («Σ».mem_starCandidates t u).mp hu with ⟨hu, htu⟩ |
      ⟨u', hu', p, hp, htu', rfl⟩
    · exact (heold («Σ».ray_mem_of_mem_cone hu (hsu he))).elim
    · have hpe : p ≠ e := fun h => heold (h ▸ «Σ».ray_mem_of_mem_cone ht hp)
      have hps : p ∉ s := by
        intro hps
        rcases (mem_starRaySet _ _ _ _).mp (hsu hps) with h | ⟨h, _⟩
        · exact hpe h
        · exact h rfl
      refine ⟨p, hp, hps, «Σ».downward u' hu' _ ?_⟩
      apply Finset.union_subset
      · intro v hv
        rcases (mem_starRaySet _ _ _ _).mp (hsu (Finset.mem_of_mem_erase hv)) with
          hve | ⟨_, hvu⟩
        · exact ((Finset.mem_erase.mp hv).1 hve).elim
        · exact hvu
      · exact htu'
  · rintro ⟨p, hp, hps, hparent⟩
    let u := s.erase e ∪ t
    have htu : t ⊆ u := Finset.subset_union_right
    have hnew := «Σ».starRaySet_mem_starSubdivision t ht hne hparent htu hp
    apply («Σ».starSubdivision t ht hne).downward _ hnew s
    intro v hv
    apply (mem_starRaySet _ _ _ _).mpr
    by_cases hve : v = e
    · exact Or.inl hve
    · refine Or.inr ⟨fun hvp => hps (hvp ▸ hv), ?_⟩
      exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hve, hv⟩)

/-- The exceptional ray belongs to the constructed fan. -/
theorem sum_mem_starSubdivision_rays :
    (∑ v ∈ t, v) ∈ («Σ».starSubdivision t ht hne).rays := by
  let p := hne.choose
  have hp : p ∈ t := hne.choose_spec
  apply ((«Σ».starSubdivision t ht hne).mem_rays_iff _).mpr
  exact ⟨starRaySet t t p,
    «Σ».starRaySet_mem_starSubdivision t ht hne ht (Finset.Subset.refl t) hp,
    (mem_starRaySet _ _ _ _).mpr (Or.inl rfl)⟩

/-- Every old ray remains a ray after a nontrivial smooth star subdivision. -/
theorem old_ray_mem_starSubdivision_rays (hcard : 2 ≤ t.card)
    {v : Lattice n} (hv : v ∈ «Σ».rays) :
    v ∈ («Σ».starSubdivision t ht hne).rays := by
  have hnot : ¬ t ⊆ {v} := by
    intro h
    have hle := Finset.card_le_card h
    simp only [Finset.card_singleton] at hle
    omega
  have hsingle := «Σ».mem_starSubdivision_of_unchanged t ht hne
    («Σ».singleton_mem_of_mem_rays hv) hnot
  exact ((«Σ».starSubdivision t ht hne).mem_rays_iff v).mpr
    ⟨{v}, hsingle, Finset.mem_singleton_self v⟩

/-- The ray set is exactly the old ray set with the single genuine sum ray
adjoined. -/
theorem starSubdivision_rays_eq (hcard : 2 ≤ t.card) :
    («Σ».starSubdivision t ht hne).rays = insert (∑ v ∈ t, v) «Σ».rays := by
  apply Finset.Subset.antisymm («Σ».starSubdivision_rays_subset t ht hne)
  intro v hv
  rcases Finset.mem_insert.mp hv with rfl | hv
  · exact «Σ».sum_mem_starSubdivision_rays t ht hne
  · exact «Σ».old_ray_mem_starSubdivision_rays t ht hne hcard hv

/-- The old focus is a primitive collection of the new fan. -/
theorem focus_isPrimitiveCollection_starSubdivision (hcard : 2 ≤ t.card) :
    («Σ».starSubdivision t ht hne).IsPrimitiveCollection t := by
  have het : (∑ v ∈ t, v) ∉ t := by
    intro he
    exact «Σ».sum_rays_not_mem_rays ht hcard («Σ».ray_mem_of_mem_cone ht he)
  have hnot : t ∉ («Σ».starSubdivision t ht hne).cones := by
    intro h
    exact ((«Σ».mem_starSubdivision_without_sum_iff t ht hne het).mp h).2
      (Finset.Subset.refl t)
  refine ⟨?_, hnot, ?_⟩
  · intro v hv
    exact «Σ».old_ray_mem_starSubdivision_rays t ht hne hcard
      («Σ».ray_mem_of_mem_cone ht hv)
  · intro s hst
    have hnot : ¬ t ⊆ s := by
      intro hts
      exact (Finset.ssubset_iff_subset_ne.mp hst).2
        (Finset.Subset.antisymm hst.subset hts)
    exact «Σ».mem_starSubdivision_of_unchanged t ht hne
      («Σ».downward t ht s hst.subset) hnot

/-- The exceptional primitive relation is the actual vector identity
`Σ focus rays = new sum ray`. -/
def exceptionalPrimitiveRelation (hcard : 2 ≤ t.card) :
    («Σ».starSubdivision t ht hne).PrimitiveRelation where
  positive := t
  negative := {∑ v ∈ t, v}
  coefficient := fun _ => 1
  primitive := «Σ».focus_isPrimitiveCollection_starSubdivision t ht hne hcard
  negative_cone := («Σ».starSubdivision t ht hne).singleton_mem_of_mem_rays
    («Σ».sum_mem_starSubdivision_rays t ht hne)
  coefficient_pos := by simp
  equation := by simp

theorem exceptionalPrimitiveRelation_degree (hcard : 2 ≤ t.card)
    (a : Lattice n → ℝ) :
    («Σ».exceptionalPrimitiveRelation t ht hne hcard).degree a =
      (∑ v ∈ t, a v) - a (∑ v ∈ t, v) := by
  simp [PrimitiveRelation.degree, exceptionalPrimitiveRelation]

/-- The exceptional primitive relation satisfies the full contraction
replacement condition, derived from the exact new-cone membership rule. -/
theorem exceptionalPrimitiveRelation_contractible (hcard : 2 ≤ t.card) :
    («Σ».exceptionalPrimitiveRelation t ht hne hcard).IsCombinatoriallyContractible := by
  let e := ∑ v ∈ t, v
  change ∀ ν ∈ («Σ».starSubdivision t ht hne).cones,
    Disjoint ν (t ∪ {e}) → {e} ∪ ν ∈ («Σ».starSubdivision t ht hne).cones →
      ∀ x ∈ t, t.erase x ∪ {e} ∪ ν ∈ («Σ».starSubdivision t ht hne).cones
  intro ν hν hdisj hcone x hx
  have heν : e ∉ ν := by
    intro he
    exact Finset.disjoint_left.mp hdisj he (Finset.mem_union_right _ (Finset.mem_singleton_self e))
  have hxν : x ∉ ν := by
    intro hxn
    exact Finset.disjoint_left.mp hdisj hxn (Finset.mem_union_left _ hx)
  have hxe : x ≠ e := by
    intro h
    have hxold := «Σ».ray_mem_of_mem_cone ht hx
    rw [h] at hxold
    exact «Σ».sum_rays_not_mem_rays ht hcard hxold
  have hecone : e ∈ {e} ∪ ν := Finset.mem_union_left _ (Finset.mem_singleton_self e)
  obtain ⟨p, hp, hpn, hparent⟩ :=
    («Σ».mem_starSubdivision_with_sum_iff t ht hne hcard hecone).mp hcone
  have hparentEq : ({e} ∪ ν).erase e ∪ t = ν ∪ t := by
    ext z
    by_cases hze : z = e
    · subst z
      simp [heν]
    · simp [Finset.mem_erase, hze]
  rw [hparentEq] at hparent
  have hsume : e ∈ t.erase x ∪ {e} ∪ ν :=
    Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self e))
  apply («Σ».mem_starSubdivision_with_sum_iff t ht hne hcard hsume).mpr
  refine ⟨x, hx, ?_, ?_⟩
  · simp [hxν, hxe]
  · have hsets : (t.erase x ∪ {e} ∪ ν).erase e ∪ t = ν ∪ t := by
      ext z
      by_cases hze : z = e
      · subst z
        simp [heν]
      · simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
        tauto
    change (t.erase x ∪ {e} ∪ ν).erase e ∪ t ∈ «Σ».cones
    rw [hsets]
    exact hparent

/-- Any other primitive collection avoiding the exceptional ray is a
primitive collection of the original fan. This is the old-positive part
of the primitive-collection transformation theorem. -/
theorem primitiveCollection_pushdown_without_sum (hcard : 2 ≤ t.card)
    {P : Finset (Lattice n)}
    (hP : («Σ».starSubdivision t ht hne).IsPrimitiveCollection P)
    (heP : (∑ v ∈ t, v) ∉ P) (hPt : P ≠ t) :
    «Σ».IsPrimitiveCollection P := by
  have htnew : t ∉ («Σ».starSubdivision t ht hne).cones :=
    («Σ».focus_isPrimitiveCollection_starSubdivision t ht hne hcard).2.1
  have hPold : P ∉ «Σ».cones := by
    intro hPold
    have htP : t ⊆ P := by
      by_contra hnot
      exact hP.2.1 («Σ».mem_starSubdivision_of_unchanged t ht hne hPold hnot)
    have hproper : t ⊂ P := Finset.ssubset_iff_subset_ne.mpr ⟨htP, Ne.symm hPt⟩
    exact htnew (hP.2.2 t hproper)
  refine ⟨?_, hPold, ?_⟩
  · intro v hv
    have h := «Σ».starSubdivision_rays_subset t ht hne (hP.1 hv)
    rcases Finset.mem_insert.mp h with hve | hvr
    · exact (heP (hve ▸ hv)).elim
    · exact hvr
  · intro s hs
    have hes : (∑ v ∈ t, v) ∉ s := fun h => heP (hs.subset h)
    exact ((«Σ».mem_starSubdivision_without_sum_iff t ht hne hes).mp (hP.2.2 s hs)).1

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricStarCombinatorics
-- END ORIGINAL PaperVerification.ToricStarCombinatorics


-- BEGIN ORIGINAL PaperVerification.ToricOneExceptionalPositive
section Source_ToricOneExceptionalPositive

-- original header: module

-- original header: public import PaperVerification.ToricPrimitiveOverlap
-- original header: public import PaperVerification.ToricStarCombinatorics

-- original header: @[expose] public section

/-!
# The one-positive-exceptional primitive bound

The bound in Lemma 5.1(i) follows from actual primitive-collection
minimality and contraction replacement. No dimension-of-fibers statement
or algebraic-geometric negativity theorem is assumed.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan.PrimitiveRelation

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} (R : «Σ».PrimitiveRelation)

/-- A primitive collection containing the exceptional ray is disjoint from
the old contraction's positive rays and from the old focus rays. -/
theorem primitive_with_exceptional_disjoint_fiber_rays
    (hR : R.IsCombinatoriallyContractible)
    (hne : R.negative.Nonempty) (hcard : 2 ≤ R.negative.card)
    {S : Finset (Lattice n)}
    (hS : («Σ».starSubdivision R.negative R.negative_cone hne).IsPrimitiveCollection S)
    (heS : (∑ v ∈ R.negative, v) ∈ S) :
    Disjoint S R.positive ∧ Disjoint S R.negative := by
  let T := R.negative
  let e := ∑ v ∈ T, v
  let «Σ'» := «Σ».starSubdivision T R.negative_cone hne
  have heold : e ∉ «Σ».rays := «Σ».sum_rays_not_mem_rays R.negative_cone hcard
  have heT : e ∉ T := fun h => heold («Σ».ray_mem_of_mem_cone R.negative_cone h)
  have heP : e ∉ R.positive := fun h => heold (R.primitive.1 h)
  have hST : Disjoint S T := by
    let E := «Σ».exceptionalPrimitiveRelation T R.negative_cone hne hcard
    have hE := «Σ».exceptionalPrimitiveRelation_contractible T R.negative_cone hne hcard
    have hNE : E.negative ⊆ S := Finset.singleton_subset_iff.mpr heS
    have hneq : E.positive ≠ S := by
      intro heq
      change T = S at heq
      exact heT (heq.symm ▸ heS)
    exact (E.positive_disjoint_of_focus_subset_primitive hE hS hNE hneq).symm
  refine ⟨?_, hST⟩
  apply Finset.disjoint_left.mpr
  intro x hxS hxP
  have hxe : x ≠ e := fun he => heP (he ▸ hxP)
  let A := S.erase e
  have hAnew : A ∈ «Σ'».cones := hS.2.2 A (Finset.erase_ssubset heS)
  have hA := («Σ».mem_starSubdivision_without_sum_iff T R.negative_cone hne
    (Finset.notMem_erase e S)).mp hAnew
  have hnotPA : ¬ R.positive ⊆ A := by
    intro h
    exact R.primitive.2.1 («Σ».downward A hA.1 R.positive h)
  obtain ⟨u, huP, huA⟩ := Finset.not_subset.mp hnotPA
  have huT : u ∉ T := fun h => Finset.disjoint_left.mp R.disjoint huP h
  have hxeS : e ∈ S.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxe, heS⟩
  have hproper := hS.2.2 (S.erase x) (Finset.erase_ssubset hxS)
  obtain ⟨p, hpT, hpS, hparent⟩ :=
    («Σ».mem_starSubdivision_with_sum_iff T R.negative_cone hne hcard hxeS).mp hproper
  have hparent' : A.erase x ∪ T ∈ «Σ».cones := by
    change (S.erase x).erase e ∪ T ∈ «Σ».cones at hparent
    simpa only [A, Finset.erase_right_comm] using hparent
  have huC : u ∉ A.erase x ∪ T := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact huA (Finset.mem_of_mem_erase h)
    · exact huT h
  have hfilled := R.fill_cone_with_positive_except hR hparent'
    (Finset.subset_union_right : T ⊆ A.erase x ∪ T) huP huC
  have hAT : A ∪ T ∈ «Σ».cones := by
    apply «Σ».downward _ hfilled _
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · by_cases hzx : z = x
      · subst z
        have hxu : x ≠ u := by
          intro h
          exact huA (h ▸ Finset.mem_erase.mpr ⟨hxe, hxS⟩)
        exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hxu, hxP⟩)
      · exact Finset.mem_union_right _ (Finset.mem_union_left _
          (Finset.mem_erase.mpr ⟨hzx, hz⟩))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ hz)
  obtain ⟨p, hpT, hpA⟩ := Finset.not_subset.mp hA.2
  have hpS : p ∉ S := by
    intro hpS
    have hpe : p ≠ e := fun h => heT (h ▸ hpT)
    exact hpA (Finset.mem_erase.mpr ⟨hpe, hpS⟩)
  exact hS.2.1 ((«Σ».mem_starSubdivision_with_sum_iff T R.negative_cone hne hcard heS).mpr
    ⟨p, hpT, hpS, hAT⟩)

/-- The exact additive form of Lemma 5.1(i) after a nontrivial star:
`r + q + s ≤ n + 2`, equivalently `s ≤ b + 2` when `n=r+q+b`. -/
theorem primitive_with_exceptional_card_bound
    (hR : R.IsCombinatoriallyContractible)
    (hne : R.negative.Nonempty) (hcard : 2 ≤ R.negative.card)
    {S : Finset (Lattice n)}
    (hS : («Σ».starSubdivision R.negative R.negative_cone hne).IsPrimitiveCollection S)
    (heS : (∑ v ∈ R.negative, v) ∈ S) :
    R.fiberDimension + R.negative.card + S.card ≤ n + 2 := by
  let e := ∑ v ∈ R.negative, v
  let A := S.erase e
  have hsize :=
    ((«Σ».starSubdivision R.negative R.negative_cone hne).primitiveCollection_card_bounds hS).1
  have hAcard : A.card = S.card - 1 := Finset.card_erase_of_mem heS
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hxA⟩ := hAne
  have hxS := Finset.mem_of_mem_erase hxA
  have hxe := (Finset.mem_erase.mp hxA).1
  have he' : e ∈ S.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxe, heS⟩
  obtain ⟨p, hp, hpn, hparent⟩ := («Σ».mem_starSubdivision_with_sum_iff R.negative
    R.negative_cone hne hcard he').mp (hS.2.2 _ (Finset.erase_ssubset hxS))
  have hparent' : A.erase x ∪ R.negative ∈ «Σ».cones := by
    change (S.erase x).erase e ∪ R.negative ∈ «Σ».cones at hparent
    simpa only [A, Finset.erase_right_comm] using hparent
  have hdisj := R.primitive_with_exceptional_disjoint_fiber_rays hR hne hcard hS heS
  obtain ⟨u, hu⟩ := «Σ».primitiveCollection_nonempty R.primitive
  have huC : u ∉ A.erase x ∪ R.negative := by
    intro hh
    rcases Finset.mem_union.mp hh with hh | hh
    · exact Finset.disjoint_left.mp hdisj.1
        (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hh)) hu
    · exact Finset.disjoint_left.mp R.disjoint hu hh
  have hfilled := R.fill_cone_with_positive_except hR hparent'
    Finset.subset_union_right hu huC
  have hdim := «Σ».card_cone_le hfilled
  have hPN : Disjoint (R.positive.erase u) R.negative :=
    R.disjoint.mono_left (Finset.erase_subset u R.positive)
  have hPA : Disjoint (R.positive.erase u) (A.erase x) := by
    apply Finset.disjoint_left.mpr
    intro v hvP hvA
    exact Finset.disjoint_left.mp hdisj.1
      (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hvA)) (Finset.mem_of_mem_erase hvP)
  have hAN : Disjoint (A.erase x) R.negative :=
    hdisj.2.mono_left ((Finset.erase_subset x A).trans (Finset.erase_subset e S))
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_right.mpr ⟨hPA, hPN⟩),
    Finset.card_union_of_disjoint hAN, Finset.card_erase_of_mem hu,
    Finset.card_erase_of_mem hxA, hAcard] at hdim
  unfold fiberDimension
  omega

/-- The codimension-one case uses the original divisor ray and makes no
subdivision. Its bound is the same additive formula with `q=1`. -/
theorem primitive_with_divisor_focus_card_bound
    (hR : R.IsCombinatoriallyContractible) (e : Lattice n)
    (hfocus : R.negative = {e})
    {S : Finset (Lattice n)} (hS : «Σ».IsPrimitiveCollection S) (heS : e ∈ S) :
    R.fiberDimension + 1 + S.card ≤ n + 2 := by
  have heN : e ∈ R.negative := hfocus.symm ▸ Finset.mem_singleton_self e
  have hneq : R.positive ≠ S := by
    intro he
    exact Finset.disjoint_left.mp R.disjoint (he.symm ▸ heS) heN
  have hdisj := R.positive_disjoint_of_focus_subset_primitive hR hS
    (by simpa only [hfocus, Finset.singleton_subset_iff] using heS) hneq
  let A := S.erase e
  have hsize := («Σ».primitiveCollection_card_bounds hS).1
  have hAcard : A.card = S.card - 1 := Finset.card_erase_of_mem heS
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < A.card by omega)
  have hxS := Finset.mem_of_mem_erase hx
  have hC := hS.2.2 (S.erase x) (Finset.erase_ssubset hxS)
  have hNC : R.negative ⊆ S.erase x := by
    rw [hfocus, Finset.singleton_subset_iff]
    exact Finset.mem_erase.mpr ⟨Ne.symm (Finset.mem_erase.mp hx).1, heS⟩
  obtain ⟨u, hu⟩ := «Σ».primitiveCollection_nonempty R.primitive
  have huC : u ∉ S.erase x := fun hh =>
    Finset.disjoint_left.mp hdisj hu (Finset.mem_of_mem_erase hh)
  have hfill := R.fill_cone_with_positive_except hR hC hNC hu huC
  have hdim := «Σ».card_cone_le hfill
  have hPC : Disjoint (R.positive.erase u) (S.erase x) :=
    hdisj.mono (Finset.erase_subset u R.positive) (Finset.erase_subset x S)
  rw [Finset.card_union_of_disjoint hPC, Finset.card_erase_of_mem hu,
    Finset.card_erase_of_mem hxS] at hdim
  unfold fiberDimension
  omega

end SmoothCompleteFan.PrimitiveRelation

end PaperVerification.ToricGeometry
end
end Source_ToricOneExceptionalPositive
-- END ORIGINAL PaperVerification.ToricOneExceptionalPositive


-- BEGIN ORIGINAL PaperVerification.ToricFiberWalls
section Source_ToricFiberWalls

-- original header: module

-- original header: public import PaperVerification.ToricOneExceptionalPositive
-- original header: public import PaperVerification.ToricContractibleWalls

-- original header: @[expose] public section

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
end
end Source_ToricFiberWalls
-- END ORIGINAL PaperVerification.ToricFiberWalls


-- BEGIN ORIGINAL PaperVerification.ToricRelationTransport
section Source_ToricRelationTransport

-- original header: module

-- original header: public import PaperVerification.ToricPrimitiveRelations

-- original header: @[expose] public section

/-!
# Transport of actual primitive relations across equal focus stars

Only the cone-membership proofs change. The positive/negative ray sets,
integer coefficients and lattice equation are literally retained.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan.PrimitiveRelation

variable {n : ℕ} {«Σ» Γ : SmoothCompleteFan n} (R : «Σ».PrimitiveRelation)

theorem degree_congr_on_rays (a b : Lattice n → ℝ)
    (hP : ∀ v ∈ R.positive, a v = b v)
    (hN : ∀ v ∈ R.negative, a v = b v) : R.degree a = R.degree b := by
  unfold degree
  congr 1
  · exact Finset.sum_congr rfl hP
  · exact Finset.sum_congr rfl (fun v hv => congrArg ((R.coefficient v : ℝ) * ·) (hN v hv))

theorem degree_change_one_negative (a b : Lattice n → ℝ)
    (e : Lattice n) (he : e ∈ R.negative) (t : ℝ)
    (hP : ∀ v ∈ R.positive, a v = b v)
    (hN : ∀ v ∈ R.negative.erase e, a v = b v)
    (heq : a e = b e - t) :
    R.degree a = R.degree b + (R.coefficient e : ℝ) * t := by
  have hpos : (∑ v ∈ R.positive, a v) = ∑ v ∈ R.positive, b v :=
    Finset.sum_congr rfl hP
  have hneg : (∑ v ∈ R.negative.erase e, (R.coefficient v : ℝ) * a v) =
      ∑ v ∈ R.negative.erase e, (R.coefficient v : ℝ) * b v :=
    Finset.sum_congr rfl (fun v hv => congrArg ((R.coefficient v : ℝ) * ·) (hN v hv))
  unfold degree
  rw [hpos, ← Finset.add_sum_erase R.negative
    (fun v => (R.coefficient v : ℝ) * a v) he,
    ← Finset.add_sum_erase R.negative (fun v => (R.coefficient v : ℝ) * b v) he,
    hneg, heq]
  ring

def copyToFan (Γ : SmoothCompleteFan n)
    (hP : Γ.IsPrimitiveCollection R.positive) (hN : R.negative ∈ Γ.cones) :
    Γ.PrimitiveRelation :=
  ⟨R.positive, R.negative, R.coefficient, hP, hN, R.coefficient_pos, R.equation⟩

@[simp] theorem copyToFan_degree (Γ : SmoothCompleteFan n)
    (hP : Γ.IsPrimitiveCollection R.positive) (hN : R.negative ∈ Γ.cones)
    (a : Lattice n → ℝ) :
    (R.copyToFan Γ hP hN).degree a = R.degree a := rfl

theorem copyToFan_contractible
    (Γ : SmoothCompleteFan n)
    (hP : Γ.IsPrimitiveCollection R.positive) (hN : R.negative ∈ Γ.cones)
    (hstars : ∀ s : Finset (Lattice n), R.negative ⊆ s →
      (s ∈ «Σ».cones ↔ s ∈ Γ.cones))
    (hR : R.IsCombinatoriallyContractible) :
    (R.copyToFan Γ hP hN).IsCombinatoriallyContractible := by
  intro ν hν hdisj hNν x hx
  have hNνold := (hstars (R.negative ∪ ν) Finset.subset_union_left).mpr hNν
  have hνold := «Σ».downward _ hNνold ν Finset.subset_union_right
  have hreplace := hR ν hνold hdisj hNνold x hx
  exact (hstars (R.positive.erase x ∪ R.negative ∪ ν)
    (Finset.subset_union_right.trans Finset.subset_union_left)).mp hreplace

end SmoothCompleteFan.PrimitiveRelation

end PaperVerification.ToricGeometry
end
end Source_ToricRelationTransport
-- END ORIGINAL PaperVerification.ToricRelationTransport


-- BEGIN ORIGINAL PaperVerification.ToricDisjointStarIntersections
section Source_ToricDisjointStarIntersections

-- original header: module

-- original header: public import PaperVerification.ToricStarFanFaces

-- original header: @[expose] public section

/-!
# Intersections of star charts over disjoint centers

Each exceptional sum ray is absent from the other old parent cone. Hence
both new charts restrict to ordinary faces of the old common face, and their
intersection is exactly their common-ray cone.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem star_cones_inter_disjoint_foci
    {U V T A : Finset (Lattice n)}
    (hU : U ∈ «Σ».cones) (hV : V ∈ «Σ».cones)
    (hT : T ∈ «Σ».cones) (hA : A ∈ «Σ».cones)
    (hTU : T ⊆ U) (hAV : A ⊆ V)
    (hTV : ¬ T ⊆ V) (hAU : ¬ A ⊆ U) (p q : Lattice n) :
    latticeRayCone (starRaySet U T p) ⊓ latticeRayCone (starRaySet V A q) =
      latticeRayCone (starRaySet U T p ∩ starRaySet V A q) := by
  let C := starRaySet U T p
  let D := starRaySet V A q
  have hC := latticeRayCone_starRaySet_le hTU p
  have hD := latticeRayCone_starRaySet_le hAV q
  have heD : (∑ v ∈ T, v) ∉ D := by
    intro he
    have hh := hD (latticeRayCone_generator D he)
    exact hTV ((«Σ».sum_rays_mem_cone_iff hT hV).mp hh)
  have heC : (∑ v ∈ A, v) ∉ C := by
    intro he
    have hh := hC (latticeRayCone_generator C he)
    exact hAU ((«Σ».sum_rays_mem_cone_iff hA hU).mp hh)
  have hCV : C ∩ V ∈ «Σ».cones := «Σ».downward V hV _ Finset.inter_subset_right
  have hDU : D ∩ U ∈ «Σ».cones := «Σ».downward U hU _ Finset.inter_subset_right
  have hmeet : latticeRayCone C ⊓ latticeRayCone D =
      (latticeRayCone C ⊓ latticeRayCone V) ⊓
        (latticeRayCone D ⊓ latticeRayCone U) := by
    ext x
    exact ⟨fun h => ⟨⟨h.1, hD h.2⟩, ⟨h.2, hC h.1⟩⟩,
      fun h => ⟨h.1.1, h.2.1⟩⟩
  rw [hmeet, «Σ».star_cone_inter_unchanged hU hT hV hTU hTV p,
    «Σ».star_cone_inter_unchanged hV hA hU hAV hAU q,
    «Σ».intersection (C ∩ V) hCV (D ∩ U) hDU]
  congr 1
  ext z
  constructor
  · intro hz
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hz).1).1,
        (Finset.mem_inter.mp (Finset.mem_inter.mp hz).2).1⟩
  · intro hz
    obtain ⟨hzC, hzD⟩ := Finset.mem_inter.mp hz
    have hzU : z ∈ U := by
      rcases (mem_starRaySet U T p z).mp hzC with hze | ⟨_, hzU⟩
      · exact (heD (hze ▸ hzD)).elim
      · exact hzU
    have hzV : z ∈ V := by
      rcases (mem_starRaySet V A q z).mp hzD with hze | ⟨_, hzV⟩
      · exact (heC (hze ▸ hzC)).elim
      · exact hzV
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_inter.mpr ⟨hzC, hzV⟩, Finset.mem_inter.mpr ⟨hzD, hzU⟩⟩

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricDisjointStarIntersections
-- END ORIGINAL PaperVerification.ToricDisjointStarIntersections


