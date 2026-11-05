module

public import PaperVerification.ToricBundleFanEdgeBounds
public import PaperVerification.ToricBundleFanReconstruction
public import PaperVerification.ToricContractibleEdgeDegrees


@[expose] public section
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
