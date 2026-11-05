module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Elab.Tactic.Omega
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Order.Field
public import paper_verification.toric001
public import paper_verification.toric002
public import paper_verification.toric017
public import paper_verification.toric018

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.ToricMatchedCenters
section Source_ToricMatchedCenters

-- original header: module
-- original header: public import PaperVerification.ToricNormalFan
-- original header: @[expose] public section
/-!
# Matched unit boxes for actual smooth lattice polytopes

This is the geometric center construction in Lemma 4.2, obtained from the literal
smoothness, edge-length, and common-normal-fan assumptions. Every interior lattice
point is proved to lie in the convex hull of the matched center sums. The lattice
point selection from those boxes is supplied by the independent basis-box covering
argument.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators

namespace LatticePolytope

/-- Full matched-center geometry for the actual polytopes, with no additional
normal-fan or shifted-polytope hypothesis. The indexing set consists of the
actual vertices of `P`; all integral edge bases are allowed to differ. -/
theorem matched_unit_box_centers {n : ℕ} (P Q : LatticePolytope n)
    (hP : P.Smooth) (hQ : Q.Smooth) (hfan : P.SameNormalFan Q)
    (hlP : P.EdgesAtLeast n) (hlQ : Q.EdgesAtLeast n) :
    ∃ (b : P.carrier.extremePoints ℝ → Module.Basis (Fin n) ℤ (Lattice n))
      (a c : P.carrier.extremePoints ℝ → Ambient n),
      (∀ j (t : Fin n → ℝ), (∀ i, |t i| ≤ 1 / 2) →
        a j + ∑ i, t i • integralBasisReal (b j) i ∈ P.carrier) ∧
      (∀ j (t : Fin n → ℝ), (∀ i, |t i| ≤ 1 / 2) →
        c j + ∑ i, t i • integralBasisReal (b j) i ∈ Q.carrier) ∧
      ∀ m : Lattice n, embed n m ∈ interior (P.minkowskiSum Q) →
        embed n m ∈ convexHull ℝ (Set.range fun j => a j + c j) := by
  classical
  let J := P.carrier.extremePoints ℝ
  letI : Fintype J := P.finite_vertices.fintype
  have hdata (j : J) := P.sameNormalFan_matched_bases Q hP hQ hfan j j.property
  choose w vZ wZ b p q hw hvZ hwZ hcones hp hq hPcone hQcone using hdata
  let u : J × Fin n → Ambient n →ₗ[ℝ] ℝ :=
    fun i => (integralBasisReal (b i.1)).coord i.2
  let ap : J × Fin n → ℤ := fun i => (b i.1).repr (vZ i.1) i.2
  let aq : J × Fin n → ℤ := fun i => (b i.1).repr (wZ i.1) i.2
  let active : J → Fin n → J × Fin n := fun j i => (j, i)
  let a : J → Ambient n := fun j => cornerCenter (j : Ambient n) (integralBasisReal (b j))
  let c : J → Ambient n := fun j => cornerCenter (w j) (integralBasisReal (b j))
  have hdual (j : J) (i : Fin n) (x : Ambient n) :
      u (active j i) x = (integralBasisReal (b j)).repr x i := rfl
  have hactiveP (j : J) (i : Fin n) : u (active j i) j = (ap (active j i) : ℝ) := by
    change (integralBasisReal (b j)).repr (j : Ambient n) i = _
    rw [← hvZ j, integralBasisReal_repr]
  have hactiveQ (j : J) (i : Fin n) : u (active j i) (w j) = (aq (active j i) : ℝ) := by
    change (integralBasisReal (b j)).repr (w j) i = _
    rw [← hwZ j, integralBasisReal_repr]
  have hsupportP (x : Ambient n) (hx : x ∈ P.carrier) :
      x ∈ normalHalfspaces u (fun i => (ap i : ℝ)) := by
    rintro ⟨j, i⟩
    have h := hPcone j x hx i
    rw [map_sub, Finsupp.sub_apply] at h
    change (ap (j, i) : ℝ) ≤ (integralBasisReal (b j)).repr x i
    rw [← hactiveP j i]
    exact sub_nonneg.mp h
  have hsupportQ (x : Ambient n) (hx : x ∈ Q.carrier) :
      x ∈ normalHalfspaces u (fun i => (aq i : ℝ)) := by
    rintro ⟨j, i⟩
    have h := hQcone j x hx i
    rw [map_sub, Finsupp.sub_apply] at h
    change (aq (j, i) : ℝ) ≤ (integralBasisReal (b j)).repr x i
    rw [← hactiveQ j i]
    exact sub_nonneg.mp h
  have hunitP (j : J) (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) :
      (j : Ambient n) + ∑ i, t i • integralBasisReal (b j) i ∈ P.carrier := by
    have hv : embed n (vZ j) ∈ P.carrier := by rw [hvZ]; exact j.property.1
    have h := P.integral_edges_unit_corner_box hlP (vZ j) hv (b j) (p j)
      (fun i => by simpa only [hvZ] using (hp j i).2) t ht
    simpa only [hvZ] using h
  have hunitQ (j : J) (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) :
      w j + ∑ i, t i • integralBasisReal (b j) i ∈ Q.carrier := by
    have hv : embed n (wZ j) ∈ Q.carrier := by rw [hwZ]; exact (hw j).1
    have h := Q.integral_edges_unit_corner_box hlQ (wZ j) hv (b j) (q j)
      (fun i => by simpa only [hwZ] using (hq j i).2) t ht
    simpa only [hwZ] using h
  have hu (i : J × Fin n) : u i ≠ 0 := by
    intro hz
    have h := congrArg (fun f : Ambient n →ₗ[ℝ] ℝ => f (integralBasisReal (b i.1) i.2)) hz
    simpa [u, Module.Basis.coord_apply] using h
  have hint (i : J × Fin n) (j : J) (k : Fin n) :
      ∃ z : ℤ, (z : ℝ) = u i (integralBasisReal (b j) k) := by
    refine ⟨(b i.1).repr (b j k) i.2, ?_⟩
    simp [u, Module.Basis.coord_apply]
  have hcomplete (f : Ambient n →ₗ[ℝ] ℝ) :
      ∃ j : J, ∀ i, 0 ≤ f (integralBasisReal (b j) i) :=
    P.smooth_basis_cones_complete b vZ p hvZ hp f
  have hac (j : J) : a j ∈ normalHalfspaces u (fun i => (ap i : ℝ) + 1 / 2) :=
    integral_cornerCenter_feasible u (fun i => (ap i : ℝ)) j
      (integralBasisReal (b j)) hu (fun i k => hint i j k)
      (fun t ht => hsupportP _ (hunitP j t ht))
  have hcc (j : J) : c j ∈ normalHalfspaces u (fun i => (aq i : ℝ) + 1 / 2) :=
    integral_cornerCenter_feasible u (fun i => (aq i : ℝ)) (w j)
      (integralBasisReal (b j)) hu (fun i k => hint i j k)
      (fun t ht => hsupportQ _ (hunitQ j t ht))
  have hacactive (j : J) (i : Fin n) :
      u (active j i) (a j) = (ap (active j i) : ℝ) + 1 / 2 := by
    change u (active j i) (cornerCenter j (integralBasisReal (b j))) = _
    rw [cornerCenter_dual_coordinate _ _ _ i (hdual j i), hactiveP]
  have hccactive (j : J) (i : Fin n) :
      u (active j i) (c j) = (aq (active j i) : ℝ) + 1 / 2 := by
    change u (active j i) (cornerCenter (w j) (integralBasisReal (b j))) = _
    rw [cornerCenter_dual_coordinate _ _ _ i (hdual j i), hactiveQ]
  have hcenters := matched_centers_convexHull u
    (fun i => (ap i : ℝ) + 1 / 2) (fun i => (aq i : ℝ) + 1 / 2)
    (fun j => integralBasisReal (b j)) active a c hdual hcomplete hacactive hccactive hac hcc
  refine ⟨b, a, c, ?_, ?_, ?_⟩
  · intro j t ht
    exact cornerCenter_box_mem P.carrier j (integralBasisReal (b j)) (hunitP j) t ht
  · intro j t ht
    exact cornerCenter_box_mem Q.carrier (w j) (integralBasisReal (b j)) (hunitQ j) t ht
  · intro m hm
    have hsumsubset : P.minkowskiSum Q ⊆
        normalHalfspaces u (fun i => ((ap i + aq i : ℤ) : ℝ)) := by
      rintro _ ⟨x, hx, y, hy, rfl⟩ i
      have hp' := hsupportP x hx i
      have hq' := hsupportQ y hy i
      simpa only [map_add, Int.cast_add] using add_le_add hp' hq'
    have hmint := interior_mono hsumsubset hm
    have huinteger (i : J × Fin n) (z : Lattice n) :
        ∃ k : ℤ, u i (embed n z) = k :=
      ⟨(b i.1).repr z i.2, integralBasisReal_repr (b i.1) z i.2⟩
    have hslack := integral_support_of_interior u (fun i => ap i + aq i)
      huinteger hu m hmint
    rw [← hcenters]
    intro i
    have h := hslack i
    push_cast at h
    linarith

end LatticePolytope

end PaperVerification.ToricGeometry
end
end Source_ToricMatchedCenters
-- END ORIGINAL PaperVerification.ToricMatchedCenters


-- BEGIN ORIGINAL PaperVerification.ToricInteriorDecomposition
section Source_ToricInteriorDecomposition

-- original header: module
-- original header: public import PaperVerification.ToricMatchedCenters
-- original header: public import PaperVerification.ToricBasisBoxFamily
-- original header: @[expose] public section
/-!
# Interior lattice targets in a sum of smooth long-edge polytopes

This composes the actual normal-fan and shifted-center construction with the
finite-family lattice covering theorem. The resulting statement has only the
paper's geometric hypotheses and concerns actual integer-coordinate summands.
Boundary targets still require the separate face reduction in Lemma 4.2.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators
open PaperVerification.Toric

theorem mem_standardIntegerLattice_iff {n : ℕ} (x : Ambient n) :
    x ∈ standardIntegerLattice n ↔ ∃ z : Lattice n, embed n z = x := by
  constructor
  · intro hx
    obtain ⟨z, hz⟩ := (standardLatticeEquiv n).surjective ⟨x, hx⟩
    refine ⟨z, ?_⟩
    have he := congrArg (fun y : standardIntegerLattice n => (y : Ambient n)) hz
    simpa only [standardLatticeEquiv_coe] using he
  · rintro ⟨z, rfl⟩
    rw [← standardLatticeEquiv_coe z]
    exact (standardLatticeEquiv n z).property

namespace LatticePolytope

/-- The interior-target part of Lemma 4.2, with the smoothness, edge lengths,
same normal fan, and lattice summands interpreted literally. -/
theorem interior_lattice_decomposition {n : ℕ} (P Q : LatticePolytope n)
    (hP : P.Smooth) (hQ : Q.Smooth) (hfan : P.SameNormalFan Q)
    (hlP : P.EdgesAtLeast n) (hlQ : Q.EdgesAtLeast n)
    (m : Lattice n) (hm : embed n m ∈ interior (P.minkowskiSum Q)) :
    ∃ x y : Lattice n, embed n x ∈ P.carrier ∧ embed n y ∈ Q.carrier ∧ x + y = m := by
  classical
  let J := P.carrier.extremePoints ℝ
  letI : Fintype J := P.finite_vertices.fintype
  obtain ⟨b, a, c, hboxP, hboxQ, hcenters⟩ := P.matched_unit_box_centers Q hP hQ hfan hlP hlQ
  obtain ⟨p, hp, hpsum, hpm⟩ :=
    exists_probability_of_mem_convexHull_range (fun j : J => a j + c j) (hcenters m hm)
  let L := standardIntegerLattice n
  letI : DiscreteTopology L := standardIntegerLattice_discreteTopology n
  letI : DiscreteTopology L.toAddSubgroup := inferInstanceAs (DiscreteTopology L)
  have hclosed : IsClosed (L.toAddSubgroup : Set (Ambient n)) :=
    AddSubgroup.isClosed_of_discreteTopology
  have hbL (j : J) (i : Fin n) : integralBasisReal (b j) i ∈ L.toAddSubgroup := by
    rw [integralBasisReal_apply]
    exact (mem_standardIntegerLattice_iff _).mpr ⟨b j i, rfl⟩
  have hmL : embed n m ∈ L.toAddSubgroup :=
    (mem_standardIntegerLattice_iff _).mpr ⟨m, rfl⟩
  obtain ⟨x, hxP, y, hyQ, hxL, hyL, hxy⟩ :=
    finite_basis_boxes_lattice_decomposition_pi (fun j : J => integralBasisReal (b j))
      L.toAddSubgroup hclosed hbL P.carrier Q.carrier
      (convex_convexHull ℝ _) (convex_convexHull ℝ _) p hp hpsum a c
      hboxP hboxQ (embed n m) hmL hpm.symm
  obtain ⟨xZ, hxZ⟩ := (mem_standardIntegerLattice_iff x).mp hxL
  obtain ⟨yZ, hyZ⟩ := (mem_standardIntegerLattice_iff y).mp hyL
  refine ⟨xZ, yZ, ?_, ?_, ?_⟩
  · simpa only [hxZ] using hxP
  · simpa only [hyZ] using hyQ
  · apply embed_injective n
    simpa only [map_add, hxZ, hyZ] using hxy

end LatticePolytope

end PaperVerification.ToricGeometry
end
end Source_ToricInteriorDecomposition
-- END ORIGINAL PaperVerification.ToricInteriorDecomposition


-- BEGIN ORIGINAL PaperVerification.ToricDilations
section Source_ToricDilations

-- original header: module
-- original header: public import PaperVerification.ToricIntegralAffine
-- original header: public import PaperVerification.ToricInteriorDecomposition
-- original header: public import Mathlib.Topology.Algebra.ConstMulAction
-- original header: @[expose] public section
/-!
# Positive integral dilations of the literal smooth lattice polytope

Positive dilation preserves smoothness and the actual normal fan, multiplies
lattice edge lengths, and identifies the needed Minkowski sum with the next
dilation. These facts allow induction in the full integer-decomposition degree.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped Pointwise BigOperators

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

theorem dilatedGenerators_image (k : ℕ) :
    (embed n) '' ((P.generators.image (fun z => (k : ℤ) • z)) : Set (Lattice n)) =
      (k : ℝ) • ((embed n) '' (P.generators : Set (Lattice n))) := by
  classical
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨embed n w, ⟨w, hw, rfl⟩, by simp only [embed_int_smul, Int.cast_natCast]⟩
  · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨(k : ℤ) • w, Finset.mem_image.mpr ⟨w, hw, rfl⟩,
      by simp only [embed_int_smul, Int.cast_natCast]⟩

/-- The ordinary dilation by a strictly positive natural number. -/
def dilate (k : ℕ) (hk : 0 < k) : LatticePolytope n where
  generators := P.generators.image (fun z => (k : ℤ) • z)
  nonempty := P.nonempty.image _
  fullDimensional := by
    rw [P.dilatedGenerators_image, convexHull_smul]
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
    let e := LinearEquiv.smulOfNeZero ℝ (Ambient n) (k : ℝ) hkR
    change affineSpan ℝ (e.toLinearMap.toAffineMap '' P.carrier) = ⊤
    exact e.toLinearMap.toAffineMap.span_eq_top_of_surjective e.surjective P.fullDimensional

@[simp] theorem carrier_dilate (k : ℕ) (hk : 0 < k) :
    (P.dilate k hk).carrier = (k : ℝ) • P.carrier := by
  change convexHull ℝ ((embed n) ''
    ((P.generators.image (fun z => (k : ℤ) • z)) : Set (Lattice n))) = _
  rw [P.dilatedGenerators_image, convexHull_smul]
  rfl

/-- Actual edges are carried bijectively to actual edges by positive dilation. -/
theorem dilate_isEdge_iff (k : ℕ) (hk : 0 < k) (v w : Ambient n) :
    (P.dilate k hk).IsEdge ((k : ℝ) • v) ((k : ℝ) • w) ↔ P.IsEdge v w := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  let e := LinearEquiv.smulOfNeZero ℝ (Ambient n) (k : ℝ) hkR
  rw [IsEdge, IsEdge, P.carrier_dilate]
  change (e v ≠ e w ∧ IsExtreme ℝ (e.toLinearMap.toAffineMap '' P.carrier)
    (segment ℝ (e.toLinearMap.toAffineMap v) (e.toLinearMap.toAffineMap w))) ↔ _
  rw [← image_segment ℝ e.toLinearMap.toAffineMap,
    affine_isExtreme_image_iff e.toLinearMap.toAffineMap e.injective]
  constructor
  · rintro ⟨hne, hface⟩
    exact ⟨fun he => hne (congrArg e he), hface⟩
  · rintro ⟨hne, hface⟩
    exact ⟨fun he => hne (e.injective he), hface⟩

@[simp] theorem dilated_endpoint (k : ℕ) (v : Lattice n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) (l : ℕ) :
    embed n ((k : ℤ) • v + ((k * l : ℕ) : ℤ) • b i) =
      (k : ℝ) • embed n (v + (l : ℤ) • b i) := by
  simp only [map_add, embed_int_smul, Int.cast_natCast, Nat.cast_mul,
    Int.cast_mul, smul_add, smul_smul]

/-- Positive integral dilation keeps exactly the same primitive edge bases. -/
theorem smooth_dilate (hP : P.Smooth) (k : ℕ) (hk : 0 < k) :
    (P.dilate k hk).Smooth := by
  intro v hv
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  let e := LinearEquiv.smulOfNeZero ℝ (Ambient n) (k : ℝ) hkR
  have hvertices : (P.dilate k hk).carrier.extremePoints ℝ =
      e '' P.carrier.extremePoints ℝ := by
    rw [P.carrier_dilate]
    exact (image_extremePoints e P.carrier).symm
  rw [hvertices] at hv
  obtain ⟨v, hv, rfl⟩ := hv
  obtain ⟨vZ, b, l, hvZ, hedges, hall⟩ := hP v hv
  refine ⟨(k : ℤ) • vZ, b, fun i => k * l i, ?_, ?_, ?_⟩
  · simp only [embed_int_smul, Int.cast_natCast, hvZ]
    rfl
  · intro i
    refine ⟨Nat.mul_pos hk (hedges i).1, ?_⟩
    rw [dilated_endpoint]
    exact (P.dilate_isEdge_iff k hk _ _).mpr (hedges i).2
  · intro w hw
    obtain ⟨w, rfl⟩ := e.surjective w
    have hw' : P.IsEdge v w := (P.dilate_isEdge_iff k hk v w).mp hw
    obtain ⟨i, hi⟩ := hall w hw'
    refine ⟨i, ?_⟩
    rw [dilated_endpoint, hi]
    rfl

/-- Coordinate gcd, hence lattice edge length, scales by the same positive integer. -/
theorem latticeLength_smul (k : ℕ) (v w : Lattice n) :
    latticeLength ((k : ℤ) • v) ((k : ℤ) • w) = k * latticeLength v w := by
  simp only [latticeLength, Pi.smul_apply, smul_eq_mul, ← mul_sub,
    Int.natAbs_mul, Int.natAbs_natCast]
  rw [Finset.gcd_mul_left]
  simp

/-- Any fixed lower bound on actual edge lengths is preserved by positive integral dilation. -/
theorem edgesAtLeast_dilate {bound : ℕ} (hP : P.EdgesAtLeast bound)
    (k : ℕ) (hk : 0 < k) : (P.dilate k hk).EdgesAtLeast bound := by
  intro v w hvw
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  let e := LinearEquiv.smulOfNeZero ℝ (Ambient n) (k : ℝ) hkR
  obtain ⟨v, rfl⟩ := e.surjective v
  obtain ⟨w, rfl⟩ := e.surjective w
  have hvw' := (P.dilate_isEdge_iff k hk v w).mp hvw
  obtain ⟨vZ, wZ, hvZ, hwZ, hlen⟩ := hP v w hvw'
  refine ⟨(k : ℤ) • vZ, (k : ℤ) • wZ, ?_, ?_, ?_⟩
  · simp only [embed_int_smul, Int.cast_natCast, hvZ]
    rfl
  · simp only [embed_int_smul, Int.cast_natCast, hwZ]
    rfl
  · rw [latticeLength_smul]
    calc
      bound ≤ latticeLength vZ wZ := hlen
      _ = 1 * latticeLength vZ wZ := by simp
      _ ≤ k * latticeLength vZ wZ :=
        Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr hk)

/-- The actual normal cone at a scaled point is unchanged. -/
theorem normalCone_dilate (k : ℕ) (hk : 0 < k) (x : Ambient n) :
    (P.dilate k hk).normalCone ((k : ℝ) • x) = P.normalCone x := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  ext u
  have hsum (y : Ambient n) :
      (∑ i, u i * (((k : ℝ) • y) i - ((k : ℝ) • x) i)) =
        (k : ℝ) * ∑ i, u i * (y i - x i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  constructor
  · intro h y hy
    have hky : (k : ℝ) • y ∈ (P.dilate k hk).carrier := by
      rw [P.carrier_dilate]
      exact ⟨y, hy, rfl⟩
    have h' := h ((k : ℝ) • y) hky
    rw [hsum] at h'
    exact (mul_nonneg_iff_of_pos_left hkR).mp h'
  · intro h y hy
    rw [P.carrier_dilate] at hy
    obtain ⟨y, hy, rfl⟩ := hy
    rw [hsum]
    exact mul_nonneg hkR.le (h y hy)

/-- Equality of ordinary normal fans under positive dilation. -/
theorem sameNormalFan_dilate (k : ℕ) (hk : 0 < k) :
    P.SameNormalFan (P.dilate k hk) := by
  ext C
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(k : ℝ) • x, ?_, (P.normalCone_dilate k hk x).symm⟩
    rw [P.carrier_dilate]
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hC⟩
    rw [P.carrier_dilate] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx, hC.trans (P.normalCone_dilate k hk x)⟩

/-- Minkowski addition of a convex polytope and its positive dilation is the
next ordinary dilation. -/
theorem minkowskiSum_dilate (k : ℕ) (hk : 0 < k) :
    P.minkowskiSum (P.dilate k hk) = ((k + 1 : ℕ) : ℝ) • P.carrier := by
  rw [minkowskiSum, P.carrier_dilate]
  calc
    P.carrier + (k : ℝ) • P.carrier = (1 : ℝ) • P.carrier + (k : ℝ) • P.carrier := by simp
    _ = (1 + (k : ℝ)) • P.carrier :=
      ((convex_convexHull ℝ _).add_smul zero_le_one (Nat.cast_nonneg k)).symm
    _ = ((k + 1 : ℕ) : ℝ) • P.carrier := by congr 1; push_cast; ring

end LatticePolytope

end PaperVerification.ToricGeometry
end
end Source_ToricDilations
-- END ORIGINAL PaperVerification.ToricDilations


-- BEGIN ORIGINAL PaperVerification.ToricIDP
section Source_ToricIDP

-- original header: module
-- original header: public import PaperVerification.ToricDilations
-- original header: public import PaperVerification.ToricBoundary
-- original header: @[expose] public section
/-!
# Induction in the full integer-decomposition degree and face dimension

Interior targets use the actual Lemma 4.2 construction. Boundary targets use
integer decomposition on their actual proper faces, with no degree restriction.
The second theorem packages the remaining dimension induction through saturated
integral affine face charts.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped Pointwise
open PaperVerification.ToricExchange

namespace LatticePolytope

/-- Lowering a geometric edge-length bound preserves its meaning. -/
theorem edgesAtLeast_mono {n : ℕ} (P : LatticePolytope n) {a b : ℕ}
    (hP : P.EdgesAtLeast b) (hab : a ≤ b) : P.EdgesAtLeast a := by
  intro v w hvw
  obtain ⟨vZ, wZ, hvZ, hwZ, hlen⟩ := hP v w hvw
  exact ⟨vZ, wZ, hvZ, hwZ, hab.trans hlen⟩

/-- The full all-degree induction: actual interior splitting plus integer
decomposition on proper faces imply integer decomposition of the whole polytope. -/
theorem idp_of_boundary_faces {n : ℕ} (P : LatticePolytope n)
    (hP : P.Smooth) (hlP : P.EdgesAtLeast n)
    (hfaces : ∀ F : Set (Ambient n), F.Nonempty → Convex ℝ F →
      IsExtreme ℝ P.carrier F → F ≠ P.carrier →
      IntegerDecompositionProperty (embed n) F) :
    P.HasIDP := by
  change IntegerDecompositionProperty (embed n) P.carrier
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk z hz
    obtain ⟨x, hx, hz⟩ := hz
    by_cases hkone : k = 1
    · subst k
      have hzP : embed n z ∈ P.carrier := by rw [hz]; simpa using hx
      exact ⟨{⟨z, hzP⟩}, by simp, by simp⟩
    · have hprev : 0 < k - 1 := by omega
      have hprevlt : k - 1 < k := by omega
      have hprevadd : k - 1 + 1 = k := by omega
      by_cases hint : x ∈ interior P.carrier
      · have hm : embed n z ∈ interior (P.minkowskiSum (P.dilate (k - 1) hprev)) := by
          rw [P.minkowskiSum_dilate, hprevadd]
          have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
          rw [interior_smul₀ hkR]
          exact ⟨x, hint, hz.symm⟩
        obtain ⟨a, b, ha, hb, hab⟩ := P.interior_lattice_decomposition
          (P.dilate (k - 1) hprev) hP (P.smooth_dilate hP (k - 1) hprev)
          (P.sameNormalFan_dilate (k - 1) hprev) hlP
          (P.edgesAtLeast_dilate hlP (k - 1) hprev) z hm
        rw [P.carrier_dilate] at hb
        obtain ⟨y, hy, hyb⟩ := hb
        obtain ⟨s, hcard, htotal⟩ := ih (k - 1) hprevlt (by omega) b ⟨y, hy, hyb.symm⟩
        refine ⟨⟨a, ha⟩ ::ₘ s, ?_, ?_⟩
        · simpa only [Multiset.card_cons, hcard, hprevadd]
        · simpa only [total_cons, htotal] using hab
      · obtain ⟨F, hxF, hFc, hFP, hFproper⟩ := P.boundary_proper_face x hx hint
        obtain ⟨s, hcard, htotal⟩ := hfaces F ⟨x, hxF⟩ hFc hFP hFproper
          k hk z ⟨x, hxF, hz⟩
        let inc : latticePoints (embed n) F → latticePoints (embed n) P.carrier :=
          fun a => ⟨a, hFP.subset a.property⟩
        refine ⟨s.map inc, ?_, ?_⟩
        · simpa only [Multiset.card_map] using hcard
        · have hsum : total (latticePoints (embed n) P.carrier) (s.map inc) =
              total (latticePoints (embed n) F) s := by
            simp only [total, Multiset.map_map]
            rfl
          exact hsum.trans htotal

/-- Dimension induction transfers the exact edge threshold to every saturated
proper face. This theorem is the induction principle; its chart hypothesis must
be supplied by the separate face-inheritance construction. -/
theorem idp_of_smooth_face_charts
    (hcharts : ∀ n : ℕ, ∀ P : LatticePolytope n,
      P.Smooth → P.EdgesAtLeast n → ∀ F : Set (Ambient n),
      F.Nonempty → Convex ℝ F → IsExtreme ℝ P.carrier F → F ≠ P.carrier →
      ∃ (d : ℕ) (Q : LatticePolytope d) (e : IntegralAffineEmbedding d n),
        d < n ∧ Q.Smooth ∧ Q.EdgesAtLeast n ∧ e.realMap '' Q.carrier = F) :
    ∀ n : ℕ, ∀ P : LatticePolytope n, P.Smooth → P.EdgesAtLeast n → P.HasIDP := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P hP hlP
    apply P.idp_of_boundary_faces hP hlP
    intro F hFne hFc hFP hFproper
    obtain ⟨d, Q, e, hdn, hQ, hlQ, heQ⟩ := hcharts n P hP hlP F hFne hFc hFP hFproper
    have hQidp := ih d hdn Q hQ (Q.edgesAtLeast_mono hlQ hdn.le)
    have h := e.integerDecompositionProperty_image Q.carrier hQidp
    simpa only [heQ] using h

end LatticePolytope

end PaperVerification.ToricGeometry
end
end Source_ToricIDP
-- END ORIGINAL PaperVerification.ToricIDP


-- BEGIN ORIGINAL PaperVerification.ToricSmoothFaces
section Source_ToricSmoothFaces

-- original header: module
-- original header: public import PaperVerification.ToricFaceInheritance
-- original header: public import PaperVerification.ToricChartSmoothness
-- original header: public import PaperVerification.ToricIDP
-- original header: @[expose] public section
/-!
# Smooth face inheritance and the unrestricted integer decomposition theorem

The face chart is constructed from actual primitive edge directions. Saturation
preserves all lattice points and exact edge lengths; changing the local chart at
each vertex proves global smoothness. This closes the dimension induction in
the integer decomposition property without an additional geometric hypothesis.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

/-- Every geometric edge bound passes to a saturated coordinate polytope of
an actual face, with precisely the same bound. -/
theorem edgesAtLeast_face_chart {d bound : ℕ} (hP : P.EdgesAtLeast bound)
    (F : Set (Ambient n)) (hF : IsExtreme ℝ P.carrier F)
    (Q : LatticePolytope d) (e : IntegralAffineEmbedding d n)
    (heF : e.realMap '' Q.carrier = F) : Q.EdgesAtLeast bound := by
  apply (Q.edgesAtLeast_iff bound).mpr
  intro v w hvw
  have hedge : P.IsEdge (embed n (e.latticeMap v)) (embed n (e.latticeMap w)) := by
    rw [e.embed_latticeMap, e.embed_latticeMap]
    refine ⟨fun h => hvw.1 (e.realMap_injective h), ?_⟩
    have h := affine_isExtreme_image e.realMap e.realMap_injective hvw.2
    rw [heF, image_segment] at h
    exact hF.trans h
  have hlen := (P.edgesAtLeast_iff bound).mp hP (e.latticeMap v) (e.latticeMap w) hedge
  simpa only [e.latticeLength_latticeMap] using hlen

/-- Every nonempty actual convex face of a smooth lattice polytope is a
saturated integral affine image of a smooth full-dimensional lattice polytope.
All edge bounds are inherited, and every proper face has smaller dimension. -/
theorem smooth_face_chart {bound : ℕ} (hP : P.Smooth) (hlP : P.EdgesAtLeast bound)
    (F : Set (Ambient n)) (hFne : F.Nonempty) (hFconv : Convex ℝ F)
    (hF : IsExtreme ℝ P.carrier F) :
    ∃ (d : ℕ) (Q : LatticePolytope d) (e : IntegralAffineEmbedding d n),
      d ≤ n ∧ (F ≠ P.carrier → d < n) ∧ Q.Smooth ∧ Q.EdgesAtLeast bound ∧
        e.realMap '' Q.carrier = F := by
  obtain ⟨v, hv⟩ := P.face_vertices_nonempty F hFconv hF hFne
  obtain ⟨d, Q, e, lengths, hd, hdstrict, hezero, heF, hedges, hall⟩ :=
    P.exists_face_chart_at_vertex hP F hFconv hF v hv
  refine ⟨d, Q, e, hd, hdstrict, ?_, P.edgesAtLeast_face_chart hlP F hF Q e heF, heF⟩
  apply smooth_of_local_saturated_charts F Q e heF
  intro w hw
  obtain ⟨k, R, f, ls, hk, hkstrict, hfzero, hfF, haxis, hcomplete⟩ :=
    P.exists_face_chart_at_vertex hP F hFconv hF w hw
  exact ⟨k, R, f, ls, hfzero, hfF, haxis, hcomplete⟩

/-- The proper-face form needed in unrestricted dimension induction. -/
theorem proper_smooth_face_chart {bound : ℕ} (hP : P.Smooth)
    (hlP : P.EdgesAtLeast bound) (F : Set (Ambient n)) (hFne : F.Nonempty)
    (hFconv : Convex ℝ F) (hF : IsExtreme ℝ P.carrier F) (hproper : F ≠ P.carrier) :
    ∃ (d : ℕ) (Q : LatticePolytope d) (e : IntegralAffineEmbedding d n),
      d < n ∧ Q.Smooth ∧ Q.EdgesAtLeast bound ∧ e.realMap '' Q.carrier = F := by
  obtain ⟨d, Q, e, hd, hstrict, hQ, hlQ, heQ⟩ :=
    P.smooth_face_chart hP hlP F hFne hFconv hF
  exact ⟨d, Q, e, hstrict hproper, hQ, hlQ, heQ⟩

/-- Corollary 4.3: every smooth lattice polytope whose edges have length at
least its dimension has the full integer decomposition property in every degree.
This includes dimension zero and does not assume decomposition on its faces. -/
theorem integerDecomposition_of_smooth_long_edges (hP : P.Smooth)
    (hlP : P.EdgesAtLeast n) : P.HasIDP := by
  apply idp_of_smooth_face_charts ?_ n P hP hlP
  intro k R hR hlR F hFne hFconv hF hproper
  exact R.proper_smooth_face_chart hR hlR F hFne hFconv hF hproper

end LatticePolytope

end PaperVerification.ToricGeometry
end
end Source_ToricSmoothFaces
-- END ORIGINAL PaperVerification.ToricSmoothFaces


-- BEGIN ORIGINAL PaperVerification.ToricBundleFanPolytopes
section Source_ToricBundleFanPolytopes

-- original header: module

-- original header: public import PaperVerification.ToricBundleFanFaces
-- original header: public import PaperVerification.ToricFanPolytopeSmoothness
-- original header: public import PaperVerification.ToricSmoothFaces


-- original header: @[expose] public section
/-!
# Genuine endpoint base polytopes and inherited edge lengths

This combines the explicit quotient construction with the independently
proved fan/polytope dictionary.  Each endpoint divisor produces an actual
smooth lattice polytope with exactly the base normal fan; its edges inherit
the original bound through its saturated embedding as an actual face.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} {R : «Σ».PrimitiveRelation}
  (c : R.BundleCoordinates)

theorem fiberDegree_pos (c : R.BundleCoordinates) (hN : R.negative = ∅) (a : Lattice n → ℝ)
    (ha : «Σ».IsStrictSupport a) : 0 < ∑ v ∈ R.positive, a v := by
  have h := R.degree_pos_of_strictSupport ha
  simpa only [SmoothCompleteFan.PrimitiveRelation.degree, hN, Finset.sum_empty, sub_zero] using h

theorem endpoint_integerBaseWeight_cast (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a : Lattice n → ℤ) (u : Lattice n) :
    (fun q => (c.integerBaseWeight hR hN a (c.endpointIntegerWeight a u) q : ℝ)) =
      c.baseWeight hR hN (fun v => (a v : ℝ))
        (c.endpointWeight (fun v => (a v : ℝ)) u) := by
  funext q
  rw [c.integerBaseWeight_cast]
  congr 1
  funext v
  exact c.endpointIntegerWeight_cast a u v

/-- Complete geometric input for induction on the base: the actual
endpoint polytope, smoothness, its exact normal fan, unchanged edge bound,
and the saturated endpoint-face chart. -/
theorem exists_endpoint_basePolytope (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun v => (a v : ℝ)))
    (P : LatticePolytope n) (hP : P.carrier = «Σ».fanPolytope (fun v => (a v : ℝ)))
    {bound : ℕ} (hbound : P.EdgesAtLeast bound) {u : Lattice n} (hu : u ∈ R.positive) :
    ∃ Q : LatticePolytope (n - c.fiberIndices.card),
      Q.carrier = c.baseFan.fanPolytope
        (c.baseWeight hR hN (fun v => (a v : ℝ))
          (c.endpointWeight (fun v => (a v : ℝ)) u)) ∧
      Q.Smooth ∧ Q.normalFan = c.baseFan.realCones ∧ Q.EdgesAtLeast bound ∧
      (c.fiberChart a (c.endpointIntegerWeight a u)).realMap '' Q.carrier =
        c.endpointFace (fun v => (a v : ℝ)) u := by
  let A := c.integerBaseWeight hR hN a (c.endpointIntegerWeight a u)
  have hA : c.baseFan.IsStrictSupport (fun q => (A q : ℝ)) := by
    change c.baseFan.IsStrictSupport
      (fun q => (c.integerBaseWeight hR hN a (c.endpointIntegerWeight a u) q : ℝ))
    rw [c.endpoint_integerBaseWeight_cast hR hN a u]
    exact c.endpoint_isStrictSupport hR hN _ ha hu
  obtain ⟨Q, hQ, hQsm, hQfan⟩ := c.baseFan.exists_smooth_latticePolytope_of_integral_strictSupport
    (c.baseFan_isPure hpure) A hA
  have hQ' : Q.carrier = c.baseFan.fanPolytope
      (c.baseWeight hR hN (fun v => (a v : ℝ))
        (c.endpointWeight (fun v => (a v : ℝ)) u)) := by
    simpa only [A, c.endpoint_integerBaseWeight_cast hR hN a u] using hQ
  have hk : 0 ≤ ∑ v ∈ R.positive, a v := by
    have hpos := c.fiberDegree_pos hN (fun v => (a v : ℝ)) ha
    exact_mod_cast hpos.le
  have himage : (c.fiberChart a (c.endpointIntegerWeight a u)).realMap '' Q.carrier =
      c.endpointFace (fun v => (a v : ℝ)) u := by
    rw [hQ']
    exact c.endpointChart_image hR hN a hk hu
  have hface : IsExtreme ℝ P.carrier (c.endpointFace (fun v => (a v : ℝ)) u) := by
    rw [hP]
    exact c.endpointFace_isExtreme _ _
  have hlength : Q.EdgesAtLeast bound := P.edgesAtLeast_face_chart hbound _ hface Q
    (c.fiberChart a (c.endpointIntegerWeight a u)) himage
  exact ⟨Q, hQ', hQsm, hQfan, hlength, himage⟩

end SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

end PaperVerification.ToricGeometry
end
end Source_ToricBundleFanPolytopes
-- END ORIGINAL PaperVerification.ToricBundleFanPolytopes


-- BEGIN ORIGINAL PaperVerification.ToricBundleFanAverages
section Source_ToricBundleFanAverages

-- original header: module

-- original header: public import PaperVerification.ToricBundleFanEndpoints


-- original header: @[expose] public section
/-!
# Affine dependence of base divisors on homogeneous weights

The actual base coefficients are the barycentric average of the endpoint
coefficients, for every real homogeneous weight of the correct total degree.
Nonnegative weights therefore preserve strict support.  Addition and primitive
relation degrees use the same literal coefficient functions.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem IsStrictSupport.weighted_sum {κ : Type*} (s : Finset κ)
    (a : κ → Lattice n → ℝ) (w : κ → ℝ)
    (ha : ∀ i ∈ s, «Σ».IsStrictSupport (a i))
    (hw : ∀ i ∈ s, 0 ≤ w i) (hpos : ∃ i ∈ s, 0 < w i) :
    «Σ».IsStrictSupport (fun v => ∑ i ∈ s, w i * a i v) := by
  intro C hC
  let ℓ : κ → Ambient n →ₗ[ℝ] ℝ := fun i =>
    if hi : i ∈ s then Classical.choose (ha i hi C hC) else 0
  have he (i : κ) (hi : i ∈ s) : ∀ v ∈ C, ℓ i (embed n v) = a i v := by
    simpa only [ℓ, dif_pos hi] using (Classical.choose_spec (ha i hi C hC)).1
  have hlt (i : κ) (hi : i ∈ s) :
      ∀ v ∈ «Σ».rays, v ∉ C → ℓ i (embed n v) < a i v := by
    simpa only [ℓ, dif_pos hi] using (Classical.choose_spec (ha i hi C hC)).2
  refine ⟨∑ i ∈ s, w i • ℓ i, ?_, ?_⟩
  · intro v hv
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [he i hi v hv]
  · intro v hv hvC
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    have hgap : 0 < ∑ i ∈ s, w i * (a i v - ℓ i (embed n v)) := by
      apply Finset.sum_pos'
      · intro i hi
        exact mul_nonneg (hw i hi) (sub_pos.mpr (hlt i hi v hv hvC)).le
      · obtain ⟨i, hi, hiw⟩ := hpos
        exact ⟨i, hi, mul_pos hiw (sub_pos.mpr (hlt i hi v hv hvC))⟩
    simpa only [mul_sub, Finset.sum_sub_distrib, sub_pos] using hgap

namespace PrimitiveRelation

variable {«Σ»} (T : «Σ».PrimitiveRelation)

theorem degree_weighted_sum {κ : Type*} (s : Finset κ)
    (a : κ → Lattice n → ℝ) (w : κ → ℝ) :
    T.degree (fun v => ∑ i ∈ s, w i * a i v) = ∑ i ∈ s, w i * T.degree (a i) := by
  induction s using Finset.induction_on with
  | empty => simp [degree]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    change T.degree (w i • a i + (fun v => ∑ j ∈ s, w j * a j v)) = _
    rw [T.degree_add, T.degree_smul, ih]

end PrimitiveRelation

end SmoothCompleteFan

namespace SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} {R : «Σ».PrimitiveRelation}
  (c : R.BundleCoordinates)

theorem baseWeight_add (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅)
    (a b α β : Lattice n → ℝ) :
    c.baseWeight hR hN (a + b) (α + β) =
      c.baseWeight hR hN a α + c.baseWeight hR hN b β := by
  funext q
  unfold baseWeight
  simp only [Pi.add_apply]
  have he (i : Fin n) :
      (c.basis.repr (c.baseRayLift hR hN q) i : ℝ) *
        ((α (c.basis i) + β (c.basis i)) - (a (c.basis i) + b (c.basis i))) =
      (c.basis.repr (c.baseRayLift hR hN q) i : ℝ) * (α (c.basis i) - a (c.basis i)) +
        (c.basis.repr (c.baseRayLift hR hN q) i : ℝ) * (β (c.basis i) - b (c.basis i)) := by ring
  simp only [he, Finset.sum_add_distrib]
  ring

theorem baseWeight_congr_weight (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅)
    (a α β : Lattice n → ℝ) (h : ∀ v ∈ R.positive, α v = β v) :
    c.baseWeight hR hN a α = c.baseWeight hR hN a β := by
  funext q
  unfold baseWeight
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [h _ (c.fiber_subset_positive (Finset.mem_image.mpr ⟨i, hi, rfl⟩))]

theorem normalized_weights_sum (c : R.BundleCoordinates) (a α : Lattice n → ℝ)
    (hk : (∑ v ∈ R.positive, a v) ≠ 0)
    (hα : (∑ v ∈ R.positive, α v) = ∑ v ∈ R.positive, a v) :
    (∑ v ∈ R.positive, α v / (∑ w ∈ R.positive, a w)) = 1 := by
  rw [← Finset.sum_div, hα, div_self hk]

/-- The precise barycentric formula in Section 3.2, for all real weights
with the correct total fiber degree. -/
theorem baseWeight_convex_combination (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a α : Lattice n → ℝ)
    (hk : (∑ v ∈ R.positive, a v) ≠ 0)
    (hα : (∑ v ∈ R.positive, α v) = ∑ v ∈ R.positive, a v) :
    c.baseWeight hR hN a α = fun q =>
      ∑ v ∈ R.positive, (α v / (∑ w ∈ R.positive, a w)) *
        c.baseWeight hR hN a (c.endpointWeight a v) q := by
  funext q
  let k := ∑ w ∈ R.positive, a w
  let A := c.baseWeight hR hN a 0 q
  let E : Fin n → ℝ := fun i => (c.basis.repr (c.baseRayLift hR hN q) i : ℝ)
  have hsum : (∑ v ∈ R.positive, α v / k) = 1 := c.normalized_weights_sum a α hk hα
  have hi (i : Fin n) (hi : i ∈ c.fiberIndices) :
      (∑ v ∈ R.positive, α v / k * c.endpointWeight a v (c.basis i)) = α (c.basis i) := by
    have hbi := c.fiber_subset_positive (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    simp only [endpointWeight, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq]
    simp only [if_pos hbi]
    exact div_mul_cancel₀ _ hk
  have he (v : Lattice n) : c.baseWeight hR hN a (c.endpointWeight a v) q =
      A + ∑ i ∈ c.fiberIndices, E i * c.endpointWeight a v (c.basis i) :=
    c.baseWeight_affine hR hN a (c.endpointWeight a v) q
  rw [c.baseWeight_affine hR hN a α q]
  change A + (∑ i ∈ c.fiberIndices, E i * α (c.basis i)) = _
  simp_rw [he, mul_add, Finset.mul_sum]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hii
  calc
    E i * α (c.basis i) = E i *
        (∑ v ∈ R.positive, α v / k * c.endpointWeight a v (c.basis i)) := by rw [hi i hii]
    _ = ∑ v ∈ R.positive,
        α v / k * (E i * c.endpointWeight a v (c.basis i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      ring

/-- Every nonnegative homogeneous slice has a genuine strictly supported
base divisor, including boundary weights with zero entries. -/
theorem baseWeight_isStrictSupport (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a α : Lattice n → ℝ) (ha : «Σ».IsStrictSupport a)
    (hα : (∑ v ∈ R.positive, α v) = ∑ v ∈ R.positive, a v)
    (hα0 : ∀ v ∈ R.positive, 0 ≤ α v) :
    c.baseFan.IsStrictSupport (c.baseWeight hR hN a α) := by
  have hk : 0 < ∑ v ∈ R.positive, a v := by
    have h := R.degree_pos_of_strictSupport ha
    simpa only [SmoothCompleteFan.PrimitiveRelation.degree, hN, Finset.sum_empty, sub_zero] using h
  have hw (v : Lattice n) (hv : v ∈ R.positive) :
      0 ≤ α v / (∑ w ∈ R.positive, a w) := div_nonneg (hα0 v hv) hk.le
  have hsum := c.normalized_weights_sum a α hk.ne' hα
  have hpos : ∃ v ∈ R.positive, 0 < α v / (∑ w ∈ R.positive, a w) := by
    apply (Finset.sum_pos_iff_of_nonneg hw).mp
    rw [hsum]
    exact zero_lt_one
  rw [c.baseWeight_convex_combination hR hN a α hk.ne' hα]
  exact SmoothCompleteFan.IsStrictSupport.weighted_sum c.baseFan R.positive
    (fun v => c.baseWeight hR hN a (c.endpointWeight a v))
    (fun v => α v / (∑ w ∈ R.positive, a w))
    (fun v hv => c.endpoint_isStrictSupport hR hN a ha hv) hw hpos

/-- Any lower bound valid on all endpoint relation degrees is retained at
every nonnegative homogeneous weight. -/
theorem baseWeight_degree_lower_bound (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a α : Lattice n → ℝ)
    (hk : 0 < ∑ v ∈ R.positive, a v)
    (hα : (∑ v ∈ R.positive, α v) = ∑ v ∈ R.positive, a v)
    (hα0 : ∀ v ∈ R.positive, 0 ≤ α v)
    (T : c.baseFan.PrimitiveRelation) (B : ℝ)
    (hB : ∀ u ∈ R.positive,
      B ≤ T.degree (c.baseWeight hR hN a (c.endpointWeight a u))) :
    B ≤ T.degree (c.baseWeight hR hN a α) := by
  rw [c.baseWeight_convex_combination hR hN a α hk.ne' hα, T.degree_weighted_sum]
  calc
    B = (∑ u ∈ R.positive, α u / (∑ w ∈ R.positive, a w)) * B := by
      rw [c.normalized_weights_sum a α hk.ne' hα, one_mul]
    _ = ∑ u ∈ R.positive, α u / (∑ w ∈ R.positive, a w) * B :=
      Finset.sum_mul R.positive (fun u => α u / (∑ w ∈ R.positive, a w)) B
    _ ≤ _ := Finset.sum_le_sum (fun u hu => mul_le_mul_of_nonneg_left (hB u hu)
      (div_nonneg (hα0 u hu) hk.le))

end SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

end PaperVerification.ToricGeometry
end
end Source_ToricBundleFanAverages
-- END ORIGINAL PaperVerification.ToricBundleFanAverages


-- BEGIN ORIGINAL PaperVerification.ToricSupportAveragedEdges
section Source_ToricSupportAveragedEdges

-- original header: module

-- original header: public import PaperVerification.ToricFanPolytopeSmoothness
-- original header: public import PaperVerification.ToricBundleFanAverages


-- original header: @[expose] public section
/-!
# Edge bounds under convex averages on one actual normal fan

For each fixed primitive dual direction, every endpoint polytope contains
the initial segment of the prescribed common length.  Averaging its actual
Cartier vertices averages these feasible points.  The complete classification
of actual incident edges then bounds every edge of the averaged polytope.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem cartierPoint_weighted_sum {κ : Type*} (s : Finset κ)
    (a : κ → Lattice n → ℝ) (w : κ → ℝ) (C : «Σ».fullCones) :
    «Σ».cartierPoint (fun v => ∑ i ∈ s, w i * a i v) C =
      ∑ i ∈ s, w i • «Σ».cartierPoint (a i) C := by
  simp only [cartierPoint, Finset.sum_smul, Finset.smul_sum, smul_neg,
    mul_smul, Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_comm

theorem support_axis_point_of_edgesAtLeast (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {bound : ℕ} (hbound : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast bound)
    (s : «Σ».fullCones) (i : Fin n) :
    «Σ».cartierPoint (fun u => (a u : ℝ)) s + (bound : ℝ) • «Σ».cartierBasis s i ∈
      «Σ».fanPolytope (fun u => (a u : ℝ)) := by
  let P := «Σ».supportLatticePolytope hpure a ha
  obtain ⟨lengths, hlengths⟩ := «Σ».support_polytope_coordinate_edges hpure a ha s
  have hedge : P.IsEdge (embed n («Σ».cartierLatticePoint a s))
      (embed n («Σ».cartierLatticePoint a s +
        (lengths i : ℤ) • integralDualBasis («Σ».fullConeBasis s) i)) := by
    simpa only [«Σ».embed_cartierLatticePoint] using (hlengths i).2.1
  have hlen := P.edge_basis_length_bound hbound («Σ».cartierLatticePoint a s)
    (integralDualBasis («Σ».fullConeBasis s)) i (lengths i) hedge
  have hlenR : (bound : ℝ) ≤ lengths i := by exact_mod_cast hlen
  have hpos : (0 : ℝ) < lengths i := by exact_mod_cast (hlengths i).1
  let t : ℝ := bound / lengths i
  have ht : t ∈ Icc 0 1 := ⟨div_nonneg (Nat.cast_nonneg _) hpos.le,
    (div_le_one hpos).mpr hlenR⟩
  have hend : embed n («Σ».cartierLatticePoint a s +
      (lengths i : ℤ) • integralDualBasis («Σ».fullConeBasis s) i) =
      «Σ».cartierPoint (fun u => (a u : ℝ)) s + (lengths i : ℝ) • «Σ».cartierBasis s i := by
    rw [map_add, embed_int_smul, Int.cast_natCast, «Σ».embed_cartierLatticePoint]
    rw [cartierBasis, integralBasisReal_apply]
  have hseg : «Σ».cartierPoint (fun u => (a u : ℝ)) s + (bound : ℝ) • «Σ».cartierBasis s i ∈
      segment ℝ («Σ».cartierPoint (fun u => (a u : ℝ)) s)
        (embed n («Σ».cartierLatticePoint a s +
          (lengths i : ℤ) • integralDualBasis («Σ».fullConeBasis s) i)) := by
    rw [hend]
    refine ⟨1 - t, t, sub_nonneg.mpr ht.2, ht.1, by ring, ?_⟩
    have htlen : t * (lengths i : ℝ) = bound := div_mul_cancel₀ _ hpos.ne'
    rw [smul_add, smul_smul, htlen, sub_smul, one_smul]
    abel
  have hmem := (hlengths i).2.1.2.subset hseg
  simpa only [P, «Σ».supportLatticePolytope_carrier] using hmem

theorem support_edgesAtLeast_of_axis_points (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    (bound : ℕ)
    (haxis : ∀ s : «Σ».fullCones, ∀ i : Fin n,
      «Σ».cartierPoint (fun u => (a u : ℝ)) s + (bound : ℝ) • «Σ».cartierBasis s i ∈
        «Σ».fanPolytope (fun u => (a u : ℝ))) :
    («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast bound := by
  let P := «Σ».supportLatticePolytope hpure a ha
  apply (P.edgesAtLeast_iff bound).mpr
  intro v w hedge
  have hv := (P.edge_endpoints_extreme hedge).1
  have hP : P.carrier = convexHull ℝ (Set.range («Σ».cartierPoint (fun u => (a u : ℝ)))) := by
    rw [«Σ».supportLatticePolytope_carrier,
      «Σ».fanPolytope_eq_convexHull_cartier hpure _ (IsStrictSupport.isNef «Σ» ha)]
  have hv' := hP ▸ hv
  obtain ⟨s, hs⟩ := extremePoints_convexHull_subset hv'
  have hvZ : v = «Σ».cartierLatticePoint a s := by
    apply embed_injective n
    rw [«Σ».embed_cartierLatticePoint]
    exact hs.symm
  subst v
  have hedge' : P.IsEdge («Σ».cartierPoint (fun u => (a u : ℝ)) s) (embed n w) := by
    simpa only [«Σ».embed_cartierLatticePoint] using hedge
  obtain ⟨lengths, hlengths⟩ := «Σ».support_polytope_coordinate_edges hpure a ha s
  obtain ⟨i, hi⟩ := «Σ».support_polytope_edge_has_coordinate_direction hpure a ha s (embed n w) hedge'
  have hwseg := (hlengths i).2.2 ▸ hi
  have hverts := P.edge_endpoints_extreme hedge'
  have hend := (P.edge_endpoints_extreme (hlengths i).2.1).2.1
  have hwZ : w = «Σ».cartierLatticePoint a s +
      (lengths i : ℤ) • integralDualBasis («Σ».fullConeBasis s) i := by
    rcases (mem_extremePoints_iff_forall_segment.mp hverts.2).2
      _ hverts.1.1 _ hend hwseg with heq | heq
    · exact (hedge'.1 heq).elim
    · apply embed_injective n
      exact heq.symm
  rw [hwZ, LatticePolytope.latticeLength_basis_direction]
  have haxismem : «Σ».cartierPoint (fun u => (a u : ℝ)) s +
      (bound : ℝ) • «Σ».cartierBasis s i ∈
      P.coordinateRayFace («Σ».cartierPoint (fun u => (a u : ℝ)) s) («Σ».cartierBasis s) i := by
    refine ⟨?_, ?_⟩
    · simpa only [P, «Σ».supportLatticePolytope_carrier] using haxis s i
    · intro j hji
      simp [Module.Basis.repr_self_apply, hji, Ne.symm hji]
  rw [(hlengths i).2.2] at haxismem
  obtain ⟨r, t, hr, ht, hrt, he⟩ := haxismem
  have ht1 : t ≤ 1 := by linarith
  have he' := congrArg (fun x => («Σ».cartierBasis s).repr x i) he
  have hend' : embed n («Σ».cartierLatticePoint a s +
      (lengths i : ℤ) • integralDualBasis («Σ».fullConeBasis s) i) =
      «Σ».cartierPoint (fun u => (a u : ℝ)) s + (lengths i : ℝ) • «Σ».cartierBasis s i := by
    rw [map_add, embed_int_smul, Int.cast_natCast, «Σ».embed_cartierLatticePoint]
    rw [cartierBasis, integralBasisReal_apply]
  rw [hend'] at he'
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
    Module.Basis.repr_self_apply, if_pos rfl, ite_true, smul_eq_mul, mul_one] at he'
  have hlen0 : (0 : ℝ) ≤ lengths i := Nat.cast_nonneg _
  have hlength : (bound : ℝ) ≤ lengths i := by
    have hm := mul_le_mul_of_nonneg_right ht1 hlen0
    have hscaled := congrArg
      (fun t : ℝ => t * («Σ».cartierBasis s).repr
        («Σ».cartierPoint (fun u => (a u : ℝ)) s) i) hrt
    simp only [add_mul, one_mul] at hscaled
    nlinarith only [he', hscaled, hm]
  exact_mod_cast hlength

/-- Edge bounds are preserved by a convex combination of integral strictly
supported coefficients whenever the resulting coefficients are integral. -/
theorem support_edgesAtLeast_convex_combination {κ : Type*} (s : Finset κ)
    (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    (A : κ → Lattice n → ℤ)
    (hA : ∀ i ∈ s, «Σ».IsStrictSupport (fun u => (A i u : ℝ)))
    (w : κ → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : (∑ i ∈ s, w i) = 1)
    (hcoeff : (fun u => (a u : ℝ)) = fun u => ∑ i ∈ s, w i * (A i u : ℝ))
    (bound : ℕ)
    (hedges : ∀ i (hi : i ∈ s),
      («Σ».supportLatticePolytope hpure (A i) (hA i hi)).EdgesAtLeast bound) :
    («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast bound := by
  apply «Σ».support_edgesAtLeast_of_axis_points hpure a ha bound
  intro C j
  have hv : «Σ».cartierPoint (fun u => (a u : ℝ)) C =
      ∑ i ∈ s, w i • «Σ».cartierPoint (fun u => (A i u : ℝ)) C := by
    rw [hcoeff, «Σ».cartierPoint_weighted_sum]
  intro u hu
  have hle := Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left
    («Σ».support_axis_point_of_edgesAtLeast hpure (A i) (hA i hi) (hedges i hi) C j u hu)
      (hw i hi))
  change -(a u : ℝ) ≤ (dotProductEquiv ℝ (Fin n) (embed n u))
    («Σ».cartierPoint (fun u => (a u : ℝ)) C + (bound : ℝ) • «Σ».cartierBasis C j)
  rw [show (a u : ℝ) = ∑ i ∈ s, w i * (A i u : ℝ) from congrFun hcoeff u, hv]
  simp only [map_add, map_sum, map_smul, smul_eq_mul] at hle ⊢
  have hconst : (∑ i ∈ s, w i * ((bound : ℝ) *
      (dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierBasis C j))) =
      (bound : ℝ) * (dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierBasis C j) := by
    rw [← Finset.sum_mul, hsum, one_mul]
  simp only [mul_add, mul_neg, Finset.sum_neg_distrib,
    Finset.sum_add_distrib, hconst] at hle
  exact hle

end PaperVerification.ToricGeometry.SmoothCompleteFan
end
end Source_ToricSupportAveragedEdges
-- END ORIGINAL PaperVerification.ToricSupportAveragedEdges


-- BEGIN ORIGINAL PaperVerification.ToricBundleFanEdgeBounds
section Source_ToricBundleFanEdgeBounds

-- original header: module

-- original header: public import PaperVerification.ToricBundleFanPolytopes
-- original header: public import PaperVerification.ToricSupportAveragedEdges


-- original header: @[expose] public section
/-!
# Actual base polytopes at arbitrary integral homogeneous weights

Every nonnegative integral homogeneous weight gives an actual smooth lattice
polytope with the same base normal fan.  All its edge lengths retain the
original bound.  The proof transfers the endpoint faces through saturated
charts and then averages feasible primitive axis segments on the fixed fan.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace LatticePolytope

theorem edgesAtLeast_of_le {n : ℕ} (P : LatticePolytope n) {a b : ℕ}
    (h : P.EdgesAtLeast b) (hab : a ≤ b) : P.EdgesAtLeast a := by
  intro v w hedge
  obtain ⟨vZ, wZ, hv, hw, hlength⟩ := h v w hedge
  exact ⟨vZ, wZ, hv, hw, hab.trans hlength⟩

theorem edgesAtLeast_congr {n : ℕ} {P Q : LatticePolytope n}
    (h : P.carrier = Q.carrier) {bound : ℕ} :
    P.EdgesAtLeast bound ↔ Q.EdgesAtLeast bound := by
  simp only [EdgesAtLeast, IsEdge, h]

end LatticePolytope

namespace SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} {R : «Σ».PrimitiveRelation}
  (c : R.BundleCoordinates)

theorem integerBaseWeight_isStrictSupport (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a α : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun v => (a v : ℝ)))
    (hα : (∑ v ∈ R.positive, α v) = ∑ v ∈ R.positive, a v)
    (hα0 : ∀ v ∈ R.positive, 0 ≤ α v) :
    c.baseFan.IsStrictSupport (fun q => (c.integerBaseWeight hR hN a α q : ℝ)) := by
  have hαR : (∑ v ∈ R.positive, (α v : ℝ)) = ∑ v ∈ R.positive, (a v : ℝ) := by
    exact_mod_cast hα
  have hαR0 (v : Lattice n) (hv : v ∈ R.positive) : (0 : ℝ) ≤ α v := by
    exact_mod_cast hα0 v hv
  have he : (fun q => (c.integerBaseWeight hR hN a α q : ℝ)) =
      c.baseWeight hR hN (fun v => (a v : ℝ)) (fun v => (α v : ℝ)) := by
    funext q
    exact c.integerBaseWeight_cast hR hN a α q
  rw [he]
  exact c.baseWeight_isStrictSupport hR hN _ _ ha hαR hαR0

theorem support_basePolytope_edgesAtLeast (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (hpure : «Σ».IsPure) (a α : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun v => (a v : ℝ)))
    (hα : (∑ v ∈ R.positive, α v) = ∑ v ∈ R.positive, a v)
    (hα0 : ∀ v ∈ R.positive, 0 ≤ α v)
    (P : LatticePolytope n) (hP : P.carrier = «Σ».fanPolytope (fun v => (a v : ℝ)))
    {bound : ℕ} (hbound : P.EdgesAtLeast bound) :
    (c.baseFan.supportLatticePolytope (c.baseFan_isPure hpure)
      (c.integerBaseWeight hR hN a α)
      (c.integerBaseWeight_isStrictSupport hR hN a α ha hα hα0)).EdgesAtLeast bound := by
  let aR : Lattice n → ℝ := fun v => (a v : ℝ)
  let αR : Lattice n → ℝ := fun v => (α v : ℝ)
  let A : Lattice n → Lattice (n - c.fiberIndices.card) → ℤ :=
    fun u => c.integerBaseWeight hR hN a (c.endpointIntegerWeight a u)
  have hA (u : Lattice n) (hu : u ∈ R.positive) :
      c.baseFan.IsStrictSupport (fun q => (A u q : ℝ)) := by
    change c.baseFan.IsStrictSupport
      (fun q => (c.integerBaseWeight hR hN a (c.endpointIntegerWeight a u) q : ℝ))
    rw [c.endpoint_integerBaseWeight_cast hR hN a u]
    exact c.endpoint_isStrictSupport hR hN _ ha hu
  have hsum : (∑ v ∈ R.positive, αR v) = ∑ v ∈ R.positive, aR v := by
    change (∑ v ∈ R.positive, (α v : ℝ)) = ∑ v ∈ R.positive, (a v : ℝ)
    exact_mod_cast hα
  have hk : 0 < ∑ v ∈ R.positive, aR v := c.fiberDegree_pos hN aR ha
  have hweights (v : Lattice n) (hv : v ∈ R.positive) :
      0 ≤ αR v / (∑ w ∈ R.positive, aR w) := by
    apply div_nonneg _ hk.le
    change (0 : ℝ) ≤ (α v : ℝ)
    exact_mod_cast hα0 v hv
  have hcoeff : (fun q => (c.integerBaseWeight hR hN a α q : ℝ)) =
      fun q => ∑ u ∈ R.positive, (αR u / (∑ v ∈ R.positive, aR v)) * (A u q : ℝ) := by
    funext q
    rw [c.integerBaseWeight_cast]
    have he := congrFun (c.baseWeight_convex_combination hR hN aR αR hk.ne' hsum) q
    change c.baseWeight hR hN aR αR q =
      ∑ u ∈ R.positive, (αR u / (∑ v ∈ R.positive, aR v)) *
        (c.integerBaseWeight hR hN a (c.endpointIntegerWeight a u) q : ℝ)
    calc
      c.baseWeight hR hN aR αR q =
          ∑ u ∈ R.positive, (αR u / (∑ v ∈ R.positive, aR v)) *
            c.baseWeight hR hN aR (c.endpointWeight aR u) q := he
      _ = _ := by
        apply Finset.sum_congr rfl
        intro u hu
        exact congrArg (fun t : ℝ => (αR u / (∑ v ∈ R.positive, aR v)) * t)
          (congrFun (c.endpoint_integerBaseWeight_cast hR hN a u) q).symm
  apply c.baseFan.support_edgesAtLeast_convex_combination R.positive
    (c.baseFan_isPure hpure) _ _ A hA
    (fun u => αR u / (∑ v ∈ R.positive, aR v)) hweights
    (c.normalized_weights_sum aR αR hk.ne' hsum) hcoeff bound
  intro u hu
  obtain ⟨Q, hQ, _, _, hQbound, _⟩ :=
    c.exists_endpoint_basePolytope hR hN hpure a ha P hP hbound hu
  have he : Q.carrier = (c.baseFan.supportLatticePolytope
      (c.baseFan_isPure hpure) (A u) (hA u hu)).carrier := by
    rw [c.baseFan.supportLatticePolytope_carrier, hQ]
    congr 1
    exact (c.endpoint_integerBaseWeight_cast hR hN a u).symm
  exact (LatticePolytope.edgesAtLeast_congr he).mp hQbound

/-- Full induction data for every integral homogeneous fiber weight, with
the actual carrier, actual normal fan, and unchanged geometric edge bound. -/
theorem exists_basePolytope (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (hpure : «Σ».IsPure) (a α : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun v => (a v : ℝ)))
    (hα : (∑ v ∈ R.positive, α v) = ∑ v ∈ R.positive, a v)
    (hα0 : ∀ v ∈ R.positive, 0 ≤ α v)
    (P : LatticePolytope n) (hP : P.carrier = «Σ».fanPolytope (fun v => (a v : ℝ)))
    {bound : ℕ} (hbound : P.EdgesAtLeast bound) :
    ∃ Q : LatticePolytope (n - c.fiberIndices.card),
      Q.carrier = c.baseFan.fanPolytope
        (fun q => (c.integerBaseWeight hR hN a α q : ℝ)) ∧
      Q.Smooth ∧ Q.normalFan = c.baseFan.realCones ∧ Q.EdgesAtLeast bound := by
  let hA := c.integerBaseWeight_isStrictSupport hR hN a α ha hα hα0
  let Q := c.baseFan.supportLatticePolytope (c.baseFan_isPure hpure)
    (c.integerBaseWeight hR hN a α) hA
  exact ⟨Q, c.baseFan.supportLatticePolytope_carrier _ _ _,
    c.baseFan.supportLatticePolytope_smooth _ _ _,
    c.baseFan.supportLatticePolytope_normalFan _ _ _,
    c.support_basePolytope_edgesAtLeast hR hN hpure a α ha hα hα0 P hP hbound⟩

end SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

end PaperVerification.ToricGeometry
end
end Source_ToricBundleFanEdgeBounds
-- END ORIGINAL PaperVerification.ToricBundleFanEdgeBounds


-- BEGIN ORIGINAL PaperVerification.ToricAdjointSupport
section Source_ToricAdjointSupport

-- original header: module

-- original header: public import PaperVerification.ToricFanPolytopes
-- original header: public import Mathlib.Topology.Algebra.Order.Field

-- original header: @[expose] public section

/-!
# Interior lattice points and the literal canonical shift

Primitive fan rays are nonzero integral vectors. The topological interior
is therefore cut out by the strict ray inequalities. At a lattice point,
strict integral slack is equivalent to slack at least one, exactly the
coefficient shift by minus one used for the toric canonical divisor.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem normalRay_functional_ne_zero (u : Lattice n) (hu : u ∈ «Σ».rays) :
    dotProductEquiv ℝ (Fin n) (embed n u) ≠ 0 := by
  intro he
  have hemb : embed n u = 0 := (dotProductEquiv ℝ (Fin n)).injective (by simpa using he)
  exact «Σ».ray_ne_zero hu ((embed_injective n) (by simpa using hemb))

/-- The topological interior uses strict inequalities for the actual
nonzero primitive rays. This includes dimension zero. -/
theorem interior_fanPolytope_eq (a : Lattice n → ℝ) :
    interior («Σ».fanPolytope a) =
      {x | ∀ u ∈ «Σ».rays, -a u < (dotProductEquiv ℝ (Fin n) (embed n u)) x} := by
  ext x
  constructor
  · intro hx u hu
    rw [«Σ».fanPolytope_eq_normalHalfspaces] at hx
    exact strict_support_of_interior
      (fun v : «Σ».rays => dotProductEquiv ℝ (Fin n) (embed n v))
      (fun v : «Σ».rays => -a v) x hx ⟨u, hu⟩ («Σ».normalRay_functional_ne_zero u hu)
  · intro hx
    let U : Set (Ambient n) :=
      ⋂ u ∈ «Σ».rays, {x | -a u < (dotProductEquiv ℝ (Fin n) (embed n u)) x}
    have hUopen : IsOpen U := by
      apply isOpen_biInter_finset
      intro u hu
      exact isOpen_lt continuous_const
        (dotProductEquiv ℝ (Fin n) (embed n u)).continuous_of_finiteDimensional
    have hxU : x ∈ U := Set.mem_iInter₂.mpr hx
    have hUsub : U ⊆ «Σ».fanPolytope a := by
      intro y hy u hu
      exact (Set.mem_iInter₂.mp hy u hu).le
    exact (interior_maximal hUsub hUopen) hxU

/-- The integral support pairing agrees with the genuine integer dot
product before casting. -/
theorem normalRay_pairing_lattice (u z : Lattice n) :
    (dotProductEquiv ℝ (Fin n) (embed n u)) (embed n z) =
      ((∑ i, u i * z i : ℤ) : ℝ) := by
  simp [dotProductEquiv, dotProduct, embed]

/-- A lattice point lies in the actual interior exactly when it lies in
the support polytope with every primitive coefficient reduced by one. -/
theorem lattice_mem_interior_iff_adjointSupport (a : Lattice n → ℤ) (z : Lattice n) :
    embed n z ∈ interior («Σ».fanPolytope (fun u => (a u : ℝ))) ↔
      embed n z ∈ «Σ».fanPolytope (fun u => ((a u - 1 : ℤ) : ℝ)) := by
  rw [«Σ».interior_fanPolytope_eq]
  constructor
  · intro hz u hu
    have h := hz u hu
    change -(a u : ℝ) < (dotProductEquiv ℝ (Fin n) (embed n u)) (embed n z) at h
    change -((a u - 1 : ℤ) : ℝ) ≤
      (dotProductEquiv ℝ (Fin n) (embed n u)) (embed n z)
    rw [normalRay_pairing_lattice] at h ⊢
    have hi : -a u < ∑ i, u i * z i := by exact_mod_cast h
    have hi' : -(a u - 1) ≤ ∑ i, u i * z i := by omega
    exact_mod_cast hi'
  · intro hz u hu
    have h := hz u hu
    change -((a u - 1 : ℤ) : ℝ) ≤
      (dotProductEquiv ℝ (Fin n) (embed n u)) (embed n z) at h
    change -(a u : ℝ) < (dotProductEquiv ℝ (Fin n) (embed n u)) (embed n z)
    rw [normalRay_pairing_lattice] at h ⊢
    have hi : -(a u - 1) ≤ ∑ i, u i * z i := by exact_mod_cast h
    have hi' : -a u < ∑ i, u i * z i := by omega
    exact_mod_cast hi'

end PaperVerification.ToricGeometry.SmoothCompleteFan
end
end Source_ToricAdjointSupport
-- END ORIGINAL PaperVerification.ToricAdjointSupport


-- BEGIN ORIGINAL PaperVerification.ToricSimplexAdjoint
section Source_ToricSimplexAdjoint

-- original header: module
-- original header: public import PaperVerification.ToricSimplexGeometry
-- original header: public import Lean.Elab.Tactic.Omega
-- original header: @[expose] public section
/-!
# Adjoint simplex allocation

The second summand has every homogeneous coordinate strictly positive.
This is exactly the simplex case of the interior-summand theorem, including
the endpoint where its adjoint simplex is a point.
-/

namespace PaperVerification.Toric

open scoped BigOperators Pointwise

/-- Allocate a homogeneous simplex target so that the entire second vector
is strictly positive. Only the second degree needs the interior threshold. -/
theorem simplex_adjoint_homogeneous {d k l : ℕ}
    (hdl : d + 1 ≤ l) (m : Fin (d + 1) → ℕ)
    (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = k + l) :
    ∃ a b : Fin (d + 1) → ℕ,
      (∀ i, a i + b i = m i) ∧
      (∑ i, a i) = k ∧ (∑ i, b i) = l ∧
      (∀ i, 0 < b i) := by
  let c : Fin (d + 1) → ℕ := fun i => m i - 1
  have hc (i : Fin (d + 1)) : c i + 1 = m i := by
    dsimp [c]
    have h := hm i
    omega
  have hcSum : (∑ i, c i) + (d + 1) = k + l := by
    calc
      (∑ i, c i) + (d + 1) = ∑ i, (c i + 1) := by
        simp [Finset.sum_add_distrib]
      _ = ∑ i, m i := Finset.sum_congr rfl (fun i _ => hc i)
      _ = k + l := hsum
  obtain ⟨a, ha, haSum⟩ := allocate_le_sum Finset.univ c k (by omega)
  let b : Fin (d + 1) → ℕ := fun i => m i - a i
  have hab (i : Fin (d + 1)) : a i + b i = m i := by
    have hai := ha i (Finset.mem_univ i)
    have hci := hc i
    dsimp [b]
    omega
  have hb (i : Fin (d + 1)) : 0 < b i := by
    have hai := ha i (Finset.mem_univ i)
    have hci := hc i
    dsimp [b]
    omega
  have habSum : (∑ i, a i) + (∑ i, b i) = k + l := by
    rw [← Finset.sum_add_distrib]
    exact (Finset.sum_congr rfl (fun i _ => hab i)).trans hsum
  exact ⟨a, b, hab, haSum, by omega, hb⟩

/-- Affine natural-coordinate form, with all coordinates of the second
summand positive and strict slack in its degree inequality. -/
theorem simplex_adjoint_affine {d k l : ℕ}
    (hdl : d + 1 ≤ l) (m : Fin d → ℕ)
    (hm : ∀ i, 0 < m i) (hmsum : (∑ i, m i) < k + l) :
    ∃ a b : Fin d → ℕ,
      NatSimplex k a ∧ (∀ i, 0 < b i) ∧ (∑ i, b i) < l ∧
      (∀ i, a i + b i = m i) := by
  let m' : Fin (d + 1) → ℕ := Fin.cons (k + l - ∑ i, m i) m
  have hm' : ∀ i, 0 < m' i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [m', Fin.cons_zero]
      omega
    · simpa only [m', Fin.cons_succ] using hm j
  have hsum' : ∑ i, m' i = k + l := by
    simp only [Fin.sum_univ_succ, m', Fin.cons_zero, Fin.cons_succ]
    omega
  obtain ⟨a', b', hab, ha, hb, hbpos⟩ :=
    simplex_adjoint_homogeneous hdl m' hm' hsum'
  refine ⟨fun i => a' i.succ, fun i => b' i.succ, ?_, ?_, ?_, ?_⟩
  · change (∑ i : Fin d, a' i.succ) ≤ k
    rw [Fin.sum_univ_succ] at ha
    omega
  · exact fun i => hbpos i.succ
  · change (∑ i : Fin d, b' i.succ) < l
    rw [Fin.sum_univ_succ] at hb
    have hzero := hbpos 0
    omega
  · intro i
    simpa only [m', Fin.cons_succ] using hab i.succ

/-- The full ambient integer-lattice simplex allocation. -/
theorem simplex_adjoint_integer {d k l : ℕ}
    (hdl : d + 1 ≤ l) (m : Fin d → ℤ)
    (hm : ∀ i, 0 < m i) (hmsum : (∑ i, m i) < (k + l : ℕ)) :
    ∃ a b : Fin d → ℤ,
      IntegerSimplex k a ∧ (∀ i, 0 < b i) ∧ (∑ i, b i) < (l : ℤ) ∧
      (∀ i, a i + b i = m i) := by
  let mN : Fin d → ℕ := fun i => (m i).toNat
  have hmN (i : Fin d) : 0 < mN i := by
    have h := hm i
    dsimp [mN]
    omega
  have hmcast (i : Fin d) : (mN i : ℤ) = m i :=
    Int.toNat_of_nonneg (le_of_lt (hm i))
  have hmNsum : (∑ i, mN i) < k + l := by
    have hcast : ((∑ i, mN i : ℕ) : ℤ) = ∑ i, m i := by
      simp only [Nat.cast_sum, hmcast]
    omega
  obtain ⟨aN, bN, ha, hbpos, hbSum, hab⟩ :=
    simplex_adjoint_affine hdl mN hmN hmNsum
  refine ⟨fun i => (aN i : ℤ), fun i => (bN i : ℤ),
    (natSimplex_iff_integerSimplex aN).mp ha, ?_, ?_, ?_⟩
  · intro i
    change (0 : ℤ) < (bN i : ℤ)
    exact_mod_cast hbpos i
  · change (∑ i : Fin d, (bN i : ℤ)) < (l : ℤ)
    exact_mod_cast hbSum
  · intro i
    change (aN i : ℤ) + (bN i : ℤ) = m i
    rw [← Nat.cast_add, hab, hmcast]

/-- The actual topological simplex case of the interior-summand assertion.
All dimensions, arbitrary first degree, and the second adjoint endpoint are
included. -/
theorem simplex_adjoint_topological {d k l : ℕ}
    (hdl : d + 1 ≤ l) (m : Fin d → ℤ)
    (hm : (fun i => (m i : ℝ)) ∈
      interior (RealSimplex d k + RealSimplex d l)) :
    ∃ a b : Fin d → ℤ,
      (fun i => (a i : ℝ)) ∈ RealSimplex d k ∧
      (fun i => (b i : ℝ)) ∈ interior (RealSimplex d l) ∧
      (∀ i, a i + b i = m i) := by
  cases d with
  | zero =>
      have hsimplex (r : ℕ) : RealSimplex 0 (r : ℝ) = Set.univ := by
        ext x
        simp [RealSimplex]
      refine ⟨0, m, ?_, ?_, ?_⟩
      · rw [hsimplex k]
        exact Set.mem_univ _
      · rw [hsimplex l, interior_univ]
        exact Set.mem_univ _
      · intro i
        simp
  | succ d =>
      have hm' := interior_mono (add_realSimplex_subset (d + 1) k l) hm
      rw [interior_realSimplex] at hm'
      have hmpos (i : Fin (d + 1)) : 0 < m i :=
        Int.cast_pos.mp (hm'.1 i)
      have hmsum : (∑ i, m i) < (k + l : ℕ) := by
        have h := hm'.2
        push_cast at h ⊢
        exact_mod_cast h
      obtain ⟨a, b, ha, hbpos, hbSum, hab⟩ :=
        simplex_adjoint_integer hdl m hmpos hmsum
      refine ⟨a, b, (integerSimplex_iff_realSimplex a).mp ha, ?_, hab⟩
      rw [interior_realSimplex]
      refine ⟨fun i => Int.cast_pos.mpr (hbpos i), ?_⟩
      change (∑ i : Fin (d + 1), (b i : ℝ)) < (l : ℝ)
      exact_mod_cast hbSum

end PaperVerification.Toric

end Source_ToricSimplexAdjoint
-- END ORIGINAL PaperVerification.ToricSimplexAdjoint


-- BEGIN ORIGINAL PaperVerification.ToricBundleFanAllocation
section Source_ToricBundleFanAllocation

-- original header: module

-- original header: public import PaperVerification.ToricBundleFanIntegral
-- original header: public import PaperVerification.ToricSimplexParity
-- original header: public import PaperVerification.ToricSimplexAdjoint


-- original header: @[expose] public section
/-!
# Integral homogeneous weights in a genuine bundle lattice

The independent fiber coordinates are an actual subset of an integral
basis.  Finite simplex allocation applies in those coordinates; the omitted
homogeneous coordinate is the remaining total degree.  This retains all
integral targets, all parity classes, and zero coordinates on boundary slices.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

def finsetIntegerExtension {ι : Type*} (s : Finset ι)
    (a : Fin s.card → ℤ) (i : ι) : ℤ :=
  if hi : i ∈ s then a (s.equivFin ⟨i, hi⟩) else 0

theorem finsetIntegerExtension_apply {ι : Type*} (s : Finset ι)
    (a : Fin s.card → ℤ) {i : ι} (hi : i ∈ s) :
    finsetIntegerExtension s a i = a (s.equivFin ⟨i, hi⟩) := by
  simp only [finsetIntegerExtension, dif_pos hi]

theorem sum_finsetIntegerExtension {ι : Type*} (s : Finset ι)
    (a : Fin s.card → ℤ) :
    (∑ i ∈ s, finsetIntegerExtension s a i) = ∑ j, a j := by
  calc
    (∑ i ∈ s, finsetIntegerExtension s a i) =
        ∑ i : s, finsetIntegerExtension s a i :=
      (Finset.sum_coe_sort s (finsetIntegerExtension s a)).symm
    _ = ∑ i : s, a (s.equivFin i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact finsetIntegerExtension_apply s a i.property
    _ = ∑ j, a j := s.equivFin.sum_comp a

theorem sum_finsetIntegerRestriction {ι : Type*} (s : Finset ι) (a : ι → ℤ) :
    (∑ j : Fin s.card, a (s.equivFin.symm j)) = ∑ i ∈ s, a i := by
  calc
    (∑ j : Fin s.card, a (s.equivFin.symm j)) = ∑ i : s, a i :=
      s.equivFin.symm.sum_comp (fun i : s => a i)
    _ = ∑ i ∈ s, a i := Finset.sum_coe_sort s a

theorem finset_simplex_parity_integer {ι : Type*} (s : Finset ι) {k l : ℕ}
    (hk : s.card ≤ k) (hl : s.card ≤ l) (m p : ι → ℤ)
    (hm : ∀ i ∈ s, 0 < m i) (hsum : (∑ i ∈ s, m i) < (k + l : ℕ)) :
    ∃ a b : ι → ℤ,
      (∀ i ∈ s, 0 ≤ a i) ∧ (∑ i ∈ s, a i) ≤ k ∧
      (∀ i ∈ s, 0 ≤ b i) ∧ (∑ i ∈ s, b i) ≤ l ∧
      (∀ i ∈ s, a i + b i = m i) ∧
      (∀ i ∈ s, (a i - p i) % 2 = 0) := by
  let m' : Fin s.card → ℤ := fun j => m (s.equivFin.symm j)
  let p' : Fin s.card → ℤ := fun j => p (s.equivFin.symm j)
  have hm' (j : Fin s.card) : 0 < m' j := hm _ (s.equivFin.symm j).property
  have hsum' : (∑ j, m' j) < (k + l : ℕ) := by
    simpa only [m', sum_finsetIntegerRestriction] using hsum
  obtain ⟨a, b, ha, hb, hab, hpar⟩ :=
    PaperVerification.Toric.simplex_parity_integer hk hl m' p' hm' hsum'
  refine ⟨finsetIntegerExtension s a, finsetIntegerExtension s b,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [finsetIntegerExtension_apply s a hi]
    exact ha.1 _
  · rw [sum_finsetIntegerExtension]
    exact ha.2
  · intro i hi
    rw [finsetIntegerExtension_apply s b hi]
    exact hb.1 _
  · rw [sum_finsetIntegerExtension]
    exact hb.2
  · intro i hi
    simpa only [finsetIntegerExtension_apply s a hi,
      finsetIntegerExtension_apply s b hi, m', Equiv.symm_apply_apply] using
      hab (s.equivFin ⟨i, hi⟩)
  · intro i hi
    simpa only [finsetIntegerExtension_apply s a hi, p', Equiv.symm_apply_apply] using
      hpar (s.equivFin ⟨i, hi⟩)

theorem finset_simplex_adjoint_integer {ι : Type*} (s : Finset ι) {k l : ℕ}
    (hl : s.card + 1 ≤ l) (m : ι → ℤ)
    (hm : ∀ i ∈ s, 0 < m i) (hsum : (∑ i ∈ s, m i) < (k + l : ℕ)) :
    ∃ a b : ι → ℤ,
      (∀ i ∈ s, 0 ≤ a i) ∧ (∑ i ∈ s, a i) ≤ k ∧
      (∀ i ∈ s, 0 < b i) ∧ (∑ i ∈ s, b i) < l ∧
      (∀ i ∈ s, a i + b i = m i) := by
  let m' : Fin s.card → ℤ := fun j => m (s.equivFin.symm j)
  have hm' (j : Fin s.card) : 0 < m' j := hm _ (s.equivFin.symm j).property
  have hsum' : (∑ j, m' j) < (k + l : ℕ) := by
    simpa only [m', sum_finsetIntegerRestriction] using hsum
  obtain ⟨a, b, ha, hbpos, hbsum, hab⟩ :=
    PaperVerification.Toric.simplex_adjoint_integer hl m' hm' hsum'
  refine ⟨finsetIntegerExtension s a, finsetIntegerExtension s b,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [finsetIntegerExtension_apply s a hi]
    exact ha.1 _
  · rw [sum_finsetIntegerExtension]
    exact ha.2
  · intro i hi
    rw [finsetIntegerExtension_apply s b hi]
    exact hbpos _
  · rw [sum_finsetIntegerExtension]
    exact hbsum
  · intro i hi
    simpa only [finsetIntegerExtension_apply s a hi,
      finsetIntegerExtension_apply s b hi, m', Equiv.symm_apply_apply] using
      hab (s.equivFin ⟨i, hi⟩)

namespace SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} {R : «Σ».PrimitiveRelation}
  (c : R.BundleCoordinates)

theorem fiber_basis_ne_omitted {i : Fin n} (hi : i ∈ c.fiberIndices) :
    c.basis i ≠ c.omitted := by
  have h := c.fiber_ray_set ▸ Finset.mem_image.mpr ⟨i, hi, rfl⟩
  exact (Finset.mem_erase.mp h).1

theorem integer_weight_sum_split (f : Lattice n → ℤ) :
    (∑ v ∈ R.positive, f v) =
      (∑ i ∈ c.fiberIndices, f (c.basis i)) + f c.omitted := by
  rw [← Finset.sum_erase_add R.positive f c.omitted_mem,
    ← c.fiber_ray_set, Finset.sum_image]
  exact fun i _ j _ hij => c.basis.injective hij

def homogeneousIntegerExtension (k : ℤ) (a : Fin n → ℤ) (v : Lattice n) : ℤ :=
  if v = c.omitted then k - ∑ i ∈ c.fiberIndices, a i
  else ∑ i ∈ c.fiberIndices, if c.basis i = v then a i else 0

@[simp] theorem homogeneousIntegerExtension_omitted (k : ℤ) (a : Fin n → ℤ) :
    c.homogeneousIntegerExtension k a c.omitted = k - ∑ i ∈ c.fiberIndices, a i := by
  simp only [homogeneousIntegerExtension, if_pos rfl, ite_true]

theorem homogeneousIntegerExtension_basis (k : ℤ) (a : Fin n → ℤ)
    {i : Fin n} (hi : i ∈ c.fiberIndices) :
    c.homogeneousIntegerExtension k a (c.basis i) = a i := by
  rw [homogeneousIntegerExtension, if_neg (c.fiber_basis_ne_omitted hi)]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    exact if_neg (fun h => hji (c.basis.injective h))
  · exact fun h => (h hi).elim

theorem homogeneousIntegerExtension_total (k : ℤ) (a : Fin n → ℤ) :
    (∑ v ∈ R.positive, c.homogeneousIntegerExtension k a v) = k := by
  rw [c.integer_weight_sum_split, c.homogeneousIntegerExtension_omitted]
  have he : (∑ i ∈ c.fiberIndices, c.homogeneousIntegerExtension k a (c.basis i)) =
      ∑ i ∈ c.fiberIndices, a i :=
    Finset.sum_congr rfl (fun i hi => c.homogeneousIntegerExtension_basis k a hi)
  rw [he]
  ring

theorem homogeneousIntegerExtension_nonneg (k : ℤ) (a : Fin n → ℤ)
    (ha : ∀ i ∈ c.fiberIndices, 0 ≤ a i)
    (hsum : (∑ i ∈ c.fiberIndices, a i) ≤ k) :
    ∀ v ∈ R.positive, 0 ≤ c.homogeneousIntegerExtension k a v := by
  intro v hv
  by_cases he : v = c.omitted
  · rw [he, c.homogeneousIntegerExtension_omitted]
    exact sub_nonneg.mpr hsum
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp
      (c.fiber_ray_set.symm ▸ Finset.mem_erase.mpr ⟨he, hv⟩)
    rw [c.homogeneousIntegerExtension_basis k a hi]
    exact ha i hi

theorem homogeneousIntegerExtension_pos (k : ℤ) (a : Fin n → ℤ)
    (ha : ∀ i ∈ c.fiberIndices, 0 < a i)
    (hsum : (∑ i ∈ c.fiberIndices, a i) < k) :
    ∀ v ∈ R.positive, 0 < c.homogeneousIntegerExtension k a v := by
  intro v hv
  by_cases he : v = c.omitted
  · rw [he, c.homogeneousIntegerExtension_omitted]
    exact sub_pos.mpr hsum
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp
      (c.fiber_ray_set.symm ▸ Finset.mem_erase.mpr ⟨he, hv⟩)
    rw [c.homogeneousIntegerExtension_basis k a hi]
    exact ha i hi

theorem homogeneousIntegerExtension_sum (k l : ℤ) (a b : Fin n → ℤ)
    (γ : Lattice n → ℤ) (hγ : (∑ v ∈ R.positive, γ v) = k + l)
    (hab : ∀ i ∈ c.fiberIndices, a i + b i = γ (c.basis i)) :
    ∀ v ∈ R.positive,
      c.homogeneousIntegerExtension k a v + c.homogeneousIntegerExtension l b v = γ v := by
  intro v hv
  by_cases he : v = c.omitted
  · subst v
    rw [c.homogeneousIntegerExtension_omitted, c.homogeneousIntegerExtension_omitted]
    have hs : (∑ i ∈ c.fiberIndices, a i) + (∑ i ∈ c.fiberIndices, b i) =
        ∑ i ∈ c.fiberIndices, γ (c.basis i) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl hab
    rw [c.integer_weight_sum_split] at hγ
    linarith
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp
      (c.fiber_ray_set.symm ▸ Finset.mem_erase.mpr ⟨he, hv⟩)
    rw [c.homogeneousIntegerExtension_basis k a hi,
      c.homogeneousIntegerExtension_basis l b hi]
    exact hab i hi

/-- Full integral fiber allocation with unrestricted prescribed parity on
the independent lattice fiber coordinates. -/
theorem homogeneous_parity_allocation {k l : ℕ}
    (hk : c.fiberIndices.card ≤ k) (hl : c.fiberIndices.card ≤ l)
    (γ p : Lattice n → ℤ)
    (hγ : (∑ v ∈ R.positive, γ v) = (k + l : ℕ))
    (hγpos : ∀ v ∈ R.positive, 0 < γ v) :
    ∃ α β : Lattice n → ℤ,
      (∑ v ∈ R.positive, α v) = k ∧ (∑ v ∈ R.positive, β v) = l ∧
      (∀ v ∈ R.positive, 0 ≤ α v) ∧ (∀ v ∈ R.positive, 0 ≤ β v) ∧
      (∀ v ∈ R.positive, α v + β v = γ v) ∧
      (∀ i ∈ c.fiberIndices, (α (c.basis i) - p (c.basis i)) % 2 = 0) := by
  have hpos (i : Fin n) (hi : i ∈ c.fiberIndices) : 0 < γ (c.basis i) :=
    hγpos _ (c.fiber_subset_positive (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
  have hsum : (∑ i ∈ c.fiberIndices, γ (c.basis i)) < (k + l : ℕ) := by
    rw [c.integer_weight_sum_split] at hγ
    have hp := hγpos c.omitted c.omitted_mem
    linarith
  obtain ⟨a, b, ha0, ha, hb0, hb, hab, hpar⟩ := finset_simplex_parity_integer
    c.fiberIndices hk hl (fun i => γ (c.basis i)) (fun i => p (c.basis i)) hpos hsum
  refine ⟨c.homogeneousIntegerExtension k a, c.homogeneousIntegerExtension l b,
    c.homogeneousIntegerExtension_total _ _, c.homogeneousIntegerExtension_total _ _,
    c.homogeneousIntegerExtension_nonneg _ _ ha0 ha,
    c.homogeneousIntegerExtension_nonneg _ _ hb0 hb,
    c.homogeneousIntegerExtension_sum _ _ a b γ (by simpa using hγ) hab, ?_⟩
  intro i hi
  rw [c.homogeneousIntegerExtension_basis _ a hi]
  exact hpar i hi

theorem homogeneous_adjoint_allocation {k l : ℕ}
    (hl : c.fiberIndices.card + 1 ≤ l) (γ : Lattice n → ℤ)
    (hγ : (∑ v ∈ R.positive, γ v) = (k + l : ℕ))
    (hγpos : ∀ v ∈ R.positive, 0 < γ v) :
    ∃ α β : Lattice n → ℤ,
      (∑ v ∈ R.positive, α v) = k ∧ (∑ v ∈ R.positive, β v) = l ∧
      (∀ v ∈ R.positive, 0 ≤ α v) ∧ (∀ v ∈ R.positive, 0 < β v) ∧
      (∀ v ∈ R.positive, α v + β v = γ v) := by
  have hpos (i : Fin n) (hi : i ∈ c.fiberIndices) : 0 < γ (c.basis i) :=
    hγpos _ (c.fiber_subset_positive (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
  have hsum : (∑ i ∈ c.fiberIndices, γ (c.basis i)) < (k + l : ℕ) := by
    rw [c.integer_weight_sum_split] at hγ
    have hp := hγpos c.omitted c.omitted_mem
    linarith
  obtain ⟨a, b, ha0, ha, hbpos, hb, hab⟩ := finset_simplex_adjoint_integer
    c.fiberIndices hl (fun i => γ (c.basis i)) hpos hsum
  exact ⟨c.homogeneousIntegerExtension k a, c.homogeneousIntegerExtension l b,
    c.homogeneousIntegerExtension_total _ _, c.homogeneousIntegerExtension_total _ _,
    c.homogeneousIntegerExtension_nonneg _ _ ha0 ha,
    c.homogeneousIntegerExtension_pos _ _ hbpos hb,
    c.homogeneousIntegerExtension_sum _ _ a b γ (by simpa using hγ) hab⟩

end SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

end PaperVerification.ToricGeometry
end
end Source_ToricBundleFanAllocation
-- END ORIGINAL PaperVerification.ToricBundleFanAllocation


-- BEGIN ORIGINAL PaperVerification.ToricBundleFanReconstruction
section Source_ToricBundleFanReconstruction

-- original header: module

-- original header: public import PaperVerification.ToricBundleFanAllocation
-- original header: public import PaperVerification.ToricBundleFanAverages
-- original header: public import PaperVerification.ToricAdjointSupport


-- original header: @[expose] public section
/-!
# Interior, addition, and parity in the actual bundle lattice

The homogeneous slice coordinates describe the ambient topological interior,
the ordinary integer lattice addition, and the doubled integer lattice.
These are reconstruction theorems, not extra structure imposed on a bundle.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

open Set
open scoped BigOperators Classical
open PaperVerification.ToricExchange

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} {R : «Σ».PrimitiveRelation}
  (c : R.BundleCoordinates)

theorem point_mem_interior_fanPolytope_iff (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a α : Lattice n → ℝ)
    (hα : (∑ v ∈ R.positive, α v) = ∑ v ∈ R.positive, a v)
    (y : Ambient (n - c.fiberIndices.card)) :
    c.point a α y ∈ interior («Σ».fanPolytope a) ↔
      (∀ v ∈ R.positive, 0 < α v) ∧
        y ∈ interior (c.baseFan.fanPolytope (c.baseWeight hR hN a α)) := by
  rw [«Σ».interior_fanPolytope_eq, c.baseFan.interior_fanPolytope_eq]
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · intro v hv
      have h := hx v (R.primitive.1 hv)
      rw [c.point_pairing_positive hN a α hα y hv] at h
      linarith
    · intro q hq
      have hv := c.baseRayLift_mem hR hN hq
      have h := hx (c.baseRayLift hR hN q) (Finset.mem_sdiff.mp hv).1
      have he := c.nonfiber_slack_identity hR hN a α y hv
      rw [c.quotient_baseRayLift hR hN hq] at he
      linarith
  · rintro ⟨hα0, hy⟩ v hv
    by_cases hvP : v ∈ R.positive
    · rw [c.point_pairing_positive hN a α hα y hvP]
      linarith [hα0 v hvP]
    · have hv' := Finset.mem_sdiff.mpr ⟨hv, hvP⟩
      have hq := (c.base_ray_iff hR hN _).mpr ⟨v, hv', rfl⟩
      have h := hy (c.quotientLattice v) hq
      have he := c.nonfiber_slack_identity hR hN a α y hv'
      linarith

def integerHomogeneousWeight (c : R.BundleCoordinates) (a : Lattice n → ℤ) (x v : Lattice n) : ℤ :=
  a v + ∑ i, v i * x i

theorem integerHomogeneousWeight_cast (a : Lattice n → ℤ) (x v : Lattice n) :
    (c.integerHomogeneousWeight a x v : ℝ) =
      c.homogeneousWeight (fun u => (a u : ℝ)) (embed n x) v := by
  rw [homogeneousWeight, SmoothCompleteFan.normalRay_pairing_lattice]
  simp only [integerHomogeneousWeight, Int.cast_add]

theorem integerHomogeneousWeight_total (hN : R.negative = ∅)
    (a : Lattice n → ℤ) (x : Lattice n) :
    (∑ v ∈ R.positive, c.integerHomogeneousWeight a x v) =
      ∑ v ∈ R.positive, a v := by
  have h := c.homogeneousWeight_total hN (fun v => (a v : ℝ)) (embed n x)
  simp only [← c.integerHomogeneousWeight_cast] at h
  exact_mod_cast h

theorem integerHomogeneousWeight_pos_of_interior (a : Lattice n → ℤ)
    (x : Lattice n) (hx : embed n x ∈ interior («Σ».fanPolytope (fun v => (a v : ℝ))))
    {v : Lattice n} (hv : v ∈ «Σ».rays) :
    0 < c.integerHomogeneousWeight a x v := by
  have h := («Σ».interior_fanPolytope_eq (fun u => (a u : ℝ)) ▸ hx) v hv
  have hpos : (0 : ℝ) < c.integerHomogeneousWeight a x v := by
    rw [c.integerHomogeneousWeight_cast, homogeneousWeight]
    linarith
  exact_mod_cast hpos

theorem fiberIndices_card_le : c.fiberIndices.card ≤ n := by
  simpa only [Fintype.card_fin] using Finset.card_le_univ c.fiberIndices

theorem baseDimension_lt : n - c.fiberIndices.card < n := by
  have hpos : 0 < c.fiberIndices.card := by
    rw [c.fiberIndices_card]
    exact R.fiberDimension_pos
  have hle := c.fiberIndices_card_le
  omega

theorem integerPoint_homogeneousWeight_basePoint (a : Lattice n → ℤ) (x : Lattice n) :
    c.integerPoint a (c.integerHomogeneousWeight a x) (c.integerBasePoint x) = x := by
  apply embed_injective n
  rw [c.integerPoint_compatible, c.integerBasePoint_compatible]
  have he : (fun v => (c.integerHomogeneousWeight a x v : ℝ)) =
      c.homogeneousWeight (fun v => (a v : ℝ)) (embed n x) := by
    funext v
    exact c.integerHomogeneousWeight_cast a x v
  rw [he]
  exact c.point_homogeneousWeight_basePoint _ _

theorem integerPoint_congr_weights (a α β : Lattice n → ℤ)
    (h : ∀ i ∈ c.fiberIndices, α (c.basis i) = β (c.basis i))
    (y : Lattice (n - c.fiberIndices.card)) :
    c.integerPoint a α y = c.integerPoint a β y := by
  unfold integerPoint integerPointFunctional
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i hi]

theorem integerPoint_add (a b α β : Lattice n → ℤ)
    (y z : Lattice (n - c.fiberIndices.card)) :
    c.integerPoint (a + b) (α + β) (y + z) =
      c.integerPoint a α y + c.integerPoint b β z := by
  funext j
  simp only [integerPoint, integerDualVector, integerPointFunctional,
    LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, Pi.add_apply, smul_eq_mul, map_add]
  have he (i : Fin n) :
      (α (c.basis i) + β (c.basis i) - (a (c.basis i) + b (c.basis i))) *
          c.basis.coord i (Pi.basisFun ℤ (Fin n) j) =
      (α (c.basis i) - a (c.basis i)) * c.basis.coord i (Pi.basisFun ℤ (Fin n) j) +
      (β (c.basis i) - b (c.basis i)) * c.basis.coord i (Pi.basisFun ℤ (Fin n) j) := by ring
  simp only [he, Finset.sum_add_distrib]
  ring

theorem integerPoint_sub (a b α β : Lattice n → ℤ)
    (y z : Lattice (n - c.fiberIndices.card)) :
    c.integerPoint (a - b) (α - β) (y - z) =
      c.integerPoint a α y - c.integerPoint b β z := by
  have h := c.integerPoint_add (a - b) b (α - β) β (y - z) z
  simp only [sub_add_cancel] at h
  exact eq_sub_iff_add_eq.mpr h.symm

theorem integerBasePoint_add (x y : Lattice n) :
    c.integerBasePoint (x + y) = c.integerBasePoint x + c.integerBasePoint y := by
  funext j
  simp [integerBasePoint, integerDualVector, map_add]

theorem integerBasePoint_integerPoint (a α : Lattice n → ℤ)
    (y : Lattice (n - c.fiberIndices.card)) :
    c.integerBasePoint (c.integerPoint a α y) = y := by
  apply embed_injective (n - c.fiberIndices.card)
  rw [c.integerBasePoint_compatible, c.integerPoint_compatible, c.basePoint_point]

/-- Prescribed parity on the independent integral fiber coordinates,
together with the ordinary base parity class, is exactly sufficient for
the full ambient doubled-lattice condition. -/
theorem integerPoint_sameParity (a α : Lattice n → ℤ) (x : Lattice n)
    (y : Lattice (n - c.fiberIndices.card))
    (hfiber : ∀ i ∈ c.fiberIndices,
      (α (c.basis i) - c.integerHomogeneousWeight a x (c.basis i)) % 2 = 0)
    (hbase : SameParity y (c.integerBasePoint x)) :
    SameParity (c.integerPoint a α y) x := by
  let p := c.integerHomogeneousWeight a x
  let δ : Lattice n → ℤ := fun v => (α v - p v) / 2
  obtain ⟨z, hz⟩ := hbase
  refine ⟨c.integerPoint 0 δ z, ?_⟩
  have hf (i : Fin n) (hi : i ∈ c.fiberIndices) :
      (α - p) (c.basis i) = (δ + δ) (c.basis i) := by
    have h := hfiber i hi
    change α (c.basis i) - p (c.basis i) = δ (c.basis i) + δ (c.basis i)
    dsimp [δ, p] at *
    omega
  calc
    c.integerPoint a α y - x =
        c.integerPoint a α y - c.integerPoint a p (c.integerBasePoint x) := by
      rw [c.integerPoint_homogeneousWeight_basePoint]
    _ = c.integerPoint 0 (α - p) (y - c.integerBasePoint x) := by
      rw [← c.integerPoint_sub, sub_self]
    _ = c.integerPoint 0 (δ + δ) (z + z) := by
      rw [hz]
      exact c.integerPoint_congr_weights 0 (α - p) (δ + δ) hf _
    _ = c.integerPoint 0 δ z + c.integerPoint 0 δ z := by
      simpa only [zero_add] using c.integerPoint_add 0 0 δ δ z z

theorem integerPoint_sum_eq (a b α β : Lattice n → ℤ)
    (m : Lattice n) (y z : Lattice (n - c.fiberIndices.card))
    (hweights : ∀ v ∈ R.positive,
      α v + β v = c.integerHomogeneousWeight (a + b) m v)
    (hbase : y + z = c.integerBasePoint m) :
    c.integerPoint a α y + c.integerPoint b β z = m := by
  rw [← c.integerPoint_add, hbase]
  calc
    c.integerPoint (a + b) (α + β) (c.integerBasePoint m) =
        c.integerPoint (a + b) (c.integerHomogeneousWeight (a + b) m)
          (c.integerBasePoint m) := by
      apply c.integerPoint_congr_weights
      intro i hi
      exact hweights _ (c.fiber_subset_positive (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
    _ = m := c.integerPoint_homogeneousWeight_basePoint _ _

theorem basePoint_mem_interior_sum_support (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a b α β : Lattice n → ℝ) (x : Ambient n)
    (hx : x ∈ interior («Σ».fanPolytope (a + b)))
    (hweights : ∀ v ∈ R.positive,
      α v + β v = c.homogeneousWeight (a + b) x v) :
    c.basePoint x ∈ interior (c.baseFan.fanPolytope
      (c.baseWeight hR hN a α + c.baseWeight hR hN b β)) := by
  have hx' : c.point (a + b) (c.homogeneousWeight (a + b) x) (c.basePoint x) ∈
      interior («Σ».fanPolytope (a + b)) := by
    rw [c.point_homogeneousWeight_basePoint]
    exact hx
  have hbase := ((c.point_mem_interior_fanPolytope_iff hR hN (a + b)
    (c.homogeneousWeight (a + b) x) (c.homogeneousWeight_total hN _ _) _).mp hx').2
  have he := c.baseWeight_congr_weight hR hN (a + b) (α + β)
    (c.homogeneousWeight (a + b) x) hweights
  rw [← he, c.baseWeight_add] at hbase
  exact hbase

theorem integerPoint_mem_fanPolytope_iff (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a α : Lattice n → ℤ)
    (hα : (∑ v ∈ R.positive, α v) = ∑ v ∈ R.positive, a v)
    (y : Lattice (n - c.fiberIndices.card)) :
    embed n (c.integerPoint a α y) ∈ «Σ».fanPolytope (fun v => (a v : ℝ)) ↔
      (∀ v ∈ R.positive, 0 ≤ α v) ∧
        embed (n - c.fiberIndices.card) y ∈ c.baseFan.fanPolytope
          (fun q => (c.integerBaseWeight hR hN a α q : ℝ)) := by
  have hαR : (∑ v ∈ R.positive, (α v : ℝ)) = ∑ v ∈ R.positive, (a v : ℝ) := by
    exact_mod_cast hα
  rw [c.integerPoint_compatible, c.point_mem_fanPolytope_iff hR hN _ _ hαR]
  have he : (fun q => (c.integerBaseWeight hR hN a α q : ℝ)) =
      c.baseWeight hR hN (fun v => (a v : ℝ)) (fun v => (α v : ℝ)) := by
    funext q
    exact c.integerBaseWeight_cast hR hN a α q
  rw [he]
  constructor
  · rintro ⟨hα0, hy⟩
    refine ⟨?_, hy⟩
    intro v hv
    have h := hα0 v hv
    change (0 : ℝ) ≤ (α v : ℝ) at h
    exact_mod_cast h
  · rintro ⟨hα0, hy⟩
    refine ⟨?_, hy⟩
    intro v hv
    change (0 : ℝ) ≤ (α v : ℝ)
    exact_mod_cast hα0 v hv

theorem integerPoint_mem_interior_fanPolytope_iff (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a α : Lattice n → ℤ)
    (hα : (∑ v ∈ R.positive, α v) = ∑ v ∈ R.positive, a v)
    (y : Lattice (n - c.fiberIndices.card)) :
    embed n (c.integerPoint a α y) ∈ interior («Σ».fanPolytope (fun v => (a v : ℝ))) ↔
      (∀ v ∈ R.positive, 0 < α v) ∧
        embed (n - c.fiberIndices.card) y ∈ interior (c.baseFan.fanPolytope
          (fun q => (c.integerBaseWeight hR hN a α q : ℝ))) := by
  have hαR : (∑ v ∈ R.positive, (α v : ℝ)) = ∑ v ∈ R.positive, (a v : ℝ) := by
    exact_mod_cast hα
  rw [c.integerPoint_compatible, c.point_mem_interior_fanPolytope_iff hR hN _ _ hαR]
  have he : (fun q => (c.integerBaseWeight hR hN a α q : ℝ)) =
      c.baseWeight hR hN (fun v => (a v : ℝ)) (fun v => (α v : ℝ)) := by
    funext q
    exact c.integerBaseWeight_cast hR hN a α q
  rw [he]
  simp only [Int.cast_pos]

theorem integerBasePoint_mem_interior_sum_support (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a b α β : Lattice n → ℤ) (m : Lattice n)
    (hm : embed n m ∈ interior («Σ».fanPolytope (fun v => ((a + b) v : ℝ))))
    (hweights : ∀ v ∈ R.positive,
      α v + β v = c.integerHomogeneousWeight (a + b) m v) :
    embed (n - c.fiberIndices.card) (c.integerBasePoint m) ∈
      interior (c.baseFan.fanPolytope
        ((fun q => (c.integerBaseWeight hR hN a α q : ℝ)) +
          (fun q => (c.integerBaseWeight hR hN b β q : ℝ)))) := by
  rw [c.integerBasePoint_compatible]
  have hsum : (fun v => ((a + b) v : ℝ)) =
      (fun v => (a v : ℝ)) + (fun v => (b v : ℝ)) := by
    funext v
    simp
  rw [hsum] at hm
  have hw (v : Lattice n) (hv : v ∈ R.positive) :
      (α v : ℝ) + (β v : ℝ) =
        c.homogeneousWeight ((fun u => (a u : ℝ)) + (fun u => (b u : ℝ)))
          (embed n m) v := by
    rw [← hsum, ← c.integerHomogeneousWeight_cast]
    exact_mod_cast hweights v hv
  have h := c.basePoint_mem_interior_sum_support hR hN
    (fun v => (a v : ℝ)) (fun v => (b v : ℝ))
    (fun v => (α v : ℝ)) (fun v => (β v : ℝ)) (embed n m) hm hw
  have hA : (fun q => (c.integerBaseWeight hR hN a α q : ℝ)) =
      c.baseWeight hR hN (fun v => (a v : ℝ)) (fun v => (α v : ℝ)) := by
    funext q
    exact c.integerBaseWeight_cast hR hN a α q
  have hB : (fun q => (c.integerBaseWeight hR hN b β q : ℝ)) =
      c.baseWeight hR hN (fun v => (b v : ℝ)) (fun v => (β v : ℝ)) := by
    funext q
    exact c.integerBaseWeight_cast hR hN b β q
  simpa only [hA, hB] using h

end PaperVerification.ToricGeometry.SmoothCompleteFan.PrimitiveRelation.BundleCoordinates
end
end Source_ToricBundleFanReconstruction
-- END ORIGINAL PaperVerification.ToricBundleFanReconstruction


-- BEGIN ORIGINAL PaperVerification.ToricFiniteConeFamily
section Source_ToricFiniteConeFamily

-- original header: module
-- original header: public import PaperVerification.ToricFanConstruction
-- original header: @[expose] public section
/-!
# A finite smooth cone cover and all its faces

The generating cones need not be full dimensional. Each is assumed only to
have a genuine integral-basis ray set; coverage and the actual intersection
identity then propagate to all their subsets.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

def finiteConeFamilyClosure {n : ℕ} (C : Finset (Finset (Lattice n))) :
    Finset (Finset (Lattice n)) := C.biUnion Finset.powerset

theorem mem_finiteConeFamilyClosure {n : ℕ} (C : Finset (Finset (Lattice n)))
    (s : Finset (Lattice n)) :
    s ∈ finiteConeFamilyClosure C ↔ ∃ u ∈ C, s ⊆ u := by
  simp [finiteConeFamilyClosure]

/-- Closing a finite smooth cone cover under ray subsets produces an actual
smooth complete fan if the original cone intersections are the common-ray
cones. None of these geometric properties is discarded in the closure. -/
def fanOfFiniteSmoothCones {n : ℕ} (C : Finset (Finset (Lattice n)))
    (hsmooth : ∀ s ∈ C, ∃ b : Module.Basis (Fin n) ℤ (Lattice n),
      s ⊆ Finset.univ.image b)
    (hinter : ∀ s ∈ C, ∀ t ∈ C,
      latticeRayCone s ⊓ latticeRayCone t = latticeRayCone (s ∩ t))
    (hcover : ∀ x : Ambient n, ∃ s ∈ C, x ∈ latticeRayCone s) :
    SmoothCompleteFan n where
  cones := finiteConeFamilyClosure C
  smooth := by
    intro s hs
    obtain ⟨u, hu, hsu⟩ := (mem_finiteConeFamilyClosure C s).mp hs
    obtain ⟨b, hb⟩ := hsmooth u hu
    exact ⟨b, basisRayIndices b s, (image_basisRayIndices b s (hsu.trans hb)).symm⟩
  downward := by
    intro s hs t hts
    obtain ⟨u, hu, hsu⟩ := (mem_finiteConeFamilyClosure C s).mp hs
    exact (mem_finiteConeFamilyClosure C t).mpr ⟨u, hu, hts.trans hsu⟩
  intersection := by
    intro s hs t ht
    obtain ⟨u, hu, hsu⟩ := (mem_finiteConeFamilyClosure C s).mp hs
    obtain ⟨v, hv, htv⟩ := (mem_finiteConeFamilyClosure C t).mp ht
    obtain ⟨bu, hbu⟩ := hsmooth u hu
    obtain ⟨bv, hbv⟩ := hsmooth v hv
    have hsets : (s ∩ (u ∩ v)) ∩ t = s ∩ t := by
      ext w
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨⟨hws, hwu, hwv⟩, hwt⟩
        exact ⟨hws, hwt⟩
      · rintro ⟨hws, hwt⟩
        exact ⟨⟨hws, hsu hws, htv hwt⟩, hwt⟩
    ext x
    constructor
    · rintro ⟨hxs, hxt⟩
      have hxuv : x ∈ latticeRayCone (u ∩ v) := by
        rw [← hinter u hu v hv]
        exact ⟨latticeRayCone_mono hsu hxs, latticeRayCone_mono htv hxt⟩
      have hxmid : x ∈ latticeRayCone (s ∩ (u ∩ v)) := by
        rw [← latticeRayCone_inter_of_subsets_basis bu s (u ∩ v)
          (hsu.trans hbu) (Finset.inter_subset_left.trans hbu)]
        exact ⟨hxs, hxuv⟩
      have hmidv : s ∩ (u ∩ v) ⊆ v :=
        Finset.inter_subset_right.trans Finset.inter_subset_right
      have hxfin : x ∈ latticeRayCone ((s ∩ (u ∩ v)) ∩ t) := by
        rw [← latticeRayCone_inter_of_subsets_basis bv (s ∩ (u ∩ v)) t
          (hmidv.trans hbv) (htv.trans hbv)]
        exact ⟨hxmid, hxt⟩
      simpa only [hsets] using hxfin
    · intro hx
      exact ⟨latticeRayCone_mono Finset.inter_subset_left hx,
        latticeRayCone_mono Finset.inter_subset_right hx⟩
  complete := by
    intro x
    obtain ⟨s, hs, hx⟩ := hcover x
    exact ⟨s, (mem_finiteConeFamilyClosure C s).mpr ⟨s, hs, Finset.Subset.refl _⟩, hx⟩

end PaperVerification.ToricGeometry
end
end Source_ToricFiniteConeFamily
-- END ORIGINAL PaperVerification.ToricFiniteConeFamily


-- BEGIN ORIGINAL PaperVerification.ToricStarConeCovering
section Source_ToricStarConeCovering

-- original header: module
-- original header: public import PaperVerification.ToricFanFoundations
-- original header: public import Mathlib.Data.Finset.Max
-- original header: public import Mathlib.Tactic.Abel
-- original header: public import Mathlib.Tactic.Linarith
-- original header: @[expose] public section
/-!
# The actual support of a finite star subdivision

These lemmas work with ordinary finite nonnegative spans. In particular, the
new ray is the actual sum of the old focus rays, and preservation of support
is proved by subtracting a minimum coefficient.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Intersecting a finitely generated subcone with an actual face keeps
exactly the generators belonging to that face. -/
theorem finiteRayCone_inf_face (C F : PointedCone ℝ E) (hF : F.IsFaceOf C)
    (s : Finset E) (hs : ∀ v ∈ s, v ∈ C) :
    finiteRayCone s ⊓ F = finiteRayCone (s.filter (fun v => v ∈ F)) := by
  apply le_antisymm
  · rintro x ⟨⟨c, hc, hsum⟩, hxF⟩
    have hzero (v : E) (hv : v ∈ s) (hvF : v ∉ F) : c v = 0 := by
      by_contra hne
      have hpos : 0 < c v := lt_of_le_of_ne (hc v hv) (Ne.symm hne)
      apply hvF
      apply hF.mem_of_smul_add_mem (hs v hv)
        (Submodule.sum_mem _ (fun w hw => PointedCone.smul_mem _
          (hc w (Finset.mem_of_mem_erase hw)) (hs w (Finset.mem_of_mem_erase hw)))) hpos
      rw [Finset.add_sum_erase s (fun w => c w • w) hv, hsum]
      exact hxF
    refine ⟨c, fun v hv => hc v ((Finset.mem_filter.mp hv).1), ?_⟩
    calc
      (∑ v ∈ s.filter (fun v => v ∈ F), c v • v) = ∑ v ∈ s, c v • v := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro v hv hvfilter
        have hvF : v ∉ F := fun h => hvfilter (Finset.mem_filter.mpr ⟨hv, h⟩)
        rw [hzero v hv hvF, zero_smul]
      _ = x := hsum
  · rintro x ⟨c, hc, hsum⟩
    refine ⟨finiteRayCone_mono (Finset.filter_subset _ _) ⟨c, hc, hsum⟩, ?_⟩
    rw [← hsum]
    exact Submodule.sum_mem _ (fun v hv =>
      PointedCone.smul_mem _ (hc v hv) (Finset.mem_filter.mp hv).2)

/-- The actual ray set of one cone in the star subdivision of `s` along
the nonempty subset `t`, omitting the selected old ray `v`. -/
def starRaySet (s t : Finset E) (v : E) : Finset E :=
  insert (∑ w ∈ t, w) (s.erase v)

omit [Module ℝ E] in
/-- Membership in the actual star ray set, independent of the implementation
of decidable equality used by its finite-set operations. -/
theorem mem_starRaySet (s t : Finset E) (v w : E) :
    w ∈ starRaySet s t v ↔ w = (∑ z ∈ t, z) ∨ (w ≠ v ∧ w ∈ s) := by
  simp only [starRaySet, Finset.mem_insert, Finset.mem_erase]

/-- Every new cone is contained in its old parent cone. -/
theorem finiteRayCone_starRaySet_le {s t : Finset E} (hts : t ⊆ s) (v : E) :
    finiteRayCone (starRaySet s t v) ≤ finiteRayCone s := by
  rw [finiteRayCone_eq_hull]
  apply Submodule.span_le.mpr
  intro w hw
  rcases Finset.mem_insert.mp hw with rfl | hw
  · exact Submodule.sum_mem _ (fun w hw => finiteRayCone_generator s (hts hw))
  · exact finiteRayCone_generator s (Finset.mem_of_mem_erase hw)

/-- A cone is covered by the actual cones obtained by replacing one focus
ray with the sum of all focus rays. No smoothness or linear independence is
needed for this support assertion. -/
theorem finiteRayCone_star_cover {s t : Finset E} (hts : t ⊆ s)
    (ht : t.Nonempty) {x : E} (hx : x ∈ finiteRayCone s) :
    ∃ v ∈ t, x ∈ finiteRayCone (starRaySet s t v) := by
  obtain ⟨c, hc, hsum⟩ := hx
  obtain ⟨v, hv, hmin⟩ := t.exists_min_image c ht
  have hvs : v ∈ s := hts hv
  let d : E → ℝ := fun w => c w - if w ∈ t then c v else 0
  have hd (w : E) (hw : w ∈ s) : 0 ≤ d w := by
    by_cases hwt : w ∈ t
    · simp only [d, if_pos hwt]
      exact sub_nonneg.mpr (hmin w hwt)
    · simp only [d, if_neg hwt, sub_zero]
      exact hc w hw
  have hdv : d v = 0 := by simp [d, hv]
  have hcond : (∑ w ∈ s, (if w ∈ t then c v else 0) • w) =
      c v • ∑ w ∈ t, w := by
    calc
      (∑ w ∈ s, (if w ∈ t then c v else 0) • w) =
          ∑ w ∈ t, (if w ∈ t then c v else 0) • w := by
        symm
        apply Finset.sum_subset hts
        intro w _ hw
        simp only [if_neg hw, zero_smul]
      _ = ∑ w ∈ t, c v • w := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [if_pos hw]
      _ = c v • ∑ w ∈ t, w := Finset.smul_sum.symm
  have hfull : (∑ w ∈ s, d w • w) = x - c v • ∑ w ∈ t, w := by
    simp only [d, sub_smul, Finset.sum_sub_distrib, hcond, hsum]
  have herase : (∑ w ∈ s.erase v, d w • w) = x - c v • ∑ w ∈ t, w := by
    rw [← Finset.sum_erase_add s (fun w => d w • w) hvs, hdv, zero_smul,
      add_zero] at hfull
    exact hfull
  refine ⟨v, hv, ?_⟩
  have hfirst : c v • (∑ w ∈ t, w) ∈ finiteRayCone (starRaySet s t v) :=
    PointedCone.smul_mem _ (hc v hvs)
      (finiteRayCone_generator _ (Finset.mem_insert_self _ _))
  have hsecond : (∑ w ∈ s.erase v, d w • w) ∈
      finiteRayCone (starRaySet s t v) := by
    apply Submodule.sum_mem
    intro w hw
    exact PointedCone.smul_mem _ (hd w (Finset.mem_of_mem_erase hw))
      (finiteRayCone_generator _ (Finset.mem_insert_of_mem hw))
  have hnew := (finiteRayCone (starRaySet s t v)).add_mem hfirst hsecond
  rw [herase] at hnew
  have hcancel : c v • (∑ w ∈ t, w) +
      (x - c v • (∑ w ∈ t, w)) = x := by abel
  rw [hcancel] at hnew
  exact hnew

/-- Equality of the old cone with the finite union of the new actual cones. -/
theorem finiteRayCone_eq_union_star {s t : Finset E} (hts : t ⊆ s)
    (ht : t.Nonempty) :
    (finiteRayCone s : Set E) =
      {x | ∃ v ∈ t, x ∈ finiteRayCone (starRaySet s t v)} := by
  ext x
  constructor
  · exact finiteRayCone_star_cover hts ht
  · rintro ⟨v, hv, hx⟩
    exact finiteRayCone_starRaySet_le hts v hx

end PaperVerification.ToricGeometry
end
end Source_ToricStarConeCovering
-- END ORIGINAL PaperVerification.ToricStarConeCovering


-- BEGIN ORIGINAL PaperVerification.ToricStarConeIntersections
section Source_ToricStarConeIntersections

-- original header: module
-- original header: public import PaperVerification.ToricStarDualBasis
-- original header: public import PaperVerification.ToricStarConeCovering
-- original header: @[expose] public section
/-!
# Actual intersections of the cones in a smooth star chart

The intersection of two newly subdivided cones is proved to be their
common-ray cone. The key equality is that both chosen pivot coordinates
must be minima, hence equal; the corresponding new coefficient vanishes.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

section RaySets

variable {R E ι : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    [Fintype ι] [DecidableEq ι]

/-- The actual inserted-sum ray set is exactly the indicated subset of the
unimodular replacement basis. -/
theorem starRaySet_basis (b : Module.Basis ι R E)
    (I J : Finset ι) (hJI : J ⊆ I) (j : ι) (hj : j ∈ J) :
    starRaySet (I.image b) (J.image b) (b j) = I.image (starRayBasis b J j) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · letI := hR
    letI : Subsingleton E := Module.subsingleton R E
    ext x
    constructor
    · intro _
      exact Finset.mem_image.mpr ⟨j, hJI hj, Subsingleton.elim _ _⟩
    · intro _
      exact (mem_starRaySet _ _ _ _).mpr (Or.inl (Subsingleton.elim _ _))
  · letI := hR
    have hjI : j ∈ I := hJI hj
    have hsum : (∑ v ∈ J.image b, v) = ∑ i ∈ J, b i := by
      rw [Finset.sum_image]
      exact fun i _ k _ hik => b.injective hik
    have hrest : (I.erase j).image (starRayBasis b J j) = (I.erase j).image b := by
      apply Finset.image_congr
      intro i hi
      exact starRayBasis_other b J j i (Finset.mem_erase.mp hi).1
    calc
      starRaySet (I.image b) (J.image b) (b j) =
          insert (∑ i ∈ J, b i) ((I.erase j).image b) := by
        rw [starRaySet, hsum, ← Finset.image_erase b.injective]
      _ = insert (starRayBasis b J j j) ((I.erase j).image (starRayBasis b J j)) := by
        rw [starRayBasis_pivot b J j hj, hrest]
      _ = I.image (starRayBasis b J j) := by
        rw [← Finset.image_insert, Finset.insert_erase hjI]

end RaySets

section OneBasis

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    [Fintype ι] [DecidableEq ι]

/-- Two charts of a subdivision of one smooth cone meet in exactly the cone
on their common rays. This uses the actual sheared bases, not an asserted
fan-intersection property. -/
theorem starRayBasis_cone_inter (b : Module.Basis ι ℝ E)
    (I J : Finset ι) (hJI : J ⊆ I) (p q : ι) (hp : p ∈ J) (hq : q ∈ J) :
    finiteRayCone (I.image (starRayBasis b J p)) ⊓
        finiteRayCone (I.image (starRayBasis b J q)) =
      finiteRayCone ((I.image (starRayBasis b J p)) ∩
        (I.image (starRayBasis b J q))) := by
  by_cases hpq : p = q
  · subst q
    simp
  let bp := starRayBasis b J p
  let bq := starRayBasis b J q
  have hpI : p ∈ I := hJI hp
  have hqI : q ∈ I := hJI hq
  have hF : (I.erase q).image bp ⊆ (I.image bp) ∩ (I.image bq) := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    have hiI := Finset.mem_of_mem_erase hi
    have hiq := (Finset.mem_erase.mp hi).1
    refine Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨i, hiI, rfl⟩, ?_⟩
    by_cases hip : i = p
    · subst i
      refine Finset.mem_image.mpr ⟨q, hqI, ?_⟩
      exact (starRayBasis_pivot b J q hq).trans (starRayBasis_pivot b J p hp).symm
    · refine Finset.mem_image.mpr ⟨i, hiI, ?_⟩
      rw [starRayBasis_other b J q i hiq, starRayBasis_other b J p i hip]
  apply le_antisymm
  · intro x hx
    obtain ⟨hxpos, hxzero⟩ :=
      (mem_finiteRayCone_basis_iff bp I x).mp hx.1
    obtain ⟨hypos, hyzero⟩ :=
      (mem_finiteRayCone_basis_iff bq I x).mp hx.2
    have hqp : q ∈ J.erase p := Finset.mem_erase.mpr ⟨Ne.symm hpq, hq⟩
    have hpq' : p ∈ J.erase q := Finset.mem_erase.mpr ⟨hpq, hp⟩
    have hxq : 0 ≤ b.coord q x - b.coord p x := by
      have h := hxpos q
      change 0 ≤ bp.coord q x at h
      simpa only [bp, starRayBasis_coord, if_pos hqp] using h
    have hyp : 0 ≤ b.coord p x - b.coord q x := by
      have h := hypos p
      change 0 ≤ bq.coord p x at h
      simpa only [bq, starRayBasis_coord, if_pos hpq'] using h
    have hzeroq : bp.repr x q = 0 := by
      change bp.coord q x = 0
      rw [starRayBasis_coord, if_pos hqp]
      linarith
    apply finiteRayCone_mono hF
    apply (mem_finiteRayCone_basis_iff bp (I.erase q) x).mpr
    refine ⟨hxpos, ?_⟩
    intro i hi
    by_cases hiq : i = q
    · simpa only [hiq] using hzeroq
    · exact hxzero i (fun hiI => hi (Finset.mem_erase.mpr ⟨hiq, hiI⟩))
  · exact le_inf
      (finiteRayCone_mono Finset.inter_subset_left)
      (finiteRayCone_mono Finset.inter_subset_right)

/-- If an old coordinate face omits a focus direction, its intersection
with a new cone has no exceptional-ray coefficient. -/
theorem starRayBasis_cone_inter_old_face (b : Module.Basis ι ℝ E)
    (I J K : Finset ι) (hJI : J ⊆ I) (hKI : K ⊆ I)
    (p : ι) (hp : p ∈ J) (hJK : ¬ J ⊆ K) :
    finiteRayCone (I.image (starRayBasis b J p)) ⊓ finiteRayCone (K.image b) =
      finiteRayCone (((I.image (starRayBasis b J p))) ∩ (K.image b)) := by
  let bp := starRayBasis b J p
  have hF : (K.erase p).image b ⊆ (I.image bp) ∩ (K.image b) := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    have hiK := Finset.mem_of_mem_erase hi
    have hip := (Finset.mem_erase.mp hi).1
    refine Finset.mem_inter.mpr ⟨?_, Finset.mem_image.mpr ⟨i, hiK, rfl⟩⟩
    exact Finset.mem_image.mpr ⟨i, hKI hiK, starRayBasis_other b J p i hip⟩
  obtain ⟨q, hqJ, hqK⟩ := Finset.not_subset.mp hJK
  apply le_antisymm
  · intro x hx
    obtain ⟨hxpos, hxzero⟩ := (mem_finiteRayCone_basis_iff bp I x).mp hx.1
    obtain ⟨hypos, hyzero⟩ := (mem_finiteRayCone_basis_iff b K x).mp hx.2
    have hqzero : b.coord q x = 0 := hyzero q hqK
    have hpzero : b.coord p x = 0 := by
      by_cases hqp : q = p
      · simpa only [hqp] using hqzero
      · have hqerase : q ∈ J.erase p := Finset.mem_erase.mpr ⟨hqp, hqJ⟩
        have hqnonneg := hxpos q
        change 0 ≤ bp.coord q x at hqnonneg
        rw [starRayBasis_coord, if_pos hqerase, hqzero, zero_sub] at hqnonneg
        have hpnonneg := hypos p
        change 0 ≤ b.coord p x at hpnonneg
        linarith
    apply finiteRayCone_mono hF
    apply (mem_finiteRayCone_basis_iff b (K.erase p) x).mpr
    refine ⟨hypos, ?_⟩
    intro i hi
    by_cases hip : i = p
    · subst i
      change b.coord p x = 0
      exact hpzero
    · exact hyzero i (fun hiK => hi (Finset.mem_erase.mpr ⟨hip, hiK⟩))
  · exact le_inf
      (finiteRayCone_mono Finset.inter_subset_left)
      (finiteRayCone_mono Finset.inter_subset_right)

end OneBasis

end PaperVerification.ToricGeometry
end
end Source_ToricStarConeIntersections
-- END ORIGINAL PaperVerification.ToricStarConeIntersections


-- BEGIN ORIGINAL PaperVerification.ToricStarFanFaces
section Source_ToricStarFanFaces

-- original header: module
-- original header: public import PaperVerification.ToricStarConeIntersections
-- original header: public import PaperVerification.ToricFanConstruction
-- original header: @[expose] public section
/-!
# Restriction of star cones to old fan faces

All ray sets are finite subsets of the actual integer lattice. The exceptional
ray is their sum, and its incidence with an old face is proved from the fan's
actual geometric intersection property.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

theorem image_embed_basis {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) :
    (I.image b).image (embed n) = I.image (integralBasisReal b) := by
  rw [Finset.image_image]
  apply Finset.image_congr
  intro i hi
  exact (integralBasisReal_apply b i).symm

/-- The generic basis identity with finite images in the literal lattice. -/
theorem lattice_starRaySet_basis {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I J : Finset (Fin n)) (hJI : J ⊆ I) (j : Fin n) (hj : j ∈ J) :
    starRaySet (I.image b) (J.image b) (b j) = I.image (starRayBasis b J j) := by
  have hImage (f : Fin n → Lattice n) (K : Finset (Fin n)) :
      @Finset.image (Fin n) (Lattice n)
        (fun a b => Classical.propDecidable (a = b)) f K = K.image f := by
    ext x
    simp only [Finset.mem_image]
  have h := starRaySet_basis b I J hJI j hj
  rw [hImage b I, hImage b J, hImage (starRayBasis b J j) I] at h
  exact h

theorem embed_starRaySet {n : ℕ} (s t : Finset (Lattice n)) (v : Lattice n) :
    (starRaySet s t v).image (embed n) =
      starRaySet (s.image (embed n)) (t.image (embed n)) (embed n v) := by
  have hsum : embed n (∑ w ∈ t, w) = ∑ w ∈ t.image (embed n), w := by
    rw [map_sum, Finset.sum_image]
    exact fun a _ b _ hab => embed_injective n hab
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    apply (mem_starRaySet _ _ _ _).mpr
    rcases (mem_starRaySet _ _ _ _).mp hz with hsumz | ⟨hzv, hzs⟩
    · exact Or.inl (congrArg (embed n) hsumz |>.trans hsum)
    · exact Or.inr ⟨fun h => hzv (embed_injective n h),
        Finset.mem_image.mpr ⟨z, hzs, rfl⟩⟩
  · intro hx
    rcases (mem_starRaySet _ _ _ _).mp hx with hxsum | ⟨hxv, hxs⟩
    · refine Finset.mem_image.mpr ⟨∑ w ∈ t, w,
        (mem_starRaySet _ _ _ _).mpr (Or.inl rfl), ?_⟩
      exact hsum.trans hxsum.symm
    · obtain ⟨z, hzs, rfl⟩ := Finset.mem_image.mp hxs
      exact Finset.mem_image.mpr ⟨z,
        (mem_starRaySet _ _ _ _).mpr (Or.inr
          ⟨fun h => hxv (congrArg (embed n) h), hzs⟩), rfl⟩

theorem latticeRayCone_starRaySet_le {n : ℕ} {s t : Finset (Lattice n)}
    (hts : t ⊆ s) (v : Lattice n) :
    latticeRayCone (starRaySet s t v) ≤ latticeRayCone s := by
  unfold latticeRayCone
  rw [embed_starRaySet]
  exact finiteRayCone_starRaySet_le (Finset.image_subset_image hts) (embed n v)

theorem latticeRayCone_star_cover {n : ℕ} {s t : Finset (Lattice n)}
    (hts : t ⊆ s) (ht : t.Nonempty) {x : Ambient n} (hx : x ∈ latticeRayCone s) :
    ∃ v ∈ t, x ∈ latticeRayCone (starRaySet s t v) := by
  obtain ⟨v, hv, hxv⟩ := finiteRayCone_star_cover
    (Finset.image_subset_image hts) (ht.image (embed n)) hx
  obtain ⟨vZ, hvZ, rfl⟩ := Finset.mem_image.mp hv
  refine ⟨vZ, hvZ, ?_⟩
  unfold latticeRayCone
  rw [embed_starRaySet]
  exact hxv

theorem latticeRayCone_inf_face {n : ℕ} (C F : PointedCone ℝ (Ambient n))
    (hF : F.IsFaceOf C) (s : Finset (Lattice n))
    (hs : ∀ v ∈ s, embed n v ∈ C) :
    latticeRayCone s ⊓ F = latticeRayCone (s.filter (fun v => embed n v ∈ F)) := by
  unfold latticeRayCone
  rw [finiteRayCone_inf_face C F hF _ (by
    rintro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact hs v hv)]
  congr 1
  ext x
  constructor
  · intro hx
    obtain ⟨hx, hxF⟩ := Finset.mem_filter.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hxF⟩, rfl⟩
  · intro hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hv, hvF⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨v, hv, rfl⟩, hvF⟩

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- An actual subcone is a subset of the same integral basis as its parent. -/
theorem adapted_basis_for_subcone {s t : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (hts : t ⊆ s) :
    ∃ (b : Module.Basis (Fin n) ℤ (Lattice n)) (I J : Finset (Fin n)),
      s = I.image b ∧ t = J.image b ∧ J ⊆ I := by
  obtain ⟨b, I, rfl⟩ := «Σ».smooth s hs
  let J := I.filter (fun i => b i ∈ t)
  refine ⟨b, I, J, rfl, ?_, Finset.filter_subset _ _⟩
  ext v
  constructor
  · intro hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hts hv)
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hv⟩, rfl⟩
  · intro hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp hi).2

/-- Every new ray set is literally part of a genuine integral basis. -/
theorem starRaySet_smooth {s t : Finset (Lattice n)} (hs : s ∈ «Σ».cones)
    (hts : t ⊆ s) {v : Lattice n} (hv : v ∈ t) :
    ∃ (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)),
      starRaySet s t v = I.image b := by
  obtain ⟨b, I, J, hsI, htJ, hJI⟩ := «Σ».adapted_basis_for_subcone hs hts
  rw [htJ] at hv
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
  refine ⟨starRayBasis b J j, I, ?_⟩
  rw [hsI, htJ, lattice_starRaySet_basis b I J hJI j hj]

/-- The local star-chart intersection theorem transferred to actual integer
ray sets, with an integral basis adapted to the original cone. -/
theorem star_cones_same_parent_inter {s t : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (hts : t ⊆ s) {v w : Lattice n}
    (hv : v ∈ t) (hw : w ∈ t) :
    latticeRayCone (starRaySet s t v) ⊓ latticeRayCone (starRaySet s t w) =
      latticeRayCone (starRaySet s t v ∩ starRaySet s t w) := by
  obtain ⟨b, I, J, hsI, htJ, hJI⟩ := «Σ».adapted_basis_for_subcone hs hts
  rw [htJ] at hv hw
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hw
  rw [hsI, htJ, lattice_starRaySet_basis b I J hJI p hp,
    lattice_starRaySet_basis b I J hJI q hq]
  unfold latticeRayCone
  rw [Finset.image_inter _ _ (embed_injective n)]
  simp only [image_embed_basis, integralBasisReal_starRayBasis]
  have hImage (f : Fin n → Ambient n) (K : Finset (Fin n)) :
      @Finset.image (Fin n) (Ambient n)
        (fun a b => Classical.propDecidable (a = b)) f K = K.image f := by
    ext x
    simp only [Finset.mem_image]
  have hInter (S T : Finset (Ambient n)) :
      @Inter.inter (Finset (Ambient n))
        (@Finset.instInter (Ambient n) (fun a b => Classical.propDecidable (a = b))) S T =
          S ∩ T := by
    ext x
    simp only [Finset.mem_inter]
  have h := starRayBasis_cone_inter (integralBasisReal b) I J hJI p q hp hq
  rw [hImage (starRayBasis (integralBasisReal b) J p) I,
    hImage (starRayBasis (integralBasisReal b) J q) I, hInter] at h
  exact h

/-- The sum of all focus rays lies in an old cone exactly when that cone
contains every focus ray. -/
theorem sum_rays_mem_cone_iff {t u : Finset (Lattice n)}
    (ht : t ∈ «Σ».cones) (hu : u ∈ «Σ».cones) :
    embed n (∑ v ∈ t, v) ∈ latticeRayCone u ↔ t ⊆ u := by
  rw [map_sum]
  constructor
  · exact «Σ».sum_mem_cone_implies_subset ht hu
  · intro htu
    exact Submodule.sum_mem _ (fun v hv => latticeRayCone_generator u (htu hv))

/-- A focus of dimension at least two produces a new ray, distinct from
every original ray of the complete smooth fan. -/
theorem sum_rays_not_mem_rays {t : Finset (Lattice n)}
    (ht : t ∈ «Σ».cones) (hcard : 2 ≤ t.card) : (∑ v ∈ t, v) ∉ «Σ».rays := by
  intro hmem
  have hsingle := «Σ».singleton_mem_of_mem_rays hmem
  have hsub : t ⊆ {∑ v ∈ t, v} := («Σ».sum_rays_mem_cone_iff ht hsingle).mp
    (latticeRayCone_generator _ (Finset.mem_singleton_self _))
  have h := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at h
  omega

/-- Filtering one new ray set by incidence with an old face is explicit:
the exceptional ray survives precisely when the entire focus does. -/
theorem filter_starRaySet_by_face {s t u : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (ht : t ∈ «Σ».cones) (hu : u ∈ «Σ».cones)
    (hus : u ⊆ s) (v : Lattice n) :
    (starRaySet s t v).filter (fun w => embed n w ∈ latticeRayCone u) =
      if t ⊆ u then starRaySet u t v else u.erase v := by
  ext w
  have hcone (hws : w ∈ s) : embed n w ∈ latticeRayCone u ↔ w ∈ u := by
    exact «Σ».ray_mem_cone_iff hu ((«Σ».mem_rays_iff w).mpr ⟨s, hs, hws⟩)
  by_cases htu : t ⊆ u
  · simp only [Finset.mem_filter, mem_starRaySet, if_pos htu]
    constructor
    · rintro ⟨hstar, hwcone⟩
      rcases hstar with hsum | ⟨hwv, hws⟩
      · exact Or.inl hsum
      · exact Or.inr ⟨hwv, (hcone hws).mp hwcone⟩
    · intro hstar
      rcases hstar with hsum | ⟨hwv, hwu⟩
      · refine ⟨Or.inl hsum, ?_⟩
        rw [hsum]
        exact («Σ».sum_rays_mem_cone_iff ht hu).mpr htu
      · exact ⟨Or.inr ⟨hwv, hus hwu⟩, latticeRayCone_generator u hwu⟩
  · simp only [Finset.mem_filter, mem_starRaySet, if_neg htu, Finset.mem_erase]
    constructor
    · rintro ⟨hstar, hwcone⟩
      rcases hstar with hsum | ⟨hwv, hws⟩
      · rw [hsum] at hwcone
        exact False.elim (htu ((«Σ».sum_rays_mem_cone_iff ht hu).mp hwcone))
      · exact ⟨hwv, (hcone hws).mp hwcone⟩
    · rintro ⟨hwv, hwu⟩
      exact ⟨Or.inr ⟨hwv, hus hwu⟩, latticeRayCone_generator u hwu⟩

/-- Restriction of a new cone to an actual old face is either the
corresponding star cone in that face or its unchanged old rays. -/
theorem star_cone_inter_face {s t u : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (ht : t ∈ «Σ».cones) (hu : u ∈ «Σ».cones)
    (hts : t ⊆ s) (hus : u ⊆ s) (v : Lattice n) :
    latticeRayCone (starRaySet s t v) ⊓ latticeRayCone u =
      if t ⊆ u then latticeRayCone (starRaySet u t v) else latticeRayCone (u.erase v) := by
  rw [latticeRayCone_inf_face (latticeRayCone s) (latticeRayCone u)
    («Σ».cone_subset_isFaceOf hs hus) _ (by
      intro w hw
      exact latticeRayCone_starRaySet_le hts v (latticeRayCone_generator _ hw)),
    «Σ».filter_starRaySet_by_face hs ht hu hus v]
  split_ifs <;> rfl

/-- The same restriction formula against any old fan cone, using the
actual common face of its old parent. -/
theorem star_cone_inter_old_cone {s t u : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (ht : t ∈ «Σ».cones) (hu : u ∈ «Σ».cones)
    (hts : t ⊆ s) (v : Lattice n) :
    latticeRayCone (starRaySet s t v) ⊓ latticeRayCone u =
      if t ⊆ s ∩ u then latticeRayCone (starRaySet (s ∩ u) t v)
      else latticeRayCone ((s ∩ u).erase v) := by
  have hle := latticeRayCone_starRaySet_le hts v
  have heq : latticeRayCone (starRaySet s t v) ⊓ latticeRayCone u =
      latticeRayCone (starRaySet s t v) ⊓ latticeRayCone (s ∩ u) := by
    rw [← «Σ».intersection s hs u hu]
    ext x
    exact ⟨fun h => ⟨h.1, hle h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  rw [heq]
  exact «Σ».star_cone_inter_face hs ht
    («Σ».downward s hs _ Finset.inter_subset_left) hts Finset.inter_subset_left v

/-- A new cone and an unchanged old cone have precisely their common-ray
intersection. The focus is not contained in an unchanged old cone. -/
theorem star_cone_inter_unchanged {s t u : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (ht : t ∈ «Σ».cones) (hu : u ∈ «Σ».cones)
    (hts : t ⊆ s) (htu : ¬ t ⊆ u) (v : Lattice n) :
    latticeRayCone (starRaySet s t v) ⊓ latticeRayCone u =
      latticeRayCone (starRaySet s t v ∩ u) := by
  have hnot : ¬ t ⊆ s ∩ u := fun h => htu (h.trans Finset.inter_subset_right)
  rw [«Σ».star_cone_inter_old_cone hs ht hu hts v, if_neg hnot]
  have he : (∑ w ∈ t, w) ∉ u := by
    intro heu
    exact htu ((«Σ».sum_rays_mem_cone_iff ht hu).mp (latticeRayCone_generator u heu))
  congr 1
  ext z
  by_cases hze : z = ∑ w ∈ t, w
  · subst z
    simp [starRaySet, he]
  · simp [starRaySet, hze, Finset.mem_inter, Finset.mem_erase,
      and_assoc, and_left_comm, and_comm]

/-- New cones over any two old cones meet in their exact common-ray cone.
Restriction to the old common face reduces this to the same-parent theorem. -/
theorem star_cones_inter {s t u : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (ht : t ∈ «Σ».cones) (hu : u ∈ «Σ».cones)
    (hts : t ⊆ s) (htu : t ⊆ u) {v w : Lattice n}
    (hv : v ∈ t) (hw : w ∈ t) :
    latticeRayCone (starRaySet s t v) ⊓ latticeRayCone (starRaySet u t w) =
      latticeRayCone (starRaySet s t v ∩ starRaySet u t w) := by
  let F := s ∩ u
  have hF : F ∈ «Σ».cones := «Σ».downward s hs F Finset.inter_subset_left
  have htF : t ⊆ F := Finset.subset_inter hts htu
  have hleft := «Σ».star_cone_inter_face hs ht hF hts Finset.inter_subset_left v
  have hright := «Σ».star_cone_inter_face hu ht hF htu Finset.inter_subset_right w
  rw [if_pos htF] at hleft hright
  have hmeet : latticeRayCone (starRaySet s t v) ⊓ latticeRayCone (starRaySet u t w) =
      (latticeRayCone (starRaySet s t v) ⊓ latticeRayCone F) ⊓
      (latticeRayCone (starRaySet u t w) ⊓ latticeRayCone F) := by
    ext x
    constructor
    · intro hx
      have hxF : x ∈ latticeRayCone F := by
        rw [← «Σ».intersection s hs u hu]
        exact ⟨latticeRayCone_starRaySet_le hts v hx.1,
          latticeRayCone_starRaySet_le htu w hx.2⟩
      exact ⟨⟨hx.1, hxF⟩, ⟨hx.2, hxF⟩⟩
    · exact fun hx => ⟨hx.1.1, hx.2.1⟩
  rw [hmeet, hleft, hright, «Σ».star_cones_same_parent_inter hF htF hv hw]
  congr 1
  ext z
  by_cases hze : z = ∑ y ∈ t, y
  · subst z
    simp [starRaySet]
  · simp [starRaySet, hze, F, Finset.mem_inter, Finset.mem_erase,
      and_assoc, and_left_comm, and_comm]

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricStarFanFaces
-- END ORIGINAL PaperVerification.ToricStarFanFaces


-- BEGIN ORIGINAL PaperVerification.ToricStarSubdivision
section Source_ToricStarSubdivision

-- original header: module
-- original header: public import PaperVerification.ToricStarFanFaces
-- original header: public import PaperVerification.ToricFiniteConeFamily
-- original header: @[expose] public section
/-!
# Smooth star subdivision of an actual complete fan

The subdivision is constructed from actual finite ray sets and their actual
nonnegative spans. Smoothness follows from an integral transvection,
completeness from the minimum-coefficient covering, and the fan intersection
condition from the proved old-face restrictions and local chart calculation.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- The generating cones of the star subdivision: retain cones not containing
the focus and subdivide each remaining cone at every focus ray. -/
def starCandidates (t : Finset (Lattice n)) : Finset (Finset (Lattice n)) :=
  «Σ».cones.biUnion (fun s => if t ⊆ s then t.image (starRaySet s t) else {s})

theorem mem_starCandidates (t s : Finset (Lattice n)) :
    s ∈ «Σ».starCandidates t ↔
      (s ∈ «Σ».cones ∧ ¬ t ⊆ s) ∨
      ∃ u ∈ «Σ».cones, ∃ v ∈ t, t ⊆ u ∧ s = starRaySet u t v := by
  constructor
  · intro hs
    obtain ⟨u, hu, hsu⟩ := Finset.mem_biUnion.mp hs
    by_cases htu : t ⊆ u
    · rw [if_pos htu] at hsu
      obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hsu
      exact Or.inr ⟨u, hu, v, hv, htu, he.symm⟩
    · rw [if_neg htu] at hsu
      have hsu := Finset.mem_singleton.mp hsu
      subst s
      exact Or.inl ⟨hu, htu⟩
  · rintro (⟨hs, hts⟩ | ⟨u, hu, v, hv, htu, rfl⟩)
    · apply Finset.mem_biUnion.mpr
      exact ⟨s, hs, by rw [if_neg hts]; exact Finset.mem_singleton_self s⟩
    · apply Finset.mem_biUnion.mpr
      refine ⟨u, hu, ?_⟩
      rw [if_pos htu]
      exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

theorem starCandidates_smooth (t : Finset (Lattice n)) :
    ∀ s ∈ «Σ».starCandidates t, ∃ b : Module.Basis (Fin n) ℤ (Lattice n),
      s ⊆ Finset.univ.image b := by
  intro s hs
  rcases («Σ».mem_starCandidates t s).mp hs with ⟨hs, hts⟩ |
    ⟨u, hu, v, hv, htu, rfl⟩
  · obtain ⟨b, I, rfl⟩ := «Σ».smooth s hs
    exact ⟨b, Finset.image_subset_image (Finset.subset_univ I)⟩
  · obtain ⟨b, I, he⟩ := «Σ».starRaySet_smooth hu htu hv
    refine ⟨b, ?_⟩
    rw [he]
    exact Finset.image_subset_image (Finset.subset_univ I)

theorem starCandidates_intersection (t : Finset (Lattice n)) (ht : t ∈ «Σ».cones) :
    ∀ s ∈ «Σ».starCandidates t, ∀ u ∈ «Σ».starCandidates t,
      latticeRayCone s ⊓ latticeRayCone u = latticeRayCone (s ∩ u) := by
  intro s hs u hu
  rcases («Σ».mem_starCandidates t s).mp hs with ⟨hs, hts⟩ |
    ⟨s', hs', v, hv, hts', rfl⟩
  · rcases («Σ».mem_starCandidates t u).mp hu with ⟨hu, htu⟩ |
      ⟨u', hu', w, hw, htu', rfl⟩
    · exact «Σ».intersection s hs u hu
    · rw [inf_comm, Finset.inter_comm]
      exact «Σ».star_cone_inter_unchanged hu' ht hs htu' hts w
  · rcases («Σ».mem_starCandidates t u).mp hu with ⟨hu, htu⟩ |
      ⟨u', hu', w, hw, htu', rfl⟩
    · exact «Σ».star_cone_inter_unchanged hs' ht hu hts' htu v
    · exact «Σ».star_cones_inter hs' ht hu' hts' htu' hv hw

theorem starCandidates_cover (t : Finset (Lattice n)) (ht : t.Nonempty) :
    ∀ x : Ambient n, ∃ s ∈ «Σ».starCandidates t, x ∈ latticeRayCone s := by
  intro x
  obtain ⟨s, hs, hx⟩ := «Σ».complete x
  by_cases hts : t ⊆ s
  · obtain ⟨v, hv, hxv⟩ := latticeRayCone_star_cover hts ht hx
    refine ⟨starRaySet s t v, ?_, hxv⟩
    exact («Σ».mem_starCandidates t _).mpr (Or.inr ⟨s, hs, v, hv, hts, rfl⟩)
  · exact ⟨s, («Σ».mem_starCandidates t s).mpr (Or.inl ⟨hs, hts⟩), hx⟩

/-- The smooth complete star-subdivided fan, with every defining geometric
property proved from the original fan and the nonempty focus cone. -/
def starSubdivision (t : Finset (Lattice n)) (ht : t ∈ «Σ».cones) (hne : t.Nonempty) :
    SmoothCompleteFan n :=
  fanOfFiniteSmoothCones («Σ».starCandidates t)
    («Σ».starCandidates_smooth t) («Σ».starCandidates_intersection t ht)
    («Σ».starCandidates_cover t hne)

/-- An unchanged old cone is literally a cone of the new fan. -/
theorem mem_starSubdivision_of_unchanged (t : Finset (Lattice n))
    (ht : t ∈ «Σ».cones) (hne : t.Nonempty) {s : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (hts : ¬ t ⊆ s) :
    s ∈ («Σ».starSubdivision t ht hne).cones := by
  apply (mem_finiteConeFamilyClosure («Σ».starCandidates t) s).mpr
  exact ⟨s, («Σ».mem_starCandidates t s).mpr (Or.inl ⟨hs, hts⟩), Finset.Subset.refl s⟩

/-- Every explicitly subdivided cone is literally a cone of the new fan. -/
theorem starRaySet_mem_starSubdivision (t : Finset (Lattice n))
    (ht : t ∈ «Σ».cones) (hne : t.Nonempty) {s : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (hts : t ⊆ s) {v : Lattice n} (hv : v ∈ t) :
    starRaySet s t v ∈ («Σ».starSubdivision t ht hne).cones := by
  apply (mem_finiteConeFamilyClosure («Σ».starCandidates t) _).mpr
  exact ⟨starRaySet s t v,
    («Σ».mem_starCandidates t _).mpr (Or.inr ⟨s, hs, v, hv, hts, rfl⟩),
    Finset.Subset.refl _⟩

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricStarSubdivision
-- END ORIGINAL PaperVerification.ToricStarSubdivision


-- BEGIN ORIGINAL PaperVerification.ToricStarPurity
section Source_ToricStarPurity

-- original header: module

-- original header: public import PaperVerification.ToricStarSubdivision

-- original header: @[expose] public section

/-!
# Full cone extensions survive star subdivision

Purity is derived from the original fan's full-cone extensions and the
explicit ray-set replacement. No general purity theorem is assumed.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

theorem starRaySet_mono {n : ℕ} {s u : Finset (Lattice n)}
    (hsu : s ⊆ u) (t : Finset (Lattice n)) (p : Lattice n) :
    starRaySet s t p ⊆ starRaySet u t p := by
  intro v hv
  apply (mem_starRaySet _ _ _ _).mpr
  rcases (mem_starRaySet _ _ _ _).mp hv with hsum | ⟨hvp, hvs⟩
  · exact Or.inl hsum
  · exact Or.inr ⟨hvp, hsu hvs⟩

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem starRaySet_card {s t : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (hts : t ⊆ s) {p : Lattice n} (hp : p ∈ t) :
    (starRaySet s t p).card = s.card := by
  obtain ⟨b, I, J, hsI, htJ, hJI⟩ := «Σ».adapted_basis_for_subcone hs hts
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (htJ ▸ hp)
  rw [hsI, htJ, lattice_starRaySet_basis b I J hJI j hj,
    Finset.card_image_of_injective I (starRayBasis b J j).injective,
    Finset.card_image_of_injective I b.injective]

/-- Every cone of the actual subdivided fan extends to a full cone whenever
that property holds for the original fan. -/
theorem isPure_starSubdivision (hpure : «Σ».IsPure)
    (t : Finset (Lattice n)) (ht : t ∈ «Σ».cones) (hne : t.Nonempty) :
    («Σ».starSubdivision t ht hne).IsPure := by
  intro c hc
  obtain ⟨u, hu, hcu⟩ := (mem_finiteConeFamilyClosure («Σ».starCandidates t) c).mp hc
  rcases («Σ».mem_starCandidates t u).mp hu with ⟨hu, htu⟩ |
    ⟨u', hu', p, hp, htu', rfl⟩
  · obtain ⟨s, hs, hus, hscard⟩ := hpure u hu
    by_cases hts : t ⊆ s
    · obtain ⟨p, hp, hpu⟩ := Finset.not_subset.mp htu
      refine ⟨starRaySet s t p,
        «Σ».starRaySet_mem_starSubdivision t ht hne hs hts hp, ?_, ?_⟩
      · intro v hv
        exact (mem_starRaySet _ _ _ _).mpr (Or.inr
          ⟨fun hvp => hpu (hvp ▸ hcu hv), hus (hcu hv)⟩)
      · rw [«Σ».starRaySet_card hs hts hp, hscard]
    · exact ⟨s, «Σ».mem_starSubdivision_of_unchanged t ht hne hs hts, hcu.trans hus, hscard⟩
  · obtain ⟨s, hs, hus, hscard⟩ := hpure u' hu'
    have hts := htu'.trans hus
    exact ⟨starRaySet s t p,
      «Σ».starRaySet_mem_starSubdivision t ht hne hs hts hp,
      hcu.trans (starRaySet_mono hus t p),
      («Σ».starRaySet_card hs hts hp).trans hscard⟩

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricStarPurity
-- END ORIGINAL PaperVerification.ToricStarPurity


-- BEGIN ORIGINAL PaperVerification.ToricWallUniqueness
section Source_ToricWallUniqueness

-- original header: module

-- original header: public import PaperVerification.ToricContractionCones
-- original header: public import PaperVerification.ToricStarPurity
-- original header: public import Mathlib.Tactic.Abel
-- original header: public import Mathlib.Tactic.NormNum

-- original header: @[expose] public section

/-!
# Uniqueness of the opposite smooth cone at a wall

Two prospective opposite rays with the same negative normal coordinate
produce a common point by adding nonnegative wall coordinates. The fan's
actual common-ray intersection forces the rays to coincide.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- An integral wall in a genuine basis has at most one adjacent fan ray
whose missing coordinate is strictly negative. The two coefficients are
scaled to the same height before applying the genuine fan intersection. -/
theorem opposite_wall_ray_unique_of_negative (b : Module.Basis (Fin n) ℤ (Lattice n))
    (j : Fin n) (w z : Lattice n)
    (hw : insert w ((Finset.univ.erase j).image b) ∈ «Σ».cones)
    (hz : insert z ((Finset.univ.erase j).image b) ∈ «Σ».cones)
    (hjw : b.repr w j < 0) (hjz : b.repr z j < 0) : w = z := by
  let W := (Finset.univ.erase j).image b
  let B := integralBasisReal b
  let α : ℝ := -(b.repr z j : ℝ)
  let β : ℝ := -(b.repr w j : ℝ)
  have hα : 0 < α := neg_pos.mpr (by exact_mod_cast hjz)
  have hβ : 0 < β := neg_pos.mpr (by exact_mod_cast hjw)
  let d : Fin n → ℝ := fun i => B.repr (β • embed n z - α • embed n w) i
  let u : Fin n → ℝ := fun i => |d i| + d i
  let v : Fin n → ℝ := fun i => |d i|
  have hdj : d j = 0 := by
    simp only [d, B, map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply,
      integralBasisReal_repr, smul_eq_mul, α, β]
    ring
  have hu (i : Fin n) : 0 ≤ u i := by
    have h := neg_abs_le (d i)
    dsimp only [u]
    linarith
  have hv (i : Fin n) : 0 ≤ v i := abs_nonneg _
  have huj : u j = 0 := by simp [u, hdj]
  have hvj : v j = 0 := by simp [v, hdj]
  have hwall (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (haj : a j = 0)
      (y : Lattice n) : (∑ i, a i • B i) ∈ latticeRayCone (insert y W) := by
    apply Submodule.sum_mem
    intro i hi
    by_cases hij : i = j
    · subst i
      simp only [haj, zero_smul]
      exact Submodule.zero_mem _
    · rw [integralBasisReal_apply]
      apply PointedCone.smul_mem _ (ha i)
      apply latticeRayCone_generator
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨i, Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩, rfl⟩)
  have hsum : (∑ i, u i • B i) =
      (∑ i, v i • B i) + (β • embed n z - α • embed n w) := by
    simp only [u, add_smul, Finset.sum_add_distrib, v, d, Module.Basis.sum_repr]
  have hbalance : α • embed n w + (∑ i, u i • B i) =
      β • embed n z + (∑ i, v i • B i) := by
    rw [hsum]
    abel
  have hxw : α • embed n w + (∑ i, u i • B i) ∈ latticeRayCone (insert w W) :=
    (latticeRayCone (insert w W)).add_mem
      (PointedCone.smul_mem _ hα.le (latticeRayCone_generator _ (Finset.mem_insert_self _ _)))
      (hwall u hu huj w)
  have hxz : α • embed n w + (∑ i, u i • B i) ∈ latticeRayCone (insert z W) := by
    rw [hbalance]
    exact (latticeRayCone (insert z W)).add_mem
      (PointedCone.smul_mem _ hβ.le (latticeRayCone_generator _ (Finset.mem_insert_self _ _)))
      (hwall v hv hvj z)
  have hxmeet : α • embed n w + (∑ i, u i • B i) ∈
      latticeRayCone ((insert w W) ∩ (insert z W)) := by
    rw [← «Σ».intersection _ hw _ hz]
    exact ⟨hxw, hxz⟩
  have hface := «Σ».cone_subset_isFaceOf hw
    (Finset.inter_subset_left : insert w W ∩ insert z W ⊆ insert w W)
  have hwmeet : embed n w ∈ latticeRayCone ((insert w W) ∩ (insert z W)) :=
    hface.mem_of_smul_add_mem
      (latticeRayCone_generator _ (Finset.mem_insert_self _ _)) (hwall u hu huj w) hα hxmeet
  have hwrays : w ∈ «Σ».rays := («Σ».mem_rays_iff w).mpr
    ⟨insert w W, hw, Finset.mem_insert_self _ _⟩
  have hwz : w ∈ insert z W := («Σ».ray_mem_cone_iff hz hwrays).mp
    (latticeRayCone_mono Finset.inter_subset_right hwmeet)
  rcases Finset.mem_insert.mp hwz with hwz | hwW
  · exact hwz
  · obtain ⟨i, hi, hwi⟩ := Finset.mem_image.mp hwW
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    rw [← hwi] at hjw
    simp only [Module.Basis.repr_self_apply, if_neg hij] at hjw
    norm_num at hjw

/-- The normalized smooth-wall form used by primitive contraction relations. -/
theorem opposite_wall_ray_unique (b : Module.Basis (Fin n) ℤ (Lattice n))
    (j : Fin n) (w z : Lattice n)
    (hw : insert w ((Finset.univ.erase j).image b) ∈ «Σ».cones)
    (hz : insert z ((Finset.univ.erase j).image b) ∈ «Σ».cones)
    (hjw : b.repr w j = -1) (hjz : b.repr z j = -1) : w = z :=
  «Σ».opposite_wall_ray_unique_of_negative b j w z hw hz (by omega) (by omega)

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricWallUniqueness
-- END ORIGINAL PaperVerification.ToricWallUniqueness


-- BEGIN ORIGINAL PaperVerification.ToricContractibleWalls
section Source_ToricContractibleWalls

-- original header: module

-- original header: public import PaperVerification.ToricWallUniqueness

-- original header: @[expose] public section

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
end
end Source_ToricContractibleWalls
-- END ORIGINAL PaperVerification.ToricContractibleWalls


-- BEGIN ORIGINAL PaperVerification.ToricNormalBasisEdges
section Source_ToricNormalBasisEdges

-- original header: module

-- original header: public import PaperVerification.ToricPolytopeSupport
-- original header: public import PaperVerification.ToricStarDualBasis

-- original header: @[expose] public section

/-!
# Actual primitive edges dual to a full normal-cone basis

Equality of actual integral basis cones gives a permutation, with no
rescaling. Its dual identifies every basis direction with a genuine edge
of the smooth polytope.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

theorem integral_bases_perm_of_equal_ray_cones {n : ℕ}
    (b c : Module.Basis (Fin n) ℤ (Lattice n))
    (hcone : latticeRayCone (Finset.univ.image b) = latticeRayCone (Finset.univ.image c)) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, b i = c (σ i) := by
  have hcoords (b c : Module.Basis (Fin n) ℤ (Lattice n))
      (hcone : latticeRayCone (Finset.univ.image b) = latticeRayCone (Finset.univ.image c)) :
      ∀ i j, 0 ≤ b.repr (c j) i := by
    intro i j
    have hc : embed n (c j) ∈ latticeRayCone (Finset.univ.image b) := by
      rw [hcone]
      exact latticeRayCone_generator _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
    have hi := ((mem_latticeRayCone_basis_iff b Finset.univ _).mp hc).1 i
    rw [integralBasisReal_repr] at hi
    exact_mod_cast hi
  exact integral_bases_perm_of_nonnegative_coordinates b c (hcoords b c hcone)
    (hcoords c b hcone.symm)

theorem integralDualBasis_of_permuted_normals {n : ℕ}
    (d c : Module.Basis (Fin n) ℤ (Lattice n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i, d i = integralDualBasis c (σ i)) :
    ∀ i, integralDualBasis d i = c (σ i) := by
  intro i
  apply (integralDualBasis d).ext_elem
  intro j
  rw [Module.Basis.repr_self_apply, integralDualBasis_repr, hσ j]
  have h := integralDualBasis_pairing c (σ j) (c (σ i))
  have hpair : (∑ k, c (σ i) k * integralDualBasis c (σ j) k) =
      if i = j then (1 : ℤ) else 0 := by
    simpa only [Module.Basis.repr_self_apply, σ.injective.eq_iff, mul_comm] using h
  exact hpair.symm

/-- A smooth cone containing a complete basis cone has the full ambient
number of rays. This is proved by coordinates, without a purity assumption. -/
theorem SmoothCompleteFan.card_eq_dim_of_basis_cone_le {n : ℕ}
    («Σ» : SmoothCompleteFan n) {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones)
    (d : Module.Basis (Fin n) ℤ (Lattice n))
    (hle : latticeRayCone (Finset.univ.image d) ≤ latticeRayCone s) :
    s.card = n := by
  obtain ⟨b, I, rfl⟩ := «Σ».smooth s hs
  have hI : I = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    by_contra hi
    have hz (k : Fin n) :
        (integralBasisReal b).repr (integralBasisReal d k) i = 0 := by
      have hk := hle (latticeRayCone_generator (Finset.univ.image d)
        (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩))
      have hzero := ((mem_latticeRayCone_basis_iff b I _).mp hk).2 i hi
      simpa only [integralBasisReal_apply] using hzero
    have he := congrArg (fun x => (integralBasisReal b).repr x i)
      ((integralBasisReal d).sum_repr (integralBasisReal b i))
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      hz, smul_eq_mul, mul_zero, Finset.sum_const_zero,
      Module.Basis.repr_self_apply, if_pos rfl] at he
    norm_num at he
  rw [hI, Finset.card_image_of_injective _ b.injective, Finset.card_fin]

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

/-- A full actual integral normal basis supplies the literal primitive
edge basis at its vertex, including all positive integer edge lengths. -/
theorem full_normal_basis_edges (hP : P.Smooth)
    (v : Ambient n) (hv : v ∈ P.carrier)
    (d : Module.Basis (Fin n) ℤ (Lattice n))
    (hcone : P.normalCone v =
      (latticeRayCone (Finset.univ.image d) : Set (Ambient n))) :
    ∃ (vZ : Lattice n) (lengths : Fin n → ℕ), embed n vZ = v ∧
      ∀ i, 0 < lengths i ∧ P.IsEdge (embed n vZ)
        (embed n (vZ + (lengths i : ℤ) • integralDualBasis d i)) := by
  let b := integralDualBasis d
  have horthant : ∀ x ∈ P.carrier, ∀ i,
      0 ≤ (integralBasisReal b).repr (x - v) i := by
    intro x hx i
    have hi : embed n (d i) ∈ P.normalCone v := by
      rw [hcone]
      exact latticeRayCone_generator _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    have h := hi x hx
    rw [integralDualBasis_real_repr]
    simpa only [integralBasisReal_apply, Pi.sub_apply, mul_comm] using h
  have hvertex := P.extreme_of_supporting_basis v hv (integralBasisReal b) horthant
  obtain ⟨vZ, c, lengths, hvZ, hedges, hcoord⟩ := P.smooth_vertex_basis_cone hP v hvertex
  have hedges' : ∀ i, 0 < lengths i ∧ P.IsEdge (embed n vZ)
      (embed n (vZ + (lengths i : ℤ) • c i)) := by
    simpa only [hvZ] using hedges
  have hcoord' : ∀ x ∈ P.carrier, ∀ i,
      0 ≤ (integralBasisReal c).repr (x - embed n vZ) i := by
    simpa only [hvZ] using hcoord
  have hconeC : P.normalCone v =
      (latticeRayCone (Finset.univ.image (integralDualBasis c)) : Set (Ambient n)) := by
    simpa only [hvZ] using P.normalCone_eq_latticeRayCone vZ c lengths hedges' hcoord'
  have heq : latticeRayCone (Finset.univ.image d) =
      latticeRayCone (Finset.univ.image (integralDualBasis c)) :=
    SetLike.coe_injective (hcone.symm.trans hconeC)
  obtain ⟨σ, hσ⟩ := integral_bases_perm_of_equal_ray_cones d (integralDualBasis c) heq
  have hb := integralDualBasis_of_permuted_normals d c σ hσ
  refine ⟨vZ, fun i => lengths (σ i), hvZ, ?_⟩
  intro i
  simpa only [hb i] using hedges' (σ i)

end LatticePolytope

end PaperVerification.ToricGeometry
end
end Source_ToricNormalBasisEdges
-- END ORIGINAL PaperVerification.ToricNormalBasisEdges


-- BEGIN ORIGINAL PaperVerification.ToricEdgeWallSupport
section Source_ToricEdgeWallSupport

-- original header: module

-- original header: public import PaperVerification.ToricNormalBasisEdges
-- original header: public import PaperVerification.ToricContractibleWalls
-- original header: public import Mathlib.Tactic.Abel

-- original header: @[expose] public section

/-!
# The genuine adjacent normal cone along a primitive edge

A supporting full normal basis determines the actual primitive edge basis.
At the other endpoint of one of those edges, all wall normals remain active.
The uniqueness of the opposite fan ray then identifies the remaining active
normal. This supplies the geometric part of the edge-length/degree identity.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

theorem pairing_integral_dual_basis {n : ℕ}
    (d : Module.Basis (Fin n) ℤ (Lattice n)) (u : Lattice n) (j : Fin n) :
    (dotProductEquiv ℝ (Fin n) (embed n u))
        (integralBasisReal (integralDualBasis d) j) = (d.repr u j : ℝ) := by
  have h := integralDualBasis_real_pairing d j (embed n u)
  rw [integralBasisReal_repr] at h
  rw [integralBasisReal_apply]
  change (∑ k, embed n u k * embed n (integralDualBasis d j) k) = (d.repr u j : ℝ)
  simpa only [integralBasisReal_apply, mul_comm] using h

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

/-- The negative-side wall ray in the actual normal fan supports the opposite
endpoint of the corresponding genuine basis edge. No wall/curve dictionary is
assumed in this statement. -/
theorem opposite_wall_normal_at_edge_endpoint
    (hP : P.Smooth) («Σ» : SmoothCompleteFan n)
    (hfan : «Σ».realCones = P.normalFan)
    (v : Lattice n) (d : Module.Basis (Fin n) ℤ (Lattice n))
    (hU : Finset.univ.image d ∈ «Σ».cones)
    (hcone : P.normalCone (embed n v) =
      (latticeRayCone (Finset.univ.image d) : Set (Ambient n)))
    (j : Fin n) (k : ℕ) (hk : 0 < k)
    (hedge : P.IsEdge (embed n v)
      (embed n (v + (k : ℤ) • integralDualBasis d j)))
    (e : Lattice n)
    (hecone : insert e ((Finset.univ.erase j).image d) ∈ «Σ».cones)
    (hecoord : d.repr e j < 0) :
    embed n e ∈ P.normalCone (embed n (v + (k : ℤ) • integralDualBasis d j)) := by
  let y := embed n (v + (k : ℤ) • integralDualBasis d j)
  let W := (Finset.univ.erase j).image d
  let f (u : Lattice n) : Ambient n →ₗ[ℝ] ℝ :=
    dotProductEquiv ℝ (Fin n) (embed n u)
  have hyvertex : y ∈ P.carrier.extremePoints ℝ := (P.edge_endpoints_extreme hedge).2
  have hv : embed n v ∈ P.carrier := (P.edge_endpoints_extreme hedge).1.1
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hdisp (u : Lattice n) :
      f u (y - embed n v) = (k : ℝ) * (d.repr u j : ℝ) := by
    rw [show y - embed n v = (k : ℝ) •
      integralBasisReal (integralDualBasis d) j by
        simp only [y, map_add, embed_int_smul, Int.cast_natCast,
          integralBasisReal_apply, add_sub_cancel_left]]
    rw [map_smul, smul_eq_mul]
    congr 1
    exact pairing_integral_dual_basis d u j
  have hnormalV : P.normalCone y ∈ «Σ».realCones := by
    rw [hfan]
    exact ⟨y, hyvertex.1, rfl⟩
  obtain ⟨V, hV, hVe⟩ := hnormalV
  obtain ⟨c, hc⟩ := P.smooth_vertex_normalCone_basis hP y hyvertex
  have hVcard : V.card = n := by
    apply «Σ».card_eq_dim_of_basis_cone_le hV c
    have he : latticeRayCone (Finset.univ.image c) = latticeRayCone V :=
      SetLike.coe_injective (hc.symm.trans hVe)
    exact he.le
  have hW : W ⊆ V := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    have hdiU : d i ∈ Finset.univ.image d :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have hdi : embed n (d i) ∈ P.normalCone (embed n v) := by
      rw [hcone]
      exact latticeRayCone_generator _ hdiU
    have hdiy : embed n (d i) ∈ P.normalCone y := by
      intro x hx
      change 0 ≤ f (d i) (x - y)
      rw [show x - y = (x - embed n v) - (y - embed n v) by abel, map_sub, hdisp]
      have hh := hdi x hx
      change 0 ≤ f (d i) (x - embed n v) at hh
      simpa only [Module.Basis.repr_self_apply, if_neg hij, Int.cast_zero,
        mul_zero, sub_zero] using hh
    apply («Σ».ray_mem_cone_iff hV («Σ».ray_mem_of_mem_cone hU hdiU)).mp
    change embed n (d i) ∈ (latticeRayCone V : Set (Ambient n))
    simpa only [hVe] using hdiy
  have hnonpos (u : Lattice n) (hu : u ∈ V) : d.repr u j ≤ 0 := by
    have hnormal : embed n u ∈ P.normalCone y := by
      rw [hVe]
      exact latticeRayCone_generator V hu
    have hh := hnormal (embed n v) hv
    change 0 ≤ f u (embed n v - y) at hh
    rw [show embed n v - y = -(y - embed n v) by abel, map_neg, hdisp] at hh
    have hR : (d.repr u j : ℝ) ≤ 0 := by nlinarith
    exact_mod_cast hR
  obtain ⟨cV, hcV⟩ := «Σ».full_cone_basis hV hVcard
  have hex : ∃ i : Fin n, d.repr (cV i) j ≠ 0 := by
    by_contra hn
    have hz : ∀ i : Fin n, d.repr (cV i) j = 0 := by simpa only [not_exists, not_not] using hn
    have hh := congrArg (fun x => d.repr x j) (cV.sum_repr (d j))
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      hz, smul_eq_mul, mul_zero, Finset.sum_const_zero,
      Module.Basis.repr_self_apply, if_pos rfl] at hh
    norm_num at hh
  obtain ⟨i, hi⟩ := hex
  let z := cV i
  have hzV : z ∈ V := hcV.symm ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hzneg : d.repr z j < 0 := lt_of_le_of_ne (hnonpos z hzV) hi
  have hzW : z ∉ W := by
    intro hz
    obtain ⟨i', hi', he⟩ := Finset.mem_image.mp hz
    have hi'j := (Finset.mem_erase.mp hi').1
    rw [← he, Module.Basis.repr_self_apply, if_neg hi'j] at hzneg
    omega
  have hsubset : insert z W ⊆ V := Finset.insert_subset hzV hW
  have hcard : (insert z W).card = n := by
    rw [Finset.card_insert_of_notMem hzW, Finset.card_image_of_injective _ d.injective,
      Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_fin]
    have hn := j.isLt
    omega
  have hzcone : insert z W ∈ «Σ».cones := by
    have he : insert z W = V := Finset.eq_of_subset_of_card_le hsubset (by omega)
    exact he.symm ▸ hV
  have hez : e = z := «Σ».opposite_wall_ray_unique_of_negative d j e z
    hecone hzcone hecoord hzneg
  rw [hez, hVe]
  exact latticeRayCone_generator V hzV

end LatticePolytope

end PaperVerification.ToricGeometry
end
end Source_ToricEdgeWallSupport
-- END ORIGINAL PaperVerification.ToricEdgeWallSupport


