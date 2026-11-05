module
public import PaperVerification.ToricCriterion
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Topology.Order.LeftRight
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
@[expose] public section
/-!
# Actual faces and the hypotheses of Proposition 2.1

This file derives the exchange criterion from statements about genuine convex faces,
relative interiors, and affine half-space descriptions. The face index used by the
exchange proof is computed from the active inequalities. Globally vanishing
inequalities are removed, so the construction also works for lower-dimensional sets.
-/

noncomputable section

namespace PaperVerification.ToricExchange

open Set Filter
open scoped Pointwise Topology

variable {M V ι : Type*} [AddCommGroup M]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Relative interior commutes with any nonzero real dilation. -/
theorem intrinsicInterior_smul (c : ℝ) (hc : c ≠ 0) (F : Set V) :
    intrinsicInterior ℝ (c • F) = c • intrinsicInterior ℝ F := by
  let e : V ≃ᵃ[ℝ] V := (LinearEquiv.smulOfNeZero ℝ V c hc).toAffineEquiv
  exact e.intrinsicInterior_image F

/-- A nonnegative affine functional vanishing at a relative-interior point
vanishes on the whole set. No continuity of the functional is required. -/
theorem affine_zero_on_of_intrinsicInterior (F : Set V) (f : V →ᵃ[ℝ] ℝ)
    (hnonneg : ∀ y ∈ F, 0 ≤ f y) {x : V}
    (hx : x ∈ intrinsicInterior ℝ F) (hfx : f x = 0) :
    ∀ y ∈ F, f y = 0 := by
  rcases mem_intrinsicInterior.mp hx with ⟨xA, hxA, rfl⟩
  letI : Nonempty (affineSpan ℝ F) := ⟨xA⟩
  intro y hy
  let yA : affineSpan ℝ F := ⟨y, subset_affineSpan ℝ F hy⟩
  have hline : Tendsto (AffineMap.lineMap xA yA : ℝ → affineSpan ℝ F)
      (𝓝 0) (𝓝 xA) := by
    simpa only [ContinuousAt, AffineMap.lineMap_apply_zero] using
      (AffineMap.lineMap_continuous (p := xA) (q := yA)).continuousAt (x := (0 : ℝ))
  have hevent : ∀ᶠ t : ℝ in 𝓝 0, (AffineMap.lineMap xA yA t : V) ∈ F :=
    hline.eventually (mem_interior_iff_mem_nhds.mp hxA)
  obtain ⟨t, ht, htF⟩ := hevent.exists_lt
  have hvalue : f (AffineMap.lineMap xA yA t : V) = t * f y := by
    change (f.comp (affineSpan ℝ F).subtype) (AffineMap.lineMap xA yA t) = _
    rw [AffineMap.apply_lineMap]
    simp [AffineMap.lineMap_apply_module, hfx, yA, smul_eq_mul]
  have hn := hnonneg _ htF
  rw [hvalue] at hn
  have hy0 := hnonneg y hy
  nlinarith

/-- An actual face containing a relative-interior point contains the entire
set whose relative interior is being taken. This proves the minimal-face property
without assuming a combinatorial face poset. -/
theorem subset_extreme_of_intrinsicInterior_mem {P F G : Set V}
    (hFP : F ⊆ P) (hG : IsExtreme ℝ P G) {x : V}
    (hxF : x ∈ intrinsicInterior ℝ F) (hxG : x ∈ G) : F ⊆ G := by
  rcases mem_intrinsicInterior.mp hxF with ⟨xA, hxA, rfl⟩
  letI : Nonempty (affineSpan ℝ F) := ⟨xA⟩
  intro y hy
  let yA : affineSpan ℝ F := ⟨y, subset_affineSpan ℝ F hy⟩
  have hline : Tendsto (AffineMap.lineMap xA yA : ℝ → affineSpan ℝ F)
      (𝓝 0) (𝓝 xA) := by
    simpa only [ContinuousAt, AffineMap.lineMap_apply_zero] using
      (AffineMap.lineMap_continuous (p := xA) (q := yA)).continuousAt (x := (0 : ℝ))
  have hevent : ∀ᶠ t : ℝ in 𝓝 0, (AffineMap.lineMap xA yA t : V) ∈ F :=
    hline.eventually (mem_interior_iff_mem_nhds.mp hxA)
  obtain ⟨t, ht, htF⟩ := hevent.exists_lt
  let z : V := (AffineMap.lineMap xA yA t : V)
  have hz : z = (1 - t) • (xA : V) + t • y := by
    change (affineSpan ℝ F).subtype (AffineMap.lineMap xA yA t) = _
    rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_module]
    rfl
  have hden : 0 < 1 - t := by linarith
  have hab : (-t / (1 - t)) + 1 / (1 - t) = 1 := by
    field_simp [ne_of_gt hden] <;> ring
  have hbx : (1 / (1 - t)) * (1 - t) = 1 := by field_simp [ne_of_gt hden]
  have hay : (-t / (1 - t)) + (1 / (1 - t)) * t = 0 := by ring
  have hxseg : (xA : V) ∈ openSegment ℝ y z := by
    refine ⟨-t / (1 - t), 1 / (1 - t), div_pos (neg_pos.mpr ht) hden,
      div_pos zero_lt_one hden, hab, ?_⟩
    calc
      (-t / (1 - t)) • y + (1 / (1 - t)) • z =
          ((1 / (1 - t)) * (1 - t)) • (xA : V) +
            ((-t / (1 - t)) + (1 / (1 - t)) * t) • y := by rw [hz]; module
      _ = (xA : V) := by rw [hbx, hay]; simp
  exact hG.left_mem_of_mem_openSegment (hFP hy) (hFP htF) hxG hxseg

/-- A finite affine half-space system. This is ordinary geometric input, not a
connectivity or decomposition assumption. -/
structure AffineInequalities (ι V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  slack : ι → V →ᵃ[ℝ] ℝ
  continuous_slack : ∀ i, Continuous (slack i)

namespace AffineInequalities

variable (H : AffineInequalities ι V)

/-- The actual intersection of the closed affine half-spaces. -/
def region : Set V := {x | ∀ i, 0 ≤ H.slack i x}

/-- The face obtained by making the listed inequalities equalities. -/
def face (J : Set ι) : Set V :=
  {x | x ∈ H.region ∧ ∀ i ∈ J, H.slack i x = 0}

/-- Inequalities that are not identically zero on the region. -/
def informative (i : ι) : Prop := ∃ y ∈ H.region, H.slack i y ≠ 0

/-- Active, informative inequalities. Constant zero constraints are discarded. -/
def active (x : V) : Set ι := {i | H.slack i x = 0 ∧ H.informative i}

/-- All constraints vanishing at both points, including constant constraints. -/
def jointZeros (a b : V) : Set ι := {i | H.slack i a = 0 ∧ H.slack i b = 0}

theorem convex_region : Convex ℝ H.region := by
  intro x hx y hy a b ha hb hab i
  rw [Convex.combo_affine_apply hab]
  exact add_nonneg (smul_nonneg ha (hx i)) (smul_nonneg hb (hy i))

theorem convex_face (J : Set ι) : Convex ℝ (H.face J) := by
  intro x hx y hy a b ha hb hab
  refine ⟨H.convex_region hx.1 hy.1 ha hb hab, ?_⟩
  intro i hi
  rw [Convex.combo_affine_apply hab, hx.2 i hi, hy.2 i hi]
  simp

theorem isExtreme_face (J : Set ι) : IsExtreme ℝ H.region (H.face J) := by
  refine ⟨fun _ hx => hx.1, ?_⟩
  rintro x hx y hy z hz ⟨a, b, ha, hb, hab, he⟩
  refine ⟨hx, ?_⟩
  intro i hi
  have hzero := hz.2 i hi
  rw [← he, Convex.combo_affine_apply hab] at hzero
  have hx0 := hx i
  have hy0 := hy i
  simp only [smul_eq_mul] at hzero
  nlinarith

theorem slack_eq_zero_on_affineSpan {J : Set ι} {i : ι} (hi : i ∈ J)
    {x : V} (hx : x ∈ affineSpan ℝ (H.face J)) : H.slack i x = 0 := by
  refine affineSpan_induction (p := fun y => H.slack i y = 0) hx ?_ ?_
  · intro y hy
    exact hy.2 i hi
  · intro c u v w hu hv hw
    rw [AffineMap.map_vadd, map_smul, AffineMap.linear_apply_vsub]
    simp [hu, hv, hw]

/-- Strictness of all unselected constraints is an explicit open neighborhood
inside the affine span of the face. -/
theorem mem_intrinsicInterior_face_of_strict [Finite ι] {J : Set ι} {x : V}
    (hx : x ∈ H.face J) (hstrict : ∀ i ∉ J, 0 < H.slack i x) :
    x ∈ intrinsicInterior ℝ (H.face J) := by
  let xA : affineSpan ℝ (H.face J) := ⟨x, subset_affineSpan ℝ (H.face J) hx⟩
  let U : Set (affineSpan ℝ (H.face J)) :=
    ⋂ i : {i : ι // i ∉ J}, {y | 0 < H.slack i.1 (y : V)}
  have hU : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt continuous_const ((H.continuous_slack i.1).comp continuous_subtype_val)
  have hxU : xA ∈ U := by
    exact mem_iInter.mpr fun i => hstrict i.1 i.2
  have hUF : U ⊆ ((↑) ⁻¹' H.face J : Set (affineSpan ℝ (H.face J))) := by
    intro y hy
    refine ⟨?_, ?_⟩
    · intro i
      by_cases hi : i ∈ J
      · exact le_of_eq (H.slack_eq_zero_on_affineSpan hi y.property).symm
      · exact le_of_lt (mem_iInter.mp hy ⟨i, hi⟩)
    · intro i hi
      exact H.slack_eq_zero_on_affineSpan hi y.property
  refine mem_intrinsicInterior.mpr ⟨xA, ?_, rfl⟩
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hU.mem_nhds hxU) hUF)

theorem midpoint_mem_face {a b : V} (ha : a ∈ H.region) (hb : b ∈ H.region) :
    (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b ∈ H.face (H.jointZeros a b) := by
  apply H.convex_face (H.jointZeros a b)
    ⟨ha, fun _ hi => hi.1⟩ ⟨hb, fun _ hi => hi.2⟩ <;> norm_num

/-- The midpoint of a pair lies in the relative interior of its genuine active face. -/
theorem midpoint_mem_intrinsicInterior_face [Finite ι] {a b : V}
    (ha : a ∈ H.region) (hb : b ∈ H.region) :
    (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b ∈
      intrinsicInterior ℝ (H.face (H.jointZeros a b)) := by
  apply H.mem_intrinsicInterior_face_of_strict (H.midpoint_mem_face ha hb)
  intro i hi
  rw [Convex.combo_affine_apply (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)]
  have ha0 := ha i
  have hb0 := hb i
  have hne : H.slack i a ≠ 0 ∨ H.slack i b ≠ 0 := by
    by_cases hia : H.slack i a = 0
    · exact Or.inr (fun hib => hi ⟨hia, hib⟩)
    · exact Or.inl hia
  simp only [smul_eq_mul]
  rcases hne with hne | hne
  · have hpos : 0 < H.slack i a := lt_of_le_of_ne ha0 hne.symm
    linarith
  · have hpos : 0 < H.slack i b := lt_of_le_of_ne hb0 hne.symm
    linarith

/-- Relative-interior points of the pair's face have precisely the common active
constraints. This is the exact minimal-face fact used in the exchange argument. -/
theorem active_eq_of_intrinsicInterior_jointFace {a b u : V}
    (ha : a ∈ H.region) (hb : b ∈ H.region)
    (hu : u ∈ intrinsicInterior ℝ (H.face (H.jointZeros a b))) :
    H.active u = H.active a ∩ H.active b := by
  have huF := intrinsicInterior_subset hu
  have hzero (i : ι) : H.slack i u = 0 ↔ H.slack i a = 0 ∧ H.slack i b = 0 := by
    constructor
    · intro hi
      have hz := affine_zero_on_of_intrinsicInterior (H.face (H.jointZeros a b))
        (H.slack i) (fun y hy => hy.1 i) hu hi
      exact ⟨hz a ⟨ha, fun _ h => h.1⟩, hz b ⟨hb, fun _ h => h.2⟩⟩
    · exact fun hi => huF.2 i hi
  ext i
  constructor
  · rintro ⟨hi, hinf⟩
    have hp := (hzero i).mp hi
    exact ⟨⟨hp.1, hinf⟩, ⟨hp.2, hinf⟩⟩
  · rintro ⟨⟨ha0, hinf⟩, ⟨hb0, _⟩⟩
    exact ⟨(hzero i).mpr ⟨ha0, hb0⟩, hinf⟩

theorem mem_jointFace_of_active_subset {a b c : V}
    (hc : c ∈ H.region) (h : H.active a ∩ H.active b ⊆ H.active c) :
    c ∈ H.face (H.jointZeros a b) := by
  refine ⟨hc, ?_⟩
  intro i hi
  by_cases hinf : H.informative i
  · exact (h ⟨⟨hi.1, hinf⟩, ⟨hi.2, hinf⟩⟩).1
  · by_contra hn
    exact hinf ⟨c, hc, hn⟩

theorem jointFace_ne_region_of_active_ne_empty {a b : V}
    (h : H.active a ∩ H.active b ≠ ∅) : H.face (H.jointZeros a b) ≠ H.region := by
  obtain ⟨i, hi⟩ := Set.nonempty_iff_ne_empty.mpr h
  obtain ⟨y, hy, hne⟩ := hi.1.2
  intro he
  have hyF : y ∈ H.face (H.jointZeros a b) := by simpa only [he] using hy
  exact hne (hyF.2 i ⟨hi.1.1, hi.2.1⟩)


/-- The common-active face is the smallest actual convex face containing the pair. -/
theorem jointFace_minimal [Finite ι] {a b : V}
    (ha : a ∈ H.region) (hb : b ∈ H.region) {G : Set V}
    (hGconvex : Convex ℝ G) (hG : IsExtreme ℝ H.region G)
    (haG : a ∈ G) (hbG : b ∈ G) : H.face (H.jointZeros a b) ⊆ G := by
  apply subset_extreme_of_intrinsicInterior_mem
    (H.isExtreme_face _).subset hG (H.midpoint_mem_intrinsicInterior_face ha hb)
  exact hGconvex haG hbG (by norm_num) (by norm_num) (by norm_num)

/-- Every nonempty convex face is exactly an active-inequality face. This ensures
that the affine-inequality description captures all geometric faces. -/
theorem exists_activeFace_eq [Finite ι] {G : Set V}
    (hGconvex : Convex ℝ G) (hG : IsExtreme ℝ H.region G) (hGne : G.Nonempty) :
    ∃ x ∈ G, G = H.face (H.jointZeros x x) := by
  obtain ⟨x, hx⟩ := Set.Nonempty.intrinsicInterior hGconvex hGne
  have hxG := intrinsicInterior_subset hx
  have hxP := hG.subset hxG
  have hxF : x ∈ intrinsicInterior ℝ (H.face (H.jointZeros x x)) := by
    have h := H.midpoint_mem_intrinsicInterior_face hxP hxP
    have he : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • x = x := by module
    simpa only [he] using h
  refine ⟨x, hxG, Set.Subset.antisymm ?_ ?_⟩
  · exact subset_extreme_of_intrinsicInterior_mem hG.subset (H.isExtreme_face _) hx
      (intrinsicInterior_subset hxF)
  · exact subset_extreme_of_intrinsicInterior_mem (H.isExtreme_face _).subset hG hxF hxG

end AffineInequalities

/-- Prescribed parity on every actual face, including every lattice point of its
saturated affine span as a parity representative. This is Proposition 2.1(i). -/
def FaceParity (embedding : M →+ V) (P : Set V) : Prop :=
  ∀ F : Set V, Convex ℝ F → IsExtreme ℝ P F →
    ∀ z : M, embedding z ∈ intrinsicInterior ℝ ((2 : ℝ) • F) →
    ∀ c : M, embedding c ∈ affineSpan ℝ F →
      ∃ p q : M, embedding p ∈ F ∧ embedding q ∈ F ∧ p + q = z ∧ SameParity p c

/-- Adjoint decomposition on every actual proper face. This is Proposition 2.1(ii). -/
def FaceAdjoint (embedding : M →+ V) (P : Set V) : Prop :=
  ∀ F : Set V, Convex ℝ F → IsExtreme ℝ P F → F ≠ P →
    ∀ z : M, embedding z ∈ intrinsicInterior ℝ ((2 : ℝ) • F) →
      ∃ p q : M, embedding p ∈ F ∧ embedding q ∈ intrinsicInterior ℝ F ∧ p + q = z

/-- The sum of two lattice points belongs to the relative interior of twice their
active face. This proves the passage from a pair to the literal hypothesis of (i)/(ii). -/
theorem pair_sum_mem_intrinsicInterior_twice_face [Finite ι]
    (H : AffineInequalities ι V) (embedding : M →+ V)
    (a b : latticePoints embedding H.region) :
    embedding ((a : M) + b) ∈ intrinsicInterior ℝ
      ((2 : ℝ) • H.face (H.jointZeros (embedding a) (embedding b))) := by
  rw [intrinsicInterior_smul 2 (by norm_num)]
  refine ⟨(1 / 2 : ℝ) • embedding a + (1 / 2 : ℝ) • embedding b,
    H.midpoint_mem_intrinsicInterior_face a.property b.property, ?_⟩
  rw [map_add]
  dsimp only
  rw [two_smul, add_add_add_comm, ← add_smul, ← add_smul]
  norm_num

/-- Proposition 2.1's triple reduction for an actual finitely described polyhedron.
The hypotheses are the literal relative-interior, face-parity, and adjoint statements;
all intermediate face relations are derived from its affine inequalities. -/
theorem tripleReduction_of_face_parity_adjoint [Finite ι]
    (H : AffineInequalities ι V) (embedding : M →+ V)
    (hparity : FaceParity embedding H.region) (hadjoint : FaceAdjoint embedding H.region) :
    TripleReduction (latticePoints embedding H.region) := by
  let faceIndex : latticePoints embedding H.region → (Set ι)ᵒᵈ :=
    fun a => H.active (embedding a)
  apply tripleReduction_of_convex_face_data embedding H.region H.convex_region faceIndex
  · intro a b c hc
    change H.active (embedding a) ∩ H.active (embedding b) ⊆ H.active (embedding c) at hc
    let F := H.face (H.jointZeros (embedding a) (embedding b))
    have hcF : embedding c ∈ F := H.mem_jointFace_of_active_subset c.property hc
    obtain ⟨p, q, hp, hq, he, hpc⟩ := hparity F (H.convex_face _) (H.isExtreme_face _)
      ((a : M) + b) (pair_sum_mem_intrinsicInterior_twice_face H embedding a b)
      c (subset_affineSpan ℝ F hcF)
    exact ⟨⟨p, hp.1⟩, ⟨q, hq.1⟩, he.symm, hpc⟩
  · intro a b hab
    change H.active (embedding a) ∩ H.active (embedding b) ≠ ∅ at hab
    let F := H.face (H.jointZeros (embedding a) (embedding b))
    obtain ⟨p, q, hp, hq, he⟩ := hadjoint F (H.convex_face _) (H.isExtreme_face _)
      (H.jointFace_ne_region_of_active_ne_empty hab) ((a : M) + b)
      (pair_sum_mem_intrinsicInterior_twice_face H embedding a b)
    have hqF : embedding q ∈ F := intrinsicInterior_subset hq
    refine ⟨⟨q, hqF.1⟩, ⟨p, hp.1⟩, ?_, ?_, ?_⟩
    · simpa only [add_comm] using he.symm
    · exact H.active_eq_of_intrinsicInterior_jointFace a.property b.property hq
    · change H.active (embedding a) ∩ H.active (embedding b) ⊆ H.active (embedding p)
      rintro i ⟨ha, hb⟩
      exact ⟨hp.2 i ⟨ha.1, hb.1⟩, ha.2⟩

/-- The full quadratic-generation conclusion of Proposition 2.1 for every finite
half-space presentation, with genuine faces and no assumed exchange connectivity. -/
theorem quadratic_generation_of_face_parity_adjoint [Finite ι]
    (H : AffineInequalities ι V) (embedding : M →+ V)
    (hidp : IntegerDecompositionProperty embedding H.region)
    (hparity : FaceParity embedding H.region) (hadjoint : FaceAdjoint embedding H.region)
    (R : Type*) [CommRing R] :
    RingHom.ker (paperToricMap (latticePoints embedding H.region) R) =
      polynomialQuadraticIdeal (latticePoints embedding H.region) R :=
  paper_kernel_eq_quadrics (latticePoints embedding H.region) R
    (midpointDecomposition_of_convex_idp embedding H.region H.convex_region hidp)
    (tripleReduction_of_face_parity_adjoint H embedding hparity hadjoint)

end PaperVerification.ToricExchange
