module

public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.Part03
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Topology.Order.LeftRight
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Data.Finset.Max
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.Data.Int.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Order.Compact
public import Mathlib.Data.Fintype.Lattice

@[expose] public section
set_option autoImplicit false

section
-- BEGIN PaperVerification.ToricFaces
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
end
-- END PaperVerification.ToricFaces
end

section
-- BEGIN PaperVerification.ToricElimination
/-!
# Finite half-space representations by elimination

The missing representation theorem is developed through Fourier–Motzkin elimination.
No polyhedral representation assertion is taken as an axiom.
-/

noncomputable section

namespace PaperVerification.ToricExchange

open Set

/-- Elimination of one real unknown from a finite system of weak affine inequalities.
The retained constraints are the zero-coefficient rows and every lower/upper pair. -/
theorem exists_affine_inequality_variable_iff {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) :
    (∃ t : ℝ, ∀ i, 0 ≤ a i * t + b i) ↔
      (∀ i, a i = 0 → 0 ≤ b i) ∧
      (∀ i j, 0 < a i → a j < 0 → -b i / a i ≤ -b j / a j) := by
  classical
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨fun i hi => by simpa [hi] using ht i, ?_⟩
    intro i j hi hj
    have hlo : -b i / a i ≤ t := (div_le_iff₀ hi).mpr (by nlinarith [ht i])
    have hup : t ≤ -b j / a j := (le_div_iff_of_neg hj).mpr (by nlinarith [ht j])
    exact hlo.trans hup
  · rintro ⟨hz, hpairs⟩
    let L : Finset ι := Finset.univ.filter (fun i => 0 < a i)
    let U : Finset ι := Finset.univ.filter (fun i => a i < 0)
    have hrow (t : ℝ) (hlo : ∀ i, 0 < a i → -b i / a i ≤ t)
        (hup : ∀ i, a i < 0 → t ≤ -b i / a i) :
        ∀ i, 0 ≤ a i * t + b i := by
      intro i
      rcases lt_trichotomy (a i) 0 with hi | hi | hi
      · have := (le_div_iff_of_neg hi).mp (hup i hi)
        nlinarith
      · simpa [hi] using hz i hi
      · have := (div_le_iff₀ hi).mp (hlo i hi)
        nlinarith
    by_cases hL : L.Nonempty
    · obtain ⟨i, hi, hmax⟩ := L.exists_max_image (fun i => -b i / a i) hL
      have hi0 : 0 < a i := (Finset.mem_filter.mp hi).2
      refine ⟨-b i / a i, hrow _ ?_ ?_⟩
      · intro j hj
        exact hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
      · intro j hj
        exact hpairs i j hi0 hj
    · by_cases hU : U.Nonempty
      · obtain ⟨j, hj, hmin⟩ := U.exists_min_image (fun i => -b i / a i) hU
        refine ⟨-b j / a j, hrow _ ?_ ?_⟩
        · intro i hi
          exact False.elim (hL ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩)
        · intro i hi
          exact hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
      · refine ⟨0, hrow _ ?_ ?_⟩
        · intro i hi
          exact False.elim (hL ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩)
        · intro i hi
          exact False.elim (hU ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩)

variable {V W ι : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

namespace AffineInequalities

/-- In finite dimension, every affine functional is continuous. -/
def ofSlack (f : ι → V →ᵃ[ℝ] ℝ) : AffineInequalities ι V where
  slack := f
  continuous_slack i := AffineMap.continuous_linear_iff.mp
    (f i).linear.continuous_of_finiteDimensional

/-- Pulling back finitely many half-spaces along an actual affine map. -/
def comap (H : AffineInequalities ι V) (f : W →ᵃ[ℝ] V) : AffineInequalities ι W :=
  ofSlack (fun i => (H.slack i).comp f)

@[simp] theorem mem_comap_region (H : AffineInequalities ι V) (f : W →ᵃ[ℝ] V) (x : W) :
    x ∈ (H.comap f).region ↔ f x ∈ H.region := Iff.rfl

/-- The coefficient of the variable that will be eliminated. -/
def lastCoefficient (H : AffineInequalities ι (V × ℝ)) (i : ι) : ℝ :=
  (H.slack i).linear (0, 1)

/-- The affine row remaining when the last variable is set to zero. -/
def zeroLast (H : AffineInequalities ι (V × ℝ)) (i : ι) : V →ᵃ[ℝ] ℝ :=
  (H.slack i).comp ((AffineMap.id ℝ V).prod (AffineMap.const ℝ V (0 : ℝ)))

theorem slack_prod (H : AffineInequalities ι (V × ℝ)) (i : ι) (x : V) (t : ℝ) :
    H.slack i (x, t) = H.lastCoefficient i * t + H.zeroLast i x := by
  have he : (x, t) = t • ((0, 1) : V × ℝ) +ᵥ ((x, 0) : V × ℝ) := by ext <;> simp
  rw [he, AffineMap.map_vadd, map_smul]
  simp [lastCoefficient, zeroLast, smul_eq_mul, mul_comm]

/-- The actual projected system. Inapplicable rows are represented by `0 ≥ 0`,
which leaves the represented set unchanged. -/
noncomputable def eliminateLast (H : AffineInequalities ι (V × ℝ)) :
    AffineInequalities (ι ⊕ (ι × ι)) V := by
  classical
  exact ofSlack (fun row => match row with
    | Sum.inl i => if H.lastCoefficient i = 0 then H.zeroLast i else 0
    | Sum.inr (i, j) => if 0 < H.lastCoefficient i ∧ H.lastCoefficient j < 0 then
        (H.lastCoefficient i)⁻¹ • H.zeroLast i -
          (H.lastCoefficient j)⁻¹ • H.zeroLast j else 0)

/-- Fourier–Motzkin elimination preserves exactly the existential projection. -/
theorem mem_eliminateLast_region [Fintype ι] (H : AffineInequalities ι (V × ℝ)) (x : V) :
    x ∈ H.eliminateLast.region ↔ ∃ t : ℝ, (x, t) ∈ H.region := by
  classical
  rw [show (∃ t : ℝ, (x, t) ∈ H.region) ↔
      ∃ t : ℝ, ∀ i, 0 ≤ H.lastCoefficient i * t + H.zeroLast i x by
    simp only [region, Set.mem_setOf_eq, H.slack_prod]]
  rw [exists_affine_inequality_variable_iff]
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · intro i hi
      simpa [eliminateLast, ofSlack, hi] using hx (Sum.inl i)
    · intro i j hi hj
      have hij : 0 < H.lastCoefficient i ∧ H.lastCoefficient j < 0 := ⟨hi, hj⟩
      have h := hx (Sum.inr (i, j))
      simp only [eliminateLast, ofSlack, if_pos hij, AffineMap.coe_sub, Pi.sub_apply,
        AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul] at h
      have hle := sub_nonneg.mp h
      simpa only [neg_div, div_eq_mul_inv, mul_comm, mul_neg] using (neg_le_neg hle)
  · rintro ⟨hz, hpairs⟩ row
    rcases row with i | ⟨i, j⟩
    · by_cases hi : H.lastCoefficient i = 0
      · simpa [eliminateLast, ofSlack, hi] using hz i hi
      · simp [eliminateLast, ofSlack, hi]
    · by_cases hij : 0 < H.lastCoefficient i ∧ H.lastCoefficient j < 0
      · have h := hpairs i j hij.1 hij.2
        simp only [eliminateLast, ofSlack, if_pos hij, AffineMap.coe_sub, Pi.sub_apply,
          AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul]
        have h' : (H.lastCoefficient j)⁻¹ * H.zeroLast j x ≤
            (H.lastCoefficient i)⁻¹ * H.zeroLast i x := by
          simpa only [neg_div, div_eq_mul_inv, mul_comm, mul_neg, neg_le_neg_iff] using h
        exact sub_nonneg.mpr h'
      · simp [eliminateLast, ofSlack, hij]

end AffineInequalities

/-- The usual finite half-space representation property, with no geometric
conclusions encoded into the definition. -/
def HasFiniteHalfspaces (P : Set V) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (H : AffineInequalities ι V), P = H.region

namespace HasFiniteHalfspaces

variable {P : Set V}

theorem comap (hP : HasFiniteHalfspaces P) (f : W →ᵃ[ℝ] V) :
    HasFiniteHalfspaces (f ⁻¹' P) := by
  rcases hP with ⟨ι, hι, H, rfl⟩
  exact ⟨ι, hι, H.comap f, rfl⟩

theorem project_real {P : Set (V × ℝ)} (hP : HasFiniteHalfspaces P) :
    HasFiniteHalfspaces {x : V | ∃ t : ℝ, (x, t) ∈ P} := by
  rcases hP with ⟨ι, hι, H, rfl⟩
  letI := hι
  refine ⟨ι ⊕ (ι × ι), inferInstance, H.eliminateLast, ?_⟩
  ext x
  exact (H.mem_eliminateLast_region x).symm


/-- Moving the first coordinate of a finite tuple into the final real factor. -/
def insertCoordinate (n : ℕ) :
    ((V × (Fin n → ℝ)) × ℝ) →ₗ[ℝ] (V × (Fin (n + 1) → ℝ)) where
  toFun x := (x.1.1, Fin.cons x.2 x.1.2)
  map_add' x y := by
    apply Prod.ext
    · rfl
    · funext i
      exact Fin.cases rfl (fun _ => rfl) i
  map_smul' c x := by
    apply Prod.ext
    · rfl
    · funext i
      exact Fin.cases rfl (fun _ => rfl) i

/-- Eliminating any finite tuple of real auxiliary variables. -/
theorem project_fin (n : ℕ) {P : Set (V × (Fin n → ℝ))}
    (hP : HasFiniteHalfspaces P) :
    HasFiniteHalfspaces {x : V | ∃ w : Fin n → ℝ, (x, w) ∈ P} := by
  induction n with
  | zero =>
    let f : V →ᵃ[ℝ] V × (Fin 0 → ℝ) :=
      (AffineMap.id ℝ V).prod (AffineMap.const ℝ V 0)
    convert hP.comap f using 1
    ext x
    constructor
    · rintro ⟨w, hw⟩
      have hw0 : w = 0 := Subsingleton.elim _ _
      simpa [f, hw0] using hw
    · intro hx
      exact ⟨0, hx⟩
  | succ n ih =>
    let Q : Set ((V × (Fin n → ℝ)) × ℝ) := (insertCoordinate (V := V) n) ⁻¹' P
    have hQ : HasFiniteHalfspaces Q := by
      change HasFiniteHalfspaces ((insertCoordinate (V := V) n).toAffineMap ⁻¹' P)
      exact hP.comap (insertCoordinate (V := V) n).toAffineMap
    have hR := hQ.project_real
    have hproj := ih hR
    convert hproj using 1
    ext x
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨Fin.tail w, w 0, ?_⟩
      simpa [Q, insertCoordinate, Fin.cons_self_tail] using hw
    · rintro ⟨w, t, ht⟩
      exact ⟨Fin.cons t w, ht⟩

/-- Projection over an arbitrary finite coordinate index set. -/
theorem project_fintype {κ : Type} [Fintype κ] {P : Set (V × (κ → ℝ))}
    (hP : HasFiniteHalfspaces P) :
    HasFiniteHalfspaces {x : V | ∃ w : κ → ℝ, (x, w) ∈ P} := by
  classical
  let e := Fintype.equivFin κ
  let f : (V × (Fin (Fintype.card κ) → ℝ)) →ₗ[ℝ] (V × (κ → ℝ)) :=
    { toFun := fun x => (x.1, fun i => x.2 (e i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have h := (hP.comap f.toAffineMap).project_fin (Fintype.card κ)
  convert h using 1
  ext x
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨fun i => w (e.symm i), ?_⟩
    simpa [f] using hw
  · rintro ⟨w, hw⟩
    exact ⟨fun i => w (e i), hw⟩

end HasFiniteHalfspaces

section FiniteConvexHull

variable {n : ℕ} {κ : Type} [Fintype κ]

/-- The linear map sending weights to their weighted vector sum. -/
def weightedPointSum (v : κ → Fin n → ℝ) : (κ → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun w := ∑ i, w i • v i
  map_add' w z := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c w := by simp [smul_smul, Finset.smul_sum]

/-- Coordinate projections of the nonnegative weights. -/
def weightCoordinate (i : κ) : ((Fin n → ℝ) × (κ → ℝ)) →ₗ[ℝ] ℝ :=
  (LinearMap.proj i).comp (LinearMap.snd ℝ (Fin n → ℝ) (κ → ℝ))

/-- The affine equations defining a convex combination: total weight one, and
weighted vector sum equal to the displayed point. -/
def combinationEquation (v : κ → Fin n → ℝ) :
    Option (Fin n) → ((Fin n → ℝ) × (κ → ℝ)) →ᵃ[ℝ] ℝ
  | none => (∑ i : κ, weightCoordinate (n := n) i).toAffineMap -
      AffineMap.const ℝ ((Fin n → ℝ) × (κ → ℝ)) 1
  | some j => ((LinearMap.proj j).comp
      (LinearMap.fst ℝ (Fin n → ℝ) (κ → ℝ) -
        (weightedPointSum v).comp (LinearMap.snd ℝ (Fin n → ℝ) (κ → ℝ)))).toAffineMap

/-- A finite inequality description of the graph of all convex combinations. -/
def combinationGraph (v : κ → Fin n → ℝ) :
    AffineInequalities (κ ⊕ (Option (Fin n) × Bool)) ((Fin n → ℝ) × (κ → ℝ)) :=
  AffineInequalities.ofSlack (fun row => match row with
    | Sum.inl i => (weightCoordinate i).toAffineMap
    | Sum.inr (j, true) => combinationEquation v j
    | Sum.inr (j, false) => -(combinationEquation v j))

theorem mem_combinationGraph_region (v : κ → Fin n → ℝ) (x : Fin n → ℝ) (w : κ → ℝ) :
    (x, w) ∈ (combinationGraph v).region ↔
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧ (∑ i, w i • v i) = x := by
  classical
  have heq (j : Option (Fin n)) :
      (0 ≤ combinationEquation v j (x, w) ∧ 0 ≤ -(combinationEquation v j (x, w))) ↔
        combinationEquation v j (x, w) = 0 := by
    constructor
    · rintro ⟨hp, hn⟩
      linarith
    · intro hz
      simp [hz]
  constructor
  · intro h
    have hz (j : Option (Fin n)) : combinationEquation v j (x, w) = 0 := by
      apply (heq j).mp
      exact ⟨h (Sum.inr (j, true)), h (Sum.inr (j, false))⟩
    refine ⟨fun i => h (Sum.inl i), ?_, ?_⟩
    · have h0 := hz none
      simpa [combinationEquation, weightCoordinate] using (sub_eq_zero.mp h0)
    · funext j
      have hj := hz (some j)
      simpa [combinationEquation, weightedPointSum] using (sub_eq_zero.mp hj).symm
  · rintro ⟨hw, hsum, hvec⟩ row
    rcases row with i | ⟨j, b⟩
    · exact hw i
    · have hz : combinationEquation v j (x, w) = 0 := by
        cases j with
        | none => simp [combinationEquation, weightCoordinate, hsum]
        | some j => simp [combinationEquation, weightedPointSum, hvec]
      cases b <;> simp [combinationGraph, AffineInequalities.ofSlack, hz]

/-- A finite convex hull is exactly the projection of the convex-combination graph. -/
theorem mem_finite_convexHull_iff_weights (s : Finset (Fin n → ℝ)) (x : Fin n → ℝ) :
    x ∈ convexHull ℝ (s : Set (Fin n → ℝ)) ↔
      ∃ w : s → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
        (∑ i, w i • (i : Fin n → ℝ)) = x := by
  classical
  constructor
  · intro hx
    obtain ⟨w, hw, hsum, hvec⟩ := Finset.mem_convexHull'.mp hx
    refine ⟨fun i => w i, fun i => hw i i.property, ?_, ?_⟩
    · simpa only [Finset.univ_eq_attach, Finset.sum_attach] using hsum
    · change (∑ i ∈ s.attach, w (i : Fin n → ℝ) • (i : Fin n → ℝ)) = x
      rw [Finset.sum_attach s (fun y => w y • y)]
      exact hvec
  · rintro ⟨w, hw, hsum, hvec⟩
    exact mem_convexHull_of_exists_fintype w (fun i : s => (i : Fin n → ℝ))
      hw hsum (fun i => i.property) hvec

/-- Every finite real convex hull has a finite affine half-space representation.
The proof explicitly eliminates its convex-combination weights. -/
theorem finite_convexHull_hasFiniteHalfspaces (s : Finset (Fin n → ℝ)) :
    HasFiniteHalfspaces (convexHull ℝ (s : Set (Fin n → ℝ))) := by
  classical
  let H := combinationGraph (fun i : s => (i : Fin n → ℝ))
  have hH : HasFiniteHalfspaces H.region :=
    ⟨s ⊕ (Option (Fin n) × Bool), inferInstance, H, rfl⟩
  convert hH.project_fintype using 1
  ext x
  rw [mem_finite_convexHull_iff_weights]
  exact exists_congr fun w => (mem_combinationGraph_region _ x w).symm

end FiniteConvexHull

end PaperVerification.ToricExchange
end
-- END PaperVerification.ToricElimination
end

section
-- BEGIN PaperVerification.ToricFaceGeometry
/-!
# Faces of finite convex hulls

Every actual convex face is the convex hull of the original generators lying on it.
This supplies the finite vertex data needed when passing to lower-dimensional faces.
-/

noncomputable section

namespace PaperVerification.ToricExchange

open Set

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The original finite generators lying on a specified geometric face. -/
noncomputable def faceGenerators (s : Finset V) (F : Set V) : Finset V := by
  classical
  exact s.filter (fun v => v ∈ F)

/-- An affine functional commutes with a weighted sum whose weights total one. -/
theorem affine_apply_weighted_sum {κ : Type*} (s : Finset κ) (w : κ → ℝ) (v : κ → V)
    (hsum : ∑ i ∈ s, w i = 1) (f : V →ᵃ[ℝ] ℝ) :
    f (∑ i ∈ s, w i • v i) = ∑ i ∈ s, w i * f (v i) := by
  have h := s.map_affineCombination v w hsum f
  simpa only [Finset.affineCombination_eq_linear_combination _ _ _ hsum,
    Function.comp_apply, smul_eq_mul] using h

/-- Injective affine maps preserve actual extreme points. -/
theorem affine_mem_extremePoints_image {W : Type*} [AddCommGroup W] [Module ℝ W]
    (f : V →ᵃ[ℝ] W) (hf : Function.Injective f) {S : Set V} {x : V}
    (hx : x ∈ S.extremePoints ℝ) : f x ∈ (f '' S).extremePoints ℝ := by
  refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hopen
  rw [← image_openSegment ℝ f a b] at hopen
  obtain ⟨z, hz, he⟩ := hopen
  have hzx := hf he
  subst z
  exact congrArg f (hx.2 ha hb hz)

/-- The left endpoint is an extreme point of a nondegenerate real segment. -/
theorem left_endpoint_extreme_segment {v w : V} (hvw : v ≠ w) :
    v ∈ (segment ℝ v w).extremePoints ℝ := by
  have h0 : (0 : ℝ) ∈ (Set.Icc (0 : ℝ) 1).extremePoints ℝ := by
    refine ⟨⟨le_rfl, zero_le_one⟩, ?_⟩
    rintro x hx y hy ⟨a, b, ha, hb, hab, he⟩
    simp only [smul_eq_mul] at he
    have hax : a * x ≤ 0 := by nlinarith [mul_nonneg hb.le hy.1]
    have haz : a * x = 0 := le_antisymm hax (mul_nonneg ha.le hx.1)
    exact (mul_eq_zero.mp haz).resolve_left (ne_of_gt ha)
  rw [segment_eq_image_lineMap]
  have h := affine_mem_extremePoints_image (AffineMap.lineMap v w)
    (AffineMap.lineMap_injective ℝ hvw) h0
  simpa using h

/-- The right endpoint is also an extreme point of the segment. -/
theorem right_endpoint_extreme_segment {v w : V} (hvw : v ≠ w) :
    w ∈ (segment ℝ v w).extremePoints ℝ := by
  rw [segment_symm]
  exact left_endpoint_extreme_segment hvw.symm

namespace AffineInequalities

variable {ι : Type*} (H : AffineInequalities ι V)

/-- A face of a finite convex hull is generated by exactly those original generators
on which its defining constraints vanish. -/
theorem face_eq_convexHull_filter (s : Finset V)
    (hH : H.region = convexHull ℝ (s : Set V)) (J : Set ι) :
    H.face J = convexHull ℝ (faceGenerators s (H.face J) : Set V) := by
  classical
  change H.face J = convexHull ℝ ((s.filter (fun v => v ∈ H.face J)) : Set V)
  apply Set.Subset.antisymm
  · intro x hx
    have hxHull : x ∈ convexHull ℝ (s : Set V) := hH ▸ hx.1
    obtain ⟨w, hw, hsum, hvec⟩ := Finset.mem_convexHull'.mp hxHull
    have hgenerator (v : V) (hv : v ∈ s) : v ∈ H.region := by
      rw [hH]
      exact subset_convexHull ℝ (s : Set V) hv
    have hpositive (v : V) (hv : v ∈ s) (hwne : w v ≠ 0) : v ∈ H.face J := by
      refine ⟨hgenerator v hv, ?_⟩
      intro j hj
      have hterms : ∀ y ∈ s, 0 ≤ w y * H.slack j y :=
        fun y hy => mul_nonneg (hw y hy) (hgenerator y hy j)
      have hslacksum : (∑ y ∈ s, w y * H.slack j y) = 0 := by
        have hm := affine_apply_weighted_sum s w id hsum (H.slack j)
        simp only [id_eq] at hm
        rw [← hm, hvec]
        exact hx.2 j hj
      have hle := Finset.single_le_sum hterms hv
      rw [hslacksum] at hle
      have hzero : w v * H.slack j v = 0 := le_antisymm hle (hterms v hv)
      exact (mul_eq_zero.mp hzero).resolve_left hwne
    let t := s.filter (fun v => v ∈ H.face J)
    have hmissing (v : V) (hv : v ∈ s) (hvt : v ∉ t) : w v = 0 := by
      by_contra hne
      exact hvt (Finset.mem_filter.mpr ⟨hv, hpositive v hv hne⟩)
    have hsumt : ∑ v ∈ t, w v = 1 := by
      rw [Finset.sum_subset (Finset.filter_subset _ _) hmissing]
      exact hsum
    have hvect : ∑ v ∈ t, w v • v = x := by
      rw [Finset.sum_subset (Finset.filter_subset _ _) (fun v hv hvt => by rw [hmissing v hv hvt]; simp)]
      exact hvec
    exact Finset.mem_convexHull'.mpr ⟨w,
      fun v hv => hw v (Finset.mem_filter.mp hv).1, hsumt, hvect⟩
  · apply convexHull_min
    · exact fun v hv => (Finset.mem_filter.mp hv).2
    · exact H.convex_face J

end AffineInequalities

/-- Every actual convex face of a finite real polytope is the convex hull of the
original generators that it contains. No exposed-face assumption is added. -/
theorem convex_face_eq_convexHull_filter {n : ℕ} (s : Finset (Fin n → ℝ))
    (G : Set (Fin n → ℝ)) (hGconvex : Convex ℝ G)
    (hG : IsExtreme ℝ (convexHull ℝ (s : Set (Fin n → ℝ))) G) :
    G = convexHull ℝ (faceGenerators s G : Set (Fin n → ℝ)) := by
  classical
  by_cases hGne : G.Nonempty
  · obtain ⟨ι, hι, H, hH⟩ := finite_convexHull_hasFiniteHalfspaces s
    letI := hι
    have hGH : IsExtreme ℝ H.region G := by simpa only [hH] using hG
    obtain ⟨x, hx, hxG⟩ := H.exists_activeFace_eq hGconvex hGH hGne
    rw [hxG]
    exact H.face_eq_convexHull_filter s hH.symm _
  · have hG0 : G = ∅ := Set.not_nonempty_iff_eq_empty.mp hGne
    simp [hG0, faceGenerators]


/-- The full exchange criterion for every finite real polytope, including those
of lower dimension in their ambient lattice. Integral vertices are not needed by
this reduction: all decomposition points are still actual points of the given lattice. -/
theorem finite_polytope_exchange_criterion {n : ℕ} {M : Type*} [AddCommGroup M]
    (embedding : M →+ (Fin n → ℝ)) (P : Set (Fin n → ℝ))
    (hpoly : ∃ s : Finset (Fin n → ℝ), P = convexHull ℝ (s : Set (Fin n → ℝ)))
    (hidp : IntegerDecompositionProperty embedding P)
    (hparity : FaceParity embedding P) (hadjoint : FaceAdjoint embedding P)
    (R : Type*) [CommRing R] :
    (∀ s t : Multiset (latticePoints embedding P), s.card = t.card →
      total (latticePoints embedding P) s = total (latticePoints embedding P) t →
      Connected (latticePoints embedding P) s t) ∧
    RingHom.ker (paperToricMap (latticePoints embedding P) R) =
      polynomialQuadraticIdeal (latticePoints embedding P) R := by
  obtain ⟨s, rfl⟩ := hpoly
  obtain ⟨ι, hι, H, hH⟩ := finite_convexHull_hasFiniteHalfspaces s
  letI := hι
  rw [hH] at hidp hparity hadjoint ⊢
  have hmid := midpointDecomposition_of_convex_idp embedding H.region H.convex_region hidp
  have htriple := tripleReduction_of_face_parity_adjoint H embedding hparity hadjoint
  exact ⟨all_fibers_connected _ hmid htriple, paper_kernel_eq_quadrics _ R hmid htriple⟩

end PaperVerification.ToricExchange
end
-- END PaperVerification.ToricFaceGeometry
end

section
-- BEGIN PaperVerification.ToricStatements
/-!
# Faithful mathematical targets for the toric paper

The principal claims below are named propositions, not axioms and not claimed proofs.
The polytope, edges, smoothness, lattice lengths, sums, and kernel are all genuine
mathematical objects. No desired conclusion is included in a structure definition.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped Pointwise
open PaperVerification.ToricExchange

abbrev Lattice (n : ℕ) := Fin n → ℤ
abbrev Ambient (n : ℕ) := Fin n → ℝ

/-- The standard inclusion of the full lattice into its real vector space. -/
def embed (n : ℕ) : Lattice n →+ Ambient n where
  toFun z i := z i
  map_zero' := by ext i; simp
  map_add' z w := by ext i; simp

theorem embed_injective (n : ℕ) : Function.Injective (embed n) := by
  intro z w h
  funext i
  exact Int.cast_injective (congrFun h i)

/-- A vector in an integral basis is primitive: it is not a nonunit integer
multiple of another lattice vector. -/
theorem lattice_basis_vector_primitive {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n)
    (k : ℤ) (z : Lattice n) (h : b i = k • z) : k = 1 ∨ k = -1 := by
  have hc : b.repr (k • z) i = 1 := by
    rw [← h]
    simp
  have hsmul : b.repr (k • z) = k • b.repr z := b.repr.map_smul k z
  rw [hsmul] at hc
  have hk : k * b.repr z i = 1 := by
    simpa only [Finsupp.smul_apply, smul_eq_mul] using hc
  exact Int.eq_one_or_neg_one_of_mul_eq_one hk

/-- The coordinate gcd of a primitive integral basis vector is exactly one. -/
theorem lattice_basis_vector_gcd_one {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) :
    Finset.univ.gcd (fun j : Fin n => (b i j).natAbs) = 1 := by
  classical
  let g : ℕ := Finset.univ.gcd (fun j : Fin n => (b i j).natAbs)
  have hd (j : Fin n) : (g : ℤ) ∣ b i j :=
    Int.natCast_dvd.mpr (Finset.gcd_dvd (Finset.mem_univ j))
  choose z hz using hd
  have hv : b i = (g : ℤ) • z := by funext j; exact hz j
  rcases lattice_basis_vector_primitive b i g z hv with hg | hg
  · exact_mod_cast hg
  · have hg0 : (0 : ℤ) ≤ g := Int.natCast_nonneg g
    omega

/-- A full-dimensional lattice polytope, given by a finite generating set.
The generating set is not required to contain only vertices. -/
structure LatticePolytope (n : ℕ) where
  generators : Finset (Lattice n)
  nonempty : generators.Nonempty
  fullDimensional : affineSpan ℝ (convexHull ℝ ((embed n) '' (generators : Set (Lattice n)))) = ⊤

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

/-- The ordinary convex hull defining the polytope. -/
def carrier : Set (Ambient n) := convexHull ℝ ((embed n) '' (P.generators : Set (Lattice n)))

/-- An edge is a nondegenerate line segment that is an actual face of the polytope. -/
def IsEdge (v w : Ambient n) : Prop :=
  v ≠ w ∧ IsExtreme ℝ P.carrier (segment ℝ v w)

/-- The endpoints of an actual edge are actual vertices of the polytope. -/
theorem edge_endpoints_extreme {v w : Ambient n} (h : P.IsEdge v w) :
    v ∈ P.carrier.extremePoints ℝ ∧ w ∈ P.carrier.extremePoints ℝ :=
  ⟨h.2.extremePoints_subset_extremePoints (left_endpoint_extreme_segment h.1),
    h.2.extremePoints_subset_extremePoints (right_endpoint_extreme_segment h.1)⟩

/-- Every vertex is one of the integral generators, regardless of whether the
original finite generating set contains redundant points. -/
theorem extreme_integral {v : Ambient n} (hv : v ∈ P.carrier.extremePoints ℝ) :
    ∃ z ∈ P.generators, embed n z = v := by
  obtain ⟨z, hz, he⟩ := extremePoints_convexHull_subset hv
  exact ⟨z, hz, he⟩

/-- The integral-endpoint clause of `EdgesAtLeast` is automatic for a lattice polytope. -/
theorem edge_endpoints_integral {v w : Ambient n} (h : P.IsEdge v w) :
    ∃ vZ wZ : Lattice n, embed n vZ = v ∧ embed n wZ = w := by
  obtain ⟨hv, hw⟩ := P.edge_endpoints_extreme h
  obtain ⟨vZ, _, hvZ⟩ := P.extreme_integral hv
  obtain ⟨wZ, _, hwZ⟩ := P.extreme_integral hw
  exact ⟨vZ, wZ, hvZ, hwZ⟩

/-- Lattice length in standard coordinates, the gcd of the coordinate differences. -/
def latticeLength (v w : Lattice n) : ℕ :=
  Finset.univ.gcd (fun i : Fin n => (w i - v i).natAbs)

/-- The gcd convention for lattice length agrees exactly with positive integer
multiplicity along a primitive basis direction, as used by the smoothness definition. -/
theorem latticeLength_basis_direction (v : Lattice n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) (k : ℕ) :
    latticeLength v (v + (k : ℤ) • b i) = k := by
  simp only [latticeLength, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    add_sub_cancel_left, Int.natAbs_mul, Int.natAbs_natCast]
  rw [Finset.gcd_mul_left, lattice_basis_vector_gcd_one]
  simp

/-- Every actual edge has integral endpoints and at least the stated lattice length. -/
def EdgesAtLeast (bound : ℕ) : Prop :=
  ∀ v w : Ambient n, P.IsEdge v w →
    ∃ vZ wZ : Lattice n, embed n vZ = v ∧ embed n wZ = w ∧
      bound ≤ latticeLength vZ wZ

/-- Requiring integral endpoints adds no hypothesis: the edge bound can be
stated equivalently by quantifying only over lattice endpoints. -/
theorem edgesAtLeast_iff (bound : ℕ) :
    P.EdgesAtLeast bound ↔ ∀ v w : Lattice n,
      P.IsEdge (embed n v) (embed n w) → bound ≤ latticeLength v w := by
  constructor
  · intro h v w hvw
    obtain ⟨v', w', hv, hw, hlen⟩ := h (embed n v) (embed n w) hvw
    have hv' := embed_injective n hv
    have hw' := embed_injective n hw
    simpa only [hv', hw'] using hlen
  · intro h v w hvw
    obtain ⟨vZ, wZ, hvZ, hwZ⟩ := P.edge_endpoints_integral hvw
    refine ⟨vZ, wZ, hvZ, hwZ, ?_⟩
    apply h
    simpa only [hvZ, hwZ] using hvw

/-- The coordinate length of a basis-direction edge satisfies precisely the
geometric edge bound. -/
theorem edge_basis_length_bound {bound : ℕ} (hbound : P.EdgesAtLeast bound)
    (v : Lattice n) (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) (k : ℕ)
    (hedge : P.IsEdge (embed n v) (embed n (v + (k : ℤ) • b i))) : bound ≤ k := by
  have h := (P.edgesAtLeast_iff bound).mp hbound v (v + (k : ℤ) • b i) hedge
  simpa only [latticeLength_basis_direction] using h

/-- Smoothness exactly in terms of the primitive incident edge directions forming
a lattice basis. The final clause states that these are all incident edges. -/
def Smooth : Prop :=
  ∀ v ∈ P.carrier.extremePoints ℝ,
    ∃ (vZ : Lattice n) (basis : Module.Basis (Fin n) ℤ (Lattice n)) (lengths : Fin n → ℕ),
      embed n vZ = v ∧
      (∀ i, 0 < lengths i ∧
        P.IsEdge v (embed n (vZ + (lengths i : ℤ) • basis i))) ∧
      (∀ w : Ambient n, P.IsEdge v w →
        ∃ i, w = embed n (vZ + (lengths i : ℤ) • basis i))

/-- The ordinary normal cone at a point, using the standard pairing. -/
def normalCone (x : Ambient n) : Set (Ambient n) :=
  {u | ∀ y ∈ P.carrier, 0 ≤ ∑ i, u i * (y i - x i)}

/-- All cones of the normal fan, including the zero cone and boundary-face cones. -/
def normalFan : Set (Set (Ambient n)) :=
  {C | ∃ x ∈ P.carrier, C = P.normalCone x}

/-- Equality of the actual normal fans. -/
def SameNormalFan (Q : LatticePolytope n) : Prop := P.normalFan = Q.normalFan

/-- Ordinary Minkowski addition of the real polytopes. -/
def minkowskiSum (Q : LatticePolytope n) : Set (Ambient n) := P.carrier + Q.carrier

/-- Full IDP of the polytope, using every positive natural dilation. -/
def HasIDP : Prop := IntegerDecompositionProperty (embed n) P.carrier

/-- The actual polynomial-kernel quadratic-generation assertion over a coefficient ring. -/
def QuadraticallyGenerated (R : Type*) [CommRing R] : Prop :=
  RingHom.ker (paperToricMap (latticePoints (embed n) P.carrier) R) =
    polynomialQuadraticIdeal (latticePoints (embed n) P.carrier) R


/-- Every lattice polytope has a finite real affine-inequality presentation,
proved by eliminating its actual convex-combination weights. -/
theorem hasFiniteHalfspaces : HasFiniteHalfspaces P.carrier := by
  classical
  have h := finite_convexHull_hasFiniteHalfspaces (P.generators.image (embed n))
  simpa [carrier, Finset.coe_image] using h

/-- Proposition 2.1, with its literal face hypotheses, on every actual lattice
polytope and in every degree. The ideal equality uses precisely the paper's map. -/
theorem proposition2_1 (R : Type*) [CommRing R]
    (hidp : P.HasIDP) (hparity : FaceParity (embed n) P.carrier)
    (hadjoint : FaceAdjoint (embed n) P.carrier) :
    (∀ s t : Multiset (latticePoints (embed n) P.carrier),
      s.card = t.card → total (latticePoints (embed n) P.carrier) s =
        total (latticePoints (embed n) P.carrier) t →
      Connected (latticePoints (embed n) P.carrier) s t) ∧
      P.QuadraticallyGenerated R := by
  change _ ∧ RingHom.ker (paperToricMap (latticePoints (embed n) P.carrier) R) =
    polynomialQuadraticIdeal (latticePoints (embed n) P.carrier) R
  change IntegerDecompositionProperty (embed n) P.carrier at hidp
  obtain ⟨ι, hι, H, hP⟩ := P.hasFiniteHalfspaces
  letI := hι
  rw [hP] at hidp hparity hadjoint ⊢
  have hmid := midpointDecomposition_of_convex_idp (embed n) H.region H.convex_region hidp
  have htriple := tripleReduction_of_face_parity_adjoint H (embed n) hparity hadjoint
  exact ⟨all_fibers_connected _ hmid htriple, paper_kernel_eq_quadrics _ R hmid htriple⟩

end LatticePolytope

/-- The exact polytope claim of Theorem 1.1 over an arbitrary field.
This is only a target proposition; no proof is asserted by defining it. -/
def Theorem1_1Statement (R : Type*) [Field R] : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ P : LatticePolytope n,
    P.Smooth → P.EdgesAtLeast n → P.HasIDP ∧ P.QuadraticallyGenerated R

/-- The prescribed-parity geometric claim of Theorem 1.2. Representing a coset by
an arbitrary lattice vector is equivalent to quantifying over `M/2M`.
The correspondence with ample divisors uses the common normal fan dictionary. -/
def Theorem1_2PolytopeStatement : Prop :=
  ∀ n : ℕ, ∀ P Q : LatticePolytope n,
    P.Smooth → Q.Smooth → P.SameNormalFan Q → P.EdgesAtLeast n → Q.EdgesAtLeast n →
    ∀ m : Lattice n, embed n m ∈ interior (P.minkowskiSum Q) →
    ∀ parityRepresentative : Lattice n,
      ∃ a b : Lattice n, embed n a ∈ P.carrier ∧ embed n b ∈ Q.carrier ∧
        a + b = m ∧ SameParity a parityRepresentative

/-- The adjoint-multiplication geometric claim of Theorem 1.3, including both
inclusions in the stated equality of lattice-point sets. -/
def Theorem1_3PolytopeStatement : Prop :=
  ∀ n : ℕ, ∀ P Q : LatticePolytope n,
    P.Smooth → Q.Smooth → P.SameNormalFan Q →
    P.EdgesAtLeast (n + 1) → Q.EdgesAtLeast (n + 1) →
    ∀ m : Lattice n,
      embed n m ∈ interior (P.minkowskiSum Q) ↔
      ∃ a b : Lattice n, embed n a ∈ P.carrier ∧ embed n b ∈ interior Q.carrier ∧ a + b = m

end PaperVerification.ToricGeometry
end
-- END PaperVerification.ToricStatements
end

section
-- BEGIN PaperVerification.ToricSimplexParity
/-!
# Integral simplex allocation with prescribed parity

The allocation theorem below is the homogeneous-coordinate form of Lemma 4.4
of *Quadratic generation for smooth polytopes with long edges*.
No geometric statements about arbitrary smooth polytopes are assumed here.
-/

namespace PaperVerification.Toric

open scoped BigOperators

/-- Allocate a prescribed number of tokens among finitely many integral capacities. -/
theorem allocate_le_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ι → ℕ) (k : ℕ) (hk : k ≤ ∑ i ∈ s, c i) :
    ∃ u : ι → ℕ, (∀ i ∈ s, u i ≤ c i) ∧ (∑ i ∈ s, u i) = k := by
  induction s using Finset.induction_on generalizing k with
  | empty =>
      have : k = 0 := by simpa using hk
      subst k
      exact ⟨fun _ => 0, by simp⟩
  | @insert a s ha ih =>
      have hk' : k ≤ c a + ∑ i ∈ s, c i := by simpa [Finset.sum_insert ha] using hk
      obtain ⟨u, hu, hsum⟩ := ih (k - min k (c a)) (by omega)
      refine ⟨Function.update u a (min k (c a)), ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · simp
        · simp only [Function.update_of_ne (ne_of_mem_of_not_mem hi ha)]
          exact hu i hi
      · rw [Finset.sum_insert ha]
        have hupdate : ∑ i ∈ s, Function.update u a (min k (c a)) i = ∑ i ∈ s, u i := by
          apply Finset.sum_congr rfl
          intro i hi
          exact Function.update_of_ne (ne_of_mem_of_not_mem hi ha) _ _
        rw [hupdate]
        simp only [Function.update_self]
        omega

/-- A zero-one sum on `d + 1` coordinates cannot exceed `k ≥ d` if its parity is `k`'s. -/
theorem bit_sum_le {d k : ℕ} (e : Fin (d + 1) → ℕ)
    (he : ∀ i, e i ≤ 1) (hdk : d ≤ k) (hpar : (∑ i, e i) % 2 = k % 2) :
    ∑ i, e i ≤ k := by
  have hbound : (∑ i, e i) ≤ d + 1 := by
    calc
      (∑ i, e i) ≤ ∑ _ : Fin (d + 1), 1 := Finset.sum_le_sum (fun i _ => he i)
      _ = d + 1 := by simp
  omega

/-- Full homogeneous-coordinate simplex parity allocation.

`m` is an interior integral point of the sum of simplices of degrees `k` and `l`.
The requested parity `e` includes the zeroth homogeneous coordinate; its sum must
therefore have the parity of `k`. The dimension is arbitrary.
-/
theorem simplex_parity_homogeneous {d k l : ℕ}
    (hdk : d ≤ k) (hdl : d ≤ l)
    (m e : Fin (d + 1) → ℕ)
    (hm : ∀ i, 0 < m i) (he : ∀ i, e i ≤ 1)
    (hsum : ∑ i, m i = k + l)
    (hpar : (∑ i, e i) % 2 = k % 2) :
    ∃ a b : Fin (d + 1) → ℕ,
      (∀ i, a i + b i = m i) ∧
      (∑ i, a i) = k ∧ (∑ i, b i) = l ∧
      (∀ i, a i % 2 = e i) := by
  let c : Fin (d + 1) → ℕ := fun i => (m i - e i) / 2
  let f : Fin (d + 1) → ℕ := fun i => (m i - e i) % 2
  have hef : ∀ i, e i + 2 * c i + f i = m i := by
    intro i
    dsimp [c, f]
    have := Nat.mod_add_div (m i - e i) 2
    have := hm i
    have := he i
    omega
  have hf : ∀ i, f i ≤ 1 := by
    intro i
    dsimp [f]
    omega
  have htotal : (∑ i, e i) + 2 * (∑ i, c i) + (∑ i, f i) = k + l := by
    calc
      _ = ∑ i, (e i + 2 * c i + f i) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ = ∑ i, m i := Finset.sum_congr rfl (fun i _ => hef i)
      _ = k + l := hsum
  have hE : (∑ i, e i) ≤ k := bit_sum_le e he hdk hpar
  have hFpar : (∑ i, f i) % 2 = l % 2 := by omega
  have hF : (∑ i, f i) ≤ l := bit_sum_le f hf hdl hFpar
  have hK : k = (∑ i, e i) + 2 * ((k - ∑ i, e i) / 2) := by omega
  have hcap : (k - ∑ i, e i) / 2 ≤ ∑ i, c i := by omega
  obtain ⟨u, hu, husum⟩ := allocate_le_sum Finset.univ c ((k - ∑ i, e i) / 2) hcap
  let a : Fin (d + 1) → ℕ := fun i => e i + 2 * u i
  have ha : ∀ i, a i ≤ m i := by
    intro i
    have := hu i (Finset.mem_univ i)
    have := hef i
    dsimp [a]
    omega
  refine ⟨a, fun i => m i - a i, ?_, ?_, ?_, ?_⟩
  · intro i
    change a i + (m i - a i) = m i
    have := ha i
    omega
  · dsimp [a]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, husum]
    omega
  · have hasum : ∑ i, a i = k := by
      dsimp [a]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, husum]
      omega
    rw [Finset.sum_tsub_distrib Finset.univ (fun i _ => ha i), hsum, hasum]
    omega
  · intro i
    have := he i
    dsimp [a]
    omega

/-- Integral points of the standard affine simplex of degree `k`. -/
def NatSimplex {d : ℕ} (k : ℕ) (a : Fin d → ℕ) : Prop := ∑ i, a i ≤ k

/-- Affine-coordinate version of Lemma 4.4, including all dimensions.
The strict inequalities on `m` are exactly the interior inequalities of
`(k + l) Δ_d`. The requested residue vector is unrestricted.
-/
theorem simplex_parity_affine {d k l : ℕ}
    (hdk : d ≤ k) (hdl : d ≤ l)
    (m r : Fin d → ℕ)
    (hm : ∀ i, 0 < m i) (hmsum : (∑ i, m i) < k + l) :
    ∃ a b : Fin d → ℕ,
      NatSimplex k a ∧ NatSimplex l b ∧
      (∀ i, a i + b i = m i) ∧
      (∀ i, a i % 2 = r i % 2) := by
  let e : Fin d → ℕ := fun i => r i % 2
  have he : ∀ i, e i ≤ 1 := by
    intro i
    dsimp [e]
    omega
  have hEsum : (∑ i, e i) ≤ k := by
    calc
      (∑ i, e i) ≤ ∑ _ : Fin d, 1 := Finset.sum_le_sum (fun i _ => he i)
      _ = d := by simp
      _ ≤ k := hdk
  let m' : Fin (d + 1) → ℕ := Fin.cons (k + l - ∑ i, m i) m
  let e' : Fin (d + 1) → ℕ := Fin.cons ((k - ∑ i, e i) % 2) e
  have hm' : ∀ i, 0 < m' i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [m', Fin.cons_zero]
      omega
    · simpa [m'] using hm j
  have he' : ∀ i, e' i ≤ 1 := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [e', Fin.cons_zero]
      omega
    · simpa [e'] using he j
  have hmsum' : ∑ i, m' i = k + l := by
    simp only [Fin.sum_univ_succ, m', Fin.cons_zero, Fin.cons_succ]
    omega
  have hepar' : (∑ i, e' i) % 2 = k % 2 := by
    simp only [Fin.sum_univ_succ, e', Fin.cons_zero, Fin.cons_succ]
    omega
  obtain ⟨a', b', hab', ha', hb', hpar'⟩ :=
    simplex_parity_homogeneous hdk hdl m' e' hm' he' hmsum' hepar'
  refine ⟨fun i => a' i.succ, fun i => b' i.succ, ?_, ?_, ?_, ?_⟩
  · change (∑ i : Fin d, a' i.succ) ≤ k
    rw [Fin.sum_univ_succ] at ha'
    omega
  · change (∑ i : Fin d, b' i.succ) ≤ l
    rw [Fin.sum_univ_succ] at hb'
    omega
  · intro i
    simpa [m'] using hab' i.succ
  · intro i
    simpa [e', e] using hpar' i.succ

/-- The actual integer-coordinate inequalities for the degree-`k` standard simplex. -/
def IntegerSimplex {d : ℕ} (k : ℕ) (a : Fin d → ℤ) : Prop :=
  (∀ i, 0 ≤ a i) ∧ (∑ i, a i) ≤ k

/-- Coordinate congruence is exactly membership of the difference in the
doubled integer lattice; this identifies the residue condition with `M / 2M`. -/
theorem integer_parity_iff_double {ι : Type*} (a α : ι → ℤ) :
    (∀ i, (a i - α i) % 2 = 0) ↔ ∃ w : ι → ℤ, a - α = w + w := by
  constructor
  · intro h
    refine ⟨fun i => (a i - α i) / 2, ?_⟩
    funext i
    have hi := h i
    simp only [Pi.sub_apply, Pi.add_apply]
    omega
  · rintro ⟨w, hw⟩ i
    have hi := congrFun hw i
    simp only [Pi.sub_apply, Pi.add_apply] at hi
    omega

/-- Natural-coordinate simplex points and their integer embeddings agree exactly. -/
theorem natSimplex_iff_integerSimplex {d k : ℕ} (a : Fin d → ℕ) :
    NatSimplex k a ↔ IntegerSimplex k (fun i => (a i : ℤ)) := by
  simp [NatSimplex, IntegerSimplex, ← Nat.cast_sum]

/-- Lemma 4.4 in the ambient integer lattice, with unrestricted integer parity classes. -/
theorem simplex_parity_integer {d k l : ℕ}
    (hdk : d ≤ k) (hdl : d ≤ l)
    (m α : Fin d → ℤ)
    (hm : ∀ i, 0 < m i) (hmsum : (∑ i, m i) < (k + l : ℕ)) :
    ∃ a b : Fin d → ℤ,
      IntegerSimplex k a ∧ IntegerSimplex l b ∧
      (∀ i, a i + b i = m i) ∧
      (∀ i, (a i - α i) % 2 = 0) := by
  let mN : Fin d → ℕ := fun i => (m i).toNat
  let rN : Fin d → ℕ := fun i => (α i % 2).toNat
  have hmN : ∀ i, 0 < mN i := by
    intro i
    dsimp [mN]
    have h := hm i
    omega
  have hmcast : ∀ i, (mN i : ℤ) = m i := by
    intro i
    dsimp [mN]
    exact Int.toNat_of_nonneg (le_of_lt (hm i))
  have hmNsum : (∑ i, mN i) < k + l := by
    have hsumcast : ((∑ i, mN i : ℕ) : ℤ) = ∑ i, m i := by
      simp only [Nat.cast_sum, hmcast]
    omega
  obtain ⟨aN, bN, haN, hbN, habN, hparN⟩ :=
    simplex_parity_affine hdk hdl mN rN hmN hmNsum
  refine ⟨fun i => (aN i : ℤ), fun i => (bN i : ℤ),
    (natSimplex_iff_integerSimplex aN).mp haN,
    (natSimplex_iff_integerSimplex bN).mp hbN, ?_, ?_⟩
  · intro i
    change (aN i : ℤ) + (bN i : ℤ) = m i
    have h := habN i
    have hc := hmcast i
    omega
  · intro i
    change ((aN i : ℤ) - α i) % 2 = 0
    have h := hparN i
    have hr : (rN i : ℤ) = α i % 2 := by
      dsimp [rN]
      exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
    omega

end PaperVerification.Toric
-- END PaperVerification.ToricSimplexParity
end

section
-- BEGIN PaperVerification.ToricSimplexGeometry
/-!
# Geometric correspondence for the simplex allocation theorem

Standard simplices are defined by their usual real coordinate inequalities.
Their actual topological interiors and integer points are related here to
`simplex_parity_integer`; in particular, no interior hypothesis is replaced
by an unexplained arithmetic proxy.
-/

noncomputable section

namespace PaperVerification.Toric

open scoped BigOperators Pointwise

/-- The standard degree-`k` simplex in real affine coordinates. -/
def RealSimplex (d : ℕ) (k : ℝ) : Set (Fin d → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ k}

/-- The coordinate simplex is precisely the convex hull of the origin and scaled
standard basis vectors. This identifies `RealSimplex d k` with the paper's `k Δ_d`. -/
theorem realSimplex_eq_convexHull {d : ℕ} {k : ℝ} (hk : 0 < k) :
    RealSimplex d k =
      convexHull ℝ (insert (0 : Fin d → ℝ) (Set.range fun i => Pi.single i k)) := by
  have hconv : Convex ℝ (RealSimplex d k) := by
    intro x hx y hy a b ha hb hab
    refine ⟨fun i => add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i)), ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    have hx' := mul_le_mul_of_nonneg_left hx.2 ha
    have hy' := mul_le_mul_of_nonneg_left hy.2 hb
    nlinarith
  have hverts : insert (0 : Fin d → ℝ) (Set.range fun i => Pi.single i k) ⊆
      RealSimplex d k := by
    rintro x (rfl | ⟨i, rfl⟩)
    · exact ⟨fun _ => le_rfl, by simpa using hk.le⟩
    · refine ⟨?_, ?_⟩
      · intro j
        simp only [Pi.single_apply]
        split_ifs <;> positivity
      · simp
  refine Set.Subset.antisymm ?_ (convexHull_min hverts hconv)
  intro x hx
  let w : Fin (d + 1) → ℝ := Fin.cons (1 - (∑ i, x i) / k) (fun i => x i / k)
  let v : Fin (d + 1) → (Fin d → ℝ) := Fin.cons 0 (fun i => Pi.single i k)
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change 0 ≤ 1 - (∑ i, x i) / k
      exact sub_nonneg.mpr ((div_le_one hk).mpr hx.2)
    · change 0 ≤ x j / k
      exact div_nonneg (hx.1 j) hk.le
  have hwsum : ∑ i, w i = 1 := by
    simp only [Fin.sum_univ_succ, w, Fin.cons_zero, Fin.cons_succ,
      ← Finset.sum_div]
    ring
  have hv : ∀ i, v i ∈ insert (0 : Fin d → ℝ) (Set.range fun i => Pi.single i k) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Set.mem_insert 0 _
    · exact Set.mem_insert_of_mem _ (Set.mem_range_self j)
  have hwv : ∑ i, w i • v i = x := by
    ext j
    simp [Fin.sum_univ_succ, w, v, Pi.single_apply, Finset.sum_apply, hk.ne']
  exact mem_convexHull_of_exists_fintype w v hw hwsum hv hwv

private def coordinateSum (d : ℕ) : (Fin d → ℝ) →L[ℝ] ℝ :=
  ∑ i, ContinuousLinearMap.proj i

@[simp] private theorem coordinateSum_apply {d : ℕ} (x : Fin d → ℝ) :
    coordinateSum d x = ∑ i, x i := by
  simp [coordinateSum]

/-- Topological interior of the positive-dimensional standard simplex. -/
theorem interior_realSimplex (d : ℕ) (k : ℝ) :
    interior (RealSimplex (d + 1) k) =
      {x | (∀ i, 0 < x i) ∧ ∑ i, x i < k} := by
  have hcoord (i : Fin (d + 1)) :
      interior {x : Fin (d + 1) → ℝ | 0 ≤ x i} = {x | 0 < x i} := by
    have h :=
      ((isOpenMap_eval (X := fun _ : Fin (d + 1) => ℝ) i).preimage_interior_eq_interior_preimage
        (continuous_apply i) (Set.Ici (0 : ℝ))).symm
    rw [interior_Ici] at h
    simpa only [Set.preimage, Set.Ici, Set.Ioi, Function.eval, Set.mem_setOf_eq] using h
  have hsurj : Function.Surjective (coordinateSum (d + 1)) := by
    intro y
    exact ⟨Pi.single 0 y, by simp⟩
  have hsum :
      interior {x : Fin (d + 1) → ℝ | ∑ i, x i ≤ k} = {x | ∑ i, x i < k} := by
    have h :=
      ((coordinateSum (d + 1)).isOpenMap hsurj).preimage_interior_eq_interior_preimage
        (coordinateSum (d + 1)).continuous (Set.Iic k) |>.symm
    rw [interior_Iic] at h
    simpa only [Set.preimage, Set.Iic, Set.Iio, coordinateSum_apply, Set.mem_setOf_eq] using h
  have hset : RealSimplex (d + 1) k =
      (⋂ i, {x : Fin (d + 1) → ℝ | 0 ≤ x i}) ∩ {x | ∑ i, x i ≤ k} := by
    ext x
    simp [RealSimplex]
  rw [hset, interior_inter, interior_iInter_of_finite]
  simp_rw [hcoord, hsum]
  ext x
  simp

/-- Every point of the Minkowski sum satisfies the combined simplex inequalities. -/
theorem add_realSimplex_subset (d : ℕ) (k l : ℝ) :
    RealSimplex d k + RealSimplex d l ⊆ RealSimplex d (k + l) := by
  rintro x ⟨a, ha, b, hb, rfl⟩
  refine ⟨fun i => add_nonneg (ha.1 i) (hb.1 i), ?_⟩
  simpa only [Pi.add_apply, Finset.sum_add_distrib] using add_le_add ha.2 hb.2

/-- The integer and real coordinate definitions agree under the canonical embedding. -/
theorem integerSimplex_iff_realSimplex {d k : ℕ} (a : Fin d → ℤ) :
    IntegerSimplex k a ↔ (fun i => (a i : ℝ)) ∈ RealSimplex d k := by
  constructor
  · rintro ⟨ha, hs⟩
    refine ⟨fun i => Int.cast_nonneg_iff.mpr (ha i), ?_⟩
    have h : ((∑ i, a i : ℤ) : ℝ) ≤ ((k : ℤ) : ℝ) := Int.cast_le.mpr hs
    simpa only [Int.cast_sum, Int.cast_natCast] using h
  · rintro ⟨ha, hs⟩
    refine ⟨fun i => Int.cast_nonneg_iff.mp (ha i), ?_⟩
    have h : ((∑ i, a i : ℤ) : ℝ) ≤ ((k : ℤ) : ℝ) := by
      simpa only [Int.cast_sum, Int.cast_natCast] using hs
    exact Int.cast_le.mp h

/-- Lemma 4.4 stated with actual real simplices, topological interior of their
Minkowski sum, and the full integer lattice in every positive dimension. -/
theorem simplex_parity_topological {d k l : ℕ}
    (hd : 0 < d) (hdk : d ≤ k) (hdl : d ≤ l)
    (m α : Fin d → ℤ)
    (hm : (fun i => (m i : ℝ)) ∈
      interior (RealSimplex d k + RealSimplex d l)) :
    ∃ a b : Fin d → ℤ,
      (fun i => (a i : ℝ)) ∈ RealSimplex d k ∧
      (fun i => (b i : ℝ)) ∈ RealSimplex d l ∧
      (∀ i, a i + b i = m i) ∧
      (∀ i, (a i - α i) % 2 = 0) := by
  cases d with
  | zero => omega
  | succ d =>
      have hm' := interior_mono (add_realSimplex_subset (d + 1) k l) hm
      rw [interior_realSimplex] at hm'
      have hmpos : ∀ i, 0 < m i := by
        intro i
        have h : (0 : ℝ) < (m i : ℝ) := hm'.1 i
        exact Int.cast_pos.mp h
      have hmsum : (∑ i, m i) < (k + l : ℕ) := by
        have h := hm'.2
        push_cast at h ⊢
        exact_mod_cast h
      obtain ⟨a, b, ha, hb, hab, hpar⟩ :=
        simplex_parity_integer hdk hdl m α hmpos hmsum
      exact ⟨a, b, (integerSimplex_iff_realSimplex a).mp ha,
        (integerSimplex_iff_realSimplex b).mp hb, hab, hpar⟩

end PaperVerification.Toric
end
-- END PaperVerification.ToricSimplexGeometry
end

section
-- BEGIN PaperVerification.FiniteExponentialBalance
/-!
# Finite exponential balancing

An analytic ingredient of the determinant-minimization argument in the toric
lattice-covering lemma. A finite spanning configuration with a strictly positive
zero relation admits an exponential reweighting with zero barycenter.
-/

noncomputable section

namespace PaperVerification.Toric

open scoped BigOperators InnerProductSpace
open Filter Topology

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Sum of positive parts of the configuration's directional inner products. -/
def positivePartSum (v : ι → E) (x : E) : ℝ := ∑ i, max ⟪v i, x⟫_ℝ 0

lemma positivePartSum_nonneg (v : ι → E) (x : E) : 0 ≤ positivePartSum v x :=
  Finset.sum_nonneg (fun i _ => le_max_right _ _)

lemma positivePartSum_continuous (v : ι → E) : Continuous (positivePartSum v) := by
  unfold positivePartSum
  exact continuous_finsetSum _ (fun i _ =>
    (continuous_const.inner continuous_id).max continuous_const)

lemma positivePartSum_smul (v : ι → E) (x : E) {a : ℝ} (ha : 0 ≤ a) :
    positivePartSum v (a • x) = a * positivePartSum v x := by
  simp only [positivePartSum, real_inner_smul_right, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [mul_zero] using (mul_max_of_nonneg ⟪v i, x⟫_ℝ 0 ha).symm

/-- A positive zero relation rules out a nonzero direction having all inner products nonpositive. -/
lemma positivePartSum_pos (v : ι → E)
    (hspan : Submodule.span ℝ (Set.range v) = ⊤)
    (p : ι → ℝ) (hp : ∀ i, 0 < p i) (hzero : ∑ i, p i • v i = 0)
    {x : E} (hx : x ≠ 0) : 0 < positivePartSum v x := by
  have hnonneg := positivePartSum_nonneg v x
  by_contra hnot
  have hsum : positivePartSum v x = 0 := le_antisymm (le_of_not_gt hnot) hnonneg
  have hmaxzero : (fun i => max ⟪v i, x⟫_ℝ 0) = 0 :=
    (Fintype.sum_eq_zero_iff_of_nonneg (fun i => le_max_right ⟪v i, x⟫_ℝ 0)).mp hsum
  have hmax : ∀ i, max ⟪v i, x⟫_ℝ 0 = 0 := fun i => congrFun hmaxzero i
  have hnonpos : ∀ i, ⟪v i, x⟫_ℝ ≤ 0 := fun i =>
    (le_max_left _ _).trans (hmax i).le
  have hweighted : ∑ i, p i * ⟪v i, x⟫_ℝ = 0 := by
    have h := congrArg (fun y : E => ⟪y, x⟫_ℝ) hzero
    simpa only [sum_inner, real_inner_smul_left, inner_zero_left] using h
  have htermzero : (fun i => p i * ⟪v i, x⟫_ℝ) = 0 :=
    (Fintype.sum_eq_zero_iff_of_nonpos
      (fun i => mul_nonpos_of_nonneg_of_nonpos (hp i).le (hnonpos i))).mp hweighted
  have hterm : ∀ i, p i * ⟪v i, x⟫_ℝ = 0 := fun i => congrFun htermzero i
  have hinner : ∀ i, ⟪v i, x⟫_ℝ = 0 := fun i =>
    (mul_eq_zero.mp (hterm i)).resolve_left (hp i).ne'
  have hspaninner : ∀ y ∈ Submodule.span ℝ (Set.range v), ⟪y, x⟫_ℝ = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        exact hinner i
    | zero => simp
    | add y z hy hz hy' hz' => simp [inner_add_left, hy', hz']
    | smul a y hy hy' => simp [real_inner_smul_left, hy']
  have hxspan : x ∈ Submodule.span ℝ (Set.range v) := by
    rw [hspan]
    exact Submodule.mem_top
  have hself := hspaninner x hxspan
  exact hx ((inner_self_eq_zero (𝕜 := ℝ)).mp hself)

/-- Uniform linear growth of the positive-part support function. -/
lemma positivePartSum_lower_bound [FiniteDimensional ℝ E] [Nontrivial E]
    (v : ι → E) (hspan : Submodule.span ℝ (Set.range v) = ⊤)
    (p : ι → ℝ) (hp : ∀ i, 0 < p i) (hzero : ∑ i, p i • v i = 0) :
    ∃ ε > 0, ∀ x : E, ε * ‖x‖ ≤ positivePartSum v x := by
  have hsne : (Metric.sphere (0 : E) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr (by norm_num)
  obtain ⟨u, hu, hmin⟩ :=
    (isCompact_sphere (0 : E) 1).exists_isMinOn hsne
      (positivePartSum_continuous v).continuousOn
  have hunorm : ‖u‖ = 1 := by simpa using hu
  have hu0 : u ≠ 0 := by intro h; simp [h] at hunorm
  refine ⟨positivePartSum v u, positivePartSum_pos v hspan p hp hzero hu0, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp [hx, positivePartSum]
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hxunit : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : E) 1 := by
    simp [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hnorm.le), hnorm.ne']
  have h : positivePartSum v u ≤ positivePartSum v (‖x‖⁻¹ • x) := hmin hxunit
  rw [positivePartSum_smul v x (inv_nonneg.mpr hnorm.le)] at h
  have hmul := mul_le_mul_of_nonneg_right h hnorm.le
  simpa [mul_assoc, mul_comm, mul_left_comm, hnorm.ne'] using hmul

/-- A finite positive exponential sum. -/
def exponentialSum (v : ι → E) (d : ι → ℝ) (x : E) : ℝ :=
  ∑ i, d i * Real.exp ⟪v i, x⟫_ℝ

lemma exponentialSum_continuous (v : ι → E) (d : ι → ℝ) :
    Continuous (exponentialSum v d) := by
  unfold exponentialSum
  exact continuous_finsetSum _ (fun i _ =>
    continuous_const.mul (continuous_const.inner continuous_id).rexp)

/-- The balancing theorem for a configuration spanning its ambient real inner-product space. -/
theorem finite_exponential_balance [FiniteDimensional ℝ E] [Nonempty ι]
    (v : ι → E) (hspan : Submodule.span ℝ (Set.range v) = ⊤)
    (p : ι → ℝ) (hp : ∀ i, 0 < p i) (hzero : ∑ i, p i • v i = 0)
    (d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    ∃ x : E, ∑ i, (d i * Real.exp ⟪v i, x⟫_ℝ) • v i = 0 := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · letI := hE
    exact ⟨0, Subsingleton.elim _ _⟩
  letI := hE
  obtain ⟨ε, hε, hbound⟩ := positivePartSum_lower_bound v hspan p hp hzero
  obtain ⟨i₀, hi₀⟩ := Finite.exists_min d
  have hcoeff : 0 < d i₀ * ε := mul_pos (hd i₀) hε
  have hlower : ∀ x, d i₀ * ε * ‖x‖ ≤ exponentialSum v d x := by
    intro x
    calc
      d i₀ * ε * ‖x‖ ≤ d i₀ * positivePartSum v x := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hbound x) (hd i₀).le
      _ = ∑ i, d i₀ * max ⟪v i, x⟫_ℝ 0 := by rw [positivePartSum, Finset.mul_sum]
      _ ≤ exponentialSum v d x := by
        apply Finset.sum_le_sum
        intro i _
        have he : max ⟪v i, x⟫_ℝ 0 ≤ Real.exp ⟪v i, x⟫_ℝ := by
          refine max_le ?_ (Real.exp_pos _).le
          linarith [Real.add_one_le_exp ⟪v i, x⟫_ℝ]
        exact mul_le_mul (hi₀ i) he (le_max_right _ _) (hd i).le
  have hlim : Tendsto (exponentialSum v d) (cocompact E) atTop :=
    tendsto_atTop_mono hlower
      (Tendsto.const_mul_atTop hcoeff tendsto_norm_cocompact_atTop)
  obtain ⟨x, hxmin⟩ := (exponentialSum_continuous v d).exists_forall_le hlim
  let g : E := ∑ i, (d i * Real.exp ⟪v i, x⟫_ℝ) • v i
  have hlocal : IsLocalMin (fun t : ℝ => exponentialSum v d (x + t • g)) 0 := by
    exact Filter.Eventually.of_forall (fun t => by simpa using hxmin (x + t • g))
  have hpath : HasDerivAt (fun t : ℝ => x + t • g) g 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const g).const_add x
  have hderiv : HasDerivAt (fun t : ℝ => exponentialSum v d (x + t • g))
      ⟪g, g⟫_ℝ 0 := by
    have hi (i : ι) : HasDerivAt
        (fun t : ℝ => d i * Real.exp ⟪v i, x + t • g⟫_ℝ)
        ((d i * Real.exp ⟪v i, x⟫_ℝ) * ⟪v i, g⟫_ℝ) 0 := by
      have hi' : HasDerivAt (fun t : ℝ => ⟪v i, x + t • g⟫_ℝ) ⟪v i, g⟫_ℝ 0 := by
        simpa using (hasDerivAt_const (0 : ℝ) (v i)).inner ℝ hpath
      simpa [mul_assoc] using hi'.exp.const_mul (d i)
    have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)
    simpa only [exponentialSum, g, sum_inner, real_inner_smul_left] using hs
  refine ⟨x, ?_⟩
  exact (inner_self_eq_zero (𝕜 := ℝ)).mp (hlocal.hasDerivAt_eq_zero hderiv)

/-- The same balancing theorem in the span of the configuration. This removes
any unnecessary full-dimensionality assumption on the ambient space. -/
theorem finite_exponential_balance_in_span [FiniteDimensional ℝ E] [Nonempty ι]
    (v : ι → E)
    (p : ι → ℝ) (hp : ∀ i, 0 < p i) (hzero : ∑ i, p i • v i = 0)
    (d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    ∃ x : E, ∑ i, (d i * Real.exp ⟪v i, x⟫_ℝ) • v i = 0 := by
  let W : Submodule ℝ E := Submodule.span ℝ (Set.range v)
  have hv : ∀ i, v i ∈ W := fun i => Submodule.subset_span ⟨i, rfl⟩
  let vW : ι → W := fun i => ⟨v i, hv i⟩
  have hspan : Submodule.span ℝ (Set.range vW) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff W hv).mpr rfl
  have hzeroW : ∑ i, p i • vW i = 0 := by
    apply Subtype.ext
    simpa [vW] using hzero
  obtain ⟨x, hx⟩ := finite_exponential_balance vW hspan p hp hzeroW d hd
  refine ⟨x, ?_⟩
  have h := congrArg (fun z : W => (z : E)) hx
  simpa [vW] using h

/-- A strictly positive convex combination is the barycenter of a suitable
exponential reweighting with any prescribed positive base coefficients.

This is the finite-dimensional analytic step behind the log-determinant
argument: the points will be the incidence vectors of all vector-space bases. -/
theorem finite_exponential_barycenter [FiniteDimensional ℝ E] [Nonempty ι]
    (v : ι → E) (p : ι → ℝ) (hp : ∀ i, 0 < p i) (hpsum : ∑ i, p i = 1)
    (d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    ∃ x : E, ∑ i, (d i * Real.exp ⟪v i, x⟫_ℝ) •
      (v i - ∑ j, p j • v j) = 0 := by
  let c : E := ∑ j, p j • v j
  have hzero : ∑ i, p i • (v i - c) = 0 := by
    simp [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hpsum, c]
  obtain ⟨x, hx⟩ := finite_exponential_balance_in_span
    (fun i => v i - c) p hp hzero d hd
  refine ⟨x, ?_⟩
  have h := congrArg (fun z : E => Real.exp ⟪c, x⟫_ℝ • z) hx
  rw [smul_zero, Finset.smul_sum] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul, inner_sub_left]
  congr 1
  calc
    d i * Real.exp ⟪v i, x⟫_ℝ =
        d i * (Real.exp ⟪c, x⟫_ℝ *
          Real.exp (⟪v i, x⟫_ℝ - ⟪c, x⟫_ℝ)) := by
            rw [← Real.exp_add]
            congr 2
            ring
    _ = _ := by ring

end PaperVerification.Toric
end
-- END PaperVerification.FiniteExponentialBalance
end

#eval "TORIC_DICTIONARY_PART_04_EOF"
