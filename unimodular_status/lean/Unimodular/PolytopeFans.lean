module

public import Unimodular.FanBridge
public import Unimodular.Geometry

@[expose] public section

noncomputable section

open Set TauCeti.Toric
open scoped Pointwise Topology BigOperators

attribute [local instance] Classical.propDecidable

namespace Unimodular.FanBridge

variable {n : ℕ}

/-- A full integral basis generates a genuine regular rational salient cone. -/
theorem basisCone_isRegular (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    IsRegularCone (standardEmbedding n) (ConeBases.cone (ι := standardEmbedding n) b) := by
  simpa only [ConeBases.cone, Set.image_univ, ← Set.range_comp, Function.comp_def] using
    isRegularCone_hull_image_basis (standardEmbedding_isIntegralLattice n) b Set.univ

def generatingCones (σ : SmoothCompleteFan n) : Set (PointedCone ℝ (Ambient n)) :=
  (fun b => ConeBases.cone (ι := standardEmbedding n) b) ''
    (σ.maximal : Set (Module.Basis (Fin n) ℤ (Lattice n)))

theorem generatingCones_finite (σ : SmoothCompleteFan n) : (generatingCones σ).Finite :=
  σ.maximal.finite_toSet.image _

theorem generatingCones_regular (σ : SmoothCompleteFan n) {C : PointedCone ℝ (Ambient n)}
    (hC : C ∈ generatingCones σ) : IsRegularCone (standardEmbedding n) C := by
  obtain ⟨b, _, rfl⟩ := hC
  exact basisCone_isRegular b

theorem generatingCones_intersection (σ : SmoothCompleteFan n)
    {C D : PointedCone ℝ (Ambient n)} (hC : C ∈ generatingCones σ)
    (hD : D ∈ generatingCones σ) : (C ⊓ D).IsFaceOf C := by
  obtain ⟨b, hb, rfl⟩ := hC
  obtain ⟨c, hc, rfl⟩ := hD
  obtain ⟨A, _, hA, _⟩ := σ.intersection b hb c hc
  have he : ConeBases.cone (ι := standardEmbedding n) b ⊓
      ConeBases.cone (ι := standardEmbedding n) c =
      PointedCone.hull ℝ (standardEmbedding n '' (b '' (A : Set (Fin n)))) := by
    apply SetLike.coe_injective
    simpa only [basisCone_eq_cone, basisFace_eq_hull, Submodule.coe_inf] using hA
  rw [he, Set.image_image]
  exact PointedCone.isFaceOf_hull_image
    ((standardEmbedding_isIntegralLattice n).linearIndependent_basis b) rfl (A : Set (Fin n))

end Unimodular.FanBridge

namespace Unimodular.SmoothCompleteFan

open FanBridge

variable {n : ℕ} (σ : SmoothCompleteFan n)

/-- The actual TauCeti fan underlying a coordinate presentation. Its cones are
all actual faces of the listed integral-basis cones. -/
def toToricFan : Fan (standardEmbedding n) :=
  Fan.ofCones (standardEmbedding_isIntegralLattice n) (generatingCones σ)
    (generatingCones_finite σ) (fun _ h => (generatingCones_regular σ h).toIsToricCone)
    (fun _ _ hC hD => generatingCones_intersection σ hC hD)

theorem mem_toToricFan_cones_iff (C : PointedCone ℝ (Ambient n)) :
    C ∈ σ.toToricFan.cones ↔ ∃ D ∈ generatingCones σ, C.IsFaceOf D :=
  Fan.mem_ofCones_cones (standardEmbedding_isIntegralLattice n) (generatingCones σ)
    (generatingCones_finite σ) (fun _ h => (generatingCones_regular σ h).toIsToricCone)
    (fun _ _ hC hD => generatingCones_intersection σ hC hD)

theorem basisCone_mem_toToricFan {b : Module.Basis (Fin n) ℤ (Lattice n)}
    (hb : b ∈ σ.maximal) : ConeBases.cone (ι := standardEmbedding n) b ∈ σ.toToricFan.cones :=
  (σ.mem_toToricFan_cones_iff _).mpr
    ⟨_, ⟨b, hb, rfl⟩, PointedCone.IsFaceOf.refl _⟩

theorem toToricFan_complete : σ.toToricFan.IsComplete := by
  apply (Fan.isComplete_iff _).2
  intro x
  obtain ⟨b, hb, hx⟩ := σ.complete x
  refine ⟨_, σ.basisCone_mem_toToricFan hb, ?_⟩
  change x ∈ (ConeBases.cone (ι := standardEmbedding n) b : Set (Ambient n))
  rw [← basisCone_eq_cone]
  exact hx

theorem toToricFan_regular : σ.toToricFan.IsRegular := by
  apply Fan.isRegular_iff.mpr
  intro C hC
  obtain ⟨D, ⟨b, hb, rfl⟩, hC⟩ := (σ.mem_toToricFan_cones_iff C).mp hC
  exact (basisCone_isRegular b).of_isFaceOf hC

/-- Passing from the coordinate presentation to actual cones preserves precisely
the primitive ray vectors, including their signs. -/
@[simp] theorem toToricFan_ray_iff (u : Lattice n) :
    ConeBases.IsRay σ.toToricFan u ↔ u ∈ σ.rays := by
  constructor
  · rintro ⟨C, hC, ρ, hu⟩
    obtain ⟨D, ⟨b, hb, rfl⟩, hC⟩ := (σ.mem_toToricFan_cones_iff C).mp hC
    have hu' := (isPrimitiveGenerator_faceEmbedding hC ρ).2 hu
    obtain ⟨i, hi⟩ := ConeBases.primitive_generator_eq_basis
      (standardEmbedding_isIntegralLattice n) b _ hu'
    exact ⟨b, hb, i, hi⟩
  · rintro ⟨b, hb, i, rfl⟩
    exact ConeBases.isRay_basis σ.toToricFan b (σ.basisCone_mem_toToricFan hb) i

/-- The basis-coordinate condition has identical content in the two presentations.
The reverse direction uses maximality of a full-dimensional cone, not an assumed
identification of arbitrary ordered bases. -/
theorem toToricFan_positiveCriterion_iff :
    ConeBases.PositiveCriterion σ.toToricFan ↔ σ.PositiveCoordinateCriterion := by
  constructor
  · intro h b hb u hu
    exact h n b (σ.basisCone_mem_toToricFan hb) u ((σ.toToricFan_ray_iff u).2 hu)
  · intro h m b hb u hu
    have hb' := hb
    obtain ⟨D, ⟨c, hc, rfl⟩, hbc⟩ := (σ.mem_toToricFan_cones_iff _).mp hb
    have he : ConeBases.cone (ι := standardEmbedding n) b =
        ConeBases.cone (ι := standardEmbedding n) c :=
      (FanMaximalCones.full_iff_maximal σ.toToricFan σ.toToricFan_complete hb').1
        (ConeBases.span_cone (standardEmbedding_isIntegralLattice n) b)
        _ (σ.basisCone_mem_toToricFan hc) hbc.le
    rw [ConeBases.positive_sum_eq_of_cone_eq (standardEmbedding_isIntegralLattice n) b c he u]
    exact h c hc u ((σ.toToricFan_ray_iff u).1 hu)

end Unimodular.SmoothCompleteFan

namespace Unimodular.SmoothReflexivePresentation

open FanBridge

variable {n : ℕ} (P : SmoothReflexivePresentation n)

/-- The ordinary real normal cone at a listed vertex: all linear functionals
maximized at that vertex on the actual convex polytope. -/
def normalConeAt (v : {v // v ∈ P.vertices}) : Set (Ambient n) :=
  {x | ∀ p ∈ P.carrier, realPairing p x ≤ realPairing (embed v.val) x}

theorem basisCone_maximizes (v : {v // v ∈ P.vertices}) {x : Ambient n}
    (hx : x ∈ basisCone (P.basis v)) : x ∈ P.normalConeAt v := by
  intro p hp
  have hx' := (mem_basisCone_iff (P.basis v) x).1 hx
  rw [realPairing_eq_coordinates (P.basis v), realPairing_eq_coordinates (P.basis v)]
  apply Finset.sum_le_sum
  intro i _
  rw [P.basis_active]
  exact mul_le_mul_of_nonneg_left
    ((P.mem_carrier_iff p).1 hp _ (P.basis_mem v i)) (hx' i)

/-- The cone of active primitive normals is exactly the actual normal cone.
The converse follows by a feasible inward step when a basis coefficient is negative. -/
theorem basisCone_eq_normalConeAt (v : {v // v ∈ P.vertices}) :
    basisCone (P.basis v) = P.normalConeAt v := by
  apply Set.Subset.antisymm (fun _ hx => P.basisCone_maximizes v hx)
  intro x hx
  apply (mem_basisCone_iff (P.basis v) x).2
  intro i
  by_contra hi
  have hneg : realCoordinates (P.basis v) x i < 0 := lt_of_not_ge hi
  let d : Ambient n := dualCorner (P.basis v) (Pi.single i (-1))
  have hd : realPairing d x = -realCoordinates (P.basis v) x i := by
    rw [realPairing_dualCorner]
    simp [Pi.single_apply]
  obtain ⟨t, ht, htall⟩ := exists_pos_feasible_step P.normals
    (fun u => 1 - pairing (embed v.val) u) (fun u => pairing d u)
    (fun u hu => sub_nonneg.mpr ((P.mem_carrier_iff _).1 (P.vertex_mem v) u hu))
    (by
      intro u hu he
      obtain ⟨j, rfl⟩ := P.active_subset v u hu (sub_eq_zero.mp he).symm
      rw [pairing_dualCorner_basis]
      simp [Pi.single_apply]
      split_ifs <;> norm_num)
  have hp : embed v.val + t • d ∈ P.carrier := by
    apply (P.mem_carrier_iff _).2
    intro u hu
    rw [pairing_add_left, pairing_smul_left]
    linarith [htall u hu]
  have hmax := hx _ hp
  rw [realPairing_add_left, realPairing_smul_left, hd] at hmax
  have hpos : 0 < t * (-realCoordinates (P.basis v) x i) := mul_pos ht (neg_pos.mpr hneg)
  linarith

/-- Indices of the normals active at both selected vertices. -/
def commonActive (v w : {v // v ∈ P.vertices}) : Finset (Fin n) :=
  Finset.univ.filter (fun i => pairing (embed w.val) (P.basis v i) = 1)

@[simp] theorem mem_commonActive (v w : {v // v ∈ P.vertices}) (i : Fin n) :
    i ∈ P.commonActive v w ↔ pairing (embed w.val) (P.basis v i) = 1 := by
  simp [commonActive]

/-- Two vertex normal cones meet in precisely their common active-normal face. -/
theorem basisCone_intersection (v w : {v // v ∈ P.vertices}) :
    basisCone (P.basis v) ∩ basisCone (P.basis w) =
      basisFace (P.basis v) (P.commonActive v w) := by
  classical
  ext x
  constructor
  · rintro ⟨hxv, hxw⟩
    have hcoeff := (mem_basisCone_iff (P.basis v) x).1 hxv
    have he : realPairing (embed v.val) x = realPairing (embed w.val) x :=
      le_antisymm (P.basisCone_maximizes w hxw _ (P.vertex_mem v))
        (P.basisCone_maximizes v hxv _ (P.vertex_mem w))
    have hnonneg (i : Fin n) : 0 ≤ realCoordinates (P.basis v) x i *
        (1 - pairing (embed w.val) (P.basis v i)) :=
      mul_nonneg (hcoeff i)
        (sub_nonneg.mpr ((P.mem_carrier_iff _).1 (P.vertex_mem w) _ (P.basis_mem v i)))
    have hsum : ∑ i, realCoordinates (P.basis v) x i *
        (1 - pairing (embed w.val) (P.basis v i)) = 0 := by
      simp_rw [mul_sub, mul_one]
      rw [Finset.sum_sub_distrib]
      have hv : realPairing (embed v.val) x = ∑ i, realCoordinates (P.basis v) x i := by
        rw [realPairing_eq_coordinates (P.basis v)]
        simp only [P.basis_active, mul_one]
      rw [← hv, ← realPairing_eq_coordinates (P.basis v), he, sub_self]
    refine ⟨realCoordinates (P.basis v) x, hcoeff, ?_, sum_basis_realCoordinates _ _⟩
    intro i hi
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).1 hsum i
      (Finset.mem_univ i)
    have hneq : 1 - pairing (embed w.val) (P.basis v i) ≠ 0 := by
      intro hz
      apply hi
      exact (P.mem_commonActive v w i).2 (sub_eq_zero.mp hz).symm
    exact (mul_eq_zero.mp hzero).resolve_right hneq
  · intro hx
    have hxv : x ∈ basisCone (P.basis v) := by
      obtain ⟨c, hc, _, he⟩ := hx
      exact ⟨c, hc, he⟩
    refine ⟨hxv, ?_⟩
    rw [basisCone_eq_cone]
    rw [basisFace_eq_hull] at hx
    have hle : PointedCone.hull ℝ
        (standardEmbedding n '' (P.basis v '' (P.commonActive v w : Set (Fin n)))) ≤
        ConeBases.cone (ι := standardEmbedding n) (P.basis w) := by
      apply Submodule.span_le.2
      rintro _ ⟨u, ⟨i, hi, rfl⟩, rfl⟩
      obtain ⟨j, hj⟩ := P.active_subset w (P.basis v i) (P.basis_mem v i)
        ((P.mem_commonActive v w i).1 hi)
      rw [← hj]
      exact PointedCone.subset_hull ⟨j, rfl⟩
    exact hle hx

/-- The coordinate fan is constructed from the actual vertex normal cones.
Completeness and all face intersections are consequences of the polytope data. -/
def coordinateFan : SmoothCompleteFan n where
  maximal := P.vertices.attach.image P.basis
  complete := by
    intro x
    obtain ⟨v, hv⟩ := P.exists_nonnegative_basis_coordinates x
    exact ⟨P.basis v, Finset.mem_image.2 ⟨v, by simp, rfl⟩,
      (mem_basisCone_iff (P.basis v) x).2 hv⟩
  intersection := by
    intro b hb c hc
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.1 hc
    exact ⟨P.commonActive v w, P.commonActive w v, P.basisCone_intersection v w,
      by rw [Set.inter_comm]; exact P.basisCone_intersection w v⟩

@[simp] theorem coordinateFan_ray_iff (u : Lattice n) :
    u ∈ P.coordinateFan.rays ↔ u ∈ P.normals := by
  constructor
  · rintro ⟨b, hb, i, rfl⟩
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 hb
    exact P.basis_mem v i
  · intro hu
    obtain ⟨v, i, hi⟩ := P.normals_occur u hu
    exact ⟨P.basis v, Finset.mem_image.2 ⟨v, by simp, rfl⟩, i, hi⟩

theorem coordinateFan_positiveCriterion (hP : P.DeeplyMonotone) :
    P.coordinateFan.PositiveCoordinateCriterion := by
  intro b hb u hu
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 hb
  exact P.positive_coordinate_bound (P.deeplyMonotone_iff_unitCornersContained.1 hP) v u
    ((P.coordinateFan_ray_iff u).1 hu)

/-- The actual finite, complete, regular rational normal fan of the smooth
reflexive polytope, in its original integral lattice. -/
def normalFan : Fan (standardEmbedding n) := P.coordinateFan.toToricFan

theorem normalFan_complete : P.normalFan.IsComplete := P.coordinateFan.toToricFan_complete

theorem normalFan_regular : P.normalFan.IsRegular := P.coordinateFan.toToricFan_regular

@[simp] theorem normalFan_ray_iff (u : Lattice n) :
    ConeBases.IsRay P.normalFan u ↔ u ∈ P.normals := by
  exact (P.coordinateFan.toToricFan_ray_iff u).trans (P.coordinateFan_ray_iff u)

theorem normalFan_positiveCriterion (hP : P.DeeplyMonotone) :
    ConeBases.PositiveCriterion P.normalFan :=
  P.coordinateFan.toToricFan_positiveCriterion_iff.2 (P.coordinateFan_positiveCriterion hP)

/-- The fan consists exactly of faces of the actual vertex normal cones. -/
theorem mem_normalFan_cones_iff (C : PointedCone ℝ (Ambient n)) :
    C ∈ P.normalFan.cones ↔ ∃ v : {v // v ∈ P.vertices},
      C.IsFaceOf (ConeBases.cone (ι := standardEmbedding n) (P.basis v)) := by
  change C ∈ P.coordinateFan.toToricFan.cones ↔ _
  rw [P.coordinateFan.mem_toToricFan_cones_iff]
  constructor
  · rintro ⟨D, ⟨b, hb, rfl⟩, hC⟩
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 hb
    exact ⟨v, hC⟩
  · rintro ⟨v, hC⟩
    exact ⟨_, ⟨P.basis v, Finset.mem_image.2 ⟨v, by simp, rfl⟩, rfl⟩, hC⟩

end Unimodular.SmoothReflexivePresentation

end
