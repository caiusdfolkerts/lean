module

public import Continuation.Divisor.WeakFanFoundations
public import Recovery.Unimodular.NativePort.A3Geometry
public import Mathlib.Topology.Order.Basic

@[expose] public section

/-! The shared full-normal-fan proofs are imported from their single owner.
The strict-support construction below retains its original proof body. -/

/- Exact owned draft: StrictSupportNormalFan. -/
section NormalFanGeometry_StrictSupportNormalFan



/-!
UNVERIFIED EXTENSION DRAFT. Strict support values on the actual rays of a
complete fan produce an actual finite convex polytope having the whole fan
as its normal fan. The normal-cone equality is proved from the inequalities;
it is not a field of the input. The application to A3 must still construct
these support values from the six square choices.
-/

set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set

namespace Unimodular.StrictSupportNormalFan

open NormalFanSupport
open TauCeti.Toric

section Cones

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Nonnegativity and the zero-set face conclusion propagate from every
actual generator to its full conic hull. -/
theorem nonneg_and_zero_mem_hull (A : Set V) (C : PointedCone ℝ V)
    (f : V →ₗ[ℝ] ℝ)
    (hA : ∀ x ∈ A, 0 ≤ f x ∧ (f x = 0 → x ∈ C)) :
    ∀ x ∈ PointedCone.hull ℝ A, 0 ≤ f x ∧ (f x = 0 → x ∈ C) := by
  let K : PointedCone ℝ V :=
    { carrier := {x | 0 ≤ f x ∧ (f x = 0 → x ∈ C)}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        refine ⟨by simpa only [map_add] using add_nonneg hx.1 hy.1,?_⟩
        intro he
        rw [map_add] at he
        have hx0 : f x = 0 := by linarith [hx.1,hy.1]
        have hy0 : f y = 0 := by linarith [hx.1,hy.1]
        exact C.add_mem (hx.2 hx0) (hy.2 hy0)
      smul_mem' := by
        intro a x hx
        change 0 ≤ f ((a : ℝ) • x) ∧
          (f ((a : ℝ) • x) = 0 → (a : ℝ) • x ∈ C)
        rw [map_smul,smul_eq_mul]
        refine ⟨mul_nonneg a.property hx.1,?_⟩
        intro he
        rcases mul_eq_zero.mp he with ha | hx0
        · simp only [ha,zero_smul,C.zero_mem]
        · exact C.smul_mem a.property (hx.2 hx0) }
  have hle : PointedCone.hull ℝ A ≤ K := Submodule.span_le.mpr hA
  exact fun x hx => hle hx

end Cones

section Fans

variable {N V E : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : N →+ V} (Φ : Fan ι) (u : E → V)

/-- The input is ordinary ray support data: equality on rays in a full cone,
strict inequality on every other ray. No normal-cone assertion is assumed. -/
structure StrictSupportData where
  height : E → ℝ
  point : FullCone Φ → Module.Dual ℝ V
  on_ray : ∀ C e, u e ∈ C.val.val → point C (u e) = height e
  off_ray : ∀ C e, u e ∉ C.val.val → point C (u e) < height e

variable (d : StrictSupportData Φ u)

theorem point_le_height (C : FullCone Φ) (e : E) :
    d.point C (u e) ≤ d.height e := by
  by_cases he : u e ∈ C.val.val
  · exact (d.on_ray C e he).le
  · exact (d.off_ray C e he).le

/-- Exact full normal cones, derived from completeness and actual conic
generation. The strict off-cone inequalities force equality only on the
original cone, including when that cone is not simplicial. -/
theorem normalCone_eq_full (hcomplete : Φ.IsComplete)
    (hgen : ∀ C ∈ Φ.cones,
      C = PointedCone.hull ℝ (u '' {e | u e ∈ C})) (C : FullCone Φ) :
    normalCone (convexHull ℝ (Set.range d.point)) (d.point C) = C.val.val := by
  have hforward (D : FullCone Φ) :
      D.val.val ≤ normalCone (convexHull ℝ (Set.range d.point)) (d.point D) := by
    rw [hgen D.val.val D.val.property]
    apply Submodule.span_le.mpr
    rintro x ⟨e,he,rfl⟩
    apply (mem_normalCone_hull_range_iff d.point (d.point D) (u e)).mpr
    intro F
    exact (point_le_height Φ u d F e).trans_eq (d.on_ray D e he).symm
  apply le_antisymm
  · intro y hy
    obtain ⟨D,hD,hfull,hyD⟩ := FanMaximalCones.full_cones_cover Φ hcomplete y
    let D' : FullCone Φ := ⟨⟨D,hD⟩,hfull⟩
    let f : V →ₗ[ℝ] ℝ := d.point D' - d.point C
    have hgenerators : ∀ x ∈ u '' {e | u e ∈ D},
        0 ≤ f x ∧ (f x = 0 → x ∈ C.val.val) := by
      rintro x ⟨e,he,rfl⟩
      have hon : d.point D' (u e) = d.height e := d.on_ray D' e he
      refine ⟨?_,?_⟩
      · change 0 ≤ d.point D' (u e) - d.point C (u e)
        rw [hon]
        exact sub_nonneg.mpr (point_le_height Φ u d C e)
      · intro hz
        by_contra hnot
        have hstrict := d.off_ray C e hnot
        change d.point D' (u e) - d.point C (u e) = 0 at hz
        rw [hon] at hz
        linarith
    have hyhull : y ∈ PointedCone.hull ℝ (u '' {e | u e ∈ D}) :=
      hgen D hD ▸ hyD
    have hprop := nonneg_and_zero_mem_hull _ C.val.val f hgenerators y hyhull
    apply hprop.2
    have hle := (mem_normalCone_hull_range_iff d.point (d.point C) y).mp hy D'
    change d.point D' y - d.point C y = 0
    have hge : 0 ≤ d.point D' y - d.point C y := hprop.1
    linarith
  · exact hforward C

include d in
/-- A genuine finite polytope, with equality of all normal cones and all fan
cones, follows from the strictly supported ray data. -/
theorem hasPolytopeNormalFan (hcomplete : Φ.IsComplete)
    (hgen : ∀ C ∈ Φ.cones,
      C = PointedCone.hull ℝ (u '' {e | u e ∈ C})) :
    NormalFanSupport.HasPolytopeNormalFan Φ :=
  hasPolytopeNormalFan_of_full Φ hcomplete d.point
    (normalCone_eq_full Φ u d hcomplete hgen)

/-- Conversely, the support value of a genuine finite polytope is attained
at one of its original finite generators. Each full normal cone then gives
equality precisely on its own rays and strict inequality on all other rays.
No simplicity or rationality assumption is used in this real statement. -/
theorem exists_strictSupportData_of_normalFan (hcomplete : Φ.IsComplete)
    (hpoly : NormalFanSupport.HasPolytopeNormalFan Φ) :
    Nonempty (StrictSupportData Φ u) := by
  classical
  obtain ⟨s,hs⟩ := hpoly
  let Q : Set (Module.Dual ℝ V) := convexHull ℝ (s : Set (Module.Dual ℝ V))
  have hsne : s.Nonempty := by
    obtain ⟨C,hC,hfull,hzero⟩ := FanMaximalCones.full_cones_cover Φ hcomplete 0
    obtain ⟨q,hq,heq⟩ := (hs C).mp hC
    exact Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨q,hq⟩)
  have hmaxex (e : E) : ∃ q ∈ s, ∀ p ∈ s, p (u e) ≤ q (u e) :=
    Finset.exists_max_image s (fun q => q (u e)) hsne
  choose m hm hmax using hmaxex
  have hbound (q : Module.Dual ℝ V) (hq : q ∈ Q) (e : E) :
      q (u e) ≤ m e (u e) := by
    apply convexHull_min (t := {q : Module.Dual ℝ V | q (u e) ≤ m e (u e)}) ?_ ?_ hq
    · intro p hp
      exact hmax e p hp
    · intro a ha b hb t v ht hv htv
      change t * a (u e) + v * b (u e) ≤ m e (u e)
      calc
        _ ≤ t * m e (u e) + v * m e (u e) :=
          add_le_add (mul_le_mul_of_nonneg_left ha ht) (mul_le_mul_of_nonneg_left hb hv)
        _ = m e (u e) := by rw [← add_mul,htv,one_mul]
  have hpex (C : FullCone Φ) :
      ∃ q ∈ Q, C.val.val = normalCone Q q := (hs C.val.val).mp C.val.property
  choose p hp heq using hpex
  refine ⟨{height := fun e => m e (u e),point := p,on_ray := ?_,off_ray := ?_}⟩
  · intro C e he
    have hnormal : u e ∈ normalCone Q (p C) := heq C ▸ he
    exact le_antisymm (hbound (p C) (hp C) e)
      (hnormal (m e) (subset_convexHull ℝ _ (hm e)))
  · intro C e hnot
    apply lt_of_le_of_ne (hbound (p C) (hp C) e)
    intro hsame
    apply hnot
    rw [heq C]
    intro q hq
    exact (hbound q hq e).trans_eq hsame.symm

/-- This is an equivalence with the actual normal-polytope condition,
obtained by proving both directions rather than defining projectivity by
the desired support equations. -/
theorem normalFan_iff_strictSupportData (hcomplete : Φ.IsComplete)
    (hgen : ∀ C ∈ Φ.cones,
      C = PointedCone.hull ℝ (u '' {e | u e ∈ C})) :
    NormalFanSupport.HasPolytopeNormalFan Φ ↔ Nonempty (StrictSupportData Φ u) := by
  constructor
  · exact exists_strictSupportData_of_normalFan Φ u hcomplete
  · rintro ⟨d⟩
    exact hasPolytopeNormalFan Φ u d hcomplete hgen

end Fans

/-- For the actual type-A root fan the generation premise is a theorem of
the checked geometric classification, so it is absent from this endpoint. -/
theorem typeA_hasPolytopeNormalFan {n : ℕ}
    (Φ : Fan (FanBridge.standardEmbedding n)) (hcomplete : Φ.IsComplete)
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n)
      (TypeAFanGeometry.rootFamily n) Φ)
    (d : StrictSupportData Φ
      (fun e : TypeAFanGeometry.Edge n => TypeAFanGeometry.realRoot e.val.1 e.val.2)) :
    NormalFanSupport.HasPolytopeNormalFan Φ := by
  apply hasPolytopeNormalFan Φ _ d hcomplete
  intro C hC
  exact TypeAFanGeometry.fan_cone_eq_hull_roots Φ hrays hC

#print axioms nonneg_and_zero_mem_hull
#print axioms normalCone_eq_full
#print axioms hasPolytopeNormalFan
#print axioms exists_strictSupportData_of_normalFan
#print axioms normalFan_iff_strictSupportData
#print axioms typeA_hasPolytopeNormalFan

end Unimodular.StrictSupportNormalFan
end

end NormalFanGeometry_StrictSupportNormalFan

#check "UNIMODULAR_NORMAL_FAN_GEOMETRY_EOF_V3"
