module

public import ToricPower.FanRayPrimitive
public import TauCeti.Geometry.Toric.Algebraic.Ray.Generation
public import TauCeti.Geometry.Toric.Algebraic.Ray.Face
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.LocallyFinite

/-! # Continuous ray coordinates on a complete regular fan

A point has unique nonnegative ray coefficients supported on a single cone.
On each cone these coefficients are the restriction of a linear map. The
finite closed-cone pasting theorem therefore proves global continuity. This
is the geometric input for contracting a recession-compatible negative-ray
complex; no sphere-realization theorem is assumed.
-/

@[expose] public noncomputable section
open TauCeti.Toric Set
open scoped Classical BigOperators

namespace ToricPower

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

def fanRayRealVector (fan : Fan i) (ρ : fan.Ray) : V :=
  i (fanRayPrimitiveGenerator fan ρ)

theorem fanRayRealVector_mem (fan : Fan i) (ρ : fan.Ray) :
    fanRayRealVector fan ρ ∈ ρ.toCone.val :=
  primitiveGenerator_mem fan.lattice (fan.isToricCone ρ.toCone.property)
    (ρ.toToricRay fan ρ.toCone le_rfl)

theorem fanRay_eq_hull_realVector (fan : Fan i) (ρ : fan.Ray) :
    ρ.toCone.val = PointedCone.hull ℝ {fanRayRealVector fan ρ} := by
  apply (ρ.toToricRay fan ρ.toCone le_rfl).eq_hull_singleton
    (fan.isToricCone ρ.toCone.property).salient (fanRayRealVector_mem fan ρ)
  simpa only [fanRayRealVector, fanRayPrimitiveGenerator, map_zero] using fan.lattice.injective.ne
    (primitiveGenerator_ne_zero fan.lattice (fan.isToricCone ρ.toCone.property)
      (ρ.toToricRay fan ρ.toCone le_rfl))

def fanConeRayEquiv (fan : Fan i) (σ : fan.cones) :
    ToricRay σ.val ≃ {ρ : fan.Ray // ρ.toCone ≤ σ} where
  toFun ρ := ⟨Fan.Ray.ofToricRay fan σ ρ, Fan.Ray.toCone_ofToricRay_le fan σ ρ⟩
  invFun ρ := ρ.val.toToricRay fan σ ρ.property
  left_inv _ := rfl
  right_inv _ := rfl

theorem fanConeRay_injective (fan : Fan i) (σ : fan.cones) :
    Function.Injective (Fan.Ray.ofToricRay fan σ) := by
  intro ρ τ h
  apply (fanConeRayEquiv fan σ).injective
  exact Subtype.ext h

theorem fanRayRealVector_linearIndepOn (fan : Fan i) (regular : fan.IsRegular)
    (σ : fan.cones) :
    LinearIndepOn ℝ (fanRayRealVector fan) {ρ | ρ.toCone ≤ σ} := by
  have hreg := (Fan.isRegular_iff).mp regular σ.val σ.property
  have hli : LinearIndependent ℝ
      (fun ρ : ToricRay σ.val => fanRayRealVector fan (Fan.Ray.ofToricRay fan σ ρ)) := by
    simpa only [fanRayRealVector, fanRayPrimitiveGenerator_ofToricRay] using
      hreg.linearIndependent_primitiveGenerator fan.lattice
  exact hli.comp (fanConeRayEquiv fan σ).symm (fanConeRayEquiv fan σ).symm.injective

def fanRayCombination (fan : Fan i) : (fan.Ray →₀ ℝ) →ₗ[ℝ] V :=
  Finsupp.linearCombination ℝ (fanRayRealVector fan)

def rayProfileSupported (fan : Fan i) (σ : fan.cones) (c : fan.Ray →₀ ℝ) : Prop :=
  ∀ ρ ∈ c.support, ρ.toCone ≤ σ

theorem rayProfileCombination_mem (fan : Fan i) (σ : fan.cones)
    (c : fan.Ray →₀ ℝ) (nonnegative : ∀ ρ, 0 ≤ c ρ)
    (supported : rayProfileSupported fan σ c) :
    fanRayCombination fan c ∈ σ.val := by
  rw [fanRayCombination, Finsupp.linearCombination_apply, Finsupp.sum]
  apply σ.val.sum_mem
  intro ρ hρ
  exact σ.val.smul_mem (nonnegative ρ)
    (supported ρ hρ (fanRayRealVector_mem fan ρ))

/-- A nonnegative sum lying in a face uses only rays of that face. -/
theorem rayProfile_supported_in_face (fan : Fan i) (σ : fan.cones)
    (F : PointedCone ℝ V) (face : F.IsFaceOf σ.val)
    (c : fan.Ray →₀ ℝ) (nonnegative : ∀ ρ, 0 ≤ c ρ)
    (supported : rayProfileSupported fan σ c)
    (member : fanRayCombination fan c ∈ F) :
    ∀ ρ ∈ c.support, ρ.toCone.val ≤ F := by
  classical
  letI : Fintype fan.Ray := Fintype.ofFinite _
  have terms (ρ : fan.Ray) : c ρ • fanRayRealVector fan ρ ∈ σ.val := by
    by_cases hρ : ρ ∈ c.support
    · exact σ.val.smul_mem (nonnegative ρ)
        (supported ρ hρ (fanRayRealVector_mem fan ρ))
    · rw [Finsupp.notMem_support_iff.mp hρ, zero_smul]
      exact σ.val.zero_mem
  have total : (∑ ρ, c ρ • fanRayRealVector fan ρ) ∈ F := by
    change (c.sum fun ρ a => a • fanRayRealVector fan ρ) ∈ F at member
    rwa [Finsupp.sum_fintype c (fun ρ a => a • fanRayRealVector fan ρ)
      (fun _ => zero_smul _ _)] at member
  intro ρ hρ
  have hp : 0 < c ρ := lt_of_le_of_ne (nonnegative ρ)
    (Ne.symm (Finsupp.mem_support_iff.mp hρ))
  have hterm := face.mem_of_sum_mem terms total ρ
  have hv := F.smul_mem (inv_nonneg.mpr hp.le) hterm
  rw [smul_smul, inv_mul_cancel₀ hp.ne', one_smul] at hv
  rw [fanRay_eq_hull_realVector]
  exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv)

def IsFanRayProfile (fan : Fan i) (x : V) (c : fan.Ray →₀ ℝ) : Prop :=
  (∀ ρ, 0 ≤ c ρ) ∧ ∃ σ : fan.cones,
    rayProfileSupported fan σ c ∧ fanRayCombination fan c = x

/-- Coordinate uniqueness uses the actual face intersection of the two cones. -/
theorem fanRayProfile_unique (fan : Fan i) (regular : fan.IsRegular)
    {x : V} {c d : fan.Ray →₀ ℝ}
    (hc : IsFanRayProfile fan x c) (hd : IsFanRayProfile fan x d) : c = d := by
  obtain ⟨cnonneg, σ, csupport, ceval⟩ := hc
  obtain ⟨dnonneg, τ, dsupport, deval⟩ := hd
  have hxσ : x ∈ σ.val := ceval ▸ rayProfileCombination_mem fan σ c cnonneg csupport
  have hxτ : x ∈ τ.val := deval ▸ rayProfileCombination_mem fan τ d dnonneg dsupport
  have dsupportσ : rayProfileSupported fan σ d := by
    intro ρ hρ
    exact (rayProfile_supported_in_face fan τ (τ.val ⊓ σ.val)
      (fan.inf_isFaceOf_left τ.property σ.property) d dnonneg dsupport
      (by rw [deval]; exact ⟨hxτ, hxσ⟩) ρ hρ).trans inf_le_right
  apply (linearIndepOn_iffₛ.mp (fanRayRealVector_linearIndepOn fan regular σ))
    c ((Finsupp.mem_supported _ _).mpr csupport)
    d ((Finsupp.mem_supported _ _).mpr dsupportσ)
  exact ceval.trans deval.symm

def localRayCombination (fan : Fan i) (σ : fan.cones) :
    (ToricRay σ.val →₀ ℝ) →ₗ[ℝ] V :=
  Finsupp.linearCombination ℝ
    (fun ρ => fanRayRealVector fan (Fan.Ray.ofToricRay fan σ ρ))

theorem localRayCombination_injective (fan : Fan i) (regular : fan.IsRegular)
    (σ : fan.cones) : Function.Injective (localRayCombination fan σ) := by
  have hreg := (Fan.isRegular_iff).mp regular σ.val σ.property
  have h := hreg.linearIndependent_primitiveGenerator fan.lattice
  simpa only [localRayCombination, fanRayRealVector, fanRayPrimitiveGenerator_ofToricRay] using
    h.finsuppLinearCombination_injective

theorem localRay_hull (fan : Fan i) (σ : fan.cones) :
    PointedCone.hull ℝ
      (Set.range (fun ρ : ToricRay σ.val => fanRayRealVector fan (Fan.Ray.ofToricRay fan σ ρ))) =
      σ.val := by
  simp only [fanRayRealVector, fanRayPrimitiveGenerator_ofToricRay]
  change PointedCone.hull ℝ
    (Set.range (i ∘ primitiveGenerator fan.lattice (fan.isToricCone σ.property))) = _
  rw [Set.range_comp]
  exact (fan.isToricCone σ.property).hull_primitiveGenerator fan.lattice

theorem localRay_nonnegative_representation (fan : Fan i) (σ : fan.cones)
    {x : V} (hx : x ∈ σ.val) :
    ∃ c : ToricRay σ.val →₀ ℝ,
      (∀ ρ, 0 ≤ c ρ) ∧ localRayCombination fan σ c = x := by
  have h : x ∈ PointedCone.hull ℝ
      ((fun ρ : ToricRay σ.val => fanRayRealVector fan (Fan.Ray.ofToricRay fan σ ρ)) '' Set.univ) := by
    rw [Set.image_univ, localRay_hull]
    exact hx
  obtain ⟨c, _, nonnegative, evaluate⟩ :=
    PointedCone.mem_hull_image_iff_linearCombination.mp h
  exact ⟨c, nonnegative, evaluate⟩

def extendConeRayProfile (fan : Fan i) (σ : fan.cones) :
    (ToricRay σ.val →₀ ℝ) →ₗ[ℝ] (fan.Ray →₀ ℝ) :=
  Finsupp.lmapDomain ℝ ℝ (Fan.Ray.ofToricRay fan σ)

theorem extendConeRayProfile_supported (fan : Fan i) (σ : fan.cones)
    (c : ToricRay σ.val →₀ ℝ) :
    rayProfileSupported fan σ (extendConeRayProfile fan σ c) := by
  intro ρ hρ
  obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hρ)
  exact Fan.Ray.toCone_ofToricRay_le fan σ τ

theorem extendConeRayProfile_nonnegative (fan : Fan i) (σ : fan.cones)
    (c : ToricRay σ.val →₀ ℝ) (hc : ∀ ρ, 0 ≤ c ρ) :
    ∀ ρ, 0 ≤ extendConeRayProfile fan σ c ρ := by
  intro ρ
  by_cases hρ : ρ ∈ (extendConeRayProfile fan σ c).support
  · obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hρ)
    change 0 ≤ Finsupp.mapDomain (Fan.Ray.ofToricRay fan σ) c (Fan.Ray.ofToricRay fan σ τ)
    rw [Finsupp.mapDomain_apply_of_injective (fanConeRay_injective fan σ)]
    exact hc τ
  · simpa only [Finsupp.notMem_support_iff.mp hρ] using (le_refl (0 : ℝ))

theorem extendConeRayProfile_evaluate (fan : Fan i) (σ : fan.cones)
    (c : ToricRay σ.val →₀ ℝ) :
    fanRayCombination fan (extendConeRayProfile fan σ c) = localRayCombination fan σ c :=
  Finsupp.linearCombination_mapDomain _ _ _

/-- A linear coordinate formula extending the actual coefficients on one cone. -/
def localFanRayCoordinates (fan : Fan i) (σ : fan.cones) :
    V →ₗ[ℝ] (fan.Ray →₀ ℝ) :=
  (extendConeRayProfile fan σ).comp (localRayCombination fan σ).leftInverse

theorem localFanRayCoordinates_profile (fan : Fan i) (regular : fan.IsRegular)
    (σ : fan.cones) {x : V} (hx : x ∈ σ.val) :
    IsFanRayProfile fan x (localFanRayCoordinates fan σ x) := by
  obtain ⟨c, nonnegative, evaluate⟩ := localRay_nonnegative_representation fan σ hx
  have he : localFanRayCoordinates fan σ x = extendConeRayProfile fan σ c := by
    rw [← evaluate]
    change extendConeRayProfile fan σ
      ((localRayCombination fan σ).leftInverse (localRayCombination fan σ c)) = _
    rw [LinearMap.leftInverse_apply_of_inj
      (LinearMap.ker_eq_bot.mpr (localRayCombination_injective fan regular σ))]
  rw [he]
  exact ⟨extendConeRayProfile_nonnegative fan σ c nonnegative, σ,
    extendConeRayProfile_supported fan σ c,
    (extendConeRayProfile_evaluate fan σ c).trans evaluate⟩

theorem fanRayProfile_exists (fan : Fan i) (complete : fan.IsComplete) (x : V) :
    ∃ c : fan.Ray →₀ ℝ, IsFanRayProfile fan x c := by
  obtain ⟨σ, hσ, hx⟩ := (Fan.isComplete_iff _).mp complete x
  obtain ⟨c, nonnegative, evaluate⟩ := localRay_nonnegative_representation fan ⟨σ, hσ⟩ hx
  exact ⟨extendConeRayProfile fan ⟨σ, hσ⟩ c,
    extendConeRayProfile_nonnegative fan ⟨σ, hσ⟩ c nonnegative,
    ⟨σ, hσ⟩, extendConeRayProfile_supported fan ⟨σ, hσ⟩ c,
    (extendConeRayProfile_evaluate fan ⟨σ, hσ⟩ c).trans evaluate⟩

/-- Actual nonnegative ray coordinates, globally defined by completeness. -/
def fanRayCoordinates (fan : Fan i) (complete : fan.IsComplete) (x : V) : fan.Ray →₀ ℝ :=
  (fanRayProfile_exists fan complete x).choose

theorem fanRayCoordinates_profile (fan : Fan i) (complete : fan.IsComplete) (x : V) :
    IsFanRayProfile fan x (fanRayCoordinates fan complete x) :=
  (fanRayProfile_exists fan complete x).choose_spec

theorem fanRayCoordinates_eq_local (fan : Fan i) (regular : fan.IsRegular)
    (complete : fan.IsComplete) (σ : fan.cones) {x : V} (hx : x ∈ σ.val) :
    fanRayCoordinates fan complete x = localFanRayCoordinates fan σ x :=
  fanRayProfile_unique fan regular (fanRayCoordinates_profile fan complete x)
    (localFanRayCoordinates_profile fan regular σ hx)

theorem localFanRayCoordinates_supported (fan : Fan i) (σ : fan.cones) (x : V) :
    rayProfileSupported fan σ (localFanRayCoordinates fan σ x) :=
  extendConeRayProfile_supported fan σ ((localRayCombination fan σ).leftInverse x)

/-- A cone is the nonnegative part of its coordinate subspace. This also
proves closedness without importing a separate polyhedral closure theorem. -/
theorem mem_cone_iff_localFanRayCoordinates (fan : Fan i) (regular : fan.IsRegular)
    (σ : fan.cones) (x : V) :
    x ∈ σ.val ↔ (∀ ρ, 0 ≤ localFanRayCoordinates fan σ x ρ) ∧
      fanRayCombination fan (localFanRayCoordinates fan σ x) = x := by
  constructor
  · intro hx
    obtain ⟨nonnegative, τ, supported, evaluate⟩ :=
      localFanRayCoordinates_profile fan regular σ hx
    exact ⟨nonnegative, evaluate⟩
  · rintro ⟨nonnegative, evaluate⟩
    rw [← evaluate]
    exact rayProfileCombination_mem fan σ _ nonnegative
      (localFanRayCoordinates_supported fan σ x)

section Topology

variable [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  [T2Space V]

theorem regularFan_cone_isClosed (fan : Fan i) (regular : fan.IsRegular)
    (σ : fan.cones) : IsClosed (σ.val : Set V) := by
  letI := fan.lattice.finiteDimensional
  have descriptions : (σ.val : Set V) =
      (⋂ ρ : fan.Ray, {x : V | 0 ≤ localFanRayCoordinates fan σ x ρ}) ∩
        {x : V | fanRayCombination fan (localFanRayCoordinates fan σ x) = x} := by
    ext x
    simpa only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq,
      SetLike.mem_coe] using
      mem_cone_iff_localFanRayCoordinates fan regular σ x
  rw [descriptions]
  apply IsClosed.inter
  · apply isClosed_iInter
    intro ρ
    exact isClosed_le continuous_const
      (((Finsupp.lapply ρ : (fan.Ray →₀ ℝ) →ₗ[ℝ] ℝ).comp
        (localFanRayCoordinates fan σ)).continuous_of_finiteDimensional)
  · exact isClosed_eq
      ((fanRayCombination fan).comp
        (localFanRayCoordinates fan σ)).continuous_of_finiteDimensional continuous_id

/-- The unique nonnegative coordinates are continuous across the actual
face intersections, by pasting their linear formulas on the finite closed
cone cover of the ambient real space. -/
theorem fanRayCoordinates_continuous_apply (fan : Fan i) (regular : fan.IsRegular)
    (complete : fan.IsComplete) (ρ : fan.Ray) :
    Continuous (fun x : V => fanRayCoordinates fan complete x ρ) := by
  letI := fan.lattice.finiteDimensional
  apply (locallyFinite_of_finite (fun σ : fan.cones => (σ.val : Set V))).continuous
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨σ, hσ, hx⟩ := (Fan.isComplete_iff fan).mp complete x
    exact Set.mem_iUnion.mpr ⟨⟨σ, hσ⟩, hx⟩
  · exact regularFan_cone_isClosed fan regular
  · intro σ
    apply (((Finsupp.lapply ρ : (fan.Ray →₀ ℝ) →ₗ[ℝ] ℝ).comp
      (localFanRayCoordinates fan σ)).continuous_of_finiteDimensional).continuousOn.congr
    intro x hx
    exact congrArg (fun c : fan.Ray →₀ ℝ => c ρ)
      (fanRayCoordinates_eq_local fan regular complete σ hx)

theorem fanRayCoordinates_continuous (fan : Fan i) (regular : fan.IsRegular)
    (complete : fan.IsComplete) :
    Continuous (fun x : V => (fanRayCoordinates fan complete x : fan.Ray → ℝ)) :=
  continuous_pi (fanRayCoordinates_continuous_apply fan regular complete)

end Topology

end ToricPower
