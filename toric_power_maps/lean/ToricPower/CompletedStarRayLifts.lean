module

public import ToricPower.CanonicalRayStarLift
public import ToricPower.FanCompletionInterface
public import ToricPower.SeparatedConeAttachment
public import ToricPower.LiftedSubfanCones
public import ToricPower.LiftExtension

/-!
# Integral lifts of a completed quotient star with a uniform packing bound

Old quotient rays keep their exact original primitive vectors. New rays
are lifted integrally and moved by one common large positive multiple of
the selected primitive vector. A finite family of actual original-fan
separating characters gives a single integer threshold, valid for every
larger translation. The lower-dimensional completion is an explicit
construction input; this file does not assert its existence.
-/

@[expose] public noncomputable section
open TauCeti.Toric
open scoped Classical
namespace ToricPower.FanSubdivision

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (fan : Fan i) (regular : fan.IsRegular) (ray : fan.Ray)

local notation "a" => fanRayPrimitiveGenerator fan ray
local notation "qZ" => Submodule.mkQ (Submodule.span ℤ {a})
local notation "star" => canonicalRayStar fan ray

variable (completion : SmoothDivisorialCompletion (canonicalRayStar fan ray))

theorem exists_completedStarBaseLift :
    ∃ lifts : completion.fan.Ray → N,
      (∀ ρ, qZ (lifts ρ) = fanRayPrimitiveGenerator completion.fan ρ) ∧
      ∀ ρ : (star).Ray,
        lifts (subfanRayEmbedding star completion.fan completion.contains ρ) =
          canonicalOldStarRayLift fan regular ray ρ := by
  apply exists_compatible_lift_extension
    (subfanRayEmbedding star completion.fan completion.contains) qZ (Submodule.mkQ_surjective _)
    (fanRayPrimitiveGenerator completion.fan) (canonicalOldStarRayLift fan regular ray)
  intro ρ
  exact (canonicalOldStarRayLift_projects fan regular ray ρ).trans
    (subfanRayEmbedding_primitive star completion.fan completion.contains ρ).symm

def completedStarBaseLift : completion.fan.Ray → N :=
  (exists_completedStarBaseLift fan regular ray completion).choose

theorem completedStarBaseLift_projects (ρ : completion.fan.Ray) :
    qZ (completedStarBaseLift fan regular ray completion ρ) =
      fanRayPrimitiveGenerator completion.fan ρ :=
  (exists_completedStarBaseLift fan regular ray completion).choose_spec.1 ρ

theorem completedStarBaseLift_old (ρ : (star).Ray) :
    completedStarBaseLift fan regular ray completion
      (subfanRayEmbedding star completion.fan completion.contains ρ) =
        canonicalOldStarRayLift fan regular ray ρ :=
  (exists_completedStarBaseLift fan regular ray completion).choose_spec.2 ρ

def completedStarRayLift (M : ℕ) (ρ : completion.fan.Ray) : N :=
  if ρ.toCone.val ∈ (star).cones then completedStarBaseLift fan regular ray completion ρ
  else completedStarBaseLift fan regular ray completion ρ + M • a


theorem completedStarRayLift_projects (M : ℕ) (ρ : completion.fan.Ray) :
    qZ (completedStarRayLift fan regular ray completion M ρ) =
      fanRayPrimitiveGenerator completion.fan ρ := by
  classical
  unfold completedStarRayLift
  split_ifs
  · exact completedStarBaseLift_projects fan regular ray completion ρ
  · rw [map_add,map_nsmul,completedStarBaseLift_projects]
    have zero : qZ a = 0 := LinearMap.mem_ker.mp (by
      rw [Submodule.ker_mkQ]
      exact Submodule.mem_span_singleton_self _)
    rw [zero,nsmul_zero,add_zero]

theorem completedStarRayLift_real_projects (M : ℕ) (ρ : completion.fan.Ray) :
    (Submodule.span ℝ {i a}).mkQ
      (i (completedStarRayLift fan regular ray completion M ρ)) =
        fanRayRealVector completion.fan ρ :=
  (rayQuotient_maps_compatible i a _).trans
    (congrArg (rayQuotientLatticeMap i a)
      (completedStarRayLift_projects fan regular ray completion M ρ))

/-- No translation is applied to an old ray. -/

theorem completedStarRayLift_old (M : ℕ) (ρ : (star).Ray) :
    completedStarRayLift fan regular ray completion M
      (subfanRayEmbedding star completion.fan completion.contains ρ) =
        canonicalOldStarRayLift fan regular ray ρ := by
  classical
  unfold completedStarRayLift
  have member : (subfanRayEmbedding star completion.fan completion.contains ρ).toCone.val ∈
      (star).cones := ρ.toCone.property
  rw [ite_eq_left member]
  exact completedStarBaseLift_old fan regular ray completion ρ


abbrev StarSeparatorIndex :=
  {p : fan.cones × fan.cones // ray.toCone ≤ p.1 ∧ ¬ ray.toCone ≤ p.2}

def starSeparator (p : StarSeparatorIndex fan ray) : N →+ ℤ :=
  (FanPacking.exists_star_separator fan ray p.val.1 p.val.2 p.property.1 p.property.2).choose

theorem starSeparator_spec (p : StarSeparatorIndex fan ray) :
    starSeparator fan ray p ∈ dualSemigroup fan.lattice p.val.1.val ∧
      -(starSeparator fan ray p) ∈ dualSemigroup fan.lattice p.val.2.val ∧
      0 < starSeparator fan ray p a ∧
      p.val.1.val ⊓ PointedCone.ofSubmodule
        (fan.lattice.realCharacter (starSeparator fan ray p)).ker = p.val.1.val ⊓ p.val.2.val :=
  (FanPacking.exists_star_separator fan ray p.val.1 p.val.2 p.property.1 p.property.2).choose_spec

/-- A single explicit finite-family argument handles all attached
cones and all original cones outside the chosen star simultaneously. -/

theorem exists_completedStar_packing_bound :
    ∃ threshold : ℕ, ∀ M ≥ threshold, ∀ p : StarSeparatorIndex fan ray,
      ∀ ρ : completion.fan.Ray, ρ.toCone.val ∉ (star).cones →
        0 < starSeparator fan ray p (completedStarRayLift fan regular ray completion M ρ) := by
  classical
  let forms := (Set.finite_range (starSeparator fan ray)).toFinset
  let vectors := (Set.finite_range (completedStarBaseLift fan regular ray completion)).toFinset
  obtain ⟨threshold,property⟩ := FanPacking.exists_uniform_positive_translation forms vectors a (by
    intro m member
    obtain ⟨p,rfl⟩ := (Set.Finite.mem_toFinset _).mp member
    exact (starSeparator_spec fan ray p).2.2.1)
  refine ⟨threshold,?_⟩
  intro M large p ρ newRay
  unfold completedStarRayLift
  rw [ite_eq_right newRay]
  apply property M large
  · exact (Set.Finite.mem_toFinset _).mpr ⟨p,rfl⟩
  · exact (Set.Finite.mem_toFinset _).mpr ⟨ρ,rfl⟩


end ToricPower.FanSubdivision
end

