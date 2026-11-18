module

public import ToricPower.GeometricCore
public import ToricPower.LatticeTrace

/-! ## Restricted fans in the saturated lattice and literal linear tests -/
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory TauCeti.Toric
namespace ToricPower
variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

theorem cone_map_comap_subtype (W : Submodule ℝ V) (σ : PointedCone ℝ V)
    (hσ : σ ≤ (W : PointedCone ℝ V)) :
    (σ.comap W.subtype).map W.subtype = σ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hσ hx⟩, hx, rfl⟩

theorem cone_comap_map_subtype (W : Submodule ℝ V) (τ : PointedCone ℝ W) :
    (τ.map W.subtype).comap W.subtype = τ := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    have he : y = x := Subtype.ext hxy
    change y ∈ τ at hy
    exact he ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Restriction of a lattice-rational cone contained in a subspace is rational
for the literal integral trace lattice. -/
theorem toricCone_comap_latticeTrace (W : Submodule ℝ V)
    {σ : PointedCone ℝ V} (hσ : IsToricCone i σ)
    (hW : σ ≤ (W : PointedCone ℝ V)) :
    IsToricCone (latticeTraceMap i W) (σ.comap W.subtype) := by
  classical
  constructor
  · obtain ⟨s, hs⟩ := (isLatticeRational_iff).mp hσ.rational
    have hg (n : N) (hn : n ∈ s) : n ∈ latticeTrace i W := by
      apply hW
      rw [hs]
      exact PointedCone.subset_hull ⟨n, hn, rfl⟩
    let t : Finset (latticeTrace i W) := s.attach.image (fun n => ⟨n.val, hg n.val n.property⟩)
    have himage : W.subtype '' (latticeTraceMap i W '' (t : Set (latticeTrace i W))) =
        i '' (s : Set N) := by
      ext x
      constructor
      · rintro ⟨y, ⟨m, hm, rfl⟩, rfl⟩
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
        exact ⟨n.val, n.property, rfl⟩
      · rintro ⟨n, hn, rfl⟩
        refine ⟨latticeTraceMap i W ⟨n, hg n hn⟩, ?_, rfl⟩
        exact ⟨⟨n, hg n hn⟩, Finset.mem_image.mpr ⟨⟨n, hn⟩, by simp, rfl⟩, rfl⟩
    have hm : (PointedCone.hull ℝ (latticeTraceMap i W '' (t : Set (latticeTrace i W)))).map
        W.subtype = σ := by
      rw [PointedCone.map, Submodule.map_span]
      change PointedCone.hull ℝ (W.subtype ''
        (latticeTraceMap i W '' (t : Set (latticeTrace i W)))) = σ
      rw [himage, ← hs]
    apply (isLatticeRational_iff).mpr
    refine ⟨t, ?_⟩
    rw [← hm, cone_comap_map_subtype]
  · intro x hx hx0 hneg
    have hxv : (x : V) ≠ 0 := by
      intro heq
      exact hx0 (Subtype.ext heq)
    exact hσ.salient (x : V) hx hxv hneg

/-- The finite fan in `W` consists of exactly those cones of the original fan
which are contained in `W`, viewed as cones in `W` itself. -/
def restrictedFan (Φ : Fan i) (W : Submodule ℝ V) (hW : IsRationalSubspace i W) :
    Fan (latticeTraceMap i W) where
  lattice := latticeTrace_isIntegralLattice i Φ.lattice W hW
  cones := (fun σ : PointedCone ℝ V => σ.comap W.subtype) ''
    {σ | σ ∈ Φ.cones ∧ σ ≤ (W : PointedCone ℝ V)}
  finite_cones := (Φ.finite_cones.subset (fun _ h => h.1)).image _
  isToricCone := by
    rintro τ ⟨σ, ⟨hσ, hσW⟩, rfl⟩
    exact toricCone_comap_latticeTrace W (Φ.isToricCone hσ) hσW
  mem_of_isFaceOf := by
    rintro τ η ⟨σ, ⟨hσ, hσW⟩, rfl⟩ hη
    have hface : (η.map W.subtype).IsFaceOf σ := by
      have hh := hη.map W.subtype Subtype.val_injective
      rwa [cone_map_comap_subtype W σ hσW] at hh
    refine ⟨η.map W.subtype, ⟨Φ.mem_of_isFaceOf hσ hface, ?_⟩,
      cone_comap_map_subtype W η⟩
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  inf_isFaceOf_left := by
    rintro τ η ⟨σ, ⟨hσ, hσW⟩, rfl⟩ ⟨υ, ⟨hυ, hυW⟩, rfl⟩
    exact (Φ.inf_isFaceOf_left hσ hυ).comap W.subtype

@[simp] theorem mem_restrictedFan_cones (Φ : Fan i) (W : Submodule ℝ V)
    (hW : IsRationalSubspace i W) (τ : PointedCone ℝ W) :
    τ ∈ (restrictedFan Φ W hW).cones ↔
      ∃ σ ∈ Φ.cones, σ ≤ (W : PointedCone ℝ V) ∧ σ.comap W.subtype = τ := by
  simp only [restrictedFan, Set.mem_image, Set.mem_ofPred_eq, and_assoc]

/-- The actual fan map induced by the inclusion of the saturated lattice. -/
def restrictedFanInclusion (Φ : Fan i) (W : Submodule ℝ V)
    (hW : IsRationalSubspace i W) : FanHom (restrictedFan Φ W hW) Φ where
  latticeMap := (latticeTrace i W).subtype.toAddMonoidHom
  realMap := W.subtype
  map_lattice _ := rfl
  map_cone := by
    rintro τ ⟨σ, ⟨hσ, hσW⟩, rfl⟩
    exact ⟨σ, hσ, (cone_map_comap_subtype W σ hσW).le⟩

/-- The manuscript's linearity condition, with its complete quantification
over the cones of the original fan. -/
def IsLinearSubspace (Φ : Fan i) (W : Submodule ℝ V) : Prop :=
  ∀ σ ∈ Φ.cones, σ ⊓ (W : PointedCone ℝ V) ∈ Φ.cones

/-- A rational linear subspace as in the manuscript. No completeness condition
on either the ambient fan or its restricted fan is included. -/
structure LinearSubspace (Φ : Fan i) where
  space : Submodule ℝ V
  rational : IsRationalSubspace i space
  linear : IsLinearSubspace Φ space

/-- Every original cone restricts to a cone of the exact restricted fan for a
linear subspace. -/
theorem LinearSubspace.comap_mem (Φ : Fan i) (W : LinearSubspace Φ)
    {σ : PointedCone ℝ V} (hσ : σ ∈ Φ.cones) :
    σ.comap W.space.subtype ∈ (restrictedFan Φ W.space W.rational).cones := by
  refine ⟨σ ⊓ (W.space : PointedCone ℝ V), ⟨W.linear σ hσ, inf_le_right⟩, ?_⟩
  ext x
  exact and_iff_left x.property

universe u
variable {N : Type u} [AddCommGroup N] {i : N →+ V}

/-- The literal scheme map from the restricted fan in `N ∩ W` to `X_Σ`. -/
def linearToricInclusion (Φ : Fan i) (W : LinearSubspace Φ) :
    (restrictedFan Φ W.space W.rational).algebraicRealization ⟶ Φ.algebraicRealization :=
  (restrictedFanInclusion Φ W.space W.rational).algebraicMap

end ToricPower
end

/-! ## Nonvacuity and exact support of the linear tests -/

@[expose] public noncomputable section
open TauCeti.Toric
namespace ToricPower
variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- The zero subspace is rational for the literal integral trace. -/
theorem rationalSubspace_bot : IsRationalSubspace i (⊥ : Submodule ℝ V) := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro x ⟨n, rfl⟩
  exact n.property

/-- The full real span of an integral lattice is rational. -/
theorem rationalSubspace_top (hi : IsIntegralLattice i) :
    IsRationalSubspace i (⊤ : Submodule ℝ V) := by
  have hr : Set.range (fun n : latticeTrace i (⊤ : Submodule ℝ V) => i n) =
      Set.range i := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n.val, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨⟨n, by simp [latticeTrace]⟩, rfl⟩
  change Submodule.span ℝ _ = ⊤
  rw [hr]
  exact hi.span_range_eq_top

/-- Every nonempty fan has the zero linear test. The family of tests in the
principal statement is therefore not empty by definition. -/
def zeroLinearSubspace (Φ : Fan i) : LinearSubspace Φ where
  space := ⊥
  rational := rationalSubspace_bot
  linear := by
    intro σ hσ
    convert Φ.bot_mem hσ using 1
    ext x
    simp

/-- The full subspace gives the identity linear test. -/
def topLinearSubspace (Φ : Fan i) : LinearSubspace Φ where
  space := ⊤
  rational := rationalSubspace_top Φ.lattice
  linear := by
    intro σ hσ
    convert hσ using 1
    ext x
    simp

/-- Restricting a nonempty fan to a rational subspace leaves a nonempty fan,
because it retains the zero cone. -/
theorem restrictedFan_nonempty (Φ : Fan i) (hne : Φ.cones.Nonempty)
    (W : Submodule ℝ V) (hW : IsRationalSubspace i W) :
    (restrictedFan Φ W hW).cones.Nonempty := by
  obtain ⟨σ, hσ⟩ := hne
  exact ⟨(⊥ : PointedCone ℝ V).comap W.subtype,
    ⟨⊥, ⟨Φ.bot_mem hσ, bot_le⟩, rfl⟩⟩

/-- The restricted fan of a linear subspace has exactly the expected support. -/
theorem restrictedFan_support (Φ : Fan i) (W : LinearSubspace Φ) :
    (restrictedFan Φ W.space W.rational).support =
      W.space.subtype ⁻¹' Φ.support := by
  ext x
  constructor
  · intro hx
    obtain ⟨τ, hτ, hxτ⟩ := (restrictedFan Φ W.space W.rational).mem_support.mp hx
    obtain ⟨σ, ⟨hσ, hσW⟩, rfl⟩ := hτ
    exact Φ.mem_support.mpr ⟨σ, hσ, hxτ⟩
  · intro hx
    obtain ⟨σ, hσ, hxσ⟩ := Φ.mem_support.mp hx
    exact (restrictedFan Φ W.space W.rational).mem_support.mpr
      ⟨σ.comap W.space.subtype, LinearSubspace.comap_mem Φ W hσ, hxσ⟩

/-- For a complete ambient fan every linear restricted fan is complete; this
is an intermediate result, not a restriction on the principal target. -/
theorem restrictedFan_complete (Φ : Fan i) (hΦ : Φ.IsComplete)
    (W : LinearSubspace Φ) :
    (restrictedFan Φ W.space W.rational).IsComplete := by
  apply (Fan.isComplete_iff _).mpr
  intro x
  obtain ⟨σ, hσ, hxσ⟩ := (Fan.isComplete_iff _).mp hΦ x.val
  exact ⟨σ.comap W.space.subtype, LinearSubspace.comap_mem Φ W hσ, hxσ⟩

/-- The saturated lattice used in the restricted fan has the full dimension
of the subspace, rather than an ambient-rank enlargement. -/
theorem latticeTrace_finrank (Φ : Fan i) (W : LinearSubspace Φ) :
    Module.finrank ℤ (latticeTrace i W.space) = Module.finrank ℝ W.space :=
  (latticeTrace_isIntegralLattice i Φ.lattice W.space W.rational).finrank_eq

end ToricPower
end
