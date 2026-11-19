module

public import ToricPower.RegularConeInequalities

/-!
# A complete rational fan adapted to every cone of a regular fan

All integral defining forms of all original cones are used simultaneously.
Their sign arrangement is a genuine complete fan. Intersecting one of its
cones with any original cone gives a face of the arrangement cone. This
is the compatibility needed at the exterior boundary; it does not assert
that original cones are themselves cones of the arrangement.
-/

@[expose] public noncomputable section
open TauCeti.Toric Set

namespace ToricPower.FanSubdivision

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

theorem inf_isFaceOf_of_weakSigns {κ : Type*} (forms : κ → V →ₗ[ℝ] ℝ)
    (source region : PointedCone ℝ V)
    (description : ∀ x, x ∈ region ↔ ∀ k, forms k x ≤ 0)
    (signs : ∀ k, (∀ x ∈ source, 0 ≤ forms k x) ∨
      (∀ x ∈ source, forms k x ≤ 0)) :
    (source ⊓ region).IsFaceOf source := by
  refine ⟨inf_le_left,?_⟩
  intro x y r hx hy positive combined
  refine ⟨hx,(description x).mpr ?_⟩
  intro k
  rcases signs k with nonnegative | nonpositive
  · have first := nonnegative x hx
    have second := nonnegative y hy
    have total := (description (r • x + y)).mp combined.2 k
    rw [map_add,map_smul,smul_eq_mul] at total
    nlinarith
  · exact nonpositive x hx

variable (fan : Fan i) (regular : fan.IsRegular)

def regularFanConeCharacters (σ : fan.cones) :
    (Fin (Module.finrank ℤ N) × Bool) → N →+ ℤ :=
  (regularCone_exists_integral_inequalities fan.lattice
    (Fan.isRegular_iff.mp regular σ.val σ.property)).choose

theorem regularFanConeCharacters_membership (σ : fan.cones) (x : V) :
    x ∈ σ.val ↔ ∀ p, fan.lattice.realCharacter (regularFanConeCharacters fan regular σ p) x ≤ 0 :=
  (regularCone_exists_integral_inequalities fan.lattice
    (Fan.isRegular_iff.mp regular σ.val σ.property)).choose_spec.1 x

theorem regularFanConeCharacters_separate (σ : fan.cones) (x : V)
    (zero : ∀ p, fan.lattice.realCharacter (regularFanConeCharacters fan regular σ p) x = 0) :
    x = 0 :=
  (regularCone_exists_integral_inequalities fan.lattice
    (Fan.isRegular_iff.mp regular σ.val σ.property)).choose_spec.2 x zero

abbrev FanHyperplaneIndex := fan.cones × (Fin (Module.finrank ℤ N) × Bool)

local instance fanHyperplaneConeFintype : Fintype fan.cones := Fintype.ofFinite _

def fanHyperplaneCharacters : FanHyperplaneIndex fan → N →+ ℤ :=
  fun p => regularFanConeCharacters fan regular p.1 p.2

theorem fanHyperplaneCharacters_separate (nonempty : fan.cones.Nonempty) (x : V)
    (zero : ∀ p, fan.lattice.realCharacter (fanHyperplaneCharacters fan regular p) x = 0) :
    x = 0 := by
  obtain ⟨σ,member⟩ := nonempty
  exact regularFanConeCharacters_separate fan regular ⟨σ,member⟩ x
    (fun p => zero (⟨σ,member⟩,p))

/-- A complete rational fan defined by all actual cone inequalities. -/
def adaptedHyperplaneFan (nonempty : fan.cones.Nonempty) : Fan i := by
  classical
  exact integralHyperplaneFan fan.lattice (fanHyperplaneCharacters fan regular)
    (fanHyperplaneCharacters_separate fan regular nonempty)

theorem adaptedHyperplaneFan_complete (nonempty : fan.cones.Nonempty) :
    (adaptedHyperplaneFan fan regular nonempty).IsComplete := by
  classical
  exact integralHyperplaneFan_complete fan.lattice (fanHyperplaneCharacters fan regular)
    (fanHyperplaneCharacters_separate fan regular nonempty)

/-- Every original cone cuts out an actual face on every arrangement cone. -/
theorem adaptedHyperplaneFan_inf_isFaceOf (nonempty : fan.cones.Nonempty)
    (τ : (adaptedHyperplaneFan fan regular nonempty).cones) (σ : fan.cones) :
    (τ.val ⊓ σ.val).IsFaceOf τ.val := by
  classical
  apply inf_isFaceOf_of_weakSigns
    (fun p => fan.lattice.realCharacter (regularFanConeCharacters fan regular σ p))
    τ.val σ.val (regularFanConeCharacters_membership fan regular σ)
  intro p
  exact integralHyperplaneFan_cone_weakSign fan.lattice (fanHyperplaneCharacters fan regular)
    (fanHyperplaneCharacters_separate fan regular nonempty) τ (σ,p)

end ToricPower.FanSubdivision
end
