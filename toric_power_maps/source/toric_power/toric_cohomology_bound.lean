module

public import ToricPower.CechMeetCohomologyBound
public import ToricPower.DivisorWeightCartierAtlas
public import ToricPower.ToricSeparated

/-!
# Uniform cohomological dimension for actual toric quasi-coherent sheaves

The entire finite cone poset is reindexed into the small universe without
changing its order or its intersections. The chart functor preserves meets
by the actual toric intersection theorem. Hence the finite Čech bound
applies to every quasi-coherent sheaf on the genuine toric scheme.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace TauCeti.Toric
open BondalThomsen.FiniteAffineCechHigherComparison
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace ToricPower

universe v

variable {N : Type} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- A universe-small copy of every cone, with no discarded charts. -/
def ToricMeetChartIndex (fan : Fan i) : Type := Shrink.{0} fan.cones

def toricMeetChartEquiv (fan : Fan i) : ToricMeetChartIndex fan ≃ fan.cones :=
  (equivShrink.{0} fan.cones).symm

instance (fan : Fan i) : Finite (ToricMeetChartIndex fan) :=
  Finite.of_equiv fan.cones (toricMeetChartEquiv fan).symm

instance (fan : Fan i) : SemilatticeInf (ToricMeetChartIndex fan) :=
  (toricMeetChartEquiv fan).semilatticeInf

/-- The actual affine chart opens preserve binary intersections. -/
def toricMeetChartOpenHom (fan : Fan i) :
    InfHom (ToricMeetChartIndex fan) fan.algebraicRealization.Opens where
  toFun a := (fan.affineToricChartι (toricMeetChartEquiv fan a)).opensRange
  map_inf' a b := by
    have h : toricMeetChartEquiv fan (a ⊓ b) =
        toricMeetChartEquiv fan a ⊓ toricMeetChartEquiv fan b :=
      (toricMeetChartEquiv fan).apply_symm_apply _
    rw [h]
    exact chart_opensRange_intersection fan _ _

def toricMeetChartOpenFunctor (fan : Fan i) :
    ToricMeetChartIndex fan ⥤ fan.algebraicRealization.Opens :=
  (OrderHom.ofClass (toricMeetChartOpenHom fan)).toFunctor

theorem toricMeetChartOpen_tupleMeet (fan : Fan i) (q : ℕ)
    (t : Fin (q+1) → ToricMeetChartIndex fan) :
    cechIntersection (toricMeetChartOpenFunctor fan).obj q t =
      (toricMeetChartOpenFunctor fan).obj (FiniteCech.tupleMeet t) := by
  rw [cechIntersection, productOpens_eq_iInf]
  change (⨅ a, toricMeetChartOpenHom fan (t a)) =
    toricMeetChartOpenHom fan (Finset.univ.inf' Finset.univ_nonempty t)
  rw [map_finset_inf', Finset.inf'_eq_inf, Finset.inf_eq_iInf]
  simp

theorem toricMeetChartOpen_covers (fan : Fan i) :
    iSup (toricMeetChartOpenFunctor fan).obj = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨σ, y, rfl⟩ := fan.exists_affineToricChartι_apply_eq x
  apply Opens.mem_iSup.mpr
  refine ⟨(toricMeetChartEquiv fan).symm σ, ?_⟩
  change fan.affineToricChartι σ y ∈
    (fan.affineToricChartι (toricMeetChartEquiv fan ((toricMeetChartEquiv fan).symm σ))).opensRange
  rw [Equiv.apply_symm_apply]
  exact ⟨y, rfl⟩

/-- Every quasi-coherent sheaf has zero cohomology above the finite
number of fan cones, with no completeness or coherence hypothesis. -/
theorem toricQuasicoherentCohomology_subsingleton (fan : Fan i)
    (M : fan.algebraicRealization.Modules) [M.IsQuasicoherent]
    (degree : ℕ) (high : Nat.card fan.cones < degree) :
    Subsingleton (Cohomology M degree) := by
  letI := toricScheme_isNoetherian fan
  letI := fan.algebraicRealization_isSeparated
  apply FiniteCech.meetCover_cohomology_subsingleton ℂ fan.algebraicRealization
    (toricMeetChartOpenFunctor fan) (toricMeetChartOpen_tupleMeet fan)
    (toricMeetChartOpen_covers fan)
    (fun a => isAffineOpen_opensRange
      (fan.affineToricChartι (toricMeetChartEquiv fan a))) M degree
  simpa only [Nat.card_congr (toricMeetChartEquiv fan)] using high

end ToricPower

end
