module

public import ToricPower.LatticeTraceSplitting

/-!
# Integral and real retractions onto the saturated trace

The complement already constructed for `N ∩ W` supplies an integral
projection onto that trace. Its scalar extension is a real-linear
retraction onto `W` whenever `W` is rational. These actual maps will
describe the torus directions in an open neighbourhood of a linear
toric subvariety.
-/

@[expose] public noncomputable section

open TauCeti.Toric

namespace ToricPower

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- The integral projection belonging to the constructed lattice complement. -/
def latticeTraceProjection (hi : IsIntegralLattice i) (W : Submodule ℝ V) :
    N →ₗ[ℤ] latticeTrace i W :=
  (LinearMap.fst ℤ (latticeTrace i W) (N ⧸ latticeTrace i W)).comp
    (latticeTraceProductQuotientEquiv hi W).symm.toLinearMap

@[simp]
theorem latticeTraceProjection_trace (hi : IsIntegralLattice i) (W : Submodule ℝ V)
    (a : latticeTrace i W) : latticeTraceProjection hi W a.val = a := by
  have h := (latticeTraceProductQuotientEquiv hi W).symm_apply_apply
    (a, (0 : N ⧸ latticeTrace i W))
  rw [latticeTraceProductQuotientEquiv_trace] at h
  exact congrArg Prod.fst h

@[simp]
theorem latticeTraceProjection_section (hi : IsIntegralLattice i) (W : Submodule ℝ V)
    (q : N ⧸ latticeTrace i W) :
    latticeTraceProjection hi W (latticeTraceQuotientSection hi W q) = 0 := by
  have h := (latticeTraceProductQuotientEquiv hi W).symm_apply_apply
    ((0 : latticeTrace i W), q)
  simpa only [latticeTraceProductQuotientEquiv_apply, ZeroMemClass.coe_zero,
    zero_add, latticeTraceProjection, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearEquiv.coe_coe] using congrArg Prod.fst h

/-- The two components of the complement reconstruct the original vector. -/
theorem latticeTraceProjection_add_section (hi : IsIntegralLattice i)
    (W : Submodule ℝ V) (n : N) :
    (latticeTraceProjection hi W n : N) +
      latticeTraceQuotientSection hi W ((latticeTrace i W).mkQ n) = n := by
  let e := latticeTraceProductQuotientEquiv hi W
  have h := e.apply_symm_apply n
  have hquot := congrArg (latticeTrace i W).mkQ h
  have zeroTrace (a : latticeTrace i W) : (latticeTrace i W).mkQ a.val = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr a.property
  rw [latticeTraceProductQuotientEquiv_apply, map_add, zeroTrace,
    latticeTraceQuotientSection_mkQ, zero_add] at hquot
  change ((e.symm n).1 : N) +
    latticeTraceQuotientSection hi W ((latticeTrace i W).mkQ n) = n
  rw [← hquot]
  exact h

/-- Scalar extension of the actual integral projection. -/
def latticeTraceRealProjection (hi : IsIntegralLattice i) (W : Submodule ℝ V) :
    V →ₗ[ℝ] W :=
  hi.extend (latticeTraceMap i W) (latticeTraceProjection hi W).toAddMonoidHom

@[simp]
theorem latticeTraceRealProjection_lattice (hi : IsIntegralLattice i)
    (W : Submodule ℝ V) (n : N) :
    latticeTraceRealProjection hi W (i n) =
      latticeTraceMap i W (latticeTraceProjection hi W n) :=
  hi.extend_apply _ _ n

/-- Rationality makes the real projection a retraction on the whole
subspace, not only on its integral lattice points. -/
theorem latticeTraceRealProjection_comp_subtype (hi : IsIntegralLattice i)
    (W : Submodule ℝ V) (rational : IsRationalSubspace i W) :
    (latticeTraceRealProjection hi W).comp W.subtype = LinearMap.id := by
  let trace := latticeTrace_isIntegralLattice i hi W rational
  calc
    (latticeTraceRealProjection hi W).comp W.subtype =
        trace.extend (latticeTraceMap i W) (AddMonoidHom.id _) := by
      apply trace.eq_extend
      intro n
      change latticeTraceRealProjection hi W (i n.val) = latticeTraceMap i W n
      rw [latticeTraceRealProjection_lattice, latticeTraceProjection_trace]
    _ = LinearMap.id := trace.extend_id

@[simp]
theorem latticeTraceRealProjection_subtype (hi : IsIntegralLattice i)
    (W : Submodule ℝ V) (rational : IsRationalSubspace i W) (x : W) :
    latticeTraceRealProjection hi W x.val = x :=
  LinearMap.congr_fun (latticeTraceRealProjection_comp_subtype hi W rational) x

/-- A quotient character vanishes on the trace. This will make its
monomial a unit on every chart whose cone is contained in `W`. -/
theorem latticeTrace_quotientCharacter_trace (W : Submodule ℝ V)
    (m : (N ⧸ latticeTrace i W) →+ ℤ) (a : latticeTrace i W) :
    m ((latticeTrace i W).mkQ a.val) = 0 := by
  have hz : (latticeTrace i W).mkQ a.val = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr a.property
  rw [hz, map_zero]

/-- Restricting the real extension of a quotient character to a rational
subspace is the zero functional. -/
theorem latticeTrace_quotientCharacter_real_comp (hi : IsIntegralLattice i)
    (W : Submodule ℝ V) (rational : IsRationalSubspace i W)
    (m : (N ⧸ latticeTrace i W) →+ ℤ) :
    (hi.realCharacter (m.comp (latticeTrace i W).mkQ.toAddMonoidHom)).comp W.subtype = 0 := by
  let trace := latticeTrace_isIntegralLattice i hi W rational
  rw [← trace.realCharacter_comp hi (latticeTrace i W).subtype.toAddMonoidHom
    W.subtype (fun _ => rfl)]
  have zeroCharacter : (m.comp (latticeTrace i W).mkQ.toAddMonoidHom).comp
      (latticeTrace i W).subtype.toAddMonoidHom = 0 := by
    ext a
    exact latticeTrace_quotientCharacter_trace W m a
  rw [zeroCharacter, map_zero]

end ToricPower

end
