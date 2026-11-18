module

public import ToricPower.LatticeTrace
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# The saturated trace has an actual lattice complement

The quotient of an integral lattice by its trace in a real subspace is
torsion-free: nonzero integer multiplication cannot move a vector into
that real subspace. Finite generation over the PID `ℤ` makes this quotient
free. Its quotient map consequently has a linear section, yielding an
actual integral direct-product decomposition.

This is the lattice step in the torus-factor reduction of Section 5.
There is no added assumption that a complement or a quotient basis exists.
The scheme and cohomology comparisons require further arguments.

Development source pending compilation.
-/

@[expose] public noncomputable section

open TauCeti.Toric Module

namespace ToricPower

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- The quotient by the literal lattice trace has no integer torsion.
The assertion does not need rationality of the real subspace. -/
theorem latticeTrace_quotient_torsionFree (W : Submodule ℝ V) :
    Module.IsTorsionFree ℤ (N ⧸ latticeTrace i W) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro r x hx
  by_cases hr : r = 0
  · exact Or.inl hr
  · right
    induction x using Submodule.Quotient.induction_on with
    | _ n =>
      apply (Submodule.Quotient.mk_eq_zero (latticeTrace i W)).mpr
      rw [← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero] at hx
      change i (r • n) ∈ W at hx
      rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℝ] at hx
      exact (Submodule.smul_mem_iff W (by exact_mod_cast hr)).mp hx

/-- Finite generation and torsion-freeness give an actual free quotient
over the integers, using the proved PID structure theorem. -/
theorem latticeTrace_quotient_free (hi : IsIntegralLattice i) (W : Submodule ℝ V) :
    Module.Free ℤ (N ⧸ latticeTrace i W) := by
  letI := hi.finite
  letI := latticeTrace_quotient_torsionFree (i := i) W
  infer_instance

/-- The quotient map has an actual integral-linear section. -/
theorem latticeTrace_quotient_has_section (hi : IsIntegralLattice i)
    (W : Submodule ℝ V) :
    ∃ s : (N ⧸ latticeTrace i W) →ₗ[ℤ] N,
      (latticeTrace i W).mkQ.comp s = LinearMap.id := by
  letI := latticeTrace_quotient_free hi W
  exact (latticeTrace i W).mkQ.exists_rightInverse_of_surjective
    (latticeTrace i W).range_mkQ

def latticeTraceQuotientSection (hi : IsIntegralLattice i) (W : Submodule ℝ V) :
    (N ⧸ latticeTrace i W) →ₗ[ℤ] N :=
  (latticeTrace_quotient_has_section hi W).choose

@[simp]
theorem latticeTraceQuotientSection_mkQ (hi : IsIntegralLattice i)
    (W : Submodule ℝ V) (x : N ⧸ latticeTrace i W) :
    (latticeTrace i W).mkQ (latticeTraceQuotientSection hi W x) = x :=
  LinearMap.congr_fun (latticeTrace_quotient_has_section hi W).choose_spec x

/-- An actual integral direct-product decomposition. The first factor
embeds by the original inclusion of the saturated lattice trace. -/
def latticeTraceProductQuotientEquiv (hi : IsIntegralLattice i) (W : Submodule ℝ V) :
    (latticeTrace i W × (N ⧸ latticeTrace i W)) ≃ₗ[ℤ] N := by
  let S := latticeTrace i W
  let s := latticeTraceQuotientSection hi W
  let f := S.subtype.coprod s
  have hsub (a : S) : S.mkQ a.val = 0 :=
    (Submodule.Quotient.mk_eq_zero S).mpr a.property
  have hs (x : N ⧸ S) : S.mkQ (s x) = x :=
    latticeTraceQuotientSection_mkQ hi W x
  apply LinearEquiv.ofBijective f
  constructor
  · intro a b hab
    have hab' : (a.1 : N) + s a.2 = (b.1 : N) + s b.2 := hab
    have hsecond : a.2 = b.2 := by
      have h := congrArg S.mkQ hab'
      simpa only [map_add, hsub, hs, zero_add] using h
    apply Prod.ext _ hsecond
    apply Subtype.ext
    rw [hsecond] at hab'
    exact add_right_cancel hab'
  · intro x
    have hx : x - s (S.mkQ x) ∈ S := by
      apply (Submodule.Quotient.mk_eq_zero S).mp
      change S.mkQ (x - s (S.mkQ x)) = 0
      rw [map_sub, hs, sub_self]
    refine ⟨(⟨x - s (S.mkQ x), hx⟩, S.mkQ x), ?_⟩
    change x - s (S.mkQ x) + s (S.mkQ x) = x
    exact sub_add_cancel _ _

@[simp]
theorem latticeTraceProductQuotientEquiv_apply (hi : IsIntegralLattice i)
    (W : Submodule ℝ V) (a : latticeTrace i W) (b : N ⧸ latticeTrace i W) :
    latticeTraceProductQuotientEquiv hi W (a, b) =
      (a : N) + latticeTraceQuotientSection hi W b := rfl

@[simp]
theorem latticeTraceProductQuotientEquiv_trace (hi : IsIntegralLattice i)
    (W : Submodule ℝ V) (a : latticeTrace i W) :
    latticeTraceProductQuotientEquiv hi W (a, 0) = (a : N) := by
  simp only [latticeTraceProductQuotientEquiv_apply, map_zero, add_zero]

/-- Extend an integral character on the actual saturated trace to the
ambient lattice through the proved integral direct-product decomposition. -/
def latticeTraceCharacterExtension (hi : IsIntegralLattice i)
    (W : Submodule ℝ V) (m : latticeTrace i W →+ ℤ) : N →+ ℤ :=
  m.comp ((AddMonoidHom.fst (latticeTrace i W) (N ⧸ latticeTrace i W)).comp
    (latticeTraceProductQuotientEquiv hi W).symm.toLinearMap.toAddMonoidHom)

@[simp]
theorem latticeTraceCharacterExtension_apply_trace (hi : IsIntegralLattice i)
    (W : Submodule ℝ V) (m : latticeTrace i W →+ ℤ) (a : latticeTrace i W) :
    latticeTraceCharacterExtension hi W m a.val = m a := by
  have h := (latticeTraceProductQuotientEquiv hi W).symm_apply_apply
    (a, (0 : N ⧸ latticeTrace i W))
  rw [latticeTraceProductQuotientEquiv_trace] at h
  change m (((latticeTraceProductQuotientEquiv hi W).symm a.val).1) = m a
  rw [h]

/-- Restriction of genuine integral characters to a saturated lattice
trace is surjective.  No denominators are introduced. -/
theorem latticeTrace_characterRestriction_surjective (hi : IsIntegralLattice i)
    (W : Submodule ℝ V) :
    Function.Surjective (fun m : N →+ ℤ =>
      m.comp (latticeTrace i W).subtype.toAddMonoidHom) := by
  intro m
  refine ⟨latticeTraceCharacterExtension hi W m, ?_⟩
  ext a
  exact latticeTraceCharacterExtension_apply_trace hi W m a

/-- The inclusion of two nested saturated traces is the literal inclusion
of the underlying lattice vectors. -/
def latticeTraceInclusion {U W : Submodule ℝ V} (hUW : U ≤ W) :
    latticeTrace i U →ₗ[ℤ] latticeTrace i W :=
  Submodule.inclusion (by intro n hn; exact hUW hn)

/-- Every integral character on the smaller test lattice extends to the
larger one. This is sufficient for transporting the weight inequalities
when the retained fan cones agree. -/
theorem latticeTrace_nested_characterRestriction_surjective
    (hi : IsIntegralLattice i) {U W : Submodule ℝ V} (hUW : U ≤ W) :
    Function.Surjective (fun m : latticeTrace i W →+ ℤ =>
      m.comp (latticeTraceInclusion (i := i) hUW).toAddMonoidHom) := by
  intro m
  refine ⟨(latticeTraceCharacterExtension hi U m).comp
    (latticeTrace i W).subtype.toAddMonoidHom, ?_⟩
  ext a
  exact latticeTraceCharacterExtension_apply_trace hi U m a

/-- Evaluating integral characters on any family of lattice vectors in
the smaller subspace produces exactly the same set of integer profiles
in either trace lattice.  This is an equality of the full infinite
profile ranges, not a check of finitely many characters. -/
theorem latticeTrace_characterProfile_ranges (hi : IsIntegralLattice i)
    {U W : Submodule ℝ V} (hUW : U ≤ W)
    {J : Type*} (v : J → N) (hv : ∀ j, i (v j) ∈ U) :
    Set.range (fun m : latticeTrace i W →+ ℤ =>
      fun j => m ⟨v j, hUW (hv j)⟩) =
    Set.range (fun m : latticeTrace i U →+ ℤ =>
      fun j => m ⟨v j, hv j⟩) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨m, rfl⟩
    refine ⟨m.comp (latticeTraceInclusion (i := i) hUW).toAddMonoidHom, ?_⟩
    rfl
  · rintro _ ⟨m, rfl⟩
    obtain ⟨m', hm'⟩ := latticeTrace_nested_characterRestriction_surjective hi hUW m
    refine ⟨m', ?_⟩
    funext j
    exact DFunLike.congr_fun hm' ⟨v j, hv j⟩

/-- Any predicate depending only on those exact integer pairings has
the same existential character test in the two saturated lattices.
The predicate can record all divisor inequalities and a cohomology
nonvanishing condition for the resulting finite weight complex. -/
theorem latticeTrace_exists_characterProfile_iff (hi : IsIntegralLattice i)
    {U W : Submodule ℝ V} (hUW : U ≤ W)
    {J : Type*} (v : J → N) (hv : ∀ j, i (v j) ∈ U)
    (P : (J → ℤ) → Prop) :
    (∃ m : latticeTrace i W →+ ℤ,
      P (fun j => m ⟨v j, hUW (hv j)⟩)) ↔
    ∃ m : latticeTrace i U →+ ℤ, P (fun j => m ⟨v j, hv j⟩) := by
  constructor
  · rintro ⟨m, hm⟩
    have hmem : (fun j => m ⟨v j, hUW (hv j)⟩) ∈
        Set.range (fun m : latticeTrace i U →+ ℤ => fun j => m ⟨v j, hv j⟩) := by
      rw [← latticeTrace_characterProfile_ranges hi hUW v hv]
      exact ⟨m, rfl⟩
    obtain ⟨m', hm'⟩ := hmem
    exact ⟨m', by simpa only [hm'] using hm⟩
  · rintro ⟨m, hm⟩
    have hmem : (fun j => m ⟨v j, hv j⟩) ∈
        Set.range (fun m : latticeTrace i W →+ ℤ => fun j => m ⟨v j, hUW (hv j)⟩) := by
      rw [latticeTrace_characterProfile_ranges hi hUW v hv]
      exact ⟨m, rfl⟩
    obtain ⟨m', hm'⟩ := hmem
    exact ⟨m', by simpa only [hm'] using hm⟩

end ToricPower
