module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import paper_verification.literal007
import all paper_verification.literal007
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

section ComponentSource_0
/- Original module: TauCeti.LinearAlgebra.SymmetricAlgebra.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Generators of symmetric algebras

The canonical map from a module over a commutative semiring into its symmetric algebra is
injective, without a freeness assumption. Its main application is that an abelian Lie algebra
embeds in its universal enveloping algebra, which is its symmetric algebra
(`TauCeti.UniversalEnvelopingAlgebra.ι_injective_of_isLieAbelian`).

For the symmetric algebra of the base semiring itself, the degree-one element `ι R R 1`
generates the whole algebra. An algebra morphism whose range contains this element is therefore
surjective, a criterion used for coordinate morphisms of additive root subgroups.

A ring homomorphism out of a symmetric algebra is determined by its values on scalars and on
generators (`SymmetricAlgebra.ringHom_ext`), even when its target is nonassociative. The `ext`
tactic reduces equality of these homomorphisms to agreement on scalars and generators.
-/

public section

namespace TauCeti.SymmetricAlgebra

variable (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The canonical map into the symmetric algebra is injective for every module over a
commutative semiring. -/
theorem ι_injective : Function.Injective (_root_.SymmetricAlgebra.ι R M) := by
  -- Adapted from Mathlib's `TensorAlgebra.ι_leftInverse`.
  let : Module Rᵐᵒᵖ M := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  have : IsCentralScalar R M := ⟨fun _ _ ↦ rfl⟩
  exact Function.LeftInverse.injective (g := (TrivSqZeroExt.sndHom R M).comp
    (_root_.SymmetricAlgebra.lift (TrivSqZeroExt.inrHom R M)).toLinearMap) fun x ↦ by simp

end TauCeti.SymmetricAlgebra

namespace SymmetricAlgebra

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- A ring homomorphism out of a symmetric algebra is determined by its values on scalars and on
generators. See note [partially-applied ext lemmas]. -/
@[ext high]
theorem ringHom_ext {A : Type*} [NonAssocSemiring A] {F G : SymmetricAlgebra R M →+* A}
    (h₁ : F.comp (algebraMap R _) = G.comp (algebraMap R _))
    (h₂ : ∀ m, F (ι R M m) = G (ι R M m)) : F = G := by
  refine RingHom.ext fun x ↦ ?_
  induction x using SymmetricAlgebra.induction with
  | algebraMap r => exact DFunLike.congr_fun h₁ r
  | ι m => exact h₂ m
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

end SymmetricAlgebra

namespace AlgHom

/-- An algebra morphism into the symmetric algebra of the base semiring is surjective if its
range contains the degree-one generator. -/
theorem surjective_of_ι_one_mem_range {R A : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] (f : A →ₐ[R] SymmetricAlgebra R R)
    (hgen : SymmetricAlgebra.ι R R 1 ∈ f.range) : Function.Surjective f := by
  intro y
  have hy : y ∈ f.range := by
    induction y using SymmetricAlgebra.induction with
    | algebraMap r => exact f.range.algebraMap_mem r
    | ι r =>
        simpa only [← map_smul, smul_eq_mul, mul_one] using
          f.range.smul_mem hgen r
    | mul y z hy hz => exact mul_mem hy hz
    | add y z hy hz => exact add_mem hy hz
  exact (AlgHom.mem_range _).mp hy

end AlgHom
end
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: TauCeti.LinearAlgebra.SymmetricAlgebra.Basic"

section ComponentSource_1
/- Original module: TauCeti.LinearAlgebra.SymmetricAlgebra.Homogeneous -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Homogeneous submodules of a symmetric algebra

For a module `M` over a commutative semiring `R`, this file defines the degree-`n` piece of
`SymmetricAlgebra R M` to be the `n`-th power of the range of the canonical generator map,
identifies it with the span of the products of exactly `n` generators, and records that degrees add
under multiplication and that scaling linear evaluation scales degree-`n` values by the `n`-th
power. The pieces span the whole symmetric algebra, but no internal direct-sum
decomposition is proven here. A derivation of the symmetric algebra that sends every generator to
degree one preserves every homogeneous submodule.

## Main definitions and results

* `TauCeti.SymmetricAlgebra.homogeneousSubmodule`: the degree-`n` homogeneous submodule.
* `TauCeti.SymmetricAlgebra.homogeneousSubmodule_eq_span`: it is spanned by the products of
  exactly `n` generators.
* `TauCeti.SymmetricAlgebra.adjoin_range_ι`: the generators generate the symmetric algebra.
* `TauCeti.SymmetricAlgebra.iSup_homogeneousSubmodule_eq_top`: the homogeneous pieces span the
  whole symmetric algebra.
* `TauCeti.SymmetricAlgebra.instGradedMonoid`: the homogeneous submodules form a graded monoid.
* `TauCeti.SymmetricAlgebra.homogeneousSubmoduleZeroEquiv`,
  `TauCeti.SymmetricAlgebra.homogeneousSubmoduleOneEquiv`: the homogeneous pieces of degree zero
  and one are the scalars and the module itself.
* `AlgHom.apply_eq_pow_mul_of_forall_ι_eq`: rescaling generator values in the target
  algebra rescales homogeneous values by the corresponding power.
* `TauCeti.SymmetricAlgebra.derivation_mem_homogeneousSubmodule`: a derivation sending generators
  to degree one preserves every homogeneous submodule.

This is the homogeneous-piece prerequisite for the degreewise PBW comparison map in
Layer 3, “PBW, a substantial sub-project”, of the
[highest-weight roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md).
-/

public section

namespace TauCeti.SymmetricAlgebra

universe u v

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The degree-`n` homogeneous part of `SymmetricAlgebra R M`: the `n`-th power of the range of
the canonical generator map. -/
abbrev homogeneousSubmodule (n : ℕ) : Submodule R (SymmetricAlgebra R M) :=
  LinearMap.range (SymmetricAlgebra.ι R M) ^ n

/-- A symmetric-algebra generator is homogeneous of degree one. -/
theorem ι_mem_homogeneousSubmodule (x : M) :
    SymmetricAlgebra.ι R M x ∈ homogeneousSubmodule R M 1 := by
  simpa only [pow_one] using LinearMap.mem_range_self (SymmetricAlgebra.ι R M) x

variable {R M} in
/-- Algebra maps whose values on generators differ by a scalar in the target algebra
have degree-`n` values differing by its `n`th power. -/
theorem _root_.AlgHom.apply_eq_pow_mul_of_forall_ι_eq {A : Type*}
    [CommSemiring A] [Algebra R A] (f g : SymmetricAlgebra R M →ₐ[R] A)
    (c : A) (h : ∀ m, g (SymmetricAlgebra.ι R M m) = c * f (SymmetricAlgebra.ι R M m))
    {n : ℕ} {s : SymmetricAlgebra R M} (hs : s ∈ homogeneousSubmodule R M n) :
    g s = c ^ n * f s := by
  induction hs using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add x y _ _ _ ihx ihy => simp [ihx, ihy, mul_add]
  | mem_mul m hm _ _ _ ih =>
    obtain ⟨y, rfl⟩ := hm
    simp only [map_mul, h, ih, pow_succ]
    ring

/-- Scaling a linear evaluation by `r` scales the value of a homogeneous polynomial of
degree `n` by `rⁿ`. -/
theorem lift_smul_of_mem_homogeneousSubmodule {A : Type*} [CommSemiring A] [Algebra R A]
    (f : M →ₗ[R] A) (r : R) {n : ℕ} {p : SymmetricAlgebra R M}
    (hp : p ∈ homogeneousSubmodule R M n) :
    SymmetricAlgebra.lift (r • f) p = r ^ n • SymmetricAlgebra.lift f p := by
  simpa only [Algebra.smul_def, map_pow] using
    AlgHom.apply_eq_pow_mul_of_forall_ι_eq (SymmetricAlgebra.lift f)
      (SymmetricAlgebra.lift (r • f)) (algebraMap R A r)
      (fun m ↦ by simp [Algebra.smul_def]) hp

/-- A product of `n` symmetric-algebra generators is homogeneous of degree `n`. -/
theorem prod_map_ι_mem_homogeneousSubmodule (l : List M) :
    (l.map (SymmetricAlgebra.ι R M)).prod ∈ homogeneousSubmodule R M l.length :=
  TauCeti.Algebra.prod_map_mem_range_pow _ l

/-- Products of exactly `n` elements from a spanning family span the degree-`n` homogeneous
submodule. -/
theorem homogeneousSubmodule_eq_span_of_span {ι : Type*} (e : ι → M)
    (he : Submodule.span R (Set.range e) = ⊤) (n : ℕ) :
    homogeneousSubmodule R M n =
      Submodule.span R {p | ∃ l : List ι, l.length = n ∧
        (l.map fun i ↦ SymmetricAlgebra.ι R M (e i)).prod = p} :=
  (TauCeti.Algebra.span_prod_map_eq_range_pow_of_span _ e he n).symm

/-- The degree-`n` homogeneous submodule is spanned by the products of exactly `n` generators. -/
theorem homogeneousSubmodule_eq_span (n : ℕ) :
    homogeneousSubmodule R M n =
      Submodule.span R {p | ∃ l : List M, l.length = n ∧
        (l.map (SymmetricAlgebra.ι R M)).prod = p} := by
  have hid : Submodule.span R (Set.range (id : M → M)) = ⊤ := by
    rw [Set.range_id, Submodule.span_univ]
  simpa only [id_eq] using homogeneousSubmodule_eq_span_of_span R M id hid n

/-- The symmetric algebra is generated as an algebra by the image of the generator map. -/
theorem adjoin_range_ι : _root_.Algebra.adjoin R (Set.range (SymmetricAlgebra.ι R M)) = ⊤ := by
  apply top_unique
  intro x hx
  clear hx
  induction x using _root_.SymmetricAlgebra.induction with
  | algebraMap r => exact (_root_.Algebra.adjoin R _).algebraMap_mem r
  | ι x => exact _root_.Algebra.subset_adjoin (Set.mem_range_self x)
  | mul a b ha hb => exact (_root_.Algebra.adjoin R _).mul_mem ha hb
  | add a b ha hb => exact (_root_.Algebra.adjoin R _).add_mem ha hb

/-- The homogeneous submodules span the whole symmetric algebra. This is the spanning half of an
internal grading; directness is not asserted here. -/
theorem iSup_homogeneousSubmodule_eq_top :
    (⨆ n, homogeneousSubmodule R M n) = ⊤ := by
  calc
    (⨆ n, homogeneousSubmodule R M n) =
        ⨆ k, TauCeti.Algebra.wordFiltration (SymmetricAlgebra.ι R M) k := by
      apply le_antisymm
      · exact iSup_le fun n ↦ le_iSup_of_le n
          (TauCeti.Algebra.range_pow_le_wordFiltration (SymmetricAlgebra.ι R M) n)
      · refine iSup_le fun k ↦ ?_
        rw [TauCeti.Algebra.wordFiltration_eq_iSup_pow]
        exact iSup_le fun i ↦ le_iSup (homogeneousSubmodule R M) i
    _ = (_root_.Algebra.adjoin R
        (Set.range (SymmetricAlgebra.ι R M))).toSubmodule :=
      TauCeti.Algebra.iSup_wordFiltration_eq_adjoin (SymmetricAlgebra.ι R M)
    _ = ⊤ := by rw [adjoin_range_ι]; rfl

/-- The degree-zero homogeneous submodule of a symmetric algebra is the image of the scalars,
which embed injectively. -/
noncomputable def homogeneousSubmoduleZeroEquiv : homogeneousSubmodule R M 0 ≃ₗ[R] R :=
  ((LinearEquiv.ofInjective (Algebra.linearMap R (SymmetricAlgebra R M))
    (SymmetricAlgebra.algebraMap_leftInverse M).injective).trans
    (LinearEquiv.ofEq _ _ (by rw [homogeneousSubmodule, pow_zero, Submodule.one_eq_range]))).symm

/-- The inverse of `homogeneousSubmoduleZeroEquiv` sends a scalar to its image in the symmetric
algebra. -/
@[simp]
theorem coe_homogeneousSubmoduleZeroEquiv_symm_apply (r : R) :
    ((homogeneousSubmoduleZeroEquiv R M).symm r : SymmetricAlgebra R M) =
      algebraMap R (SymmetricAlgebra R M) r :=
  (rfl)

/-- A degree-zero element of a symmetric algebra is the image of the scalar
`homogeneousSubmoduleZeroEquiv` assigns to it. -/
@[simp]
theorem algebraMap_homogeneousSubmoduleZeroEquiv_apply (x : homogeneousSubmodule R M 0) :
    algebraMap R (SymmetricAlgebra R M) (homogeneousSubmoduleZeroEquiv R M x) = x := by
  conv_rhs => rw [← (homogeneousSubmoduleZeroEquiv R M).symm_apply_apply x]
  exact (coe_homogeneousSubmoduleZeroEquiv_symm_apply R M _).symm

/-- The degree-one homogeneous submodule of a symmetric algebra is the image of the module, which
embeds injectively. -/
noncomputable def homogeneousSubmoduleOneEquiv : homogeneousSubmodule R M 1 ≃ₗ[R] M :=
  ((LinearEquiv.ofInjective (SymmetricAlgebra.ι R M) (ι_injective R M)).trans
    (LinearEquiv.ofEq _ _ (pow_one _).symm)).symm

/-- The inverse of `homogeneousSubmoduleOneEquiv` sends an element of the module to its
generator. -/
@[simp]
theorem coe_homogeneousSubmoduleOneEquiv_symm_apply (m : M) :
    ((homogeneousSubmoduleOneEquiv R M).symm m : SymmetricAlgebra R M) =
      SymmetricAlgebra.ι R M m :=
  (rfl)

/-- A degree-one element of a symmetric algebra is the generator of the element of the module
`homogeneousSubmoduleOneEquiv` assigns to it. -/
@[simp]
theorem ι_homogeneousSubmoduleOneEquiv_apply (x : homogeneousSubmodule R M 1) :
    SymmetricAlgebra.ι R M (homogeneousSubmoduleOneEquiv R M x) = x := by
  conv_rhs => rw [← (homogeneousSubmoduleOneEquiv R M).symm_apply_apply x]
  exact (coe_homogeneousSubmoduleOneEquiv_symm_apply R M _).symm

/-- The homogeneous submodules form a graded monoid: the unit is homogeneous of degree zero, and
multiplication adds degrees. -/
instance instGradedMonoid : SetLike.GradedMonoid (homogeneousSubmodule R M) :=
  Submodule.nat_power_gradedMonoid (LinearMap.range (SymmetricAlgebra.ι R M))

/-- A derivation of the symmetric algebra sending every generator into degree one preserves every
homogeneous submodule. -/
theorem derivation_mem_homogeneousSubmodule
    (D : Derivation R (SymmetricAlgebra R M) (SymmetricAlgebra R M))
    (hD : ∀ x, D (SymmetricAlgebra.ι R M x) ∈ homogeneousSubmodule R M 1) {n : ℕ}
    {p : SymmetricAlgebra R M} (hp : p ∈ homogeneousSubmodule R M n) :
    D p ∈ homogeneousSubmodule R M n := by
  induction hp using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add x y i _ _ ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | mem_mul m hm i x hx ih =>
      obtain ⟨y, rfl⟩ := hm
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine Submodule.add_mem _ ?_ (SetLike.mul_mem_graded hx (hD y))
      rw [Nat.succ_eq_add_one, Nat.add_comm]
      exact SetLike.mul_mem_graded (ι_mem_homogeneousSubmodule R M y) ih

end TauCeti.SymmetricAlgebra
end
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: TauCeti.LinearAlgebra.SymmetricAlgebra.Homogeneous"

section ComponentSource_2
/- Original module: PaperVerification.SymmetricBasisDegree -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license. Authors: The Tau Ceti contributors.
-/


/-!
# The homogeneous degree of the basis polynomial equivalence

This file preserves exactly the first three mathematical declarations of
Tau Ceti's `SymmetricAlgebra/BasisComparison.lean`. Only its import closure
is narrowed, leaving unrelated monomial-basis and divisibility results to
the subsequent source component. Exact provenance is recorded alongside.
-/

public section

namespace TauCeti.SymmetricAlgebra

open Module

universe u v w

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {R M} in
/-- The algebra equivalence induced by a basis sends the generator of `x` to the linear form with
the coordinates of `x`. -/
@[simp]
theorem _root_.SymmetricAlgebra.equivMvPolynomial_ι {ι : Type w} (b : Basis ι R M) (x : M) :
    SymmetricAlgebra.equivMvPolynomial b (SymmetricAlgebra.ι R M x) =
      b.constr R MvPolynomial.X x := by
  have : (SymmetricAlgebra.equivMvPolynomial b).toLinearMap ∘ₗ SymmetricAlgebra.ι R M =
      b.constr R MvPolynomial.X := b.ext fun i ↦ by simp
  exact LinearMap.congr_fun this x

/-- The algebra equivalence induced by a basis preserves homogeneous degree. -/
@[simp]
theorem map_homogeneousSubmodule_equivMvPolynomial {ι : Type w} (b : Basis ι R M) (n : ℕ) :
    (homogeneousSubmodule R M n).map
        (SymmetricAlgebra.equivMvPolynomial b).toLinearMap =
      MvPolynomial.homogeneousSubmodule ι R n := by
  rw [← MvPolynomial.homogeneousSubmodule_one_pow, ← AlgEquiv.toLinearEquiv_toLinearMap,
    ← AlgEquiv.toAlgHom_toLinearMap,
    Submodule.map_pow (LinearMap.range (SymmetricAlgebra.ι R M))
      (SymmetricAlgebra.equivMvPolynomial b).toAlgHom n]
  congr 1
  rw [MvPolynomial.homogeneousSubmodule_one_eq_span_X, LinearMap.range_eq_map, ← b.span_eq,
    Submodule.map_span, Submodule.map_span, ← Set.image_comp, ← Set.range_comp]
  simp only [Function.comp_def, AlgHom.toLinearMap_apply, AlgEquiv.coe_toAlgHom,
    SymmetricAlgebra.equivMvPolynomial_ι_apply]

/-- An element of a symmetric algebra is homogeneous of degree `n` exactly when its image under
the polynomial equivalence induced by a basis is. -/
@[simp]
theorem _root_.SymmetricAlgebra.equivMvPolynomial_isHomogeneous_iff {ι : Type w}
    (b : Basis ι R M) (n : ℕ) (p : SymmetricAlgebra R M) :
    (SymmetricAlgebra.equivMvPolynomial b p).IsHomogeneous n ↔ p ∈ homogeneousSubmodule R M n := by
  rw [← MvPolynomial.mem_homogeneousSubmodule, ← map_homogeneousSubmodule_equivMvPolynomial R M b n,
    Submodule.mem_map_equiv (e := (SymmetricAlgebra.equivMvPolynomial b).toLinearEquiv)]
  simp


end TauCeti.SymmetricAlgebra
end
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.SymmetricBasisDegree"


set_option pp.explicit false
set_option pp.proofs false
set_option pp.deepTerms false
set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let opts ← getOptions
  if true && env.header.trustLevel != 0 then
    throwError "The final environment has nonzero kernel trust level"
  if Lean.debug.skipKernelTC.get opts then
    throwError "The final environment disabled kernel type checking"
  if Lean.Elab.inServer.get opts then
    throwError "The final environment unexpectedly uses server mode"
  let required : Array (Name × String) := #[
    (`TauCeti.SymmetricAlgebra.ι_injective, "theorem"),
    (`TauCeti.SymmetricAlgebra.homogeneousSubmodule, "definition"),
    (`SymmetricAlgebra.equivMvPolynomial_ι, "theorem"),
    (`TauCeti.SymmetricAlgebra.map_homogeneousSubmodule_equivMvPolynomial, "theorem"),
    (`SymmetricAlgebra.equivMvPolynomial_isHomogeneous_iff, "theorem")
  ]
  let localNames := env.checked.get.constants.foldStage2 (fun acc name _ => acc.push name) (#[] : Array Name)
  if localNames.isEmpty then throwError "Empty authored declaration audit"
  let mut names := localNames
  for (name, _) in required do
    unless names.contains name do names := names.push name
  let mut rows : Array Json := #[]
  for name in names do
    let some info := env.checked.get.find? name | throwError "Missing checked declaration {name}"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient primitive"
    if kind == "axiom" then throwError "Authored axiom {name}"
    let value := info.value? (allowOpaque := true)
    if kind == "theorem" || kind == "definition" || kind == "opaque" then
      unless value.isSome do throwError "No actual body {name}"
    for (requiredName, expectedKind) in required do
      if name == requiredName && kind != expectedKind then
        throwError "Endpoint kind mismatch {name}: expected {expectedKind}, got {kind}"
    let axioms ← collectAxioms name
    for ax in axioms do
      if ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound then
        throwError "Unapproved transitive axiom {name}: {ax}"
    let mut fields := [("name", toJson name.toString), ("kind", toJson kind),
      ("actual_body_available", toJson value.isSome),
      ("universe_parameters", toJson (info.levelParams.map Name.toString)),
      ("type_dependencies", toJson (info.type.getUsedConstants.map Name.toString)),
      ("body_dependencies", toJson ((value.map Expr.getUsedConstants).getD #[] |>.map Name.toString)),
      ("transitive_axioms", toJson (axioms.map Name.toString))]
    if required.any (fun e => e.1 == name) then
      let typeText ← liftTermElabM <| return (← Meta.ppExpr info.type).pretty
      fields := fields ++ [("readable_type", toJson typeText)]
    rows := rows.push (Json.mkObj fields)
  IO.FS.createDirAll ".lake/reports"
  let path := ".lake/reports/" ++ (← getEnv).mainModule.toString ++ ".json"
  IO.FS.writeFile path (Json.mkObj [("accepted", toJson true),
    ("nonce", toJson "58e5390fbc6421a85ac42db7af0c3e0f"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:58e5390fbc6421a85ac42db7af0c3e0f"
