module

public import ToricPower.RestrictedFan
public import ToricPower.LatticeTraceSplitting
public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Separation

/-!
# Integral support characters vanishing on a linear test

For a rational subspace `W` whose intersection with a rational cone `σ` is a
face, an integral support character can be chosen to vanish on all of `W`.
Vanishing merely on the face would not suffice for restriction of characters.

The proof applies integral Tucker duality to the cone generators together with
both signs of a basis of the saturated trace lattice `N ∩ W`. The two signs
force the dual character to vanish on the trace. Tucker's positive relation,
and the face property, show that its zero face is exactly `σ ∩ W`.

Consequently every nonnegative integral character of the restricted cone
extends to a nonnegative integral character of the original cone: extend it
first as a lattice character, then add a sufficiently large nonnegative
multiple of the support character. This is the affine algebra needed for the
literal linear inclusion, including noncomplete fans and torus factors.
-/

@[expose] public noncomputable section

open TauCeti TauCeti.Toric

namespace ToricPower

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- An integral supporting character for the face `σ ∩ W` that vanishes
on the entire rational subspace, not merely on its intersection with `σ`. -/
theorem exists_latticeTrace_annihilating_support_character
    (hi : IsIntegralLattice i) (W : Submodule ℝ V)
    (hW : IsRationalSubspace i W) {σ : PointedCone ℝ V}
    (hσ : IsLatticeRational i σ) (hface : (σ ⊓ (W : PointedCone ℝ V)).IsFaceOf σ) :
    ∃ m : N →+ ℤ, m ∈ dualSemigroup hi σ ∧
      (∀ a : latticeTrace i W, m a.val = 0) ∧
      σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)) =
        σ ⊓ (W : PointedCone ℝ V) := by
  classical
  letI := hi.free
  letI := hi.finite
  let S := latticeTrace i W
  let b := Module.finBasis ℤ S
  obtain ⟨s, rfl⟩ := isLatticeRational_iff.mp hσ
  obtain ⟨x, m, relation, nonnegative, positive⟩ :=
    exists_nat_sum_nsmul_eq_zero_and_forall_coeff_add_dual_pos
      (Sum.elim (fun a : s => (a : N))
        (Sum.elim (fun j => (b j : N)) (fun j => -(b j : N))))
  have onGenerators : ∀ a ∈ s, 0 ≤ m a := fun a ha => nonnegative (.inl ⟨a, ha⟩)
  have zeroRestriction : m.toIntLinearMap.comp S.subtype = 0 := by
    apply b.ext
    intro j
    change m (b j : N) = 0
    have hp : 0 ≤ m (b j : N) := nonnegative (.inr (.inl j))
    have hn : 0 ≤ m (-(b j : N)) := nonnegative (.inr (.inr j))
    rw [map_neg] at hn
    omega
  have onTrace (a : S) : m a.val = 0 := by
    exact LinearMap.congr_fun zeroRestriction a
  have onSubspace : W ≤ LinearMap.ker (hi.realCharacter m) := by
    rw [← hW]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change hi.realCharacter m (i a.val) = 0
    rw [hi.realCharacter_apply, onTrace, Int.cast_zero]
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at relation
  have integralSum_mem : (∑ a : s, x (.inl a) • (a : N)) ∈ S := by
    have sum_eq : (∑ a : s, x (.inl a) • (a : N)) =
        -((∑ j, x (.inr (.inl j)) • (b j : N)) +
          ∑ j, x (.inr (.inr j)) • (-(b j : N))) :=
      eq_neg_of_add_eq_zero_left relation
    rw [sum_eq]
    apply S.neg_mem
    apply S.add_mem
    · exact S.sum_mem fun j _ => S.nsmul_mem (b j).property _
    · exact S.sum_mem fun j _ => S.nsmul_mem (S.neg_mem (b j).property) _
  have realSum_mem : (∑ a : s, x (.inl a) • i (a : N)) ∈
      PointedCone.hull ℝ (i '' (s : Set N)) ⊓ (W : PointedCone ℝ V) := by
    constructor
    · apply Submodule.sum_mem
      intro a _
      exact nsmul_mem (show i (a : N) ∈ PointedCone.hull ℝ (i '' (s : Set N)) from
        PointedCone.subset_hull ⟨a.val, a.property, rfl⟩) _
    · change (∑ a : s, x (.inl a) • i (a : N)) ∈ W
      have traceValue : i (∑ a : s, x (.inl a) • (a : N)) ∈ W := integralSum_mem
      simpa only [map_sum, map_nsmul] using traceValue
  refine ⟨m, (mem_dualSemigroup_hull_image hi _ m).mpr onGenerators, onTrace, ?_⟩
  apply PointedCone.inf_ker_eq_of_eq_hull rfl hface
  · rintro _ ⟨a, ha, rfl⟩
    rw [hi.realCharacter_apply]
    exact_mod_cast onGenerators a ha
  · rintro _ ⟨a, ha, rfl⟩
    constructor
    · intro zeroValue
      have zeroIntegral : m a = 0 := by
        simpa only [hi.realCharacter_apply, Int.cast_eq_zero] using zeroValue
      have positiveCoefficient : 0 < x (.inl ⟨a, ha⟩) := by
        have h := positive (.inl ⟨a, ha⟩)
        simpa only [Sum.elim_inl, zeroIntegral, add_zero, Nat.cast_pos] using h
      apply hface.mem_of_sum_smul_mem (c := fun a : s => (x (.inl a) : ℝ))
        (fun a : s => PointedCone.subset_hull ⟨a.val, a.property, rfl⟩)
        (fun _ => Nat.cast_nonneg _) _ ⟨a, ha⟩ (Nat.cast_pos.mpr positiveCoefficient)
      simpa only [Nat.cast_smul_eq_nsmul] using realSum_mem
    · intro member
      exact onSubspace member.2

/-- The support character required for each literal linear test is obtained
from the fan's face axiom and the test's full cone-intersection condition. -/
theorem linearSubspace_exists_annihilating_support_character
    (fan : Fan i) (W : LinearSubspace fan) (σ : fan.cones) :
    ∃ m : N →+ ℤ, m ∈ dualSemigroup fan.lattice σ.val ∧
      (∀ a : latticeTrace i W.space, m a.val = 0) ∧
      σ.val ⊓ PointedCone.ofSubmodule (LinearMap.ker (fan.lattice.realCharacter m)) =
        σ.val ⊓ (W.space : PointedCone ℝ V) :=
  exists_latticeTrace_annihilating_support_character fan.lattice W.space W.rational
    (fan.isToricCone σ.property).rational
    (fan.isFaceOf_of_le σ.property (W.linear σ.val σ.property) inf_le_left)

/-- Restriction of the actual nonnegative-character semigroup is surjective.
The proof retains integrality; multiplying a target character to clear a
denominator would not prove this statement. -/
theorem latticeTrace_dualSemigroupRestriction_surjective
    (hi : IsIntegralLattice i) (W : Submodule ℝ V)
    (hW : IsRationalSubspace i W) {σ : PointedCone ℝ V}
    (hσ : IsLatticeRational i σ) (hface : (σ ⊓ (W : PointedCone ℝ V)).IsFaceOf σ) :
    Function.Surjective
      (dualSemigroupMap (latticeTrace_isIntegralLattice i hi W hW) hi
        (latticeTrace i W).subtype.toAddMonoidHom W.subtype (fun _ => rfl)
        (σ := σ.comap W.subtype) (τ := σ) (fun _ hx => hx)) := by
  intro character
  let hiW := latticeTrace_isIntegralLattice i hi W hW
  let extended := latticeTraceCharacterExtension hi W (character : latticeTrace i W →+ ℤ)
  have restricted : extended.comp (latticeTrace i W).subtype.toAddMonoidHom = character := by
    ext a
    exact latticeTraceCharacterExtension_apply_trace hi W _ a
  have realRestriction : hiW.realCharacter (character : latticeTrace i W →+ ℤ) =
      (hi.realCharacter extended).comp W.subtype := by
    rw [← restricted]
    exact hiW.realCharacter_comp hi (latticeTrace i W).subtype.toAddMonoidHom
      W.subtype (fun _ => rfl) extended
  have onFace : extended ∈ dualSemigroup hi (σ ⊓ (W : PointedCone ℝ V)) := by
    apply (mem_dualSemigroup hi extended).mpr
    intro v hv
    have h := (mem_dualSemigroup hiW (character : latticeTrace i W →+ ℤ)).mp
      character.property (x := (⟨v, hv.2⟩ : W)) hv.1
    simpa only [realRestriction, LinearMap.comp_apply, Submodule.subtype_apply] using h
  obtain ⟨support, hs, ann, cut⟩ :=
    exists_latticeTrace_annihilating_support_character hi W hW hσ hface
  obtain ⟨n, hn⟩ := exists_add_nsmul_mem_dualSemigroup hi hσ.fg hs (by
    rw [cut]
    exact onFace)
  refine ⟨⟨extended + n • support, hn⟩, ?_⟩
  apply Subtype.ext
  apply DFunLike.ext
  intro a
  erw [dualSemigroupMap_apply]
  change extended a.val + n • support a.val = (character : latticeTrace i W →+ ℤ) a
  rw [ann, nsmul_zero, add_zero]
  exact latticeTraceCharacterExtension_apply_trace hi W _ a

/-- Surjectivity for every cone chart of a literal linear toric subvariety. -/
theorem linearSubspace_dualSemigroupRestriction_surjective
    (fan : Fan i) (W : LinearSubspace fan) (σ : fan.cones) :
    Function.Surjective
      (dualSemigroupMap (restrictedFan fan W.space W.rational).lattice fan.lattice
        (latticeTrace i W.space).subtype.toAddMonoidHom W.space.subtype (fun _ => rfl)
        (σ := σ.val.comap W.space.subtype) (τ := σ.val) (fun _ hx => hx)) :=
  latticeTrace_dualSemigroupRestriction_surjective fan.lattice W.space W.rational
    (fan.isToricCone σ.property).rational
    (fan.isFaceOf_of_le σ.property (W.linear σ.val σ.property) inf_le_left)

end ToricPower

end
