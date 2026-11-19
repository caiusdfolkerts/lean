module

public import TauCeti.AlgebraicGeometry.Modules.Localization
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.Tactic.Module

/-!
# Clearing poles of actual quasi-coherent sections

These statements concern the ordinary restriction maps of an actual
module sheaf. Their proofs use the proved affine localization theorem,
including its kernel statement; no torsion-freeness is required.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace ToricPower.PoleClearing

universe u v

variable {X : Scheme.{u}}

/-- Restriction of an actual module section. -/
abbrev restrict (M : X.Modules) {U W : X.Opens} (h : W ≤ U) :
    Γ(M, U) →+ Γ(M, W) := (M.presheaf.map (homOfLE h).op).hom

/-- Restriction of a regular function. -/
abbrev restrictRing {U W : X.Opens} (h : W ≤ U) :
    Γ(X, U) →+* Γ(X, W) := (X.presheaf.map (homOfLE h).op).hom

theorem restrict_comp (M : X.Modules) {U W Z : X.Opens}
    (hWU : W ≤ U) (hZW : Z ≤ W) (s : Γ(M, U)) :
    restrict M hZW (restrict M hWU s) = restrict M (hZW.trans hWU) s := by
  exact (M.presheaf.map_comp_apply (homOfLE hWU).op (homOfLE hZW).op s).symm

theorem restrictRing_comp {U W Z : X.Opens}
    (hWU : W ≤ U) (hZW : Z ≤ W) (s : Γ(X, U)) :
    restrictRing hZW (restrictRing hWU s) = restrictRing (hZW.trans hWU) s := by
  exact (X.presheaf.map_comp_apply (homOfLE hWU).op (homOfLE hZW).op s).symm

theorem restrict_smul (M : X.Modules) {U W : X.Opens} (h : W ≤ U)
    (a : Γ(X, U)) (s : Γ(M, U)) :
    restrict M h (a • s) = restrictRing h a • restrict M h s :=
  M.map_smul (homOfLE h) a s

/-- A section on a principal open extends after multiplication by a power
of its defining function. The principal open may be supplied by an equality. -/
theorem exists_power_section (M : X.Modules) [M.IsQuasicoherent]
    {U W : X.Opens} (affine : IsAffineOpen U) (f : Γ(X, U))
    (principal : X.basicOpen f = W) (included : W ≤ U) (s : Γ(M, W)) :
    ∃ (n : ℕ) (t : Γ(M, U)),
      restrict M included t = (restrictRing included f) ^ n • s := by
  subst W
  letI := M.isLocalizedModule_basicOpenRestrict affine f
  obtain ⟨n, t, h⟩ := IsLocalizedModule.Away.surj (M.basicOpenRestrict f) f s
  refine ⟨n, t, ?_⟩
  rw [← algebraMap_smul Γ(X, X.basicOpen f) (f ^ n) s,
    Scheme.Modules.basicOpenRestrict_apply] at h
  change restrictRing included (f ^ n) • s = restrict M included t at h
  simpa only [map_pow] using h.symm

/-- If an actual section restricts to zero on a principal open, some
power of the defining function annihilates it. -/
theorem exists_power_annihilating (M : X.Modules) [M.IsQuasicoherent]
    {U W : X.Opens} (affine : IsAffineOpen U) (f : Γ(X, U))
    (principal : X.basicOpen f = W) (included : W ≤ U) (t : Γ(M, U))
    (vanishes : restrict M included t = 0) : ∃ n : ℕ, f ^ n • t = 0 := by
  subst W
  letI := M.isLocalizedModule_basicOpenRestrict affine f
  obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq f
    (f := M.basicOpenRestrict f)
    (show (M.basicOpenRestrict f) t = (M.basicOpenRestrict f) 0 by
      simpa only [map_zero, Scheme.Modules.basicOpenRestrict_apply] using vanishes)
  exact ⟨n, by simpa only [smul_zero] using hn⟩

/-- Finitely many local denominators admit one common exponent. -/
theorem exists_uniform_power_sections {Index : Type v} [Finite Index]
    (M : X.Modules) [M.IsQuasicoherent]
    (opens : Index → X.Opens) (affine : ∀ j, IsAffineOpen (opens j))
    (U : X.Opens) (f : ∀ j, Γ(X, opens j))
    (principal : ∀ j, X.basicOpen (f j) = opens j ⊓ U) (s : Γ(M, U)) :
    ∃ (n : ℕ) (t : ∀ j, Γ(M, opens j)), ∀ j,
      restrict M (inf_le_left : opens j ⊓ U ≤ opens j) (t j) =
        (restrictRing (inf_le_left : opens j ⊓ U ≤ opens j) (f j)) ^ n •
          restrict M (inf_le_right : opens j ⊓ U ≤ U) s := by
  classical
  letI := Fintype.ofFinite Index
  choose n t ht using fun j => exists_power_section M (affine j) (f j)
    (principal j) inf_le_left (restrict M inf_le_right s)
  let bound := Finset.univ.sup n
  have bounded (j : Index) : n j ≤ bound := Finset.le_sup (Finset.mem_univ j)
  refine ⟨bound, fun j => f j ^ (bound - n j) • t j, ?_⟩
  intro j
  rw [restrict_smul, map_pow, ht j, smul_smul, ← pow_add,
    Nat.sub_add_cancel (bounded j)]

/-- Compatible extensions are obtained after one further common power.
The second pole-clearing step kills the discrepancies on the affine
overlaps, so the module sheaf is allowed to have arbitrary torsion. -/
theorem exists_compatible_power_sections {Index : Type v} [Finite Index]
    (M : X.Modules) [M.IsQuasicoherent]
    (opens : Index → X.Opens) (affine : ∀ j, IsAffineOpen (opens j))
    (affineOverlap : ∀ j k, IsAffineOpen (opens j ⊓ opens k))
    (U : X.Opens) (f : ∀ j, Γ(X, opens j))
    (principal : ∀ j, X.basicOpen (f j) = opens j ⊓ U)
    (transition : ∀ j k, Γ(X, opens j ⊓ opens k)ˣ)
    (equations : ∀ j k,
      restrictRing (inf_le_left : opens j ⊓ opens k ≤ opens j) (f j) =
        (transition j k : Γ(X, opens j ⊓ opens k)) *
          restrictRing (inf_le_right : opens j ⊓ opens k ≤ opens k) (f k))
    (s : Γ(M, U)) :
    ∃ (n : ℕ) (t : ∀ j, Γ(M, opens j)),
      (∀ j, restrict M (inf_le_left : opens j ⊓ U ≤ opens j) (t j) =
        (restrictRing (inf_le_left : opens j ⊓ U ≤ opens j) (f j)) ^ n •
          restrict M (inf_le_right : opens j ⊓ U ≤ U) s) ∧
      (∀ j k, restrict M (inf_le_left : opens j ⊓ opens k ≤ opens j) (t j) =
        (transition j k : Γ(X, opens j ⊓ opens k)) ^ n •
          restrict M (inf_le_right : opens j ⊓ opens k ≤ opens k) (t k)) := by
  classical
  letI := Fintype.ofFinite Index
  obtain ⟨n, t, ht⟩ := exists_uniform_power_sections M opens affine U f principal s
  have restricted (j : Index) (W : X.Opens) (hWj : W ≤ opens j) (hWU : W ≤ U) :
      restrict M hWj (t j) = (restrictRing hWj (f j)) ^ n • restrict M hWU s := by
    have h := congrArg (restrict M (le_inf hWj hWU)) (ht j)
    simpa only [restrict_smul, map_pow, restrict_comp, restrictRing_comp] using h
  let difference (j k : Index) : Γ(M, opens j ⊓ opens k) :=
    restrict M inf_le_left (t j) -
      (transition j k : Γ(X, opens j ⊓ opens k)) ^ n •
        restrict M inf_le_right (t k)
  have difference_zero (j k : Index) :
      restrict M (inf_le_left : (opens j ⊓ opens k) ⊓ U ≤ opens j ⊓ opens k)
        (difference j k) = 0 := by
    let W := (opens j ⊓ opens k) ⊓ U
    have hf := congrArg (restrictRing (inf_le_left : W ≤ opens j ⊓ opens k))
      (equations j k)
    simp only [map_mul, restrictRing_comp] at hf
    dsimp only [difference]
    rw [map_sub, restrict_smul, map_pow, restrict_comp, restrict_comp,
      restricted j W (inf_le_left.trans inf_le_left) inf_le_right,
      restricted k W (inf_le_left.trans inf_le_right) inf_le_right,
      hf, mul_pow, mul_smul, sub_self]
  have annihilated (j k : Index) : ∃ d : ℕ,
      (restrictRing (inf_le_left : opens j ⊓ opens k ≤ opens j) (f j)) ^ d •
        difference j k = 0 := by
    apply exists_power_annihilating M (affineOverlap j k)
      (restrictRing inf_le_left (f j)) (W := (opens j ⊓ opens k) ⊓ U)
      _ inf_le_left (difference j k) (difference_zero j k)
    change X.basicOpen (X.presheaf.map (homOfLE inf_le_left).op (f j)) = _
    rw [Scheme.basicOpen_res, principal j]
    simp only [inf_assoc, inf_left_comm, inf_idem, inf_left_idem]
  choose d hd using annihilated
  let bound := Finset.univ.sup (fun p : Index × Index => d p.1 p.2)
  have bounded (j k : Index) : d j k ≤ bound :=
    Finset.le_sup (f := fun p : Index × Index => d p.1 p.2) (Finset.mem_univ (j, k))
  have annihilated_bound (j k : Index) :
      (restrictRing (inf_le_left : opens j ⊓ opens k ≤ opens j) (f j)) ^ bound •
        difference j k = 0 := by
    calc
      _ = (restrictRing (inf_le_left : opens j ⊓ opens k ≤ opens j) (f j)) ^
          (bound - d j k) •
          ((restrictRing (inf_le_left : opens j ⊓ opens k ≤ opens j) (f j)) ^
            (d j k) • difference j k) := by
            rw [← mul_smul, ← pow_add, Nat.sub_add_cancel (bounded j k)]
      _ = 0 := by rw [hd j k, smul_zero]
  refine ⟨bound + n, fun j => f j ^ bound • t j, ?_, ?_⟩
  · intro j
    rw [restrict_smul, map_pow, ht j, smul_smul, ← pow_add]
  · intro j k
    have same := annihilated_bound j k
    dsimp only [difference] at same
    rw [smul_sub, sub_eq_zero] at same
    rw [restrict_smul, restrict_smul, map_pow, map_pow, same, equations j k]
    rw [mul_pow, pow_add]
    module

end ToricPower.PoleClearing

end
