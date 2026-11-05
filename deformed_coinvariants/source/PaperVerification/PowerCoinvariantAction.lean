module

public import PaperVerification.PowerCoinvariantStabilizer
public import Mathlib.RepresentationTheory.Basic

/-!
# Actual point-stabilizer invariants of homogeneous coinvariant pieces

Every fixed quotient class has a fixed homogeneous polynomial representative:
average a homogeneous representative over the point stabilizer. The proved
bounded one-variable form of that representative then shows that all such
classes vanish in degrees at least the number of variables.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial
open scoped BigOperators

namespace PaperVerification.PowerCoinvariantStabilizer

open PowerOperators

variable {K : Type*} [Field K] {n : ℕ}
local notation "P" => MvPolynomial (Fin (n+1)) K
local notation "Q" => P ⧸ ordinaryCoinvariantIdeal K (n+1)

theorem rename_mem_coinvariantIdeal (e : Equiv.Perm (Fin (n+1)))
    {p : P} (hp : p ∈ ordinaryCoinvariantIdeal K (n+1)) :
    MvPolynomial.rename e p ∈ ordinaryCoinvariantIdeal K (n+1) := by
  have hle : ordinaryCoinvariantIdeal K (n+1) ≤
      (ordinaryCoinvariantIdeal K (n+1)).comap (MvPolynomial.rename e).toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change MvPolynomial.rename e (MvPolynomial.esymm (Fin (n+1)) K (i.val+1)) ∈
      ordinaryCoinvariantIdeal K (n+1)
    rw [MvPolynomial.rename_esymm]
    exact Ideal.subset_span ⟨i,rfl⟩
  exact hle hp

def coinvariantRename (e : Equiv.Perm (Fin (n+1))) : Q →ₐ[K] Q :=
  Ideal.Quotient.liftₐ _ (quotientMap.comp (MvPolynomial.rename e))
    (fun p hp => Ideal.Quotient.eq_zero_iff_mem.mpr (rename_mem_coinvariantIdeal e hp))

@[simp] theorem coinvariantRename_mk (e : Equiv.Perm (Fin (n+1))) (p : P) :
    coinvariantRename e (quotientMap p) = quotientMap (MvPolynomial.rename e p) := rfl

def coinvariantAction : Representation K (Equiv.Perm (Fin (n+1))) Q where
  toFun e := (coinvariantRename e).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro z
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective z
    change coinvariantRename 1 (quotientMap p) = quotientMap p
    rw [coinvariantRename_mk]
    change quotientMap (MvPolynomial.rename id p) = quotientMap p
    rw [MvPolynomial.rename_id_apply]
  map_mul' e f := by
    apply LinearMap.ext
    intro z
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective z
    change coinvariantRename (e*f) (quotientMap p) =
      coinvariantRename e (coinvariantRename f (quotientMap p))
    rw [coinvariantRename_mk,coinvariantRename_mk,coinvariantRename_mk,MvPolynomial.rename_rename]
    rfl

theorem coinvariantAction_preserves_degree (e : Equiv.Perm (Fin (n+1))) (d : ℕ)
    {z : Q} (hz : z ∈ (coinvariantGrading (K := K) (n := n)).piece d) :
    coinvariantAction e z ∈ (coinvariantGrading (K := K) (n := n)).piece d := by
  rw [coinvariantGrading_piece] at hz ⊢
  obtain ⟨p,hp,rfl⟩ := hz
  exact ⟨MvPolynomial.rename e p,hp.rename_isHomogeneous,rfl⟩

def coinvariantDegreeRepresentation (d : ℕ) :
    Representation K (Equiv.Perm (Fin (n+1))) ((coinvariantGrading (K := K) (n := n)).piece d) :=
  Representation.subrepresentation coinvariantAction ((coinvariantGrading (K := K) (n := n)).piece d)
    (fun e _ hz => coinvariantAction_preserves_degree e d hz)

def stabilizerAverage (p : P) : P :=
  (Fintype.card (Equiv.Perm (Fin n)) : K)⁻¹ •
    ∑ e : Equiv.Perm (Fin n), MvPolynomial.rename (liftPermutation e) p

theorem stabilizerAverage_invariant (p : P) (g : Equiv.Perm (Fin n)) :
    MvPolynomial.rename (liftPermutation g) (stabilizerAverage p) = stabilizerAverage p := by
  simp only [stabilizerAverage,map_smul,map_sum]
  congr 1
  have hterm (e : Equiv.Perm (Fin n)) :
      MvPolynomial.rename (liftPermutation g) (MvPolynomial.rename (liftPermutation e) p) =
        MvPolynomial.rename (liftPermutation (g*e)) p := by
    rw [MvPolynomial.rename_rename,liftPermutation_mul]
    rfl
  simp_rw [hterm]
  exact Equiv.sum_comp (Equiv.mulLeft g) (fun e => MvPolynomial.rename (liftPermutation e) p)

theorem stabilizerAverage_homogeneous (d : ℕ) (p : P) (hp : p.IsHomogeneous d) :
    (stabilizerAverage p).IsHomogeneous d := by
  change (Fintype.card (Equiv.Perm (Fin n)) : K)⁻¹ •
    (∑ e : Equiv.Perm (Fin n), MvPolynomial.rename (liftPermutation e) p) ∈
      homogeneousSubmodule (Fin (n+1)) K d
  apply Submodule.smul_mem
  exact IsHomogeneous.sum _ _ _ (fun _ _ => hp.rename_isHomogeneous)

theorem quotient_stabilizerAverage [CharZero K] (p : P)
    (hp : ∀ e : Equiv.Perm (Fin n), coinvariantRename (liftPermutation e) (quotientMap p) = quotientMap p) :
    quotientMap (stabilizerAverage p) = quotientMap p := by
  have hterm (e : Equiv.Perm (Fin n)) :
      quotientMap (MvPolynomial.rename (liftPermutation e) p) = quotientMap p := hp e
  simp only [stabilizerAverage,map_smul,map_sum,hterm,Finset.sum_const,Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul K,smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),one_smul]

/-- The actual homogeneous coinvariant quotient has no point-stabilizer
fixed class in degrees at least the full number of variables. -/
theorem point_stabilizer_fixed_eq_zero [CharZero K] (d : ℕ) (hd : n+1 ≤ d)
    (z : Q) (hz : z ∈ (coinvariantGrading (K := K) (n := n)).piece d)
    (hfixed : ∀ e : Equiv.Perm (Fin n), coinvariantRename (liftPermutation e) z = z) : z = 0 := by
  rw [coinvariantGrading_piece] at hz
  obtain ⟨p,hp,rfl⟩ := hz
  change quotientMap p = 0
  rw [← quotient_stabilizerAverage p hfixed]
  exact homogeneous_invariant_class_eq_zero d hd (stabilizerAverage p)
    (stabilizerAverage_homogeneous d p hp) (stabilizerAverage_invariant p)

end PaperVerification.PowerCoinvariantStabilizer
