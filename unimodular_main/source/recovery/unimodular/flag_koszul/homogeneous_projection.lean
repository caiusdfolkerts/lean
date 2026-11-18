module

public import Recovery.Unimodular.FlagKoszul.HomogeneousWords

/-!
# Actual homogeneous projections and homogeneous preimage lifts

These are linear projections on the ordinary finitely supported word-chain
module. They are defined from the specified coefficient basis, rather than
from an assumed grading or an assumed exactness property. Their commutation
with an actual coefficient map is proved from its basis-degree formula.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Unimodular.FlagKoszul.HomogeneousWords

variable {K I J J' M N : Type*} [CommRing K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

/-- The actual degree projection, with its range encoded by the genuine
homogeneous submodule. -/
def projectionInto (D : Module.Basis J K M) (δ : I → ℕ) (d : J → ℕ)
    (r q : ℕ) : (List I →₀ M) →ₗ[K] piece D δ d r q := by
  classical
  exact Finsupp.lsum K (fun L => D.constr K (fun j =>
    if h : L.length = r ∧ d j + wordDegree δ L = q then
      ⟨Finsupp.single L (D j), single_basis_mem_piece D δ d L j h.1 h.2⟩
    else 0))

def projection (D : Module.Basis J K M) (δ : I → ℕ) (d : J → ℕ)
    (r q : ℕ) : (List I →₀ M) →ₗ[K] (List I →₀ M) :=
  (piece D δ d r q).subtype.comp (projectionInto D δ d r q)

theorem projection_mem (D : Module.Basis J K M) (δ : I → ℕ) (d : J → ℕ)
    (r q : ℕ) (z : List I →₀ M) :
    projection D δ d r q z ∈ piece D δ d r q :=
  (projectionInto D δ d r q z).property

@[simp] theorem projection_single_basis (D : Module.Basis J K M)
    (δ : I → ℕ) (d : J → ℕ) (r q : ℕ) (L : List I) (j : J) :
    projection D δ d r q (Finsupp.single L (D j)) =
      if L.length = r ∧ d j + wordDegree δ L = q then
        Finsupp.single L (D j) else 0 := by
  classical
  simp only [projection, LinearMap.comp_apply, projectionInto,
    Finsupp.lsum_single, Module.Basis.constr_basis]
  split <;> rfl

/-- The projection fixes every chain of the specified degree. -/
theorem projection_eq_self (D : Module.Basis J K M) (δ : I → ℕ) (d : J → ℕ)
    {r q : ℕ} {z : List I →₀ M} (hz : z ∈ piece D δ d r q) :
    projection D δ d r q z = z := by
  apply piece_induction D δ d
    (fun z => projection D δ d r q z = z) (by simp)
    (fun x y hx hy => by simp only [map_add, hx, hy]) ?_ z hz
  intro L j c hL hj
  simp only [map_smul, projection_single_basis, hL, hj, and_self, if_true]

/-- Distinct word-length/internal-degree pieces are killed by the projection. -/
theorem projection_eq_zero_of_piece (D : Module.Basis J K M)
    (δ : I → ℕ) (d : J → ℕ) {r q r' q' : ℕ}
    {z : List I →₀ M} (hz : z ∈ piece D δ d r' q')
    (hne : ¬(r' = r ∧ q' = q)) : projection D δ d r q z = 0 := by
  apply piece_induction D δ d
    (fun z => projection D δ d r q z = 0) (by simp)
    (fun x y hx hy => by simp only [map_add, hx, hy, add_zero]) ?_ z hz
  intro L j c hL hj
  have hn : ¬(L.length = r ∧ d j + wordDegree δ L = q) := by
    intro h
    exact hne ⟨hL.symm.trans h.1, hj.symm.trans h.2⟩
  simp only [map_smul, projection_single_basis, if_neg hn, smul_zero]

@[simp] theorem projection_idempotent (D : Module.Basis J K M)
    (δ : I → ℕ) (d : J → ℕ) (r q : ℕ) (z : List I →₀ M) :
    projection D δ d r q (projection D δ d r q z) = projection D δ d r q z :=
  projection_eq_self D δ d (projection_mem D δ d r q z)

/-- An actual coefficient map of degree `c` commutes with the exact degree
projections, with the target degree shifted by `c`. -/
theorem coefficientMap_projection (D : Module.Basis J K M)
    (E : Module.Basis J' K N) (δ : I → ℕ) (d : J → ℕ) (e : J' → ℕ)
    (f : M →ₗ[K] N) (c : ℕ)
    (hf : ∀ j a, E.repr (f (D j)) a ≠ 0 → e a = d j + c)
    (r q : ℕ) (z : List I →₀ M) :
    Finsupp.mapRange.linearMap f (projection D δ d r q z) =
      projection E δ e r (q + c) (Finsupp.mapRange.linearMap f z) := by
  classical
  have heq : (Finsupp.mapRange.linearMap f).comp (projection D δ d r q) =
      (projection E δ e r (q + c)).comp (Finsupp.mapRange.linearMap f) := by
    apply Finsupp.lhom_ext'
    intro L
    apply D.ext
    intro j
    change Finsupp.mapRange.linearMap f (projection D δ d r q (Finsupp.single L (D j))) =
      projection E δ e r (q + c) (Finsupp.mapRange.linearMap f (Finsupp.single L (D j)))
    rw [projection_single_basis]
    have hx : Finsupp.mapRange.linearMap f (Finsupp.single L (D j)) ∈
        piece E δ e L.length (d j + wordDegree δ L + c) :=
      coefficientMap_mem_piece D E δ d e f c hf
        (single_basis_mem_piece D δ d L j rfl rfl)
    by_cases h : L.length = r ∧ d j + wordDegree δ L = q
    · rw [if_pos h]
      exact (projection_eq_self E δ e (by simpa only [h.1, h.2] using hx)).symm
    · rw [if_neg h, map_zero]
      symm
      apply projection_eq_zero_of_piece E δ e hx
      intro hh
      exact h ⟨hh.1, Nat.add_right_cancel hh.2⟩
  exact LinearMap.congr_fun heq z

/-- A homogeneous target with an ordinary preimage has a homogeneous preimage.
The only grading hypothesis is the actual coefficient-basis degree formula. -/
theorem exists_homogeneous_preimage (D : Module.Basis J K M)
    (E : Module.Basis J' K N) (δ : I → ℕ) (d : J → ℕ) (e : J' → ℕ)
    (f : M →ₗ[K] N) (c : ℕ)
    (hf : ∀ j a, E.repr (f (D j)) a ≠ 0 → e a = d j + c)
    {r q : ℕ} {z : List I →₀ N} (hz : z ∈ piece E δ e r (q + c))
    (hpre : ∃ w : List I →₀ M, Finsupp.mapRange.linearMap f w = z) :
    ∃ w : List I →₀ M, w ∈ piece D δ d r q ∧ Finsupp.mapRange.linearMap f w = z := by
  obtain ⟨w, hw⟩ := hpre
  refine ⟨projection D δ d r q w, projection_mem D δ d r q w, ?_⟩
  rw [coefficientMap_projection D E δ d e f c hf, hw]
  exact projection_eq_self E δ e hz

/-- The same lifting statement with a target degree and a nonnegative shift.
In particular it applies to quotient maps with shift zero and multiplication
by one variable with shift one. -/
theorem exists_homogeneous_preimage_sub (D : Module.Basis J K M)
    (E : Module.Basis J' K N) (δ : I → ℕ) (d : J → ℕ) (e : J' → ℕ)
    (f : M →ₗ[K] N) (c : ℕ)
    (hf : ∀ j a, E.repr (f (D j)) a ≠ 0 → e a = d j + c)
    {r q : ℕ} (hc : c ≤ q) {z : List I →₀ N} (hz : z ∈ piece E δ e r q)
    (hpre : ∃ w : List I →₀ M, Finsupp.mapRange.linearMap f w = z) :
    ∃ w : List I →₀ M, w ∈ piece D δ d r (q - c) ∧
      Finsupp.mapRange.linearMap f w = z := by
  apply exists_homogeneous_preimage D E δ d e f c hf ?_ hpre
  simpa only [Nat.sub_add_cancel hc] using hz

#print axioms projection_mem
#print axioms projection_eq_self
#print axioms coefficientMap_projection
#print axioms exists_homogeneous_preimage
#print axioms exists_homogeneous_preimage_sub

end Unimodular.FlagKoszul.HomogeneousWords
