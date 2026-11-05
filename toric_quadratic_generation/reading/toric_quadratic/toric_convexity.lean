module
public import PaperVerification.ToricExchange
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
@[expose] public section
/-!
# The convexity and integer-decomposition bridge

This file makes the geometric hypothesis in the exchange induction explicit.
The degree-`k` polytope is the ordinary scalar dilate `k • P`, represented by
an existential witness in `P`. The integer-decomposition property is required at
all positive natural degrees, with no bounded-degree restriction.
-/

noncomputable section

namespace PaperVerification.ToricExchange

variable {M V : Type*} [AddCommGroup M] [AddCommGroup V] [Module ℝ V]
variable (embedding : M →+ V) (P : Set V)

/-- The actual set of lattice points in a real convex set. -/
def latticePoints : Set M := embedding ⁻¹' P

/-- Integer decomposition in every positive degree, for the specified lattice embedding. -/
def IntegerDecompositionProperty : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ z : M,
    (∃ x ∈ P, embedding z = (k : ℝ) • x) →
    ∃ s : Multiset (latticePoints embedding P), s.card = k ∧
      total (latticePoints embedding P) s = z

/-- The arithmetic mean of a nonempty multiset of lattice points lies in the
convex set containing those points. -/
theorem average_total_mem (hP : Convex ℝ P)
    (s : Multiset (latticePoints embedding P)) (hs : 0 < s.card) :
    (s.card : ℝ)⁻¹ • embedding (total (latticePoints embedding P) s) ∈ P := by
  classical
  let l := s.toList
  have hn : (s.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
  have hweights : (∑ _i : Fin l.length, (s.card : ℝ)⁻¹) = 1 := by
    simp [l, Multiset.length_toList, nsmul_eq_mul, mul_inv_cancel₀ hn]
  have hsum : (∑ i : Fin l.length, embedding ((l[i.1] : latticePoints embedding P) : M)) =
      embedding (total (latticePoints embedding P) s) := by
    rw [Fin.sum_univ_fun_getElem l
      (fun a : latticePoints embedding P => embedding (a : M))]
    change (s.toList.map (fun a : latticePoints embedding P => embedding (a : M))).sum = _
    rw [Multiset.sum_map_toList s
      (fun a : latticePoints embedding P => embedding (a : M))]
    simp only [total, map_multiset_sum, Multiset.map_map]
    rfl
  have hmean := hP.sum_mem (t := Finset.univ)
    (w := fun _i : Fin l.length => (s.card : ℝ)⁻¹)
    (z := fun i : Fin l.length => embedding ((l[i.1] : latticePoints embedding P) : M))
    (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)) hweights
    (fun i _ => (l[i.1]).property)
  simpa only [← Finset.smul_sum, hsum] using hmean

/-- Convexity and the actual integer-decomposition property imply precisely the
midpoint decomposition used by the all-degree exchange proof. -/
theorem midpointDecomposition_of_convex_idp (hP : Convex ℝ P)
    (hidp : IntegerDecompositionProperty embedding P) :
    MidpointDecomposition (latticePoints embedding P) := by
  intro u v hu huv z hz
  have hv : 0 < v.card := by omega
  have huP := average_total_mem embedding P hP u hu
  have hvP := average_total_mem embedding P hP v hv
  rw [← huv] at hvP
  have hz' : embedding z + embedding z =
      embedding (total (latticePoints embedding P) u) +
      embedding (total (latticePoints embedding P) v) := by
    simpa using congrArg embedding hz
  have hhalf : (1 / 2 : ℝ) •
      (embedding (total (latticePoints embedding P) u) +
        embedding (total (latticePoints embedding P) v)) = embedding z := by
    rw [← hz',← two_smul ℝ (embedding z),smul_smul]
    norm_num
  have hw := hP huP hvP (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show 0 ≤ (1 / 2 : ℝ) by norm_num) (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hw' : (u.card : ℝ)⁻¹ • embedding z ∈ P := by
    convert hw using 1
    rw [← hhalf]
    simp only [smul_add,smul_comm (u.card : ℝ)⁻¹ (1 / 2 : ℝ)]
  apply hidp u.card (by omega) z
  refine ⟨(u.card : ℝ)⁻¹ • embedding z, hw', ?_⟩
  have hn : (u.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hu)
  simp [smul_smul, mul_inv_cancel₀ hn]

/-- Congruence modulo twice the ambient lattice, stated without quotient notation. -/
def SameParity (a b : M) : Prop := ∃ w : M, a - b = w + w

/-- For points in an affine face, ambient parity is exactly parity in the saturated
face lattice: the halving witness automatically lies in the real face direction. -/
theorem sameParity_iff_saturated_direction (W : Submodule ℝ V) (p c : M)
    (hdirection : embedding (p - c) ∈ W) :
    SameParity p c ↔ ∃ w : M, embedding w ∈ W ∧ p - c = w + w := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_, hw⟩
    have htwice : embedding w + embedding w ∈ W := by
      simpa only [hw, map_add] using hdirection
    have hhalf := W.smul_mem (1 / 2 : ℝ) htwice
    convert hhalf using 1
    rw [← two_smul ℝ (embedding w),smul_smul]
    norm_num
  · rintro ⟨w, _, hw⟩
    exact ⟨w, hw⟩

/-- Convexity turns an integral parity midpoint into an actual lattice point of the polytope. -/
theorem midpoint_of_sameParity (hP : Convex ℝ P)
    (p c : latticePoints embedding P) (hpc : SameParity (p : M) c) :
    ∃ e : latticePoints embedding P, (p : M) + c = (e : M) + e := by
  obtain ⟨w, hw⟩ := hpc
  have he : (p : M) + c = (c + w) + (c + w) := by
    calc
      (p : M) + c = (p - c) + (c + c) := by abel
      _ = (w + w) + (c + c) := by rw [hw]
      _ = (c + w) + (c + w) := by abel
  have hmid := hP p.property c.property (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show 0 ≤ (1 / 2 : ℝ) by norm_num) (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have he' : embedding p + embedding c = embedding (c + w) + embedding (c + w) := by
    simpa using congrArg embedding he
  have hm : embedding (c + w) ∈ P := by
    convert hmid using 1
    rw [← smul_add, he',← two_smul ℝ (embedding (c + w)),smul_smul]
    norm_num
  exact ⟨⟨c + w, hm⟩, he⟩

/-- The parity and proper-face adjoint data imply triple reduction using actual convexity,
so no midpoint-closure axiom is needed. -/
theorem tripleReduction_of_convex_face_data (hP : Convex ℝ P)
    {F : Type*} [SemilatticeSup F] [OrderTop F]
    (face : latticePoints embedding P → F)
    (parity : ∀ a b c : latticePoints embedding P, face c ≤ face a ⊔ face b →
      ∃ p q : latticePoints embedding P,
        (a : M) + b = (p : M) + q ∧ SameParity (p : M) c)
    (adjoint : ∀ a b : latticePoints embedding P, face a ⊔ face b ≠ ⊤ →
      ∃ u v : latticePoints embedding P, (a : M) + b = (u : M) + v ∧
        face u = face a ⊔ face b ∧ face v ≤ face a ⊔ face b) :
    TripleReduction (latticePoints embedding P) := by
  apply tripleReduction_of_face_data (latticePoints embedding P) face ?_ adjoint
  intro a b c hc
  obtain ⟨p, q, he, hp⟩ := parity a b c hc
  obtain ⟨e, hmid⟩ := midpoint_of_sameParity embedding P hP p c hp
  exact ⟨p, q, e, he, hmid⟩

end PaperVerification.ToricExchange
