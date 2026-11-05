import cubical.local_propagation

/-!
# From local polynomial kernels to propagation of global solutions

`StarData` records actual edges around the central vertex and the opposite
vertices of incident squares.  All endpoint equations are stated explicitly.
The local full-rank condition is a theorem input, not part of the structure.
-/

namespace Cubical

open Matrix

noncomputable section

variable {B W E N L T : Type*}

structure StarData (black : E → B) (white : E → W)
    (N L T : Type*) where
  center : W
  neighbor : N → B
  centralEdge : N → E
  centralBlack : ∀ n, black (centralEdge n) = neighbor n
  centralWhite : ∀ n, white (centralEdge n) = center
  left : L → N
  right : L → N
  opposite : L → W
  leftEdge : L → E
  rightEdge : L → E
  leftBlack : ∀ e, black (leftEdge e) = neighbor (left e)
  rightBlack : ∀ e, black (rightEdge e) = neighbor (right e)
  leftWhite : ∀ e, white (leftEdge e) = opposite e
  rightWhite : ∀ e, white (rightEdge e) = opposite e
  pin : T → N

namespace StarData

variable {black : E → B} {white : E → W}

def matrix (S : StarData black white N L T) (d : ℕ) :=
  Local.polynomialMatrix d S.center S.opposite S.left S.right S.pin

theorem propagate [Fintype N] [Fintype L] [Fintype T] [Nonempty T]
    (S : StarData black white N L T) (d : ℕ) (p : W → Fin d → ℝ)
    (hrank : Function.Injective
      (evalMatrix (S.matrix d) (fun wi ↦ p wi.1 wi.2)).mulVec)
    (m : Motion B W d) (hm : m ∈ solutionSpace d black white p)
    (hpin : ∀ t, m.1 (S.neighbor (S.pin t)) = 0) :
    ∀ n, m.1 (S.neighbor n) = 0 := by
  let u : N × Fin d → ℝ := fun ni ↦ m.1 (S.neighbor ni.1) ni.2
  have heq := (mem_solutionSpace_iff d black white p m).mp hm
  have hcenter : m.2 S.center = 0 := by
    let t : T := Classical.arbitrary T
    have h := heq (S.centralEdge (S.pin t))
    rw [S.centralBlack, S.centralWhite, hpin t] at h
    simpa using h
  have hker : evalMatrix (S.matrix d) (fun wi ↦ p wi.1 wi.2) *ᵥ u = 0 := by
    apply (Local.kernel_iff d S.center S.opposite S.left S.right S.pin _ u).mpr
    refine ⟨?_, ?_, ?_⟩
    · intro n
      have h := heq (S.centralEdge n)
      rw [S.centralBlack, S.centralWhite, hcenter, add_zero] at h
      exact h
    · intro e
      have hl := heq (S.leftEdge e)
      have hr := heq (S.rightEdge e)
      rw [S.leftBlack, S.leftWhite] at hl
      rw [S.rightBlack, S.rightWhite] at hr
      dsimp only [u]
      simp only [mul_sub, Finset.sum_sub_distrib]
      linarith
    · intro t i
      exact congrFun (hpin t) i
  have hu : u = 0 := hrank (hker.trans (Matrix.mulVec_zero _).symm)
  intro n
  funext i
  exact congrFun hu (n, i)

/-- Simultaneous local propagation for an arbitrary finite collection of
stars, with independent rigidity witnesses for their links. -/
theorem simultaneous_propagation
    {J : Type*} [Fintype J] {N L T : J → Type*}
    [∀ j, Fintype (N j)] [∀ j, Fintype (L j)] [∀ j, Fintype (T j)]
    [∀ j, Nonempty (T j)]
    (S : ∀ j, StarData black white (N j) (L j) (T j)) (k : ℕ)
    (hinj : ∀ j, Function.Injective (S j).opposite)
    (hne : ∀ j e, (S j).opposite e ≠ (S j).center)
    (hq : ∀ j, ∃ q : N j → Fin k → ℝ,
      Local.PinnedRigid k (S j).left (S j).right (S j).pin q) :
    ∃ p : W → Fin (k + 1) → ℝ,
      ∀ j (m : Motion B W (k + 1)),
        m ∈ solutionSpace (k + 1) black white p →
        (∀ t, m.1 ((S j).neighbor ((S j).pin t)) = 0) →
        ∀ n, m.1 ((S j).neighbor n) = 0 := by
  classical
  have hw : ∀ j, ∃ x : W × Fin (k + 1) → ℝ,
      Function.Injective (evalMatrix ((S j).matrix (k + 1)) x).mulVec := by
    intro j
    obtain ⟨q, hq⟩ := hq j
    exact Local.exists_injective_specialization k (S j).center (S j).opposite
      (S j).left (S j).right (S j).pin (hinj j) (hne j) q hq
  obtain ⟨p, hp⟩ := exists_simultaneous_injective_specialization
    (fun j ↦ (S j).matrix (k + 1)) hw
  refine ⟨fun w i ↦ p (w, i), ?_⟩
  intro j m hm hpin
  exact (S j).propagate (k + 1) (fun w i ↦ p (w, i)) (hp j) m hm hpin

end StarData
end
end Cubical
