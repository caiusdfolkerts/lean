module

public import PaperVerification.ToricFanPolytopes
public import Mathlib.Topology.Algebra.Order.Field

@[expose] public section

/-!
# Interior lattice points and the literal canonical shift

Primitive fan rays are nonzero integral vectors. The topological interior
is therefore cut out by the strict ray inequalities. At a lattice point,
strict integral slack is equivalent to slack at least one, exactly the
coefficient shift by minus one used for the toric canonical divisor.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem normalRay_functional_ne_zero (u : Lattice n) (hu : u ∈ «Σ».rays) :
    dotProductEquiv ℝ (Fin n) (embed n u) ≠ 0 := by
  intro he
  have hemb : embed n u = 0 := (dotProductEquiv ℝ (Fin n)).injective (by simpa using he)
  exact «Σ».ray_ne_zero hu ((embed_injective n) (by simpa using hemb))

/-- The topological interior uses strict inequalities for the actual
nonzero primitive rays. This includes dimension zero. -/
theorem interior_fanPolytope_eq (a : Lattice n → ℝ) :
    interior («Σ».fanPolytope a) =
      {x | ∀ u ∈ «Σ».rays, -a u < (dotProductEquiv ℝ (Fin n) (embed n u)) x} := by
  ext x
  constructor
  · intro hx u hu
    rw [«Σ».fanPolytope_eq_normalHalfspaces] at hx
    exact strict_support_of_interior
      (fun v : «Σ».rays => dotProductEquiv ℝ (Fin n) (embed n v))
      (fun v : «Σ».rays => -a v) x hx ⟨u, hu⟩ («Σ».normalRay_functional_ne_zero u hu)
  · intro hx
    let U : Set (Ambient n) :=
      ⋂ u ∈ «Σ».rays, {x | -a u < (dotProductEquiv ℝ (Fin n) (embed n u)) x}
    have hUopen : IsOpen U := by
      apply isOpen_biInter_finset
      intro u hu
      exact isOpen_lt continuous_const
        (dotProductEquiv ℝ (Fin n) (embed n u)).continuous_of_finiteDimensional
    have hxU : x ∈ U := Set.mem_iInter₂.mpr hx
    have hUsub : U ⊆ «Σ».fanPolytope a := by
      intro y hy u hu
      exact (Set.mem_iInter₂.mp hy u hu).le
    exact (interior_maximal hUsub hUopen) hxU

/-- The integral support pairing agrees with the genuine integer dot
product before casting. -/
theorem normalRay_pairing_lattice (u z : Lattice n) :
    (dotProductEquiv ℝ (Fin n) (embed n u)) (embed n z) =
      ((∑ i, u i * z i : ℤ) : ℝ) := by
  simp [dotProductEquiv, dotProduct, embed]

/-- A lattice point lies in the actual interior exactly when it lies in
the support polytope with every primitive coefficient reduced by one. -/
theorem lattice_mem_interior_iff_adjointSupport (a : Lattice n → ℤ) (z : Lattice n) :
    embed n z ∈ interior («Σ».fanPolytope (fun u => (a u : ℝ))) ↔
      embed n z ∈ «Σ».fanPolytope (fun u => ((a u - 1 : ℤ) : ℝ)) := by
  rw [«Σ».interior_fanPolytope_eq]
  constructor
  · intro hz u hu
    have h := hz u hu
    change -(a u : ℝ) < (dotProductEquiv ℝ (Fin n) (embed n u)) (embed n z) at h
    change -((a u - 1 : ℤ) : ℝ) ≤
      (dotProductEquiv ℝ (Fin n) (embed n u)) (embed n z)
    rw [normalRay_pairing_lattice] at h ⊢
    have hi : -a u < ∑ i, u i * z i := by exact_mod_cast h
    have hi' : -(a u - 1) ≤ ∑ i, u i * z i := by omega
    exact_mod_cast hi'
  · intro hz u hu
    have h := hz u hu
    change -((a u - 1 : ℤ) : ℝ) ≤
      (dotProductEquiv ℝ (Fin n) (embed n u)) (embed n z) at h
    change -(a u : ℝ) < (dotProductEquiv ℝ (Fin n) (embed n u)) (embed n z)
    rw [normalRay_pairing_lattice] at h ⊢
    have hi : -(a u - 1) ≤ ∑ i, u i * z i := by exact_mod_cast h
    have hi' : -a u < ∑ i, u i * z i := by omega
    exact_mod_cast hi'

end PaperVerification.ToricGeometry.SmoothCompleteFan
