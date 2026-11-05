module

public import PaperVerification.ToricWallStrictSupport
public import PaperVerification.ToricSupportAveragedEdges
public import PaperVerification.ToricCartierCharacterModules

@[expose] public section

/-!
# Actual polytopes and edge bounds from genuine wall degrees

The adjacent Cartier points differ by the primitive dual direction times
the wall slack. Their actual convex segment therefore contains every
initial segment up to a common slack bound. The proved classification of
all incident edges transfers this to all genuine polytope edges.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped Classical BigOperators

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

def integerWallSlack (a : Lattice n→ℤ) (s : «Σ».fullCones) (u : Lattice n) : ℤ :=
  a u+integerPairing u («Σ».cartierLatticePoint a s)

theorem integerWallSlack_cast (a : Lattice n→ℤ) (s : «Σ».fullCones) (u : Lattice n) :
    («Σ».integerWallSlack a s u : ℝ)=«Σ».wallSlack (fun v=>(a v:ℝ)) s u := by
  rw [wallSlack,← «Σ».embed_cartierLatticePoint a s,normalRay_pairing_lattice]
  simp only [integerWallSlack,integerPairing,Int.cast_add]

def HasWallSlacksAtLeast (a : Lattice n→ℤ) (bound : ℕ) : Prop :=
  ∀ s t : «Σ».fullCones,(s.val∩t.val).card=n-1 →
    ∀ u∈t.val,u∉s.val → (bound:ℤ)≤«Σ».integerWallSlack a s u

theorem positiveWallSlacks_of_bound (a : Lattice n→ℤ) (bound : ℕ)
    (hbound : 0<bound) (ha : «Σ».HasWallSlacksAtLeast a bound) :
    «Σ».HasPositiveWallSlacks (fun u=>(a u:ℝ)) := by
  intro s t hst u hut hus
  rw [← «Σ».integerWallSlack_cast]
  have hpos : (0:ℤ)<«Σ».integerWallSlack a s u :=
    lt_of_lt_of_le (by exact_mod_cast hbound) (ha s t hst u hut hus)
  exact_mod_cast hpos

theorem support_edgesAtLeast_of_wallSlacks (hpure : «Σ».IsPure)
    (a : Lattice n→ℤ) (ha : «Σ».IsStrictSupport (fun u=>(a u:ℝ))) (bound : ℕ)
    (hbound : «Σ».HasWallSlacksAtLeast a bound) :
    («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast bound := by
  apply «Σ».support_edgesAtLeast_of_axis_points hpure a ha bound
  intro s j
  obtain ⟨t,w,ht,hwj,hmeet,hwt,hws⟩ := «Σ».exists_full_opposite_wall hpure s j
  have hcard : (s.val∩t.val).card=n-1 := by rw [hmeet,basis_wall_card]
  let aR : Lattice n→ℝ := fun u=>(a u:ℝ)
  let L := «Σ».wallSlack aR s w
  have hL : (bound:ℝ)≤L := by
    change (bound:ℝ) ≤ «Σ».wallSlack (fun v => (a v : ℝ)) s w
    rw [← «Σ».integerWallSlack_cast a s w]
    exact_mod_cast hbound s t hcard w hwt hws
  have hLp : 0<L := by
    have hw : w∈«Σ».rays := «Σ».ray_mem_of_mem_cone («Σ».fullCones_mem t) hwt
    have h := «Σ».cartierPoint_support_lt_of_not_mem ha s hw hws
    dsimp [L,wallSlack]
    linarith
  have hsv : «Σ».cartierPoint aR s∈«Σ».fanPolytope aR :=
    «Σ».cartierPoint_mem_of_nef (IsStrictSupport.isNef «Σ» ha) s
  have htv : «Σ».cartierPoint aR t∈«Σ».fanPolytope aR :=
    «Σ».cartierPoint_mem_of_nef (IsStrictSupport.isNef «Σ» ha) t
  let «λ» : ℝ := bound/L
  have «hλ0» : 0≤«λ» := div_nonneg (Nat.cast_nonneg _) hLp.le
  have «hλ1» : «λ»≤1 := (div_le_one hLp).mpr hL
  have «hλL» : «λ»*L=bound := div_mul_cancel₀ _ hLp.ne'
  have hseg : «Σ».cartierPoint aR s+(bound:ℝ) • «Σ».cartierBasis s j ∈
      segment ℝ («Σ».cartierPoint aR s) («Σ».cartierPoint aR t) := by
    refine ⟨1-«λ»,«λ»,sub_nonneg.mpr «hλ1»,«hλ0»,by ring,?_⟩
    rw [«Σ».cartierPoint_across_wall aR s t j w ht hwj,
      smul_add,smul_smul,«hλL»,sub_smul,one_smul]
    abel
  exact («Σ».convex_fanPolytope aR).segment_subset hsv htv hseg

/-- Positive lower bounds on all actual wall degrees construct the
entire genuine smooth lattice polytope with the prescribed fan and with
the same lower bound on every actual edge. -/
theorem exists_smooth_latticePolytope_of_positive_wall_bounds
    (hpure : «Σ».IsPure) (a : Lattice n→ℤ) (bound : ℕ) (hbound : 0<bound)
    (ha : «Σ».HasWallSlacksAtLeast a bound) :
    ∃ P : LatticePolytope n,
      P.carrier=«Σ».fanPolytope (fun u=>(a u:ℝ)) ∧
      P.Smooth ∧ P.normalFan=«Σ».realCones ∧ P.EdgesAtLeast bound := by
  let hs := «Σ».strictSupport_of_positive_wallSlacks hpure (fun u=>(a u:ℝ))
    («Σ».positiveWallSlacks_of_bound a bound hbound ha)
  exact ⟨«Σ».supportLatticePolytope hpure a hs,
    «Σ».supportLatticePolytope_carrier hpure a hs,
    «Σ».supportLatticePolytope_smooth hpure a hs,
    «Σ».supportLatticePolytope_normalFan hpure a hs,
    «Σ».support_edgesAtLeast_of_wallSlacks hpure a hs bound ha⟩

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.support_edgesAtLeast_of_wallSlacks
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.exists_smooth_latticePolytope_of_positive_wall_bounds
