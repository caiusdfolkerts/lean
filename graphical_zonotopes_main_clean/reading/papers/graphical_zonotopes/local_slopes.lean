module

public import Papers.GraphicalZonotopes.GraphicalCone
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem mobius_sub (f g : SetFunction V) : mobius (f-g)=mobius f-mobius g := by
  exact (zetaEquiv (V := V)).symm.map_sub f g

@[simp] theorem mobius_smul (a : ℝ) (f : SetFunction V) : mobius (a • f)=a • mobius f := by
  exact (zetaEquiv (V := V)).symm.map_smul a f

/-- Equality of an entire elemental row determines every Möbius coefficient
containing its two endpoints. This is Boolean Möbius inversion, not a test on
selected contexts. -/
theorem mobius_scale_of_delta_scale {f z : SetFunction V} {u v : V}
    (huv : u≠v) (a : ℝ)
    (h : ∀ S : Finset V,u∉S → v∉S → delta f u v S=a*delta z u v S)
    {C : Finset V} (hu : u∈C) (hv : v∈C) : mobius f C=a*mobius z C := by
  have hzero : ∀ S : Finset V,u∉S → v∉S → delta (f-a • z) u v S=0 := by
    intro S hSu hSv
    rw [delta_sub,delta_smul,h S hSu hSv,sub_self]
  have hcoeff := (nonedge_coefficients_zero_iff (mobius (f-a • z)) huv).mp
    (by simpa only [zeta_mobius] using hzero) C hu hv
  rw [mobius_sub,mobius_smul] at hcoeff
  change mobius f C-a*mobius z C=0 at hcoeff
  exact sub_eq_zero.mp hcoeff

abbrev SlopeEdge (G : SimpleGraph V) := {e : V×V // G.Adj e.1 e.2}

/-- Edge scales interact whenever the same nonzero original Möbius
coefficient contains both edges. -/
def coefficientEdgeGraph (G : SimpleGraph V) (z : SetFunction V) :
    SimpleGraph (SlopeEdge G) where
  Adj e f := e≠f ∧ ∃ C : Finset V,mobius z C≠0 ∧
    e.1.1∈C ∧ e.1.2∈C ∧ f.1.1∈C ∧ f.1.2∈C
  symm := ⟨by
    rintro e f ⟨hef,C,hC,he₁,he₂,hf₁,hf₂⟩
    exact ⟨Ne.symm hef,C,hC,hf₁,hf₂,he₁,he₂⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A local-to-global extremality criterion used in the Boolean phase
construction. Each local hypothesis concerns every context of the actual
original elemental row. Connected nonzero coefficients then force all row
scales to agree. -/
theorem extremeSupermodular_of_local_row_lines {G : SimpleGraph V}
    {z : SetFunction V} (hn : TranslationNormalized z) (hs : Supermodular z)
    (hne : z≠0) (hG : Graphical G z)
    (hconn : (coefficientEdgeGraph G z).Connected)
    (hlocal : ∀ f : SetFunction V,TranslationNormalized f →
      (∀ u v,u≠v → ∀ S : Finset V,u∉S → v∉S →
        delta z u v S=0 → delta f u v S=0) →
      ∀ e : SlopeEdge G,∃ a : ℝ,∀ S : Finset V,
        e.1.1∉S → e.1.2∉S → delta f e.1.1 e.1.2 S=a*delta z e.1.1 e.1.2 S) :
    ExtremeSupermodular z := by
  classical
  apply extremeSupermodular_of_tightEquations hn hs hne
  intro f hfn hzeros
  choose a ha using hlocal f hfn hzeros
  obtain ⟨e₀⟩ := hconn.nonempty
  have hedge : ∀ e d : SlopeEdge G,(coefficientEdgeGraph G z).Adj e d → a e=a d := by
    rintro e d ⟨hed,C,hC,he₁,he₂,hd₁,hd₂⟩
    have he := mobius_scale_of_delta_scale (G.ne_of_adj e.2) (a e) (ha e) he₁ he₂
    have hd := mobius_scale_of_delta_scale (G.ne_of_adj d.2) (a d) (ha d) hd₁ hd₂
    exact mul_right_cancel₀ hC (he.symm.trans hd)
  have hconst : ∀ e : SlopeEdge G,a e=a e₀ := by
    intro e
    have hr := hconn.preconnected e e₀
    rw [SimpleGraph.reachable_eq_reflTransGen] at hr
    induction hr with
    | refl => rfl
    | @tail d e hpath hde ih => exact ih.trans (hedge d e hde)
  have hrow : ∀ u v,u≠v → ∀ S : Finset V,u∉S → v∉S →
      delta f u v S=a e₀*delta z u v S := by
    intro u v huv S hu hv
    by_cases hadj : G.Adj u v
    · let e : SlopeEdge G := ⟨(u,v),hadj⟩
      have h := ha e S hu hv
      rw [hconst e] at h
      exact h
    · have hz := hG u v huv hadj S hu hv
      rw [hzeros u v huv S hu hv hz,hz,mul_zero]
  have hwn : TranslationNormalized (f-a e₀ • z) := by
    refine ⟨?_,?_⟩
    · change f ∅-a e₀*z ∅=0
      rw [hfn.1,hn.1]
      ring
    · intro v
      change f {v}-a e₀*z {v}=0
      rw [hfn.2 v,hn.2 v]
      ring
  refine ⟨a e₀,sub_eq_zero.mp (normalized_zero_elemental_eq_zero hwn ?_)⟩
  intro u v huv S hu hv
  rw [delta_sub,delta_smul,hrow u v huv S hu hv,sub_self]

end GraphicalZonotopes
