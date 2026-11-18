module

public import Papers.GraphicalZonotopes.TetrahedronPairWeights
public import Papers.GraphicalZonotopes.GraphicalCone
public import Papers.GraphicalZonotopes.Lattice

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ThreeTreeStates
open Finset
open RootedResponse
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual integral Möbius vector of the construction: every
tetrahedron has coefficient one, a triangle has the negative common column
sum, and an edge has the sum of its local maxima. All other coordinates
vanish, including the translation coordinates. -/
def coefficients {S : Finset V} {G : SimpleGraph V} (h : ThreeTreeOn S G)
    (s : CompatibleRows G) : SetFunction V := fun C =>
  if hC : C∈tetrahedra G then 1
  else if hT : C∈triangles G then -(triangleWeight h s ⟨C,hT⟩ : ℝ)
  else if hE : C∈edgeFamily G then (pairWeight G s C ((mem_edgeFamily G C).mp hE).1 : ℝ)
  else 0

theorem coefficients_tetrahedron {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {C : Finset V}
    (hC : C∈tetrahedra G) : coefficients h s C=1 := by
  simp only [coefficients,dif_pos hC]

theorem coefficients_triangle {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {T : Finset V}
    (hT : T∈triangles G) : coefficients h s T= -(triangleWeight h s ⟨T,hT⟩ : ℝ) := by
  have hnot : T∉tetrahedra G := by
    intro hm
    have h4 := (mem_filter.mp hm).2.1
    have h3 := (mem_triangles.mp hT).1
    omega
  simp only [coefficients,dif_neg hnot,dif_pos hT]

theorem coefficients_pair {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {E : Finset V}
    (hE : E∈edgeFamily G) :
    coefficients h s E=(pairWeight G s E ((mem_edgeFamily G E).mp hE).1 : ℝ) := by
  have h2 := ((mem_edgeFamily G E).mp hE).1
  have hnot4 : E∉tetrahedra G := by
    intro hm
    have h4 := (mem_filter.mp hm).2.1
    omega
  have hnot3 : E∉triangles G := by
    intro hm
    have h3 := (mem_triangles.mp hm).1
    omega
  simp only [coefficients,dif_neg hnot4,dif_neg hnot3,dif_pos hE]

theorem coefficients_triangle_values {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {T : Finset V}
    (hT : T∈triangles G) :
    coefficients h s T=0 ∨ coefficients h s T= -1 ∨ coefficients h s T= -2 := by
  rw [coefficients_triangle h s hT]
  rcases triangleWeight_mem h s ⟨T,hT⟩ with hd | hd | hd <;> rw [hd] <;> norm_num

theorem coefficients_cliqueSupported {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) : CliqueSupported G (coefficients h s) := by
  classical
  refine ⟨?_,?_,?_⟩
  · simp [coefficients,tetrahedra,triangles,edgeFamily]
  · intro v
    simp [coefficients,tetrahedra,triangles,edgeFamily]
  · intro C u v hu hv huv hnon
    have h4 : C∉tetrahedra G := by
      intro hm
      exact hnon ((mem_filter.mp hm).2.2 hu hv huv)
    have h3 : C∉triangles G := by
      intro hm
      exact hnon ((mem_triangles.mp hm).2 hu hv huv)
    have h2 : C∉edgeFamily G := by
      intro hm
      exact hnon (((mem_edgeFamily G C).mp hm).2 u hu v hv huv)
    simp only [coefficients,dif_neg h4,dif_neg h3,dif_neg h2]

theorem coefficients_integerValued {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) : IntegerValued (coefficients h s) := by
  classical
  intro C
  unfold coefficients
  split
  · exact ⟨1,by norm_num⟩
  · split
    · rename_i hT
      exact ⟨-(triangleWeight h s ⟨C,hT⟩ : ℤ),by simp⟩
    · split
      · rename_i hE
        exact ⟨pairWeight G s C ((mem_edgeFamily G C).mp hE).1,rfl⟩
      · exact ⟨0,by norm_num⟩

def setFunction {S : Finset V} {G : SimpleGraph V} (h : ThreeTreeOn S G)
    (s : CompatibleRows G) : SetFunction V := zeta (coefficients h s)

theorem setFunction_normalized_graphical {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) :
    TranslationNormalized (setFunction h s) ∧ Graphical G (setFunction h s) :=
  (cliqueSupported_iff G _).mp (coefficients_cliqueSupported h s)

theorem setFunction_integerValued {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) : IntegerValued (setFunction h s) :=
  zeta_integerValued (coefficients_integerValued h s)

theorem setFunction_mobius {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) :
    mobius (setFunction h s)=coefficients h s := mobius_zeta _

theorem setFunction_ne_zero {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) : setFunction h s≠0 := by
  intro hz
  have hy : coefficients h s=0 := by
    apply zeta_injective
    rw [show zeta (coefficients h s)=0 from hz]
    ext C
    simp [zeta]
  obtain ⟨C,hC⟩ := h.tetrahedra_nonempty
  have he := coefficients_tetrahedron h s hC
  rw [hy] at he
  norm_num at he

end ThreeTreeStates
end GraphicalZonotopes
