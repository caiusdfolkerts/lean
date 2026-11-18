module
public import bier
@[expose] public section
noncomputable section
open scoped Classical
namespace PalomarBier
open Bier
/-- Theorem 1 principal example, including the original ghost label. The Solution
supplies the concrete principalInput from the manuscript's explicit matrices. -/
theorem principal_example :
    ∃ I : Complex (Option (Fin 20 ⊕ Fin 145162)), ∃ hI : I.Proper,
      ¬ I.face {none} ∧ I.dimension = 9 ∧ (I.bier hI).IsSphere 145181 ∧
      (I.bier hI).dimension = 145181 ∧ (I.bier hI).vertices.card = 290365 ∧
      ¬ Polytopal (I.bier hI) := by
  refine ⟨Bier.principalInput, Bier.principalCore.ghost_proper, ?_, Bier.principal_example⟩
  simp [Bier.principalInput, Bier.Complex.ghost]
/-- Theorem 1 with all labels actual vertices of both input and Bier sphere. -/
theorem all_labels_example :
    ∃ I : Complex (Option (Fin 20 ⊕ Fin 145162)), ∃ hI : I.Proper,
      I.vertices = Finset.univ ∧ I.dimension = 9 ∧
      (I.bier hI).vertices = Finset.univ ∧ (I.bier hI).vertices.card = 290366 ∧
      (I.bier hI).dimension = 145181 ∧ (I.bier hI).IsSphere 145181 ∧
      ¬ Polytopal (I.bier hI) := by
  exact ⟨Bier.allLabelsInput,
    Bier.principalCore.isolatedExtension_proper Bier.principalCore_proper,
    Bier.all_labels_example⟩
/-- Theorem 1 with a self-dual input and centrally symmetric Bier sphere. -/
theorem self_dual_example :
    ∃ I : Complex ((Fin 20 ⊕ Fin 145162) ⊕ Bool), ∃ hI : I.Proper,
      (∀ F, (I.dual hI).face F ↔ I.face F) ∧
      (I.bier hI).IsSphere 145182 ∧ (I.bier hI).dimension = 145182 ∧
      (I.bier hI).vertices.card = 290368 ∧ (I.bier hI).IsCentrallySymmetric ∧
      ¬ Polytopal (I.bier hI) := by
  exact ⟨Bier.selfDualInput, Bier.principalCore.selfDualSuspension_proper,
    Bier.self_dual_example⟩
/-- Theorem 1 with input dimension three and the exact stated output counts. -/
theorem three_dimensional_example :
    ∃ I : Complex (Option (Fin 9 ⊕ (Fin 73 → Fin 2))), ∃ hI : I.Proper,
      I.dimension = 3 ∧ (I.bier hI).IsSphere (2 ^ 73 + 8) ∧
      (I.bier hI).dimension = 2 ^ 73 + 8 ∧ (I.bier hI).vertices.card = 2 ^ 74 + 19 ∧
      ¬ Polytopal (I.bier hI) := by
  exact ⟨Bier.threeDimensionalInput,
    (Bier.patternCore 9 3 73 Bier.enough_triples).ghost_proper,
    Bier.three_dimensional_example⟩
/-- The final construction for the full binomial-inequality parameter range. -/
theorem general_allSign_construction_unrestricted (m k : ℕ)
    (hchoose : m ^ 2 - m + 2 ≤ m.choose k) :
    ∃ I : Complex (Option (Fin m ⊕ (Fin (m ^ 2 - m + 1) → Fin 2))), ∃ hI : I.Proper,
      I.dimension = k ∧ (I.bier hI).IsSphere (m + 2 ^ (m ^ 2 - m + 1) - 1) ∧
      (I.bier hI).vertices.card = 2 * (m + 2 ^ (m ^ 2 - m + 1)) + 1 ∧
      ¬ Polytopal (I.bier hI) := by
  obtain ⟨h, hdim, hsphere, hvertices, hnon⟩ :=
    Bier.general_allSign_construction_unrestricted m k hchoose
  exact ⟨Bier.patternInput m k (m ^ 2 - m + 1) h,
    (Bier.patternCore m k (m ^ 2 - m + 1) h).ghost_proper,
    hdim, hsphere, hvertices, hnon⟩
end PalomarBier

/- Complete literal characterizations of every non-proof record field below.
These equations determine each supplied constructor completely by proof
irrelevance; they do not refer to opaque source primitives. -/
namespace PalomarBier.Spec
open LeanEval.Geometry.PlatonicClassification
/-- The face polytope has exactly the original extreme vertices lying in the face. -/
theorem facePolytope_vertices {n : ℕ} (P : ConvexPolytope n) {f : Set (E n)}
    (hf : P.IsFace f) :
    (facePolytope P hf).vertices = P.vertices.filter (fun v => v ∈ f) := by rfl
/-- Every realized face is exactly the standard basis image of an input face. -/
theorem standardRealization_faces {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : PreAbstractSimplicialComplex ι) :
    (DifferentialGeometry.Topology.Engulfing.standardRealization P).faces =
      (fun s : Finset ι => s.image (fun i => Pi.single i (1 : ℝ))) '' P.faces := by rfl
/-- The abstract complex contains exactly the actual nonempty faces. -/
theorem toAbstract_faces {V : Type*} [Fintype V] [DecidableEq V] (K : Bier.Complex V) :
    K.toAbstract.faces = {s | s.Nonempty ∧ K.face s} := by rfl
/-- Alexander duality is complement nonmembership on the full fixed ground set. -/
theorem dual_face {V : Type*} [Fintype V] [DecidableEq V] (K : Bier.Complex V)
    (hK : K.Proper) (s : Finset V) : (K.dual hK).face s ↔ ¬K.face sᶜ := by rfl
/-- All Bier faces are precisely the disjoint deleted-join face pairs. -/
theorem bier_face {V : Type*} [Fintype V] [DecidableEq V] (K : Bier.Complex V)
    (hK : K.Proper) (s : Finset (V ⊕ V)) :
    (K.bier hK).face s ↔
      K.face s.toLeft ∧ ¬K.face s.toRightᶜ ∧ Disjoint s.toLeft s.toRight := by rfl
/-- The new label is genuinely absent from every face. -/
theorem ghost_face {V : Type*} [Fintype V] [DecidableEq V] (K : Bier.Complex V)
    (s : Finset (Option V)) : K.ghost.face s ↔ none ∉ s ∧ K.face s.eraseNone := by rfl
end PalomarBier.Spec
