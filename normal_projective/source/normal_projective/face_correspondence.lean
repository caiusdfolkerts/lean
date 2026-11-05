module
public import normal_projective.halfspace_faces
/-! # From genuine vertex–facet incidence to genuine exposed-face order -/
@[expose] public section
noncomputable section
open Set
namespace NormalProjective
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]

abbrev HalfspaceFaces (f : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ) :=
  {F : Set E // IsExposed ℝ (halfspaceRegion f h) F}

abbrev HalfspaceVertices (f : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ) :=
  (halfspaceRegion f h).extremePoints ℝ

theorem halfspace_face_subset_iff_vertices
    (f : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ)
    (hP : IsCompact (halfspaceRegion f h)) (F G : HalfspaceFaces f h) :
    F.val ⊆ G.val ↔ ∀ v : HalfspaceVertices f h, v.val ∈ F.val → v.val ∈ G.val := by
  constructor
  · intro h v hv
    exact h hv
  · intro h
    rw [exposedFace_eq_convexHull_vertices f _ hP F.property]
    exact convexHull_min (fun x hx => h ⟨x, hx.2⟩ hx.1)
      (G.property.convex (convex_halfspaceRegion f _))

theorem halfspace_face_ext_vertices
    (f : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ)
    (hP : IsCompact (halfspaceRegion f h)) (F G : HalfspaceFaces f h)
    (he : ∀ v : HalfspaceVertices f h, v.val ∈ F.val ↔ v.val ∈ G.val) : F = G := by
  apply Subtype.ext
  apply Set.Subset.antisymm
  · exact (halfspace_face_subset_iff_vertices f h hP F G).mpr (fun v => (he v).mp)
  · exact (halfspace_face_subset_iff_vertices f h hP G F).mpr (fun v => (he v).mpr)

/-- Transfer the universally tight labelled facets, with the empty face treated explicitly. -/
def transferFace (f g : ι → E →ₗ[ℝ] ℝ) (h k : ι → ℝ)
    (F : HalfspaceFaces f h) : HalfspaceFaces g k := by
  classical
  exact if hF : F.val.Nonempty then
    ⟨tightFace g k {i | ∀ y ∈ F.val, f i y = h i}, tightFace_isExposed g k _⟩
  else ⟨∅, isExposed_empty⟩

theorem mem_transferFace_iff
    (f g : ι → E →ₗ[ℝ] ℝ) (h k : ι → ℝ)
    (e : HalfspaceVertices f h ≃ HalfspaceVertices g k)
    (hinc : ∀ (v : HalfspaceVertices f h) i, f i v.val = h i ↔ g i (e v).val = k i)
    (F : HalfspaceFaces f h) (v : HalfspaceVertices f h) :
    (e v).val ∈ (transferFace f g h k F).val ↔ v.val ∈ F.val := by
  classical
  by_cases hF : F.val.Nonempty
  · simp only [transferFace, dif_pos hF]
    constructor
    · rintro ⟨_, hv⟩
      rw [exposedFace_eq_tightFace f h F.property hF]
      exact ⟨v.property.1, fun i hi => (hinc v i).mpr (hv i hi)⟩
    · intro hv
      exact ⟨(e v).property.1, fun i hi => (hinc v i).mp (hi _ hv)⟩
  · have hempty : F.val = ∅ := Set.not_nonempty_iff_eq_empty.mp hF
    simp [transferFace, hF, hempty]

/-- A vertex bijection preserving every labelled facet extends to the actual face lattice. -/
def halfspaceFaceOrderIso
    (f g : ι → E →ₗ[ℝ] ℝ) (h k : ι → ℝ)
    (hP : IsCompact (halfspaceRegion f h)) (hQ : IsCompact (halfspaceRegion g k))
    (e : HalfspaceVertices f h ≃ HalfspaceVertices g k)
    (hinc : ∀ (v : HalfspaceVertices f h) i, f i v.val = h i ↔ g i (e v).val = k i) :
    HalfspaceFaces f h ≃o HalfspaceFaces g k := by
  classical
  have hinc' : ∀ (v : HalfspaceVertices g k) i,
      g i v.val = k i ↔ f i (e.symm v).val = h i := by
    intro v i
    simpa using (hinc (e.symm v) i).symm
  refine
    { toFun := transferFace f g h k
      invFun := transferFace g f k h
      left_inv := ?_
      right_inv := ?_
      map_rel_iff' := ?_ }
  · intro F
    apply halfspace_face_ext_vertices f h hP
    intro v
    have ha := mem_transferFace_iff g f k h e.symm hinc'
      (transferFace f g h k F) (e v)
    have hb := mem_transferFace_iff f g h k e hinc F v
    simpa using ha.trans hb
  · intro F
    apply halfspace_face_ext_vertices g k hQ
    intro v
    have ha := mem_transferFace_iff f g h k e hinc
      (transferFace g f k h F) (e.symm v)
    have hb := mem_transferFace_iff g f k h e.symm hinc' F v
    simpa using ha.trans hb
  · intro F G
    change (transferFace f g h k F).val ⊆ (transferFace f g h k G).val ↔ F.val ⊆ G.val
    rw [halfspace_face_subset_iff_vertices f h hP F G,
      halfspace_face_subset_iff_vertices g k hQ]
    constructor
    · intro hh v hv
      exact (mem_transferFace_iff f g h k e hinc G v).mp
        (hh (e v) ((mem_transferFace_iff f g h k e hinc F v).mpr hv))
    · intro hh v hv
      obtain ⟨u, rfl⟩ := e.surjective v
      exact (mem_transferFace_iff f g h k e hinc G u).mpr
        (hh u ((mem_transferFace_iff f g h k e hinc F u).mp hv))

theorem halfspaceFaceOrderIso_facet
    (f g : ι → E →ₗ[ℝ] ℝ) (h k : ι → ℝ)
    (hP : IsCompact (halfspaceRegion f h)) (hQ : IsCompact (halfspaceRegion g k))
    (e : HalfspaceVertices f h ≃ HalfspaceVertices g k)
    (hinc : ∀ (v : HalfspaceVertices f h) i, f i v.val = h i ↔ g i (e v).val = k i)
    (i : ι) :
    (halfspaceFaceOrderIso f g h k hP hQ e hinc)
        ⟨tightFace f h {i}, tightFace_isExposed f h {i}⟩ =
      ⟨tightFace g k {i}, tightFace_isExposed g k {i}⟩ := by
  apply halfspace_face_ext_vertices g k hQ
  intro v
  obtain ⟨u, rfl⟩ := e.surjective v
  rw [show (halfspaceFaceOrderIso f g h k hP hQ e hinc)
        ⟨tightFace f h {i}, tightFace_isExposed f h {i}⟩ =
      transferFace f g h k ⟨tightFace f h {i}, tightFace_isExposed f h {i}⟩ from rfl]
  rw [mem_transferFace_iff f g h k e hinc]
  simpa [tightFace, u.property.1, (e u).property.1] using hinc u i

end NormalProjective

