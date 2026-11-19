module
prelude
public import GraphCatalogueCore

@[expose] public section

/-!
# The 45 unordered edges on ten vertices

Small finite checks establish the endpoint encoding once. Every vertex
bijection then induces an incidence-preserving edge bijection by a general
proof, avoiding a separate 45-by-10 incidence check for every certificate frame.
-/
namespace Papers.RationalityTen.TenGraphEdges
open GrowthRenaming GraphCatalogueCore ConcreteGrowth

set_option maxHeartbeats 0
set_option maxRecDepth 10000

def firstTable : Table Nat :=
(.branch 22
 (.branch 11
 (.branch 5
 (.leaf 0)
 (.branch 8
 (.leaf 0)
 (.branch 9
 (.leaf 0)
 (.leaf 1))))
 (.branch 16
 (.leaf 1)
 (.branch 19
 (.branch 17
 (.leaf 1)
 (.leaf 2))
 (.leaf 2))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.leaf 2)
 (.leaf 3))
 (.branch 30
 (.leaf 3)
 (.leaf 4)))
 (.branch 39
 (.branch 36
 (.branch 34
 (.leaf 4)
 (.branch 35
 (.leaf 4)
 (.leaf 5)))
 (.leaf 5))
 (.branch 42
 (.leaf 6)
 (.branch 43
 (.leaf 7)
 (.branch 44
 (.leaf 7)
 (.leaf 8)))))))
def secondTable : Table Nat :=
(.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf 1)
 (.leaf 2))
 (.branch 3
 (.leaf 3)
 (.branch 4
 (.leaf 4)
 (.leaf 5))))
 (.branch 8
 (.branch 6
 (.leaf 6)
 (.branch 7
 (.leaf 7)
 (.leaf 8)))
 (.branch 9
 (.leaf 9)
 (.branch 10
 (.leaf 2)
 (.leaf 3)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf 4)
 (.leaf 5))
 (.branch 14
 (.leaf 6)
 (.branch 15
 (.leaf 7)
 (.leaf 8))))
 (.branch 19
 (.branch 17
 (.leaf 9)
 (.branch 18
 (.leaf 3)
 (.leaf 4)))
 (.branch 20
 (.leaf 5)
 (.branch 21
 (.leaf 6)
 (.leaf 7))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf 8)
 (.leaf 9))
 (.branch 25
 (.leaf 4)
 (.branch 26
 (.leaf 5)
 (.leaf 6))))
 (.branch 30
 (.branch 28
 (.leaf 7)
 (.branch 29
 (.leaf 8)
 (.leaf 9)))
 (.branch 31
 (.leaf 5)
 (.branch 32
 (.leaf 6)
 (.leaf 7)))))
 (.branch 39
 (.branch 36
 (.branch 34
 (.leaf 8)
 (.branch 35
 (.leaf 9)
 (.leaf 6)))
 (.branch 37
 (.leaf 7)
 (.branch 38
 (.leaf 8)
 (.leaf 9))))
 (.branch 42
 (.branch 40
 (.leaf 7)
 (.branch 41
 (.leaf 8)
 (.leaf 9)))
 (.branch 43
 (.leaf 8)
 (.leaf 9))))))
def pairTable : Table Nat :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf 0)
 (.branch 2
 (.leaf 0)
 (.leaf 1)))
 (.branch 4
 (.leaf 2)
 (.branch 5
 (.leaf 3)
 (.leaf 4))))
 (.branch 9
 (.branch 7
 (.leaf 5)
 (.branch 8
 (.leaf 6)
 (.leaf 7)))
 (.branch 10
 (.leaf 8)
 (.leaf 0))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf 9)
 (.branch 14
 (.leaf 10)
 (.leaf 11)))
 (.branch 16
 (.leaf 12)
 (.branch 17
 (.leaf 13)
 (.leaf 14))))
 (.branch 21
 (.branch 19
 (.leaf 15)
 (.branch 20
 (.leaf 16)
 (.leaf 1)))
 (.branch 23
 (.branch 22
 (.leaf 9)
 (.leaf 0))
 (.branch 24
 (.leaf 17)
 (.leaf 18))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf 19)
 (.branch 27
 (.leaf 20)
 (.leaf 21)))
 (.branch 29
 (.leaf 22)
 (.branch 30
 (.leaf 23)
 (.leaf 2))))
 (.branch 34
 (.branch 32
 (.leaf 10)
 (.branch 33
 (.leaf 17)
 (.leaf 0)))
 (.branch 35
 (.leaf 24)
 (.branch 36
 (.leaf 25)
 (.leaf 26)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf 27)
 (.branch 39
 (.leaf 28)
 (.leaf 29)))
 (.branch 41
 (.leaf 3)
 (.branch 42
 (.leaf 11)
 (.leaf 18))))
 (.branch 46
 (.branch 44
 (.leaf 24)
 (.branch 45
 (.leaf 0)
 (.leaf 30)))
 (.branch 48
 (.branch 47
 (.leaf 31)
 (.leaf 32))
 (.branch 49
 (.leaf 33)
 (.leaf 34)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf 4)
 (.branch 52
 (.leaf 12)
 (.leaf 19)))
 (.branch 54
 (.leaf 25)
 (.branch 55
 (.leaf 30)
 (.leaf 0))))
 (.branch 59
 (.branch 57
 (.leaf 35)
 (.branch 58
 (.leaf 36)
 (.leaf 37)))
 (.branch 60
 (.leaf 38)
 (.branch 61
 (.leaf 5)
 (.leaf 13)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf 20)
 (.branch 64
 (.leaf 26)
 (.leaf 31)))
 (.branch 66
 (.leaf 35)
 (.branch 67
 (.leaf 0)
 (.leaf 39))))
 (.branch 71
 (.branch 69
 (.leaf 40)
 (.branch 70
 (.leaf 41)
 (.leaf 6)))
 (.branch 73
 (.branch 72
 (.leaf 14)
 (.leaf 21))
 (.branch 74
 (.leaf 27)
 (.leaf 32))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf 36)
 (.branch 77
 (.leaf 39)
 (.leaf 0)))
 (.branch 79
 (.leaf 42)
 (.branch 80
 (.leaf 43)
 (.leaf 7))))
 (.branch 84
 (.branch 82
 (.leaf 15)
 (.branch 83
 (.leaf 22)
 (.leaf 28)))
 (.branch 85
 (.leaf 33)
 (.branch 86
 (.leaf 37)
 (.leaf 40)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf 42)
 (.branch 89
 (.leaf 0)
 (.leaf 44)))
 (.branch 91
 (.leaf 8)
 (.branch 92
 (.leaf 16)
 (.leaf 23))))
 (.branch 96
 (.branch 94
 (.leaf 29)
 (.branch 95
 (.leaf 34)
 (.leaf 38)))
 (.branch 98
 (.branch 97
 (.leaf 41)
 (.leaf 43))
 (.branch 99
 (.leaf 44)
 (.leaf 0))))))))

def first (edge : Fin 45) : Fin 10 := Fin.ofNat 10 (firstTable.get edge.val)
def second (edge : Fin 45) : Fin 10 := Fin.ofNat 10 (secondTable.get edge.val)
def encode (a b : Fin 10) : Fin 45 := Fin.ofNat 45 (pairTable.get (10*a.val+b.val))
def incidence (edge : Fin 45) (vertex : Fin 10) : Bool :=
  decide (vertex = first edge ∨ vertex = second edge)

theorem endpoints_distinct : ∀ edge, first edge ≠ second edge := by
  have h : (List.finRange 45).all (fun edge => decide (first edge ≠ second edge)) = true := by
    decide +kernel
  intro edge
  exact of_decide_eq_true (List.all_eq_true.mp h edge (List.mem_finRange edge))

theorem encode_incidence (a b vertex : Fin 10) (hne : a ≠ b) :
    incidence (encode a b) vertex = decide (vertex = a ∨ vertex = b) := by
  have h : (List.finRange 10).all (fun a => (List.finRange 10).all (fun b =>
      (List.finRange 10).all (fun vertex => decide (a = b) ||
        decide (incidence (encode a b) vertex = decide (vertex = a ∨ vertex = b))))) = true := by
    decide +kernel
  have ha := List.all_eq_true.mp h a (List.mem_finRange a)
  have hb := List.all_eq_true.mp ha b (List.mem_finRange b)
  have hv := List.all_eq_true.mp hb vertex (List.mem_finRange vertex)
  rcases Bool.or_eq_true_iff.mp hv with heq | hgood
  · exact False.elim (hne (of_decide_eq_true heq))
  · exact of_decide_eq_true hgood

theorem incidence_ext (a b : Fin 45) (h : ∀ vertex, incidence a vertex = incidence b vertex) :
    a = b := by
  have checked : (List.finRange 45).all (fun a => (List.finRange 45).all (fun b =>
      decide (a = b) || (List.finRange 10).any
        (fun vertex => decide (incidence a vertex ≠ incidence b vertex)))) = true := by
    decide +kernel
  have ha := List.all_eq_true.mp checked a (List.mem_finRange a)
  have hb := List.all_eq_true.mp ha b (List.mem_finRange b)
  rcases Bool.or_eq_true_iff.mp hb with heq | hdiff
  · exact of_decide_eq_true heq
  · obtain ⟨vertex, _, hvertex⟩ := List.any_eq_true.mp hdiff
    exact False.elim ((of_decide_eq_true hvertex) (h vertex))

def inverseBijection (p : Bijection (Fin 10)) : Bijection (Fin 10) where
  forward := p.inverse
  inverse := p.forward
  left_inverse := p.right_inverse
  right_inverse := p.left_inverse

def edgeMap (p : Bijection (Fin 10)) (edge : Fin 45) : Fin 45 :=
  encode (p.forward (first edge)) (p.forward (second edge))

theorem edgeMap_incidence (p : Bijection (Fin 10)) (edge : Fin 45) (vertex : Fin 10) :
    incidence (edgeMap p edge) (p.forward vertex) = incidence edge vertex := by
  rw [edgeMap, encode_incidence _ _ _ (fun h => endpoints_distinct edge (p.injective h))]
  apply Bool.eq_iff_iff.mpr
  simp only [incidence, decide_eq_true_eq]
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl (p.injective h)
    · exact Or.inr (p.injective h)
  · intro h
    rcases h with h | h
    · exact Or.inl (congrArg p.forward h)
    · exact Or.inr (congrArg p.forward h)

def edgeBijection (p : Bijection (Fin 10)) : Bijection (Fin 45) where
  forward := edgeMap p
  inverse := edgeMap (inverseBijection p)
  left_inverse edge := by
    apply incidence_ext
    intro vertex
    have hi := edgeMap_incidence (inverseBijection p) (edgeMap p edge) (p.forward vertex)
    simp only [inverseBijection, p.left_inverse] at hi
    exact hi.trans (edgeMap_incidence p edge vertex)
  right_inverse edge := by
    apply incidence_ext
    intro vertex
    have hi := edgeMap_incidence p (edgeMap (inverseBijection p) edge) (p.inverse vertex)
    simp only [p.right_inverse] at hi
    exact hi.trans (edgeMap_incidence (inverseBijection p) edge vertex)

def toRenaming (p : Bijection (Fin 10)) : IncidenceRenaming incidence where
  cells := edgeBijection p
  ridgeMap := p
  incidence := edgeMap_incidence p
  compatibility _ _ := rfl
  kind_preserved _ := rfl

def vertexMap (code : Nat) (vertex : Fin 10) : Fin 10 :=
  Fin.ofNat 10 (Nat.land (code >>> (4*vertex.val)) 15)

def permutationCheck (forward inverse : Nat) : Bool :=
  (List.finRange 10).all fun vertex =>
    decide (vertexMap inverse (vertexMap forward vertex) = vertex) &&
      decide (vertexMap forward (vertexMap inverse vertex) = vertex)

def checkedBijection (forward inverse : Nat) (h : permutationCheck forward inverse = true) :
    Bijection (Fin 10) where
  forward := vertexMap forward
  inverse := vertexMap inverse
  left_inverse vertex := of_decide_eq_true (Bool.and_eq_true_iff.mp
    (List.all_eq_true.mp h vertex (List.mem_finRange vertex))).1
  right_inverse vertex := of_decide_eq_true (Bool.and_eq_true_iff.mp
    (List.all_eq_true.mp h vertex (List.mem_finRange vertex))).2

#print axioms toRenaming
#print axioms checkedBijection
end Papers.RationalityTen.TenGraphEdges
