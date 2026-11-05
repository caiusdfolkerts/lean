module
prelude
public import PureGP.SupportCore
public import PureGP.Cases.C042

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.PureGP.Initializers.C042
/- Finite consequence of support-sign equations; their actual geometry is separate. -/
def anchor : Nat := 0
def globalNegation : Bool := Bool.false
def edgeTable : Table SupportEdge := (Table.node 112 (Table.node 56 (Table.node 28 (Table.node 14 (Table.node 7 (Table.node 3 (Table.node 1 (Table.leaf (SupportEdge.mk 18 33 Bool.false)) (Table.node 2 (Table.leaf (SupportEdge.mk 18 43 Bool.false)) (Table.leaf (SupportEdge.mk 18 49 Bool.false)))) (Table.node 5 (Table.node 4 (Table.leaf (SupportEdge.mk 18 52 Bool.false)) (Table.leaf (SupportEdge.mk 19 34 Bool.false))) (Table.node 6 (Table.leaf (SupportEdge.mk 19 44 Bool.false)) (Table.leaf (SupportEdge.mk 19 50 Bool.false))))) (Table.node 10 (Table.node 8 (Table.leaf (SupportEdge.mk 19 53 Bool.false)) (Table.node 9 (Table.leaf (SupportEdge.mk 20 35 Bool.false)) (Table.leaf (SupportEdge.mk 20 45 Bool.false)))) (Table.node 12 (Table.node 11 (Table.leaf (SupportEdge.mk 20 51 Bool.false)) (Table.leaf (SupportEdge.mk 20 54 Bool.false))) (Table.node 13 (Table.leaf (SupportEdge.mk 90 110 Bool.false)) (Table.leaf (SupportEdge.mk 90 120 Bool.false)))))) (Table.node 21 (Table.node 17 (Table.node 15 (Table.leaf (SupportEdge.mk 90 124 Bool.false)) (Table.node 16 (Table.leaf (SupportEdge.mk 90 125 Bool.false)) (Table.leaf (SupportEdge.mk 160 180 Bool.false)))) (Table.node 19 (Table.node 18 (Table.leaf (SupportEdge.mk 160 190 Bool.false)) (Table.leaf (SupportEdge.mk 160 194 Bool.false))) (Table.node 20 (Table.leaf (SupportEdge.mk 160 195 Bool.false)) (Table.leaf (SupportEdge.mk 0 57 Bool.true))))) (Table.node 24 (Table.node 22 (Table.leaf (SupportEdge.mk 0 58 Bool.true)) (Table.node 23 (Table.leaf (SupportEdge.mk 0 59 Bool.true)) (Table.leaf (SupportEdge.mk 0 60 Bool.true)))) (Table.node 26 (Table.node 25 (Table.leaf (SupportEdge.mk 1 61 Bool.true)) (Table.leaf (SupportEdge.mk 1 62 Bool.true))) (Table.node 27 (Table.leaf (SupportEdge.mk 1 63 Bool.true)) (Table.leaf (SupportEdge.mk 1 64 Bool.true))))))) (Table.node 42 (Table.node 35 (Table.node 31 (Table.node 29 (Table.leaf (SupportEdge.mk 6 71 Bool.true)) (Table.node 30 (Table.leaf (SupportEdge.mk 6 72 Bool.true)) (Table.leaf (SupportEdge.mk 6 73 Bool.true)))) (Table.node 33 (Table.node 32 (Table.leaf (SupportEdge.mk 6 74 Bool.true)) (Table.leaf (SupportEdge.mk 21 91 Bool.true))) (Table.node 34 (Table.leaf (SupportEdge.mk 21 92 Bool.true)) (Table.leaf (SupportEdge.mk 21 93 Bool.true))))) (Table.node 38 (Table.node 36 (Table.leaf (SupportEdge.mk 21 94 Bool.true)) (Table.node 37 (Table.leaf (SupportEdge.mk 126 196 Bool.false)) (Table.leaf (SupportEdge.mk 126 197 Bool.false)))) (Table.node 40 (Table.node 39 (Table.leaf (SupportEdge.mk 126 198 Bool.false)) (Table.leaf (SupportEdge.mk 126 199 Bool.false))) (Table.node 41 (Table.leaf (SupportEdge.mk 23 58 Bool.false)) (Table.leaf (SupportEdge.mk 23 92 Bool.false)))))) (Table.node 49 (Table.node 45 (Table.node 43 (Table.leaf (SupportEdge.mk 23 95 Bool.false)) (Table.node 44 (Table.leaf (SupportEdge.mk 23 99 Bool.true)) (Table.leaf (SupportEdge.mk 24 59 Bool.false)))) (Table.node 47 (Table.node 46 (Table.leaf (SupportEdge.mk 24 93 Bool.false)) (Table.leaf (SupportEdge.mk 24 96 Bool.false))) (Table.node 48 (Table.leaf (SupportEdge.mk 24 100 Bool.true)) (Table.leaf (SupportEdge.mk 33 68 Bool.false))))) (Table.node 52 (Table.node 50 (Table.leaf (SupportEdge.mk 33 104 Bool.true)) (Table.node 51 (Table.leaf (SupportEdge.mk 33 107 Bool.true)) (Table.leaf (SupportEdge.mk 33 110 Bool.true)))) (Table.node 54 (Table.node 53 (Table.leaf (SupportEdge.mk 43 78 Bool.false)) (Table.leaf (SupportEdge.mk 43 114 Bool.true))) (Table.node 55 (Table.leaf (SupportEdge.mk 43 117 Bool.true)) (Table.leaf (SupportEdge.mk 43 120 Bool.true)))))))) (Table.node 84 (Table.node 70 (Table.node 63 (Table.node 59 (Table.node 57 (Table.leaf (SupportEdge.mk 168 203 Bool.false)) (Table.node 58 (Table.leaf (SupportEdge.mk 168 234 Bool.false)) (Table.leaf (SupportEdge.mk 168 237 Bool.false)))) (Table.node 61 (Table.node 60 (Table.leaf (SupportEdge.mk 168 240 Bool.false)) (Table.leaf (SupportEdge.mk 28 63 Bool.false))) (Table.node 62 (Table.leaf (SupportEdge.mk 28 93 Bool.true)) (Table.leaf (SupportEdge.mk 28 102 Bool.false))))) (Table.node 66 (Table.node 64 (Table.leaf (SupportEdge.mk 28 104 Bool.false)) (Table.node 65 (Table.leaf (SupportEdge.mk 29 64 Bool.false)) (Table.leaf (SupportEdge.mk 29 94 Bool.true)))) (Table.node 68 (Table.node 67 (Table.leaf (SupportEdge.mk 29 103 Bool.false)) (Table.leaf (SupportEdge.mk 29 105 Bool.false))) (Table.node 69 (Table.leaf (SupportEdge.mk 35 70 Bool.false)) (Table.leaf (SupportEdge.mk 35 100 Bool.true)))))) (Table.node 77 (Table.node 73 (Table.node 71 (Table.leaf (SupportEdge.mk 35 109 Bool.true)) (Table.node 72 (Table.leaf (SupportEdge.mk 35 110 Bool.true)) (Table.leaf (SupportEdge.mk 51 86 Bool.false)))) (Table.node 75 (Table.node 74 (Table.leaf (SupportEdge.mk 51 116 Bool.false)) (Table.leaf (SupportEdge.mk 51 123 Bool.true))) (Table.node 76 (Table.leaf (SupportEdge.mk 51 124 Bool.true)) (Table.leaf (SupportEdge.mk 176 211 Bool.false))))) (Table.node 80 (Table.node 78 (Table.leaf (SupportEdge.mk 176 236 Bool.true)) (Table.node 79 (Table.leaf (SupportEdge.mk 176 243 Bool.false)) (Table.leaf (SupportEdge.mk 176 244 Bool.false)))) (Table.node 82 (Table.node 81 (Table.leaf (SupportEdge.mk 37 72 Bool.false)) (Table.leaf (SupportEdge.mk 37 92 Bool.false))) (Table.node 83 (Table.leaf (SupportEdge.mk 37 111 Bool.false)) (Table.leaf (SupportEdge.mk 37 114 Bool.true))))))) (Table.node 98 (Table.node 91 (Table.node 87 (Table.node 85 (Table.leaf (SupportEdge.mk 37 115 Bool.true)) (Table.node 86 (Table.leaf (SupportEdge.mk 46 81 Bool.false)) (Table.leaf (SupportEdge.mk 46 101 Bool.false)))) (Table.node 89 (Table.node 88 (Table.leaf (SupportEdge.mk 46 111 Bool.false)) (Table.leaf (SupportEdge.mk 46 121 Bool.true))) (Table.node 90 (Table.leaf (SupportEdge.mk 48 83 Bool.false)) (Table.leaf (SupportEdge.mk 48 103 Bool.false))))) (Table.node 94 (Table.node 92 (Table.leaf (SupportEdge.mk 48 113 Bool.false)) (Table.node 93 (Table.leaf (SupportEdge.mk 48 123 Bool.false)) (Table.leaf (SupportEdge.mk 50 85 Bool.false)))) (Table.node 96 (Table.node 95 (Table.leaf (SupportEdge.mk 50 105 Bool.false)) (Table.leaf (SupportEdge.mk 50 115 Bool.false))) (Table.node 97 (Table.leaf (SupportEdge.mk 50 124 Bool.false)) (Table.leaf (SupportEdge.mk 53 88 Bool.false)))))) (Table.node 105 (Table.node 101 (Table.node 99 (Table.leaf (SupportEdge.mk 53 108 Bool.false)) (Table.node 100 (Table.leaf (SupportEdge.mk 53 118 Bool.false)) (Table.leaf (SupportEdge.mk 53 125 Bool.false)))) (Table.node 103 (Table.node 102 (Table.leaf (SupportEdge.mk 192 227 Bool.false)) (Table.leaf (SupportEdge.mk 192 242 Bool.false))) (Table.node 104 (Table.leaf (SupportEdge.mk 192 247 Bool.false)) (Table.leaf (SupportEdge.mk 192 251 Bool.true))))) (Table.node 108 (Table.node 106 (Table.leaf (SupportEdge.mk 0 126 Bool.false)) (Table.node 107 (Table.leaf (SupportEdge.mk 0 128 Bool.false)) (Table.leaf (SupportEdge.mk 0 129 Bool.false)))) (Table.node 110 (Table.node 109 (Table.leaf (SupportEdge.mk 0 130 Bool.false)) (Table.leaf (SupportEdge.mk 2 131 Bool.true))) (Table.node 111 (Table.leaf (SupportEdge.mk 2 135 Bool.false)) (Table.leaf (SupportEdge.mk 2 136 Bool.false))))))))) (Table.node 168 (Table.node 140 (Table.node 126 (Table.node 119 (Table.node 115 (Table.node 113 (Table.leaf (SupportEdge.mk 2 137 Bool.false)) (Table.node 114 (Table.leaf (SupportEdge.mk 7 141 Bool.true)) (Table.leaf (SupportEdge.mk 7 145 Bool.false)))) (Table.node 117 (Table.node 116 (Table.leaf (SupportEdge.mk 7 146 Bool.false)) (Table.leaf (SupportEdge.mk 7 147 Bool.false))) (Table.node 118 (Table.leaf (SupportEdge.mk 22 161 Bool.true)) (Table.leaf (SupportEdge.mk 22 165 Bool.false))))) (Table.node 122 (Table.node 120 (Table.leaf (SupportEdge.mk 22 166 Bool.false)) (Table.node 121 (Table.leaf (SupportEdge.mk 22 167 Bool.false)) (Table.leaf (SupportEdge.mk 57 196 Bool.true)))) (Table.node 124 (Table.node 123 (Table.leaf (SupportEdge.mk 57 200 Bool.false)) (Table.leaf (SupportEdge.mk 57 201 Bool.false))) (Table.node 125 (Table.leaf (SupportEdge.mk 57 202 Bool.false)) (Table.leaf (SupportEdge.mk 6 126 Bool.false)))))) (Table.node 133 (Table.node 129 (Table.node 127 (Table.leaf (SupportEdge.mk 6 141 Bool.false)) (Table.node 128 (Table.leaf (SupportEdge.mk 6 143 Bool.false)) (Table.leaf (SupportEdge.mk 6 144 Bool.false)))) (Table.node 131 (Table.node 130 (Table.leaf (SupportEdge.mk 8 128 Bool.false)) (Table.leaf (SupportEdge.mk 8 145 Bool.true))) (Table.node 132 (Table.leaf (SupportEdge.mk 8 148 Bool.false)) (Table.leaf (SupportEdge.mk 8 149 Bool.false))))) (Table.node 136 (Table.node 134 (Table.leaf (SupportEdge.mk 12 132 Bool.false)) (Table.node 135 (Table.leaf (SupportEdge.mk 12 151 Bool.true)) (Table.leaf (SupportEdge.mk 12 154 Bool.false)))) (Table.node 138 (Table.node 137 (Table.leaf (SupportEdge.mk 12 155 Bool.false)) (Table.leaf (SupportEdge.mk 37 162 Bool.true))) (Table.node 139 (Table.leaf (SupportEdge.mk 37 181 Bool.true)) (Table.leaf (SupportEdge.mk 37 184 Bool.false))))))) (Table.node 154 (Table.node 147 (Table.node 143 (Table.node 141 (Table.leaf (SupportEdge.mk 37 185 Bool.false)) (Table.node 142 (Table.leaf (SupportEdge.mk 72 197 Bool.true)) (Table.leaf (SupportEdge.mk 72 216 Bool.true)))) (Table.node 145 (Table.node 144 (Table.leaf (SupportEdge.mk 72 219 Bool.false)) (Table.leaf (SupportEdge.mk 72 220 Bool.false))) (Table.node 146 (Table.leaf (SupportEdge.mk 15 135 Bool.false)) (Table.leaf (SupportEdge.mk 15 145 Bool.false))))) (Table.node 150 (Table.node 148 (Table.leaf (SupportEdge.mk 15 151 Bool.false)) (Table.node 149 (Table.leaf (SupportEdge.mk 15 157 Bool.false)) (Table.leaf (SupportEdge.mk 17 137 Bool.false)))) (Table.node 152 (Table.node 151 (Table.leaf (SupportEdge.mk 17 147 Bool.false)) (Table.leaf (SupportEdge.mk 17 153 Bool.false))) (Table.node 153 (Table.leaf (SupportEdge.mk 17 159 Bool.true)) (Table.leaf (SupportEdge.mk 19 139 Bool.false)))))) (Table.node 161 (Table.node 157 (Table.node 155 (Table.leaf (SupportEdge.mk 19 149 Bool.false)) (Table.node 156 (Table.leaf (SupportEdge.mk 19 155 Bool.false)) (Table.leaf (SupportEdge.mk 19 160 Bool.true)))) (Table.node 159 (Table.node 158 (Table.leaf (SupportEdge.mk 53 178 Bool.true)) (Table.leaf (SupportEdge.mk 53 188 Bool.true))) (Table.node 160 (Table.leaf (SupportEdge.mk 53 192 Bool.true)) (Table.leaf (SupportEdge.mk 53 195 Bool.true))))) (Table.node 164 (Table.node 162 (Table.leaf (SupportEdge.mk 88 213 Bool.true)) (Table.node 163 (Table.leaf (SupportEdge.mk 88 223 Bool.true)) (Table.leaf (SupportEdge.mk 88 227 Bool.true)))) (Table.node 166 (Table.node 165 (Table.leaf (SupportEdge.mk 88 230 Bool.true)) (Table.leaf (SupportEdge.mk 41 146 Bool.true))) (Table.node 167 (Table.leaf (SupportEdge.mk 41 166 Bool.true)) (Table.leaf (SupportEdge.mk 41 182 Bool.false)))))))) (Table.node 196 (Table.node 182 (Table.node 175 (Table.node 171 (Table.node 169 (Table.leaf (SupportEdge.mk 41 187 Bool.true)) (Table.node 170 (Table.leaf (SupportEdge.mk 42 147 Bool.true)) (Table.leaf (SupportEdge.mk 42 167 Bool.true)))) (Table.node 173 (Table.node 172 (Table.leaf (SupportEdge.mk 42 183 Bool.false)) (Table.leaf (SupportEdge.mk 42 188 Bool.true))) (Table.node 174 (Table.leaf (SupportEdge.mk 45 150 Bool.true)) (Table.leaf (SupportEdge.mk 45 170 Bool.true))))) (Table.node 178 (Table.node 176 (Table.leaf (SupportEdge.mk 45 186 Bool.false)) (Table.node 177 (Table.leaf (SupportEdge.mk 45 190 Bool.false)) (Table.leaf (SupportEdge.mk 54 159 Bool.true)))) (Table.node 180 (Table.node 179 (Table.leaf (SupportEdge.mk 54 179 Bool.true)) (Table.leaf (SupportEdge.mk 54 193 Bool.true))) (Table.node 181 (Table.leaf (SupportEdge.mk 54 195 Bool.false)) (Table.leaf (SupportEdge.mk 119 224 Bool.false)))))) (Table.node 189 (Table.node 185 (Table.node 183 (Table.leaf (SupportEdge.mk 119 239 Bool.false)) (Table.node 184 (Table.leaf (SupportEdge.mk 119 248 Bool.true)) (Table.leaf (SupportEdge.mk 119 250 Bool.false)))) (Table.node 187 (Table.node 186 (Table.leaf (SupportEdge.mk 43 148 Bool.true)) (Table.leaf (SupportEdge.mk 43 168 Bool.true))) (Table.node 188 (Table.leaf (SupportEdge.mk 43 184 Bool.false)) (Table.leaf (SupportEdge.mk 43 187 Bool.false))))) (Table.node 192 (Table.node 190 (Table.leaf (SupportEdge.mk 43 190 Bool.false)) (Table.node 191 (Table.leaf (SupportEdge.mk 61 131 Bool.false)) (Table.leaf (SupportEdge.mk 61 196 Bool.false)))) (Table.node 194 (Table.node 193 (Table.leaf (SupportEdge.mk 61 206 Bool.false)) (Table.leaf (SupportEdge.mk 61 208 Bool.false))) (Table.node 195 (Table.leaf (SupportEdge.mk 63 133 Bool.false)) (Table.leaf (SupportEdge.mk 63 198 Bool.false))))))) (Table.node 210 (Table.node 203 (Table.node 199 (Table.node 197 (Table.leaf (SupportEdge.mk 63 209 Bool.true)) (Table.node 198 (Table.leaf (SupportEdge.mk 63 211 Bool.false)) (Table.leaf (SupportEdge.mk 66 136 Bool.false)))) (Table.node 201 (Table.node 200 (Table.leaf (SupportEdge.mk 66 201 Bool.false)) (Table.leaf (SupportEdge.mk 66 212 Bool.true))) (Table.node 202 (Table.leaf (SupportEdge.mk 66 214 Bool.false)) (Table.leaf (SupportEdge.mk 82 152 Bool.false))))) (Table.node 206 (Table.node 204 (Table.leaf (SupportEdge.mk 82 217 Bool.true)) (Table.node 205 (Table.leaf (SupportEdge.mk 82 226 Bool.true)) (Table.leaf (SupportEdge.mk 82 228 Bool.false)))) (Table.node 208 (Table.node 207 (Table.leaf (SupportEdge.mk 102 172 Bool.false)) (Table.leaf (SupportEdge.mk 102 232 Bool.true))) (Table.node 209 (Table.leaf (SupportEdge.mk 102 241 Bool.true)) (Table.leaf (SupportEdge.mk 102 243 Bool.false)))))) (Table.node 217 (Table.node 213 (Table.node 211 (Table.leaf (SupportEdge.mk 81 151 Bool.false)) (Table.node 212 (Table.leaf (SupportEdge.mk 81 206 Bool.true)) (Table.leaf (SupportEdge.mk 81 216 Bool.true)))) (Table.node 215 (Table.node 214 (Table.leaf (SupportEdge.mk 81 226 Bool.false)) (Table.leaf (SupportEdge.mk 81 227 Bool.false))) (Table.node 216 (Table.leaf (SupportEdge.mk 96 166 Bool.false)) (Table.leaf (SupportEdge.mk 96 201 Bool.false))))) (Table.node 221 (Table.node 219 (Table.node 218 (Table.leaf (SupportEdge.mk 96 232 Bool.false)) (Table.leaf (SupportEdge.mk 96 237 Bool.true))) (Table.node 220 (Table.leaf (SupportEdge.mk 96 239 Bool.false)) (Table.leaf (SupportEdge.mk 123 193 Bool.false)))) (Table.node 223 (Table.node 222 (Table.leaf (SupportEdge.mk 123 228 Bool.false)) (Table.leaf (SupportEdge.mk 123 243 Bool.false))) (Table.node 224 (Table.leaf (SupportEdge.mk 123 248 Bool.false)) (Table.leaf (SupportEdge.mk 123 251 Bool.false))))))))))
def edge (index : Nat) : SupportEdge := edgeTable.get index
def zeroTable : Table Nat := (Table.node 5 (Table.node 2 (Table.node 1 (Table.leaf 55) (Table.leaf 56)) (Table.node 3 (Table.leaf 98) (Table.node 4 (Table.leaf 106) (Table.leaf 122)))) (Table.node 7 (Table.node 6 (Table.leaf 127) (Table.leaf 142)) (Table.node 8 (Table.leaf 158) (Table.node 9 (Table.leaf 189) (Table.leaf 207)))))
def zero (index : Nat) : Nat := zeroTable.get index
def SupportEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 225 → (edge index).Holds assignment
def ZeroEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 10 → Eq (assignment (zero index)) Sign.zero

theorem initial_domains_sound (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment) :
    ∀ index, LT.lt index 252 →
      Eq ((Cases.C042.initial index).allows
        (Sign.withNegation globalNegation (assignment index))) Bool.true :=
  let hnode57 : Eq (assignment 57) Sign.negative :=
    Eq.trans (h_support 20 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode58 : Eq (assignment 58) Sign.negative :=
    Eq.trans (h_support 21 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode59 : Eq (assignment 59) Sign.negative :=
    Eq.trans (h_support 22 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode60 : Eq (assignment 60) Sign.negative :=
    Eq.trans (h_support 23 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode126 : Eq (assignment 126) Sign.positive :=
    Eq.trans (h_support 105 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode128 : Eq (assignment 128) Sign.positive :=
    Eq.trans (h_support 106 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode129 : Eq (assignment 129) Sign.positive :=
    Eq.trans (h_support 107 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode130 : Eq (assignment 130) Sign.positive :=
    Eq.trans (h_support 108 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode6 : Eq (assignment 6) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 125 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode126)
  let hnode8 : Eq (assignment 8) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 129 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode128)
  let hnode23 : Eq (assignment 23) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 40 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode58)
  let hnode24 : Eq (assignment 24) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 44 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode59)
  let hnode196 : Eq (assignment 196) Sign.positive :=
    Eq.trans (h_support 121 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode57)
  let hnode197 : Eq (assignment 197) Sign.positive :=
    Eq.trans (h_support 37 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode126)
  let hnode198 : Eq (assignment 198) Sign.positive :=
    Eq.trans (h_support 38 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode126)
  let hnode199 : Eq (assignment 199) Sign.positive :=
    Eq.trans (h_support 39 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode126)
  let hnode200 : Eq (assignment 200) Sign.negative :=
    Eq.trans (h_support 122 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode57)
  let hnode201 : Eq (assignment 201) Sign.negative :=
    Eq.trans (h_support 123 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode57)
  let hnode202 : Eq (assignment 202) Sign.negative :=
    Eq.trans (h_support 124 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode57)
  let hnode61 : Eq (assignment 61) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 191 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode196)
  let hnode63 : Eq (assignment 63) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 195 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode198)
  let hnode66 : Eq (assignment 66) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 199 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode201)
  let hnode71 : Eq (assignment 71) Sign.negative :=
    Eq.trans (h_support 28 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode6)
  let hnode72 : Eq (assignment 72) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 141 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode197)
  let hnode73 : Eq (assignment 73) Sign.negative :=
    Eq.trans (h_support 30 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode6)
  let hnode74 : Eq (assignment 74) Sign.negative :=
    Eq.trans (h_support 31 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode6)
  let hnode92 : Eq (assignment 92) Sign.negative :=
    Eq.trans (h_support 41 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode23)
  let hnode93 : Eq (assignment 93) Sign.negative :=
    Eq.trans (h_support 45 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode24)
  let hnode95 : Eq (assignment 95) Sign.negative :=
    Eq.trans (h_support 42 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode23)
  let hnode96 : Eq (assignment 96) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 216 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode201)
  let hnode99 : Eq (assignment 99) Sign.positive :=
    Eq.trans (h_support 43 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode23)
  let hnode100 : Eq (assignment 100) Sign.positive :=
    Eq.trans (h_support 47 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode24)
  let hnode141 : Eq (assignment 141) Sign.positive :=
    Eq.trans (h_support 126 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode6)
  let hnode143 : Eq (assignment 143) Sign.positive :=
    Eq.trans (h_support 127 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode6)
  let hnode144 : Eq (assignment 144) Sign.positive :=
    Eq.trans (h_support 128 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode6)
  let hnode145 : Eq (assignment 145) Sign.negative :=
    Eq.trans (h_support 130 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode8)
  let hnode148 : Eq (assignment 148) Sign.positive :=
    Eq.trans (h_support 131 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode8)
  let hnode149 : Eq (assignment 149) Sign.positive :=
    Eq.trans (h_support 132 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode8)
  let hnode1 : Eq (assignment 1) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 24 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode61)
  let hnode7 : Eq (assignment 7) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 113 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode141)
  let hnode15 : Eq (assignment 15) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 146 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode145)
  let hnode19 : Eq (assignment 19) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 154 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode149)
  let hnode21 : Eq (assignment 21) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 33 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode92)
  let hnode28 : Eq (assignment 28) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 61 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode93)
  let hnode35 : Eq (assignment 35) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 69 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode100)
  let hnode37 : Eq (assignment 37) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 81 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode92)
  let hnode43 : Eq (assignment 43) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 185 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode148)
  let hnode131 : Eq (assignment 131) Sign.positive :=
    Eq.trans (h_support 190 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode61)
  let hnode133 : Eq (assignment 133) Sign.positive :=
    Eq.trans (h_support 194 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode63)
  let hnode136 : Eq (assignment 136) Sign.negative :=
    Eq.trans (h_support 198 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode66)
  let hnode166 : Eq (assignment 166) Sign.negative :=
    Eq.trans (h_support 215 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode96)
  let hnode206 : Eq (assignment 206) Sign.positive :=
    Eq.trans (h_support 192 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode61)
  let hnode208 : Eq (assignment 208) Sign.positive :=
    Eq.trans (h_support 193 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode61)
  let hnode209 : Eq (assignment 209) Sign.negative :=
    Eq.trans (h_support 196 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode63)
  let hnode211 : Eq (assignment 211) Sign.positive :=
    Eq.trans (h_support 197 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode63)
  let hnode212 : Eq (assignment 212) Sign.positive :=
    Eq.trans (h_support 200 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode66)
  let hnode214 : Eq (assignment 214) Sign.negative :=
    Eq.trans (h_support 201 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode66)
  let hnode216 : Eq (assignment 216) Sign.positive :=
    Eq.trans (h_support 142 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode72)
  let hnode219 : Eq (assignment 219) Sign.negative :=
    Eq.trans (h_support 143 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode72)
  let hnode220 : Eq (assignment 220) Sign.negative :=
    Eq.trans (h_support 144 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode72)
  let hnode232 : Eq (assignment 232) Sign.negative :=
    Eq.trans (h_support 217 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode96)
  let hnode237 : Eq (assignment 237) Sign.positive :=
    Eq.trans (h_support 218 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode96)
  let hnode239 : Eq (assignment 239) Sign.negative :=
    Eq.trans (h_support 219 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode96)
  let hnode2 : Eq (assignment 2) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 109 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode131)
  let hnode18 : Eq (assignment 18) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 1 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode43)
  let hnode20 : Eq (assignment 20) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 8 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode35)
  let hnode22 : Eq (assignment 22) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 119 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode166)
  let hnode34 : Eq (assignment 34) Sign.positive :=
    Eq.trans (h_support 4 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode19)
  let hnode41 : Eq (assignment 41) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 166 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode166)
  let hnode44 : Eq (assignment 44) Sign.positive :=
    Eq.trans (h_support 5 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode19)
  let hnode50 : Eq (assignment 50) Sign.positive :=
    Eq.trans (h_support 6 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode19)
  let hnode53 : Eq (assignment 53) Sign.positive :=
    Eq.trans (h_support 7 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode19)
  let hnode62 : Eq (assignment 62) Sign.positive :=
    Eq.trans (h_support 25 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode1)
  let hnode64 : Eq (assignment 64) Sign.positive :=
    Eq.trans (h_support 27 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode1)
  let hnode70 : Eq (assignment 70) Sign.negative :=
    Eq.trans (h_support 68 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode35)
  let hnode78 : Eq (assignment 78) Sign.negative :=
    Eq.trans (h_support 52 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode43)
  let hnode81 : Eq (assignment 81) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 211 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode206)
  let hnode91 : Eq (assignment 91) Sign.negative :=
    Eq.trans (h_support 32 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode21)
  let hnode94 : Eq (assignment 94) Sign.negative :=
    Eq.trans (h_support 35 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode21)
  let hnode102 : Eq (assignment 102) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 207 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode232)
  let hnode104 : Eq (assignment 104) Sign.positive :=
    Eq.trans (h_support 63 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode28)
  let hnode109 : Eq (assignment 109) Sign.positive :=
    Eq.trans (h_support 70 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode35)
  let hnode110 : Eq (assignment 110) Sign.positive :=
    Eq.trans (h_support 71 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode35)
  let hnode111 : Eq (assignment 111) Sign.negative :=
    Eq.trans (h_support 82 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode37)
  let hnode114 : Eq (assignment 114) Sign.positive :=
    Eq.trans (h_support 83 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode37)
  let hnode115 : Eq (assignment 115) Sign.positive :=
    Eq.trans (h_support 84 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode37)
  let hnode117 : Eq (assignment 117) Sign.positive :=
    Eq.trans (h_support 54 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode43)
  let hnode119 : Eq (assignment 119) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 182 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode239)
  let hnode120 : Eq (assignment 120) Sign.positive :=
    Eq.trans (h_support 55 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode43)
  let hnode135 : Eq (assignment 135) Sign.negative :=
    Eq.trans (h_support 145 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode15)
  let hnode139 : Eq (assignment 139) Sign.positive :=
    Eq.trans (h_support 153 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode19)
  let hnode146 : Eq (assignment 146) Sign.negative :=
    Eq.trans (h_support 115 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode7)
  let hnode147 : Eq (assignment 147) Sign.negative :=
    Eq.trans (h_support 116 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode7)
  let hnode151 : Eq (assignment 151) Sign.negative :=
    Eq.trans (h_support 147 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode15)
  let hnode155 : Eq (assignment 155) Sign.positive :=
    Eq.trans (h_support 155 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode19)
  let hnode157 : Eq (assignment 157) Sign.negative :=
    Eq.trans (h_support 148 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode15)
  let hnode160 : Eq (assignment 160) Sign.negative :=
    Eq.trans (h_support 156 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode19)
  let hnode162 : Eq (assignment 162) Sign.positive :=
    Eq.trans (h_support 137 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode37)
  let hnode168 : Eq (assignment 168) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 58 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode237)
  let hnode176 : Eq (assignment 176) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 76 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode211)
  let hnode181 : Eq (assignment 181) Sign.positive :=
    Eq.trans (h_support 138 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode37)
  let hnode184 : Eq (assignment 184) Sign.negative :=
    Eq.trans (h_support 139 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode37)
  let hnode185 : Eq (assignment 185) Sign.negative :=
    Eq.trans (h_support 140 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode37)
  let hnode187 : Eq (assignment 187) Sign.negative :=
    Eq.trans (h_support 188 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode43)
  let hnode190 : Eq (assignment 190) Sign.negative :=
    Eq.trans (h_support 189 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode43)
  let hnode12 : Eq (assignment 12) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 134 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode151)
  let hnode17 : Eq (assignment 17) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 150 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode147)
  let hnode29 : Eq (assignment 29) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 64 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode64)
  let hnode33 : Eq (assignment 33) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 49 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode104)
  let hnode42 : Eq (assignment 42) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 169 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode147)
  let hnode45 : Eq (assignment 45) Sign.negative :=
    Eq.trans (h_support 9 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode20)
  let hnode46 : Eq (assignment 46) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 85 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode81)
  let hnode49 : Eq (assignment 49) Sign.negative :=
    Eq.trans (h_support 2 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode18)
  let hnode51 : Eq (assignment 51) Sign.negative :=
    Eq.trans (h_support 10 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode20)
  let hnode52 : Eq (assignment 52) Sign.negative :=
    Eq.trans (h_support 3 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode18)
  let hnode54 : Eq (assignment 54) Sign.negative :=
    Eq.trans (h_support 11 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode20)
  let hnode85 : Eq (assignment 85) Sign.positive :=
    Eq.trans (h_support 93 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode50)
  let hnode88 : Eq (assignment 88) Sign.positive :=
    Eq.trans (h_support 97 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode53)
  let hnode90 : Eq (assignment 90) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 12 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode110)
  let hnode105 : Eq (assignment 105) Sign.positive :=
    Eq.trans (h_support 94 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode50)
  let hnode108 : Eq (assignment 108) Sign.positive :=
    Eq.trans (h_support 98 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode53)
  let hnode118 : Eq (assignment 118) Sign.positive :=
    Eq.trans (h_support 99 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode53)
  let hnode124 : Eq (assignment 124) Sign.positive :=
    Eq.trans (h_support 96 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode50)
  let hnode125 : Eq (assignment 125) Sign.positive :=
    Eq.trans (h_support 100 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode53)
  let hnode137 : Eq (assignment 137) Sign.negative :=
    Eq.trans (h_support 112 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode2)
  let hnode161 : Eq (assignment 161) Sign.positive :=
    Eq.trans (h_support 117 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode22)
  let hnode165 : Eq (assignment 165) Sign.negative :=
    Eq.trans (h_support 118 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode22)
  let hnode167 : Eq (assignment 167) Sign.negative :=
    Eq.trans (h_support 120 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode22)
  let hnode172 : Eq (assignment 172) Sign.positive :=
    Eq.trans (h_support 206 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode102)
  let hnode178 : Eq (assignment 178) Sign.negative :=
    Eq.trans (h_support 157 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode53)
  let hnode180 : Eq (assignment 180) Sign.negative :=
    Eq.trans (h_support 16 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode160)
  let hnode182 : Eq (assignment 182) Sign.positive :=
    Eq.trans (h_support 167 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode41)
  let hnode188 : Eq (assignment 188) Sign.negative :=
    Eq.trans (h_support 158 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode53)
  let hnode192 : Eq (assignment 192) Sign.negative :=
    Eq.trans (h_support 159 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode53)
  let hnode194 : Eq (assignment 194) Sign.negative :=
    Eq.trans (h_support 18 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode160)
  let hnode195 : Eq (assignment 195) Sign.negative :=
    Eq.trans (h_support 160 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode53)
  let hnode203 : Eq (assignment 203) Sign.positive :=
    Eq.trans (h_support 56 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode168)
  let hnode224 : Eq (assignment 224) Sign.negative :=
    Eq.trans (h_support 181 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode119)
  let hnode226 : Eq (assignment 226) Sign.negative :=
    Eq.trans (h_support 213 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode81)
  let hnode227 : Eq (assignment 227) Sign.negative :=
    Eq.trans (h_support 214 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode81)
  let hnode234 : Eq (assignment 234) Sign.positive :=
    Eq.trans (h_support 57 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode168)
  let hnode236 : Eq (assignment 236) Sign.negative :=
    Eq.trans (h_support 77 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode176)
  let hnode240 : Eq (assignment 240) Sign.positive :=
    Eq.trans (h_support 59 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode168)
  let hnode241 : Eq (assignment 241) Sign.negative :=
    Eq.trans (h_support 208 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode102)
  let hnode243 : Eq (assignment 243) Sign.positive :=
    Eq.trans (h_support 209 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode102)
  let hnode244 : Eq (assignment 244) Sign.positive :=
    Eq.trans (h_support 79 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode176)
  let hnode248 : Eq (assignment 248) Sign.positive :=
    Eq.trans (h_support 183 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode119)
  let hnode250 : Eq (assignment 250) Sign.negative :=
    Eq.trans (h_support 184 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode119)
  let hnode68 : Eq (assignment 68) Sign.negative :=
    Eq.trans (h_support 48 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode33)
  let hnode82 : Eq (assignment 82) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 204 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode226)
  let hnode86 : Eq (assignment 86) Sign.negative :=
    Eq.trans (h_support 72 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode51)
  let hnode101 : Eq (assignment 101) Sign.negative :=
    Eq.trans (h_support 86 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode46)
  let hnode103 : Eq (assignment 103) Sign.positive :=
    Eq.trans (h_support 66 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode29)
  let hnode107 : Eq (assignment 107) Sign.positive :=
    Eq.trans (h_support 50 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode33)
  let hnode116 : Eq (assignment 116) Sign.negative :=
    Eq.trans (h_support 73 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode51)
  let hnode121 : Eq (assignment 121) Sign.positive :=
    Eq.trans (h_support 88 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode46)
  let hnode123 : Eq (assignment 123) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 222 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode243)
  let hnode132 : Eq (assignment 132) Sign.positive :=
    Eq.trans (h_support 133 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode12)
  let hnode150 : Eq (assignment 150) Sign.positive :=
    Eq.trans (h_support 173 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode45)
  let hnode153 : Eq (assignment 153) Sign.negative :=
    Eq.trans (h_support 151 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode17)
  let hnode154 : Eq (assignment 154) Sign.positive :=
    Eq.trans (h_support 135 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode12)
  let hnode159 : Eq (assignment 159) Sign.positive :=
    Eq.trans (h_support 177 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode54)
  let hnode170 : Eq (assignment 170) Sign.positive :=
    Eq.trans (h_support 174 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode45)
  let hnode179 : Eq (assignment 179) Sign.positive :=
    Eq.trans (h_support 178 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode54)
  let hnode183 : Eq (assignment 183) Sign.positive :=
    Eq.trans (h_support 171 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode42)
  let hnode186 : Eq (assignment 186) Sign.negative :=
    Eq.trans (h_support 175 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode45)
  let hnode193 : Eq (assignment 193) Sign.positive :=
    Eq.trans (h_support 179 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode54)
  let hnode213 : Eq (assignment 213) Sign.negative :=
    Eq.trans (h_support 161 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode88)
  let hnode223 : Eq (assignment 223) Sign.negative :=
    Eq.trans (h_support 162 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode88)
  let hnode230 : Eq (assignment 230) Sign.negative :=
    Eq.trans (h_support 164 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode88)
  let hnode242 : Eq (assignment 242) Sign.negative :=
    Eq.trans (h_support 102 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode192)
  let hnode247 : Eq (assignment 247) Sign.negative :=
    Eq.trans (h_support 103 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode192)
  let hnode251 : Eq (assignment 251) Sign.positive :=
    Eq.trans (h_support 104 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode192)
  let hnode48 : Eq (assignment 48) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 90 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode103)
  let hnode152 : Eq (assignment 152) Sign.positive :=
    Eq.trans (h_support 202 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode82)
  let hnode217 : Eq (assignment 217) Sign.negative :=
    Eq.trans (h_support 203 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode82)
  let hnode228 : Eq (assignment 228) Sign.positive :=
    Eq.trans (h_support 205 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode82)
  let hnode83 : Eq (assignment 83) Sign.positive :=
    Eq.trans (h_support 89 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode48)
  let hnode113 : Eq (assignment 113) Sign.positive :=
    Eq.trans (h_support 91 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode48)
  let predicate : Nat → Prop := fun index =>
    Eq ((Cases.C042.initial index).allows
      (Sign.withNegation globalNegation (assignment index))) Bool.true
  let bounded0 := below_zero predicate
  let bounded1 := below_succ bounded0 (domain_from_eq (domain := Cases.C042.initial 0) (congrArg (Sign.withNegation globalNegation) h_anchor) (Eq.refl Bool.true))
  let bounded2 := below_succ bounded1 (domain_from_eq (domain := Cases.C042.initial 1) (congrArg (Sign.withNegation globalNegation) hnode1) (Eq.refl Bool.true))
  let bounded3 := below_succ bounded2 (domain_from_eq (domain := Cases.C042.initial 2) (congrArg (Sign.withNegation globalNegation) hnode2) (Eq.refl Bool.true))
  let bounded4 := below_succ bounded3 (top_allows (Sign.withNegation globalNegation (assignment 3)))
  let bounded5 := below_succ bounded4 (top_allows (Sign.withNegation globalNegation (assignment 4)))
  let bounded6 := below_succ bounded5 (top_allows (Sign.withNegation globalNegation (assignment 5)))
  let bounded7 := below_succ bounded6 (domain_from_eq (domain := Cases.C042.initial 6) (congrArg (Sign.withNegation globalNegation) hnode6) (Eq.refl Bool.true))
  let bounded8 := below_succ bounded7 (domain_from_eq (domain := Cases.C042.initial 7) (congrArg (Sign.withNegation globalNegation) hnode7) (Eq.refl Bool.true))
  let bounded9 := below_succ bounded8 (domain_from_eq (domain := Cases.C042.initial 8) (congrArg (Sign.withNegation globalNegation) hnode8) (Eq.refl Bool.true))
  let bounded10 := below_succ bounded9 (top_allows (Sign.withNegation globalNegation (assignment 9)))
  let bounded11 := below_succ bounded10 (top_allows (Sign.withNegation globalNegation (assignment 10)))
  let bounded12 := below_succ bounded11 (top_allows (Sign.withNegation globalNegation (assignment 11)))
  let bounded13 := below_succ bounded12 (domain_from_eq (domain := Cases.C042.initial 12) (congrArg (Sign.withNegation globalNegation) hnode12) (Eq.refl Bool.true))
  let bounded14 := below_succ bounded13 (top_allows (Sign.withNegation globalNegation (assignment 13)))
  let bounded15 := below_succ bounded14 (top_allows (Sign.withNegation globalNegation (assignment 14)))
  let bounded16 := below_succ bounded15 (domain_from_eq (domain := Cases.C042.initial 15) (congrArg (Sign.withNegation globalNegation) hnode15) (Eq.refl Bool.true))
  let bounded17 := below_succ bounded16 (top_allows (Sign.withNegation globalNegation (assignment 16)))
  let bounded18 := below_succ bounded17 (domain_from_eq (domain := Cases.C042.initial 17) (congrArg (Sign.withNegation globalNegation) hnode17) (Eq.refl Bool.true))
  let bounded19 := below_succ bounded18 (domain_from_eq (domain := Cases.C042.initial 18) (congrArg (Sign.withNegation globalNegation) hnode18) (Eq.refl Bool.true))
  let bounded20 := below_succ bounded19 (domain_from_eq (domain := Cases.C042.initial 19) (congrArg (Sign.withNegation globalNegation) hnode19) (Eq.refl Bool.true))
  let bounded21 := below_succ bounded20 (domain_from_eq (domain := Cases.C042.initial 20) (congrArg (Sign.withNegation globalNegation) hnode20) (Eq.refl Bool.true))
  let bounded22 := below_succ bounded21 (domain_from_eq (domain := Cases.C042.initial 21) (congrArg (Sign.withNegation globalNegation) hnode21) (Eq.refl Bool.true))
  let bounded23 := below_succ bounded22 (domain_from_eq (domain := Cases.C042.initial 22) (congrArg (Sign.withNegation globalNegation) hnode22) (Eq.refl Bool.true))
  let bounded24 := below_succ bounded23 (domain_from_eq (domain := Cases.C042.initial 23) (congrArg (Sign.withNegation globalNegation) hnode23) (Eq.refl Bool.true))
  let bounded25 := below_succ bounded24 (domain_from_eq (domain := Cases.C042.initial 24) (congrArg (Sign.withNegation globalNegation) hnode24) (Eq.refl Bool.true))
  let bounded26 := below_succ bounded25 (top_allows (Sign.withNegation globalNegation (assignment 25)))
  let bounded27 := below_succ bounded26 (top_allows (Sign.withNegation globalNegation (assignment 26)))
  let bounded28 := below_succ bounded27 (top_allows (Sign.withNegation globalNegation (assignment 27)))
  let bounded29 := below_succ bounded28 (domain_from_eq (domain := Cases.C042.initial 28) (congrArg (Sign.withNegation globalNegation) hnode28) (Eq.refl Bool.true))
  let bounded30 := below_succ bounded29 (domain_from_eq (domain := Cases.C042.initial 29) (congrArg (Sign.withNegation globalNegation) hnode29) (Eq.refl Bool.true))
  let bounded31 := below_succ bounded30 (top_allows (Sign.withNegation globalNegation (assignment 30)))
  let bounded32 := below_succ bounded31 (top_allows (Sign.withNegation globalNegation (assignment 31)))
  let bounded33 := below_succ bounded32 (top_allows (Sign.withNegation globalNegation (assignment 32)))
  let bounded34 := below_succ bounded33 (domain_from_eq (domain := Cases.C042.initial 33) (congrArg (Sign.withNegation globalNegation) hnode33) (Eq.refl Bool.true))
  let bounded35 := below_succ bounded34 (domain_from_eq (domain := Cases.C042.initial 34) (congrArg (Sign.withNegation globalNegation) hnode34) (Eq.refl Bool.true))
  let bounded36 := below_succ bounded35 (domain_from_eq (domain := Cases.C042.initial 35) (congrArg (Sign.withNegation globalNegation) hnode35) (Eq.refl Bool.true))
  let bounded37 := below_succ bounded36 (top_allows (Sign.withNegation globalNegation (assignment 36)))
  let bounded38 := below_succ bounded37 (domain_from_eq (domain := Cases.C042.initial 37) (congrArg (Sign.withNegation globalNegation) hnode37) (Eq.refl Bool.true))
  let bounded39 := below_succ bounded38 (top_allows (Sign.withNegation globalNegation (assignment 38)))
  let bounded40 := below_succ bounded39 (top_allows (Sign.withNegation globalNegation (assignment 39)))
  let bounded41 := below_succ bounded40 (top_allows (Sign.withNegation globalNegation (assignment 40)))
  let bounded42 := below_succ bounded41 (domain_from_eq (domain := Cases.C042.initial 41) (congrArg (Sign.withNegation globalNegation) hnode41) (Eq.refl Bool.true))
  let bounded43 := below_succ bounded42 (domain_from_eq (domain := Cases.C042.initial 42) (congrArg (Sign.withNegation globalNegation) hnode42) (Eq.refl Bool.true))
  let bounded44 := below_succ bounded43 (domain_from_eq (domain := Cases.C042.initial 43) (congrArg (Sign.withNegation globalNegation) hnode43) (Eq.refl Bool.true))
  let bounded45 := below_succ bounded44 (domain_from_eq (domain := Cases.C042.initial 44) (congrArg (Sign.withNegation globalNegation) hnode44) (Eq.refl Bool.true))
  let bounded46 := below_succ bounded45 (domain_from_eq (domain := Cases.C042.initial 45) (congrArg (Sign.withNegation globalNegation) hnode45) (Eq.refl Bool.true))
  let bounded47 := below_succ bounded46 (domain_from_eq (domain := Cases.C042.initial 46) (congrArg (Sign.withNegation globalNegation) hnode46) (Eq.refl Bool.true))
  let bounded48 := below_succ bounded47 (top_allows (Sign.withNegation globalNegation (assignment 47)))
  let bounded49 := below_succ bounded48 (domain_from_eq (domain := Cases.C042.initial 48) (congrArg (Sign.withNegation globalNegation) hnode48) (Eq.refl Bool.true))
  let bounded50 := below_succ bounded49 (domain_from_eq (domain := Cases.C042.initial 49) (congrArg (Sign.withNegation globalNegation) hnode49) (Eq.refl Bool.true))
  let bounded51 := below_succ bounded50 (domain_from_eq (domain := Cases.C042.initial 50) (congrArg (Sign.withNegation globalNegation) hnode50) (Eq.refl Bool.true))
  let bounded52 := below_succ bounded51 (domain_from_eq (domain := Cases.C042.initial 51) (congrArg (Sign.withNegation globalNegation) hnode51) (Eq.refl Bool.true))
  let bounded53 := below_succ bounded52 (domain_from_eq (domain := Cases.C042.initial 52) (congrArg (Sign.withNegation globalNegation) hnode52) (Eq.refl Bool.true))
  let bounded54 := below_succ bounded53 (domain_from_eq (domain := Cases.C042.initial 53) (congrArg (Sign.withNegation globalNegation) hnode53) (Eq.refl Bool.true))
  let bounded55 := below_succ bounded54 (domain_from_eq (domain := Cases.C042.initial 54) (congrArg (Sign.withNegation globalNegation) hnode54) (Eq.refl Bool.true))
  let bounded56 := below_succ bounded55 (domain_from_eq (domain := Cases.C042.initial 55) (congrArg (Sign.withNegation globalNegation) (h_zero 0 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded57 := below_succ bounded56 (domain_from_eq (domain := Cases.C042.initial 56) (congrArg (Sign.withNegation globalNegation) (h_zero 1 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded58 := below_succ bounded57 (domain_from_eq (domain := Cases.C042.initial 57) (congrArg (Sign.withNegation globalNegation) hnode57) (Eq.refl Bool.true))
  let bounded59 := below_succ bounded58 (domain_from_eq (domain := Cases.C042.initial 58) (congrArg (Sign.withNegation globalNegation) hnode58) (Eq.refl Bool.true))
  let bounded60 := below_succ bounded59 (domain_from_eq (domain := Cases.C042.initial 59) (congrArg (Sign.withNegation globalNegation) hnode59) (Eq.refl Bool.true))
  let bounded61 := below_succ bounded60 (domain_from_eq (domain := Cases.C042.initial 60) (congrArg (Sign.withNegation globalNegation) hnode60) (Eq.refl Bool.true))
  let bounded62 := below_succ bounded61 (domain_from_eq (domain := Cases.C042.initial 61) (congrArg (Sign.withNegation globalNegation) hnode61) (Eq.refl Bool.true))
  let bounded63 := below_succ bounded62 (domain_from_eq (domain := Cases.C042.initial 62) (congrArg (Sign.withNegation globalNegation) hnode62) (Eq.refl Bool.true))
  let bounded64 := below_succ bounded63 (domain_from_eq (domain := Cases.C042.initial 63) (congrArg (Sign.withNegation globalNegation) hnode63) (Eq.refl Bool.true))
  let bounded65 := below_succ bounded64 (domain_from_eq (domain := Cases.C042.initial 64) (congrArg (Sign.withNegation globalNegation) hnode64) (Eq.refl Bool.true))
  let bounded66 := below_succ bounded65 (top_allows (Sign.withNegation globalNegation (assignment 65)))
  let bounded67 := below_succ bounded66 (domain_from_eq (domain := Cases.C042.initial 66) (congrArg (Sign.withNegation globalNegation) hnode66) (Eq.refl Bool.true))
  let bounded68 := below_succ bounded67 (top_allows (Sign.withNegation globalNegation (assignment 67)))
  let bounded69 := below_succ bounded68 (domain_from_eq (domain := Cases.C042.initial 68) (congrArg (Sign.withNegation globalNegation) hnode68) (Eq.refl Bool.true))
  let bounded70 := below_succ bounded69 (top_allows (Sign.withNegation globalNegation (assignment 69)))
  let bounded71 := below_succ bounded70 (domain_from_eq (domain := Cases.C042.initial 70) (congrArg (Sign.withNegation globalNegation) hnode70) (Eq.refl Bool.true))
  let bounded72 := below_succ bounded71 (domain_from_eq (domain := Cases.C042.initial 71) (congrArg (Sign.withNegation globalNegation) hnode71) (Eq.refl Bool.true))
  let bounded73 := below_succ bounded72 (domain_from_eq (domain := Cases.C042.initial 72) (congrArg (Sign.withNegation globalNegation) hnode72) (Eq.refl Bool.true))
  let bounded74 := below_succ bounded73 (domain_from_eq (domain := Cases.C042.initial 73) (congrArg (Sign.withNegation globalNegation) hnode73) (Eq.refl Bool.true))
  let bounded75 := below_succ bounded74 (domain_from_eq (domain := Cases.C042.initial 74) (congrArg (Sign.withNegation globalNegation) hnode74) (Eq.refl Bool.true))
  let bounded76 := below_succ bounded75 (top_allows (Sign.withNegation globalNegation (assignment 75)))
  let bounded77 := below_succ bounded76 (top_allows (Sign.withNegation globalNegation (assignment 76)))
  let bounded78 := below_succ bounded77 (top_allows (Sign.withNegation globalNegation (assignment 77)))
  let bounded79 := below_succ bounded78 (domain_from_eq (domain := Cases.C042.initial 78) (congrArg (Sign.withNegation globalNegation) hnode78) (Eq.refl Bool.true))
  let bounded80 := below_succ bounded79 (top_allows (Sign.withNegation globalNegation (assignment 79)))
  let bounded81 := below_succ bounded80 (top_allows (Sign.withNegation globalNegation (assignment 80)))
  let bounded82 := below_succ bounded81 (domain_from_eq (domain := Cases.C042.initial 81) (congrArg (Sign.withNegation globalNegation) hnode81) (Eq.refl Bool.true))
  let bounded83 := below_succ bounded82 (domain_from_eq (domain := Cases.C042.initial 82) (congrArg (Sign.withNegation globalNegation) hnode82) (Eq.refl Bool.true))
  let bounded84 := below_succ bounded83 (domain_from_eq (domain := Cases.C042.initial 83) (congrArg (Sign.withNegation globalNegation) hnode83) (Eq.refl Bool.true))
  let bounded85 := below_succ bounded84 (top_allows (Sign.withNegation globalNegation (assignment 84)))
  let bounded86 := below_succ bounded85 (domain_from_eq (domain := Cases.C042.initial 85) (congrArg (Sign.withNegation globalNegation) hnode85) (Eq.refl Bool.true))
  let bounded87 := below_succ bounded86 (domain_from_eq (domain := Cases.C042.initial 86) (congrArg (Sign.withNegation globalNegation) hnode86) (Eq.refl Bool.true))
  let bounded88 := below_succ bounded87 (top_allows (Sign.withNegation globalNegation (assignment 87)))
  let bounded89 := below_succ bounded88 (domain_from_eq (domain := Cases.C042.initial 88) (congrArg (Sign.withNegation globalNegation) hnode88) (Eq.refl Bool.true))
  let bounded90 := below_succ bounded89 (top_allows (Sign.withNegation globalNegation (assignment 89)))
  let bounded91 := below_succ bounded90 (domain_from_eq (domain := Cases.C042.initial 90) (congrArg (Sign.withNegation globalNegation) hnode90) (Eq.refl Bool.true))
  let bounded92 := below_succ bounded91 (domain_from_eq (domain := Cases.C042.initial 91) (congrArg (Sign.withNegation globalNegation) hnode91) (Eq.refl Bool.true))
  let bounded93 := below_succ bounded92 (domain_from_eq (domain := Cases.C042.initial 92) (congrArg (Sign.withNegation globalNegation) hnode92) (Eq.refl Bool.true))
  let bounded94 := below_succ bounded93 (domain_from_eq (domain := Cases.C042.initial 93) (congrArg (Sign.withNegation globalNegation) hnode93) (Eq.refl Bool.true))
  let bounded95 := below_succ bounded94 (domain_from_eq (domain := Cases.C042.initial 94) (congrArg (Sign.withNegation globalNegation) hnode94) (Eq.refl Bool.true))
  let bounded96 := below_succ bounded95 (domain_from_eq (domain := Cases.C042.initial 95) (congrArg (Sign.withNegation globalNegation) hnode95) (Eq.refl Bool.true))
  let bounded97 := below_succ bounded96 (domain_from_eq (domain := Cases.C042.initial 96) (congrArg (Sign.withNegation globalNegation) hnode96) (Eq.refl Bool.true))
  let bounded98 := below_succ bounded97 (top_allows (Sign.withNegation globalNegation (assignment 97)))
  let bounded99 := below_succ bounded98 (domain_from_eq (domain := Cases.C042.initial 98) (congrArg (Sign.withNegation globalNegation) (h_zero 2 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded100 := below_succ bounded99 (domain_from_eq (domain := Cases.C042.initial 99) (congrArg (Sign.withNegation globalNegation) hnode99) (Eq.refl Bool.true))
  let bounded101 := below_succ bounded100 (domain_from_eq (domain := Cases.C042.initial 100) (congrArg (Sign.withNegation globalNegation) hnode100) (Eq.refl Bool.true))
  let bounded102 := below_succ bounded101 (domain_from_eq (domain := Cases.C042.initial 101) (congrArg (Sign.withNegation globalNegation) hnode101) (Eq.refl Bool.true))
  let bounded103 := below_succ bounded102 (domain_from_eq (domain := Cases.C042.initial 102) (congrArg (Sign.withNegation globalNegation) hnode102) (Eq.refl Bool.true))
  let bounded104 := below_succ bounded103 (domain_from_eq (domain := Cases.C042.initial 103) (congrArg (Sign.withNegation globalNegation) hnode103) (Eq.refl Bool.true))
  let bounded105 := below_succ bounded104 (domain_from_eq (domain := Cases.C042.initial 104) (congrArg (Sign.withNegation globalNegation) hnode104) (Eq.refl Bool.true))
  let bounded106 := below_succ bounded105 (domain_from_eq (domain := Cases.C042.initial 105) (congrArg (Sign.withNegation globalNegation) hnode105) (Eq.refl Bool.true))
  let bounded107 := below_succ bounded106 (domain_from_eq (domain := Cases.C042.initial 106) (congrArg (Sign.withNegation globalNegation) (h_zero 3 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded108 := below_succ bounded107 (domain_from_eq (domain := Cases.C042.initial 107) (congrArg (Sign.withNegation globalNegation) hnode107) (Eq.refl Bool.true))
  let bounded109 := below_succ bounded108 (domain_from_eq (domain := Cases.C042.initial 108) (congrArg (Sign.withNegation globalNegation) hnode108) (Eq.refl Bool.true))
  let bounded110 := below_succ bounded109 (domain_from_eq (domain := Cases.C042.initial 109) (congrArg (Sign.withNegation globalNegation) hnode109) (Eq.refl Bool.true))
  let bounded111 := below_succ bounded110 (domain_from_eq (domain := Cases.C042.initial 110) (congrArg (Sign.withNegation globalNegation) hnode110) (Eq.refl Bool.true))
  let bounded112 := below_succ bounded111 (domain_from_eq (domain := Cases.C042.initial 111) (congrArg (Sign.withNegation globalNegation) hnode111) (Eq.refl Bool.true))
  let bounded113 := below_succ bounded112 (top_allows (Sign.withNegation globalNegation (assignment 112)))
  let bounded114 := below_succ bounded113 (domain_from_eq (domain := Cases.C042.initial 113) (congrArg (Sign.withNegation globalNegation) hnode113) (Eq.refl Bool.true))
  let bounded115 := below_succ bounded114 (domain_from_eq (domain := Cases.C042.initial 114) (congrArg (Sign.withNegation globalNegation) hnode114) (Eq.refl Bool.true))
  let bounded116 := below_succ bounded115 (domain_from_eq (domain := Cases.C042.initial 115) (congrArg (Sign.withNegation globalNegation) hnode115) (Eq.refl Bool.true))
  let bounded117 := below_succ bounded116 (domain_from_eq (domain := Cases.C042.initial 116) (congrArg (Sign.withNegation globalNegation) hnode116) (Eq.refl Bool.true))
  let bounded118 := below_succ bounded117 (domain_from_eq (domain := Cases.C042.initial 117) (congrArg (Sign.withNegation globalNegation) hnode117) (Eq.refl Bool.true))
  let bounded119 := below_succ bounded118 (domain_from_eq (domain := Cases.C042.initial 118) (congrArg (Sign.withNegation globalNegation) hnode118) (Eq.refl Bool.true))
  let bounded120 := below_succ bounded119 (domain_from_eq (domain := Cases.C042.initial 119) (congrArg (Sign.withNegation globalNegation) hnode119) (Eq.refl Bool.true))
  let bounded121 := below_succ bounded120 (domain_from_eq (domain := Cases.C042.initial 120) (congrArg (Sign.withNegation globalNegation) hnode120) (Eq.refl Bool.true))
  let bounded122 := below_succ bounded121 (domain_from_eq (domain := Cases.C042.initial 121) (congrArg (Sign.withNegation globalNegation) hnode121) (Eq.refl Bool.true))
  let bounded123 := below_succ bounded122 (domain_from_eq (domain := Cases.C042.initial 122) (congrArg (Sign.withNegation globalNegation) (h_zero 4 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded124 := below_succ bounded123 (domain_from_eq (domain := Cases.C042.initial 123) (congrArg (Sign.withNegation globalNegation) hnode123) (Eq.refl Bool.true))
  let bounded125 := below_succ bounded124 (domain_from_eq (domain := Cases.C042.initial 124) (congrArg (Sign.withNegation globalNegation) hnode124) (Eq.refl Bool.true))
  let bounded126 := below_succ bounded125 (domain_from_eq (domain := Cases.C042.initial 125) (congrArg (Sign.withNegation globalNegation) hnode125) (Eq.refl Bool.true))
  let bounded127 := below_succ bounded126 (domain_from_eq (domain := Cases.C042.initial 126) (congrArg (Sign.withNegation globalNegation) hnode126) (Eq.refl Bool.true))
  let bounded128 := below_succ bounded127 (domain_from_eq (domain := Cases.C042.initial 127) (congrArg (Sign.withNegation globalNegation) (h_zero 5 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded129 := below_succ bounded128 (domain_from_eq (domain := Cases.C042.initial 128) (congrArg (Sign.withNegation globalNegation) hnode128) (Eq.refl Bool.true))
  let bounded130 := below_succ bounded129 (domain_from_eq (domain := Cases.C042.initial 129) (congrArg (Sign.withNegation globalNegation) hnode129) (Eq.refl Bool.true))
  let bounded131 := below_succ bounded130 (domain_from_eq (domain := Cases.C042.initial 130) (congrArg (Sign.withNegation globalNegation) hnode130) (Eq.refl Bool.true))
  let bounded132 := below_succ bounded131 (domain_from_eq (domain := Cases.C042.initial 131) (congrArg (Sign.withNegation globalNegation) hnode131) (Eq.refl Bool.true))
  let bounded133 := below_succ bounded132 (domain_from_eq (domain := Cases.C042.initial 132) (congrArg (Sign.withNegation globalNegation) hnode132) (Eq.refl Bool.true))
  let bounded134 := below_succ bounded133 (domain_from_eq (domain := Cases.C042.initial 133) (congrArg (Sign.withNegation globalNegation) hnode133) (Eq.refl Bool.true))
  let bounded135 := below_succ bounded134 (top_allows (Sign.withNegation globalNegation (assignment 134)))
  let bounded136 := below_succ bounded135 (domain_from_eq (domain := Cases.C042.initial 135) (congrArg (Sign.withNegation globalNegation) hnode135) (Eq.refl Bool.true))
  let bounded137 := below_succ bounded136 (domain_from_eq (domain := Cases.C042.initial 136) (congrArg (Sign.withNegation globalNegation) hnode136) (Eq.refl Bool.true))
  let bounded138 := below_succ bounded137 (domain_from_eq (domain := Cases.C042.initial 137) (congrArg (Sign.withNegation globalNegation) hnode137) (Eq.refl Bool.true))
  let bounded139 := below_succ bounded138 (top_allows (Sign.withNegation globalNegation (assignment 138)))
  let bounded140 := below_succ bounded139 (domain_from_eq (domain := Cases.C042.initial 139) (congrArg (Sign.withNegation globalNegation) hnode139) (Eq.refl Bool.true))
  let bounded141 := below_succ bounded140 (top_allows (Sign.withNegation globalNegation (assignment 140)))
  let bounded142 := below_succ bounded141 (domain_from_eq (domain := Cases.C042.initial 141) (congrArg (Sign.withNegation globalNegation) hnode141) (Eq.refl Bool.true))
  let bounded143 := below_succ bounded142 (domain_from_eq (domain := Cases.C042.initial 142) (congrArg (Sign.withNegation globalNegation) (h_zero 6 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded144 := below_succ bounded143 (domain_from_eq (domain := Cases.C042.initial 143) (congrArg (Sign.withNegation globalNegation) hnode143) (Eq.refl Bool.true))
  let bounded145 := below_succ bounded144 (domain_from_eq (domain := Cases.C042.initial 144) (congrArg (Sign.withNegation globalNegation) hnode144) (Eq.refl Bool.true))
  let bounded146 := below_succ bounded145 (domain_from_eq (domain := Cases.C042.initial 145) (congrArg (Sign.withNegation globalNegation) hnode145) (Eq.refl Bool.true))
  let bounded147 := below_succ bounded146 (domain_from_eq (domain := Cases.C042.initial 146) (congrArg (Sign.withNegation globalNegation) hnode146) (Eq.refl Bool.true))
  let bounded148 := below_succ bounded147 (domain_from_eq (domain := Cases.C042.initial 147) (congrArg (Sign.withNegation globalNegation) hnode147) (Eq.refl Bool.true))
  let bounded149 := below_succ bounded148 (domain_from_eq (domain := Cases.C042.initial 148) (congrArg (Sign.withNegation globalNegation) hnode148) (Eq.refl Bool.true))
  let bounded150 := below_succ bounded149 (domain_from_eq (domain := Cases.C042.initial 149) (congrArg (Sign.withNegation globalNegation) hnode149) (Eq.refl Bool.true))
  let bounded151 := below_succ bounded150 (domain_from_eq (domain := Cases.C042.initial 150) (congrArg (Sign.withNegation globalNegation) hnode150) (Eq.refl Bool.true))
  let bounded152 := below_succ bounded151 (domain_from_eq (domain := Cases.C042.initial 151) (congrArg (Sign.withNegation globalNegation) hnode151) (Eq.refl Bool.true))
  let bounded153 := below_succ bounded152 (domain_from_eq (domain := Cases.C042.initial 152) (congrArg (Sign.withNegation globalNegation) hnode152) (Eq.refl Bool.true))
  let bounded154 := below_succ bounded153 (domain_from_eq (domain := Cases.C042.initial 153) (congrArg (Sign.withNegation globalNegation) hnode153) (Eq.refl Bool.true))
  let bounded155 := below_succ bounded154 (domain_from_eq (domain := Cases.C042.initial 154) (congrArg (Sign.withNegation globalNegation) hnode154) (Eq.refl Bool.true))
  let bounded156 := below_succ bounded155 (domain_from_eq (domain := Cases.C042.initial 155) (congrArg (Sign.withNegation globalNegation) hnode155) (Eq.refl Bool.true))
  let bounded157 := below_succ bounded156 (top_allows (Sign.withNegation globalNegation (assignment 156)))
  let bounded158 := below_succ bounded157 (domain_from_eq (domain := Cases.C042.initial 157) (congrArg (Sign.withNegation globalNegation) hnode157) (Eq.refl Bool.true))
  let bounded159 := below_succ bounded158 (domain_from_eq (domain := Cases.C042.initial 158) (congrArg (Sign.withNegation globalNegation) (h_zero 7 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded160 := below_succ bounded159 (domain_from_eq (domain := Cases.C042.initial 159) (congrArg (Sign.withNegation globalNegation) hnode159) (Eq.refl Bool.true))
  let bounded161 := below_succ bounded160 (domain_from_eq (domain := Cases.C042.initial 160) (congrArg (Sign.withNegation globalNegation) hnode160) (Eq.refl Bool.true))
  let bounded162 := below_succ bounded161 (domain_from_eq (domain := Cases.C042.initial 161) (congrArg (Sign.withNegation globalNegation) hnode161) (Eq.refl Bool.true))
  let bounded163 := below_succ bounded162 (domain_from_eq (domain := Cases.C042.initial 162) (congrArg (Sign.withNegation globalNegation) hnode162) (Eq.refl Bool.true))
  let bounded164 := below_succ bounded163 (top_allows (Sign.withNegation globalNegation (assignment 163)))
  let bounded165 := below_succ bounded164 (top_allows (Sign.withNegation globalNegation (assignment 164)))
  let bounded166 := below_succ bounded165 (domain_from_eq (domain := Cases.C042.initial 165) (congrArg (Sign.withNegation globalNegation) hnode165) (Eq.refl Bool.true))
  let bounded167 := below_succ bounded166 (domain_from_eq (domain := Cases.C042.initial 166) (congrArg (Sign.withNegation globalNegation) hnode166) (Eq.refl Bool.true))
  let bounded168 := below_succ bounded167 (domain_from_eq (domain := Cases.C042.initial 167) (congrArg (Sign.withNegation globalNegation) hnode167) (Eq.refl Bool.true))
  let bounded169 := below_succ bounded168 (domain_from_eq (domain := Cases.C042.initial 168) (congrArg (Sign.withNegation globalNegation) hnode168) (Eq.refl Bool.true))
  let bounded170 := below_succ bounded169 (top_allows (Sign.withNegation globalNegation (assignment 169)))
  let bounded171 := below_succ bounded170 (domain_from_eq (domain := Cases.C042.initial 170) (congrArg (Sign.withNegation globalNegation) hnode170) (Eq.refl Bool.true))
  let bounded172 := below_succ bounded171 (top_allows (Sign.withNegation globalNegation (assignment 171)))
  let bounded173 := below_succ bounded172 (domain_from_eq (domain := Cases.C042.initial 172) (congrArg (Sign.withNegation globalNegation) hnode172) (Eq.refl Bool.true))
  let bounded174 := below_succ bounded173 (top_allows (Sign.withNegation globalNegation (assignment 173)))
  let bounded175 := below_succ bounded174 (top_allows (Sign.withNegation globalNegation (assignment 174)))
  let bounded176 := below_succ bounded175 (top_allows (Sign.withNegation globalNegation (assignment 175)))
  let bounded177 := below_succ bounded176 (domain_from_eq (domain := Cases.C042.initial 176) (congrArg (Sign.withNegation globalNegation) hnode176) (Eq.refl Bool.true))
  let bounded178 := below_succ bounded177 (top_allows (Sign.withNegation globalNegation (assignment 177)))
  let bounded179 := below_succ bounded178 (domain_from_eq (domain := Cases.C042.initial 178) (congrArg (Sign.withNegation globalNegation) hnode178) (Eq.refl Bool.true))
  let bounded180 := below_succ bounded179 (domain_from_eq (domain := Cases.C042.initial 179) (congrArg (Sign.withNegation globalNegation) hnode179) (Eq.refl Bool.true))
  let bounded181 := below_succ bounded180 (domain_from_eq (domain := Cases.C042.initial 180) (congrArg (Sign.withNegation globalNegation) hnode180) (Eq.refl Bool.true))
  let bounded182 := below_succ bounded181 (domain_from_eq (domain := Cases.C042.initial 181) (congrArg (Sign.withNegation globalNegation) hnode181) (Eq.refl Bool.true))
  let bounded183 := below_succ bounded182 (domain_from_eq (domain := Cases.C042.initial 182) (congrArg (Sign.withNegation globalNegation) hnode182) (Eq.refl Bool.true))
  let bounded184 := below_succ bounded183 (domain_from_eq (domain := Cases.C042.initial 183) (congrArg (Sign.withNegation globalNegation) hnode183) (Eq.refl Bool.true))
  let bounded185 := below_succ bounded184 (domain_from_eq (domain := Cases.C042.initial 184) (congrArg (Sign.withNegation globalNegation) hnode184) (Eq.refl Bool.true))
  let bounded186 := below_succ bounded185 (domain_from_eq (domain := Cases.C042.initial 185) (congrArg (Sign.withNegation globalNegation) hnode185) (Eq.refl Bool.true))
  let bounded187 := below_succ bounded186 (domain_from_eq (domain := Cases.C042.initial 186) (congrArg (Sign.withNegation globalNegation) hnode186) (Eq.refl Bool.true))
  let bounded188 := below_succ bounded187 (domain_from_eq (domain := Cases.C042.initial 187) (congrArg (Sign.withNegation globalNegation) hnode187) (Eq.refl Bool.true))
  let bounded189 := below_succ bounded188 (domain_from_eq (domain := Cases.C042.initial 188) (congrArg (Sign.withNegation globalNegation) hnode188) (Eq.refl Bool.true))
  let bounded190 := below_succ bounded189 (domain_from_eq (domain := Cases.C042.initial 189) (congrArg (Sign.withNegation globalNegation) (h_zero 8 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded191 := below_succ bounded190 (domain_from_eq (domain := Cases.C042.initial 190) (congrArg (Sign.withNegation globalNegation) hnode190) (Eq.refl Bool.true))
  let bounded192 := below_succ bounded191 (top_allows (Sign.withNegation globalNegation (assignment 191)))
  let bounded193 := below_succ bounded192 (domain_from_eq (domain := Cases.C042.initial 192) (congrArg (Sign.withNegation globalNegation) hnode192) (Eq.refl Bool.true))
  let bounded194 := below_succ bounded193 (domain_from_eq (domain := Cases.C042.initial 193) (congrArg (Sign.withNegation globalNegation) hnode193) (Eq.refl Bool.true))
  let bounded195 := below_succ bounded194 (domain_from_eq (domain := Cases.C042.initial 194) (congrArg (Sign.withNegation globalNegation) hnode194) (Eq.refl Bool.true))
  let bounded196 := below_succ bounded195 (domain_from_eq (domain := Cases.C042.initial 195) (congrArg (Sign.withNegation globalNegation) hnode195) (Eq.refl Bool.true))
  let bounded197 := below_succ bounded196 (domain_from_eq (domain := Cases.C042.initial 196) (congrArg (Sign.withNegation globalNegation) hnode196) (Eq.refl Bool.true))
  let bounded198 := below_succ bounded197 (domain_from_eq (domain := Cases.C042.initial 197) (congrArg (Sign.withNegation globalNegation) hnode197) (Eq.refl Bool.true))
  let bounded199 := below_succ bounded198 (domain_from_eq (domain := Cases.C042.initial 198) (congrArg (Sign.withNegation globalNegation) hnode198) (Eq.refl Bool.true))
  let bounded200 := below_succ bounded199 (domain_from_eq (domain := Cases.C042.initial 199) (congrArg (Sign.withNegation globalNegation) hnode199) (Eq.refl Bool.true))
  let bounded201 := below_succ bounded200 (domain_from_eq (domain := Cases.C042.initial 200) (congrArg (Sign.withNegation globalNegation) hnode200) (Eq.refl Bool.true))
  let bounded202 := below_succ bounded201 (domain_from_eq (domain := Cases.C042.initial 201) (congrArg (Sign.withNegation globalNegation) hnode201) (Eq.refl Bool.true))
  let bounded203 := below_succ bounded202 (domain_from_eq (domain := Cases.C042.initial 202) (congrArg (Sign.withNegation globalNegation) hnode202) (Eq.refl Bool.true))
  let bounded204 := below_succ bounded203 (domain_from_eq (domain := Cases.C042.initial 203) (congrArg (Sign.withNegation globalNegation) hnode203) (Eq.refl Bool.true))
  let bounded205 := below_succ bounded204 (top_allows (Sign.withNegation globalNegation (assignment 204)))
  let bounded206 := below_succ bounded205 (top_allows (Sign.withNegation globalNegation (assignment 205)))
  let bounded207 := below_succ bounded206 (domain_from_eq (domain := Cases.C042.initial 206) (congrArg (Sign.withNegation globalNegation) hnode206) (Eq.refl Bool.true))
  let bounded208 := below_succ bounded207 (domain_from_eq (domain := Cases.C042.initial 207) (congrArg (Sign.withNegation globalNegation) (h_zero 9 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded209 := below_succ bounded208 (domain_from_eq (domain := Cases.C042.initial 208) (congrArg (Sign.withNegation globalNegation) hnode208) (Eq.refl Bool.true))
  let bounded210 := below_succ bounded209 (domain_from_eq (domain := Cases.C042.initial 209) (congrArg (Sign.withNegation globalNegation) hnode209) (Eq.refl Bool.true))
  let bounded211 := below_succ bounded210 (top_allows (Sign.withNegation globalNegation (assignment 210)))
  let bounded212 := below_succ bounded211 (domain_from_eq (domain := Cases.C042.initial 211) (congrArg (Sign.withNegation globalNegation) hnode211) (Eq.refl Bool.true))
  let bounded213 := below_succ bounded212 (domain_from_eq (domain := Cases.C042.initial 212) (congrArg (Sign.withNegation globalNegation) hnode212) (Eq.refl Bool.true))
  let bounded214 := below_succ bounded213 (domain_from_eq (domain := Cases.C042.initial 213) (congrArg (Sign.withNegation globalNegation) hnode213) (Eq.refl Bool.true))
  let bounded215 := below_succ bounded214 (domain_from_eq (domain := Cases.C042.initial 214) (congrArg (Sign.withNegation globalNegation) hnode214) (Eq.refl Bool.true))
  let bounded216 := below_succ bounded215 (top_allows (Sign.withNegation globalNegation (assignment 215)))
  let bounded217 := below_succ bounded216 (domain_from_eq (domain := Cases.C042.initial 216) (congrArg (Sign.withNegation globalNegation) hnode216) (Eq.refl Bool.true))
  let bounded218 := below_succ bounded217 (domain_from_eq (domain := Cases.C042.initial 217) (congrArg (Sign.withNegation globalNegation) hnode217) (Eq.refl Bool.true))
  let bounded219 := below_succ bounded218 (top_allows (Sign.withNegation globalNegation (assignment 218)))
  let bounded220 := below_succ bounded219 (domain_from_eq (domain := Cases.C042.initial 219) (congrArg (Sign.withNegation globalNegation) hnode219) (Eq.refl Bool.true))
  let bounded221 := below_succ bounded220 (domain_from_eq (domain := Cases.C042.initial 220) (congrArg (Sign.withNegation globalNegation) hnode220) (Eq.refl Bool.true))
  let bounded222 := below_succ bounded221 (top_allows (Sign.withNegation globalNegation (assignment 221)))
  let bounded223 := below_succ bounded222 (top_allows (Sign.withNegation globalNegation (assignment 222)))
  let bounded224 := below_succ bounded223 (domain_from_eq (domain := Cases.C042.initial 223) (congrArg (Sign.withNegation globalNegation) hnode223) (Eq.refl Bool.true))
  let bounded225 := below_succ bounded224 (domain_from_eq (domain := Cases.C042.initial 224) (congrArg (Sign.withNegation globalNegation) hnode224) (Eq.refl Bool.true))
  let bounded226 := below_succ bounded225 (top_allows (Sign.withNegation globalNegation (assignment 225)))
  let bounded227 := below_succ bounded226 (domain_from_eq (domain := Cases.C042.initial 226) (congrArg (Sign.withNegation globalNegation) hnode226) (Eq.refl Bool.true))
  let bounded228 := below_succ bounded227 (domain_from_eq (domain := Cases.C042.initial 227) (congrArg (Sign.withNegation globalNegation) hnode227) (Eq.refl Bool.true))
  let bounded229 := below_succ bounded228 (domain_from_eq (domain := Cases.C042.initial 228) (congrArg (Sign.withNegation globalNegation) hnode228) (Eq.refl Bool.true))
  let bounded230 := below_succ bounded229 (top_allows (Sign.withNegation globalNegation (assignment 229)))
  let bounded231 := below_succ bounded230 (domain_from_eq (domain := Cases.C042.initial 230) (congrArg (Sign.withNegation globalNegation) hnode230) (Eq.refl Bool.true))
  let bounded232 := below_succ bounded231 (top_allows (Sign.withNegation globalNegation (assignment 231)))
  let bounded233 := below_succ bounded232 (domain_from_eq (domain := Cases.C042.initial 232) (congrArg (Sign.withNegation globalNegation) hnode232) (Eq.refl Bool.true))
  let bounded234 := below_succ bounded233 (top_allows (Sign.withNegation globalNegation (assignment 233)))
  let bounded235 := below_succ bounded234 (domain_from_eq (domain := Cases.C042.initial 234) (congrArg (Sign.withNegation globalNegation) hnode234) (Eq.refl Bool.true))
  let bounded236 := below_succ bounded235 (top_allows (Sign.withNegation globalNegation (assignment 235)))
  let bounded237 := below_succ bounded236 (domain_from_eq (domain := Cases.C042.initial 236) (congrArg (Sign.withNegation globalNegation) hnode236) (Eq.refl Bool.true))
  let bounded238 := below_succ bounded237 (domain_from_eq (domain := Cases.C042.initial 237) (congrArg (Sign.withNegation globalNegation) hnode237) (Eq.refl Bool.true))
  let bounded239 := below_succ bounded238 (top_allows (Sign.withNegation globalNegation (assignment 238)))
  let bounded240 := below_succ bounded239 (domain_from_eq (domain := Cases.C042.initial 239) (congrArg (Sign.withNegation globalNegation) hnode239) (Eq.refl Bool.true))
  let bounded241 := below_succ bounded240 (domain_from_eq (domain := Cases.C042.initial 240) (congrArg (Sign.withNegation globalNegation) hnode240) (Eq.refl Bool.true))
  let bounded242 := below_succ bounded241 (domain_from_eq (domain := Cases.C042.initial 241) (congrArg (Sign.withNegation globalNegation) hnode241) (Eq.refl Bool.true))
  let bounded243 := below_succ bounded242 (domain_from_eq (domain := Cases.C042.initial 242) (congrArg (Sign.withNegation globalNegation) hnode242) (Eq.refl Bool.true))
  let bounded244 := below_succ bounded243 (domain_from_eq (domain := Cases.C042.initial 243) (congrArg (Sign.withNegation globalNegation) hnode243) (Eq.refl Bool.true))
  let bounded245 := below_succ bounded244 (domain_from_eq (domain := Cases.C042.initial 244) (congrArg (Sign.withNegation globalNegation) hnode244) (Eq.refl Bool.true))
  let bounded246 := below_succ bounded245 (top_allows (Sign.withNegation globalNegation (assignment 245)))
  let bounded247 := below_succ bounded246 (top_allows (Sign.withNegation globalNegation (assignment 246)))
  let bounded248 := below_succ bounded247 (domain_from_eq (domain := Cases.C042.initial 247) (congrArg (Sign.withNegation globalNegation) hnode247) (Eq.refl Bool.true))
  let bounded249 := below_succ bounded248 (domain_from_eq (domain := Cases.C042.initial 248) (congrArg (Sign.withNegation globalNegation) hnode248) (Eq.refl Bool.true))
  let bounded250 := below_succ bounded249 (top_allows (Sign.withNegation globalNegation (assignment 249)))
  let bounded251 := below_succ bounded250 (domain_from_eq (domain := Cases.C042.initial 250) (congrArg (Sign.withNegation globalNegation) hnode250) (Eq.refl Bool.true))
  let bounded252 := below_succ bounded251 (domain_from_eq (domain := Cases.C042.initial 251) (congrArg (Sign.withNegation globalNegation) hnode251) (Eq.refl Bool.true))
  bounded252

theorem support_sign_contradiction (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment)
    (h_gp : Data.ValidUsedRelations assignment) : False :=
  Cases.C042.abstract_sign_contradiction
    (fun index => Sign.withNegation globalNegation (assignment index))
    (initial_domains_sound assignment h_anchor h_support h_zero)
    (Data.ValidUsedRelations.with_global_negation h_gp globalNegation)
end Papers.RationalityTen.PureGP.Initializers.C042
#print axioms Papers.RationalityTen.PureGP.Initializers.C042.support_sign_contradiction
