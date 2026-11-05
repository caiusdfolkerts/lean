module
prelude
public import PureGP.SupportCore
public import PureGP.Cases.C018

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.PureGP.Initializers.C018
/- Finite consequence of support-sign equations; their actual geometry is separate. -/
def anchor : Nat := 2
def globalNegation : Bool := Bool.false
def edgeTable : Table SupportEdge := (Table.node 122 (Table.node 61 (Table.node 30 (Table.node 15 (Table.node 7 (Table.node 3 (Table.node 1 (Table.leaf (SupportEdge.mk 6 21 Bool.false)) (Table.node 2 (Table.leaf (SupportEdge.mk 6 36 Bool.false)) (Table.leaf (SupportEdge.mk 6 37 Bool.false)))) (Table.node 5 (Table.node 4 (Table.leaf (SupportEdge.mk 6 38 Bool.false)) (Table.leaf (SupportEdge.mk 10 25 Bool.false))) (Table.node 6 (Table.leaf (SupportEdge.mk 10 42 Bool.true)) (Table.leaf (SupportEdge.mk 10 44 Bool.true))))) (Table.node 11 (Table.node 9 (Table.node 8 (Table.leaf (SupportEdge.mk 10 45 Bool.true)) (Table.leaf (SupportEdge.mk 14 29 Bool.false))) (Table.node 10 (Table.leaf (SupportEdge.mk 14 48 Bool.true)) (Table.leaf (SupportEdge.mk 14 50 Bool.true)))) (Table.node 13 (Table.node 12 (Table.leaf (SupportEdge.mk 14 51 Bool.true)) (Table.leaf (SupportEdge.mk 74 94 Bool.false))) (Table.node 14 (Table.leaf (SupportEdge.mk 74 113 Bool.false)) (Table.leaf (SupportEdge.mk 74 115 Bool.false)))))) (Table.node 22 (Table.node 18 (Table.node 16 (Table.leaf (SupportEdge.mk 74 116 Bool.false)) (Table.node 17 (Table.leaf (SupportEdge.mk 144 164 Bool.false)) (Table.leaf (SupportEdge.mk 144 183 Bool.false)))) (Table.node 20 (Table.node 19 (Table.leaf (SupportEdge.mk 144 185 Bool.false)) (Table.leaf (SupportEdge.mk 144 186 Bool.false))) (Table.node 21 (Table.leaf (SupportEdge.mk 2 57 Bool.false)) (Table.leaf (SupportEdge.mk 2 61 Bool.false))))) (Table.node 26 (Table.node 24 (Table.node 23 (Table.leaf (SupportEdge.mk 2 65 Bool.true)) (Table.leaf (SupportEdge.mk 2 66 Bool.true))) (Table.node 25 (Table.leaf (SupportEdge.mk 5 60 Bool.false)) (Table.leaf (SupportEdge.mk 5 64 Bool.false)))) (Table.node 28 (Table.node 27 (Table.leaf (SupportEdge.mk 5 69 Bool.false)) (Table.leaf (SupportEdge.mk 5 70 Bool.false))) (Table.node 29 (Table.leaf (SupportEdge.mk 17 77 Bool.true)) (Table.leaf (SupportEdge.mk 17 83 Bool.true))))))) (Table.node 45 (Table.node 37 (Table.node 33 (Table.node 31 (Table.leaf (SupportEdge.mk 17 88 Bool.false)) (Table.node 32 (Table.leaf (SupportEdge.mk 17 89 Bool.false)) (Table.leaf (SupportEdge.mk 32 97 Bool.true)))) (Table.node 35 (Table.node 34 (Table.leaf (SupportEdge.mk 32 103 Bool.true)) (Table.leaf (SupportEdge.mk 32 108 Bool.false))) (Table.node 36 (Table.leaf (SupportEdge.mk 32 109 Bool.false)) (Table.leaf (SupportEdge.mk 137 202 Bool.false))))) (Table.node 41 (Table.node 39 (Table.node 38 (Table.leaf (SupportEdge.mk 137 208 Bool.false)) (Table.leaf (SupportEdge.mk 137 213 Bool.true))) (Table.node 40 (Table.leaf (SupportEdge.mk 137 214 Bool.true)) (Table.leaf (SupportEdge.mk 23 58 Bool.false)))) (Table.node 43 (Table.node 42 (Table.leaf (SupportEdge.mk 23 92 Bool.false)) (Table.leaf (SupportEdge.mk 23 95 Bool.false))) (Table.node 44 (Table.leaf (SupportEdge.mk 23 98 Bool.true)) (Table.leaf (SupportEdge.mk 25 60 Bool.false)))))) (Table.node 53 (Table.node 49 (Table.node 47 (Table.node 46 (Table.leaf (SupportEdge.mk 25 94 Bool.false)) (Table.leaf (SupportEdge.mk 25 97 Bool.false))) (Table.node 48 (Table.leaf (SupportEdge.mk 25 100 Bool.false)) (Table.leaf (SupportEdge.mk 34 69 Bool.false)))) (Table.node 51 (Table.node 50 (Table.leaf (SupportEdge.mk 34 105 Bool.true)) (Table.leaf (SupportEdge.mk 34 108 Bool.true))) (Table.node 52 (Table.leaf (SupportEdge.mk 34 110 Bool.false)) (Table.leaf (SupportEdge.mk 44 79 Bool.false))))) (Table.node 57 (Table.node 55 (Table.node 54 (Table.leaf (SupportEdge.mk 44 115 Bool.true)) (Table.leaf (SupportEdge.mk 44 118 Bool.true))) (Table.node 56 (Table.leaf (SupportEdge.mk 44 120 Bool.false)) (Table.leaf (SupportEdge.mk 169 204 Bool.false)))) (Table.node 59 (Table.node 58 (Table.leaf (SupportEdge.mk 169 235 Bool.false)) (Table.leaf (SupportEdge.mk 169 238 Bool.false))) (Table.node 60 (Table.leaf (SupportEdge.mk 169 240 Bool.true)) (Table.leaf (SupportEdge.mk 26 61 Bool.false)))))))) (Table.node 91 (Table.node 76 (Table.node 68 (Table.node 64 (Table.node 62 (Table.leaf (SupportEdge.mk 26 91 Bool.true)) (Table.node 63 (Table.leaf (SupportEdge.mk 26 102 Bool.true)) (Table.leaf (SupportEdge.mk 26 103 Bool.true)))) (Table.node 66 (Table.node 65 (Table.leaf (SupportEdge.mk 27 62 Bool.false)) (Table.leaf (SupportEdge.mk 27 92 Bool.true))) (Table.node 67 (Table.leaf (SupportEdge.mk 27 104 Bool.true)) (Table.leaf (SupportEdge.mk 27 105 Bool.true))))) (Table.node 72 (Table.node 70 (Table.node 69 (Table.leaf (SupportEdge.mk 30 65 Bool.false)) (Table.leaf (SupportEdge.mk 30 95 Bool.true))) (Table.node 71 (Table.leaf (SupportEdge.mk 30 107 Bool.true)) (Table.leaf (SupportEdge.mk 30 108 Bool.true)))) (Table.node 74 (Table.node 73 (Table.leaf (SupportEdge.mk 46 81 Bool.false)) (Table.leaf (SupportEdge.mk 46 111 Bool.false))) (Table.node 75 (Table.leaf (SupportEdge.mk 46 121 Bool.true)) (Table.leaf (SupportEdge.mk 46 122 Bool.true)))))) (Table.node 83 (Table.node 79 (Table.node 77 (Table.leaf (SupportEdge.mk 171 206 Bool.false)) (Table.node 78 (Table.leaf (SupportEdge.mk 171 231 Bool.true)) (Table.leaf (SupportEdge.mk 171 241 Bool.false)))) (Table.node 81 (Table.node 80 (Table.leaf (SupportEdge.mk 171 242 Bool.false)) (Table.leaf (SupportEdge.mk 37 72 Bool.false))) (Table.node 82 (Table.leaf (SupportEdge.mk 37 92 Bool.false)) (Table.leaf (SupportEdge.mk 37 111 Bool.false))))) (Table.node 87 (Table.node 85 (Table.node 84 (Table.leaf (SupportEdge.mk 37 115 Bool.true)) (Table.leaf (SupportEdge.mk 38 73 Bool.false))) (Table.node 86 (Table.leaf (SupportEdge.mk 38 93 Bool.false)) (Table.leaf (SupportEdge.mk 38 112 Bool.false)))) (Table.node 89 (Table.node 88 (Table.leaf (SupportEdge.mk 38 116 Bool.true)) (Table.leaf (SupportEdge.mk 43 78 Bool.false))) (Table.node 90 (Table.leaf (SupportEdge.mk 43 98 Bool.false)) (Table.leaf (SupportEdge.mk 43 117 Bool.true))))))) (Table.node 106 (Table.node 98 (Table.node 94 (Table.node 92 (Table.leaf (SupportEdge.mk 43 120 Bool.true)) (Table.node 93 (Table.leaf (SupportEdge.mk 49 84 Bool.false)) (Table.leaf (SupportEdge.mk 49 104 Bool.false)))) (Table.node 96 (Table.node 95 (Table.leaf (SupportEdge.mk 49 121 Bool.true)) (Table.leaf (SupportEdge.mk 49 124 Bool.true))) (Table.node 97 (Table.leaf (SupportEdge.mk 184 219 Bool.false)) (Table.leaf (SupportEdge.mk 184 234 Bool.false))))) (Table.node 102 (Table.node 100 (Table.node 99 (Table.leaf (SupportEdge.mk 184 246 Bool.false)) (Table.leaf (SupportEdge.mk 184 249 Bool.false))) (Table.node 101 (Table.leaf (SupportEdge.mk 48 83 Bool.false)) (Table.leaf (SupportEdge.mk 48 103 Bool.false)))) (Table.node 104 (Table.node 103 (Table.leaf (SupportEdge.mk 48 113 Bool.false)) (Table.leaf (SupportEdge.mk 48 122 Bool.false))) (Table.node 105 (Table.leaf (SupportEdge.mk 48 123 Bool.false)) (Table.leaf (SupportEdge.mk 2 127 Bool.true)))))) (Table.node 114 (Table.node 110 (Table.node 108 (Table.node 107 (Table.leaf (SupportEdge.mk 2 131 Bool.true)) (Table.leaf (SupportEdge.mk 2 135 Bool.false))) (Table.node 109 (Table.leaf (SupportEdge.mk 2 137 Bool.false)) (Table.leaf (SupportEdge.mk 4 129 Bool.true)))) (Table.node 112 (Table.node 111 (Table.leaf (SupportEdge.mk 4 133 Bool.true)) (Table.leaf (SupportEdge.mk 4 138 Bool.true))) (Table.node 113 (Table.leaf (SupportEdge.mk 4 140 Bool.false)) (Table.leaf (SupportEdge.mk 16 146 Bool.false))))) (Table.node 118 (Table.node 116 (Table.node 115 (Table.leaf (SupportEdge.mk 16 152 Bool.false)) (Table.leaf (SupportEdge.mk 16 157 Bool.true))) (Table.node 117 (Table.leaf (SupportEdge.mk 16 159 Bool.false)) (Table.leaf (SupportEdge.mk 31 166 Bool.false)))) (Table.node 120 (Table.node 119 (Table.leaf (SupportEdge.mk 31 172 Bool.false)) (Table.leaf (SupportEdge.mk 31 177 Bool.true))) (Table.node 121 (Table.leaf (SupportEdge.mk 31 179 Bool.false)) (Table.leaf (SupportEdge.mk 66 201 Bool.false))))))))) (Table.node 183 (Table.node 152 (Table.node 137 (Table.node 129 (Table.node 125 (Table.node 123 (Table.leaf (SupportEdge.mk 66 207 Bool.false)) (Table.node 124 (Table.leaf (SupportEdge.mk 66 212 Bool.true)) (Table.leaf (SupportEdge.mk 66 214 Bool.false)))) (Table.node 127 (Table.node 126 (Table.leaf (SupportEdge.mk 8 128 Bool.false)) (Table.leaf (SupportEdge.mk 8 142 Bool.true))) (Table.node 128 (Table.leaf (SupportEdge.mk 8 145 Bool.true)) (Table.leaf (SupportEdge.mk 8 149 Bool.false))))) (Table.node 133 (Table.node 131 (Table.node 130 (Table.leaf (SupportEdge.mk 9 129 Bool.false)) (Table.leaf (SupportEdge.mk 9 143 Bool.true))) (Table.node 132 (Table.leaf (SupportEdge.mk 9 146 Bool.true)) (Table.leaf (SupportEdge.mk 9 150 Bool.false)))) (Table.node 135 (Table.node 134 (Table.leaf (SupportEdge.mk 18 138 Bool.false)) (Table.leaf (SupportEdge.mk 18 154 Bool.false))) (Table.node 136 (Table.leaf (SupportEdge.mk 18 157 Bool.false)) (Table.leaf (SupportEdge.mk 18 160 Bool.false)))))) (Table.node 144 (Table.node 140 (Table.node 138 (Table.leaf (SupportEdge.mk 43 168 Bool.true)) (Table.node 139 (Table.leaf (SupportEdge.mk 43 184 Bool.false)) (Table.leaf (SupportEdge.mk 43 187 Bool.false)))) (Table.node 142 (Table.node 141 (Table.leaf (SupportEdge.mk 43 190 Bool.false)) (Table.leaf (SupportEdge.mk 78 203 Bool.true))) (Table.node 143 (Table.leaf (SupportEdge.mk 78 219 Bool.false)) (Table.leaf (SupportEdge.mk 78 222 Bool.false))))) (Table.node 148 (Table.node 146 (Table.node 145 (Table.leaf (SupportEdge.mk 78 225 Bool.false)) (Table.leaf (SupportEdge.mk 8 128 Bool.false))) (Table.node 147 (Table.leaf (SupportEdge.mk 8 142 Bool.true)) (Table.leaf (SupportEdge.mk 8 145 Bool.true)))) (Table.node 150 (Table.node 149 (Table.leaf (SupportEdge.mk 8 148 Bool.false)) (Table.leaf (SupportEdge.mk 10 130 Bool.false))) (Table.node 151 (Table.leaf (SupportEdge.mk 10 144 Bool.true)) (Table.leaf (SupportEdge.mk 10 147 Bool.true))))))) (Table.node 167 (Table.node 159 (Table.node 155 (Table.node 153 (Table.leaf (SupportEdge.mk 10 150 Bool.true)) (Table.node 154 (Table.leaf (SupportEdge.mk 19 139 Bool.false)) (Table.leaf (SupportEdge.mk 19 155 Bool.false)))) (Table.node 157 (Table.node 156 (Table.leaf (SupportEdge.mk 19 158 Bool.false)) (Table.leaf (SupportEdge.mk 19 160 Bool.true))) (Table.node 158 (Table.leaf (SupportEdge.mk 44 169 Bool.true)) (Table.leaf (SupportEdge.mk 44 185 Bool.false))))) (Table.node 163 (Table.node 161 (Table.node 160 (Table.leaf (SupportEdge.mk 44 188 Bool.false)) (Table.leaf (SupportEdge.mk 44 190 Bool.true))) (Table.node 162 (Table.leaf (SupportEdge.mk 79 204 Bool.true)) (Table.leaf (SupportEdge.mk 79 220 Bool.false)))) (Table.node 165 (Table.node 164 (Table.leaf (SupportEdge.mk 79 223 Bool.false)) (Table.leaf (SupportEdge.mk 79 225 Bool.true))) (Table.node 166 (Table.leaf (SupportEdge.mk 11 131 Bool.false)) (Table.leaf (SupportEdge.mk 11 141 Bool.false)))))) (Table.node 175 (Table.node 171 (Table.node 169 (Table.node 168 (Table.leaf (SupportEdge.mk 11 151 Bool.false)) (Table.leaf (SupportEdge.mk 11 152 Bool.false))) (Table.node 170 (Table.leaf (SupportEdge.mk 14 134 Bool.false)) (Table.leaf (SupportEdge.mk 14 144 Bool.false)))) (Table.node 173 (Table.node 172 (Table.leaf (SupportEdge.mk 14 155 Bool.true)) (Table.leaf (SupportEdge.mk 14 156 Bool.true))) (Table.node 174 (Table.leaf (SupportEdge.mk 17 137 Bool.false)) (Table.leaf (SupportEdge.mk 17 147 Bool.false))))) (Table.node 179 (Table.node 177 (Table.node 176 (Table.leaf (SupportEdge.mk 17 158 Bool.true)) (Table.leaf (SupportEdge.mk 17 159 Bool.true))) (Table.node 178 (Table.leaf (SupportEdge.mk 48 173 Bool.true)) (Table.leaf (SupportEdge.mk 48 183 Bool.true)))) (Table.node 181 (Table.node 180 (Table.leaf (SupportEdge.mk 48 192 Bool.true)) (Table.leaf (SupportEdge.mk 48 193 Bool.true))) (Table.node 182 (Table.leaf (SupportEdge.mk 83 208 Bool.true)) (Table.leaf (SupportEdge.mk 83 218 Bool.true)))))))) (Table.node 214 (Table.node 198 (Table.node 190 (Table.node 186 (Table.node 184 (Table.leaf (SupportEdge.mk 83 227 Bool.true)) (Table.node 185 (Table.leaf (SupportEdge.mk 83 228 Bool.true)) (Table.leaf (SupportEdge.mk 36 141 Bool.true)))) (Table.node 188 (Table.node 187 (Table.leaf (SupportEdge.mk 36 161 Bool.true)) (Table.leaf (SupportEdge.mk 36 181 Bool.false))) (Table.node 189 (Table.leaf (SupportEdge.mk 36 183 Bool.false)) (Table.leaf (SupportEdge.mk 38 143 Bool.true))))) (Table.node 194 (Table.node 192 (Table.node 191 (Table.leaf (SupportEdge.mk 38 163 Bool.true)) (Table.leaf (SupportEdge.mk 38 184 Bool.true))) (Table.node 193 (Table.leaf (SupportEdge.mk 38 186 Bool.false)) (Table.leaf (SupportEdge.mk 41 146 Bool.true)))) (Table.node 196 (Table.node 195 (Table.leaf (SupportEdge.mk 41 166 Bool.true)) (Table.leaf (SupportEdge.mk 41 187 Bool.true))) (Table.node 197 (Table.leaf (SupportEdge.mk 41 189 Bool.false)) (Table.leaf (SupportEdge.mk 47 152 Bool.true)))))) (Table.node 206 (Table.node 202 (Table.node 200 (Table.node 199 (Table.leaf (SupportEdge.mk 47 172 Bool.true)) (Table.leaf (SupportEdge.mk 47 191 Bool.true))) (Table.node 201 (Table.leaf (SupportEdge.mk 47 193 Bool.false)) (Table.leaf (SupportEdge.mk 112 217 Bool.false)))) (Table.node 204 (Table.node 203 (Table.leaf (SupportEdge.mk 112 232 Bool.false)) (Table.leaf (SupportEdge.mk 112 246 Bool.true))) (Table.node 205 (Table.leaf (SupportEdge.mk 112 248 Bool.false)) (Table.leaf (SupportEdge.mk 68 138 Bool.false))))) (Table.node 210 (Table.node 208 (Table.node 207 (Table.leaf (SupportEdge.mk 68 203 Bool.false)) (Table.leaf (SupportEdge.mk 68 209 Bool.false))) (Table.node 209 (Table.leaf (SupportEdge.mk 68 212 Bool.false)) (Table.leaf (SupportEdge.mk 69 139 Bool.false)))) (Table.node 212 (Table.node 211 (Table.leaf (SupportEdge.mk 69 204 Bool.false)) (Table.leaf (SupportEdge.mk 69 210 Bool.false))) (Table.node 213 (Table.leaf (SupportEdge.mk 69 213 Bool.false)) (Table.leaf (SupportEdge.mk 70 140 Bool.false))))))) (Table.node 229 (Table.node 221 (Table.node 217 (Table.node 215 (Table.leaf (SupportEdge.mk 70 205 Bool.false)) (Table.node 216 (Table.leaf (SupportEdge.mk 70 211 Bool.false)) (Table.leaf (SupportEdge.mk 70 214 Bool.false)))) (Table.node 219 (Table.node 218 (Table.leaf (SupportEdge.mk 90 160 Bool.false)) (Table.leaf (SupportEdge.mk 90 225 Bool.true))) (Table.node 220 (Table.leaf (SupportEdge.mk 90 229 Bool.true)) (Table.leaf (SupportEdge.mk 90 230 Bool.true))))) (Table.node 225 (Table.node 223 (Table.node 222 (Table.leaf (SupportEdge.mk 110 180 Bool.false)) (Table.leaf (SupportEdge.mk 110 240 Bool.true))) (Table.node 224 (Table.leaf (SupportEdge.mk 110 244 Bool.true)) (Table.leaf (SupportEdge.mk 110 245 Bool.true)))) (Table.node 227 (Table.node 226 (Table.leaf (SupportEdge.mk 101 171 Bool.false)) (Table.leaf (SupportEdge.mk 101 206 Bool.false))) (Table.node 228 (Table.leaf (SupportEdge.mk 101 231 Bool.true)) (Table.leaf (SupportEdge.mk 101 242 Bool.false)))))) (Table.node 237 (Table.node 233 (Table.node 231 (Table.node 230 (Table.leaf (SupportEdge.mk 102 172 Bool.false)) (Table.leaf (SupportEdge.mk 102 207 Bool.false))) (Table.node 232 (Table.leaf (SupportEdge.mk 102 232 Bool.true)) (Table.leaf (SupportEdge.mk 102 243 Bool.false)))) (Table.node 235 (Table.node 234 (Table.leaf (SupportEdge.mk 104 174 Bool.false)) (Table.leaf (SupportEdge.mk 104 209 Bool.false))) (Table.node 236 (Table.leaf (SupportEdge.mk 104 234 Bool.true)) (Table.leaf (SupportEdge.mk 104 244 Bool.false))))) (Table.node 241 (Table.node 239 (Table.node 238 (Table.leaf (SupportEdge.mk 107 177 Bool.false)) (Table.leaf (SupportEdge.mk 107 212 Bool.false))) (Table.node 240 (Table.leaf (SupportEdge.mk 107 237 Bool.true)) (Table.leaf (SupportEdge.mk 107 245 Bool.false)))) (Table.node 243 (Table.node 242 (Table.leaf (SupportEdge.mk 121 191 Bool.false)) (Table.leaf (SupportEdge.mk 121 226 Bool.false))) (Table.node 244 (Table.leaf (SupportEdge.mk 121 246 Bool.false)) (Table.leaf (SupportEdge.mk 121 251 Bool.false))))))))))
def edge (index : Nat) : SupportEdge := edgeTable.get index
def zeroTable : Table Nat := (Table.node 10 (Table.node 5 (Table.node 2 (Table.node 1 (Table.leaf 8) (Table.leaf 39)) (Table.node 3 (Table.leaf 67) (Table.node 4 (Table.leaf 99) (Table.leaf 101)))) (Table.node 7 (Table.node 6 (Table.leaf 114) (Table.leaf 128)) (Table.node 8 (Table.leaf 136) (Table.node 9 (Table.leaf 142) (Table.leaf 145))))) (Table.node 15 (Table.node 12 (Table.node 11 (Table.leaf 148) (Table.leaf 149)) (Table.node 13 (Table.leaf 153) (Table.node 14 (Table.leaf 171) (Table.leaf 182)))) (Table.node 17 (Table.node 16 (Table.leaf 206) (Table.leaf 215)) (Table.node 18 (Table.leaf 231) (Table.node 19 (Table.leaf 241) (Table.leaf 242))))))
def zero (index : Nat) : Nat := zeroTable.get index
def SupportEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 245 → (edge index).Holds assignment
def ZeroEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 20 → Eq (assignment (zero index)) Sign.zero

theorem initial_domains_sound (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment) :
    ∀ index, LT.lt index 252 →
      Eq ((Cases.C018.initial index).allows
        (Sign.withNegation globalNegation (assignment index))) Bool.true :=
  let hnode57 : Eq (assignment 57) Sign.positive :=
    Eq.trans (h_support 20 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode61 : Eq (assignment 61) Sign.positive :=
    Eq.trans (h_support 21 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode65 : Eq (assignment 65) Sign.negative :=
    Eq.trans (h_support 22 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode66 : Eq (assignment 66) Sign.negative :=
    Eq.trans (h_support 23 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode127 : Eq (assignment 127) Sign.negative :=
    Eq.trans (h_support 105 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode131 : Eq (assignment 131) Sign.negative :=
    Eq.trans (h_support 106 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode135 : Eq (assignment 135) Sign.positive :=
    Eq.trans (h_support 107 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode137 : Eq (assignment 137) Sign.positive :=
    Eq.trans (h_support 108 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode11 : Eq (assignment 11) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 165 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode131)
  let hnode17 : Eq (assignment 17) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 173 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode137)
  let hnode26 : Eq (assignment 26) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 60 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode61)
  let hnode30 : Eq (assignment 30) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 68 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode65)
  let hnode201 : Eq (assignment 201) Sign.negative :=
    Eq.trans (h_support 121 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode66)
  let hnode202 : Eq (assignment 202) Sign.positive :=
    Eq.trans (h_support 36 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode137)
  let hnode207 : Eq (assignment 207) Sign.negative :=
    Eq.trans (h_support 122 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode66)
  let hnode208 : Eq (assignment 208) Sign.positive :=
    Eq.trans (h_support 37 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode137)
  let hnode212 : Eq (assignment 212) Sign.positive :=
    Eq.trans (h_support 123 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode66)
  let hnode213 : Eq (assignment 213) Sign.negative :=
    Eq.trans (h_support 38 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode137)
  let hnode214 : Eq (assignment 214) Sign.negative :=
    Eq.trans (h_support 124 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode66)
  let hnode68 : Eq (assignment 68) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 208 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode212)
  let hnode69 : Eq (assignment 69) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 212 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode213)
  let hnode70 : Eq (assignment 70) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 216 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode214)
  let hnode77 : Eq (assignment 77) Sign.negative :=
    Eq.trans (h_support 28 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode17)
  let hnode83 : Eq (assignment 83) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 181 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode208)
  let hnode88 : Eq (assignment 88) Sign.positive :=
    Eq.trans (h_support 30 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode17)
  let hnode89 : Eq (assignment 89) Sign.positive :=
    Eq.trans (h_support 31 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode17)
  let hnode91 : Eq (assignment 91) Sign.negative :=
    Eq.trans (h_support 61 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode26)
  let hnode95 : Eq (assignment 95) Sign.positive :=
    Eq.trans (h_support 69 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode30)
  let hnode102 : Eq (assignment 102) Sign.negative :=
    Eq.trans (h_support 62 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode26)
  let hnode103 : Eq (assignment 103) Sign.negative :=
    Eq.trans (h_support 63 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode26)
  let hnode107 : Eq (assignment 107) Sign.positive :=
    Eq.trans (h_support 70 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode30)
  let hnode108 : Eq (assignment 108) Sign.positive :=
    Eq.trans (h_support 71 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode30)
  let hnode141 : Eq (assignment 141) Sign.negative :=
    Eq.trans (h_support 166 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode11)
  let hnode147 : Eq (assignment 147) Sign.positive :=
    Eq.trans (h_support 174 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode17)
  let hnode151 : Eq (assignment 151) Sign.negative :=
    Eq.trans (h_support 167 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode11)
  let hnode152 : Eq (assignment 152) Sign.negative :=
    Eq.trans (h_support 168 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode11)
  let hnode158 : Eq (assignment 158) Sign.negative :=
    Eq.trans (h_support 175 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode17)
  let hnode159 : Eq (assignment 159) Sign.negative :=
    Eq.trans (h_support 176 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode17)
  let hnode5 : Eq (assignment 5) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 27 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode70)
  let hnode10 : Eq (assignment 10) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 151 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode147)
  let hnode16 : Eq (assignment 16) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 114 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode152)
  let hnode19 : Eq (assignment 19) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 155 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode158)
  let hnode23 : Eq (assignment 23) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 42 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode95)
  let hnode32 : Eq (assignment 32) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 33 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode103)
  let hnode34 : Eq (assignment 34) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 50 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode108)
  let hnode36 : Eq (assignment 36) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 185 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode141)
  let hnode47 : Eq (assignment 47) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 197 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode152)
  let hnode48 : Eq (assignment 48) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 101 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode103)
  let hnode138 : Eq (assignment 138) Sign.positive :=
    Eq.trans (h_support 205 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode68)
  let hnode139 : Eq (assignment 139) Sign.negative :=
    Eq.trans (h_support 209 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode69)
  let hnode140 : Eq (assignment 140) Sign.negative :=
    Eq.trans (h_support 213 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode70)
  let hnode172 : Eq (assignment 172) Sign.negative :=
    Eq.trans (h_support 229 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode102)
  let hnode177 : Eq (assignment 177) Sign.positive :=
    Eq.trans (h_support 237 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode107)
  let hnode203 : Eq (assignment 203) Sign.positive :=
    Eq.trans (h_support 206 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode68)
  let hnode204 : Eq (assignment 204) Sign.negative :=
    Eq.trans (h_support 210 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode69)
  let hnode205 : Eq (assignment 205) Sign.negative :=
    Eq.trans (h_support 214 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode70)
  let hnode209 : Eq (assignment 209) Sign.positive :=
    Eq.trans (h_support 207 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode68)
  let hnode210 : Eq (assignment 210) Sign.negative :=
    Eq.trans (h_support 211 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode69)
  let hnode211 : Eq (assignment 211) Sign.negative :=
    Eq.trans (h_support 215 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode70)
  let hnode218 : Eq (assignment 218) Sign.positive :=
    Eq.trans (h_support 182 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode83)
  let hnode227 : Eq (assignment 227) Sign.positive :=
    Eq.trans (h_support 183 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode83)
  let hnode228 : Eq (assignment 228) Sign.positive :=
    Eq.trans (h_support 184 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode83)
  let hnode232 : Eq (assignment 232) Sign.positive :=
    Eq.trans (h_support 231 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode102)
  let hnode237 : Eq (assignment 237) Sign.negative :=
    Eq.trans (h_support 239 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode107)
  let hnode243 : Eq (assignment 243) Sign.negative :=
    Eq.trans (h_support 232 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode102)
  let hnode245 : Eq (assignment 245) Sign.positive :=
    Eq.trans (h_support 240 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode107)
  let hnode4 : Eq (assignment 4) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 111 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode138)
  let hnode6 : Eq (assignment 6) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 1 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode36)
  let hnode14 : Eq (assignment 14) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 9 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode48)
  let hnode18 : Eq (assignment 18) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 133 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode138)
  let hnode25 : Eq (assignment 25) Sign.negative :=
    Eq.trans (h_support 4 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode10)
  let hnode31 : Eq (assignment 31) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 118 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode172)
  let hnode42 : Eq (assignment 42) Sign.positive :=
    Eq.trans (h_support 5 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode10)
  let hnode44 : Eq (assignment 44) Sign.positive :=
    Eq.trans (h_support 6 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode10)
  let hnode45 : Eq (assignment 45) Sign.positive :=
    Eq.trans (h_support 7 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode10)
  let hnode58 : Eq (assignment 58) Sign.positive :=
    Eq.trans (h_support 40 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode23)
  let hnode60 : Eq (assignment 60) Sign.negative :=
    Eq.trans (h_support 24 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode5)
  let hnode64 : Eq (assignment 64) Sign.negative :=
    Eq.trans (h_support 25 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode5)
  let hnode78 : Eq (assignment 78) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 141 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode203)
  let hnode79 : Eq (assignment 79) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 161 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode204)
  let hnode92 : Eq (assignment 92) Sign.positive :=
    Eq.trans (h_support 41 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode23)
  let hnode97 : Eq (assignment 97) Sign.negative :=
    Eq.trans (h_support 32 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode32)
  let hnode98 : Eq (assignment 98) Sign.negative :=
    Eq.trans (h_support 43 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode23)
  let hnode104 : Eq (assignment 104) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 234 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode209)
  let hnode105 : Eq (assignment 105) Sign.positive :=
    Eq.trans (h_support 49 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode34)
  let hnode109 : Eq (assignment 109) Sign.positive :=
    Eq.trans (h_support 35 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode32)
  let hnode110 : Eq (assignment 110) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 224 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode245)
  let hnode112 : Eq (assignment 112) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 202 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode232)
  let hnode113 : Eq (assignment 113) Sign.negative :=
    Eq.trans (h_support 102 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode48)
  let hnode122 : Eq (assignment 122) Sign.negative :=
    Eq.trans (h_support 103 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode48)
  let hnode123 : Eq (assignment 123) Sign.negative :=
    Eq.trans (h_support 104 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode48)
  let hnode130 : Eq (assignment 130) Sign.negative :=
    Eq.trans (h_support 149 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode10)
  let hnode144 : Eq (assignment 144) Sign.positive :=
    Eq.trans (h_support 150 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode10)
  let hnode146 : Eq (assignment 146) Sign.negative :=
    Eq.trans (h_support 113 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode16)
  let hnode150 : Eq (assignment 150) Sign.positive :=
    Eq.trans (h_support 152 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode10)
  let hnode155 : Eq (assignment 155) Sign.negative :=
    Eq.trans (h_support 154 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode19)
  let hnode157 : Eq (assignment 157) Sign.positive :=
    Eq.trans (h_support 115 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode16)
  let hnode160 : Eq (assignment 160) Sign.positive :=
    Eq.trans (h_support 156 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode19)
  let hnode161 : Eq (assignment 161) Sign.negative :=
    Eq.trans (h_support 186 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode36)
  let hnode169 : Eq (assignment 169) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 56 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode204)
  let hnode173 : Eq (assignment 173) Sign.positive :=
    Eq.trans (h_support 177 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode48)
  let hnode181 : Eq (assignment 181) Sign.positive :=
    Eq.trans (h_support 187 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode36)
  let hnode183 : Eq (assignment 183) Sign.positive :=
    Eq.trans (h_support 178 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode48)
  let hnode191 : Eq (assignment 191) Sign.negative :=
    Eq.trans (h_support 199 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode47)
  let hnode192 : Eq (assignment 192) Sign.positive :=
    Eq.trans (h_support 179 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode48)
  let hnode193 : Eq (assignment 193) Sign.positive :=
    Eq.trans (h_support 180 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode48)
  let hnode9 : Eq (assignment 9) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 131 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode146)
  let hnode21 : Eq (assignment 21) Sign.positive :=
    Eq.trans (h_support 0 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode6)
  let hnode27 : Eq (assignment 27) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 65 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode92)
  let hnode29 : Eq (assignment 29) Sign.positive :=
    Eq.trans (h_support 8 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode14)
  let hnode37 : Eq (assignment 37) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 81 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode92)
  let hnode38 : Eq (assignment 38) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 86 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode112)
  let hnode41 : Eq (assignment 41) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 193 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode146)
  let hnode43 : Eq (assignment 43) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 89 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode98)
  let hnode46 : Eq (assignment 46) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 75 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode122)
  let hnode49 : Eq (assignment 49) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 93 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode104)
  let hnode50 : Eq (assignment 50) Sign.negative :=
    Eq.trans (h_support 10 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode14)
  let hnode51 : Eq (assignment 51) Sign.negative :=
    Eq.trans (h_support 11 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode14)
  let hnode74 : Eq (assignment 74) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 13 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode113)
  let hnode90 : Eq (assignment 90) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 217 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode160)
  let hnode94 : Eq (assignment 94) Sign.negative :=
    Eq.trans (h_support 45 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode25)
  let hnode100 : Eq (assignment 100) Sign.negative :=
    Eq.trans (h_support 47 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode25)
  let hnode115 : Eq (assignment 115) Sign.negative :=
    Eq.trans (h_support 53 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode44)
  let hnode118 : Eq (assignment 118) Sign.negative :=
    Eq.trans (h_support 54 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode44)
  let hnode120 : Eq (assignment 120) Sign.positive :=
    Eq.trans (h_support 55 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode44)
  let hnode121 : Eq (assignment 121) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 241 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode191)
  let hnode129 : Eq (assignment 129) Sign.positive :=
    Eq.trans (h_support 109 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode4)
  let hnode133 : Eq (assignment 133) Sign.positive :=
    Eq.trans (h_support 110 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode4)
  let hnode134 : Eq (assignment 134) Sign.positive :=
    Eq.trans (h_support 169 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode14)
  let hnode154 : Eq (assignment 154) Sign.positive :=
    Eq.trans (h_support 134 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode18)
  let hnode156 : Eq (assignment 156) Sign.negative :=
    Eq.trans (h_support 172 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode14)
  let hnode164 : Eq (assignment 164) Sign.positive :=
    Eq.trans (h_support 16 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode144)
  let hnode166 : Eq (assignment 166) Sign.negative :=
    Eq.trans (h_support 117 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode31)
  let hnode174 : Eq (assignment 174) Sign.positive :=
    Eq.trans (h_support 233 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode104)
  let hnode179 : Eq (assignment 179) Sign.negative :=
    Eq.trans (h_support 120 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode31)
  let hnode180 : Eq (assignment 180) Sign.negative :=
    Eq.trans (h_support 221 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode110)
  let hnode185 : Eq (assignment 185) Sign.positive :=
    Eq.trans (h_support 158 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode44)
  let hnode186 : Eq (assignment 186) Sign.positive :=
    Eq.trans (h_support 19 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode144)
  let hnode188 : Eq (assignment 188) Sign.positive :=
    Eq.trans (h_support 159 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode44)
  let hnode190 : Eq (assignment 190) Sign.negative :=
    Eq.trans (h_support 160 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode44)
  let hnode217 : Eq (assignment 217) Sign.positive :=
    Eq.trans (h_support 201 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode112)
  let hnode219 : Eq (assignment 219) Sign.negative :=
    Eq.trans (h_support 142 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode78)
  let hnode220 : Eq (assignment 220) Sign.positive :=
    Eq.trans (h_support 162 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode79)
  let hnode222 : Eq (assignment 222) Sign.negative :=
    Eq.trans (h_support 143 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode78)
  let hnode223 : Eq (assignment 223) Sign.positive :=
    Eq.trans (h_support 163 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode79)
  let hnode225 : Eq (assignment 225) Sign.negative :=
    Eq.trans (h_support 144 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode78)
  let hnode234 : Eq (assignment 234) Sign.negative :=
    Eq.trans (h_support 235 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode104)
  let hnode235 : Eq (assignment 235) Sign.negative :=
    Eq.trans (h_support 57 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode169)
  let hnode238 : Eq (assignment 238) Sign.negative :=
    Eq.trans (h_support 58 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode169)
  let hnode240 : Eq (assignment 240) Sign.positive :=
    Eq.trans (h_support 222 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode110)
  let hnode244 : Eq (assignment 244) Sign.positive :=
    Eq.trans (h_support 223 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode110)
  let hnode246 : Eq (assignment 246) Sign.negative :=
    Eq.trans (h_support 203 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode112)
  let hnode248 : Eq (assignment 248) Sign.positive :=
    Eq.trans (h_support 204 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode112)
  let hnode62 : Eq (assignment 62) Sign.negative :=
    Eq.trans (h_support 64 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode27)
  let hnode72 : Eq (assignment 72) Sign.positive :=
    Eq.trans (h_support 80 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode37)
  let hnode73 : Eq (assignment 73) Sign.positive :=
    Eq.trans (h_support 84 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode38)
  let hnode81 : Eq (assignment 81) Sign.positive :=
    Eq.trans (h_support 72 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode46)
  let hnode84 : Eq (assignment 84) Sign.positive :=
    Eq.trans (h_support 92 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode49)
  let hnode93 : Eq (assignment 93) Sign.positive :=
    Eq.trans (h_support 85 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode38)
  let hnode111 : Eq (assignment 111) Sign.positive :=
    Eq.trans (h_support 73 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode46)
  let hnode116 : Eq (assignment 116) Sign.negative :=
    Eq.trans (h_support 87 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode38)
  let hnode117 : Eq (assignment 117) Sign.positive :=
    Eq.trans (h_support 90 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode43)
  let hnode124 : Eq (assignment 124) Sign.negative :=
    Eq.trans (h_support 95 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode49)
  let hnode143 : Eq (assignment 143) Sign.negative :=
    Eq.trans (h_support 189 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode38)
  let hnode163 : Eq (assignment 163) Sign.negative :=
    Eq.trans (h_support 190 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode38)
  let hnode168 : Eq (assignment 168) Sign.positive :=
    Eq.trans (h_support 137 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode43)
  let hnode184 : Eq (assignment 184) Sign.negative :=
    Eq.trans (h_support 191 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode38)
  let hnode187 : Eq (assignment 187) Sign.negative :=
    Eq.trans (h_support 139 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode43)
  let hnode189 : Eq (assignment 189) Sign.positive :=
    Eq.trans (h_support 196 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode41)
  let hnode226 : Eq (assignment 226) Sign.negative :=
    Eq.trans (h_support 242 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode121)
  let hnode229 : Eq (assignment 229) Sign.negative :=
    Eq.trans (h_support 219 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode90)
  let hnode230 : Eq (assignment 230) Sign.negative :=
    Eq.trans (h_support 220 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode90)
  let hnode251 : Eq (assignment 251) Sign.negative :=
    Eq.trans (h_support 244 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode121)
  let hnode249 : Eq (assignment 249) Sign.negative :=
    Eq.trans (h_support 99 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode184)
  let predicate : Nat → Prop := fun index =>
    Eq ((Cases.C018.initial index).allows
      (Sign.withNegation globalNegation (assignment index))) Bool.true
  let bounded0 := below_zero predicate
  let bounded1 := below_succ bounded0 (top_allows (Sign.withNegation globalNegation (assignment 0)))
  let bounded2 := below_succ bounded1 (top_allows (Sign.withNegation globalNegation (assignment 1)))
  let bounded3 := below_succ bounded2 (domain_from_eq (domain := Cases.C018.initial 2) (congrArg (Sign.withNegation globalNegation) h_anchor) (Eq.refl Bool.true))
  let bounded4 := below_succ bounded3 (top_allows (Sign.withNegation globalNegation (assignment 3)))
  let bounded5 := below_succ bounded4 (domain_from_eq (domain := Cases.C018.initial 4) (congrArg (Sign.withNegation globalNegation) hnode4) (Eq.refl Bool.true))
  let bounded6 := below_succ bounded5 (domain_from_eq (domain := Cases.C018.initial 5) (congrArg (Sign.withNegation globalNegation) hnode5) (Eq.refl Bool.true))
  let bounded7 := below_succ bounded6 (domain_from_eq (domain := Cases.C018.initial 6) (congrArg (Sign.withNegation globalNegation) hnode6) (Eq.refl Bool.true))
  let bounded8 := below_succ bounded7 (top_allows (Sign.withNegation globalNegation (assignment 7)))
  let bounded9 := below_succ bounded8 (domain_from_eq (domain := Cases.C018.initial 8) (congrArg (Sign.withNegation globalNegation) (h_zero 0 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded10 := below_succ bounded9 (domain_from_eq (domain := Cases.C018.initial 9) (congrArg (Sign.withNegation globalNegation) hnode9) (Eq.refl Bool.true))
  let bounded11 := below_succ bounded10 (domain_from_eq (domain := Cases.C018.initial 10) (congrArg (Sign.withNegation globalNegation) hnode10) (Eq.refl Bool.true))
  let bounded12 := below_succ bounded11 (domain_from_eq (domain := Cases.C018.initial 11) (congrArg (Sign.withNegation globalNegation) hnode11) (Eq.refl Bool.true))
  let bounded13 := below_succ bounded12 (top_allows (Sign.withNegation globalNegation (assignment 12)))
  let bounded14 := below_succ bounded13 (top_allows (Sign.withNegation globalNegation (assignment 13)))
  let bounded15 := below_succ bounded14 (domain_from_eq (domain := Cases.C018.initial 14) (congrArg (Sign.withNegation globalNegation) hnode14) (Eq.refl Bool.true))
  let bounded16 := below_succ bounded15 (top_allows (Sign.withNegation globalNegation (assignment 15)))
  let bounded17 := below_succ bounded16 (domain_from_eq (domain := Cases.C018.initial 16) (congrArg (Sign.withNegation globalNegation) hnode16) (Eq.refl Bool.true))
  let bounded18 := below_succ bounded17 (domain_from_eq (domain := Cases.C018.initial 17) (congrArg (Sign.withNegation globalNegation) hnode17) (Eq.refl Bool.true))
  let bounded19 := below_succ bounded18 (domain_from_eq (domain := Cases.C018.initial 18) (congrArg (Sign.withNegation globalNegation) hnode18) (Eq.refl Bool.true))
  let bounded20 := below_succ bounded19 (domain_from_eq (domain := Cases.C018.initial 19) (congrArg (Sign.withNegation globalNegation) hnode19) (Eq.refl Bool.true))
  let bounded21 := below_succ bounded20 (top_allows (Sign.withNegation globalNegation (assignment 20)))
  let bounded22 := below_succ bounded21 (domain_from_eq (domain := Cases.C018.initial 21) (congrArg (Sign.withNegation globalNegation) hnode21) (Eq.refl Bool.true))
  let bounded23 := below_succ bounded22 (top_allows (Sign.withNegation globalNegation (assignment 22)))
  let bounded24 := below_succ bounded23 (domain_from_eq (domain := Cases.C018.initial 23) (congrArg (Sign.withNegation globalNegation) hnode23) (Eq.refl Bool.true))
  let bounded25 := below_succ bounded24 (top_allows (Sign.withNegation globalNegation (assignment 24)))
  let bounded26 := below_succ bounded25 (domain_from_eq (domain := Cases.C018.initial 25) (congrArg (Sign.withNegation globalNegation) hnode25) (Eq.refl Bool.true))
  let bounded27 := below_succ bounded26 (domain_from_eq (domain := Cases.C018.initial 26) (congrArg (Sign.withNegation globalNegation) hnode26) (Eq.refl Bool.true))
  let bounded28 := below_succ bounded27 (domain_from_eq (domain := Cases.C018.initial 27) (congrArg (Sign.withNegation globalNegation) hnode27) (Eq.refl Bool.true))
  let bounded29 := below_succ bounded28 (top_allows (Sign.withNegation globalNegation (assignment 28)))
  let bounded30 := below_succ bounded29 (domain_from_eq (domain := Cases.C018.initial 29) (congrArg (Sign.withNegation globalNegation) hnode29) (Eq.refl Bool.true))
  let bounded31 := below_succ bounded30 (domain_from_eq (domain := Cases.C018.initial 30) (congrArg (Sign.withNegation globalNegation) hnode30) (Eq.refl Bool.true))
  let bounded32 := below_succ bounded31 (domain_from_eq (domain := Cases.C018.initial 31) (congrArg (Sign.withNegation globalNegation) hnode31) (Eq.refl Bool.true))
  let bounded33 := below_succ bounded32 (domain_from_eq (domain := Cases.C018.initial 32) (congrArg (Sign.withNegation globalNegation) hnode32) (Eq.refl Bool.true))
  let bounded34 := below_succ bounded33 (top_allows (Sign.withNegation globalNegation (assignment 33)))
  let bounded35 := below_succ bounded34 (domain_from_eq (domain := Cases.C018.initial 34) (congrArg (Sign.withNegation globalNegation) hnode34) (Eq.refl Bool.true))
  let bounded36 := below_succ bounded35 (top_allows (Sign.withNegation globalNegation (assignment 35)))
  let bounded37 := below_succ bounded36 (domain_from_eq (domain := Cases.C018.initial 36) (congrArg (Sign.withNegation globalNegation) hnode36) (Eq.refl Bool.true))
  let bounded38 := below_succ bounded37 (domain_from_eq (domain := Cases.C018.initial 37) (congrArg (Sign.withNegation globalNegation) hnode37) (Eq.refl Bool.true))
  let bounded39 := below_succ bounded38 (domain_from_eq (domain := Cases.C018.initial 38) (congrArg (Sign.withNegation globalNegation) hnode38) (Eq.refl Bool.true))
  let bounded40 := below_succ bounded39 (domain_from_eq (domain := Cases.C018.initial 39) (congrArg (Sign.withNegation globalNegation) (h_zero 1 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded41 := below_succ bounded40 (top_allows (Sign.withNegation globalNegation (assignment 40)))
  let bounded42 := below_succ bounded41 (domain_from_eq (domain := Cases.C018.initial 41) (congrArg (Sign.withNegation globalNegation) hnode41) (Eq.refl Bool.true))
  let bounded43 := below_succ bounded42 (domain_from_eq (domain := Cases.C018.initial 42) (congrArg (Sign.withNegation globalNegation) hnode42) (Eq.refl Bool.true))
  let bounded44 := below_succ bounded43 (domain_from_eq (domain := Cases.C018.initial 43) (congrArg (Sign.withNegation globalNegation) hnode43) (Eq.refl Bool.true))
  let bounded45 := below_succ bounded44 (domain_from_eq (domain := Cases.C018.initial 44) (congrArg (Sign.withNegation globalNegation) hnode44) (Eq.refl Bool.true))
  let bounded46 := below_succ bounded45 (domain_from_eq (domain := Cases.C018.initial 45) (congrArg (Sign.withNegation globalNegation) hnode45) (Eq.refl Bool.true))
  let bounded47 := below_succ bounded46 (domain_from_eq (domain := Cases.C018.initial 46) (congrArg (Sign.withNegation globalNegation) hnode46) (Eq.refl Bool.true))
  let bounded48 := below_succ bounded47 (domain_from_eq (domain := Cases.C018.initial 47) (congrArg (Sign.withNegation globalNegation) hnode47) (Eq.refl Bool.true))
  let bounded49 := below_succ bounded48 (domain_from_eq (domain := Cases.C018.initial 48) (congrArg (Sign.withNegation globalNegation) hnode48) (Eq.refl Bool.true))
  let bounded50 := below_succ bounded49 (domain_from_eq (domain := Cases.C018.initial 49) (congrArg (Sign.withNegation globalNegation) hnode49) (Eq.refl Bool.true))
  let bounded51 := below_succ bounded50 (domain_from_eq (domain := Cases.C018.initial 50) (congrArg (Sign.withNegation globalNegation) hnode50) (Eq.refl Bool.true))
  let bounded52 := below_succ bounded51 (domain_from_eq (domain := Cases.C018.initial 51) (congrArg (Sign.withNegation globalNegation) hnode51) (Eq.refl Bool.true))
  let bounded53 := below_succ bounded52 (top_allows (Sign.withNegation globalNegation (assignment 52)))
  let bounded54 := below_succ bounded53 (top_allows (Sign.withNegation globalNegation (assignment 53)))
  let bounded55 := below_succ bounded54 (top_allows (Sign.withNegation globalNegation (assignment 54)))
  let bounded56 := below_succ bounded55 (top_allows (Sign.withNegation globalNegation (assignment 55)))
  let bounded57 := below_succ bounded56 (top_allows (Sign.withNegation globalNegation (assignment 56)))
  let bounded58 := below_succ bounded57 (domain_from_eq (domain := Cases.C018.initial 57) (congrArg (Sign.withNegation globalNegation) hnode57) (Eq.refl Bool.true))
  let bounded59 := below_succ bounded58 (domain_from_eq (domain := Cases.C018.initial 58) (congrArg (Sign.withNegation globalNegation) hnode58) (Eq.refl Bool.true))
  let bounded60 := below_succ bounded59 (top_allows (Sign.withNegation globalNegation (assignment 59)))
  let bounded61 := below_succ bounded60 (domain_from_eq (domain := Cases.C018.initial 60) (congrArg (Sign.withNegation globalNegation) hnode60) (Eq.refl Bool.true))
  let bounded62 := below_succ bounded61 (domain_from_eq (domain := Cases.C018.initial 61) (congrArg (Sign.withNegation globalNegation) hnode61) (Eq.refl Bool.true))
  let bounded63 := below_succ bounded62 (domain_from_eq (domain := Cases.C018.initial 62) (congrArg (Sign.withNegation globalNegation) hnode62) (Eq.refl Bool.true))
  let bounded64 := below_succ bounded63 (top_allows (Sign.withNegation globalNegation (assignment 63)))
  let bounded65 := below_succ bounded64 (domain_from_eq (domain := Cases.C018.initial 64) (congrArg (Sign.withNegation globalNegation) hnode64) (Eq.refl Bool.true))
  let bounded66 := below_succ bounded65 (domain_from_eq (domain := Cases.C018.initial 65) (congrArg (Sign.withNegation globalNegation) hnode65) (Eq.refl Bool.true))
  let bounded67 := below_succ bounded66 (domain_from_eq (domain := Cases.C018.initial 66) (congrArg (Sign.withNegation globalNegation) hnode66) (Eq.refl Bool.true))
  let bounded68 := below_succ bounded67 (domain_from_eq (domain := Cases.C018.initial 67) (congrArg (Sign.withNegation globalNegation) (h_zero 2 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded69 := below_succ bounded68 (domain_from_eq (domain := Cases.C018.initial 68) (congrArg (Sign.withNegation globalNegation) hnode68) (Eq.refl Bool.true))
  let bounded70 := below_succ bounded69 (domain_from_eq (domain := Cases.C018.initial 69) (congrArg (Sign.withNegation globalNegation) hnode69) (Eq.refl Bool.true))
  let bounded71 := below_succ bounded70 (domain_from_eq (domain := Cases.C018.initial 70) (congrArg (Sign.withNegation globalNegation) hnode70) (Eq.refl Bool.true))
  let bounded72 := below_succ bounded71 (top_allows (Sign.withNegation globalNegation (assignment 71)))
  let bounded73 := below_succ bounded72 (domain_from_eq (domain := Cases.C018.initial 72) (congrArg (Sign.withNegation globalNegation) hnode72) (Eq.refl Bool.true))
  let bounded74 := below_succ bounded73 (domain_from_eq (domain := Cases.C018.initial 73) (congrArg (Sign.withNegation globalNegation) hnode73) (Eq.refl Bool.true))
  let bounded75 := below_succ bounded74 (domain_from_eq (domain := Cases.C018.initial 74) (congrArg (Sign.withNegation globalNegation) hnode74) (Eq.refl Bool.true))
  let bounded76 := below_succ bounded75 (top_allows (Sign.withNegation globalNegation (assignment 75)))
  let bounded77 := below_succ bounded76 (top_allows (Sign.withNegation globalNegation (assignment 76)))
  let bounded78 := below_succ bounded77 (domain_from_eq (domain := Cases.C018.initial 77) (congrArg (Sign.withNegation globalNegation) hnode77) (Eq.refl Bool.true))
  let bounded79 := below_succ bounded78 (domain_from_eq (domain := Cases.C018.initial 78) (congrArg (Sign.withNegation globalNegation) hnode78) (Eq.refl Bool.true))
  let bounded80 := below_succ bounded79 (domain_from_eq (domain := Cases.C018.initial 79) (congrArg (Sign.withNegation globalNegation) hnode79) (Eq.refl Bool.true))
  let bounded81 := below_succ bounded80 (top_allows (Sign.withNegation globalNegation (assignment 80)))
  let bounded82 := below_succ bounded81 (domain_from_eq (domain := Cases.C018.initial 81) (congrArg (Sign.withNegation globalNegation) hnode81) (Eq.refl Bool.true))
  let bounded83 := below_succ bounded82 (top_allows (Sign.withNegation globalNegation (assignment 82)))
  let bounded84 := below_succ bounded83 (domain_from_eq (domain := Cases.C018.initial 83) (congrArg (Sign.withNegation globalNegation) hnode83) (Eq.refl Bool.true))
  let bounded85 := below_succ bounded84 (domain_from_eq (domain := Cases.C018.initial 84) (congrArg (Sign.withNegation globalNegation) hnode84) (Eq.refl Bool.true))
  let bounded86 := below_succ bounded85 (top_allows (Sign.withNegation globalNegation (assignment 85)))
  let bounded87 := below_succ bounded86 (top_allows (Sign.withNegation globalNegation (assignment 86)))
  let bounded88 := below_succ bounded87 (top_allows (Sign.withNegation globalNegation (assignment 87)))
  let bounded89 := below_succ bounded88 (domain_from_eq (domain := Cases.C018.initial 88) (congrArg (Sign.withNegation globalNegation) hnode88) (Eq.refl Bool.true))
  let bounded90 := below_succ bounded89 (domain_from_eq (domain := Cases.C018.initial 89) (congrArg (Sign.withNegation globalNegation) hnode89) (Eq.refl Bool.true))
  let bounded91 := below_succ bounded90 (domain_from_eq (domain := Cases.C018.initial 90) (congrArg (Sign.withNegation globalNegation) hnode90) (Eq.refl Bool.true))
  let bounded92 := below_succ bounded91 (domain_from_eq (domain := Cases.C018.initial 91) (congrArg (Sign.withNegation globalNegation) hnode91) (Eq.refl Bool.true))
  let bounded93 := below_succ bounded92 (domain_from_eq (domain := Cases.C018.initial 92) (congrArg (Sign.withNegation globalNegation) hnode92) (Eq.refl Bool.true))
  let bounded94 := below_succ bounded93 (domain_from_eq (domain := Cases.C018.initial 93) (congrArg (Sign.withNegation globalNegation) hnode93) (Eq.refl Bool.true))
  let bounded95 := below_succ bounded94 (domain_from_eq (domain := Cases.C018.initial 94) (congrArg (Sign.withNegation globalNegation) hnode94) (Eq.refl Bool.true))
  let bounded96 := below_succ bounded95 (domain_from_eq (domain := Cases.C018.initial 95) (congrArg (Sign.withNegation globalNegation) hnode95) (Eq.refl Bool.true))
  let bounded97 := below_succ bounded96 (top_allows (Sign.withNegation globalNegation (assignment 96)))
  let bounded98 := below_succ bounded97 (domain_from_eq (domain := Cases.C018.initial 97) (congrArg (Sign.withNegation globalNegation) hnode97) (Eq.refl Bool.true))
  let bounded99 := below_succ bounded98 (domain_from_eq (domain := Cases.C018.initial 98) (congrArg (Sign.withNegation globalNegation) hnode98) (Eq.refl Bool.true))
  let bounded100 := below_succ bounded99 (domain_from_eq (domain := Cases.C018.initial 99) (congrArg (Sign.withNegation globalNegation) (h_zero 3 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded101 := below_succ bounded100 (domain_from_eq (domain := Cases.C018.initial 100) (congrArg (Sign.withNegation globalNegation) hnode100) (Eq.refl Bool.true))
  let bounded102 := below_succ bounded101 (domain_from_eq (domain := Cases.C018.initial 101) (congrArg (Sign.withNegation globalNegation) (h_zero 4 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded103 := below_succ bounded102 (domain_from_eq (domain := Cases.C018.initial 102) (congrArg (Sign.withNegation globalNegation) hnode102) (Eq.refl Bool.true))
  let bounded104 := below_succ bounded103 (domain_from_eq (domain := Cases.C018.initial 103) (congrArg (Sign.withNegation globalNegation) hnode103) (Eq.refl Bool.true))
  let bounded105 := below_succ bounded104 (domain_from_eq (domain := Cases.C018.initial 104) (congrArg (Sign.withNegation globalNegation) hnode104) (Eq.refl Bool.true))
  let bounded106 := below_succ bounded105 (domain_from_eq (domain := Cases.C018.initial 105) (congrArg (Sign.withNegation globalNegation) hnode105) (Eq.refl Bool.true))
  let bounded107 := below_succ bounded106 (top_allows (Sign.withNegation globalNegation (assignment 106)))
  let bounded108 := below_succ bounded107 (domain_from_eq (domain := Cases.C018.initial 107) (congrArg (Sign.withNegation globalNegation) hnode107) (Eq.refl Bool.true))
  let bounded109 := below_succ bounded108 (domain_from_eq (domain := Cases.C018.initial 108) (congrArg (Sign.withNegation globalNegation) hnode108) (Eq.refl Bool.true))
  let bounded110 := below_succ bounded109 (domain_from_eq (domain := Cases.C018.initial 109) (congrArg (Sign.withNegation globalNegation) hnode109) (Eq.refl Bool.true))
  let bounded111 := below_succ bounded110 (domain_from_eq (domain := Cases.C018.initial 110) (congrArg (Sign.withNegation globalNegation) hnode110) (Eq.refl Bool.true))
  let bounded112 := below_succ bounded111 (domain_from_eq (domain := Cases.C018.initial 111) (congrArg (Sign.withNegation globalNegation) hnode111) (Eq.refl Bool.true))
  let bounded113 := below_succ bounded112 (domain_from_eq (domain := Cases.C018.initial 112) (congrArg (Sign.withNegation globalNegation) hnode112) (Eq.refl Bool.true))
  let bounded114 := below_succ bounded113 (domain_from_eq (domain := Cases.C018.initial 113) (congrArg (Sign.withNegation globalNegation) hnode113) (Eq.refl Bool.true))
  let bounded115 := below_succ bounded114 (domain_from_eq (domain := Cases.C018.initial 114) (congrArg (Sign.withNegation globalNegation) (h_zero 5 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded116 := below_succ bounded115 (domain_from_eq (domain := Cases.C018.initial 115) (congrArg (Sign.withNegation globalNegation) hnode115) (Eq.refl Bool.true))
  let bounded117 := below_succ bounded116 (domain_from_eq (domain := Cases.C018.initial 116) (congrArg (Sign.withNegation globalNegation) hnode116) (Eq.refl Bool.true))
  let bounded118 := below_succ bounded117 (domain_from_eq (domain := Cases.C018.initial 117) (congrArg (Sign.withNegation globalNegation) hnode117) (Eq.refl Bool.true))
  let bounded119 := below_succ bounded118 (domain_from_eq (domain := Cases.C018.initial 118) (congrArg (Sign.withNegation globalNegation) hnode118) (Eq.refl Bool.true))
  let bounded120 := below_succ bounded119 (top_allows (Sign.withNegation globalNegation (assignment 119)))
  let bounded121 := below_succ bounded120 (domain_from_eq (domain := Cases.C018.initial 120) (congrArg (Sign.withNegation globalNegation) hnode120) (Eq.refl Bool.true))
  let bounded122 := below_succ bounded121 (domain_from_eq (domain := Cases.C018.initial 121) (congrArg (Sign.withNegation globalNegation) hnode121) (Eq.refl Bool.true))
  let bounded123 := below_succ bounded122 (domain_from_eq (domain := Cases.C018.initial 122) (congrArg (Sign.withNegation globalNegation) hnode122) (Eq.refl Bool.true))
  let bounded124 := below_succ bounded123 (domain_from_eq (domain := Cases.C018.initial 123) (congrArg (Sign.withNegation globalNegation) hnode123) (Eq.refl Bool.true))
  let bounded125 := below_succ bounded124 (domain_from_eq (domain := Cases.C018.initial 124) (congrArg (Sign.withNegation globalNegation) hnode124) (Eq.refl Bool.true))
  let bounded126 := below_succ bounded125 (top_allows (Sign.withNegation globalNegation (assignment 125)))
  let bounded127 := below_succ bounded126 (top_allows (Sign.withNegation globalNegation (assignment 126)))
  let bounded128 := below_succ bounded127 (domain_from_eq (domain := Cases.C018.initial 127) (congrArg (Sign.withNegation globalNegation) hnode127) (Eq.refl Bool.true))
  let bounded129 := below_succ bounded128 (domain_from_eq (domain := Cases.C018.initial 128) (congrArg (Sign.withNegation globalNegation) (h_zero 6 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded130 := below_succ bounded129 (domain_from_eq (domain := Cases.C018.initial 129) (congrArg (Sign.withNegation globalNegation) hnode129) (Eq.refl Bool.true))
  let bounded131 := below_succ bounded130 (domain_from_eq (domain := Cases.C018.initial 130) (congrArg (Sign.withNegation globalNegation) hnode130) (Eq.refl Bool.true))
  let bounded132 := below_succ bounded131 (domain_from_eq (domain := Cases.C018.initial 131) (congrArg (Sign.withNegation globalNegation) hnode131) (Eq.refl Bool.true))
  let bounded133 := below_succ bounded132 (top_allows (Sign.withNegation globalNegation (assignment 132)))
  let bounded134 := below_succ bounded133 (domain_from_eq (domain := Cases.C018.initial 133) (congrArg (Sign.withNegation globalNegation) hnode133) (Eq.refl Bool.true))
  let bounded135 := below_succ bounded134 (domain_from_eq (domain := Cases.C018.initial 134) (congrArg (Sign.withNegation globalNegation) hnode134) (Eq.refl Bool.true))
  let bounded136 := below_succ bounded135 (domain_from_eq (domain := Cases.C018.initial 135) (congrArg (Sign.withNegation globalNegation) hnode135) (Eq.refl Bool.true))
  let bounded137 := below_succ bounded136 (domain_from_eq (domain := Cases.C018.initial 136) (congrArg (Sign.withNegation globalNegation) (h_zero 7 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded138 := below_succ bounded137 (domain_from_eq (domain := Cases.C018.initial 137) (congrArg (Sign.withNegation globalNegation) hnode137) (Eq.refl Bool.true))
  let bounded139 := below_succ bounded138 (domain_from_eq (domain := Cases.C018.initial 138) (congrArg (Sign.withNegation globalNegation) hnode138) (Eq.refl Bool.true))
  let bounded140 := below_succ bounded139 (domain_from_eq (domain := Cases.C018.initial 139) (congrArg (Sign.withNegation globalNegation) hnode139) (Eq.refl Bool.true))
  let bounded141 := below_succ bounded140 (domain_from_eq (domain := Cases.C018.initial 140) (congrArg (Sign.withNegation globalNegation) hnode140) (Eq.refl Bool.true))
  let bounded142 := below_succ bounded141 (domain_from_eq (domain := Cases.C018.initial 141) (congrArg (Sign.withNegation globalNegation) hnode141) (Eq.refl Bool.true))
  let bounded143 := below_succ bounded142 (domain_from_eq (domain := Cases.C018.initial 142) (congrArg (Sign.withNegation globalNegation) (h_zero 8 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded144 := below_succ bounded143 (domain_from_eq (domain := Cases.C018.initial 143) (congrArg (Sign.withNegation globalNegation) hnode143) (Eq.refl Bool.true))
  let bounded145 := below_succ bounded144 (domain_from_eq (domain := Cases.C018.initial 144) (congrArg (Sign.withNegation globalNegation) hnode144) (Eq.refl Bool.true))
  let bounded146 := below_succ bounded145 (domain_from_eq (domain := Cases.C018.initial 145) (congrArg (Sign.withNegation globalNegation) (h_zero 9 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded147 := below_succ bounded146 (domain_from_eq (domain := Cases.C018.initial 146) (congrArg (Sign.withNegation globalNegation) hnode146) (Eq.refl Bool.true))
  let bounded148 := below_succ bounded147 (domain_from_eq (domain := Cases.C018.initial 147) (congrArg (Sign.withNegation globalNegation) hnode147) (Eq.refl Bool.true))
  let bounded149 := below_succ bounded148 (domain_from_eq (domain := Cases.C018.initial 148) (congrArg (Sign.withNegation globalNegation) (h_zero 10 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded150 := below_succ bounded149 (domain_from_eq (domain := Cases.C018.initial 149) (congrArg (Sign.withNegation globalNegation) (h_zero 11 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded151 := below_succ bounded150 (domain_from_eq (domain := Cases.C018.initial 150) (congrArg (Sign.withNegation globalNegation) hnode150) (Eq.refl Bool.true))
  let bounded152 := below_succ bounded151 (domain_from_eq (domain := Cases.C018.initial 151) (congrArg (Sign.withNegation globalNegation) hnode151) (Eq.refl Bool.true))
  let bounded153 := below_succ bounded152 (domain_from_eq (domain := Cases.C018.initial 152) (congrArg (Sign.withNegation globalNegation) hnode152) (Eq.refl Bool.true))
  let bounded154 := below_succ bounded153 (domain_from_eq (domain := Cases.C018.initial 153) (congrArg (Sign.withNegation globalNegation) (h_zero 12 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded155 := below_succ bounded154 (domain_from_eq (domain := Cases.C018.initial 154) (congrArg (Sign.withNegation globalNegation) hnode154) (Eq.refl Bool.true))
  let bounded156 := below_succ bounded155 (domain_from_eq (domain := Cases.C018.initial 155) (congrArg (Sign.withNegation globalNegation) hnode155) (Eq.refl Bool.true))
  let bounded157 := below_succ bounded156 (domain_from_eq (domain := Cases.C018.initial 156) (congrArg (Sign.withNegation globalNegation) hnode156) (Eq.refl Bool.true))
  let bounded158 := below_succ bounded157 (domain_from_eq (domain := Cases.C018.initial 157) (congrArg (Sign.withNegation globalNegation) hnode157) (Eq.refl Bool.true))
  let bounded159 := below_succ bounded158 (domain_from_eq (domain := Cases.C018.initial 158) (congrArg (Sign.withNegation globalNegation) hnode158) (Eq.refl Bool.true))
  let bounded160 := below_succ bounded159 (domain_from_eq (domain := Cases.C018.initial 159) (congrArg (Sign.withNegation globalNegation) hnode159) (Eq.refl Bool.true))
  let bounded161 := below_succ bounded160 (domain_from_eq (domain := Cases.C018.initial 160) (congrArg (Sign.withNegation globalNegation) hnode160) (Eq.refl Bool.true))
  let bounded162 := below_succ bounded161 (domain_from_eq (domain := Cases.C018.initial 161) (congrArg (Sign.withNegation globalNegation) hnode161) (Eq.refl Bool.true))
  let bounded163 := below_succ bounded162 (top_allows (Sign.withNegation globalNegation (assignment 162)))
  let bounded164 := below_succ bounded163 (domain_from_eq (domain := Cases.C018.initial 163) (congrArg (Sign.withNegation globalNegation) hnode163) (Eq.refl Bool.true))
  let bounded165 := below_succ bounded164 (domain_from_eq (domain := Cases.C018.initial 164) (congrArg (Sign.withNegation globalNegation) hnode164) (Eq.refl Bool.true))
  let bounded166 := below_succ bounded165 (top_allows (Sign.withNegation globalNegation (assignment 165)))
  let bounded167 := below_succ bounded166 (domain_from_eq (domain := Cases.C018.initial 166) (congrArg (Sign.withNegation globalNegation) hnode166) (Eq.refl Bool.true))
  let bounded168 := below_succ bounded167 (top_allows (Sign.withNegation globalNegation (assignment 167)))
  let bounded169 := below_succ bounded168 (domain_from_eq (domain := Cases.C018.initial 168) (congrArg (Sign.withNegation globalNegation) hnode168) (Eq.refl Bool.true))
  let bounded170 := below_succ bounded169 (domain_from_eq (domain := Cases.C018.initial 169) (congrArg (Sign.withNegation globalNegation) hnode169) (Eq.refl Bool.true))
  let bounded171 := below_succ bounded170 (top_allows (Sign.withNegation globalNegation (assignment 170)))
  let bounded172 := below_succ bounded171 (domain_from_eq (domain := Cases.C018.initial 171) (congrArg (Sign.withNegation globalNegation) (h_zero 13 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded173 := below_succ bounded172 (domain_from_eq (domain := Cases.C018.initial 172) (congrArg (Sign.withNegation globalNegation) hnode172) (Eq.refl Bool.true))
  let bounded174 := below_succ bounded173 (domain_from_eq (domain := Cases.C018.initial 173) (congrArg (Sign.withNegation globalNegation) hnode173) (Eq.refl Bool.true))
  let bounded175 := below_succ bounded174 (domain_from_eq (domain := Cases.C018.initial 174) (congrArg (Sign.withNegation globalNegation) hnode174) (Eq.refl Bool.true))
  let bounded176 := below_succ bounded175 (top_allows (Sign.withNegation globalNegation (assignment 175)))
  let bounded177 := below_succ bounded176 (top_allows (Sign.withNegation globalNegation (assignment 176)))
  let bounded178 := below_succ bounded177 (domain_from_eq (domain := Cases.C018.initial 177) (congrArg (Sign.withNegation globalNegation) hnode177) (Eq.refl Bool.true))
  let bounded179 := below_succ bounded178 (top_allows (Sign.withNegation globalNegation (assignment 178)))
  let bounded180 := below_succ bounded179 (domain_from_eq (domain := Cases.C018.initial 179) (congrArg (Sign.withNegation globalNegation) hnode179) (Eq.refl Bool.true))
  let bounded181 := below_succ bounded180 (domain_from_eq (domain := Cases.C018.initial 180) (congrArg (Sign.withNegation globalNegation) hnode180) (Eq.refl Bool.true))
  let bounded182 := below_succ bounded181 (domain_from_eq (domain := Cases.C018.initial 181) (congrArg (Sign.withNegation globalNegation) hnode181) (Eq.refl Bool.true))
  let bounded183 := below_succ bounded182 (domain_from_eq (domain := Cases.C018.initial 182) (congrArg (Sign.withNegation globalNegation) (h_zero 14 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded184 := below_succ bounded183 (domain_from_eq (domain := Cases.C018.initial 183) (congrArg (Sign.withNegation globalNegation) hnode183) (Eq.refl Bool.true))
  let bounded185 := below_succ bounded184 (domain_from_eq (domain := Cases.C018.initial 184) (congrArg (Sign.withNegation globalNegation) hnode184) (Eq.refl Bool.true))
  let bounded186 := below_succ bounded185 (domain_from_eq (domain := Cases.C018.initial 185) (congrArg (Sign.withNegation globalNegation) hnode185) (Eq.refl Bool.true))
  let bounded187 := below_succ bounded186 (domain_from_eq (domain := Cases.C018.initial 186) (congrArg (Sign.withNegation globalNegation) hnode186) (Eq.refl Bool.true))
  let bounded188 := below_succ bounded187 (domain_from_eq (domain := Cases.C018.initial 187) (congrArg (Sign.withNegation globalNegation) hnode187) (Eq.refl Bool.true))
  let bounded189 := below_succ bounded188 (domain_from_eq (domain := Cases.C018.initial 188) (congrArg (Sign.withNegation globalNegation) hnode188) (Eq.refl Bool.true))
  let bounded190 := below_succ bounded189 (domain_from_eq (domain := Cases.C018.initial 189) (congrArg (Sign.withNegation globalNegation) hnode189) (Eq.refl Bool.true))
  let bounded191 := below_succ bounded190 (domain_from_eq (domain := Cases.C018.initial 190) (congrArg (Sign.withNegation globalNegation) hnode190) (Eq.refl Bool.true))
  let bounded192 := below_succ bounded191 (domain_from_eq (domain := Cases.C018.initial 191) (congrArg (Sign.withNegation globalNegation) hnode191) (Eq.refl Bool.true))
  let bounded193 := below_succ bounded192 (domain_from_eq (domain := Cases.C018.initial 192) (congrArg (Sign.withNegation globalNegation) hnode192) (Eq.refl Bool.true))
  let bounded194 := below_succ bounded193 (domain_from_eq (domain := Cases.C018.initial 193) (congrArg (Sign.withNegation globalNegation) hnode193) (Eq.refl Bool.true))
  let bounded195 := below_succ bounded194 (top_allows (Sign.withNegation globalNegation (assignment 194)))
  let bounded196 := below_succ bounded195 (top_allows (Sign.withNegation globalNegation (assignment 195)))
  let bounded197 := below_succ bounded196 (top_allows (Sign.withNegation globalNegation (assignment 196)))
  let bounded198 := below_succ bounded197 (top_allows (Sign.withNegation globalNegation (assignment 197)))
  let bounded199 := below_succ bounded198 (top_allows (Sign.withNegation globalNegation (assignment 198)))
  let bounded200 := below_succ bounded199 (top_allows (Sign.withNegation globalNegation (assignment 199)))
  let bounded201 := below_succ bounded200 (top_allows (Sign.withNegation globalNegation (assignment 200)))
  let bounded202 := below_succ bounded201 (domain_from_eq (domain := Cases.C018.initial 201) (congrArg (Sign.withNegation globalNegation) hnode201) (Eq.refl Bool.true))
  let bounded203 := below_succ bounded202 (domain_from_eq (domain := Cases.C018.initial 202) (congrArg (Sign.withNegation globalNegation) hnode202) (Eq.refl Bool.true))
  let bounded204 := below_succ bounded203 (domain_from_eq (domain := Cases.C018.initial 203) (congrArg (Sign.withNegation globalNegation) hnode203) (Eq.refl Bool.true))
  let bounded205 := below_succ bounded204 (domain_from_eq (domain := Cases.C018.initial 204) (congrArg (Sign.withNegation globalNegation) hnode204) (Eq.refl Bool.true))
  let bounded206 := below_succ bounded205 (domain_from_eq (domain := Cases.C018.initial 205) (congrArg (Sign.withNegation globalNegation) hnode205) (Eq.refl Bool.true))
  let bounded207 := below_succ bounded206 (domain_from_eq (domain := Cases.C018.initial 206) (congrArg (Sign.withNegation globalNegation) (h_zero 15 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded208 := below_succ bounded207 (domain_from_eq (domain := Cases.C018.initial 207) (congrArg (Sign.withNegation globalNegation) hnode207) (Eq.refl Bool.true))
  let bounded209 := below_succ bounded208 (domain_from_eq (domain := Cases.C018.initial 208) (congrArg (Sign.withNegation globalNegation) hnode208) (Eq.refl Bool.true))
  let bounded210 := below_succ bounded209 (domain_from_eq (domain := Cases.C018.initial 209) (congrArg (Sign.withNegation globalNegation) hnode209) (Eq.refl Bool.true))
  let bounded211 := below_succ bounded210 (domain_from_eq (domain := Cases.C018.initial 210) (congrArg (Sign.withNegation globalNegation) hnode210) (Eq.refl Bool.true))
  let bounded212 := below_succ bounded211 (domain_from_eq (domain := Cases.C018.initial 211) (congrArg (Sign.withNegation globalNegation) hnode211) (Eq.refl Bool.true))
  let bounded213 := below_succ bounded212 (domain_from_eq (domain := Cases.C018.initial 212) (congrArg (Sign.withNegation globalNegation) hnode212) (Eq.refl Bool.true))
  let bounded214 := below_succ bounded213 (domain_from_eq (domain := Cases.C018.initial 213) (congrArg (Sign.withNegation globalNegation) hnode213) (Eq.refl Bool.true))
  let bounded215 := below_succ bounded214 (domain_from_eq (domain := Cases.C018.initial 214) (congrArg (Sign.withNegation globalNegation) hnode214) (Eq.refl Bool.true))
  let bounded216 := below_succ bounded215 (domain_from_eq (domain := Cases.C018.initial 215) (congrArg (Sign.withNegation globalNegation) (h_zero 16 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded217 := below_succ bounded216 (top_allows (Sign.withNegation globalNegation (assignment 216)))
  let bounded218 := below_succ bounded217 (domain_from_eq (domain := Cases.C018.initial 217) (congrArg (Sign.withNegation globalNegation) hnode217) (Eq.refl Bool.true))
  let bounded219 := below_succ bounded218 (domain_from_eq (domain := Cases.C018.initial 218) (congrArg (Sign.withNegation globalNegation) hnode218) (Eq.refl Bool.true))
  let bounded220 := below_succ bounded219 (domain_from_eq (domain := Cases.C018.initial 219) (congrArg (Sign.withNegation globalNegation) hnode219) (Eq.refl Bool.true))
  let bounded221 := below_succ bounded220 (domain_from_eq (domain := Cases.C018.initial 220) (congrArg (Sign.withNegation globalNegation) hnode220) (Eq.refl Bool.true))
  let bounded222 := below_succ bounded221 (top_allows (Sign.withNegation globalNegation (assignment 221)))
  let bounded223 := below_succ bounded222 (domain_from_eq (domain := Cases.C018.initial 222) (congrArg (Sign.withNegation globalNegation) hnode222) (Eq.refl Bool.true))
  let bounded224 := below_succ bounded223 (domain_from_eq (domain := Cases.C018.initial 223) (congrArg (Sign.withNegation globalNegation) hnode223) (Eq.refl Bool.true))
  let bounded225 := below_succ bounded224 (top_allows (Sign.withNegation globalNegation (assignment 224)))
  let bounded226 := below_succ bounded225 (domain_from_eq (domain := Cases.C018.initial 225) (congrArg (Sign.withNegation globalNegation) hnode225) (Eq.refl Bool.true))
  let bounded227 := below_succ bounded226 (domain_from_eq (domain := Cases.C018.initial 226) (congrArg (Sign.withNegation globalNegation) hnode226) (Eq.refl Bool.true))
  let bounded228 := below_succ bounded227 (domain_from_eq (domain := Cases.C018.initial 227) (congrArg (Sign.withNegation globalNegation) hnode227) (Eq.refl Bool.true))
  let bounded229 := below_succ bounded228 (domain_from_eq (domain := Cases.C018.initial 228) (congrArg (Sign.withNegation globalNegation) hnode228) (Eq.refl Bool.true))
  let bounded230 := below_succ bounded229 (domain_from_eq (domain := Cases.C018.initial 229) (congrArg (Sign.withNegation globalNegation) hnode229) (Eq.refl Bool.true))
  let bounded231 := below_succ bounded230 (domain_from_eq (domain := Cases.C018.initial 230) (congrArg (Sign.withNegation globalNegation) hnode230) (Eq.refl Bool.true))
  let bounded232 := below_succ bounded231 (domain_from_eq (domain := Cases.C018.initial 231) (congrArg (Sign.withNegation globalNegation) (h_zero 17 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded233 := below_succ bounded232 (domain_from_eq (domain := Cases.C018.initial 232) (congrArg (Sign.withNegation globalNegation) hnode232) (Eq.refl Bool.true))
  let bounded234 := below_succ bounded233 (top_allows (Sign.withNegation globalNegation (assignment 233)))
  let bounded235 := below_succ bounded234 (domain_from_eq (domain := Cases.C018.initial 234) (congrArg (Sign.withNegation globalNegation) hnode234) (Eq.refl Bool.true))
  let bounded236 := below_succ bounded235 (domain_from_eq (domain := Cases.C018.initial 235) (congrArg (Sign.withNegation globalNegation) hnode235) (Eq.refl Bool.true))
  let bounded237 := below_succ bounded236 (top_allows (Sign.withNegation globalNegation (assignment 236)))
  let bounded238 := below_succ bounded237 (domain_from_eq (domain := Cases.C018.initial 237) (congrArg (Sign.withNegation globalNegation) hnode237) (Eq.refl Bool.true))
  let bounded239 := below_succ bounded238 (domain_from_eq (domain := Cases.C018.initial 238) (congrArg (Sign.withNegation globalNegation) hnode238) (Eq.refl Bool.true))
  let bounded240 := below_succ bounded239 (top_allows (Sign.withNegation globalNegation (assignment 239)))
  let bounded241 := below_succ bounded240 (domain_from_eq (domain := Cases.C018.initial 240) (congrArg (Sign.withNegation globalNegation) hnode240) (Eq.refl Bool.true))
  let bounded242 := below_succ bounded241 (domain_from_eq (domain := Cases.C018.initial 241) (congrArg (Sign.withNegation globalNegation) (h_zero 18 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded243 := below_succ bounded242 (domain_from_eq (domain := Cases.C018.initial 242) (congrArg (Sign.withNegation globalNegation) (h_zero 19 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded244 := below_succ bounded243 (domain_from_eq (domain := Cases.C018.initial 243) (congrArg (Sign.withNegation globalNegation) hnode243) (Eq.refl Bool.true))
  let bounded245 := below_succ bounded244 (domain_from_eq (domain := Cases.C018.initial 244) (congrArg (Sign.withNegation globalNegation) hnode244) (Eq.refl Bool.true))
  let bounded246 := below_succ bounded245 (domain_from_eq (domain := Cases.C018.initial 245) (congrArg (Sign.withNegation globalNegation) hnode245) (Eq.refl Bool.true))
  let bounded247 := below_succ bounded246 (domain_from_eq (domain := Cases.C018.initial 246) (congrArg (Sign.withNegation globalNegation) hnode246) (Eq.refl Bool.true))
  let bounded248 := below_succ bounded247 (top_allows (Sign.withNegation globalNegation (assignment 247)))
  let bounded249 := below_succ bounded248 (domain_from_eq (domain := Cases.C018.initial 248) (congrArg (Sign.withNegation globalNegation) hnode248) (Eq.refl Bool.true))
  let bounded250 := below_succ bounded249 (domain_from_eq (domain := Cases.C018.initial 249) (congrArg (Sign.withNegation globalNegation) hnode249) (Eq.refl Bool.true))
  let bounded251 := below_succ bounded250 (top_allows (Sign.withNegation globalNegation (assignment 250)))
  let bounded252 := below_succ bounded251 (domain_from_eq (domain := Cases.C018.initial 251) (congrArg (Sign.withNegation globalNegation) hnode251) (Eq.refl Bool.true))
  bounded252

theorem support_sign_contradiction (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment)
    (h_gp : Data.ValidUsedRelations assignment) : False :=
  Cases.C018.abstract_sign_contradiction
    (fun index => Sign.withNegation globalNegation (assignment index))
    (initial_domains_sound assignment h_anchor h_support h_zero)
    (Data.ValidUsedRelations.with_global_negation h_gp globalNegation)
end Papers.RationalityTen.PureGP.Initializers.C018
#print axioms Papers.RationalityTen.PureGP.Initializers.C018.support_sign_contradiction
