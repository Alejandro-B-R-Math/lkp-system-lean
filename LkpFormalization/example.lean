import LkpFormalization.Tactic
import LkpFormalization.Rules
import TypstInfoview

open LkpFormalization

def t₂ : BNTree Sequent :=
    lk_derive (["B", "A"], ["A"]) by
  apply_rule (weakening_left "B") (["A"], ["A"])
  left
  apply_rule (ax "A")

def t₃ : BNTree Sequent :=
  lk_derive (["A"], ["A"]) by
    apply_rule cut (["A"], ["A"]) (["A"], ["A"])
    left
    apply_rule (ax "A")
    next
    apply_rule (ax "A")

def t₄ : BNTree Sequent :=
  lk_derive (["A"], ["A" ∨ₚ "B"]) by
    apply_rule (dis_right_1 "B") (["A"], ["A"])
    left
    apply_rule (ax "A")

def t₅ : BNTree Sequent :=
  lk_derive (["B"], ["A" ∨ₚ "B"]) by
    apply_rule (dis_right_2 "A") (["B"], ["B"])
    left
    apply_rule (ax "B")

set_option typst.preamble "#import \"@preview/curryst:0.6.0\": rule, prooftree, rule-set" in
#typst t₃
