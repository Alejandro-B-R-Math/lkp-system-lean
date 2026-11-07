import LkpFormalization.Tactic
import TypstInfoview


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

set_option typst.preamble "#import \"@preview/curryst:0.6.0\": rule, prooftree, rule-set" in
#typst t₃
