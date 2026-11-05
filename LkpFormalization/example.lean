import LkpFormalization.Tactic

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

def prt_tree (t : BNTree Sequent) : IO Unit := do
  println! (toTypst t)

#eval prt_tree t₃
