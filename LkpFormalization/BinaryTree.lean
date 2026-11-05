import LkpFormalization.Typst

inductive BNTree (α : Type u) where
  | leaf
  | node (left : BNTree α) (value : α) (right : BNTree α)
  deriving Repr, DecidableEq, Inhabited


namespace BNTree

variable {α}

instance : Coe α (BNTree α) := ⟨fun v => node leaf v leaf⟩

def insert_right (T : BNTree α) (value : α) : BNTree α :=
  node leaf value T

def insert_left (T : BNTree α) (value : α) : BNTree α :=
  node T value leaf

def BNTree.toTypstAux [ToTypst α] [DecidableEq α] : BNTree α → String
  | .leaf => ""
  | .node l v r =>
    let ltyp := if l = .leaf then "" else s!"  {BNTree.toTypstAux l},\n"
    let rtyp := if r = .leaf then "" else s!"  {BNTree.toTypstAux r},\n"
    if ltyp = "" ∧ rtyp = "" then
      s!"{toTypst v}"
    else
      s!"rule(\n{ltyp}{rtyp}  {toTypst v}\n)"

instance [ToTypst α] [DecidableEq α] : ToTypst (BNTree α) where
  toTypst := BNTree.toTypstAux

end BNTree
