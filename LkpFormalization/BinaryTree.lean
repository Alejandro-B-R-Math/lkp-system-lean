import TypstInfoview

namespace LkpFormalization

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

def BNTree.toTypstAux [ToTypst α] : BNTree α → String
  | .leaf => ""
  | .node l v r =>
    let ltyp := match l with
      | leaf => ""
      | _     => s!"  {BNTree.toTypstAux l},\n"

    let rtyp := match r with
      | leaf => ""
      | _     => s!"  {BNTree.toTypstAux r},\n"

    if ltyp == "" && rtyp == "" then
      s!"{toTypst v}"
    else
      s!"rule(\n{ltyp}{rtyp}  {toTypst v}\n)"

instance [ToTypst α] : ToTypst (BNTree α) where
  toTypst := fun t => "prooftree(\n  " ++ (BNTree.toTypstAux t) ++ "\n)"

end BNTree

end LkpFormalization
