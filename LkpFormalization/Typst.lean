class ToTypst (α : Type u) where
  toTypst : α → String

export ToTypst (toTypst)

def List.toTypstAux [ToTypst α] : List α → String
  | [] => ""
  | a::[] => (toTypst a)
  | x::xs => s!"{toTypst x}, {xs.toTypstAux}"

instance [ToTypst α] : ToTypst (List α) where
  toTypst := List.toTypstAux

instance : ToTypst Nat where
  toTypst n := s!"${n}$"
