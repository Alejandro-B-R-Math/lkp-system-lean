import LkpFormalization.BinaryTree
import TypstInfoview

inductive PropForm
  | var   : String → PropForm
  | tr    : PropForm
  | fls   : PropForm
  | neg   : PropForm → PropForm
  | conj  : PropForm → PropForm → PropForm
  | disj  : PropForm → PropForm → PropForm
  | impl  : PropForm → PropForm → PropForm
  | equiv  : PropForm → PropForm → PropForm
  deriving Repr, DecidableEq, Inhabited

namespace PropForm

notation:max "⊤ₚ" => PropForm.tr
notation:max "⊥ₚ" => PropForm.fls
prefix:90 "¬ₚ "   => PropForm.neg
infixr:70 " ∧ₚ "  => PropForm.conj
infixr:65 " ∨ₚ "  => PropForm.disj
infixr:55 " ⊃ₚ "  => PropForm.impl
infixr:50 " ≡ₚ "  => PropForm.equiv

private def toString : PropForm → String
  | var s     => s
  | tr        => "⊤"
  | fls       => "⊥"
  | neg p     => "(¬ " ++ toString p ++ ")"
  | conj p q  => "(" ++ toString p ++ " ∧ " ++ toString q ++ ")"
  | disj p q  => "(" ++ toString p ++ " ∨ " ++ toString q ++ ")"
  | impl p q  => "(" ++ toString p ++ " ⊃ " ++ toString q ++ ")"
  | equiv p q => "(" ++ toString p ++ " ≡ " ++ toString q ++ ")"

instance : ToString PropForm := ⟨PropForm.toString⟩

instance : Coe String PropForm := ⟨fun s => var s⟩

instance : Repr PropForm where
  reprPrec A _ := A.toString.toFormat

def toTypstAux : PropForm → String
  | var x => x
  | tr => "top"
  | fls => "bot"
  | neg f => s!"not {f.toTypstAux}"
  | conj f₁ f₂ => s!"({f₁.toTypstAux} and {f₂.toTypstAux})"
  | disj f₁ f₂ => s!"({f₁.toTypstAux} or {f₂.toTypstAux})"
  | impl f₁ f₂ => s!"({f₁.toTypstAux} supset {f₂.toTypstAux})"
  | equiv f₁ f₂ => s!"({f₁.toTypstAux} equiv {f₂.toTypstAux})"

instance : ToTypst PropForm where
  toTypst := PropForm.toTypstAux

end PropForm

def Sequent := (List PropForm) × (List PropForm)

instance : ToTypst Sequent where
  toTypst s := (toTypst s.1) ++ " -> " ++ (toTypst s.2)

def Sequent.antecedent (s : Sequent) : List PropForm := s.1
def Sequent.succedent (s : Sequent) : List PropForm := s.2

section LKPRules

open BNTree

def ax (A : PropForm) : Option (BNTree Sequent) := some (BNTree.node .leaf ([A], [A]) .leaf)

def weakening_left (A : PropForm) : BNTree Sequent → Option (BNTree Sequent)
  | T@(node _ (Γ, Δ) _) => node T (A :: Γ, Δ) leaf
  | _ => none

def weakening_right (A : PropForm) : BNTree Sequent → Option (BNTree Sequent)
  | T@(node _ (Γ, Δ) _) => node T (Γ, Δ ++ [A]) leaf
  | _ => none

def exchange_left (i : Nat) : BNTree Sequent → Option (BNTree Sequent)
  | T@(node _ (Γ, Δ) _) =>
    match Γ.splitAt i with
    | (Γ₁, A :: B :: Γ₂) =>
      node T (Γ₁ ++ (B :: A :: Γ₂), Δ) leaf
    | _ => none
  | _ => none

def exchange_right (i : Nat) : BNTree Sequent → Option (BNTree Sequent)
  | T@(node _ (Γ, Δ) _) =>
    match Δ.splitAt i with
    | (Δ₁, A :: B :: Δ₂) =>
      node T (Γ, Δ₁ ++ (B :: A :: Δ₂)) leaf
    | _ => none
  | _ => none

def cut : BNTree Sequent → BNTree Sequent → Option (BNTree Sequent)
  | T₁@(node _ (Γ, Δ) _), T₂@(node _ (A :: Λ, Θ) _) =>
    match Δ.reverse with
      | []    => none
      | B::Δ' =>
        if B = A then
          node T₁ (Γ ++ Λ, Δ'.reverse ++ Θ) T₂
        else
          none
  | _, _ => none

def neg_left : BNTree Sequent → Option (BNTree Sequent)
  | T@(node _ (Γ, Δ) _) =>
    match Δ.reverse with
    | [] => none
    | A :: Δ' =>
      node T (¬ₚ A :: Γ, Δ'.reverse) leaf
  | _ => none

def neg_right : BNTree Sequent → Option (BNTree Sequent)
  | T@(node _ (A :: Γ, Δ) _) =>
    node T (Γ, Δ ++ [¬ₚ A]) leaf
  | _ => none

def dis_left : BNTree Sequent → BNTree Sequent → Option (BNTree Sequent)
  | T₁@(node _ (A::Γ, Δ) _), T₂@(node _ (B::Γ', Δ') _) =>
    if Γ = Γ' ∧ Δ = Δ' then
      node T₁ ((A ∨ₚ B)::Γ, Δ) T₂
    else
      none
  | _, _ => none

end LKPRules
