import LkpFormalization.BinaryTree

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

end PropForm

def Sequent := (List PropForm) × (List PropForm)

def Sequent.antecedent (s : Sequent) : List PropForm := s.1
def Sequent.succedent (s : Sequent) : List PropForm := s.2


section LKPRules

open BNTree

def weakening_left (A : PropForm) : BNTree Sequent → Option (BNTree Sequent)
  | T@(node _ (Γ, Δ) _) => T.insert_right (A :: Γ, Δ)
  | _ => none

def weakening_right (A : PropForm) : BNTree Sequent → Option (BNTree Sequent)
  | T@(node _ (Γ, Δ) _) => T.insert_right (Γ, Δ ++ [A])
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

end LKPRules
