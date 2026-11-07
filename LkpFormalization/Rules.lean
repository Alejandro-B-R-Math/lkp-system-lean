import LkpFormalization.Basic
import LkpFormalization.BinaryTree

namespace LkpFormalization

open BNTree

def ax (A : PropForm) : Option (BNTree Sequent) :=
  some (BNTree.node .leaf ([A], [A]) .leaf)

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

def dis_right_1 (B : PropForm) : BNTree Sequent → Option (BNTree Sequent)
  | T@(node _ (Γ, Δ) _) =>
    match Δ.reverse with
    | [] => none
    | A :: Δ' =>
      node T (Γ, Δ'.reverse ++ [A ∨ₚ B]) leaf
  | _ => none

def dis_right_2 (A : PropForm) : BNTree Sequent → Option (BNTree Sequent)
  | T@(node _ (Γ, Δ) _) =>
    match Δ.reverse with
    | [] => none
    | B :: Δ' =>
      node T (Γ, Δ'.reverse ++ [A ∨ₚ B]) leaf
  | _ => none

end LkpFormalization
