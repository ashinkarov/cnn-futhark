{-# OPTIONS  --backtracking-instance-search #-}

module _ where
module _ where
  open import Ar hiding (sum; slide; backslide; imapb; selb)
  open import Relation.Binary.PropositionalEquality
  open import Data.Product
  open import Data.Nat using (ℕ; zero; suc; _≟_)
  open import Data.List as L
  open import Data.List.Properties as L
  open import Relation.Nullary
  open import Data.Maybe
  open import Function
  open import Lang
  open import Ar
  open import LangEq

  open WkSub



  -- replace x with y in e.
  -- if x is any subexpression in e.
  replace : (e : E Γ is) (x y : E Γ ip) → E Γ is
  replace e x y with e-eq? e x
  ... | just (refl , refl) = y
  replace (var v) x y | nothing = var v
  replace zero x y | nothing = zero
  replace one x y | nothing = one
  replace (imaps e) x y | nothing = imaps (replace e (x ↑) (y ↑))
  replace (sels e e₁) x y | nothing = sels (replace e x y) (replace e₁ x y)
  replace (imap e) x y | nothing = imap (replace e (x ↑) (y ↑))
  replace (sel e e₁) x y | nothing = sel (replace e x y) (replace e₁ x y)
  replace (E.imapb x₁ e) x y | nothing = E.imapb x₁ (replace e (x ↑) (y ↑))
  replace (E.selb x₁ e e₁) x y | nothing = E.selb x₁ (replace e x y) (replace e₁ x y)
  replace (E.sum e) x y | nothing = E.sum (replace e (x ↑) (y ↑))
  replace (zero-but e e₁ e₂) x y | nothing = zero-but (replace e x y) (replace e₁ x y) (replace e₂ x y)
  replace (E.slide e x₁ e₁ x₂) x y | nothing = E.slide (replace e x y) x₁ (replace e₁ x y) x₂
  replace (E.backslide e e₁ x₁ x₂) x y | nothing = E.backslide (replace e x y) (replace e₁ x y) x₁ x₂
  replace (logistic e) x y | nothing = logistic (replace e x y)
  replace (bin x₁ e e₁) x y | nothing = bin x₁ (replace e x y) (replace e₁ x y)
  replace (scaledown x₁ e) x y | nothing = scaledown x₁ (replace e x y)
  replace (minus e) x y | nothing = minus (replace e x y)
  replace (let′ e e₁) x y | nothing = let′ (replace e x y) (replace e₁ (x ↑) (y ↑))


module Test where
  open import Data.List

  open import Lang
  open Syntax
  
  ex₁ : E _ _
  ex₁ = Lcon (ar [] ∷ []) (ar []) ε
        λ a → Let x := (Let y := a ⊞ a In (y) ⊞ (y)) In x

  ex-repl = replace ex₁ (var v₀ ⊞ var v₀) one

open import Lang
