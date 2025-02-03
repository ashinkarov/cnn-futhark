open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality

record Real : Set₁ where
  field
    R : Set
    fromℕ : ℕ → R
    _+_ _*_ _÷_ : R → R → R
    -_ e^_ : R → R

  infixl 10 _+_ 
  infixl 15 _*_ 
  infixl 15 _÷_ 

  logisticʳ : R → R
  logisticʳ x = fromℕ 1 ÷ (fromℕ 1 + e^ (- x))


record RealProp (r : Real) : Set where
  open Real r
  field
    +-neutˡ : ∀ {x} → fromℕ 0 + x ≡ x
    +-neutʳ : ∀ {x} → x + fromℕ 0 ≡ x
    *-neutˡ : ∀ {x} → fromℕ 1 * x ≡ x
    *-neutʳ : ∀ {x} → x * fromℕ 1 ≡ x


