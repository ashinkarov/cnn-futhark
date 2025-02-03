module _ where
  open import Data.Nat as ℕ using (ℕ)
  open import Data.Float as F using (_+_; _*_; _÷_; e^_; -_; fromℕ) renaming (Float to ℝ)
  open import Data.List as L using (List; []; _∷_)
  open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
  open import Relation.Binary.PropositionalEquality
  open import Function

  open import Ar
  
  conv : s + p ≈ r → Ar r ℝ → Ar s ℝ → suc p ≈ u → Ar u ℝ
  conv sp a w su = sum (zipWith _+_) (K 0.0) λ i → map (w i *_) (slide i sp a su)

  mconv : ⦃ s + p ≈ r ⦄ → (inp : Ar r ℝ) (w : Ar (u ⊗ s) ℝ) (b : Ar u ℝ)
        → ⦃ suc p ≈ q ⦄ → Ar (u ⊗ q) ℝ
  mconv ⦃ sp ⦄ inp w b ⦃ su ⦄ 
    = unnest λ i → map (b i +_) (conv sp inp (nest w i) su)

  logistic : Ar s ℝ → Ar s ℝ
  logistic = map λ x → 1.0 ÷ (1.0 + e^ (- x))

  avgp₂ : (m n : ℕ) → Ar (m ℕ.* 2 ∷ n ℕ.* 2 ∷ []) ℝ → Ar (m ∷ n ∷ []) ℝ
  avgp₂ m n a = map ((_÷ fromℕ 4) ∘ sum _+_ 0.0) (selb a it)
 
  forward : (inp  :  Ar (28 ∷ 28 ∷ []) ℝ) → (k₁ : Ar (6 ∷ 5 ∷ 5 ∷ []) ℝ)
          → (b₁   :  Ar (6  ∷ []) ℝ)      → (k₂ : Ar (12 ∷ 6 ∷ 5 ∷ 5 ∷ []) ℝ)
          → (b₂   :  Ar (12 ∷ []) ℝ)      → (fc : Ar (10 ∷ 12 ∷ 1 ∷ 4 ∷ 4 ∷ []) ℝ)
          → (b    :  Ar (10 ∷ []) ℝ)      → Ar (10 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ []) ℝ
  forward inp k₁ b₁ k₂ b₂ fc b = let
      c₁ : Ar (6 ∷ 24 ∷ 24 ∷ []) ℝ
      c₁ = logistic $ mconv inp k₁ b₁ 

      s₁ : Ar (6 ∷ 12 ∷ 12 ∷ []) ℝ
      s₁ = unnest {s = 6 ∷ []} $ map (avgp₂ 12 12) (nest c₁)

      c₂ : Ar (12 ∷ 1 ∷ 8 ∷ 8 ∷ []) ℝ
      c₂ = logistic $ mconv  s₁ k₂ b₂ 

      s₂ : Ar (12 ∷ 1 ∷ 4 ∷ 4 ∷ []) ℝ
      s₂ = unnest {s = 12 ∷ 1 ∷ []} $ map (avgp₂ 4 4) (nest c₂)

      r = logistic $ mconv s₂ fc b 
    in r
