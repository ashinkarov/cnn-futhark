{-# OPTIONS --backtracking-instance-search #-} -- only needed for tests
module _ where

open import Grad

module Optimise where
  open import Lang
  open import Data.Product
  open import Data.Nat
  -- We are not interested in the proof,
  -- but we are interested in the optimisation, so we ignore
  -- the R module, and make it up with a postulate

  open import Real
  postulate
    r : Real.Real
    rp : RealProp r

  open import Opt r rp public

  doopt : E Γ is → E Γ is
  doopt e = opt e .proj₁  
  
  multiopt : E Γ is → ℕ → E Γ is
  multiopt e 0 = e
  multiopt e (suc n) = doopt (multiopt e n)


module Extract where
  open import Data.String
  open import Text.Printf
  open import Data.Product as Prod
  open import Data.Nat using (ℕ; zero; suc; _+_)
  open import Data.List as L
  open import Relation.Binary.PropositionalEquality
  
  open import Lang
  open import Ar hiding (r)
  open import Function
  open import Futhark
  open import Replace

  open import Effect.Monad.State
  open import Effect.Monad using (RawMonad)
  open RawMonadState {{...}} --public
  open RawMonad {{...}} --public
  
  instance
    _ = monad
    _ = applicative
    _ = monadState

  open Optimise
  open Syntax
  open Primitives
  open WkSub

  OPT = 10
  
  -- Show Env (e.g. after running grad) where optimisations are applied
  -- to every expression in the list.
  env-opt : Env Γ Δ → Env Γ Δ
  env-opt ε = ε
  env-opt (skip ρ) = skip (env-opt ρ)
  env-opt (ρ ▹ x) = env-opt ρ ▹ multiopt x OPT

  ee-opt : EE Γ Δ → EE Γ Δ
  ee-opt (env ρ) = env (env-opt ρ)
  ee-opt (let′ x ρ) = let′ (multiopt x OPT) (ee-opt ρ)
  
  env-count-uses : Env Γ Δ → is ∈ Δ → ℕ
  env-count-uses ε v = 0
  env-count-uses (skip ρ) v = env-count-uses ρ v
  env-count-uses (ρ ▹ x) v = env-count-uses ρ v + count-uses x v

  ee-count-uses : EE Γ Δ → is ∈ Δ → ℕ
  ee-count-uses (env ρ) = env-count-uses ρ
  ee-count-uses (let′ x ρ) v = count-uses x v + ee-count-uses ρ (there v)

  ee-inline : EE Γ Δ → EE Γ Δ
  ee-inline (env x) = env x
  ee-inline (let′ x ρ) with δ ← ee-inline ρ | ee-count-uses δ v₀
  ... | 0 = ee-sub δ (sub-id ▹ x)
  ... | 1 = ee-sub δ (sub-id ▹ x)
  ... | _ = let′ x δ

  env-replace : Env Γ Δ → (a b : E Δ is) → Env Γ Δ
  env-replace ε a b = ε
  env-replace (skip ρ) a b = skip (env-replace ρ a b)
  env-replace (ρ ▹ x) a b = env-replace ρ a b ▹ replace x a b

  ee-replace : EE Γ Δ → (a b : E Δ is) → EE Γ Δ
  ee-replace (env ρ) x y = env (env-replace ρ x y)
  ee-replace (let′ e e₁) x y = let′ (replace e x y) (ee-replace e₁ (x ↑) (y ↑))
  
  ee-dedup : EE Γ Δ → EE Γ Δ
  ee-dedup (env x) = env x
  ee-dedup (let′ x e) = let′ x (ee-replace (ee-dedup e) (x ↑) (var v₀))

  ee-OPT : EE Γ Δ → EE Γ Δ
  ee-OPT ρ = ee-opt (ee-inline (ee-opt ρ))

  data NamedEnv : Ctx → Set where
    ε : NamedEnv ε
    _▹_ : NamedEnv Γ → String → NamedEnv (Γ ▹ is)
    
  from-named : NamedEnv Γ → FEnv Γ
  from-named ε = _
  from-named (_▹_ {is = ix s} ρ x) = from-named ρ , fresh-ix x
  from-named (_▹_ {is = ar s} ρ x) = from-named ρ , mkar x


  -- Show chain using SemFuthark
  env-fut′ : Env Γ Δ → NamedEnv Γ → NamedEnv Δ → State ℕ String
  env-fut′ ε ρ ν = return ""
  env-fut′ (skip e) (ρ ▹ _) ν = env-fut′ e ρ ν
  env-fut′ (e ▹ x) (ρ ▹ n) ν = do
    r ← env-fut′ e ρ ν
    v ← to-str x (from-named ν)
    return $ printf "%s\nlet d%s = %s" r n v

  ee-fut′ : EE Γ Δ → NamedEnv Γ → NamedEnv Δ → State ℕ String
  ee-fut′ (env ρ) = env-fut′ ρ
  ee-fut′ (let′ {s = s} x e) ρ ν = do
    c ← get
    modify suc
    v ← to-str x (from-named ν)
    let n = fresh-var c
    r ← ee-fut′ e ρ (ν ▹ n)
    return $ printf "let %s = %s\n%s" n v r
  
  -- Apply optimisations and generate the code.
  ee-fut : EE Γ Γ → NamedEnv Γ → String
  ee-fut e ρ = proj₂ $ runState (ee-fut′ (ee-opt $ ee-dedup $ ee-opt e) ρ ρ) 0

  pp : E Γ (ar s) → NamedEnv Γ → String
  pp e ρ = ee-fut ({- env-norm-lets $ -} grad e one zero-ee) ρ

  -- Examples
  -- ========
  conv-e : E _ _
  conv-e = Lcon (ar (5 ∷ 5 ∷ []) ∷ ar (2 ∷ 2 ∷ []) ∷ []) (ar (4 ∷ 4 ∷ [])) ε
           λ img k1 → Let t := Primitives.conv img k1 In
                      logistic t

  grad-conv-e = pp conv-e (ε ▹ "img" ▹ "k1")
  grad-conv-s = pp conv-e (ε ▹ "inp" ▹ "k1")

  compc1 : E _ _
  compc1 =  Lcon (  ar (28 ∷ 28 ∷ []) ∷ ar (6 ∷ 5 ∷ 5 ∷ [])
                  ∷ ar (6 ∷ []) ∷ ar (12 ∷ 6 ∷ 5 ∷ 5 ∷ [])
                  ∷ ar (12 ∷ []) ∷ []) 

                  --(ar (12 ∷ 1 ∷ 8 ∷ 8 ∷ [])) ε
                  (ar (12 ∷ 1 ∷ 8 ∷ 8 ∷ [])) ε
            λ inp k₁ b₁ k₂ b₂ →
            Let c₁₁ := mconv inp k₁ b₁  In
            Let c₁ := logistic c₁₁ In
            Let s₁  := (Imap {s = 6 ∷ []} λ i → avgp₂ 12 12 (sel c₁ i)) In
            Let c₂₁ := mconv s₁ k₂ b₂ In
            c₂₁
            --Let c₂ := logistic c₂₁ In
            --c₂
            


  grad-compc1-e = ee-opt (grad compc1 one zero-ee)
  grad-compc1-s = pp compc1 (ε ▹ "inp" ▹ "k1" ▹ "b1" ▹ "k2" ▹ "b2")

  test-e : E _ _
  test-e = Lcon (ar ([]) ∷  ar [] ∷ []) (ar ([])) ε
           λ x s  → Let y := logistic x In y ⊠ x  
           
           --let z = (let bad = x
           --         in (let x9 = one
           --              in x9))
           --in z ⊞ x
  test-n = WkSub.norm-lets test-e



  grad-test-e = ee-opt (grad test-e (var v₀) zero-ee)
  grad-test-s = ee-fut (grad test-e (var v₀) zero-ee) (ε ▹ "x" ▹ "s" )

  grad-cnn-e = ee-OPT (grad Primitives.cnn one zero-ee)
  grad-cnn-s = pp Primitives.cnn (ε ▹ "inp" ▹ "k1" ▹ "b1" ▹ "k2" ▹ "b2" ▹ "fc" ▹ "b" ▹ "target" )
  --grad-cnn-s = ee-fut (grad cnn (var v₀) zero-ee) (ε ▹ "inp" ▹ "k1" ▹ "b1" ▹ "k2" ▹ "b2" ▹ "fc" ▹ "b" ▹ "target" ▹ "seed")


  esum-zb : E (ε ▹ ar []) _
  esum-zb = 
         (imaps {s = 10 ∷ []}
           (E.sum
            (zero-but (var v₁) (var v₀)
             (minus
              (scaledown 2 (var v₂) ⊠ one))
             ⊞
             zero-but (var v₁) (var v₀)
             (minus
              (scaledown 2 (var v₂) ⊠
               one)))))

  esum-opt-e = multiopt esum-zb OPT



open import Lang
open Optimise
open import Opt
open import Real
open import Ar
open import Data.List
open import Data.Product
open import Data.Fin
open import Data.List.Relation.Unary.All

