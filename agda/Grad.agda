
module _ where
 
module _ where
  open import Data.Product
  open import Data.Nat using (ℕ; zero; suc; _+_; _<_; s≤s)
  open import Data.Nat.Properties
  open import Relation.Binary.PropositionalEquality
  open import Function
  open import Ar
  open import Lang
  open WkSub
  
  -- Tel Γ Δ is a telescope where the first expression
  -- is in Γ variables.  Γ is always prefix of Δ
  data Tel : Ctx → Ctx → Set where
    ε   : Tel Γ Γ
    _▹_ : Tel Γ Δ → E Δ (ar s) → Tel Γ (Δ ▹ ar s)

  data Env : Ctx → Ctx → Set where
    ε    : Env ε Γ
    skip : Env Γ Δ → Env (Γ ▹ ix s) Δ
    _▹_  : Env Γ Δ → E Δ (ar s) → Env (Γ ▹ ar s) Δ

  data EE : Ctx → Ctx → Set where
    env : Env Γ Δ → EE Γ Δ
    let′ : E Δ (ar s) → EE Γ (Δ ▹ ar s) → EE Γ Δ 

  -- Weaken all expressions in the Env enironment
  env-wk : Δ ⊆ Ψ → Env Γ Δ → Env Γ Ψ
  env-wk w ε = ε
  env-wk w (skip ρ) = skip (env-wk w ρ)
  env-wk w (ρ ▹ x) = env-wk w ρ ▹ wk w x

  -- Weaken all expressions in the EE environment
  ee-wk : Δ ⊆ Ψ → EE Γ Δ → EE Γ Ψ
  ee-wk w (env x) = env (env-wk w x)
  ee-wk w (let′ x ρ) = let′ (wk w x) (ee-wk (keep w) ρ)

  -- Throw away the last element
  ee-tail : EE (Γ ▹ is) Δ → EE Γ Δ
  ee-tail (env (skip ρ)) = env ρ
  ee-tail (env (ρ ▹ _)) = env ρ
  ee-tail (let′ x ρ) = let′ x (ee-tail ρ)

  -- Insert zeroes in the environment Env according to the ⊆ content
  env-wk-zero : Env Γ Δ → Γ ⊆ Ψ → Env Ψ Δ
  env-wk-zero ρ ε = ρ
  env-wk-zero ρ (skip {is = ix x} w) = skip (env-wk-zero ρ w)
  env-wk-zero ρ (skip {is = ar x} w) = env-wk-zero ρ w ▹ zero
  env-wk-zero (skip ρ) (keep {is = ix x} w) = skip (env-wk-zero ρ w)
  env-wk-zero (ρ ▹ x₁) (keep {is = ar x} w) = env-wk-zero ρ w ▹ x₁

  -- Insert zeroes in the environment EE according to the ⊆ content
  ee-wk-zero : EE Γ Δ → Γ ⊆ Ψ → EE Ψ Δ
  ee-wk-zero (env ρ) w = env (env-wk-zero ρ w)
  ee-wk-zero (let′ x ρ) w = let′ x (ee-wk-zero ρ w)

  -- Add zero to the end of EE (wrapper for ee-wk-zero)
  ee-push-zero : EE Γ Δ → EE (Γ ▹ ar s) Δ
  ee-push-zero ρ = ee-wk-zero ρ (skip ⊆-eq) 

  zero-env : Env Γ Δ
  zero-env {ε} = ε
  zero-env {Γ ▹ ix x} = skip zero-env
  zero-env {Γ ▹ ar x} = zero-env ▹ zero

  zero-ee : EE Γ Δ
  zero-ee = env (zero-env)

  env-update+ : Env Γ Δ → (v : ar s ∈ Γ) → (t : E Δ (ar s)) → Env Γ Δ
  env-update+ (ρ ▹ x) v₀ t = ρ ▹ (x ⊞ t)
  env-update+ (skip ρ) (there v) t = skip (env-update+ ρ v t)
  env-update+ (ρ ▹ x) (there v) t = env-update+ ρ v t ▹ x

  ee-update+ : EE Γ Δ → (v : ar s ∈ Γ) (t : E Δ (ar s)) → EE Γ Δ
  ee-update+ (env ρ) v t = env (env-update+ ρ v t)
  ee-update+ (let′ x ρ) v t = let′ x (ee-update+ ρ v (t ↑))
 
  env-map-sum : Env Γ (Δ ▹ ix s) → Env Γ Δ
  env-map-sum ε = ε
  env-map-sum (skip ρ) = skip (env-map-sum ρ)
  env-map-sum (ρ ▹ x) = env-map-sum ρ ▹ E.sum x

  ee-fold : EE Γ Δ → Env Γ Δ
  ee-fold (env x) = x
  ee-fold {Δ = Δ} (let′ {s = s} x ρ) = map-let (ee-fold ρ)
    where map-let : ∀ {Γ} → Env Γ (Δ ▹ ar s) → Env Γ Δ 
          map-let ε = ε
          map-let (skip ν) = skip (map-let ν)
          map-let (ν ▹ e) = map-let ν ▹ let′ x e

  ee-map-sum : EE Γ (Δ ▹ ix s) → EE Γ Δ
  ee-map-sum ρ = env (env-map-sum (ee-fold ρ))

  env-plus : (ρ ν : Env Γ Δ) → Env Γ Δ
  env-plus ε ν = ν
  env-plus (skip ρ) (skip ν) = skip (env-plus ρ ν)
  env-plus (ρ ▹ x) (ν ▹ y) = env-plus ρ ν ▹ (x ⊞ y)

  {-# TERMINATING #-}
  ee-plus : (ρ ν : EE Γ Δ) → EE Γ Δ
  ee-plus (env ρ) (env ν) = env (env-plus ρ ν)
  ee-plus (env ρ) (let′ x ν) = let′ x (ee-plus (ee-wk (skip ⊆-eq) (env ρ)) ν)
  ee-plus (let′ x ρ) ν = let′ x (ee-plus ρ (ee-wk (skip ⊆-eq) ν))

  -- This is a section that implements a terminating version
  -- of the ee-plus.
  let-depth : EE Γ Δ → ℕ
  let-depth (env x) = 0
  let-depth (let′ x ρ) = suc (let-depth ρ)
  
  ee-wk-depth : (ρ : EE Γ Δ) → (w : Δ ⊆ Ψ) → let-depth ρ ≡ let-depth {Δ = Ψ} (ee-wk w ρ)
  ee-wk-depth (env x) w = refl
  ee-wk-depth (let′ x ρ) w = cong suc (ee-wk-depth ρ (keep w))

  sub-<₁ : ∀ {a b c} → a < b → a ≡ c → c < b
  sub-<₁ a<b refl = a<b
  
  eep : (ρ ν : EE Γ Δ) → (l : ℕ) → (let-depth ρ + let-depth ν < l) → EE Γ Δ
  eep (env ρ) (env ν) l pf = env (env-plus ρ ν)
  eep (env ρ) (let′ x ν) (suc l) (s≤s pf) = let′ x (eep (ee-wk (skip ⊆-eq) (env ρ)) ν l pf)
  eep (let′ x ρ) ν (suc l) (s≤s pf) = let′ x (eep ρ (ee-wk (skip ⊆-eq) ν) l (sub-<₁ pf (cong (let-depth ρ +_) (ee-wk-depth _ _))))

  ee-plus′ : (ρ ν : EE Γ Δ) → EE Γ Δ
  ee-plus′ ρ ν = eep ρ ν (suc (let-depth ρ + let-depth ν)) ≤-refl



  env-lookup : Env Γ Δ → ar s ∈ Γ → E Δ (ar s)
  env-lookup (ρ ▹ x) v₀ = x
  env-lookup (skip ρ) (there v) = env-lookup ρ v
  env-lookup (ρ ▹ x) (there v) = env-lookup ρ v

  env-rm-/ : Env Γ Δ → (v : ar s ∈ Γ) → Env (Γ / v) Δ
  env-rm-/ (ρ ▹ x) v₀ = ρ
  env-rm-/ (skip ρ) (there v) = skip (env-rm-/ ρ v)
  env-rm-/ (ρ ▹ x) (there v) = env-rm-/ ρ v ▹ x

  ee-rm-/ : EE Γ Δ → (v : ar s ∈ Γ) → EE (Γ / v) Δ
  ee-rm-/ (env ρ) v = env (env-rm-/ ρ v)
  ee-rm-/ (let′ x ρ) v = let′ x (ee-rm-/ ρ v)

  glet-sub : (v : ar s ∈ Δ) → Sub ((Δ / v) ▹ ar s) Δ
  glet-sub v₀ = sub-id
  glet-sub (there v) = skeep (glet-sub v) ∙ˢ sub-swap

  glet : (v : ar s ∈ Δ) → (x : E (Δ / v) (ar s)) → E Δ (ar p) → E (Δ / v) (ar p)
  glet v x e = let′ x $′ sub e (glet-sub v)

  env-sub : Env Γ Δ → Sub Ψ Δ → Env Γ Ψ
  env-sub ε s = ε
  env-sub (skip ρ) s = skip (env-sub ρ s)
  env-sub (ρ ▹ x) s = env-sub ρ s ▹ sub x s

  ee-sub : EE Γ Δ → Sub Ψ Δ → EE Γ Ψ
  ee-sub (env x) s = env (env-sub x s)
  ee-sub (let′ x ρ) s = let′ (sub x s) (ee-sub ρ (skeep s))

  env-let : (v : ar s ∈ Δ) (x : E (Δ / v) (ar s)) → Env Γ Δ → EE Γ (Δ / v)
  env-let v x ρ = let′ x $′ env $′ env-sub ρ (glet-sub v)

  ee-let : (v : ar s ∈ Δ) (x : E (Δ / v) (ar s)) → EE Γ Δ → EE Γ (Δ / v)
  ee-let v x ρ = let′ x $ ee-sub ρ (glet-sub v) 

  {-# TERMINATING #-}
  grad-last : E Γ (ar s) → EE (Γ ▹ ar s) Γ → EE Γ Γ

  -- Just an alternative (arguably more complicated) implementation
  -- of the `grad-last` function.
  grad-last′ : (v : ar s ∈ Γ) → E (Γ / v) (ar s) → EE (Γ) (Γ / v) → EE (Γ / v) (Γ / v)

  grad : (e s : E Γ is) → EE Γ Γ → EE Γ Γ

  grad-sum : (e s : E (Γ ▹ ix s) (ar p)) → EE Γ Γ → EE Γ Γ
  grad-sum e s δ = ee-plus δ $ ee-tail $ ee-map-sum (grad e s zero-ee)

  grad {is = ix _} (var x) s δ = δ
  grad {is = ar _} (var x) s δ = ee-update+ δ x s
  grad zero s δ = δ
  grad one s δ = δ

  grad (imaps e)              s δ = grad-sum e (sels     (s ↑) (var v₀)) δ
  grad (imap e)               s δ = grad-sum e (sel      (s ↑) (var v₀)) δ
  grad (E.imapb m e)          s δ = grad-sum e (E.selb m (s ↑) (var v₀)) δ

  grad (sels e i)             s δ = grad e (imaps     (zero-but (var v₀) (i ↑) (s ↑))) δ
  grad (sel e i)              s δ = grad e (imap      (zero-but (var v₀) (i ↑) (s ↑))) δ
  grad (E.selb m e i)         s δ = grad e (E.imapb m (zero-but (var v₀) (i ↑) (s ↑))) δ

  grad (E.sum e)              s δ = grad-sum e (s ↑) δ
  grad (zero-but i j e)       s δ = grad e (zero-but i j s) δ

  grad (E.slide i p e su)     s δ = grad e (E.backslide i s su p) δ
  grad (E.backslide i e su p) s δ = grad e (E.slide i p s su) δ

  grad (e ⊞ e₁)               s   = grad e s ∘ grad e₁ s
  grad (e ⊠ e₁)               s   = grad e (s ⊠ e₁) ∘ grad e₁ (s ⊠ e)
  grad (scaledown x e)        s   = grad e (scaledown x s)
  grad (minus e)              s   = grad e (minus s)
  grad (logistic e)           s   = grad e (let′ (logistic e) ((s ↑) ⊠ var v₀ ⊠ (one ⊞ minus (var v₀))))
  
  grad (let′ e e₁) s δ =
    let
      r = grad e₁ (s ↑) (ee-push-zero $′ ee-wk (skip ⊆-eq) δ)
      --t = grad-last′ v₀ e (let′ e r)
      t = grad-last e (let′ e r)


    in t 

  grad-last′ v e (env ρ) = let
    w = env-lookup ρ v
    t = grad (wk (wk-/ v) e) (var v) (env (env-wk (wk-/ v) ρ))
    u = ee-let v w t
    r = ee-rm-/ u v
    in r
  grad-last′ v e (let′ x ρ) = let′ x $′ ee-tail $′ grad-last′ (there v) (e ↑) (ee-push-zero ρ)




  grad-last e (env (ρ ▹ x)) = ee-tail $′ let′ x $′ grad (e ↑) (var v₀) (ee-push-zero $′ ee-wk (skip ⊆-eq) (env ρ))
  grad-last e (let′ x ρ) = let
      t = let′ x $′ ee-tail $′ grad-last (e ↑) (ee-wk-zero ρ (keep (skip ⊆-eq)))
    in t


