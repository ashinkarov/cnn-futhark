
module _ where
 
module _ where
  open import Data.Product
  open import Data.Nat --using (ℕ; zero; suc; _+_; _<_; s≤s)
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

  --{-# TERMINATING #-}  -- See GradTerm.agda where this is fixed
  --ee-plus : (ρ ν : EE Γ Δ) → EE Γ Δ
  --ee-plus (env ρ) (env ν) = env (env-plus ρ ν)
  --ee-plus (env ρ) (let′ x ν) = let′ x (ee-plus (ee-wk (skip ⊆-eq) (env ρ)) ν)
  --ee-plus (let′ x ρ) ν = let′ x (ee-plus ρ (ee-wk (skip ⊆-eq) ν))

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

  -- Terminating version of env-plus.
  -- decreasinga argument is given by the sum of let-depth-s
  -- of the corresponding environments.
  ee-plus : (ρ ν : EE Γ Δ) → EE Γ Δ
  ee-plus ρ ν = eep ρ ν (suc (let-depth ρ + let-depth ν)) ≤-refl

  env-lookup : Env Γ Δ → ar s ∈ Γ → E Δ (ar s)
  env-lookup (ρ ▹ x) v₀ = x
  env-lookup (skip ρ) (there v) = env-lookup ρ v
  env-lookup (ρ ▹ x) (there v) = env-lookup ρ v

  env-sub : Env Γ Δ → Sub Ψ Δ → Env Γ Ψ
  env-sub ε s = ε
  env-sub (skip ρ) s = skip (env-sub ρ s)
  env-sub (ρ ▹ x) s = env-sub ρ s ▹ sub x s

  ee-sub : EE Γ Δ → Sub Ψ Δ → EE Γ Ψ
  ee-sub (env x) s = env (env-sub x s)
  ee-sub (let′ x ρ) s = let′ (sub x s) (ee-sub ρ (skeep s))



  e-depth : E Γ is → ℕ
  e-depth (var x) = 0
  e-depth zero = 0
  e-depth one = 0
  e-depth (imaps e) = e-depth e
  e-depth (sels e e₁) = e-depth e
  e-depth (imap e) = e-depth e
  e-depth (sel e e₁) = e-depth e
  e-depth (E.imapb x e) = e-depth e
  e-depth (E.selb x e e₁) = e-depth e
  e-depth (E.sum e) = e-depth e
  e-depth (zero-but e e₁ e₂) = e-depth e₂
  e-depth (E.slide e x e₁ x₁) = e-depth e₁
  e-depth (E.backslide e e₁ x x₁) = e-depth e₁
  e-depth (logistic e) = e-depth e
  e-depth (bin x e e₁) = e-depth e ⊔ e-depth e₁
  e-depth (scaledown x e) = e-depth e
  e-depth (minus e) = e-depth e
  e-depth (let′ e e₁) = 1 + (e-depth e ⊔ e-depth e₁)

  e-depth-wk : (e : E Γ is) (w : Γ ⊆ Δ) → e-depth (wk w e) ≡ e-depth e
  e-depth-wk (var x) w = refl
  e-depth-wk zero w = refl
  e-depth-wk one w = refl
  e-depth-wk (imaps e) w = e-depth-wk e (keep w)
  e-depth-wk (sels e e₁) w = e-depth-wk e w
  e-depth-wk (imap e) w = e-depth-wk e (keep w)
  e-depth-wk (sel e e₁) w = e-depth-wk e w
  e-depth-wk (E.imapb x e) w = e-depth-wk e (keep w)
  e-depth-wk (E.selb x e e₁) w = e-depth-wk e w
  e-depth-wk (E.sum e) w = e-depth-wk e (keep w)
  e-depth-wk (zero-but e e₁ e₂) w = e-depth-wk e₂ w
  e-depth-wk (E.slide e x e₁ x₁) w = e-depth-wk e₁ w
  e-depth-wk (E.backslide e e₁ x x₁) w = e-depth-wk e₁ w
  e-depth-wk (logistic e) w = e-depth-wk e w
  e-depth-wk (bin x e e₁) w = cong₂ _⊔_ (e-depth-wk e w) (e-depth-wk e₁ w)
  e-depth-wk (scaledown x e) w = e-depth-wk e w
  e-depth-wk (minus e) w = e-depth-wk e w
  e-depth-wk (let′ e e₁) w = cong suc (cong₂ _⊔_ (e-depth-wk e w) (e-depth-wk e₁ (keep w)))

  a<b⇒0<b : ∀ {a b} → a < b → 0 < b
  a<b⇒0<b (s≤s a<b) = s≤s z≤n

  ⊔-<₁ : ∀ {a b c} → a ⊔ b < c → a < c
  ⊔-<₁ {zero} a⊔b<c = a<b⇒0<b a⊔b<c
  ⊔-<₁ {suc a} {zero} (s≤s a⊔b<c) = s≤s a⊔b<c
  ⊔-<₁ {suc a} {suc b} (s≤s a⊔b<c) = s≤s (⊔-<₁ {a} a⊔b<c)

  ⊔-<₂ : ∀ {a b c} → a ⊔ b < c → b < c
  ⊔-<₂ {zero} {zero} a⊔b<c = a⊔b<c
  ⊔-<₂ {suc a} {zero} a⊔b<c = a<b⇒0<b a⊔b<c
  ⊔-<₂ {zero} {suc b} a⊔b<c = a⊔b<c
  ⊔-<₂ {suc a} {suc b} (s≤s a⊔b<c) = s≤s (⊔-<₂ a⊔b<c)

  e-depth-↑ : ∀ (e : E Γ is) {l} → e-depth e < l → e-depth (_↑ {ip = ip} e) < l
  e-depth-↑ {ip = ip} e e<l rewrite e-depth-wk e (skip {is = ip} ⊆-eq) = e<l

  let-depth-wkz : (ρ : EE (Γ ▹ is) Δ) → let-depth (ee-wk-zero ρ (keep (skip {is = ip} ⊆-eq))) ≡ let-depth ρ
  let-depth-wkz (env x) = refl
  let-depth-wkz (let′ x ρ) = cong suc (let-depth-wkz ρ)

  let-depth-wkz<l : (ρ : EE (Γ ▹ is) Δ) {ld : ℕ} → (let-depth ρ < ld) → let-depth (ee-wk-zero ρ (keep (skip {is = ip} ⊆-eq))) < ld
  let-depth-wkz<l {ip = ip} ρ ρ<l rewrite let-depth-wkz {ip = ip} ρ = ρ<l

  --{-# TERMINATING #-} 
  -- There are two decreasing arguments happening here:
  --    e-depth e < l                      for grad e
  --    e-depth e < l                      for grad-sum e
  --    let-depth δ < ld ∧ e-depth e < l   for grad-last e δ ...
  grad-last : (e : E Γ (ar s)) → (δ : EE (Γ ▹ ar s) Γ)  → (l : ℕ) (_ : e-depth e < l) (ld : ℕ) (_ : let-depth δ < ld) → EE Γ Γ

  grad′ : (e s : E Γ is) → EE Γ Γ → (l : ℕ) (_ : e-depth e < l) → EE Γ Γ

  grad-sum : (e s : E (Γ ▹ ix s) (ar p)) → EE Γ Γ → (l : ℕ) (_ : e-depth e < l) → EE Γ Γ
  grad-sum e s δ l e<l = ee-plus δ $ ee-tail $ ee-map-sum (grad′ e s zero-ee l e<l)

  grad′ {is = ix _} (var x) s δ l e<l = δ
  grad′ {is = ar _} (var x) s δ l e<l = ee-update+ δ x s
  grad′ zero s δ _ _ = δ
  grad′ one s δ _ _ = δ

  grad′ (imaps e)              s δ = grad-sum e (sels     (s ↑) (var v₀)) δ
  grad′ (imap e)               s δ = grad-sum e (sel      (s ↑) (var v₀)) δ
  grad′ (E.imapb m e)          s δ = grad-sum e (E.selb m (s ↑) (var v₀)) δ

  grad′ (sels e i)             s δ = grad′ e (imaps     (zero-but (var v₀) (i ↑) (s ↑))) δ
  grad′ (sel e i)              s δ = grad′ e (imap      (zero-but (var v₀) (i ↑) (s ↑))) δ
  grad′ (E.selb m e i)         s δ = grad′ e (E.imapb m (zero-but (var v₀) (i ↑) (s ↑))) δ

  grad′ (E.sum e)              s δ = grad-sum e (s ↑) δ
  grad′ (zero-but i j e)       s δ = grad′ e (zero-but i j s) δ

  grad′ (E.slide i p e su)     s δ = grad′ e (E.backslide i s su p) δ
  grad′ (E.backslide i e su p) s δ = grad′ e (E.slide i p s su) δ

  grad′ (e ⊞ e₁)               s δ l e<l  = grad′ e s (grad′ e₁ s δ l (⊔-<₂ e<l)) l (⊔-<₁ e<l)
  grad′ (e ⊠ e₁)               s δ l e<l  = grad′ e (s ⊠ e₁) (grad′ e₁ (s ⊠ e) δ l (⊔-<₂ e<l)) l (⊔-<₁ e<l)
  grad′ (scaledown x e)        s   = grad′ e (scaledown x s)
  grad′ (minus e)              s   = grad′ e (minus s)
  grad′ (logistic e)           s   = grad′ e (let′ (logistic e) ((s ↑) ⊠ var v₀ ⊠ (one ⊞ minus (var v₀))))
  
  grad′ (let′ e e₁) s δ (suc l) (s≤s e<l) =
    let
      r = grad′ e₁ (s ↑) (ee-push-zero $′ ee-wk (skip ⊆-eq) δ) l (⊔-<₂ e<l)
      t = grad-last e (let′ e r) l (⊔-<₁ e<l) _ ≤-refl
    in t 

  grad-last e (env (ρ ▹ x)) l e<l _ _ = ee-tail $′ let′ x $′ grad′ (e ↑) (var v₀) (ee-push-zero $′ ee-wk (skip ⊆-eq) (env ρ)) l (e-depth-↑ e e<l)
  grad-last e (let′ x ρ) l e<l (suc ld) (s≤s ρ<ld) = let
      t = let′ x $′ ee-tail $′ grad-last (e ↑) (ee-wk-zero ρ (keep (skip ⊆-eq))) l (e-depth-↑ e e<l) ld (let-depth-wkz<l ρ ρ<ld)
    in t


  grad : (e s : E Γ is) → EE Γ Γ → EE Γ Γ
  grad e s δ = grad′ e s δ _ ≤-refl
