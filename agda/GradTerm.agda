{-# OPTIONS --overlapping-instances #-} -- only needed for tests
-- Make Grad.agda terminating by choosing a metric for the environment

module _ where
 
module _ where
  open import Data.Nat
  open import Data.Nat.Properties
  open import Data.Unit
  open import Data.Product
  open import Data.Sum
  open import Relation.Binary.PropositionalEquality
  open import Function

  open import Ar
  open import Lang
  open WkSub
  

  data Env : Ctx → Ctx → Set where
    ε    : Env ε Γ
    skip : Env Γ Δ → Env (Γ ▹ ix s) Δ
    _▹_  : Env Γ Δ → E Δ (ar s) → Env (Γ ▹ ar s) Δ
    let′ : E Δ (ar s) → Env Γ (Δ ▹ ar s) → Env Γ Δ
  

  env-depth : Env Γ Δ → ℕ
  env-depth ε = 0
  env-depth (skip ρ) = env-depth ρ
  env-depth (ρ ▹ x) = env-depth ρ
  env-depth (let′ x ρ) = 1 + env-depth ρ

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


  --update : Env Γ Δ → (v : ar s ∈ Γ) → (f : E Δ (ar s) → E Δ (ar s)) → Env Γ Δ

  zero-env : Env Γ Δ
  zero-env {ε} = ε
  zero-env {Γ ▹ ix x} = skip zero-env
  zero-env {Γ ▹ ar x} = zero-env ▹ zero

  update+ : Env Γ Δ → (v : ar s ∈ Γ) → (t : E Δ (ar s)) → Env Γ Δ
  update+ (skip ρ) (there v) t = skip (update+ ρ v t)
  update+ (ρ ▹ x) v₀ t = ρ ▹ (x ⊞ t)
  update+ (ρ ▹ x) (there v) t = update+ ρ v t ▹ x
  update+ (let′ x ρ) v t = let′ x (update+ ρ v (t ↑))

  index : Env Γ Δ → ar s ∈ Γ → E Δ (ar s) 
  index (skip ρ) (there v) = index ρ v
  index (ρ ▹ x) v₀ = x
  index (ρ ▹ x) (there v) = index ρ v
  index (let′ x ρ) v = let′ x (index ρ v)
  
  tabulate : (∀ {s} → ar s ∈ Γ → E Δ (ar s)) → Env Γ Δ
  tabulate {Γ = ε} f = ε
  tabulate {Γ = Γ ▹ ix x} f = skip (tabulate (f ∘ there))
  tabulate {Γ = Γ ▹ ar x} f = tabulate (f ∘ there) ▹ f v₀

  tabulate-map : (env : ∀ {s} → ar s ∈ Γ → E Δ (ar s)) (transf : ∀ {s} → E Δ (ar s) → E Ψ (ar s)) → Env Γ Ψ
  tabulate-map {ε} f g = ε
  tabulate-map {Γ ▹ ix x} f g = skip (tabulate-map (f ∘ there) g)
  tabulate-map {Γ ▹ ar x} f g = tabulate-map (f ∘ there) g ▹ g (f v₀)

  -- push all the lets into the expressions of the environment
  -- FIXME: can we implement this directly?
  env-map-sum : Env Γ (Δ ▹ ix s) → Env Γ Δ
  env-map-sum e = tabulate-map (index e) E.sum

  env-wk : Δ ⊆ Ψ → Env Γ Δ → Env Γ Ψ
  env-wk s ε = ε
  env-wk s (skip ρ) = skip (env-wk s ρ)
  env-wk s (ρ ▹ x) = env-wk s ρ ▹ (wk s x)
  env-wk s (let′ x ρ) = let′ (wk s x) (env-wk (keep s) ρ)

  --pull-skip : Env (Γ ▹ ix s) Δ → Env Γ Δ
  --pull-skip (skip ρ) = ρ
  --pull-skip (let′ x ρ) = let′ x (pull-skip ρ)

  env-tail : Env (Γ ▹ is) Δ → Env Γ Δ
  env-tail (skip ρ)   = ρ
  env-tail (ρ ▹ x)    = ρ
  env-tail (let′ x ρ) = let′ x (env-tail ρ)

  env-tail-depth : (e : Env (Γ ▹ is) Δ) → env-depth e ≡ env-depth (env-tail e)
  env-tail-depth (skip e) = refl
  env-tail-depth (e ▹ x) = refl
  env-tail-depth (let′ x e) = cong suc (env-tail-depth e)

  --{-# TERMINATING #-}
  --env-plus : (a b : Env Γ Δ) → Env Γ Δ
  --env-plus ε b = ε
  --env-plus (skip a) b = skip (env-plus a (env-tail b))
  --env-plus (a ▹ x) (b ▹ x₁) = env-plus a b ▹ (x ⊞ x₁)
  --env-plus (a ▹ x) (let′ x₁ b) = let′ x₁ (env-plus (env-wk (skip ⊆-eq) a ▹ (x ↑)) b)
  --env-plus (let′ x a) b = let′ x (env-plus a (env-wk (skip ⊆-eq) b))

  sub-<₁ : ∀ {a b c} → a < b → a ≡ c → c < b
  sub-<₁ a<b refl = a<b

  a+suc : ∀ a b → a + suc b ≡ suc (a + b)
  a+suc zero b = refl
  a+suc (suc a) b = cong suc (a+suc a b)

  env-wk-depth : (a : Env Γ Δ) → (s : Δ ⊆ Ψ) → env-depth a ≡ env-depth (env-wk s a)
  env-wk-depth ε s = refl
  env-wk-depth (skip a) s = env-wk-depth a s
  env-wk-depth (a ▹ x) s = env-wk-depth a s
  env-wk-depth (let′ x a) s = cong suc (env-wk-depth a (keep s))

  env-plus′ : (a b : Env Γ Δ) → (c : ℕ) → (env-depth a + env-depth b < c) → Env Γ Δ
  env-plus′ ε b n a+b<c = ε
  env-plus′ (skip a) b n a+b<c rewrite env-tail-depth b = skip (env-plus′ a (env-tail b) n a+b<c) 
  env-plus′ (a ▹ x) (b ▹ x₁) n a+b<c = env-plus′ a b n a+b<c ▹ (x ⊞ x₁)
  env-plus′ (a ▹ x) (let′ x₁ b) (suc n) (s≤s a+b<c) 
    rewrite a+suc (env-depth a) (env-depth b) 
    = let′ x₁ (env-plus′ (env-wk (skip ⊆-eq) a ▹ (x ↑)) b n 
                         (sub-<₁ a+b<c (cong (_+ env-depth b) (env-wk-depth a _))))
  env-plus′ (let′ x a) b (suc n) (s≤s a+b<c)
    = let′ x (env-plus′ a (env-wk (skip ⊆-eq) b) n 
                          (sub-<₁ a+b<c (cong (env-depth a +_) (env-wk-depth b _))))

  env-plus : (a b : Env Γ Δ) → Env Γ Δ
  env-plus a b = env-plus′ a b (suc (env-depth a + env-depth b)) (≤-refl)

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


  grad′ : (e s : E Γ is) → (δ : Env Γ Γ) (l : ℕ) (_ : e-depth e < l) → Env Γ Γ
  
  grad′-sum : (e s : E (Γ ▹ ix s) (ar p)) → (δ : Env Γ Γ)  (l : ℕ) (_ : e-depth e < l) → Env Γ Γ
  grad′-sum e s δ l e<l = env-plus δ $ env-tail $ env-map-sum (grad′ e s zero-env l e<l)

  grad′ {is = ix _} (var x)    s δ l e<l = δ
  grad′ {is = ar _} (var x)    s δ l e<l = update+ δ x s
  grad′ zero                   s δ l e<l = δ
  grad′ one                    s δ l e<l = δ
  grad′ (imaps e)              s δ = grad′-sum e (sels     (s ↑) (var v₀)) δ 
  grad′ (imap e)               s δ = grad′-sum e (sel      (s ↑) (var v₀)) δ 
  grad′ (E.imapb m e)          s δ = grad′-sum e (E.selb m (s ↑) (var v₀)) δ

  grad′ (sels e i)             s δ = grad′ e (imaps     (zero-but (var v₀) (i ↑) (s ↑))) δ
  grad′ (sel e i)              s δ = grad′ e (imap      (zero-but (var v₀) (i ↑) (s ↑))) δ
  grad′ (E.selb m e i)         s δ = grad′ e (E.imapb m (zero-but (var v₀) (i ↑) (s ↑))) δ

  grad′ (E.sum e)              s δ = grad′-sum e (s ↑) δ
  grad′ (zero-but i j e)       s δ = grad′ e (zero-but i j s) δ

  grad′ (E.slide i p e su)     s δ = grad′ e (E.backslide i s su p) δ
  grad′ (E.backslide i e su p) s δ = grad′ e (E.slide i p s su) δ

  grad′ (e ⊞ e₁)               s δ l e<l  = grad′ e s (grad′ e₁ s δ l (⊔-<₂ e<l)) l (⊔-<₁ e<l)
  grad′ (e ⊠ e₁)               s δ l e<l  = grad′ e (s ⊠ e₁) (grad′ e₁ (s ⊠ e) δ l (⊔-<₂ e<l)) l (⊔-<₁ e<l)
  grad′ (scaledown x e)        s   = grad′ e (scaledown x s)
  grad′ (minus e)              s   = grad′ e (minus s)
  grad′ (logistic e)           s   = grad′ e (s ⊠ logistic e ⊠ (one ⊞ minus (logistic e)))
  --
  grad′ (let′ e e₁)            s δ (suc l) (s≤s e<l) = 
    -- TODO: use this example to explain what is going on.
    -- grad′ (let t = x * y in sin t * y) s δ=(dx, dy)
    --   grad′ (sin t * y) s (0, 0, 0) = let t = x*y in (0, sin t * s, cos t * y * s) 
    -- if y = xy then grad′ (sin (x*y)*y) s = (cos xy * y * y * s , cos xy * xy * s + sin xy * s)
    --                                     = (cos t * y * y * s , cos t * y * x * s + sin t * s)
    -- =>
    --   grad′ (x * y) (S := cos t * y * s) (0, sin t * s) = (y * S , sin t * s + x * S)
    let
      R = grad′ e₁ (s ↑) (env-wk (skip ⊆-eq) δ ▹ zero) l (⊔-<₂ e<l)
      dx = index R v₀
      L′ = let′ dx (grad′ (e ↑ ↑) (var v₀) zero-env l (sub-<₁ (⊔-<₁ e<l) (sym (trans (e-depth-wk (e ↑) _) (e-depth-wk e _)))))
      L′R = env-plus (env-tail L′) R
    in let′ e (env-tail L′R)
   
  grad : (e s : E Γ is) → (δ : Env Γ Γ) → Env Γ Γ
  grad e s δ = grad′ e s δ (suc (e-depth e)) ≤-refl

module Print where
  -- open import Data.Nat.Show using () renaming (show to show-nat)
  -- open import Data.List as L using (List; []; _∷_)
  -- open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
  open import Data.String
  open import Text.Printf
  -- open import Data.Unit
  open import Data.Product as Prod
  open import Data.Nat using (ℕ; zero; suc)
  --open import Ar hiding (_++_)
  open import Lang
  open import Function
  open import Futhark

  open import Effect.Monad.State
  open import Effect.Monad using (RawMonad)
  open RawMonadState {{...}} --public
  open RawMonad {{...}} --public
  
  instance
    _ = monad
    _ = applicative
    _ = monadState


  env-fut : Env Γ Δ → FEnv Γ → FEnv Δ → State ℕ String
  env-fut ε        a b = return ""
  env-fut (skip ρ) (a , i) b = env-fut ρ a b
  env-fut (ρ ▹ x)  (a , ar v) b = do
    ar t ← to-fut x b
    s ← env-fut ρ a b
    return $ printf "%s\nlet∂ %s = %s" s v t
  env-fut (let′ {s = s} x ρ) a b = do
    ar vn ← ar-var {s}
    ar va ← to-fut x b
    s ← env-fut ρ a (b , ar vn)
    return $ printf "let %s = %s\n%s" vn va s


module Test where
  open import Relation.Binary.PropositionalEquality
  open import Data.List as L using (List; []; _∷_)
  
  open import Data.Product as Prod
  open import Data.String
  open import Function
  open import Lang
  open import Futhark
  open Syntax
  open Print

  open Primitives
  open import Ar

  open import Effect.Monad.State
  
  pp : E Γ (ar s) → FEnv Γ → String
  pp e ρ = 
    let
      δ = grad e one zero-env
    in proj₂ $ runState (env-fut δ ρ ρ) 0

  
  let-e : E _ _
  let-e = Lcon (ar [] ∷ ar [] ∷ []) (ar []) ε
           λ x y → Let z := x ⊠ y In z ⊠ x

  test-let : String
  test-let = pp let-e ((_ , ar "x") , ar "y")
  
  -- Convolution
  conv-e : E _ _
  conv-e = Lcon (ar (5 ∷ 5 ∷ []) ∷ ar (2 ∷ 2 ∷ []) ∷ []) (ar (4 ∷ 4 ∷ [])) ε
           λ img k1 → Primitives.conv img k1

  test-conv : String
  test-conv = pp conv-e ((_ , ar "img"), ar "w")
