{-# OPTIONS  --backtracking-instance-search #-}
module _ where
module _ where
  open import Data.Nat using (ℕ; zero; suc)
  open import Data.List as L using (List; []; _∷_)
  open import Ar hiding (sum; slide; backslide; imapb; selb)
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  infixl 15 _▹_

  data IS : Set where
    ix  : S → IS
    ar  : S → IS
  
  -- TODO: Let's carry the name of the variable in the context
  --       so that pretty-printing gets more control.
  data Ctx : Set where
    ε    : Ctx
    _▹_  : Ctx → IS → Ctx
  
  variable
    Γ Δ Ξ Ψ : Ctx
    is ip iq ir : IS
  
  data _∈_ : IS → Ctx → Set where
    here  : is ∈ (Γ ▹ is)
    there : is ∈ Γ → is ∈ (Γ ▹ ip)

  pattern v₀ = here
  pattern v₁ = there v₀
  pattern v₂ = there v₁
  pattern v₃ = there v₂
  pattern v₄ = there v₃
  pattern v₅ = there v₄
  pattern v₆ = there v₅
  pattern v₇ = there v₆
  pattern v₈ = there v₇
  pattern v₉ = there v₈

  -- We only use this for variable comparison.
  _/_ : (Γ : Ctx) → is ∈ Γ → Ctx
  (Γ ▹ x) / here = Γ
  (Γ ▹ x) / there v = (Γ / v) ▹ x

  wkv-/ : (v : is ∈ Γ) → ip ∈ (Γ / v) → ip ∈ Γ
  wkv-/ here w = there w
  wkv-/ (there v) here = here
  wkv-/ (there v) (there w) = there (wkv-/ v w)

  data Eq : is ∈ Γ → ip ∈ Γ → Set where
    veq : {x : is ∈ Γ} → Eq x x
    neq : (x : is ∈ Γ) → (y : ip ∈ (Γ / x)) → Eq x (wkv-/ x y)

  eq? : (x : is ∈ Γ) → (y : ip ∈ Γ) → Eq x y
  eq? v₀ v₀ = veq
  eq? v₀ (there y) = neq v₀ y
  eq? (there x) v₀ = neq (there x) v₀
  eq? (there x) (there y) with eq? x y
  ... | veq = veq
  ... | neq .x y = neq (there x) (there y)


  unthere : {x y : is ∈ Γ} → there {ip = ip} x ≡ there y → x ≡ y
  unthere refl = refl

  neq-wkv : (x : is ∈ Γ) (y : is ∈ (Γ / x)) → x ≢ wkv-/ x y
  neq-wkv v₀ y = λ ()
  neq-wkv (there x) v₀ = λ ()
  neq-wkv (there x) (there y) p = (neq-wkv x y) (unthere p)

  infixl 10 _⊞_
  infixl 15 _⊠_

  data Bop : Set where
    plus mul : Bop

  unit : S
  unit = []

  data E : Ctx → IS → Set where
    var        : is ∈ Γ → E Γ is
    zero       : E Γ (ar s)
    one        : E Γ (ar s)

    imaps      : E (Γ ▹ ix s) (ar unit) → E Γ (ar s)
    sels       : E Γ (ar s) → E Γ (ix s) → E Γ (ar unit)

    imap       : E (Γ ▹ ix s) (ar p) → E Γ (ar (s ⊗ p))
    sel        : E Γ (ar (s ⊗ p)) → E Γ (ix s) → E Γ (ar p)

    imapb      : s * p ≈ q → E (Γ ▹ ix s) (ar p) → E Γ (ar q)
    selb       : s * p ≈ q → E Γ (ar q) → E Γ (ix s) → E Γ (ar p)

    sum        : E (Γ ▹ ix s) (ar p) → E Γ (ar p)
    zero-but   : E Γ (ix s) → E Γ (ix s) → E Γ (ar p) → E Γ (ar p)

    slide      : E Γ (ix s) → s + p ≈ r → E Γ (ar r) → suc p ≈ u → E Γ (ar u)
    backslide  : E Γ (ix s) → E Γ (ar u) → suc p ≈ u → s + p ≈ r → E Γ (ar r)

    logistic   : E Γ (ar s) → E Γ (ar s)
    bin        : Bop → E Γ (ar s) → E Γ (ar s) → E Γ (ar s)
    scaledown  : ℕ → E Γ (ar s) → E Γ (ar s)
    minus      : E Γ (ar s) → E Γ (ar s)
    let′       : E Γ (ar s) → E (Γ ▹ ar s) (ar p) → E Γ (ar p)

  pattern _⊠_ a b = bin mul a b
  pattern _⊞_ a b = bin plus a b



module WkSub where
  open import Data.Nat using (ℕ; zero; suc; _+_)
  open import Relation.Binary.PropositionalEquality
  open import Function

  data _⊆_ : Ctx → Ctx → Set where
    ε    : ε ⊆ ε
    skip : Γ ⊆ Δ → Γ ⊆ (Δ ▹ is)
    keep : Γ ⊆ Δ → (Γ ▹ is) ⊆ (Δ ▹ is)

  wkv : Γ ⊆ Δ → is ∈ Γ → is ∈ Δ
  wkv (skip s) v = there (wkv s v)
  wkv (keep s) v₀ = v₀
  wkv (keep s) (there v) = there (wkv s v)

  wk : Γ ⊆ Δ → E Γ is → E Δ is
  wk s (var x) = var (wkv s x)
  wk s zero = zero
  wk s one = one
  wk s (imaps e) = imaps (wk (keep s) e)
  wk s (sels e e₁) = sels (wk s e) (wk s e₁)
  wk s (imap e) = imap (wk (keep s) e)
  wk s (sel e e₁) = sel (wk s e) (wk s e₁)
  wk s (imapb x e) = imapb x (wk (keep s) e)
  wk s (selb x e e₁) = selb x (wk s e) (wk s e₁)
  wk s (sum e) = sum (wk (keep s) e)
  wk s (zero-but e e₁ e₂) = zero-but (wk s e) (wk s e₁) (wk s e₂)
  wk s (slide e x e₁ x₁) = slide (wk s e) x (wk s e₁) x₁
  wk s (backslide e e₁ x x₁) = backslide (wk s e) (wk s e₁) x x₁
  wk s (logistic e) = logistic (wk s e)
  wk s (bin x e e₁) = bin x (wk s e) (wk s e₁)
  wk s (scaledown x e) = scaledown x (wk s e)
  wk s (minus e) = minus (wk s e)
  wk s (let′ e e₁) = let′ (wk s e) (wk (keep s) e₁)

  _∙ʷ_ : Δ ⊆ Ψ → Γ ⊆ Δ → Γ ⊆ Ψ
  s ∙ʷ ε = s
  skip s ∙ʷ skip p = skip (s ∙ʷ skip p)
  keep s ∙ʷ skip p = skip s ∙ʷ p
  skip s ∙ʷ keep p = skip (s ∙ʷ keep p)
  keep s ∙ʷ keep p = keep (s ∙ʷ p)

  ⊆-eq : Γ ⊆ Γ
  ⊆-eq {ε} = ε
  ⊆-eq {Γ ▹ x} = keep ⊆-eq

  _↑ : E Γ is → E (Γ ▹ ip) is
  _↑ = wk (skip ⊆-eq)

  wk-/ : (v : is ∈ Γ) → (Γ / v) ⊆ Γ
  wk-/ v₀ = skip ⊆-eq
  wk-/ (there v) = keep (wk-/ v)

  data Sub (Γ : Ctx) : Ctx → Set where
    ε   : Sub Γ ε
    _▹_ : Sub Γ Δ → E Γ is → Sub Γ (Δ ▹ is)

  
  wks : Sub Γ Δ → Γ ⊆ Ψ → Sub Ψ Δ
  wks ε p = ε
  wks (s ▹ x) p = (wks s p) ▹ wk p x
  
  sdrop : Sub Γ Δ → Sub (Γ ▹ is) Δ
  sdrop s = wks s (skip ⊆-eq)

  skeep : Sub Γ Δ → Sub (Γ ▹ is) (Δ ▹ is)
  skeep s = sdrop s ▹ var v₀

  subv : Sub Γ Δ → is ∈ Δ → E Γ is
  subv (s ▹ x) v₀ = x
  subv (s ▹ x) (there v) = subv s v
  
  sub-id : Sub Γ Γ
  sub-id {ε} = ε
  sub-id {Γ ▹ x} = skeep sub-id


  sub : E Δ is → Sub Γ Δ → E Γ is
  sub (var x) s = subv s x
  sub zero s = zero
  sub one s = one
  sub (imaps e) s = imaps (sub e (skeep s))
  sub (sels e e₁) s = sels (sub e s) (sub e₁ s)
  sub (imap e) s = imap (sub e (skeep s))
  sub (sel e e₁) s = sel (sub e s) (sub e₁ s)
  sub (imapb x e) s = imapb x (sub e (skeep s))
  sub (selb x e e₁) s = selb x (sub e s) (sub e₁ s)
  sub (sum e) s = sum (sub e (skeep s))
  sub (zero-but e e₁ e₂) s = zero-but (sub e s) (sub e₁ s) (sub e₂ s)
  sub (slide e x e₁ x₁) s = slide (sub e s) x (sub e₁ s) x₁
  sub (backslide e e₁ x x₁) s = backslide (sub e s) (sub e₁ s) x x₁
  sub (logistic e) s = logistic (sub e s)
  sub (bin x e e₁) s = bin x (sub e s) (sub e₁ s)
  sub (scaledown x e) s = scaledown x (sub e s)
  sub (minus e) s = minus (sub e s)
  sub (let′ e e₁) s = let′ (sub e s) (sub e₁ (skeep s))

  _∙ˢ_ : Sub Δ Ψ → Sub Γ Δ → Sub Γ Ψ
  ε ∙ˢ t = ε
  (s ▹ x) ∙ˢ t = (s ∙ˢ t) ▹ sub x t

  -- All kinds of theorems

  wkv-at-eq : (v : is ∈ Γ) → wkv ⊆-eq v ≡ v
  wkv-at-eq v₀ = refl
  wkv-at-eq (there v) = cong there (wkv-at-eq v)

  subv-wks : (v : is ∈ Γ) (s : Sub Δ Γ) (w : Δ ⊆ Ψ) → subv (wks s w) v ≡ wk w (subv s v)
  subv-wks v₀ (s ▹ x) w = refl
  subv-wks (there v) (s ▹ x) w = subv-wks v s w

  subv-sdrop : (v : is ∈ Γ) (s : Sub Δ Γ) → subv (sdrop {is = ip} s) v ≡ (subv s v) ↑
  subv-sdrop v₀ (s ▹ x) = refl
  subv-sdrop (there v) (s ▹ x) = subv-wks v s _

  subv-at-id : (v : is ∈ Γ) → subv sub-id v ≡ var v
  subv-at-id v₀ = refl
  subv-at-id {is} {.(Γ ▹ ip)} (there {is = .is} {Γ = Γ} {ip = ip} v)
    rewrite subv-sdrop {ip = ip} v sub-id | subv-at-id v = cong (var ∘′ there) (wkv-at-eq v)

  sub-at-id : (e : E Γ is) → sub e sub-id ≡ e
  sub-at-id (var x) = subv-at-id x
  sub-at-id zero = refl
  sub-at-id one = refl
  sub-at-id (imaps e) = cong imaps (sub-at-id e)
  sub-at-id (sels e e₁) = cong₂ sels (sub-at-id e) (sub-at-id e₁)
  sub-at-id (imap e) = cong imap (sub-at-id e)
  sub-at-id (sel e e₁) = cong₂ sel (sub-at-id e) (sub-at-id e₁)
  sub-at-id (imapb x e) = cong (imapb x) (sub-at-id e)
  sub-at-id (selb x e e₁) = cong₂ (selb x) (sub-at-id e) (sub-at-id e₁)
  sub-at-id (sum e) = cong sum (sub-at-id e)
  sub-at-id (zero-but e e₁ e₂) rewrite (sub-at-id e) | sub-at-id e₁ | sub-at-id e₂ = refl
  sub-at-id (slide e x e₁ x₁) rewrite sub-at-id e | sub-at-id e₁ = refl
  sub-at-id (backslide e e₁ x x₁) rewrite sub-at-id e | sub-at-id e₁ = refl
  sub-at-id (logistic e) = cong logistic (sub-at-id e)
  sub-at-id (bin x e e₁) = cong₂ (bin x) (sub-at-id e) (sub-at-id e₁)
  sub-at-id (scaledown x e) = cong (scaledown x) (sub-at-id e)
  sub-at-id (minus e) = cong minus (sub-at-id e)
  sub-at-id (let′ e e₁) = cong₂ let′ (sub-at-id e) (sub-at-id e₁)

  sub-ε : (e : E ε is) → sub e ε ≡ e
  sub-ε e = sub-at-id e

  sub-swap : Sub (Γ ▹ is ▹ ip) (Γ ▹ ip ▹ is)
  sub-swap = (sdrop (sdrop sub-id) ▹ var v₀) ▹ var (there v₀)

  open import Data.Maybe
  strenv : (x : is ∈ Γ) (y : ip ∈ Γ) → Maybe (ip ∈ (Γ / x)) 
  strenv v₀ v₀ = nothing
  strenv v₀ (there y) = just y
  strenv (there x) v₀ = just v₀
  strenv (there x) (there y) = map there (strenv x y)

  stren : E Γ is → (v : ip ∈ Γ) → Maybe (E (Γ / v) is)
  stren (var x) v = map var (strenv v x)
  stren zero v = just zero
  stren one v = just one
  stren (imaps e) v = map imaps (stren e (there v))
  stren (sels e e₁) v = do
    l ← stren e v
    r ← stren e₁ v
    just (sels l r)
  stren (imap e) v = map imap (stren e (there v))
  stren (sel e e₁) v = do
    l ← stren e v
    r ← stren e₁ v
    just (sel l r)
  stren (imapb x e) v = map (imapb x) (stren e (there v))
  stren (selb x e e₁) v = do
    l ← stren e v
    r ← stren e₁ v
    just (selb x l r)
  stren (sum e) v = map sum (stren e (there v))
  stren (zero-but e e₁ e₂) v = do
    a ← stren e v
    b ← stren e₁ v
    c ← stren e₂ v
    just (zero-but a b c)
  stren (slide e x e₁ x₁) v = do
    a ← stren e v
    b ← stren e₁ v
    just (slide a x b x₁)
  stren (backslide e e₁ x x₁) v = do
    a ← stren e v
    b ← stren e₁ v
    just (backslide a b x x₁)
  stren (logistic e) v = map logistic (stren e v)
  stren (bin x e e₁) v = do
    a ← stren e v
    b ← stren e₁ v
    just (bin x a b)
  stren (scaledown x e) v = map (scaledown x) (stren e v)
  stren (minus e) v = map minus (stren e v)
  stren (let′ e e₁) v = do
    a ← stren e v
    b ← stren e₁ (there v)
    just (let′ a b)

  -- Get rid of lets that do not use their arguments.
  norm-lets : E Γ is → E Γ is
  norm-lets (var x) = (var x)
  norm-lets zero = zero
  norm-lets one = one
  norm-lets (imaps e) = imaps (norm-lets e)
  norm-lets (sels e e₁) = sels (norm-lets e) (norm-lets e₁)
  norm-lets (imap e) = imap (norm-lets e)
  norm-lets (sel e e₁) = sel (norm-lets e) (norm-lets e₁)
  norm-lets (imapb x e) = imapb x (norm-lets e)
  norm-lets (selb x e e₁) = selb x (norm-lets e) (norm-lets e₁)
  norm-lets (sum e) = sum (norm-lets e)
  norm-lets (zero-but e e₁ e₂) = zero-but (norm-lets e) (norm-lets e₁) (norm-lets e₂)
  norm-lets (slide e x e₁ x₁) = slide (norm-lets e) x (norm-lets e₁) x₁
  norm-lets (backslide e e₁ x x₁) = backslide (norm-lets e) (norm-lets e₁) x x₁
  norm-lets (logistic e) = logistic (norm-lets e)
  norm-lets (bin x e e₁) = bin x (norm-lets e) (norm-lets e₁)
  norm-lets (scaledown x e) = scaledown x (norm-lets e)
  norm-lets (minus e) = minus (norm-lets e)
  norm-lets (let′ e e₁) = maybe id (let′ (norm-lets e) (norm-lets e₁)) (stren (norm-lets e₁) v₀)

  count-uses : E Γ is → ip ∈ Γ → ℕ
  count-uses (var x) v with eq? x v
  ... | veq = 1
  ... | _ = 0
  count-uses zero v = 0
  count-uses one v = 0
  count-uses (imaps e) v = count-uses e (there v)
  count-uses (sels e e₁) v = count-uses e v + count-uses e₁ v
  count-uses (imap e) v = count-uses e (there v)
  count-uses (sel e e₁) v = count-uses e v + count-uses e₁ v
  count-uses (imapb x e) v = count-uses e (there v)
  count-uses (selb x e e₁) v = count-uses e v + count-uses e₁ v
  count-uses (sum e) v = count-uses e (there v)
  count-uses (zero-but e e₁ e₂) v = count-uses e v + count-uses e₁ v + count-uses e₂ v
  count-uses (slide e x e₁ x₁) v = count-uses e v + count-uses e₁ v
  count-uses (backslide e e₁ x x₁) v = count-uses e v + count-uses e₁ v
  count-uses (logistic e) v = count-uses e v
  count-uses (bin x e e₁) v = count-uses e v + count-uses e₁ v
  count-uses (scaledown x e) v = count-uses e v
  count-uses (minus e) v = count-uses e v
  count-uses (let′ e e₁) v = count-uses e v + count-uses e₁ (there v)



module Syntax where
  open import Data.List as L using (List; []; _∷_)
  open import Ar hiding (sum; imapb)

  -- Convenience functions when writing expressions in the DSL
  -- In some sense we are faking HOAS using instance resolution.

  data Prefix : (Γ Δ : Ctx) → Set where
    instance
      zero : Prefix Γ Γ
      suc  : ⦃ Prefix Γ Δ ⦄ → Prefix Γ (Δ ▹ is)

  -- A term that can be lifted into larger contexts
  GE : Ctx → IS → Set
  GE Γ is = ∀ {Δ} → ⦃ Prefix Γ Δ ⦄ → E Δ is

  -- A variable that can be lifted into larger contexts
  GVar : Ctx → IS → Set
  GVar Γ is = ∀ {Δ} → ⦃ p : Prefix Γ Δ ⦄ → is ∈ Δ

  -- Lift var
  V : is ∈ Γ → GVar Γ is
  V v ⦃ p = zero ⦄ = v
  V v ⦃ p = suc  ⦄ = there (V v)

  -- Use GE GVar and V to define HOAS-style imap, imaps, and impab
  Imap : ∀ {Γ}
       → (GE (Γ ▹ ix s) (ix s) → E (Γ ▹ ix s) (ar p))
       → E Γ (ar (s ⊗ p))
  Imap f = imap (f λ {Δ} ⦃ p ⦄ → var (V v₀))

  Sum : ∀ {Γ}
       → (GE (Γ ▹ ix s) (ix s) → E (Γ ▹ ix s) (ar p))
       → E Γ (ar p)
  Sum f = sum (f λ {Δ} ⦃ p ⦄ → var (V v₀))

  Imaps : ∀ {Γ}
        → (GE (Γ ▹ ix s) (ix s) → E (Γ ▹ ix s) (ar unit))
        → E Γ (ar s)
  Imaps f = imaps (f λ {Δ} ⦃ p ⦄ → var (V v₀))

  Imapb : ∀ {Γ}
        → s * p ≈ q 
        → (GE (Γ ▹ ix s) (ix s) → E (Γ ▹ ix s) (ar p)) 
        → E Γ (ar q)
  Imapb p f = imapb p (f λ {Δ} ⦃ p ⦄ → var (V v₀))

  Let-syntax : ∀ {Γ}
      → (E Γ (ar s))
      → (GE (Γ ▹ (ar s)) (ar s) → E (Γ ▹ (ar s)) (ar p))
      → E Γ (ar p)
  Let-syntax x f = let′ x (f λ {Δ} ⦃ p ⦄ → var (V v₀))
  
  infixl 3 Let-syntax
  syntax Let-syntax e (λ x → e') = Let x := e In e'

  -- Extend context with a list of types
  -- (List is a context that grows to the left)
  ext : Ctx → List IS → Ctx
  ext Γ [] = Γ
  ext Γ (x ∷ l) = ext (Γ ▹ x) l

  -- Turn the list of IS into the following function:
  --   l = [a, b, c]
  --   X = X
  --   Γ = Γ
  --   ----------------------------
  --   GE Γ a → GE Γ b → GE Γ c → X
  lfunh : (l : List IS) (X : Set) (Γ : Ctx) → Set
  lfunh [] X Γ = X
  lfunh (a ∷ l) X Γ = GE Γ a → lfunh l X Γ

  -- Diagonalise lfunh:
  --   l = [a, b]
  --   Γ = Γ
  --   is = is
  --   ---------------------------------------------
  --   GE (ext Γ l) a → GE (ext Γ l) → E (ext Γ l) is
  lfun : (l : List IS)  (Γ : Ctx) (is : IS) → Set
  lfun l Γ τ = lfunh l (E (ext Γ l) τ) (ext Γ l)

  -- Compute GE from the variable in the non-extended context
  lvar : ∀ l → is ∈ Γ → GE (ext Γ l) is
  lvar [] v = var (V v)
  lvar (x ∷ l) v = lvar l (there v)

  -- Apply function to the corresponding variables of the context
  Lcon : ∀ l is Γ → (f : lfun l Γ is) → E (ext Γ l) is
  Lcon []      is Γ f = f
  Lcon (x ∷ l) is Γ f = Lcon l is (Γ ▹ x) (f (lvar l v₀))

module Primitives where

  open import Data.List as L using (List; []; _∷_)
  open import Data.Nat as ℕ using (ℕ; zero; suc)
  open import Function using (_$_; it; _∋_)
  open import Relation.Binary.PropositionalEquality
  open import Ar hiding (slide; selb)
  open Syntax
  open WkSub

  fromPrefix : Prefix Γ Δ → Γ ⊆ Δ
  fromPrefix zero = ⊆-eq
  fromPrefix (suc ⦃ p ⦄) = skip (fromPrefix p)
  
  wkp : Prefix Γ Δ → E Γ is → E Δ is
  wkp p = wk (fromPrefix p)

  ⟨_⟩ : E Γ is → GE Γ is
  ⟨_⟩ t {Δ} ⦃ p ⦄ = wkp p t
 
  conv : ∀ {Γ} → E Γ (ar r) → ⦃ s + p ≈ r ⦄ → E Γ (ar s) → ⦃ suc p ≈ u ⦄ 
       → E Γ (ar u)
  conv f ⦃ s+p ⦄ g ⦃ ss ⦄ 
    = Sum λ i → (slide i s+p ⟨ f ⟩ ss) ⊠ Imaps λ j → sels ⟨ g ⟩ i

  mconv : ⦃ s + p ≈ r ⦄ → (inp : E Γ (ar r)) (ws : E Γ (ar (u ⊗ s)))
          (bᵥ : E Γ (ar u)) → ⦃ suc p ≈ w ⦄ → E Γ (ar (u ⊗ w))
  mconv ⦃ sp ⦄ inp wᵥ bᵥ ⦃ su ⦄ = 
    Imap λ i → conv ⟨ inp ⟩ (sel ⟨ wᵥ ⟩ i) ⊞ Imaps λ _ → sels ⟨ bᵥ ⟩ i

  avgp₂ : ∀ m n → (a : E Γ (ar (m ℕ.* 2 ∷ n ℕ.* 2 ∷ []))) 
        → E Γ (ar (m ∷ n ∷ []))
  avgp₂ m n a =
    Imaps λ i → scaledown 4 $ Sum λ j → sels (selb it ⟨ a ⟩ i) j

  sqerr : (r o : E Γ (ar [])) → E Γ (ar [])
  sqerr r o = scaledown 2 ((r ⊞ (minus o)) ⊠ (r ⊞ (minus o)))

  meansqerr : (r o : E Γ (ar s)) → E Γ (ar [])
  meansqerr r o = Sum λ i → sqerr (sels ⟨ r ⟩ i) (sels ⟨ o ⟩ i) 

  cnn : E _ _
  cnn = Lcon (  ar (28 ∷ 28 ∷ []) ∷ ar (6 ∷ 5 ∷ 5 ∷ [])
              ∷ ar (6 ∷ [])       ∷ ar (12 ∷ 6 ∷ 5 ∷ 5 ∷ [])
              ∷ ar (12 ∷ [])      ∷ ar (10 ∷ 12 ∷ 1 ∷ 4 ∷ 4 ∷ [])
              ∷ ar (10 ∷ [])      ∷ ar (10 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ []) 
              --∷ ar (10 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ []) 
              ∷ [])
             --(ar (10 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ [])) ε
             (ar ([])) ε
        λ inp k₁ b₁ k₂ b₂ fc b target → 
        Let c₁₁ := mconv inp k₁ b₁  In
        Let c₁  := logistic c₁₁ In
        Let s₁  := (Imap {s = 6 ∷ []} λ i → avgp₂ 12 12 (sel c₁ i)) In
        Let c₂₁ := mconv s₁ k₂ b₂ In
        Let c₂  := logistic c₂₁ In
        Let s₂  := (Imap {s = 12 ∷ 1 ∷ []} λ i → avgp₂ 4 4 (sel c₂ i)) In
        Let o₁  := mconv s₂ fc b In
        Let o   := logistic o₁ In
        -- Mean squared error
        Let e   := meansqerr target o In
        e
        

            

module LangTest where
  open import Ar
  open import Data.List as L using (List; []; _∷_)
  open import Function
  open Syntax

  nested-inc : E (Γ ▹ ar (s ⊗ p) ▹ ar p) (ar (s ⊗ p))
  nested-inc {s = s} = imap {s = s} ((var v₁) ⊞ sel (var v₂) (var v₀)) 

  -- Test convenience
  
  _ : Prefix (Γ ▹ ar []) (Γ ▹ ar [] ▹ (ar (5 ∷ [])))
  _ = it

  _ : E Γ (ar (5 ∷ 5 ∷ []))
  _ = Imaps λ iv → sels zero iv 

  _ : E Γ (ar (5 ∷ 5 ∷ []))
  _ = Let x := zero In x ⊞ x

  _ : E _ _
  _ = Lcon (ar (5 ∷ []) ∷ ar [] ∷ []) (ar (5 ∷ [])) ε
      λ a x → Let b := a ⊞ a In
              Let c := (Imaps λ i → sel a i ⊠ x) In
              c ⊞ c

