{-# OPTIONS  --backtracking-instance-search #-} -- only needed for tests
module _ where

module _ where
  open import Data.Nat.Show using () renaming (show to show-nat)
  open import Data.List as L using (List; []; _∷_)
  open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
  open import Relation.Binary.PropositionalEquality
  open import Data.String
  open import Text.Printf
  open import Data.Unit
  open import Data.Product as Prod hiding (_<*>_)
  open import Data.Nat using (ℕ; zero; suc)
  open import Ar hiding (_++_; Ix)
  open import Lang
  open import Function

  open import Effect.Monad.State
  open import Effect.Monad using (RawMonad)
  open RawMonadState {{...}} -- public
  open RawMonad {{...}} -- public
  
  instance
    _ = monad
    _ = applicative
    _ = monadState

  data Ix : S → Set where 
    []  : Ix []
    _∷_ : String → Ix s → Ix (n ∷ s)

  Sem : IS → Set
  -- We have a context and a selectable part.
  -- For example, consider
  --   let x = 5 in imap λ i → x
  --
  -- for each i it returns "x", and the context (λ s → "let x = 5 in {s}")
  -- so we can tabulate arrays, yet select them as needed.
  -- Note, that for general selections into lets, such as
  --   sel (let x = e in e₁) i
  -- it is safe to translate this into (let x = e in sel e₁ i).
  -- While it is tempting to pre-select only those parts of e
  -- that are needed to compute (sel e₁ i), there is no easy
  -- way to do this for all cases.
  Sem (ar s) = (Ix s → State ℕ ((String → String) × String))
  Sem (ix s) = Ix s

  FEnv : Ctx → Set
  FEnv ε = ⊤
  FEnv (Γ ▹ is) = FEnv Γ × Sem is

  lookup : is ∈ Γ → FEnv Γ → Sem is
  lookup v₀ (ρ , e) = e
  lookup (there x) (ρ , e) = lookup x ρ

  --show-shape : S → String
  --show-shape s = printf "[%s]" $ intersperse ", " $ L.map show-nat s

  shape-args : S → String
  shape-args s = intersperse " " $ L.map show-nat s

  dim : S → ℕ
  dim s = L.length s

  fresh-var : ℕ → String
  fresh-var n = "x" ++ show-nat n
  
  fresh-ix : String → Ix s
  fresh-ix n = proj₂ (runState (go n) 0)
    where
      go : String → State ℕ (Ix s)
      go {[]} n = return []
      go {x ∷ s} n = do
        c ← get
        modify suc
        is ← go {s} n
        return (printf "%s_%u" n c ∷ is)

  iv : (s : S) → State ℕ (Ix s)
  iv s = do
    c ← get
    modify suc
    return (fresh-ix (fresh-var c))

  
  bop : Bop -> String
  bop plus = "F.+"
  bop mul = "F.*"

  show-array-type : S → String
  show-array-type [] = "f32"
  show-array-type s = printf "%sf32" $ intersperse "" $ L.map (printf "[%s]" ∘ show-nat) s

  _⊗ⁱ_ : Ix s → Ix p → Ix (s Ar.⊗ p)
  [] ⊗ⁱ js = js
  (i ∷ is) ⊗ⁱ js = i ∷ (is ⊗ⁱ js)
  
  splitⁱ : (ij : Ix (s Ar.⊗ p)) → Σ (Ix s) λ i → Σ (Ix p) λ j → i ⊗ⁱ j ≡ ij
  splitⁱ {[]} ij = [] , ij , refl
  splitⁱ {_ ∷ s} (x ∷ ij) with splitⁱ {s} ij
  ... | i , j , refl = (x ∷ i) , j , refl

  ix-curry : (Ix (s Ar.⊗ p) → X) → Ix s → Ix p → X
  ix-curry f i j = f (i ⊗ⁱ j)

  ix-uncurry : (Ix s → Ix p → X) → Ix (s Ar.⊗ p) → X
  ix-uncurry {s = s} f ij with splitⁱ {s} ij
  ... | i , j , refl = f i j

  ix-map : (String → String) → Ix s → Ix s
  ix-map f [] = []
  ix-map f (x ∷ i) = f x ∷ ix-map f i
  
  ix-zipwith : ((a b : String) → String) → Ix s → Ix s → Ix s
  ix-zipwith f [] [] = []
  ix-zipwith f (x ∷ i) (y ∷ j) = f x y ∷ ix-zipwith f i j


  ix-join : Ix s → String → String
  ix-join [] d = ""
  ix-join (x ∷ []) d = x
  ix-join {s = _ ∷ s} (x ∷ y ∷ xs) d = x ++ d ++ ix-join {s} (y ∷ xs) d

  ix-to-list : Ix s → List String
  ix-to-list [] = []
  ix-to-list (x ∷ xs) = x ∷ ix-to-list xs


  to-sel : Ix s → String → String
  to-sel i a = a ++ ix-join (ix-map (printf "[%s]") i) ""


  to-imap : (s : S) → (i : Ix s) → (e : String) → String
  to-imap s i e = printf "(imap%u %s (\\ %s -> %s))" 
                   (dim s) (shape-args s) (ix-join i " ")
                   e
  --to-sum : (s : S) → (i : Ix s) → (e : String) → String
  --to-sum [] i e = e
  --to-sum s  i e = printf "(sum%ud %s)" (dim s) (to-imap s i e)

  to-sum : (s : S) → (i : Ix s) → (e : String) → String
  to-sum [] i e = e
  to-sum s  i e = printf "(isum%u %s (\\ %s -> %s))" (dim s) (shape-args s)
                         (ix-join i " ") e 

  ix-plus : s + p ≈ r → (suc_≈_ p u) 
          → (i : Ix s)
          → (j : Ix u)
          → Ix r
  ix-plus []  [] [] [] = []
  ix-plus (cons ⦃ _ ⦄ ⦃ s+p ⦄) (cons ⦃ _ ⦄ ⦃ sp ⦄) (i ∷ is) (j ∷ js) =
    printf "(%s + %s)" i j ∷ ix-plus s+p sp is js

  ix-eq : (i j : Ix s) → String
  ix-eq i j = ix-join (ix-zipwith (printf "(%s == %s)") i j) " && " 

  ix-minus : s + p ≈ r → (suc_≈_ p u)
           → (i : Ix r)
           → (j : Ix s)
           → Ix u
  ix-minus []  [] [] [] = []
  ix-minus (cons ⦃ _ ⦄ ⦃ s+p ⦄) (cons ⦃ _ ⦄ ⦃ sp ⦄) (i ∷ is) (j ∷ js) =
    printf "(%s - %s)" i j ∷ ix-minus s+p sp is js


  to-div-mod : s * p ≈ q → Ix q 
             → Ix s × Ix p 
  to-div-mod []   [] = [] , []
  to-div-mod (cons {n = n} ⦃ _ ⦄ ⦃ eq ⦄) (x ∷ i) =
    -- (i: Fin (m*n)) → [p,q] : Fin [m,n] => p=i/n q=i%n
    Prod.map (printf "(%s / %s)" x (show-nat n) ∷_)
             (printf "(%s %% %s)" x (show-nat n) ∷_)
             (to-div-mod eq i)

  from-div-mod : s * p ≈ q 
               → Ix s → Ix p 
               → Ix q
  from-div-mod [] [] [] = []
  from-div-mod (cons {n = n} ⦃ _ ⦄ ⦃ eq ⦄) (i ∷ is) (j ∷ js) =
    -- (i : Fin m) (j : Fin n)  (k : Fin (m * n))  k = i * n + j  
    printf "((%s * %s) + %s)" i (show-nat n) j
    ∷ from-div-mod eq is js

  -- Generate a new name for an external array
  mkar : String → Ix s → State ℕ ((String → String) × String)
  mkar a i = return (id , to-sel i a)

  to-fut : E Γ is → FEnv Γ → State ℕ (Sem is)

  to-str : E Γ (ar s) → FEnv Γ → State ℕ String
  to-str {s = []} e ρ = do
    p ← to-fut e ρ
    f , b ← p []
    return (f b)
  to-str {s = s} e ρ = do
    p ← to-fut e ρ
    i ← iv s
    f , b ← p i
    return (f (to-imap s i b))
    --do
    --p ← to-fut e ρ
    --i ← iv s
    --body ← p i
    --return (printf "imap%u %s λ %s -> %s" 
    --               (dim s) (shape-args s) (ix-join i " ")
    --               body)

  to-fut (var x) ρ = return $ lookup x ρ
  to-fut zero ρ = return (λ _ → return (id , "zero"))
  to-fut one ρ = return (λ _ → return (id , "one"))
  to-fut (imaps e) ρ = return λ i → do
     b ← to-fut e (ρ , i)
     f , b′ ← b []
     return (id , f b′)

     --λ i → let k = to-fut e (ρ , i) ; r = (_$ []) <$> k in join r
  to-fut (sels e e₁) ρ = do
     a ← to-fut e ρ
     x ← to-fut e₁ ρ
     return λ i → do
       f , a′ ← a x
       return (f , a′)
     --return λ _ → f x
  to-fut (imap {s = s} e) ρ = 
    return $ ix-uncurry {s} λ i j → do
      b ← to-fut e (ρ , i)
      f , b′ ← b j
      return (id , f b′)
  to-fut (sel e e₁) ρ = do
     a ← to-fut e ρ
     i ← to-fut e₁ ρ
     return λ j → do
       f , a′ ← ix-curry a i j
       return (f , a′)
  to-fut (E.imapb x e) ρ = return λ i → do
    let j , k = to-div-mod x i
    b ← to-fut e (ρ , j)
    f , b′ ← b k
    return (id , f b′)
  to-fut (E.selb x e e₁) ρ = do
    a ← to-fut e ρ
    i ← to-fut e₁ ρ
    return λ j → do
      let k = from-div-mod x i j
      f , a′ ← a k
      return (f , a′)
  to-fut (E.sum {s = s} e) ρ = do
    i ← iv s
    b ← to-fut e (ρ , i)
    return λ j → do
      f , b′ ← b j
      return (id , to-sum s i (f b′))
  to-fut (zero-but e e₁ e₂) ρ = do
    i ← to-fut e ρ
    j ← to-fut e₁ ρ
    a ← to-fut e₂ ρ
    return λ k → do
      f , a′ ← a k
      -- move context under if, so that we do not evaluate stuff that we do not need.
      return (id , printf "(if (%s) then %s else zero)" (ix-eq i j) (f a′))
  to-fut (E.slide e x e₁ x₁) ρ = do
    i ← to-fut e ρ
    a ← to-fut e₁ ρ
    return λ j → do
      f , a′ ← a (ix-plus x x₁ i j)
      return (f , a′)
  to-fut (E.backslide {u = u} e e₁ x x₁) ρ = do
    i ← to-fut e ρ
    a ← to-fut e₁ ρ
    return λ j → do
      let j-i = ix-minus x₁ x j i
      let j≥i = intersperse " && " (L.zipWith (printf "%s >= %s") (ix-to-list j) (ix-to-list i)) 
      let j-i<u = intersperse " && " (L.zipWith (printf "%s < %u") (ix-to-list j-i) u)

      f , a′ ← a j-i
      -- Again, move the context under if.
      let b = printf "if (%s && %s) then %s else zero"
                     j≥i j-i<u (f a′)

      return (id , b)
  to-fut (logistic e) ρ = do
    a ← to-fut e ρ
    return λ i → do
      f , a′ ← a i
      return (f ,  printf "(logistics %s)" a′)
  to-fut (e ⊞ e₁) ρ = do
    l ← to-fut e ρ
    r ← to-fut e₁ ρ
    return λ i → do
      f , l′ ← l i
      g , r′ ← r i
      return (f ∘ g , printf "(%s F.+ %s)" l′ r′)

  to-fut (e ⊠ e₁) ρ = do
    l ← to-fut e ρ
    r ← to-fut e₁ ρ
    return λ i → do
      f , l′ ← l i
      g , r′ ← r i
      return (f ∘ g , printf "(%s F.* %s)" l′ r′)

  to-fut (scaledown x e) ρ = do
    a ← to-fut e ρ
    return λ i → do
      f , a′ ← a i
      return (f ,  printf "(%s F./ fromi64 %s)" a′ (show-nat x))


  to-fut (minus e) ρ = do
    a ← to-fut e ρ
    return λ i → do
      f , a′ ← a i
      return (f ,  printf "(F.neg %s)" a′)

  to-fut (let′ e e₁) ρ = do
    c ← get
    modify suc
    let n = fresh-var c 
    b ← to-fut e₁ (ρ , (mkar n))
    return λ i → do
      x ← to-str e ρ
      f , b′ ← b i
      return (printf "(let %s = %s\nin %s)" n x ∘ f ,  b′)







module Test where
  open import Relation.Binary.PropositionalEquality
  open import Data.List
  open import Data.Product
  open import Data.Nat
  open import Data.String
  open import Function
  open import Lang
  open import Ar
  open Syntax

  open import Effect.Monad.State
  --open import Effect.Monad using (RawMonad)
  --open RawMonadState {{...}} -- public
  --open RawMonad {{...}} -- public
  
  instance
    _ = monad
    _ = applicative
    _ = monadState

  infixl 5 _,,_
  _,,_ = _,′_

  test-e : E _ _
  test-e = Lcon (ar (5 ∷ 5 ∷ []) ∷ ix (5 ∷ 5 ∷ []) ∷ []) (ar ([])) ε
           --λ a → Imaps λ i → sels a i ⊞ sels a i
           λ a j → sel (Let x := a ⊞ a In x ⊞ a) j
                 --Let z := zero {s = []} In
                 --Let a :=
                 -- (Imaps λ i → (Let x := zero In x ⊞ x)
                 --            ⊞ (Let y := sels a i In y ⊞ y))
                 --In sels a j


  test-s : String
  test-s = proj₂ (runState (to-str test-e ((_ , mkar "a"), ("i1" ∷ "i2" ∷ []))) 0)

  loss-e : E _ _
  loss-e = Lcon (ar (5 ∷ []) ∷ ar (5 ∷ []) ∷ []) (ar (5 ∷ [])) ε
           λ inp out → Let r := inp ⊠ inp In
                       {- err -} scaledown 2 ((r ⊞ (minus out)) ⊠ (r ⊞ (minus out)))

  loss-s : String
  loss-s = proj₂ (runState (to-str loss-e ((_ , mkar "inp") , mkar "out" )) 0)

  conv-e : E _ _
  conv-e = Lcon (ar (5 ∷ 5 ∷ []) ∷ ar (2 ∷ 2 ∷ []) ∷ []) (ar (4 ∷ 4 ∷ [])) ε
           λ img k1 → Primitives.conv img k1

  
  conv-s : String
  conv-s = proj₂ (runState (to-str conv-e (_ ,, mkar "img" ,, mkar "k1")) 0)

  --c1-s : String
  --c1-s = proj₂ $ runState (to-str (Primitives.compc1) (((_ , mkar "inp") , mkar "k1") , mkar "b1")) 0


  --λ inp k₁ b₁ k₂ b₂ fc b →
  cnn-s : String
  cnn-s = proj₂ 
        $ runState (to-str (Primitives.cnn)
                           (_ ,, mkar "inp" ,, mkar "k1" ,, mkar "b1"
                              ,, mkar "k2"  ,, mkar "b2" ,, mkar "fc"
                              ,, mkar "b" ,, mkar "target"  )) 0
