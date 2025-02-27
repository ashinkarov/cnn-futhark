--{-# OPTIONS --overlapping-instances #-}
open import Data.Nat using (zero; suc; ℕ; _+_; _*_; _≤_; s≤s; z≤n; _<_)
open import Data.Nat.Properties using (+-mono-≤; ≤-step; ≤-pred; _≟_; +-comm; +-suc)
open import Data.Fin as F using (zero; suc; Fin; combine; remQuot; fromℕ<; inject+; splitAt)
open import Data.Fin.Properties using (suc-injective; toℕ<n; splitAt-inject+)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product as Prod using (∃; _,_; _×_; proj₁; proj₂)

open import Data.List as L using (List; []; _∷_)
open import Data.List.Properties using (∷ʳ-injective; ++-cancelʳ)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty
open import Function

_∙_ :  ∀{l}{A : Set l}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ∙ refl = refl
infixr 4 _∙_

module _ where
module _ where
  S = List ℕ
  P = All Fin

  variable
    m n k : ℕ
    s p q r u w : S
    X Y Z : Set

  _⊗_ = L._++_
  _++_ : P s → P p → P (s ⊗ p)
  [] ++ js = js
  (px ∷ is) ++ js = px ∷ (is ++ js)

  _≟ˢ_ : (a b : S) → Dec (a ≡ b)
  [] ≟ˢ [] = yes refl
  [] ≟ˢ (_ ∷ p) = no λ ()
  (_ ∷ s) ≟ˢ [] = no λ ()
  (m ∷ s) ≟ˢ (n ∷ p) with m ≟ n | s ≟ˢ p
  ... | yes refl | yes refl = yes refl
  ... | yes refl | no ¬p = no λ { refl → ¬p refl }
  ... | no ¬p | _ = no λ { refl → ¬p refl }

  ++-[]₁ : s ⊗ p ≡ [] → s ≡ []
  ++-[]₁ {[]} {p} eq = refl

  ++-neutʳ : s ⊗ [] ≡ s
  ++-neutʳ {[]} = refl
  ++-neutʳ {x ∷ s} = cong (x ∷_) ++-neutʳ

  Ar : S → Set → Set
  Ar s X = P s → X
  
  K : X → Ar s X
  K x i = x
  
  map : (X → Y) → Ar s X → Ar s Y
  map f a i = f (a i)
  
  zipWith : (X → Y → Z) → Ar s X → Ar s Y → Ar s Z
  zipWith f a b i = f (a i) (b i)

  nest : Ar (s ⊗ p) X → Ar s (Ar p X)
  nest a i j = a (i ++ j)
  
  splitP : P (s ⊗ p) → P s × P p
  splitP {s = []}    is = [] , is
  splitP {s = x ∷ s} (i ∷ is) = Prod.map₁ (i ∷_) (splitP is)

  splitP-eq : (i : P (s ⊗ p)) → i ≡ _++_ {s = s}{p} (splitP i .proj₁) (splitP i .proj₂)
  splitP-eq {[]} i = refl
  splitP-eq {x ∷ s} (px ∷ i) = cong (px ∷_) (splitP-eq {s = s} i)

  splitP-proj₁ : {i : P s}{j : P p} → splitP (i ++ j) .proj₁ ≡ i
  splitP-proj₁ {i = []} = refl
  splitP-proj₁ {i = px ∷ i} = cong (px ∷_) splitP-proj₁

  splitP-proj₂ : {i : P s}{j : P p} → splitP (i ++ j) .proj₂ ≡ j
  splitP-proj₂ {i = []} = refl
  splitP-proj₂ {i = px ∷ i} = splitP-proj₂ {i = i}

  unnest : Ar s (Ar p X) → Ar (s ⊗ p) X
  unnest a i = Prod.uncurry a (splitP i) 

  ιsuc : P (n ∷ []) → P (suc n ∷ [])
  ιsuc (i ∷ []) = suc i ∷ []

  sum₁ : (X → X → X) → X → Ar (n ∷ []) X → X
  sum₁ {n = zero}   f ε a = ε
  sum₁ {n = suc n}  f ε a = f (a (zero ∷ [])) (sum₁ f ε (a ∘ ιsuc))
  
  sum : (X → X → X) → X → Ar s X → X
  sum {s = []}    f ε a = f ε (a [])
  sum {s = x ∷ s} f ε a = sum₁ f ε $ map (sum f ε) (nest a)

  sum₁-cong : (f : X → X → X) (e : X) → ∀ {a b : Ar (n ∷ []) X} → (∀ i → a i ≡ b i) 
            → sum₁ f e a ≡ sum₁ f e b 
  sum₁-cong {n = zero} f e pf = refl
  sum₁-cong {n = suc n} f e pf = cong₂ f (pf (zero ∷ [])) (sum₁-cong f e (λ i → pf (ιsuc i)))

  sum-cong : (f : X → X → X) (e : X) → ∀ {a b : Ar s X} → (∀ i → a i ≡ b i) → sum f e a ≡ sum f e b 
  sum-cong {s = []} f e pf = cong (f e) (pf _)
  sum-cong {s = x ∷ s} f e {a}{b} pf = sum₁-cong f e (λ j → sum-cong f e (λ i → pf (j ++ i))) 

  sum₁-inv : (f : X → X → X) (e : X) → {a : Ar (n ∷ []) (Ar p X)}
           → (∀ k → sum₁ (zipWith f) (K e) a k ≡ map (sum₁ f e) (λ i j → a j i) k)
  sum₁-inv {n = zero} f e {a} _ = refl
  sum₁-inv {n = suc n} f e {a} k = cong (f (a (zero ∷ []) k)) (sum₁-inv f e {a ∘ ιsuc} k)


  sum-inv : (f : X → X → X) (e : X) → {a : Ar s (Ar p X)} 
          → (∀ k → sum (zipWith f) (K e) a k ≡ map (sum f e) (λ i j → a j i) k)
  sum-inv {s = []} f e {a} _ = refl
  sum-inv {s = x ∷ s} f e {a} k = 
    sum₁-inv f e {λ i → sum (zipWith f) (K e) (λ j → a (i ++ j))} k
    ∙ sum₁-cong f e {(λ j → sum (zipWith f) (K e) (λ i → a (j ++ i)) k)} 
              (λ i → sum-inv f e {λ j → a (i ++ j)} k)

  _≟ₚ_ : (i j : P s) → Dec (i ≡ j)
  _≟ₚ_ {[]} [] [] = yes refl
  _≟ₚ_ {x ∷ s} (i ∷ is) (j ∷ js) with i F.≟ j
  ... | no ¬p = no λ { refl → ¬p refl }
  ... | yes refl with is ≟ₚ js
  ... | no ¬q = no λ { refl → ¬q refl }
  ... | yes refl = yes refl

  inject-left : Fin (suc m) → Fin (suc (n + m))
  inject-left {m} {n} i rewrite +-comm n m  = inject+ _ i
  
  split-inj₁ : (i : Fin (m + n)) (k : Fin m) → splitAt m i ≡ inj₁ k → inject+ _ k ≡ i
  split-inj₁ {suc m} zero .zero refl = refl
  split-inj₁ {suc m} (suc i) zero p with splitAt m i | inspect (splitAt m) i
  split-inj₁ {suc m} (suc i) zero () | inj₁ x | [ r ]
  split-inj₁ {suc m} (suc i) zero () | inj₂ y | [ r ]
  split-inj₁ {suc m} (suc i) (suc k) p with splitAt m i | inspect (splitAt m) i
  split-inj₁ {suc m} (suc i) (suc .x) refl | inj₁ x | [ r ] = cong suc (split-inj₁ i x r)
  
  inj₁₂ : {A B : Set}{x : A}{y : B} → inj₁ x ≡ inj₂ y → ⊥
  inj₁₂ ()
  
  _⊕_ : Fin m → Fin (1 + n) → Fin (m + n)
  zero   ⊕ j = inject-left j
  suc i  ⊕ j = suc (i ⊕ j)
  
  _⊝_ : (i : Fin (m + n)) (j : Fin m)
      → Dec (∃ λ k → j ⊕ k ≡ i)
  _⊝_ {suc m} {n} i zero rewrite +-comm m n with splitAt (suc n) i | inspect (splitAt (suc n)) i
  ... | inj₁ k | [ r ] = yes (k , split-inj₁ i k r)
  ... | inj₂ k | [ r ] = no reason
    where
      reason : _
      reason (k , refl) rewrite splitAt-inject+ (suc n) m k = inj₁₂ r
  zero ⊝ suc j = no λ { (k , ()) }
  suc i ⊝ suc j with i ⊝ j
  ... | yes (k , p) = yes (k , cong suc p)
  ... | no ¬p = no λ { (k , p) → ¬p (k , suc-injective p) } 

  inject-left-zero : inject-left {m} {n} zero ≡ zero
  inject-left-zero {m} {n} rewrite +-comm n m = refl

  suc-not-zero : {i : Fin m} → _≡_ {A = Fin (suc m)} (suc i) zero → ⊥
  suc-not-zero ()

  inject-left-suc : ∀ (i : Fin m) → inject-left {m} {n} (suc i) ≡ zero → ⊥
  inject-left-suc {m} {n} i p rewrite +-comm n m = suc-not-zero p

  zero-suc-⊥ : ∀ {i : Fin n} → _≡_ {A = Fin (suc n)} zero (suc i) → ⊥
  zero-suc-⊥ ()

  Ix : ℕ → Set
  Ix m = P (m ∷ [])

  Vec : ℕ → Set → Set
  Vec n X = Ar (n ∷ []) X

  slide₁ : Ix m → Vec (m + n) X → Vec (1 + n) X
  slide₁ (i ∷ []) v (j ∷ []) = v ((i ⊕ j) ∷ [])

  conv₁ : Vec (m + n) ℕ → Vec m ℕ → Vec (1 + n) ℕ
  conv₁ a w = sum (zipWith _+_) (K 0) (λ i → map (w i *_) (slide₁ i a))
 
  data Pointw₂ (R : (a b : ℕ) → Set) : (a b : S) → Set where
   instance
    []  : Pointw₂ R [] []
    cons : ⦃ R m n ⦄ → ⦃ Pointw₂ R s p ⦄ → Pointw₂ R (m ∷ s) (n ∷ p) 

  data Pointw₃ (R : (a b c : ℕ) → Set) : (a b c : S) → Set where
   instance
    []  : Pointw₃ R [] [] []
    cons : ⦃ R m n k ⦄ → ⦃ Pointw₃ R s p q ⦄ → Pointw₃ R (m ∷ s) (n ∷ p) (k ∷ q)
  
  _+_≈_ : (s p q : S) → Set
  s + p ≈ q = Pointw₃ (λ x y z → x + y ≡ z) s p q

  _*_≈_ : (s p q : S) → Set
  s * p ≈ q = Pointw₃ (λ x y z → x * y ≡ z) s p q

  suc_≈_ : (s p : S) → Set
  suc s ≈ p = Pointw₂ (λ x y → suc x ≡ y) s p

  _⊕′_ : P s → P u → suc p ≈ u → s + p ≈ r → P r
  (i ⊕′ j) [] [] = j
  ((i ∷ is) ⊕′ (j ∷ js)) (cons ⦃ refl ⦄ ⦃ sp ⦄) (cons ⦃ refl ⦄ ⦃ s+p ⦄)
    = (i ⊕ j) ∷ (is ⊕′ js) sp s+p

  _⊝′_ : (i : P r) (j : P s) (su : suc p ≈ u) (sp : s + p ≈ r) → Dec (∃ λ k → (j ⊕′ k) su sp ≡ i)
  ([] ⊝′ j) [] [] = yes ([] , refl)
  ((i ∷ is) ⊝′ (j ∷ js)) (cons ⦃ refl ⦄ ⦃ sp ⦄) (cons ⦃ refl ⦄ ⦃ s+p ⦄) 
        with i ⊝ j
  ... | no ¬p = no λ { ((k ∷ _) , refl) → ¬p (k , refl) }
  ... | yes (k , p) with (is ⊝′ js) sp s+p
  ... | no ¬q = no λ { ((_ ∷ xs) , refl) → ¬q (xs , refl) }
  ... | yes (ks , q) = yes (k ∷ ks , cong₂ _∷_ p q)

  slide : P s → s + p ≈ r → Ar r X → suc p ≈ u → Ar u X
  slide i pl a su j = a ((i ⊕′ j) su pl)

  backslide : P s → Ar u X → suc p ≈ u → (def : X) → s + p ≈ r → Ar r X
  backslide i a su def pl j with ((j ⊝′ i) su pl)
  ... | yes (k , _)  = a k
  ... | _            = def

  ix-div : P q → s * p ≈ q → P s
  ix-div is [] = is
  ix-div (i ∷ is) (cons ⦃ refl ⦄ ⦃ pf ⦄) 
    = Prod.proj₁ (F.remQuot _ i) ∷ ix-div is pf

  ix-mod : P q → s * p ≈ q → P p
  ix-mod is [] = is
  ix-mod (i ∷ is) (cons {m = m} ⦃ refl ⦄ ⦃ pf ⦄)
    = Prod.proj₂ (F.remQuot {m} _ i) ∷ ix-mod is pf

  ix-combine : P s → P p → s * p ≈ q → P q
  ix-combine i j [] = j
  ix-combine (i ∷ is) (j ∷ js) (cons ⦃ refl ⦄ ⦃ ps ⦄) 
    = F.combine i j ∷ ix-combine is js ps
  
  selb : Ar q X → p * s ≈ q → P p → Ar s X
  selb a p i j = a (ix-combine i j p)

  imapb : Ar s (Ar p X) → s * p ≈ q → Ar q X
  imapb a p i = a (ix-div i p) (ix-mod i p)

  slide-cong : {i j : P s} (_ : i ≡ j) (pf₁ : s + p ≈ r) {a b : Ar r X} (pf₂ : suc p ≈ u)
             → (∀ i → a i ≡ b i) → (∀ k → slide i pf₁ a pf₂ k ≡ slide j pf₁ b pf₂ k)
  slide-cong refl pf₁ pf₂ ab k = ab ((_ ⊕′ k) pf₂ pf₁)


  backslide-cong : {i j : P s} (_ : i ≡ j) {a b : Ar u X} (_ : ∀ k → a k ≡ b k)
                   (su : suc p ≈ u) (def : X) (pl : s + p ≈ r)
                 → ∀ k → backslide i a su def pl k ≡ backslide j b su def pl k
  backslide-cong {i = i} refl ab su def pl k with ((k ⊝′ i) su pl)
  ... | yes (t , _) = ab t
  ... | no _ = refl

  map-cong : (f : X → Y) {a b : Ar s X} (_ : ∀ i → a i ≡ b i)
           → ∀ k → map f a k ≡ map f b k
  map-cong f ab k = cong f (ab k)

  zipWith-cong : (f : X → Y → Z) {a b : Ar s X} (_ : ∀ i → a i ≡ b i)
                 {c d : Ar s Y} (_ : ∀ i → c i ≡ d i)
               → ∀ k → zipWith f a c k ≡ zipWith f b d k
  zipWith-cong f ab cd k = cong₂ f (ab k) (cd k)


module ArTests where
  imap : (s : S) → (P s → X) → Ar s X
  imap s f = f

  _ : sum _+_ 0 (imap (5 ∷ 6 ∷ []) (const 1)) ≡ 30
  _ = refl
  
  -- Test auto-seatch
  _ : (3 ∷ 3 ∷ []) + (5 ∷ 5 ∷ []) ≈ (8 ∷ 8 ∷ [])
  _ = it

  _ : suc (4 ∷ 4 ∷ []) ≈ (5 ∷ 5 ∷ [])
  _ = it

