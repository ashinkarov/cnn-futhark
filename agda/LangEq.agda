
module _ where
  open import Ar hiding (sum; slide; backslide; imapb; selb)
  open import Relation.Binary.PropositionalEquality
  open import Data.Product
  open import Data.Nat using (ℕ; zero; suc; _≟_)
  open import Data.List as L
  open import Data.List.Properties as L
  open import Relation.Nullary
  open import Function
  open import Lang
  open import Ar

  -- Equality of types
  _≟ⁱ_ : (a b : IS) → Dec (a ≡ b)
  ix x ≟ⁱ ix y with x ≟ˢ y
  ... | no ¬p = no λ { refl → ¬p refl }
  ... | yes refl = yes refl
  ix x ≟ⁱ ar y = no λ ()
  ar x ≟ⁱ ix y = no λ ()
  ar x ≟ⁱ ar y with x ≟ˢ y
  ... | no ¬p = no λ { refl → ¬p refl }
  ... | yes refl = yes refl

  _≟ᵒ_ : (a b : Bop) → Dec (a ≡ b)
  plus ≟ᵒ plus = yes refl
  plus ≟ᵒ mul = no λ ()
  mul ≟ᵒ plus = no λ ()
  mul ≟ᵒ mul = yes refl
  
  isVar : (e : E Γ is) → Dec (∃ λ v → e ≡ var v)
  isVar (var x) = yes (x , refl)
  isVar zero = no λ ()
  isVar one = no λ ()
  isVar (imaps e) = no λ ()
  isVar (sels e e₁) = no λ ()
  isVar (imap e) = no λ ()
  isVar (sel e e₁) = no λ ()
  isVar (imapb x e) = no λ ()
  isVar (selb x e e₁) = no λ ()
  isVar (E.sum e) = no λ ()
  isVar (zero-but e e₁ e₂) = no λ ()
  isVar (slide e x e₁ x₁) = no λ ()
  isVar (backslide e e₁ x x₁) = no λ ()
  isVar (logistic e) = no λ ()
  isVar (bin x e e₁) = no λ ()
  isVar (scaledown x e) = no λ ()
  isVar (minus e) = no λ ()
  isVar (let′ e e₁) = no λ ()

  isZero : (e : E Γ (ar s)) → Dec (e ≡ zero)
  isZero zero = yes refl 
  isZero (var x) = no  λ ()
  isZero one = no λ ()
  isZero (imaps e) = no λ ()
  isZero (sels e e₁) = no λ ()
  isZero (imap e) = no λ ()
  isZero (sel e e₁) = no λ ()
  isZero (E.imapb x e) = no λ ()
  isZero (E.selb x e e₁) = no λ ()
  isZero (E.sum e) = no λ ()
  isZero (zero-but e e₁ e₂) = no λ ()
  isZero (E.slide e x e₁ x₁) = no λ ()
  isZero (E.backslide e e₁ x x₁) = no λ ()
  isZero (logistic e) = no λ ()
  isZero (bin x e e₁) = no λ ()
  isZero (scaledown x e) = no λ ()
  isZero (minus e) = no λ ()
  isZero (let′ e e₁) = no λ ()

  isOne : (e : E Γ (ar s)) → Dec (e ≡ one)
  isOne zero = no λ () 
  isOne (var x) = no λ ()
  isOne one = yes refl
  isOne (imaps e) = no λ ()
  isOne (sels e e₁) = no λ ()
  isOne (imap e) = no λ ()
  isOne (sel e e₁) = no λ ()
  isOne (E.imapb x e) = no λ ()
  isOne (E.selb x e e₁) = no λ ()
  isOne (E.sum e) = no λ ()
  isOne (zero-but e e₁ e₂) = no λ ()
  isOne (E.slide e x e₁ x₁) = no λ ()
  isOne (E.backslide e e₁ x x₁) = no λ ()
  isOne (logistic e) = no λ ()
  isOne (bin x e e₁) = no λ ()
  isOne (scaledown x e) = no λ ()
  isOne (minus e) = no λ ()
  isOne (let′ e e₁) = no λ ()

  isImap : (e : E Γ (ar q)) 
         → Dec (∃₂ λ s p 
                → Σ (s L.++ p ≡ q) λ eq → ∃ λ u → subst (E Γ ∘ ar) (sym eq) e ≡ imap {s = s} u)
  isImap (var x) = no λ { (_ , _ , refl , _ , ()) }
  isImap zero = no λ { (_ , _ , refl , _ , ()) }
  isImap one = no λ { (_ , _ , refl , _ , ()) }
  isImap (imaps e) = no λ { (_ , _ , refl , _ , ()) }
  isImap (sels e e₁) = no λ { ([] , [] , refl , _ , ())  }
  isImap (imap e) = yes (_ , _ , refl , e , refl)
  isImap (sel e e₁) = no λ { (_ , _ , refl , _ , ()) }
  isImap (E.imapb x e) = no λ { (_ , _ , refl , _ , ()) }
  isImap (E.selb x e e₁) = no λ { (_ , _ , refl , _ , ()) }
  isImap (E.sum e) = no λ { (_ , _ , refl , _ , ()) }
  isImap (zero-but e e₁ e₂) = no λ { (_ , _ , refl , _ , ()) }
  isImap (E.slide e x e₁ x₁) = no λ { (_ , _ , refl , _ , ()) }
  isImap (E.backslide e e₁ x x₁) = no λ { (_ , _ , refl , _ , ()) }
  isImap (logistic e) = no λ { (_ , _ , refl , _ , ()) }
  isImap (bin x e e₁) = no λ { (_ , _ , refl , _ , ()) }
  isImap (scaledown x e) = no λ { (_ , _ , refl , _ , ()) }
  isImap (minus e) = no λ { (_ , _ , refl , _ , ()) }
  isImap (let′ e e₁) = no λ { (_ , _ , refl , _ , ()) }


  isImaps : (e : E Γ (ar s)) → Dec (∃ λ u → e ≡ imaps u)
  isImaps (var x) = no λ ()
  isImaps zero = no λ ()
  isImaps one = no λ ()
  isImaps (imaps e) = yes (e , refl)
  isImaps (sels e e₁) = no λ ()
  isImaps (imap e) = no λ ()
  isImaps (sel e e₁) = no λ ()
  isImaps (E.imapb x e) = no λ ()
  isImaps (E.selb x e e₁) = no λ ()
  isImaps (E.sum e) = no λ ()
  isImaps (zero-but e e₁ e₂) = no λ ()
  isImaps (E.slide e x e₁ x₁) = no λ ()
  isImaps (E.backslide e e₁ x x₁) = no λ ()
  isImaps (logistic e) = no λ ()
  isImaps (bin x e e₁) = no λ ()
  isImaps (scaledown x e) = no λ ()
  isImaps (minus e) = no λ ()
  isImaps (let′ e e₁) = no λ ()

  isZeroBut : (e : E Γ (ar p)) → Dec (∃₂ λ s i → ∃₂ λ j u → e ≡ zero-but {s = s} i j u)
  isZeroBut (var x) = no λ ()
  isZeroBut zero = no λ ()
  isZeroBut one = no λ ()
  isZeroBut (imaps e) = no λ ()
  isZeroBut (sels e e₁) = no λ ()
  isZeroBut (imap e) = no λ ()
  isZeroBut (sel e e₁) = no λ ()
  isZeroBut (E.imapb x e) = no λ ()
  isZeroBut (E.selb x e e₁) = no λ ()
  isZeroBut (E.sum e) = no λ ()
  isZeroBut (zero-but e e₁ e₂) = yes (_ , e , e₁ , e₂ , refl)
  isZeroBut (E.slide e x e₁ x₁) = no λ ()
  isZeroBut (E.backslide e e₁ x x₁) = no λ ()
  isZeroBut (logistic e) = no λ ()
  isZeroBut (bin x e e₁) = no λ ()
  isZeroBut (scaledown x e) = no λ ()
  isZeroBut (minus e) = no λ ()
  isZeroBut (let′ e e₁) = no λ ()

  isSels : (e : E Γ (ar p)) (s : S) → Dec (Σ (p ≡ []) λ eq → ∃₂ λ t u → subst (E Γ ∘ ar) eq e ≡ sels {s = s} t u) 
  isSels (var x) s = no λ { (refl , _ , _ , ()) }
  isSels zero s = no λ { (refl , _ , _ , ()) }
  isSels one s = no λ { (refl , _ , _ , ()) }
  isSels (imaps e) s = no λ { (refl , _ , _ , ()) }
  isSels (sels {s = s′} e e₁) s with s′ ≟ˢ s
  ... | no ¬p = no λ { (refl , t , u , refl) → ¬p refl }
  ... | yes refl = yes (refl , e , e₁ , refl)
  isSels (imap {s = s} e) s′ = no foo
    where foo : _
          foo (eq , t , u , x) with ++-[]₁ {s = s} eq
          foo (eq , t , u , x) | rr rewrite rr | eq with x
          ... | ()
  isSels (sel e e₁) s = no λ { (refl , _ , _ , ()) }
  isSels (E.imapb x e) s = no λ { (refl , _ , _ , ()) }
  isSels (E.selb x e e₁) s = no λ { (refl , _ , _ , ()) }
  isSels (E.sum e) s = no λ { (refl , _ , _ , ()) }
  isSels (zero-but e e₁ e₂) s = no λ { (refl , _ , _ , ()) }
  isSels (E.slide e x e₁ x₁) s = no λ { (refl , _ , _ , ()) }
  isSels (E.backslide e e₁ x x₁) s = no λ { (refl , _ , _ , ()) }
  isSels (logistic e) s = no λ { (refl , _ , _ , ()) }
  isSels (bin x e e₁) s = no λ { (refl , _ , _ , ()) }
  isSels (scaledown x e) s = no λ { (refl , _ , _ , ()) }
  isSels (minus e) s = no λ { (refl , _ , _ , ()) }
  isSels (let′ e e₁) s = no λ { (refl , _ , _ , ()) }

  isSel :  (e : E Γ (ar p)) → Dec (∃ λ s → ∃₂ λ t u → e ≡ sel {s = s}{p} t u)
  isSel (var x) = no λ { (_ , _ , _ , ()) }
  isSel zero = no λ { (_ , _ , _ , ()) }
  isSel one = no λ { (_ , _ , _ , ()) }
  isSel (imaps e) = no λ { (_ , _ , _ , ()) }
  isSel (sels e e₁) = no λ { (_ , _ , _ , ()) }
  isSel (imap e) = no λ { (_ , _ , _ , ()) }
  isSel (sel e e₁) = yes (_ , e , e₁ , refl)
  isSel (E.imapb x e) = no λ { (_ , _ , _ , ()) }
  isSel (E.selb x e e₁) = no λ { (_ , _ , _ , ()) }
  isSel (E.sum e) = no λ { (_ , _ , _ , ()) }
  isSel (zero-but e e₁ e₂) = no λ { (_ , _ , _ , ()) }
  isSel (E.slide e x e₁ x₁) = no λ { (_ , _ , _ , ()) }
  isSel (E.backslide e e₁ x x₁) = no λ { (_ , _ , _ , ()) }
  isSel (logistic e) = no λ { (_ , _ , _ , ()) }
  isSel (bin x e e₁) = no λ { (_ , _ , _ , ()) }
  isSel (scaledown x e) = no λ { (_ , _ , _ , ()) }
  isSel (minus e) = no λ { (_ , _ , _ , ()) }
  isSel (let′ e e₁) = no λ { (_ , _ , _ , ()) }
  

  isImapb : (e : E Γ (ar q)) → Dec (∃₂ λ s p → Σ (s * p ≈ q) λ pf → ∃ λ t → e ≡ E.imapb pf t)
  isImapb (var x) = no λ { (_ , _ , _ , _ , ()) }
  isImapb zero = no λ { (_ , _ , _ , _ , ()) }
  isImapb one = no λ { (_ , _ , _ , _ , ()) }
  isImapb (imaps e) = no λ { (_ , _ , _ , _ , ()) }
  isImapb (sels e e₁) = no λ { (_ , _ , _ , _ , ()) }
  isImapb (imap e) = no λ { (_ , _ , _ , _ , ()) }
  isImapb (sel e e₁) = no λ { (_ , _ , _ , _ , ()) }
  isImapb (E.imapb x e) = yes (_ , _ , x , e , refl)
  isImapb (E.selb x e e₁) = no λ { (_ , _ , _ , _ , ()) }
  isImapb (E.sum e) = no λ { (_ , _ , _ , _ , ()) }
  isImapb (zero-but e e₁ e₂) = no λ { (_ , _ , _ , _ , ()) }
  isImapb (E.slide e x e₁ x₁) = no λ { (_ , _ , _ , _ , ()) }
  isImapb (E.backslide e e₁ x x₁) = no λ { (_ , _ , _ , _ , ()) }
  isImapb (logistic e) = no λ { (_ , _ , _ , _ , ()) }
  isImapb (bin x e e₁) = no λ { (_ , _ , _ , _ , ()) }
  isImapb (scaledown x e) = no λ { (_ , _ , _ , _ , ()) }
  isImapb (minus e) = no λ { (_ , _ , _ , _ , ()) }
  isImapb (let′ e e₁) = no λ { (_ , _ , _ , _ , ()) }

  isSelb : (e : E Γ (ar p)) → Dec (∃₂ λ s q → Σ (s * p ≈ q) λ pf → ∃₂ λ t u → e ≡ E.selb pf t u)
  isSelb (var x) = no λ { (_ , _ , _ , _ , _ , ()) }
  isSelb zero = no λ { (_ , _ , _ , _ , _ , ()) }
  isSelb one = no λ { (_ , _ , _ , _ , _ , ()) }
  isSelb (imaps e) = no λ { (_ , _ , _ , _ , _ , ()) }
  isSelb (sels e e₁) = no λ { (_ , _ , _ , _ , _ , ()) }
  isSelb (imap e) = no λ { (_ , _ , _ , _ , _ , ()) }
  isSelb (sel e e₁) = no λ { (_ , _ , _ , _ , _ , ()) }
  isSelb (E.imapb x e) = no λ { (_ , _ , _ , _ , _ , ()) }
  isSelb (E.selb x e e₁) = yes (_ , _ , x , e , e₁ , refl)
  isSelb (E.sum e) = no λ { (_ , _ , _ , _ , _ , ()) }
  isSelb (zero-but e e₁ e₂) = no λ { (_ , _ , _ , _ , _ , ()) }
  isSelb (E.slide e x e₁ x₁) = no λ { (_ , _ , _ , _ , _ , ()) }
  isSelb (E.backslide e e₁ x x₁) = no λ { (_ , _ , _ , _ , _ , ()) }
  isSelb (logistic e) = no λ { (_ , _ , _ , _ , _ , ()) }
  isSelb (bin x e e₁) = no λ { (_ , _ , _ , _ , _ , ()) }
  isSelb (scaledown x e) = no λ { (_ , _ , _ , _ , _ , ()) }
  isSelb (minus e) = no λ { (_ , _ , _ , _ , _ , ()) }
  isSelb (let′ e e₁) = no λ { (_ , _ , _ , _ , _ , ()) }

  isSum : (e : E Γ (ar p)) → Dec (∃₂ λ s t → e ≡ E.sum {s = s} t)
  isSum (var x) = no λ ()
  isSum zero = no λ ()
  isSum one = no λ ()
  isSum (imaps e) = no λ ()
  isSum (sels e e₁) = no λ ()
  isSum (imap e) = no λ ()
  isSum (sel e e₁) = no λ ()
  isSum (E.imapb x e) = no λ ()
  isSum (E.selb x e e₁) = no λ ()
  isSum (E.sum e) = yes (_ , e , refl)
  isSum (zero-but e e₁ e₂) = no λ ()
  isSum (E.slide e x e₁ x₁) = no λ ()
  isSum (E.backslide e e₁ x x₁) = no λ ()
  isSum (logistic e) = no λ ()
  isSum (bin x e e₁) = no λ ()
  isSum (scaledown x e) = no λ ()
  isSum (minus e) = no λ ()
  isSum (let′ e e₁) = no λ ()

  isSlide : (e : E Γ (ar u)) → Dec (∃₂ λ s′ p′ → ∃₂ λ r′ t → ∃₂ λ x′ t₁ → ∃ λ x₁ → e ≡ E.slide {s = s′}{p′}{r′} t x′ t₁ x₁) 
  isSlide (var x) = no λ ()
  isSlide zero = no λ ()
  isSlide one = no λ ()
  isSlide (imaps e) = no λ ()
  isSlide (sels e e₁) = no λ ()
  isSlide (imap e) = no λ ()
  isSlide (sel e e₁) = no λ ()
  isSlide (E.imapb x e) = no λ ()
  isSlide (E.selb x e e₁) = no λ ()
  isSlide (E.sum e) = no λ ()
  isSlide (zero-but e e₁ e₂) = no λ ()
  isSlide (E.slide e x e₁ x₁) =  yes (_ , _ , _ , e , x , e₁ , x₁ , refl)
  isSlide (E.backslide e e₁ x x₁) = no λ ()
  isSlide (logistic e) = no λ ()
  isSlide (bin x e e₁) = no λ ()
  isSlide (scaledown x e) = no λ ()
  isSlide (minus e) = no λ ()
  isSlide (let′ e e₁) = no λ ()
  
  isBackslide : (e : E Γ (ar r)) 
              → Dec (∃₂ λ s′ u′ → ∃₂ λ p′ t → ∃₂ λ t₁ x → ∃ λ x₁ 
                     → e ≡ E.backslide {s = s′}{u = u′}{p = p′} t t₁ x x₁)
  isBackslide (var x) = no λ ()
  isBackslide zero = no λ ()
  isBackslide one = no λ ()
  isBackslide (imaps e) = no λ ()
  isBackslide (sels e e₁) = no λ ()
  isBackslide (imap e) = no λ ()
  isBackslide (sel e e₁) = no λ ()
  isBackslide (E.imapb x e) = no λ ()
  isBackslide (E.selb x e e₁) = no λ ()
  isBackslide (E.sum e) = no λ ()
  isBackslide (zero-but e e₁ e₂) = no λ ()
  isBackslide (E.slide e x e₁ x₁) = no λ ()
  isBackslide (E.backslide e e₁ x x₁) = yes (_ , _ , _ , e , e₁ , x , x₁ , refl)
  isBackslide (logistic e) = no λ ()
  isBackslide (bin x e e₁) = no λ ()
  isBackslide (scaledown x e) = no λ ()
  isBackslide (minus e) = no λ ()
  isBackslide (let′ e e₁) = no λ ()

  isLogistic : (e : E Γ (ar s)) → Dec (∃ λ t → e ≡ logistic t)
  isLogistic (var x) = no λ ()
  isLogistic zero = no λ ()
  isLogistic one = no λ ()
  isLogistic (imaps e) = no λ ()
  isLogistic (sels e e₁) = no λ ()
  isLogistic (imap e) = no λ ()
  isLogistic (sel e e₁) = no λ ()
  isLogistic (E.imapb x e) = no λ ()
  isLogistic (E.selb x e e₁) = no λ ()
  isLogistic (E.sum e) = no λ ()
  isLogistic (zero-but e e₁ e₂) = no λ ()
  isLogistic (E.slide e x e₁ x₁) = no λ ()
  isLogistic (E.backslide e e₁ x x₁) = no λ ()
  isLogistic (logistic e) = yes (e , refl)
  isLogistic (bin x e e₁) = no λ ()
  isLogistic (scaledown x e) = no λ ()
  isLogistic (minus e) = no λ ()
  isLogistic (let′ e e₁) = no λ ()

  isBin : (e : E Γ (ar s)) → Dec (∃₂ λ o t → ∃ λ t₁ → e ≡ bin o t t₁)
  isBin (var x) = no λ ()
  isBin zero = no λ ()
  isBin one = no λ ()
  isBin (imaps e) = no λ ()
  isBin (sels e e₁) = no λ ()
  isBin (imap e) = no λ ()
  isBin (sel e e₁) = no λ ()
  isBin (E.imapb x e) = no λ ()
  isBin (E.selb x e e₁) = no λ ()
  isBin (E.sum e) = no λ ()
  isBin (zero-but e e₁ e₂) = no λ ()
  isBin (E.slide e x e₁ x₁) = no λ ()
  isBin (E.backslide e e₁ x x₁) = no λ ()
  isBin (logistic e) = no λ ()
  isBin (bin x e e₁) = yes (x , e , e₁ , refl)
  isBin (scaledown x e) = no λ ()
  isBin (minus e) = no λ ()
  isBin (let′ e e₁) = no λ ()

  isScaledown : (e : E Γ (ar s)) → Dec (∃₂ λ x t  → e ≡ scaledown x t)
  isScaledown (var x) = no λ ()
  isScaledown zero = no λ ()
  isScaledown one = no λ ()
  isScaledown (imaps e) = no λ ()
  isScaledown (sels e e₁) = no λ ()
  isScaledown (imap e) = no λ ()
  isScaledown (sel e e₁) = no λ ()
  isScaledown (E.imapb x e) = no λ ()
  isScaledown (E.selb x e e₁) = no λ ()
  isScaledown (E.sum e) = no λ ()
  isScaledown (zero-but e e₁ e₂) = no λ ()
  isScaledown (E.slide e x e₁ x₁) = no λ ()
  isScaledown (E.backslide e e₁ x x₁) = no λ ()
  isScaledown (logistic e) = no λ ()
  isScaledown (bin x e e₁) = no λ ()
  isScaledown (scaledown x e) = yes (x , e , refl)
  isScaledown (minus e) = no λ ()
  isScaledown (let′ e e₁) = no λ ()

  isMinus : (e : E Γ (ar s)) → Dec (∃ λ t  → e ≡ minus t)
  isMinus (var x) = no λ ()
  isMinus zero = no λ ()
  isMinus one = no λ ()
  isMinus (imaps e) = no λ ()
  isMinus (sels e e₁) = no λ ()
  isMinus (imap e) = no λ ()
  isMinus (sel e e₁) = no λ ()
  isMinus (E.imapb x e) = no λ ()
  isMinus (E.selb x e e₁) = no λ ()
  isMinus (E.sum e) = no λ ()
  isMinus (zero-but e e₁ e₂) = no λ ()
  isMinus (E.slide e x e₁ x₁) = no λ ()
  isMinus (E.backslide e e₁ x x₁) = no λ ()
  isMinus (logistic e) = no λ ()
  isMinus (bin x e e₁) = no λ ()
  isMinus (scaledown x e) = no λ () 
  isMinus (minus e) = yes (e , refl)
  isMinus (let′ e e₁) = no λ ()

  isLet : (e : E Γ (ar p)) → Dec (∃₂ λ s′ t → ∃ λ t₁ → e ≡ let′ {s = s′} t t₁) 
  isLet (var x) = no λ ()
  isLet zero = no λ ()
  isLet one = no λ ()
  isLet (imaps e) = no λ ()
  isLet (sels e e₁) = no λ ()
  isLet (imap e) = no λ ()
  isLet (sel e e₁) = no λ ()
  isLet (E.imapb x e) = no λ ()
  isLet (E.selb x e e₁) = no λ ()
  isLet (E.sum e) = no λ ()
  isLet (zero-but e e₁ e₂) = no λ ()
  isLet (E.slide e x e₁ x₁) = no λ ()
  isLet (E.backslide e e₁ x x₁) = no λ ()
  isLet (logistic e) = no λ ()
  isLet (bin x e e₁) = no λ ()
  isLet (scaledown x e) = no λ ()
  isLet (minus e) = no λ ()
  isLet (let′ e e₁) = yes (_ , e , e₁ , refl)

  unvar : {x y : is ∈ Γ} → var x ≡ var y → x ≡ y
  unvar refl = refl

  -- Hail UIP
  *≈-uniq : (a b : s * p ≈ q) → a ≡ b 
  *≈-uniq {[]} {[]} {[]} [] [] = refl
  *≈-uniq {x ∷ s} {x₁ ∷ p} {x₂ ∷ q} (cons ⦃ refl ⦄ ⦃ a ⦄) (cons ⦃ refl ⦄ ⦃ b ⦄) 
    = cong₂ (λ t u → cons ⦃ t ⦄ ⦃ u ⦄) refl (*≈-uniq a b)

  +≈-uniq : (a b : s + p ≈ q) → a ≡ b 
  +≈-uniq {[]} {[]} {[]} [] [] = refl
  +≈-uniq {x ∷ s} {x₁ ∷ p} {x₂ ∷ q} (cons ⦃ refl ⦄ ⦃ a ⦄) (cons ⦃ refl ⦄ ⦃ b ⦄) 
    = cong₂ (λ t u → cons ⦃ t ⦄ ⦃ u ⦄) refl (+≈-uniq a b)

  suc≈-uniq : (a b : suc s ≈ p) → a ≡ b
  suc≈-uniq [] [] = refl
  suc≈-uniq (cons ⦃ refl ⦄ ⦃ a ⦄) (cons ⦃ refl ⦄ ⦃ b ⦄) = cong₂ (λ t u → cons ⦃ t ⦄ ⦃ u ⦄) refl (suc≈-uniq a b)

  cong₃ : {X Y Z W : Set} (f : X → Y → Z → W) → ∀ {x x₁ y y₁ z z₁} 
        → x ≡ x₁ → y ≡ y₁ → z ≡ z₁ → f x y z ≡ f x₁ y₁ z₁
  cong₃ _ refl refl refl = refl

  open import Data.Maybe

  _≟ᵉ_ : (a b : E Γ is) → Maybe (a ≡ b)
  var x ≟ᵉ u with isVar u
  ... | no ¬p = nothing
  ... | yes (v , refl) with eq? x v
  ... | neq _ _ = nothing
  ... | veq = just refl 
  zero ≟ᵉ u with isZero u
  ... | no ¬p = nothing
  ... | yes refl = just refl
  one ≟ᵉ u with isOne u
  ... | no ¬p = nothing
  ... | yes refl = just refl 
  imaps e ≟ᵉ u with isImaps u
  ... | no ¬p = nothing
  ... | yes (u′ , refl) = e ≟ᵉ u′ >>= just ∘ (cong imaps)
  sels {s = s} e e₁ ≟ᵉ u with isSels u s
  ... | no ¬p = nothing
  ... | yes (refl , u , u₁ , refl) = do
    eu ← e ≟ᵉ u
    e₁u₁ ← e₁ ≟ᵉ u₁
    just (cong₂ sels eu e₁u₁)
  imap {s = s}{p} e ≟ᵉ u with isImap u
  ... | no ¬p = nothing
  ... | yes (s′ , p′ , spq , u , eq) with s ≟ˢ s′
  ... | no ¬p = nothing
  ... | yes refl with ++-cancelˡ s′ p′ p spq 
  (imap {_} {s′} {p} e ≟ᵉ u₁) | yes (s′ , p , refl , u , refl) | yes refl | refl = e ≟ᵉ u >>= just ∘ (cong imap)
  sel {s = s} e e₁ ≟ᵉ u with isSel u
  ... | no ¬p = nothing
  ... | yes (s′ , u , u₁ , refl) with s ≟ˢ s′
  ... | no ¬p = nothing
  ... | yes refl = do
    eu ← e ≟ᵉ u
    e₁u₁ ← e₁ ≟ᵉ u₁
    just (cong₂ sel eu e₁u₁)
  E.imapb {s = s}{p} x e ≟ᵉ u with isImapb u
  ... | no ¬p = nothing
  ... | yes (s′ , p′ , x′ , t , refl) with s ≟ˢ s′
  ... | no ¬p = nothing
  ... | yes refl with p ≟ˢ p′
  ... | no ¬p = nothing
  ... | yes refl rewrite *≈-uniq x x′ = e ≟ᵉ t >>= just ∘ (cong (E.imapb x′))
  E.selb {s = s}{q = q} x e e₁ ≟ᵉ u with isSelb u
  ... | no ¬p = nothing
  ... | yes (s′ , q′ , x′ , u , u₁ , refl) with s ≟ˢ s′
  ... | no ¬p = nothing
  ... | yes refl with q ≟ˢ q′
  ... | no ¬p = nothing
  ... | yes refl rewrite *≈-uniq x x′ = do
    eu ← e ≟ᵉ u
    e₁u₁ ← e₁ ≟ᵉ u₁
    just (cong₂ (E.selb x′) eu e₁u₁)
  E.sum {s = s} e ≟ᵉ u with isSum u
  ... | no ¬p = nothing
  ... | yes (s′ , u , refl) with s ≟ˢ s′
  ... | no ¬p = nothing
  ... | yes refl = e ≟ᵉ u >>= just ∘ (cong E.sum)
  zero-but {s = s} e e₁ e₂ ≟ᵉ u with isZeroBut u
  ... | no ¬p = nothing
  ... | yes (s′ , i , j , u , refl) with s ≟ˢ s′
  ... | no ¬p = nothing
  ... | yes refl = do
    ei ← e ≟ᵉ i
    e₁j ← e₁ ≟ᵉ j
    e₂u ← e₂ ≟ᵉ u
    just (cong₃ zero-but ei e₁j e₂u)
  E.slide {s = s}{p}{r} e x e₁ x₁ ≟ᵉ w with isSlide w
  ... | no ¬p = nothing
  ... | yes (s′ , p′ , r′ , t , x′ , t₁ , x₁′ , refl) with s ≟ˢ s′ | p ≟ˢ p′ | r ≟ˢ r′
  ... | yes refl | yes refl | yes refl rewrite +≈-uniq x x′ | suc≈-uniq x₁ x₁′ = do
    et ← e ≟ᵉ t
    e₁t₁ ← e₁ ≟ᵉ t₁
    just (cong₂ (λ a b → E.slide a _ b _) et e₁t₁)
  ... | _ | _ | _ = nothing
  E.backslide {s = s}{u}{p} e e₁ x x₁ ≟ᵉ w with isBackslide w
  ... | no ¬p = nothing
  ... | yes (s′ , u′ , p′ , t , t₁ , x′ , x₁′ , refl) with s ≟ˢ s′ | u ≟ˢ u′ | p ≟ˢ p′
  ... | yes refl | yes refl | yes refl rewrite suc≈-uniq x x′ | +≈-uniq x₁ x₁′ = do
    et ← e ≟ᵉ t
    e₁t₁ ← e₁ ≟ᵉ t₁
    just (cong₂ (λ a b → E.backslide a b _ _ ) et e₁t₁) 
  ... | _ | _ | _ = nothing
  logistic e ≟ᵉ u with isLogistic u
  ... | no ¬p = nothing
  ... | yes (t , refl) = e ≟ᵉ t >>= just ∘ (cong logistic)
  bin x e e₁ ≟ᵉ u with isBin u
  ... | no ¬p = nothing
  ... | yes (o , t , t₁ , refl) with x ≟ᵒ o
  ... | no ¬p = nothing
  ... | yes refl = do
    et ← e ≟ᵉ t
    e₁t₁ ← e₁ ≟ᵉ t₁
    just (cong₂ (bin _) et e₁t₁)
  scaledown x e ≟ᵉ u with isScaledown u
  ... | no ¬p = nothing
  ... | yes (x′ , t , refl) with x ≟ x′
  ... | no ¬p = nothing
  ... | yes refl = e ≟ᵉ t >>= just ∘ (cong (scaledown _))
  minus e ≟ᵉ u with isMinus u
  ... | no ¬p = nothing
  ... | yes (t , refl) = e ≟ᵉ t >>= just ∘ (cong minus)
  let′ {s = s} e e₁ ≟ᵉ u with isLet u
  ... | no ¬p = nothing
  ... | yes (s′ , t , t₁ , refl) with s ≟ˢ s′
  ... | no ¬p = nothing
  ... | yes refl = do
    et ← e ≟ᵉ t
    e₁t₁ ← e₁ ≟ᵉ t₁
    just (cong₂ let′ et e₁t₁)


  e-eq? : (a : E Γ is) (b : E Γ ip) → Maybe (Σ (is ≡ ip) λ pp → subst (E Γ) pp a ≡ b)
  e-eq? {is = is}{ip} a b with is ≟ⁱ ip
  ... | no ¬p = nothing
  ... | yes refl = a ≟ᵉ b >>= just ∘ (refl ,_) 




